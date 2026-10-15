-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3927
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:04:37.164601+00:00
-- url     : https://prove2.me/submissions/009a7dff-a7ab-4b5b-85fc-e5513144a33f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 706115107 ≤ n < 706294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 706116357 1250 706115107 706115143
    0x6020904200927090303090d030b0a0909080c0f0304151b081b0115140f130f0207020a08010b01030b010206090303130c0519050f0109181104170a05 65
    0x4030941c54a0440e0007400c040510030005844010714a03c111402814482d508680040b0700b4603140f13050701c0c1d07203070300964130200f1520560381500f090503c00e102303606c2889001408101441d240c400001c000d429509001c5e00c2c00b0354108101003901104000b04a40c0203610390140d52140c1c40d000600c0c01d040c0e240706c8807000b4000061141c60006003455481a02180e0000b6440e441d50061203060b0802c00c0803d018000175880c1000e403004041400c00100100c4103442ea4442c46400b44006001d0030755442d554242d040f40c81c065a000140e00c40d42c02080845800160060415003142c0008401d142507500a60241c3d42d40d401050640d6814024600070a000307000410303941c2440c04105035a4800148070a030400e0000c80c42204000804d60100c0080000820301c07440031078108036844807916980700381c0b8030421107803111001a5026041d100e0803140190a82800704210185400203002c0485015030703048001c0001095540510248041e1060018002c1aa1124919100d49001840c40000310108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 706117607 1250 706116357 706116401
    0x150905090a1a2b0501060f0504091a0402010e0303120a110703050301060f020c040e031b01060f050607020a09050403050d0b090c09060706060f18050c160311070504050406020904 78
    0x40d803024401080e402d42079034101d4000c400030780000c0d6402400d0011851001c00c01d410181406015005a026129942c001c0707103c4aa40760304001c121444000c0007010440410f4640340201038115040fa0302c240103042081c1840c241c2000a400c6038000c4400410b040b40c401c0074010b0724070051207054683c0451510b003601e07044854a001d0100c1c041403185500304019a01c0d082007551081c0050840340138040d01c00c1c490209150800741e103a81105222200c0008000000503080c1c3d014000e0404544d0380e400f00051244c1050140119903100074002d0340c100300703200800a8480304502ca010301c5117020307946058803410811500307020b45440c004000d20845442003030080741e040b100221110000221904c55a0f1106498240050510b43d8800701041e11004030009108024071500c45030060844010007581e41e504e102e10310580218010b45000e49100400100000d001e012580c43d074148200440e510396603100c00080540c0c41c110340448000c1e8002c20100701604050290001c00f9a21150030300b188 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 706118857 1250 706117607 706117631
    0x1719050108010632030601060801090509061b0f0f0a0207051c020a2d0603022a030703050c0f06070f030f0b220908070c080601060507050304060e0406150905090a 71
    0x303013912401c9901c16202c44a94070700420140d80484640040c0641522119a525180035015000902c0391441503410200050010f400200791039101d4021034504514405d200120000719070803030014008124800c1100013600a96080680100b86069000b0a45541800300707100c1000d902e2a00d0002e0106907000c0440180e8501c46680181c42c2e56600200030f0b0300304080030f0441c01030000c4c03111088032002c4902050181d1b240c4c0082802c200e459640448065400400742c1c1c0100607a4032400c4140c1040c00100000b92007080101407a005101c122a5031400d00d842c098205030040c3c400d8008a6103001c848200a03406004418400d03070240420091228034101064a94000301340b0801d1100000d01850a0041d05038060300c046500180c0d1582c540b111860410f500103614001c10140748100000003e1040c411412184026800700c00f550509207028019104415043d0005d584907881303400104000c0d07000720071041060b036146e450228443c42c000602106410161040c0c030154200080c003109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 706120107 1250 706118857 706118879
    0x5011203170c2b02070b15220905010e0d02030c1005090c010e270f0903250c0b030c1b010e070b03040206070813090506090f0a0c17190501080106 64
    0x3205201543c00101c1040003104202060080545814507440030030180f0500c142d40c02c225110fa007456002403613042c07520b0100501909101d4a81e0307034a000744550744501000d40c2e000950040d1255002203228501d0071401400e00b00f2860000c0010703400443d810404a03400c220420184407828402c10450400c4611151a920303501c0e042810b00090b100c010020f900c0703007c5c40c030b010002c00c44010386400300000d44080e041d00c3c00b0368070042e41e600b0900c0400c0d4811400b00440c0c000c1c80d1051400c8003003c1e8103070b1000d14000102402038822000b241d500164170b543e20170040d440351580f4440d845e55810034030982c108404280c94883c100c0c2c0e01d096070f0008034040018142d025147d01c03240e99612565507100050985c0b10b440001002103502190484054000300c1d2504203880e00032406000320703036844050082d8a4003c13545860390010000c00308102c484664007000120040d850300c0e06402121070202025840223542592007042504460500c3d08141e2240030701400c0c4203802031040303a2912400c028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 706121357 1250 706120107 706120117
    0x6121f152706060e060903101b02212203150504050105180607200703050706090605030f0c0304021f020c0325150c1a060f0d120305130605011203170c 66
    0x801100c001610080691f02005020403001e40341c44144010781c1500307000005001011100c4c40580b20b10301e08100401c0410700f01c482107100c1d900104d420414000c0c0c44080582c0312a0b01c02e080c8016120000c00401c80107a00f0522000b5031110200b0141403510300182191002403030400491401c0b108042c0d800d45c0821050741000791031800501c0e141d90b0102550407d60400301d0151548190721001040040101d8660103c425586549900f642e503828284d0f9180300443e80c924603810310000040008450f1000f96804c0750019081a40c0b0704000f01d4520714440e4401001005640108204521442e0401c202002120301500301300322101440c000d410140c00c07500070b04c445c60880300c0f40440381d14881c0540c400c0103030b000a0380c4401c0d01300c005c0e0b4a0708890307010b4882c5401403580441e001d0341070601101c070345e903010740c020111f5811400b0b01d54101c0c01000c2c084c04904904541c40d00140100c0c034913000f403a01801003d134142140c169146405002c42840007032210765480e0041c10005116002c0c01515 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 706122607 1250 706121357 706121359
    0x509090607120b0f0307030b07080c03150411090402030f01030506090706120c0c02030601030b0a060b09010e040e0106050607110405070819050c1303050c0906121f152706060e 77
    0x41a540c070035000055009044405050300340c401c0000c00024840c2c4003007058000d00c0c40350ac55a24503192820440450b110884d40040c5489242c200d85e5840d0606078009950740003907142c058101580280000c0030781c0d06c16a80c510309400101d006109002050103402d40000c1160020300c1858500000540300200c1e94841c1140141e81301240d5165a00851105210f190700405a41881d0f84a140034803200c1c0341501d482a086141a00100d100d00000c411a50302c1201611040e82c0101090200006082c0c19020101c0654a0303440000e100d4407410302904049102d00c00303c90f5804d09640500007101e900a0642080011800034440c8e880380c4e4020001403140b004002003620713590260305014030702c01c185058901c0082240c0c0002441030101c2e400134006001ca401e092540c4031803040040520021581c0690b80c0c011112801c01c40b604100100048140350b100418101e199401003820070301198408581040703411300d16043d802c0e583c10040c2c0800d1005c0380030480c950030311800410a80c0250070316 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 706123857 1250 706122607 706122611
    0x902011107060f120f0504050a03030b01031103130302100e01230c0702060708071e0b07090b1b0a02041407020d0c0b0f04050c0d030f0207060234030803090601050909060712 76
    0x40c4d00c0d4036142e50440041c1c1c400c0701a0a00045c1898a0a0f903039524030084280d00207846e00902d042e09601ca80103600a014180c45d9003030031a2603820701d04840b400b00802c12825440394200341d420b0301485005045829980000000c1c005024003100c04420848078032150421000c8010803000707550700e1082e10151381c0c050300c96546840c0c031361408421501c5100c43c042c181ea0f0f00d1012014040461031320068400303224112031159070b11040c500780c80000c01c50040f13000d410350074000c64040091a40200c104072091030210b90110a158000c10100c40c03c2880000c803300c1d00c0b00402602a4041108906050b00703894045402d1b01182c40b002c1042502070701c01c425028065021500f407010410010603c44001412100324107640d2801030031f0844400d100e07501600540e0000100a800410841010345118040003480d00941c95a803902a01d20b0400c00305040710004007102058410001c8e6201d080c082006185a504110400410800003040d201c140c0d0300c200100114aa80811521100030002c0300c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 706125107 1250 706123857 706123877
    0x50901060c0203030d02161e030c12090f080325080f03060a09053d0306050405030f0706020c16060f08040c21110a030b042a06030902011107060f 64
    0x3e0f05512518125010840c000300d100c08000600e0b61640c1001c0348640429102c0c0c00c03169006203100500840094041000b820304003000c80d06854600c2d041e4001850010b20460321852041c07850122500034646070341c00030980070305070408500500d1000e0250909030a00452a42c1c49000c1d600c40c1c64450044504003002042450302d4428062015102c8420300744030a240621542c0341d040900083c1103001e90701c040710001c650000c1805654407440213082080c041d8150b4a07124050a4080c0088400c1c0c401000302c0c018801d003280180412610034280941d41d05040b400d41032420100d4000603c882000c01400c0200a40207011811000b419081040c0c16584508009108603415404040030954045500d031100058001107400c0314841d80002e0b8800003103c00303203c0340340d42e5808010a00305c00080854041a00c0e0581d500304e103040c0001c81c3c114450441c10700000710205034806c0011030344609800c4219a00500c0490b4506500402007152614208004080c0c0c190701070010180450600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 706126357 1250 706125107 706125109
    0x1091802070501020f3c12040c080604150e0c06122502030702012c06160c030309060806030a080d0f02070602071113020301140609030a02030d2304050901060c02 71
    0x540b01c0c0c80c81082d000325103c554250192607115034080901200c408031000070ba440c4246d004c51101464814552503040020032540c6035070920024006036101d2011f0180007032804c0c401c000040c4198441d0b200300c2c5c0115007050448050705e0701e07025042d207641c004c4503101c0040e0312980d0130744280140c09500c0320516103a40300b402da01c86803001c0c0142070240c0e1003100e051006400000500c001803003a6511310211840d17400ba41c55003420f0200c544104104c0c0b5511260074a4000c0141c015034424000c0600030520341c0c0d54484103800580e1044000c252081300c1042584d41050103168080303010380c00b808040941d603403882c2041c032407602c040440e00da94560541d043d501c0b5a050b00c0c030507940518115136804650904029070089411520b00c03840d050400342c01a28a03900a42e4101e6440c4208820502892000c204194100880064061240d45450b001681d400c00c262400212107032101c031030000a22602100511f8662001c0d200a20100301c02c000301d86600c4000c504440c0c25140048002e10a84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 706127607 1250 706126357 706126361
    0x6041e020f090f070905030c0310020703021213030c050402070b04171209150711060705161203090618030e1201060305101a150733140601091802070501 67
    0x68011908501aa01008034546220f40b00754054402c90301e502d24401d40e94000c040d9107010340107140b03405801c40c0444580e80031007900501022032081c01a200a44036001a040ca40c1d003248440c000205403495080041c011542428404bc10041c0d03020342c58418292201102030002820040480703210300340520014802000b9543e104410007161146400c0c0304078100c3c0c1c0c6010010149040f00f240101080030540511440509070003020081c0203580e40750603056900b80c2001f048000c2c1c01c0701324030410303000440e850301180049245c9d0720f0018040486090443c210744030781d403119072035031184104d11010a40282030401040d10845040d00d088201401da1405040304d81e200401c188180d1a10022502003070b04007a500406001c40020010f005030300304461002c2e00f051030144110100186008a4000c001c035a02184042915984501c04c0c3d4464148078200c0d9596000c40e159203da0600120ba03541d02d02c90380047c1c1c01d2a04613025070a010b20300c802540d000760300c0e4a4540e0b000a2010400c003080d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 706128857 1250 706127607 706127629
    0x1807090c0206090d1b031b060204060225050d0b0c121824070c0303090b0a021e040302060405010c050a020d03051c1b1b0206070303021b06041e02 64
    0x650024020329125410103580d98209940103041801280c000d4060346124644207008030300c204da000344030740d58581c41c00d41d030f003160440407075021070f00f2041001c0104500d40000c100078401c1d64010841c0040356890b0010501d0500d03022400901889010896a0f807072070743c1400c2c2190001c501c450261254030010b8500d121303d5201c804290501420881007151001111010050350402e4a9142035008400500009025403140d5024a03000200c0c1d01c05104100100c1054482d003000a00903442c0c1d100d42c10024401c80707103040031940001e11141420030200060f020105e03050365080c240350565001481030f0080c0c2c010141000b54a8071180c05022042104d607440d60303006804600c07201c01504000f0f06c50342c0003010450450f014a010f501c4880c10901c02c4c101d11040007a12401d90f401d04074411961007446580000c002c1c4441001c032809661200000c00e4018403030385005076941054075440000009503071880100d80c20501c1000b0219640c410010140440107001da07203c1601d51002411003500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 706130107 1250 706128857 706128869
    0xd0804031112090411220303111501120203151501031113030605071b0b040b130f080901090b04080d030605030d0f0e04110a030e07050d020109030803101203030c0909050f1807 77
    0x10600081e21034400100d000025a4040d07aa27134201000381c020306aa880070b10007101c03802070145100403c01000d407008040c11903803008007079459880302e8981c0c074100040241c1da416200c00051445007620340e058418030a00c0c071140c1716503d0414004008000c4070006911000d00007507141c400141c0604d1240302d5615180c0d503203196440142401e42840c0458110850342104d445906102040c040c004010b0301490440d4001c840ea10720040541d18043c00703400c40c1c900c0307505010303d454021803a501090041c0025280003002482c0514031744000805681c032503800703140031b6003001a6401009031b2100c11a900e140301d82c1014082340d0011008500280300b6907444010024002c2006250154190801c0c60050312040880390b040707840748200701441d40b001d40300901203030700003604100150645002e9548042c046180c015034543c4c801303c00003d030803000b808034000b0f40c0d03400c14031000c107030004850342c09080101030412070743c40c1c1079042c1c20b143c00c0c1c041d0018181310110720040c0703000102002000041c0032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 706131357 1250 706130107 706130137
    0x41e03080408010902040b011103034210030e0312090c0d05100e01020429040302091e0a020301060f051326011b170411030d0804031112090411 63
    0x681c401e0b8480c000d000e001c40032481103040c60034401266115800c450318807088440a140b460b1a0b40c600d120003800d2000004103201824004240b4a140382d840c542040e89a01500c034444e4000c0340c041000c10084c0d400b80c0780034945081c8503003902c220300005440e880315070350501c401035490701c0009500e032111072101d0703d601c50086000c2c00d081001c0030a101c0c3c17101160850a10608826054a500303038040c5000700702d0740d2280c0c04541541d0780c9182703048240d41030320203481d0b600e450780306d4000c509900c408407114401c4100140140340c0200c64402042d9010031046811400d6504102005044c0065000361500300031020891000050000171800020404100c0b000680e85000c14100d440c8502d200c010360780b035440d090b42c45045400d117428140101c4107076034841451a0321180c9041c0032b500060b0003a1459044441c4c130000c561020050104502095202c1812030b01d05484c0040c41c46864503000100b680251031880314000f800c400b682c026403400c403004600b90100e40c545081030b01550142c994241 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 706132607 1250 706131357 706131359
    0x40b0403050c070605190f05030a0b0604120606030b0702010225061401060815010504030b040311070803040303180603090c03140f06010909020405060603040b040209041104020735041e030804 84
    0x1038020380104144083c600b00030300f00d0904044259800c150034421800452230410000d000341c24107034050a15264018001400e15844180c8a50300070103074031048071025601c1c2c1061003482075024100da401103030307880203502d030441c0c8400300a28a00c42007080388401540b48000c20402a0351b40103c0709a003070203000043d01d5070399000004d107500420364560014800700390a450583d4031580440b000d03a40c01548000361510707681d40032520149000f00442d45c60140b1240401c040505000504c000d50080d42d50000d4100b6000300c3c0310b00d8010690125042c58a020f40c4240024403101014040341d400c18100d450407510101c04908001646915042500a010000c00c3c441d481d03070700034020f981c025101003000f0358482c03040c0040d07448165400b402c071440d11000640149403c81510b90700a05c24640014440348a0300418203a81001c10110389020410411804010310b0019150b800401e075000140445080000001c1d144600e02500080c240c1c04610402040c0003440130b08000c56105c402c0c180d40d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 706133857 1250 706132607 706132619
    0x12030d0515060315090136021315090b12150a0503160f090513080a020a0b0109021b0c01050f030619060203040603050105091b071a0903120109050f040b0403050c07 72
    0x20303211803c14544912298000810303076000902000818080003020151000c0c50b08280f1399840080300060301e00d413034007000312704000440d080e000300050000c00c0f400040607030b0000000c1c1038045c50350042454280240581d04580414820035134012071030915192134110f015000c0744040341540c02403030309482040561495020342c20018000c030f41c1d21102440d03030140c9826043c1e007551070659140003440303544100d03140071500079401020b1448050044a182070749640c0e074040078488c01d0307201600702540868450800390009a030040140d100c00040c1000041d05000038100c0e004055810710001000b10010f2200e031200a586c43c3c1c200c070300051200046544a4000b56254024011a00043d0500c000016642080c0e03902c0350080c84403002038841e03084600145082c2e6000000b0641c0ca03050b0b18500384018040d03208995001c7c20300e82000d1a60350000b100b41840c000410381c0440d01c00340c039003c100200e00030080641030304541e2000c3d01070f502d5192401d0454841c001e0854908041c0100d40c000114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 706135107 1250 706133857 706133881
    0xb0d08040b0919050d020928020901020d0927090f051e06090c090a0f05070f1b0b040204021b150126100b2106010602010b12030d05150603 61
    0x8103510885101c0218288500481800f565501c0b40d950840035008265005242141c1115070090016000c40f901080c814202c101c20004040b042c9017056000505580c1075a05011001048900d8101450000d2402902030301864150b020680740304040d04150ba10341419410004903141c115507480d150f01c2090409a03165000c844001c0c10513880090b4031501c400000c1400c5200e028060060b00002d4180e00c02d10410040080c94481c5503940e95800300301450780c51007110b018089035a200f214495550030050700f92140880c030b40350f03a1003e144e250f01c0098038445a19030f01036410340e070140c3c45020341504000508480c129040141c05050652900e46400c0700500f0304031440c00b2104404440d9000a5000705031a444401c41680c01c240710b130701c54010b03c1382c1140c82004005410250105540043c1080101000b0b801403000c1e00208010480c6a5090240c1c01d00103508580c43c400040b038184035a07a507031064004041205850343c00083c0d0031251407040d01c8545001a00e000e40d41d107048422000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 706136357 1250 706135107 706135117
    0x2090a060918030801051903061a0415261906020c0606040e031b070f08070e0105040b0102071503090b0c090108011a0a030e030702030d050408060601180302040b0d08040b 75
    0x4040c40d181004082c40c1010311081c0005800d40c0703030441d40c0d07403c220600c2101c03c2d429100001e2903c0c80c041c00000100548030741030000d14004948200d6140000c10041550703086181210400804d0000f03010943c1081c06800710a031542c014905400401c408440c00c0540503c1d00940c03c00005e0b03c2403050251940041504940d03200544902e641c4013000c201c00c5403d022982003055106001030343d01d402c0b10050002c0504816030480d01703207540c1c4080118481c54560406903541c1c210f510308010a8558104507405080129010300040c40603a000030368070109841101d080b146000301c1030b00c41034000d62000104c1504040f4007103552414140d1881e07241e010025880c0094a914000142e4250703c00c543c40504072000c00c4185451700002084019243c606404800750104205000040c3d0b0100420300f074900342526420748842ca4801d110f41400401401d080c10b00c03c3c0309408400740400caaa03540c0940e84d04940020307401c44044089000c441b640500200034400c00500800c45583c0f800c0070740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 706137607 1250 706136357 706136369
    0x60f09360303180f030a0c0605040c03060e100633110307060204050f030705090a1a0315100812040330030b0a0b0f041202060f0a081e040b0a02030a0902090a06 70
    0x504804407113a001680c074403401d208040054180c0e41030500048254000e01c0d00300f405500c1d420310094894651004454028812118642c00601d612410000902584004281120017040c4154ac0c2d4010520541d2072203420000014101000b150054010803a90303042c0010002102c1d110394030761514034001d61040c02220f12a443c06e01d080c40c42d40c600018036409a0340041c00780341360f90300c1c1e050009001c2c00c0340c2030f4902c005440c4130040c1c4040740c0341041074a03078034021031009007045d051030070309a01c441d44560003540440d0804024900301450030340484044030344c01b110801c8420500c0c00c1101403000f100c4581130005608001030404c1640c1600504e03003440c4201c0d0200c504036940c0301400b0540c42400e1009549a200307100c100f0212184460798102503001400c00e51404c44014100e5019900c209445000b0498440a00c0301460072142c0c024080981d0302841001424070351544030b1540402041007124a40000c0080d0803001a44c11014609601414045503418948014809400140122 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 706138857 1250 706137607 706137613
    0x7140a120f15060b03010e0c16140f0a0b1608011413110705060f161205040c050a03051b0f060d11040b0c100b030102040e241305060f0936030318 64
    0x4031f080c41d002c540844803c44140d680141a03000c0300e2b03680e4a54680a44440c80043c0161000450b0600b400e00c8038003401ca214030303803650fa98a040c200c0360b60400b40300c842e04810400c03003800600a421110f101043c002404940420b060106000c030310300079000c1c96541415190002c12404104040018090b00400788032900c1583c17680c8000100030291030310500e49000541e1040c5460f103000e12079000704d801c2401000702d0614951940085540030540d40c1c0304481303a5004582046000c4a4024039240c13228045601e02000405540000c015001e20381c403080322183e50b0f0f0b00b94120020503104a81c014130304080c1c40340d02c59000c12076098072105802d01a00b8250704003030380d07450146418400c94050350a013040c0f0189544a5084800c010301c0c01e003000300568296071441190740c7d5238610040070030448a03d00420030345468000d01c03144031075900045001d001950240044d242a081c1c5d0254210080c00340107400f0f1032059081d514140407208a85000c3c0000401c0c0600500a0401654a440341c4021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 706140107 1250 706138857 706138861
    0xc0f0801060f14030a0b030609030a020f03090a0504021c0f0609110a090e0c070c12060b0409080405010302070501020708030f040c060c080301090f02070b0907140a120f15060b03010e 80
    0x400d4034599030b051109000291010201100c84100c680655006000c0500004140c031513100405c0c604101a10280401d0b0301c0494900c1c1d01e268104800c40c1c0600310b210145040c40160008600010700d5401903910442d0045407020807550f07041550780e01160a400244180e040d1100e60800030181c41c0a407080b0700b41045030743c5254102940071070b11a24202c1e0717502d03070550340740400700ca40403013010b0001700c2022804c01074080800d01800c100000b030b0109048040c41f03107030646403000448550b41c0810340103038108620300d40815508030a40c0c1c101c1d107003820301607682d004030725219009100350b11006004e0306011040c003170801c0e520188140f0840c07158019000c00c83d112281070343c041115900003021074108000501ca85e800030341118a1a41e40c01a025040071610703901d0301e401d00412a030f0649550b000313803030030400c85008801c0a00e6207101901ea2030101810701628405483c9000c102804414424400008104000c43c90043e07007440403070f0030000a0340712075500540741d2080c4503901d02c2da80c00b540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 706141357 1250 706140107 706140119
    0x60b0d0c0e1c0f05070905010f12020a1a040e040609032303070f09090207110102100209150f07020904030207080607030e0606010804020103110d0b1009180911040c0f0801 75
    0x8048010800300030b1462051004110551218401c040e904840004600710800000b030410800301001e007504000108141d03040804004c07071894980d20100d68810781040050150b1a1050101c040d100891454921440c610344010085d1041307500c00440c2c49400002c10007403040c0b5a000b5000706100e6694485074128070f400700f0502c1c000c0703209484001e540810229500b81e0060500c0460a030180c1400c1017a6135071b40e4494400c907044014207580035010815078008640e0f061055102e5000e6816046051490b02c0011a009805554602d940008000ad400741d803d6507201c251348160b640101095100d00e000e00e0025140c000910a5500a20611002c10741c4c00d4080d02840300c50305215402440382d9503400d8011600440064003c2e4145962a50191035645101e0000d1200c000c1d1002e0100f1084189000d00070040d068001e00400c0044202c01401001c40c000d130020114103445a012a651105040c0b4807040c250a00c042584149044d080d8200c0ca5004060380081c140e0310745502c503443c2c1c0e9480b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 706142607 1250 706141357 706141367
    0x90f010207061403090a0204020a0c060b06030702100b03011d160f051e18130c0f140618060d05071805010801180608060112120212031306020d060b0d0c 67
    0x1010b60310214801c2e200941c281090030001d16400700603501180c100c581d594001c2402c80e40008651000103000000060611003940200d40712104107456492451401c2a0001d40b550002d5465180c40ca4640b01d61400301d41e0300350050701c0c011030018254003030202d0640c2003681c3e9802880305829035164a040000300710360096044412110302030028000105107002900307940c4900380d441c661101c21824809143e10080c0f4010788034000c541741d0104040703454145100c03001e400c1c0c0c0c03041c40040d040c1d00003440401c42c01c030002c240ba60b00c10381301e0300d40710484925a03a44101640d5900c541145e030200341061240d0858100c07a000b0401511024130702d51001d0280b807640d90480c0200c6022401c035100400c680c1946c4840c1d503a901c5244038002412a499000351402e0183c281e212200107440ca080407002c0c080d00380165904905140010160682900e080b0740702d501005001310f5040c94440143c2d028880d058040383c410b820302840401c80f01d41c4541003802e0f190004143e00d8412481d00c2809586a8015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 706143857 1250 706142607 706142609
    0x7090806040f02010309081b010609060e090a0b0405150c1309091a0a0b0d0c080105071d010e0607050607030f0b032116020901060804050616080712060f0308090f010207 74
    0x215201d00d40d0340b10035070015005440516011542030200304150b03006003494071140c4031180320b6103002144084c94001d114040d6641c60300710300d06200100c824407064000000ba420481e5902c80d04861142d03545c0c0c1061802c001d00541038101d110451002c010082c031014008141000a0300c012410590f1208402c5003101e4542e54000c1201414448100310311030100a0b1643c0114120800700b05802c1d46004601409000c5108588840902205000f010428015198815882e1406140c80c0c900c050310300f4480030700c404100b41803002071380e403a43d60383d05c905041f118000e4000c0216000c50500902c010000d0201c2c1e014012014603200f0b01080324034020580400d03181e0404c01034041800000030101c030303079400002004240410788403e0001615848195070080465441c0c1c81e400c0c3c0b07424100141810070041014103900060700140c0140ca07000f1051940100e0689411180004800c1030034000f070180342c01024540c5816039000041004c5600104241c420640d4000921502080103a03a0b501d05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 706145107 1250 706143857 706143863
    0x121407051b070504090c0e011403060a200a021b040507171512060703110301050a0303030207030e0307140103200301330e121f1508150709080604 64
    0xc2001e904480c0e8210010340040100205845100342d0710700001d82225200f00045400e41d00e240300c1003000b51120b098035801001010307601000040708400090721a0300050020003400d9a0b0b4540340d10849440c491100b00200c0346039032994078603907036501a54820a64884091800c00e2100e080060304141c040d490141a803610f46506051142e00c04408a210051800b28101c1c1184041e03503052f44c804424645031241140078103400d0505500040640e994030742d10310748070b510403c0100b00546902e20b690046075054600180c2307408252508960b408001050701d5454070807000046000d0220a03070003c080382090324104801d4811507003200c14140030640d8001125000e0004224105d04950302690040c9020700b00c07140c042041c0c54180007048a050b10100098a0300d501c102c03075003000c1300c00071140c040300c100074a2865110180d85400c907014030505400242ca651040c004140c03916079110291001c6402c0d140715014042a0700d00c40d8804449800c0003507180840000c2488020030031500a50f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 706146357 1250 706145107 706145117
    0xc0703020a350309220615080106020a0b0a0504020609040603030e0315090601030807020a03060c02031c020702090415090503070f0308061221160309060905010e01170901020910121407 81
    0x10000e00f0440300d0104d50401034059840c0072000d0005c90010710a0001400c0302892100309541c018800170580503058101901399885a005080410307484020750368003130314a05000c16180e50314808901d140c01500c1359980c001e814042c001c420075800100340b09002d0029411221380529625008844010039181c0c5402604440700520201d40f506c001850b146c1e0014010043c00c0d0350303903600e0000f11900551110b00682000c00c0c035482e810f00560b925180e03442d042c107040d030038250300f6000a4214600900b0007405101a0064004409520f4001c58601904903056075159603060030200000440004101e002511039000161a171414814500782c80349144000d000b001c4070003818204000503c90a500d0f40401071003850807a00e5110b08000e461403080d921500304a1400c030014000091030341100781448200a0301c9084c599000804003102c140411924007a901c420304000d00911510840d150040d02200412079807a03086000010314004500b41017040c00d40c110260b0104520558210700025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 706147607 1250 706146357 706146367
    0x1115120402040e0c0607030305040b0a0912030c02160306060509010e01080a060c2a060e06070c020f06040909081803061b1810260c07080c0703020a3503 67
    0x1082c590b000d500e00702419001c039004448500c000400982000c40300b1400280c980d0100010071025610190b000321460320103000742c02942e51169184036191122208055690a120501c0da108000c11030b008860050890b800c140c881c244440a480d0500589014404074400019007510700441c1c43c1c100c84007800544809403076607494101521000000c1000c00903c081c0c4a0404d00b04003425501c0022030f8119030b8611851880d03c2400c0e58001c842950003a00100c0c200068960080540700715603170704030384545080800c4c0717001403154010be0300030401861518621404200819005000d0b580186030740340ca5100c121420582c1d00d076001c8a0300d072004d0b0450b0045034146d83c10328002e00003013400c58030070f0300d1480e101202058811280304c00e800002940076800441c0350840001c00303072000c02c0103000780020b031030034900c0e4035118402c1410041c03107804002040d039240a4140031800256a00030207400c0d566a8500c4014201d20400d0302090740c0310444080301805255030b0b48002003840d0540040e41c200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 706148857 1250 706147607 706147609
    0x403020a060507060b03030f0c0607081b090a0b0c011d03071e0f060e0615010e0906010804080409090615060201022a0705030f0a1205030903030c0d060b071115120402 73
    0x160003d0808070342c0d503070301c3d403030130032403a40e01032024124040425444035114249164060f29222000c0c102d21b041c450800d0501c03e01082121003043d041661a4015030348091134004600303001480ea1041d2400040400c071100b181c003044d0844039155104d054403c40100040000780c2c1c480c800c600004024001605d805550350760318298011145029110300000403080ea11050305644005c140d03d0300380e030442410000301c00d0320007510004000d400c1ca0452110102480030945201000d40803034140000e42000030200914078080750050000c9240c00d0000d19928039080c4045c00c034000009490641340320020503224814801d60b48088882c01903024149403850a03284808000340c464182d500402c0c0c2c002c203464404024052403410301d1402001c1203c0d00742404018006000980300402004006015410500005480e005258941e09995851500c07984c00c00a050310b500c0304d4810300000c01c50006021001034018020001034640c8101c4070792070030f290001442100c2900602c0103c0074003142c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 706150107 1250 706148857 706148867
    0x9060e0c040612090f06020a02060106090b0a080c1303050a0b040b011a03070e041b0c1b1a09011b1208250806031504080a1403190b010905040507031508030403020a06 73
    0x10b00b4011941e00c40317000456180c80c01aa4092224140941e000400410a159000481d00001e0518154090030651a680003d0109070040c219591880c1c0104445250300c1d94003034031030011a03014040f141540b0b503a141803090b030181110709079065666103000265008075211799580c00c000807020603285940b00030094400c0c62018440716000303699101c0126041045400541c2202965192070110440c54a00002c2040c0e4a80880154281141c020002d1103085500b5804910745038512a49525103080100c4056140803224200341442003441001d00403980444c0401c143c0698a1903650b50b035001d1403103280c69010781503120403041da1030080811442501c401e42c2140006003540c034441900c40040c2070710036081d1010383d4401d2000400c20801034100011114a81107040220304500d00304080b000e800702603071010034805441d041039000f00d33032103800315401916009000f00f14030708101c04010020035410341e545822082000021800270400001e441c100e9030700401d1394891505003181156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 706151357 1250 706150107 706150121
    0x120510031e2406080a0206070f1506060c03030b150d201902150f06090624090a0803040b04090c0504080102160b18060109051f09060e0c040612 63
    0x35080108080840000d00341c2d00c10109040112140c03401400403404442e0100c8440b40d100c1203607940640b40d00c0c0d0068880d01d060341c0c0c8540e041400e010b0070058a051844040c542402d090300c0b880e1408801060040d0030000040910340a0b940c10091414504103000001d5404040300000358003e2000c90081c3c5460b0304840000203160146c441a0f0300c1c544140105a0031500c1455440d00d10b03881240384080d41008400602e180b00c4108010a00340440c0d00a90070074040c2409004102d880f000980c2d03503e4070784440d100101400c10181006031240e58101e201c0c0c014138550b900c41c0d10512000201c0c42e10000a44003526582603100789400d181c0a1941c00420051901e2010700c00c06020001d1104000c0c030103072280410801d804500480f41b46000f86640704001c003410f00d41c0400314441d80781070600180e91810b64840c41070000c0c4076241c1c021a07070315004408a00b60200c0c030300094003041c0d000840e00300d5411107004006009180c2c41e9a412030300385000728055000010303110355001d9220452600921 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 706152607 1250 706151357 706151393
    0x10504030e09070e1503010504150b0f1b030715050907140607020103090b0c0721120c090915080f01020901021506060d020c0c09011e29030103030c0312051003 70
    0x4c1203200801011941145240030318031000354000c0010000d40c100b90182441c00442c01d4200c480c45030400b1490528bd02403840740c0d00c1541404100d20a0801407942c42251034100300c0c1c11a901c03681a072030b02c1600481c042c0102d036100c50801003c40d55106000a1100a035015945425200c1c4105403d1042e90b40180030260304041d111080348001c90300062926008061403800282e40b00c0346800c00c0e002400b0074410f01221031090403520702d000c17940710100e1401e8001303046010a0440c0400c5e0115807944c1203402c00036146140a03641240d64540c286400203c840c0042680d8003442809503281c200e000d90724402e40940c011040362a01e500c4800003459010303800800c402d007080800898034040b60403440d803411aa9000710f00c1840c0e60318158030741780c1c0100320182451200052700700d002e0082144620900c0d0b14822000e0001e642110840101c00b81c000096005544942c2d49090003445265a03000540c042000d107020030030079401c580180b0703100c0d40000000300c0d06c0a21316074a5181c20511402c0071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 706153857 1250 706152607 706152617
    0x5060d02040e0d1d0906040e01200406020601090c0c120210090804060836070803070c0f1a07080c152e081e0f010501060c14010504030e0907 62
    0x9040140d94500c61030600305802e1004008440045078054100708000611907124201c218444001d0303910719100c01d9000350292804212420452075079409003a4000807001a032128034640b16500d00302001034411505907900b2075032581da0b00c030182001c07603d4040200000510560415000c100220071460002901d44106d909440c2007480d00d10840f4105001204e086d00c0004082240c1d030750100010760022902c80c40c0e000c0e20f04408032214101701d40300d001c0c05080b001d41102c1019000c818000280240318100949a8403201480d01c400c031030b0140e014052440490940125680b502d080040d446904c22413682c510304845500e9002c0d0315000071015110600c29a8100280c0b000048076080c0100c40c0041301020a031528170b5400307154480c42c0d1100700c0c0c19132410340810079000c00081042c03418200e250040c1f5146100c04280381814661760181209600382030000403065840b816070740030507002e19101d0b11140c2149180c1420383c0d8060340d000c1c000410f0303552101010318007841025044081d600701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 706155107 1250 706153857 706153879
    0xc09060f03010f0504050f060d060506031e100c020610050d021c0c051003020a270506041701050601110c131b0201020c0111120f04060f020c01091406090a03030506 72
    0x14100c0140c0c001d810010000c0440e0008104a080600549030007145210341c5a044e03181aa000c50801c0c80e001c1c0c03020780407684407004290151400d1100c0291600c030001c41011002007044c0c04d5641e0240c103100904c85625004031611411f101140b460302440c0f40b10301e500c130407910302001c00c03034101d05c900c00681e402002000143c20110407481a9201d1900c500480c0f28850301d0082089444881611b400045c540108070074200268080c0e1079003415985420b84280c07c425032034206c802d009094010b682c00c801c0014010603048404030f081d4015201000c020b01056032032800441380c00c0c0192301c7d810115030120a40d80c146192040d110498149103590005010000810f804400500e0300300300382c0545d41c000741d6000042c0080c0110034408004400407440e00b0a0380c080900c607400010001c3c0000c5050202060030800180c1081400e0f20b44e8070b40543d1500305840c1c2c0c0a008207607090341201c40b030010105000e204480171039424400c04420b80980341031256034600780d0140c10004d001590148410790307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 706156357 1250 706155107 706155127
    0x9070309030912320105152b0609030203191e08090a0c060905190b07030c2a140a30050105070507171306030c0e030d180603050c030c0906 61
    0x284080480781d5014030300c2d000344c080c00c101421908050940704580c2140c1c40e552059881d06000440c643c10201040318040441c003181c000900420034000f4901401c00c00040c0600d507002018000100c543c0c138840e440fa5481c4c1d9400e50310f44020340c143c49840d581643c410038040c0d0007607041541c40303041e45040c2c98041210b41c0e2070401d0070555420220125020890901c56401d041c10703580d035825002020f909050f800c0c4514079815019451008040000c199080810050002100c51511610f0740001c1003070081103a103440710078668050601e5a0002d0181903080e850000d007008203c50040c8680e150404d80400c031051a03241a2040c039924681c042100d100040c424400c00703100d80e400b9a10b180d00d50b405c5160940c0c01d14401c040c401400e00040c849902405400e180420465403941000684c1041e0070301c05851807461184807035498012204030115542e04010303800c2c032004100390103103056911240305a0450706c0c20341d0902c54034101440090042444440180482c0800800c036a0500d01022 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 706157607 1250 706156357 706156403
    0x70305061216090b0d08090907091205030d0e0613061a09040605010504050117030328091103060a1a0d1704080709060b16020114130305010b09070309030912 69
    0x40d14038480c1145050801c02180f440c4550710103200c1c21101842c0d0b0440e5525400d00c28080d02d0803152043d044107010481040c0039074105002042c0108000b9652003c80c1030064480e0003084c805501c241c240075181e04a5180801c81a2245451039000e00c10904680c5a0100034462454400e1030741c1c0c2d2082d1140c00c190345030030400740b190f44140f2001c1007640c1400d05100030707160103038000c48034031a03d0700b060076034403201209507540300d441d000c150b00d11816610144400a500482e84541051130199810b0501c0000039140c100ca00d0241d0440e00d0a49407047c080040301d141400c0860445140318804245180140074510414080c000070900b00050f1801603149501980c0944500ea010150400945106000b004014440b0101e61801c00141e60704881560b1203045000781084504c1c80304101d03041e20790742660420008010b5200300d0903120702e00380e8000c110340c42d103140c402e8002e480004c1105100340500c040040c0d0540e100840181340c0700c2c0d498410508180105c07908118180000b04010150b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 706158857 1250 706157607 706157623
    0x20d0f02130e01020d0b010219110a150e04050705190e060c0712210504060e040e07181a010c080a030605090c03180d02071712070f1502120703050612 66
    0x91000590b500f0034035680d00111041080b146065420051920410030000480c54004a400c000e0ac0c041c0b41d021100041c84811a1f0b801c00c2c2850b82da465031208401d03600141e40d528400c41a20104140d44440300f040d50940581401500b0b08500302d59013141d407d00c41c031010946450050801c5040c40865003141d41483e81c0c81d004a00c05241041c081c00038003444030f00070045000c0540401d40411940c20009119115500494041c482c540b259208642c0350795020342d41d41080f203015242c82c16100c20740d44a2403191000e8140c0e000342020345040e0100c032800c4c46541800f2058407914030070001039550340180e4000000c48000d2541d00c0c840001d5a482e00003002e031050560302d85407030303482c54151407000900785055518102c03030380001440c3e141141c000a411044d20041c444a011289441d03921514003140880722408840c0e01280c4001044207080404906621540220b03000961041c025400c0b40103030207003410764854501c0400d800501a5005a0b0410005002108160005001e55190240b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 706160107 1250 706158857 706158881
    0x70c05040e0f060f04020108040b190609020c071703030103020906180901062d0621020424020303040803060d0f140d080105030f0304091508070902070506060409020d0f0213 76
    0x1503001114010b40901115501c1400d04011070304506054000a2140034000d00c002e080381c2200c0c000c218281c1c980551503406807444030b03080c807a15031242400c02c0030303400260200440e449807490100b00c0382803c40d41e0f84460b1040c0f000441c1980c0c0f840d001c0081451024020321382020b20501003010380d40310940703039610910683d000802c16500e00304806003014081680d45003260030022800070448808501134003150b29a1034003410551a552090f81101d82e92582c0610356840090002031001e90140403201d2401317840c1010401d04801c90f000d0780c8074482118001d10982042002852504e0100040c4100900030551103544803e10350300c190712100600108010b60340015055000315a221098a000d0070301540940003102103458050354900990041c10103003a100c0d0521240e5000408048004008007070488401c240da8410030802940850401d44440c02180005002f50400e401084041a4098007500c0729924035114500e5604c1200000caa0212850b030401b15190b407903004081803910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 706161357 1250 706160107 706160113
    0x131506080c0405010509060d0303270c05030303040506130312090302011a0402040602030a030905010b21101a19030b1f090c05090105031302090f092a06070c05040e 72
    0xc103109440d4a0308484456603440b81c0e00344030060041d030302d8216950781c002c0010341c2e11110b4084149001d40140002c0c02d561b6400d503514503c00300e810b0303910480401c8441e018481c0c6035540ea44520506031248000c0301e01030603d5000310086038401892101d03001c071140c0079181850141c201030528200b178402c000e030140c00507034650b0514400b0781c490030000141c0301b60442e41140303403500d04100a03480340103944c0f881d002d06586548484c01e01c0020740201058034002000748145451400a5044543c1e00700b110a80c107105d80d14010002140380d00c6041825402c5012114822060070104980710110340d81d50101015050030000003d1490340340d840c0182a8468400404405403040d65403281e007a9101101c90360030030005070042c2c1d8000f0200c0300c0607036007841c1c0340b55655100782d0001d515002c2443c000350004044d000308040000d903000410f0151a0301429140c0482845502d025048030745010001d40c4800c20558418500c1d004000b810090b200300500c4445903034541c0020111042c114400c04160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 706162607 1250 706161357 706161359
    0x705150409140f07020f07051507080723190f140d021b010810060503220b180609100507110102130f0f1208070303021b0f01051005010c060203131506 66
    0xc060b843e02d040d8003405a1000b8001c04a010384115030381c80035445168051034401181107001c4106500301c51030740c3d811602c5a517903800359240c9105402c503003041a800d00c0d0307044100001c4c1c001021640202040c045d006400030802103840381205008030300c40c1103440b1203445042058500d81030081517601c1285401030b260b00e010203241200340c0040d034103229041150100c10840c0401e0707465001e4040e5004c61421725101e603111080f140e031284c0c28000300840b143d1200d404008110345144400c4c8120090b00d1981c4182d222039a1316946c440c401e560341980c40d00013104094048880342c0c080e941c451445c1c500b000400c0681c565081c04c9070300455000c01201ca4014003804151403049a120042048550241c00149001d40607003600c0540540180020b800041b5002414860b405036444d507a071060150004029000c02950740b50241c58501c201c2c0d5003040005104c11888504410440388182c507403600640300359607110000d40c0000c0a0b038400c100e4070b10f0f094000c100c14440d0300350342c1401c03a00001545 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 706163857 1250 706162607 706162621
    0x402150c0a051b0103020f04140a0305060a020421020f01080a0b0a0810050f0f04080a032003060307060503010510030f0e070f0f050a14060c070e1302150309070515040914 75
    0xc43d403a16906060500401134240b80c503010030101c6085881d24464203000070b03024400600640c00070b0341302a180341706080500c40c081541c1d60080c41200d0200900030340311910206403250012890340065400b04801e00c15483c154012a41c00c2da000d1010903001640b481c06c1c80002e40441d82e00e42000440360b0204100340ba481000e0700c05d403500404425140c201615102b64101100310780104001d2000340c01103078208081e0f00940040c1070498090307080c011145030101c00c04110340c004842482c072a03c128a40001d0711402041140c0c143c42d4003524052035079400103015009071078500500ea290b00e41d120101403030400d01380016805000d02502004215103003030f0b1203210070041a00f11030f104510a28040020301809280c02c495200b0a03034049483c2c46003806114203103a19540b200f4401345a05040081940c00c0d020b444000e030303200b141d41100c5110005440421400100d400c00a5580034180034002403802e0302036020040b10054180b4642601d40328148103503202c040d20302c2c10241c880c2d405d00c111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 706165107 1250 706163857 706163893
    0xb040302010219020d14100203010e060f040c0905010e120a0812091c031d2b09051302030624130602030c060a0c03150e090706170402150c0a05 63
    0x11881610030f0784400d100b2140c0004200d02c0621400600300800c510102e40706400074066542d5030100b0440440d00c0e5a0349a0388041e4005040f40c07054402c122024080000f032400d44100000107171180c2e0742034000e508000c015a04828165085030348400c400914001c9000304120800340a0300c0742047d07035140c00d400d00401c010030380d0141240c03501c2e40007400c00d13203426014000c00600b2544240b6012074059860390752040e000b01190800c982e05e0141511089840d80e0b5511142c1c0004c400584c04581c29410220071210344040e8054251b012819580c1d503124150300750007554200070300428012448903c50b030a4059088084941a1880d00105124040c00c410804c200010310281c0043c51500c13054550362511407000401e5203000564401544003020b200f58032510078100310b1040200c1442e1507068160f01c40d1400c41e0a45410700c0390002c0402c18511405038907900043c4c010000c25281c4a0b039003084000ca00c0c0f8400307900e281c3c04c1400300e00c5107004200101d40b4800c3c0540d024100190303d0402070b0704 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 706166357 1250 706165107 706165123
    0x4080a110d0b070c0807051608070b040f120201050913090c050103020f09010c050f031303150209100c0302030f18090703020307120e190c080105061903080a030b09010b0403020102 79
    0x11154849000038000720b5566451154000c070305142000101d0964988190303a406121009001071140c10f40032810280ca00e0704440540d03481c2c00071200700d1540c800c00e9040760b01c920301030905880000c0d5020090241c0560403607455031b105041c00381c00c000d0b00c4004204829428405d071164292580c41540920000c03860322801717041c0070300c3c055142170000c1c0020034861240e58540303810048604101001e001c2d0030300002815114280990ba681c0c802494054082c140500003502c0c402c0100142030003004442c0300311400d00502a01c00454a402080151011054050300394154041007101d004074440070740042c16424804240d11402040340003e2101c040700c02018081850b104000f44000d8a80004800c0400e890544020410340c000a80e0942001c0d0051017040d0300307061503c1a603080080d408140c0090702c451a0080249030340341c1d01001521007034040e0101254242400078000704841000a06084045d4180414643c501d480460090ba000741d000060107540480c0a004541c0d05022a00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 706167607 1250 706166357 706166359
    0x3016080c1e01060501080f09011407020a060b0906010207061805060307050a170c18030a020909030c150c0d0f1b0302180103020c0601260607020c090106021c0f020304090204080a11 79
    0xf460410f40060940341d0040c100c10b46007022100043c107444025000080382840070b01d03545600b0304000c00041d42d5000c00da40c08985180c28007000c0322050a00b800558070038101640140026458150181d91000e00800c0c0000481106600842c1545481d0b0046000320403e65038155600c00c59003000b0000342c90f2802d02400c5540d80350502080c40d40c0a41038400401c009052028030004650000c2d1030040d0780c0100079085180c890400500c0403010028100b40503419040e1030002d200c214216091a000b26413403108401e05100760411048140d0003105440503203c00007071500e00d005020303d89618440a9080040e4000613031040d5214001c580c0d8030324031020b08041d810040007603d09616003205024081900e510080c000164030b904034030030842401c41c002519018184002d0080d2039886034010140115004400001c0c403a100041003502c1074450003018101140300c0034101ca110016400c4e0f03c003144810b00c40420b840310148001c01c02050b280b0001d00c3d034820f00785050000c01017010700c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 706168857 1250 706167607 706167611
    0xc15031109150a0314040f05010606050307120506010c210201180818042d2a0f20030306120a0f0b1003140a053016080c1e01 55
    0x4065803241c0118659201018810780c0e15083c2c0000d04600030091001400300090201d0244001e00201c805180c0d001030280d8002d100c141e440fa06d0030f855030b1005036541000164001c803800760420541d0f001c25003100301407500300c81c07120903622500458150365042945c014076194024217115024400d405078100c2d0140040c503a03040c0c507207030351030705010b9143c0000100b100441e000700c480d40e0705d03440300c8009117000d010901c101d007080001d034040300e02080c4101641858400c000c0c0c413503074509075000704125040f074000110b01f503030360002ca42500156003545c00340425901c1e6035103040450300240e150000000025a1031f4580b0008102901500460140c4d40750000c2c4011808201030780e80444000d030300031680780701ca074075107070f0351003030110690342c0090440491100b0a50400b080402c2c070940b000d00035021215034846240702c0e0a42c034090400b42c280d1207000d0380d07005c0e5842040c0c0c2001c0c2c03000c80008010002c20034400d850b410141d074803442019085400c04000100100c40380568204958004402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 706170107 1250 706168857 706168867
    0x130602060106020c01050c07080115030c0902180d03020109021f090b03100326070b042303030a18060c1709150109050903090a0f0f050301110301060e010c0c150311 72
    0x280d00c59011390001ea04200002172481d201c0402000500001c0003084000c006c1400403034012507902030035000442e400041440000b0350302685000780c40e07a00c400100851030b220b6800040100d000d00414080701555203816100c030243e44d40d1034488200b9400d00c1c003c4001c010f02c142c40203203440c107a030700600f40710b003004e0040c819505000c50400c1d05036940611091151a180b10044ac2c250401032003040303c4201c0001c104007002080800d00e805a4842c1c6450300302d01640280103a640c2500c20a2400998010300018680c1286600400a0859115101c0101201302d403900410b4400c0c005034480801c464041c4c0c06280401d10401c154001c8001001e082c0c0f050104050001205041c410b81c991583c80d0f201082034030005004030750107910300400782c1d616143d03148850320324540c55100c1e40d50500e640800001300c600381070081511848003500490b10b941c0c00d214058600c0c22041c050b071410813038003030b20920014919556402c0a09807450310640b003940700540c01800c1e80e40c1c0700714080d00d8102c1802 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 706171357 1250 706170107 706170119
    0x6050a0807080a020108180d051809041101180902031e18190c050618011b0302071e030203060403030509011802013213080c040b010206070c0c0b030c1306020601 71
    0xfa078114100d03070928103002c5135221141d801d10b40350008900b8070068024002840d000d5074129004010010041004501d0300950104000c0180e07001c0f10041d008110400c0030042d150312032091401201000e0041e50705254841d156001240c000b2160801c09010720320540c051802c9500320180d001c2802284101c00320b042030034076615500c0313203141491074045401c0798004012944003d2006041e010b420030b5100d014200725558802d4488000b1408107045a130051181c041c00c4600340001c6030150000d010540c0f82144400104240c0400508030803440c0301c012005036018012107000d64025500426681032110003142120f80703981d0114005192441200010703600701c000411068454a40b071102840107a41003611325004c840d00c240c809c2d400107010003140c140ac0c1c2052043e40c0300802111200b600f00400d00c021501414103090140c2e010703d0003d208a8810000f100620703104840c80c00f07006545002007529034205a0700102100408104520100b00c11038403c0000c140b544010701381035241c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 706172607 1250 706171357 706171363
    0x606040c091a0f1c1406060f0c0309030a05070e01140a0b090d020301060801091401060e01150207080a030302180d0305030c071e1101020d050306060d0e011401060306050a080708 78
    0x44a491041646242c2c4000c1c11002001500d91200e1207414032642c1c4d166400c82c003a642105001001c5410b441c051807a2448040582154854400a01100c4c07404443e621300c50041d03002695860010700c000c20003500b258034203124480c0c841e44104000c0c401a41460409681068141c01620682003810030044c082d6032080712220854a506649550b40d0301c268012459026a0380800780d0190300b4014006403091056021840c00c0d809000c03541c80e030401e0b4961180c261001d40c03081d0f81200500c01c0060140d1078511404500d028030324012104025078a0214604000b452a4154040b96020800502002506110340c9065004841f9104a000a560060f1450002400113103a081c0080781400c20400445480d50001d403405c0c0440381f03001c54500e803c2c500c1110b900c034803034014000d41da690401c07103000d181580d006007402000c2d41d0400c0910711500000302100c50071340743c4640d241c201100c01845810099406425159808a40f05050900b84540d520450740311002e190700c00541001141408 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 706173857 1250 706172607 706172609
    0x170c0a06030504030c0b09031c140a0c05040306060806060907170c13031506061b0308070c0f150b03010c0e0303070b0402180a0b01020705090108030d0e012c0606040c09 74
    0x340c10000744944a504084918400354400100500011003d00400c21400400380c480c1b00561000407080d2495643c001045d1405401031300c600701c0d8201c010501650a68015010b001200d140540c00e059903a19800103503030160344103860b242c00c608184101801c1c103940460b80b02015003080d00c00800711b90502142510f004124154608010481890101c0c103032030000011500b216041440b50340d091a21002003401d40318110109a04072000140710545d08800c1442c56019110380d58141d84007502965104e000071011522600c500b00c00a001900d003a00e180c0c0314000c40103000031498120000c0c142151010407074034090028603207803840942c1d8004100c0d0f018075840300706070360161100c3c804607400d40c9540c401c00402200030400c01c020403100d54400714111001b64210381c1950707620300601c10102403e00944030f00790020070140e074401200e60800060001040000191032070000c00c0788512160074414121900079454030310484180420401d5000a82201c0c01c101400f14410090104030603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 706175107 1250 706173857 706173869
    0x70210031415211e0c1c080a05030604022119150b0903070801060623091005310e100b1c0b0402161a01060212090411040f170c0a 57
    0x2d44401031010500901c2000c110444003d008508402d84e0314503543c03113446000b10a0b004a00070b080030072480400d540b01c03030076441c0c2101c5a9440c143c4c10300b80403205070b80700801a9401a80800c2a00c1c4c040d88007101c0860810032114081c03145040c401d00e003000040c45d00400350580340c10103150300c40c1640034100300b072708032024250016076400140c4d000c03030305204443d4004049035107860740014105400840c1310507019451504640c0541c0e4201a890070b46c001c2200060304861074080781040d00d0b020354001d02c6035240811542d029081401000881c100540d0070048371401d00b42030402411100a441c40e4014031042201c415160400c4e01841d401d002c4c01a0101a2080c400386504060003a640300088215000e40107550380c1c0c0d04901924510b511481003101c400d1803440e40090440f40d0b1400c100d06a8125901800c440307031204d4001c00003a0048107915500a55a03101c0403c0400c09100038001000499240050f840c038151000040011072041002c540e040100702c801e2903036480c4c0d10304080e105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 706176357 1250 706175107 706175149
    0x60316080f0906011511030d0b120109030909020d0f0603110f0d11010c031701080105100e19021803010e010914060c0909070e1e04050615030406050705070210031415 73
    0x4070002c0c11106c10240d54050010390000143d10401003805800007036441d0400d032404460f52450611075400c03540c607003078007400046164000740100c107081d0700100085001190046a610440f082c8041107404c1a8002c6071001600030140780a0b0030400350111020320100c0350900c1d2009203845e05c02c030f200d251010040c104403811010380d0800d8000c00b030f1200c003085441d281910a685510b0294028842583d00080b404d030507000c001402046200303034511030100300003503004001800240c41c002e500200c0584074071020101c9000a10b4400f480364034610100c550001c2003004840c144103603146034620b03c0c00701c5508810100300109240004440d0f04004c00c2d549408265a87c0c0d800300d4034481e81d520030035031102d4140000d18959000b000c03e00c0794890f088804000710340b182010400301c440700e1040c050b400841880060003140b15548040e81c88083c504160780351051550003d4801407440500101003940c0d520202c1d03408820b0000310358420060844611012540d800050580032001c00d81e03041c0320 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 706177607 1250 706176357 706176389
    0x506060f0f03130b16090f2601061208180a080a0305030402030115030f330902031212040b060a0b0319200c150402061215060316080f090601 62
    0x1034809140e03d1100e4026507000c0a43c1000142e00032050900035154000450060000c02d080200d402d025088804445050100880c210070a240030102e454805940d0355840b580012000a03081d891914130384940030f840e0762240303004810454032601e0a906406400c001a040c000c4840000b001c500a80d09818200c1d100d56503440064003501480000905900000f1000001c0022504004181c01c1c8500c4814803043d0103078404c1c2c2c1c01310f12a510000d10764010358682c41c0c1da094180e4410800d0307600150580340360809080300c41c51981c0c00300c2080d95220066008000034800c10340140344d000711044410030907180c80d060b261401170001a110520b13100c091944200c000d940d036840b1140b10010171480222492035620040848d07005085106114050060b0b40460b8141c000ca0041c482c560051000d400c00d400155042109203005001201048031940c56090690f62440690700c174032490941e401c0c1004100d08002c00c00400a0090604103545200340210310b000811200e066a00b0103451010706 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 706178857 1250 706177607 706177621
    0x61b0c03020d0c0503010e0d09290a080105030f0a12052b1a030601031505312108010911120c090102011104060c0b180d080603010506060f0f03 63
    0x1011603903000961101c0e05401480c01c0107001400c080444808a008102008000040301d80310010802424009140ca09013840109110704002c07a0b560000c0340050004880c224048820340c1c845071030800440c2c650401002141783c00c11004d00074540e08030207423040d0890781c1e0340d150408080305201d40900c04081044540c0c18491800350103030158030a01d50340c144940211210007043c1d124510303084800141111050303400c0c00515281280c1d80101c2c2e41e045600040f407100010103020303000001c01c40c0c1c441c0c50101210207540d00c07034402d510146021150714151b841c080e51207912801d500b01c00d918403404010074440d08201c125044589216000c183c41e280c54005140500c83c0d9486080b8041c100f10a1004014804000c1c0c1280c4400b0780003000000e00c0d5a90007203503030045204e000e00140c194422500011400c071b0b51150840c3c801d102c000511035420780041d00305071081d0301010004104100f0080700d4503003406807a4103c2015682c1a213481d010b080006c68a103d40c2d09121142d20f40007004c101b003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706180107 1250 706178857 706178873
    0x10501031e05130b06040b0105040e040201020a0506010303090503060f070806040f1b051c05090307030c11090c0304061401080d0c33060506090d030e0a0305010c02010b01020f07061b 80
    0x44100c1c090100440d1400000ca520020807151040d15120540d0380000d4050529200e002c4c12450161510741c10245086e016618002c00200100c0c1140035096840000030000c1000d40c9c0618800d0306d03006856428401070620b03103680200307449208240c1d28103100f00d05800c0019503030009030030ba0f804a04003003d1100f410180141c500e0790440e110380b0b50540c102d800c0d80500501941c44c4200e0703e904410110b49a80015030b10144c030701071500e0f002040110000303030203040000c2c907580c13050720001505429800003e0034504201d40c554014100001000300b04011880b0320b40c1ca402c81e24030010079550400c510203540b054400c040e02c081c0a0401664000d0003800105c025168000c0d5513401c8050304040761099000d011101c6031380509080c03003400700d06031600c131040c0e8003011b01c0540030040745600303030b20103d440b100800780380b5400c04003010011010601c280500e00030507007190000320780004c065000a07d40300b01945808031036003000b80103010b0298854015181030003540c0d000d20f0880018108151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706181357 1250 706180107 706180151
    0xa05090403020f0709151e0b160c091b0305010f0605180301150f0e0403080408090616050d1b20150a0f2a0311030f07111c080301050103 60
    0x301a02c81c104c800203040e60150072040c0600900304a0350411556a5040d0380001c140d1100802c4502c0b042105020041031180900300303040c06101ba0a50f54400782e01d803060440c00036040080e41c180c880e11100d8681607120034205220016240401c1258506160300020844601440c402c02400003103c403010300f00d080c080d550040000703000f0400d10114003141c501c8a0707580e01c10f107184013074110700010b9000441000c06200d44d4040e2140c008581d15a0381c6c6040c02d50256020315404482071000303001c04101e00b203c48050307a01c40d10091a00c903841c0180540384000c100000d91016410300001d4002448154880030102800381c040c0050183c2000010301c484880c2c002200360b40404036150f00d5007a0702c00b40b0000301034002c0c0c407042c40014844500c02d6070780c150074140c80d100890400180001a1152952400200d0301106403401c003c07000c404010158822402030b1003d80d60f00442240c1c03490010546083c482c221000c40710300101d0350341d5000c03180c001403065605045d0b85201040400202c003507148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706182607 1250 706181357 706181383
    0x30d23130e090d140f1b0607080105090a2003100b071b05011d12030f0d05310b071b0302150c04061202070602070f030512090c0a0509040302 62
    0x8101191a100c04040c01c2204942031042441001250300840d40580078859002031460b40143c41c4c440d4070140030740680c0c010f242c1c100c4031302c1246c105d2000c003900c1440050700852090703940d440e0355450301c82080388807030002e8001f208013441c00d10ba06880901c0468142105003401d070009480b540e0f8445148400e28450b0300c0b039050004002034905c20400b1098915140b00d83e01c408214800d41c8a0380112119450404c07501c00039603108441300034500e0852500e0b81c080898008503031502c200e1100d0720310640c01185810a8940d1204180700d031003c060281c09402035980007a099040410009040440520f000040c0c04440d40c5408116458819012600da81c50603021030035140a50f842c0c025650360700c000303640341c4203101e0318042103044016030121401c98a070341d51280841c1030340014440080d80460003c4400316400c00007080021200c003514100e190003611096294040c2c00462009900001d2010b086900303d0f00081c41380d990303641c110b1030070382e081507810b802c180c1c0d6a8034080c3d25100000c2600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706183857 1250 706182607 706182637
    0xf23040212070930050115080a0c0509070912080f070b0124050a03020c0106051e21100f14150a0509010e06060c0307150507030605030d23 61
    0x740da4254034081c5004030142c1d50b881a020340d07501030686000c2e81e40960142d18032203020491401200302d40e40b03103003070900450000488050b07810101c5071001807940b1090194224410003428040f4000841d401080b054442200500d404500145040c41c0f48c000c009081c00010700c03460a108004d0300341d0b1022054480f41c66900c034071502303002e41908424400c026100104c48074011000c106511030055800c01038540a04111810b44290040c4d001440c242b020340d965054009060750301c00a45000744501081c0c9155110650f00c1481400100b04002e1003910b012048080d10904000034208910f001e1124000390480c81c503000c000c05058108a4418610050010722218a882140c84100904111444c03806030741c0c2d40040c40b01c80f01c000d00c101c145107102c0d50000740385030405c0c01c010403000c00010150780c0f4040203941d60381f030040c40a6101600507959041008600d54052180e54082d003011030041c000071044880040c24000400303070071200c410f00207a9900760340345480b0135102010301e42058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706185107 1250 706183857 706183867
    0x180304030f0c1502030702030a11181806160203180402160506010f12052a060703090f062d030b12100c03141503031308031c05010f230402 61
    0x3104201600c0c50003510880c03482040240031181c0004120386c846540035000e801e2600d0715481c1d07144640d92505800360000740266180a000e01d240c00e145105001130207030b2440422505181c035140941c0140710500c6e81000c1c280c21683c2540000c10788601d005c0d00385c058617480449002060103400f40c1c1e0520800c1e41c0b0400102020004041545411382d007420f151803500759550b5024075a070075072048001d405500082c0004a800c0d103070380c62554904810004000340348001d40041059540066402d070001014031005000c5004c403401c001006200914102044800c0f14004100a0191081041c1d541c40e518682c600601e00036089919403c9000b400c5400d41b6140070120341e00c03500c0c0384901200c41072030499500100e501900c20111106003040554030035650b4400c050000800710300e4900d505200a014941140842268880150802501075501d80303807459641c84194100a02401c8000d042400600c000b0003514044812900f00390300c80d030f540303807927851701006034031509400725070024000a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706186357 1250 706185107 706185113
    0x82b1209030e030c04200c0a1e05010506060708040e281a09010b1b011e09021f020607120603080406180e01030506010306020c0f0f0c15090306180304030f 68
    0x340300b082d0481c10350544841e161a0800c001c01c0b02e100d1241d801ca0304840843e150500b01d0000302500d20a180c00307045980244a544078110000d101180d85100585c40443d1042001028003c05410400a0300c0d51800e02043d40d0300c4581e24000e43c010302d410500300400160803070705044a1419000c22040409800080c541c603000d01500001e804040400080d28026030142012204603040f11240000d49040540114240c041203070381c150720300065929101c1ea080b6199444900038589a429980001c483e1200c0c030501906602c181c0e41152103442c200440d81c078007034000c145617511400b1440c09900c1c00c4195071500c402010b0940000d841d140300400d011030030341c1d001441850110701103603040c08601c0d030329032440031400000d020041c0035030444001000011115000741c981000f0030400e56500c80b400105561500845404016540d8000702025016091084070081400821510b141c070300503880011070790700ca0000d4a130032005110f5010b0304000741c20500544000d0359014015981621140c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706187607 1250 706186357 706186367
    0x1602090702030a0e0f0612040312050a150509060a0501110f0609010c09170a06020f040806070806040507030e0a020603040521030402012d12060f0b070c082b120903 72
    0x209000041a0320080c11311040c03505500403c0750071002440b1500e172807000d004c40d410b122405841141484040c10101d441440140070311480b40a02c1c84001582252400710784194840c607a1005020710f8106080c0700d05d03606c07010044026120300f800c01a6070801582d4041e0f161405580064000d40907410610502c00019045030314241003903aa0a10301503281c0c4c0e001611501d810b0401ea456034040c01c180c0b07000506507005440b1103040b0036010b50810740d882c05040e04201081700c2d441c0005007140c04102c0315142501c0b4503500400d02d0314041089a82407240c442e42c4414541000e80315500203c005002c02c1130402061410031070240900c1890621070010940d150400e807003c13804210040540ca00b5804d0b11b135404c0c000c995000b060a85002201c1d84244c0e4240031409075508101d4a1311000704008801d61090710040601280280e5500d1032800c1c040300000c000d800c60409600450310705020180c560700d06480f083d00c21403840654100c50601a2006090035488184050514001005040d006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706188857 1250 706187607 706187617
    0x605161410090203010605090609011703090409060c080a0227120d08100602031c151e050411070305030708090c030a1410060b1b0f060c0417010203011505160209070203 74
    0xb5002131010b1b9844400700a2920403c03202c1c20b41000280c00100581c241c0035105a1900c1500c00031b030b03481e04403000041000d595821006032041515880c5000880e540a45130b940c1c8190030101c114240000b00890000801d800c0c01c0b00210380181030440800e540d90902010220f6030028111030304901c40344005095000f084a5484e266400d18400040d0705001000726803000d03a20003400f03007100c0c5982180c1c0c8010110650b9003019103c40203004281080c1007818401c14885c884201509140740200300b009403490b5010810810609100e8200003941140c1506e802010700d0030300410903074600e800a890040f4003a015585441000102c805002c181c1d0440ca800381c8041e015a50300074060030045003550610b1286200180003000300300468068017119840e030860b10720545001c1401c000c081c91510409551005042c18001010414400403101169a8842c498004c1d406c66141926464040a41185110134403800064042074001c0c034032041d00c4040c2c1c0c020308880302401c004800941d0390f048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706190107 1250 706188857 706188859
    0x306150c0804120f1703040209010909080d060f05040e0102040b030f0601120f06060e01050a0c02090c12010f05180903180d080a020d030507020a0c090c02011503080711010906051614100902 83
    0x113401e00380061125005c11203120790b03009042d010881e481e00b0707070940003825441c5c4241c03151b2005002100042e07095000c0c100003840320682c0009034500348400c201c02c80d0b083c90034416031031384104030130807c168203076003604c1c1c4c408115501c01303009943c2c01005940120600c485000400d140030b0302404102015031010b400e41708580c0d1581c108081d02001544c80780300310010440411008907034000146460301000f98041c02e5100302d107080a000c03555480500e1400e0b0014451a40b40010610040c244035040800a940c42010000d4a003072450145445c3e00c510344140000600100c03e1002c142c0714031210420840e4040015542c07005034090003500c8040c180c250000103810000407880203031000404581d070a802810504c07a0034170b802e1441c4010f11148141200b0342d5200e24100e0220a61b108420004501481caa9a6201a145440741e040d140411a01e07051145045042c030403170741e201d016560303a10581c0080704a200e0040c1840544460000d0102c82640b1800401c0c0250f4030300c54019844a030300c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706191357 1250 706190107 706190123
    0x306020a09141002100507112e0b030c240a2a080406030e0c1002060403080117151306090302030706050a050112030f0e1009030b1b270607030f0f0306150c0804120f 72
    0x751407010310540d0020031a2b2641740d401120f00c2d07a40c5183c2600c071f0805a200c2485210403c01e29a03001d16820b8210300415000f040c41103943c9541c4d03000c0c0c0d14080e44034541c0f2591000351035019030f403100250702481c00355004060340c038181210070b604108902494010f004000301c80034081041c000350344150488044002640e044000190002060f801101025031500903045825100450000d400d0b0b00405ca05031140ca0030f042c04020400b40d1080d4005140240d0255648030100d01b009410740b00301804184c9558600300040000e0142c00191030040f076403502e0003940a041000c1c040360010401500d50b980700c0c182200752078880380c00482000890f84120a07003039003035689000c0943d01c0d0360740301911150107804004180c0405100c0d58601d241d081c1c0c3d42898125000a100840c6040d001601c04401080425290729500d542102008c50080100d24042c403215082400c0910101d0f04e9040c003a0521440030010010801a00c1c1514050035103046a2401c154003400c014092814440096030490 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706192607 1250 706191357 706191433
    0x180d030c03212a020d080a021c090303061d01030302060105061605010e0606030d05040b09120a1410060e070c02090717150114030c1606060306020a0914100210050711 73
    0x50000c1350751721800c2d81e9a00c6240309079540c003620b40c0196000d5007011900415044040000b1103040c4545460b09019540000e502e500303141842a201407502d0b001c0e05102441801040003079030004403281501c0054641035110b10300160110302040d0a01c4c40145154223102852415810006409120380c600f14100c2c0d4048080c1e002c103903010301c01ca001c2c0007802101080300c1c22860070100d0031160b000d14040200d4402c9686900c0314004841e140b61410010342010305c800d01802414022400501b03942845a1018144140c01804003c00b00000030b00a0a1840002d2201b41c010221001c043c035140060043c40e16140802a9091006030030b8640401c0309204151600f2080805581c4a400c0d60314446140150102c094a40b4424a000445c0d04035142c0c0004400642c69002800603810f494035403084103400d00c91a4000241c0303007603103d030103401c1c175410b036903c8154002a03500c1010080030340060707a511212011034501002c031066500c0380c070540d40e90481d40307901401d1100143c0c1d11009102c09038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706193857 1250 706192607 706192691
    0x40c051e030a060b0310060b0d05060a0503030304080306041508060a0b03031b03070b0f0c070609110402040b030a05010b0a02190c330804031202030907170102180d030c0321 76
    0x13103087d4011184a20024001c1000c0074606a00050704884024208040e80341d03100000307451035004580817141e0600220601c001402d150003101d180600c01300d02442c6440c1400360569a5900051034003000903281c1c44401600d850900c110384002600040c50341c0d4510300d0907000c541e031781d0000004942e0034030020700207002000d22041060003182c250071107a1030071100392900c0c0c01504007200160b41c5444060345000d80ca80d294401000203201e4426035030b48910b04203800c2021150143c3c018000d52800700811a145a801702d5810b55480b513091001448005604100ba404185a0404d0f1240c0d000c0e000c800410000d2419025041142c042100c0110105184100c0302c07110309480080201d0300e43e0030f128240440e10380285900150850031243304695407580b20300c0700c0204200b4a43d56950006400c440d0121500c01d03044901e03030540320071110700340e2580d000303100540d00c400240c20800d076600c01d89400059482c40c9000c00340182c80a1000e8012200e405119214004070900100d812031184003003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706195107 1250 706193857 706193861
    0xf09052a030a1e0c0e131e0206220509010602010e06091506130e0d0e030f070f0504050c040308031e070e0102070b03060406050a120b010e040c051e030a060b0310 71
    0x2003940d00600380f003ca5882e400c0680c8842050440843e02d003a4489400701ea1070f059411014456600c1c4020400c40034080d00300040c080c80400000481d200c0b1004501c00543c03640402c940c0e4951140568071608010400303041540f403020380000b540013040100000764540d05410455200103c0016546544c54040c0c85035541c2c1820281e1041c060407200004400d4640010b140300c4010301c0f9007010844d605402c07100c6003041c8000c02e4050104502c5001d00360581001c014806c410361800009149841c105080e03059000501e02c6110310441d01ca0000645188036003040d140190360101c2c4090b202e04105d06011010381c0a070324400909000c010000b003900340300b200c40900000c8103801400982e03013040300100d41940010940754200352125400261130b1101c2480000815085004080849181c5020404004103900007031807160300100b0f002c0410400e4001d141200c82c11124407074103803481800480040c4100a000345e1600512030b015003800f5054104008a41e021004d45070064818407000301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706196357 1250 706195107 706195123
    0x20d0e0c0405100f090b120a1a01080f03040b0708130b070b07030c0e04151503020c070e22050114130605070201020f04091107020604030804091802130f09052a03 71
    0xc451180300010880000554800c140304540940300f5044421010181890407003808c0c800c5030034058074a80100c14420362040540074021040c050080c004009507525620f024a01824015600000d8454200078805044481110801c0c20041402d65541c018500035040319205031401070350280003a104501c28410b101410b0300c01e4079041005142002480010102e14a003110400c43d65500440e075601403003100c02e980183c0f80d0700940e840000b10b00d418240700d125401001c0001002d01480080052401c0c04400d0a42c4d54a1855000c9410709100c0d001d41002d1650b4286000c009041c080750a46202c4001d01c1c40703000300001d0140b03427a500b40807401c0344240c145041c0c0114050009200344141a005000c1c81c81b82c04054505107010b0360000369040c0d10a51045400c014000340401008005014138000351518940c04000d0321116004110512034074814070360f5095603407150007002001c941c402c2100b0303a0407000b280d6021502403480c3c80225880b05280303903072100d11450071560386000103280f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706197607 1250 706196357 706196369
    0x70807050409120c050a06020465071217010320040e1b090c040b03010b0a021009150f060f050d051c03050103030e0102011b05030604020d0e0c040510 66
    0x5030401c540f408040700c9a0240140440b8540036010a08000c0317030150000c3c1010700303609400340c000691040e0130f0401e80c98140514041d850320701401c50205c8001c1010314002440700305481500010030b461680c0c0f01448207803010030384810100d0380c5414020704103c0c1c00b0282c807243c1c850281c89440c204501007945030074400105030018407543c145800c81c1c03010140e00e0b48040a0404104001038200c03990912200c100d4803841c51403503009029291130400f115039082444e07a241e061510382001e00c21040791005004080d031100001074581500c620070880a40c0d82c404c541c004010b0300c030f00ca241c42264549c401980c611030504103c0c8051100c030041c4160307021140c00140b0b003000d20780760000340600d0340c204c2e220681d2030340913401c2c0b15103000f200f04881c40c10718020f958001807103606501d006010b2180842d88581160700d0041c142c8120341542440310017404071420140c1e12a59000000b802038858000c0351141c59050440907114408001000c580f01c1030116814010380da10482d55002a0300c55110f10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706198857 1250 706197607 706197623
    0x801060b0307032d1e050c070c0f0b030c0a0e0303030906040605010b161101020703021c150902090406050603030c010c050c070b0f04210605011211030c0a061817070807050409 77
    0x113415507401d281c0c007180d1080150000d244c090000c40100301e003240c400312451003c40c20002213440030030114401c030b280541541314031302140b141445038212150000500460500720009940c81c425401800340211201c0b004046035aa403070681e105680760310003a201102e806080c000082a040d06140c1580c9010080d4610390454503601d031540c00c0710305050304d8114107501401700040096100c3c09003103001c0310311b0030400e0350011885203000c000745250824007070501c501c0c1c8003103100141e446002d8290001d411078000700307103521003800090642c469001d48890b19880d0400c00e480b42d0340c0240242040142034000d9410156030380840c1d80b65413248013048418034034104824800c0c82190307012980105821845001001e141e940e8803c115142071304401050035592907280104500c1e0006409250029005000715440d5940890a61029400390b0300c103001c1c602221614100400080c80c1c000d0400041440840c403030000a15180c1c400fa000d4040c2ca401051004691803c1c00d0103031100e0150b100d080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706200107 1250 706198857 706198931
    0x720431a030a0605040c0c030212120a0f0f050a06030b060901060801031401112b0b09180c04060e06090709060e010f110a03120e06040812040c0801060b030703 70
    0x381030180d41c002041c1c0070b0318030f94882000c203168540703104140381100251241152604c41e41006460003105040340c56204804022a40e040c1c0301c0e1441c1107401c803854100100350802c00c107241102030104013040c030348190301d4042002901c0b003070b607005001100d0160810300c065880d07031024009129400d00611010414805c01000001d0f03241d50100700e0985404000241050220400c0362103a101207810700c1c0300213480380864001659030b400400010401c400812154013003c001c5a03050b003000b0000d4102c400095034000b4140380500201c1060b1000a00802c28a0b440d07983c0150000011307221940120801c0000440d03050207483c2807401e4540c542c443c0440020300c0001151032a1303100c90b003002040180003c007101c81404115041e0094440c6d1100001071b040b0780312480484d102001001403a43c009020b12020840000465000d80181880030a280d66103040ca186103900c113900800f4a036282c08000030303c4840b1100554010241682c06002042c410508168000101c032400015002aa44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706201357 1250 706200107 706200149
    0x20622290f0c16090c030507050316080c0915070506010501180e15030f0709180f06020a030b0a0621140f041713030203010c0305072043 60
    0x201a00340040d802c41100c00049403030f210b01403901c605030b20031000c59442d01e014a4920f81c150143c964000d22034135019055160026140c40c3c41c8640880750820f00c400d0402141580e41804c040302c481c00380c00b82214540244104072150140d100d02800d0f6200d003e908004901903100324960450006103015844016050000365502020701600030003180034000900d24107902c0a1203a05651003004004c1c04050341f41c903210000b0b0721101e01c1242011515403e20034001040d00454100440d00242c0060f00c442e03c80e41c1c280c00034040c10440c1907014410890016060340d0100c84100341c8185c42100d40508050400c02c182070306c14501980c05500e00314400110046032410f49143c5c000e00170000c24a20740700025403002190300c1018501700748044004c0c00d2003913040902810310486070a240801052400d41c00041140d00090313070707803040856000d8802062610030416909152007507103500300d01f0344445080505811403540702c1003c0c00780400f034210000c04071103621404c0350508000c0122000c0c0c41c030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706202607 1250 706201357 706201387
    0x20414180f01150509120303040507050102031e0f0705030408100f06031101050309100203013b010b070302030c0d0818010606020705010c02120a0804030302060a0b150702062229 78
    0x1a503000c04001040c00b02121030342d82d0b1b40071b1118070480e20001e1550381c10b103030a0103410005150001810741d07004000000c03440b800315041a5402c80042580f5407182c0f002800c2d001944200c050141041c0320201d008500c4400208071030010030000d0600300504003222108200355601c1d480041d0014400213a002000d50082c0011580405840309891043d52451100c800702d0f0070a0300030b10706416190340124401c03105110420303012481e10b18484078144800c070f5003004000e01401307220507020717021600c0010035000304181da80c00c4880c0300030360700190140d4100a1103813804403041ca044103a802d09040e01100103106250030307906141e005c0c194807420f000046d14014550749040b42c00039482e80c3d06c00d070b08600601c05030b900280f28a8802d5a194a541002883c0000151042c00340500d400f0b4541925914201080c861040e40a111600d82a0384c0c00080d0321400f480e1140e4a103051441c0521580214810081c42078074240030010070009115000d00e020b9009801d01d51074007040030058245e1614000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706203857 1250 706202607 706202639
    0x160f030203150a0e0106020c12060a110f1c050a0b13051812281e03090813030c0b0408031213020604080303060301050703090206070b100504020414180f01 68
    0x2d4668410501150340100781d4030100b960201910b15041c3e801070080590620942c0001d1608072002c2040d02ca0741441c0ba070300d4070009006261707003694840848171034481103026a10107200f04024a9105c217504030314103522045050385e1079074040c80e00c0d000a0f24581c0303601c514409000d02401104591000d4540100108030290400315200c0c50160341c140c4d200004c000c0d116070244400a0141c41b10011381c0d003a0100c105210303250368044c482c148024203403a8130416184412203403440f10341c803000712540298000c0c0005032028004110002e14030384d072001101049400ca80c8503521854080c0e175284915205401140240b101c00d4008214000d800c1d070741040701d02e80120342c514441e010705025900046281d032150303100500c00d4001204124241ca028420203500510504050000707050301c0d40003480350310403240014401c0c2243e0700480c400303500d2440d0030005450060001c55031b494403160030b4074050215140381071064010000301f411020b10306e908240901d0700c400d40501b15900b042164418400c2d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706205107 1250 706203857 706203871
    0xa0b070302040504060303050c01050f0c1206190801090201090b180f030106050406030c17030a0e0d031205070507020a14030705010c0609020d0807020f0406230102010b03150708160f030203 83
    0x1c0c00b0101c0e0a035039512502d0000c620980307a00b42c1c2c80b0b042d05036007803d40700014041d00060500100300301c016100340d012110070452484290f001d941d5528001140e0b5112440300d500d51350d508581c042440a070540c0080341da68000d0702c0c0c2e45002541c0e8440007800744594400703034400d14041c02025182d0b08000b1400e0b102a07200174000b040051303c8102080c1200c109a00907038140b03140710307820003035001e60709204400c07521180c02551074044980d0000d0724003070b90120841e000314166100a000d01d03100382207218013880841010300c00c5081c0705400802617089204181d21a0480c7c2c500002c05580f403100144a0280c060084c0c5030062400c001550056072142c000c0d9040390f00d03140344030016510441440c0d109072003000d0050f01c1d40d07198018441c0e901e519590030340c040d51a0075024010745014400313402802c5d00028002110003001c9004074054041d02c203442d0b4141c492800303142d0b04d400003001c0d134603c91486c658a8818903070b5108480156074400341a030701c0116180300c0202d80e5240c07003a00103650000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706206357 1250 706205107 706205111
    0x9010f090b061f2a051c081609031212050901020a1d1f110304080a060b0f01020a021201060803070609120c08030403030c030617070303260109090203120a0f200a0b0703 74
    0x80700d51a82406c00040201120b138240003000002d9029030001c0f190307900b040c0302e01301c004455902400c0107417030010710740005003180b0b94070610080030620074140e2602e100142541845076080c8102c44a000c2d40081c01d80101140405080c4000345100c81d00000318098001c0580001e940301e00403010000d90018190401c001d544581c2000c1044e04000400c01454064000c2800c0022418080201c801c030f080c44601c100582d404540ca0760380d00080079141990101c80007000354240314520740c0100001d40c442d50180c04080791140a01a0f0b9030700012501c4d0080284611850301c182c0c01303d610746e021030310003401c080c1d0510214000c88c2c400c1e849501011110706001420755121203103e4445800e441035001c1030f502402042c010150f110103c3d030200501038402816130451030040c20000281402554900d41e0344482842c259941004600a1003a14144183e910b071041203004040c811500a0303c1e0108040d541e1202daa14090132262900501035000360110503416903484201c1c072000780640c01019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706207607 1250 706206357 706206437
    0x7080412060b030706170106031a15220504110a05040e101a1903110904020903150c1801020c011d010e060a0504030501061212050309010f090b061f 65
    0x61003c0000d68085d20342a02c8007141411445070800e11190140c109808140c10000410192206484801e5040c07104580d0f03450f8035034a032003001035140070b07001368250045040440f00b25114001b02d03800d0140c0f1425101408001d49225250700544107201c0c02d640000e030100b104202003461585e1141c0c12451088a031454a80d441c005401070110f1400308110080300000c2d0400e81d0040e0312007036002d0354a00d081c288603030711190f02d5061150050204090045400058141c1a40e4080c0290809003403c803c07005070506005c2c58185658019880d400501d800030b000ba00c000f1341c000560642400c3d0142d4804c2038108070301001c480d0314403500380001d0501c0624900824241d8805010300f0f20344100e03568440d00e6030314605145095503c00c1d40981c0c04054101101400329200a14a00d8040c03114142030360780ba110410100c0c010a4900343c40499146000103c8041003110001b281c007c1d9002c0b03400c171140c04100d102c025540b0200480800109081c02403680501c100f0641d9010300d20810b0f0040c2c1c0f401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706208857 1250 706207607 706207609
    0x9120712110619230705130b1b0706030e0d1d1810120b06060c070b07080a111b090901020c0109060504030801270b1f02061b07080412060b 61
    0x42101601c2d10080a2140f01c400780a00070203105214100710380300c070280c84d42e030703e0b5000c0200c95100150003002040170006071001a419008480c100400f02107080c142d4900c2d00140b000564140050640700d180900c0c01c002074102d110b0f018841030b00d0aa440a8000c075584000c044c2c0d03d03d03000b02c22514104100e400c1c1d0800980c0c50200c80303400340c80003005160f102c0c54695006a01000c280d003001441210b4481c0c2c2c0d802041000003101e81c0104140c0f140d40ea03030554a00c1c1c0c2442c00d012a40300e131000540000c4e01908201600300a8500c4070348a88501d5802901c64074131680700c805490001e20911005181600d103807401810990308030504000052170070702408203043c00d44040b038400f60754150b16541408200b540c0322854500606d82205010403070f03281228000c0990300e820ba451071600344c5450700c07000a0341d1129440ea007807820448400c03c001e8804240039444110855500f1502c2028200740950f40101070f0480d50625403045c00d15151506114402011102c040000c3c0d803841d680d50b45440072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706210107 1250 706208857 706208863
    0x213030210020d110a0809100c02030a03020a020a0902160f022d03070b0a123603030c080c0f03090106030812311e06060f0e0912071211 60
    0xc0d41066000e02210000c2e0031001e00f4140021a4150b00b03a03000b052410301240085050f2120500102c400030803400103010700303c07941c089c0920040e606001d00b081c51810580c001034074403011032007900c508500580c0c0b0141d03001280202c10f07402c28050400311400340016404843c1038000ca10080100940b041c88800840c641c5a030001070410000e805007254040f8a010803c0c10010181c400700b891600c0c900103130041100000041c0000d409440323282c500c00b24103403210500401010510400ca442041d1340e1240c0a41d005000f0950200f0320300070740c2c031303400520408100d403043c05200c10107464059100e14050309544004d03c51860355507110b4004c000540c1d00c0d0024a2441c40c0c1700d0b090f4205041403204c007042c00721049689030701045036044900d0301d1002807440d45159074029070091100505803c1c0c0203025202100002d0500345044004699544a01b05074010b0341d40ba05414405941c842c0300d03150351030840302c03000302225800384083d400040c6010b81140c40340113107140c0305c881c0e00340c00100c1d50720b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706211357 1250 706210107 706210129
    0x2703240203132f090903160b04140703050331090b103b1008100602030c0616020304180204180504020a05130b06030901060509100b09010302130302 65
    0x8800c0c01024072410500984a0040203152201c5243e02c14982d85610722105035030321003040b20f021303100d0350001407031240c1c0620580f034032000f107404101d4400c01245010804100100e0781110400c2c00107401c55082c500000b058800d481d1700030011481c1006007039003103a40a01c500c0c0441240303450f04515860084079001c044006042111000c07849035007074402c21104a41c42006d0f1010401485240d507603100100303030114107090281c8800403045900203441c140040c3d00c0300c5d0041e004810340724824444d40e400003159105802c4607141c43c00540c4c90382c1081b6104d01c9628440511030f40f002020440d5681c4c0030050031b0002c0030b140112440c260355402c60b50319440102c0040c014965010904128003a034211100030b5803507d04008105620749a030003d419005280640380c0601c01c5507408484183c2264829070110100401c41626440c00c02e05803070182c1080d000d4940074040d804081a080781800300d54109540810700e800b030501c601000110000e4002d0700d1400030042c8608400405a168459440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706212607 1250 706211357 706211371
    0x50412140d140f07080919030306030605070c12020109050c040b180a0e06060f010f1101020922060b03040b0708100302090123100504060c0c0b1303032703240203 71
    0x1030305034035100481c0004203000134030003014404044104286000b0100300700008a00c2c5050382e8150b44581d003800c4000302166040242603d1414003071000c07440d00702003840040c61140302c010f6241080d241e0700300c1c05d84001000050003a402000d11101a2410b0b1f007140c100f2046c0503240d262480200e8011894140090340c1003882c041d91450b464214002c01c0c001c1c0f6a1101007601c0c090f181c5c0a001000a02c01d90b041020001000344d1400c8480b80010300703404503021480c1c01400b211002140c04100c0d000e1003000010079801070b00c0e20b140066549041c2c000c0e40d2003036412039032140703140c0d5980700f081d61050002424003504e00b50309840800141d5610015602a21010319008006840c40985546411188070704904c5145144202c1403400c2c2c1c824129000e960581ca070400542e022840c0001184484d500010f83c0c044010548080e42c0c94050010720031240259246a010b640c082d0300040d00d15036418960303414514010050003c030308940384080456071052841d543c0e01402000c046c04a81080e2085 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706213857 1250 706212607 706212641
    0x5060f150d150b040306093210152903041101260a0f0b060a032007020f09040821010807050105030c0d15091b080a050412140d 56
    0x4106885840c4112914401c40540c0b190181d03091403106150340c0203511004202e55210040c83c2c081020030000380c1c45400b040c10201880b0105440c14a4070440030000080c6140701c0e40b6500203002d03c0703d000300480c0d80f07030107809041c02d541401e040d0032034024003007100040380322000000110301740c440009620480c010382e41941c829401c0400104240d07031400d100400300c0c0e503400c40c2d01d8401440d41e213556044699208002104e56042c200350000d0242030171400c0d4441c002050002d42c0b41c0e0540c021000351020102d009030300c01c9102902011130300401501a4100d0450780e42c440c49400c20300310f01a002405240101c0c00c0110118281d001c0906400c2c01c8002d03207084100402020404105040180509082441c158074103a0700c1e10300303140034403172542140940320300100402d152100c2c1c2840c040c00a5500601c09205010080010006002150400030b40090b0000c1c00307090941c030030540100e43c0900c808001c100e01120851348103814504440005c0010010304156201c1c0d403181c050071001b01012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706215107 1250 706213857 706213867
    0x303090221060601030203070e030708032116142a0d030e031608070506010b03010806070507020d1128050f0a081e031309022205100305060f15 63
    0x1485818000d2090002a48001c40c400304500340700416600c0c1d00100030b10703006032241d40d601411601748403451480354050064800214185002200400425070f111809015242c00a800e548400c0c100701d403140401030220b03400c1800d80d440b401c00008098484443c850918400903040108450008503449103c501e8a11003891404180044400344150f41000c2045000b0b440e04940c607480740e0340315002400c012070812000c114819007a83c09068110041f501d6640c1c49115200d0541c3c03082c02801003034030070700703000840047c420b0301280c0c1c0b450740c080d114090303c51007907455500c44c440003d4026800740300b129050940407100035960310091000d07009626110314210501100425541440d030003000d05c010f0600018500140e210a80010364031020390a80038040443e05501408100d1240300c10034600c0040c240000350080c121201601c9402e0084840d00925802555024802d03e034100c0d042182c08d0356018000c2d0f0000c0c1e0b00c02000340c45c1c00c0e000007003080055800065100d22440c22030010503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706216357 1250 706215107 706215109
    0x1e03110301140910050d11040603140601140609010f0315051e0103050c030c04030f0305090d14060f0f0a020f041e061209080313050102071b0501120515190f0303030902 74
    0x4115044404d18540021050520740401d10040715a40c02a0456045550441d0b4076200e42d84002c0c020740e004120410041a0f400f002034594100b0300c81c00810044140f000035013880d0a0781140c060388016103550302082c900c054142c001d0320031034161454113545494001801e494240c101d210722040302962907500d012100c0003504540c8098485046e00f0010b008018005e503c803c1102c080d29001181d000110f1000e03e003c980c503126861400350040038991103542000b48004000000315424000e40d841980c0d00d01803040c14a000316904622040001c02254180181e03074028a8110200704504d880c01c0e4581c0746d5841c5400c422080e4010441d45038100300515580481c40103104440c80d501404414020713124200c190201030b02005142020903400001c00c58254103e420361540201741c901d07030044010422422242a1203003d0118001c1c4088800b03450442c420f0902c107003004200345c0084002a024096005101049559405012140801c12210002d00e5100841c8660703804103100c12244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706217607 1250 706216357 706216369
    0x5090f120a02101a040e070b040807090c0c110f0a03020a080d0906050705150a180b0f06030304030302072c0f040c090509030306130b060c0312161e0311030114 70
    0x403008960540c40d116100c080781c201c50380c1c0d9114044c030488022902c5022046050309120455112003d5100e0008000480701408240002100c5040c007080040d142c07900000d07941c401c2c8102c07009158101a114a228500c0c0005070388030a0140506000380c21901c0e43c1c049509100075411441c0d495005609003c490b590000c68180585001d25100782010441c1e40c0c1e46030740d189030311500c200301c241c2d4000080c6003507002e030b104a1408484542e0750055110314142441c2e1302c601a103c10907040c0744540010800d050010440f821a035040c1c0c002d1080c00c0c45c241010000750000013007145100704e07003075422003580034071808207001310340c130740840f0146040905e02800301c09000e40c040344e0042e0034841044203a800210645c0c0d0b0001c2c00307640c2d00900314140344640009080c200325007580700c00046006220340c10000094404880034600662039612581260035061100c0d098040c0043c03c601e0410b41c3c042058400c0c0760a0005608000c61707a499036103001d041c29003090b0040340c4041c92007850b458141c6420 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706218857 1250 706217607 706217623
    0x801020f0705072403020a020123090607050310050609061303050f070806010308041e08030d09060f09170708040306060608040318210215030103060605120d08070305090f120a02 78
    0x5003461500210307010b0b204841d5513000c4542c0b010300d5030201c0d082c45224000e40120701811002809445515203913001102c1c1e1500580b6580090b1090070000340c00c02d800b82081300d0049a82c02e044444892130f06c8100b01095001c244501c5c1c001100b48820141e02a1800020006e1489200074099407180c4003121461b2141e00c0d0301c442142d0b804680104007140b0000111810b40c3c01d50300e40d84080c11ba0b19510801c119410fa03004000c644030004a030391039000b07035070b0010204500c141000c1c010300c81211000801d4403420507010713080d03070848018144908c0c090f0006042041c0b19580c06801c169803519030303008440c9964000c60100e81581c1c104010180d0040005005601261851074070f2801d15400402007400b41c203003100080c0e9903000388d00c19550340004010604030220702e03e5a403981c4038548100542582e100342c130b01401c030341c54044075405000b2800307644540040da45d604865031a00400c801801e0041c00c880b090b80074641649031410702c02d122811108600c14a00c682da0507005400030700e40325072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706220107 1250 706218857 706218869
    0x6030d020318010c03020f0a050c010e0103110a03090201090807091a040c270b0f04090e0316020409140303040f030905030c060f0d1508010606020d080c0706150801020f070507 77
    0x1c100740840b80c20505498800c001c0203281c007204000f19882d06030b250622130100480741d4464034004004221000440c6034103102e003031f80c0b110340c01c080c1d030740054065921405031700321040d03028080c800c4441e119900144800e0300524001038070594401c211818a8420f400103501980c64222040341c45400800c01004007006403000c2141c0041350130001c0805000314a030001341c4025030010255104401d40600103004440e0700681d441041020764501a4058840c130b814550400b50414075915001c41503a14044417219003e01c144126420031004109c41401100c6107800b2881203006204100041c0d403040b0b108056034040b42015040103040488103901040c40380c2d004a11862032034490301d090326807510300a1310094030b482e48841d01c100035100b01b16070382d10400110440001c444105401c02c3c000c48882e41c0944008012580d002c44a01000710382c000703440c00040080000050b020340c8800e02c0040c034000541419903c0340e0842d401d82e400450f540303412090108007581888400d2141c6001098 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706221357 1250 706220107 706220113
    0x90f09190c06140f120a111b07050901081e03040902030f0f0c0a0504091d01140a06080d0f0518030105130204180203060f040f02180a0c03090c0b0708160b06030d02 72
    0xc000002c0010520843d101c4814504105010901b0721030540c01031218810119071903070311594012001034449400b05040c11280c4561080001c0505129002034103840b08039003d412110280301101510700c4840032080710030302c42040002120902c2d0310245011303644030405001c56080c0220301510750700340542891142681040f40008868112040354210307130742d242010031714403500781000100060905c401c030495420700c2d102c84c0e040903007680309900c90010044100845601e5100310740d0355044509406021500800700156014000c1e8050403801100c1810fa41c4c50004c0340c800f107400d480302501c0f15154810640c000d40c0c2117103441e0040003c04e80d6004590317561350085400199a85c08060b20320b14002c088100803400780000f500c1c4030018035402510a80f0744882e20300f074040b0003840884144100c0d5142488407c4100e2003400341198654019584808203810180d00d85d5a990001c0b20841c2d020000304460540e02011241142c450740c0150000c0c00c1524015041c5400c00c1210040681190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706222607 1250 706221357 706221367
    0x804180f0c05090d02060d0f1e0e0c060306030102130e240a031e0b04050604210f050d0209150405100801210f050a05010b041a090f09190c0614 63
    0x40c0d101d003d54481070f20854500c1481019070004c03500c4c91003500748000c511400d240c41090052000d410100c880d091a038101444455104103160495080c03850358100b41e00805501d004c41e2034240040d5400c048002e00040c070305043c021382034034403280581c0202100c1030064100002c6c1c8a0355203011000c26003071081980c0c0141d070301c00007503003140e21400000c102c500d40c02d240081410010000000d0302d0342c020301c41005402d240c00d007255101c03c1203078210340c00c11010090002621402041400550307143d201c41040c0c2070900310950f070b190054182c9041c0139900380505002d40d640c1c502061519801c0c0115940d5481c24142805600c1184180d101c00f0b111001004001007042030f00c01441d0011130800d19180c02b03a007460068451200791201410900c0348010340b07814498103502c4a4006031040b107003040071201c5411282d607042404100b0607403011030400020340c41e0708042007440d8003c0d10b074003d40f47d602556949549000038014010703103403640d040e841400a10380103400d488400b0140d8107450b08103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706223857 1250 706222607 706222631
    0x2a10091110050405090a020708030f1f15080603010e070f0342020904020d150801061214010603020315040b09062203020a0204060902090a0e070f080403020a0804180f 73
    0x9110314400c045c09625810000b03055000c141d03042d24451644021600d42ea03003410b1218a00f02a0244ca5035104440c06000001108007486040c0b02101c1040f5188080104840c0056844480080130300e074255481c1c400c42c001890050090001400e040b00741e0241303103400c600303040e0301c081b01b2a07100c072050003410301040282c0c0d01c21400c480c0d0a40c10720346d0303c42800d103111b000c107030064000d8000c2550014000310b500b1020300e07050b40001006032280d56100c4212665581c039107003650b100d8801d614442e400508040041080d1485070321002c00d42c0340010522582d81d03804649000c2b215181c45020701101c1040c4820070442802e5180c0060310300c40103001c141440920b000c81c0341c4031a8407042d2450740c407040180c1050b00a110f54180706800800800420390390b01841c0000e9440707640701a210b510200d0001c144001101a40c40c018a0142d40f41d00b810311090800740c4507190090825802d41c0b190010b0180041c0801000b800548000d000340c0390241270450502041e0b950500c000310004d030900140f140e003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706225107 1250 706223857 706223867
    0x18020a091806091803080105122b020118030f11031e091f0f0c05010e0a0501060f0b0f070813030501090309060807020604120806010c05070305030c0c01050705032a10091110 76
    0x40d14409c6035a40800303a64481c1c00c0c0d14000012408480d841192070502c900750051074403c81c4e405d06190020301010b845d502c021964089501c0000f0089001d228070703002001d108412803808480ca64040305d1600380b90316140a401408295040310400380012a44454208642c10b80e200c40c0000c1d41082d0500d003c40409440c001200d40140b0400403007280800c1845003d40185000b620b0400503616042c0703403410131601803c41c502409540d18070b6810002168505001114455200c0020043c01c1026640e00d10031140d20004a05c0b83c00d00700100c0110200b042071188011a0303220741c032004001460204003404644000b040342c130540d00402c040001180144034144681809450900155920900181c03012080c03a400902140f00f100004010000004010f011134000c540840d003001c00501c004603014400d031a00100990403d200b0484104056251801c1102c164007950002c010042c41403460310b1110b8400070b000b1030722045924188000040002240c840544130000000703181480506 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706226357 1250 706225107 706225109
    0x61b050a110f10054312020f0c0d0303090503030109060306050c04060e0904030908030f27150706090807060507090918020f030f070b12010603020418020a0918060918030801 76
    0x240f100c641d1107040340c18035a8280039228400310300c0c8000e4005c002c84480058a0021044840034540380f59801c40c140006503c03c50a007459000b04102e41d80c64080c4141c0c0c1200f10700460905407501590030000b4406d001540c081c00e4a070301c00142052031420100180c80c2b01408420150074100001c0c01016070040c084264146d007510a00d042e07444030b20f41101e076040b5903840717030740c2c5404003003001910084520000c00660f00800030010f000448031100007042010f0900c010340c0010004a0840d0b00342c5c510000d840322134001d060000d810383d410780303810f1b401d6800b01100f1640c0603520030801140c4d5412990200180c00b60700810440244180c804000c108001040644a02e460083c0e05071250b904204e01041d00c10401c0070350b03070602c0d910340c919007072074020040344c0c2c901003034600000c902d8600c00c0c07007030710210f03220b000c010040d403041c21000100950040210900b0440710032000308000c40f40403164164594080340c0000c0c514900750f00c540031541c0c2403105c40f0340d0701e80506182c800f0913800b869540c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706227607 1250 706226357 706226377
    0x140d1206050a2102130e070f0e06010819090807120c02151303020d080703090803030c0a0e010203070203071502010b27090a0f0c14010513061b050a110f1005 69
    0x1112401c240609600c100f45400d800961088065194000685e00394005103000400c2d04110340d141622410449220800f502604500302d4001000440541c810091030f034204920482e604806401008400c00740ca6440d00152201080025008204031a4000306e5190700302c14030b4000340034102d80c1d00040e1610070040c0701300860b09001c503490201e4810400075030011030740100990040354452030880d81c60781107040181e010501c0c508002505890120440380314441071082c16161268402085e01c0c0319540d2840d050461106024403001130300c0802007880a0036645001d0421010360070300090a4a89044002e409004403460b14000a400903618422101c82c142e4800010741d40c4072915480c0100401d4050002d140c050954002d0044800740041500e01c4600c0c0840c0303e001e0400151014131408c50818480d949083e030401090b84540c0e060103032444001302d490180b0109840e0a4541034210200b034450703480c1642c408007207160111400c0c03207124003642c00040d10a41160050428044c0c0e1440c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706228857 1250 706227607 706227629
    0x10c080c130504060e090f0a080702130b061c05010902070305040302062d130e06030d0806130204090e1605011e0e0d03050c060a0204051e0d140d1206050a 68
    0xc0c401d0442580c15809040007800422902d81c1d03400c0414140c80c81558040c00300d006484171075914080c0450480080ea4200e100341e46040310782c0d42404540801a25101c0c003559940c40c42070301981d5400c0050143d0340c250030720f2420850f6411080c02c103c64041e48001200d40c41040440e0000f0b82040c04e84040326011211140c03118903480340e101b01c164100ba540c0501c001c1c4221150a03460440c0301810407441420080344102d915100003503151a000c2d0b5203940e165202e10707070f8001c280d1710a64040d5030144014050340d6042c1c1842d9041d0099030403030380002e1080c0ea01c1d1300c12000c07802070800049081c2c49038036142e01c00710380c580800602208005203540788a1601c69403100d544602402007416901005008422881302c141401803c0360000445115903028613030102e40c00700418000c1d6410b5601c010032450b6075040080f20115100001d041e03003600308407503e0500000c80c240765030b007514041d50000506a0280c0911b4010542540141000303451854600c040c4a151203800a40d815904c0348080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706230107 1250 706228857 706228867
    0x10510030b0c1207090303020d09060909020d090b330a0e0a200403021309020609040b120d170906041106030910060609090b0303030103121835010c080c 67
    0x1d00301c00d0f100b424146030901003007009005001e90f20502d19011240681d0030ba500d00100140300311144500d51140f0f400040d07a51409020a95899001b48004880008001841c1c0070a64034002814412101e401100c180f05500c2020b08039481001210280d4181006c090561450009104040d4a004010b000888a0f000a002941a502082504500e001341c00304d130810802c850354003030744140000c80c040e20a5250440c3c44548900a55000950082c019030a292409040c0002400e410301000d43c0710300380640e08031000200b4070480c010b881003035450a0007880004001d0320035400107009001c0a41c41541004041101e40d02800c0c8404030849420b0340c5c0b6121080361500d042d010110400d48545407840026440d41c010400c40304842403c08103000e42c0300c130b50081545a000074440540b6000e0f00015010185104403903508098824070207160b0034a460b240e800e90080c0791030801090301d00c460130500f060b04614020f41c194055144000f8030020f0a02c4c400249a900040c0840e03042e69400300e9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706231357 1250 706230107 706230121
    0x6110d02070b120603120f030417070201140d1d01060312022404140d09150e01020307080706110c06011e080c0f01050c011119023f0a080a0b03010510030b 68
    0x401c2c0c0b010400300300c106c0c58a5960f01000c86900f80d009803801c5464404169290b0a1401001d0503074030001d030140c5030700364140c3d009201401640d0100c040c0d504200d60391b42c280050312041400518030002c80f100002080c500f94540200c0c030040481d60366040d907016407100350031070003051307490302121143c5000f104494645150030418452003440c40380440c007a881c103031100203038080d411408039088540340b01404000e01c4001d48102d0900e52000d40103800c02c20074280803610030001401490f2203081d00190100c0d81048014150300500c880406540000e001080300098681c142c144c00d9034101d6102c000d982c50900910f9450011b618a42d000c0d0b2500042044960701460540b201144104024080381c000300c14855a10352015282000040030041000c40c0688005000c070070100340284c05c003c5d02c0350146448038056685020f025807406241d40c880081c81210b1001d03090b0b6034100d4840c08501d0a0558100c0c3c1610404145140039070b2402c0100031108114101c0c0390203c0707410a0030f081080e1500d00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706232607 1250 706231357 706231363
    0x70615050409030507020a0509131b03050f03030a050a06050f04051506041401110102040303050405060d092009330103060302090403020331061d090106110d02070b120603 75
    0x20380116407180c5800082401d1540000080c5038082c800c03250310b00318548600400442c00000e9a40c1000c042100035184001103440e1380500c546007200e1301245030190340f80d660502d008061510030b550340e080801440241c900398003410340c00c4001110103000c8035081601040c21605c2041c5070501c10340e00d65002c15201039220312003111501021b061950358503241c04000030b44031b204c20404d500142e0704140c010503601d010710a40d001d07207525070340f01d030325180c81c0c001040140c0c1c00c80c1d610703140d260381d550703000c00d00107640400003000000fa81140002c0f5414a9000c1140e580401414101c000f030044020a050381d0489100c401754100b180424800c0755442170040f0000c010981000703401501c41001c1c00281900080030b800c4c0034411040315075909000d10400d60040703d40716116040b20003018814031100d4000d10381d0385240399411401941e100c240d2000a100c03204203901c01c0002c680102e40c0c409290380e0a01204841400b6800101905403403c81d0002ea503114820423031081048010204299507814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706233857 1250 706232607 706232609
    0x2060105100f051b060613050606030609100806071d04152114060a0e0312040b1b12070f021603020409050f0d0302122203030c02030c07030606031406010506070615 72
    0x7881301c540e22080d91066840c1c1c3c51034191030b440c0c0300b030a602c00a00a00c0079a40601d51007414050f18141c00c58031a5800d02c211001e001d420983e1103030440303070701207884003040000300c3c801c1300c566031840210510001018643d5014402290160b414088901c015420b4064903d048550460700b400c1401c881040740d000300740c0342e04d40003404c0d00940076440c40c4c0c0c5030340081c8403030154900707000c10801c495146440654a00c1001c00702d10500440b1000100030406007a440d9a01045200d514408039504e80301c420011b0780911406590940d903001803005441d44042d2000c0c0c0020540010208480c1c0d50b01c00b8441d00d001444001c0c412a2180c6462040150520030341e0540c1c12000c080320501d0440305400750203500403600704070380c0c00354060001d9175101d4100d078185024028159403481c80703041a04c0446c05440103c05404c02d51000300107005446008014180083d030052800041c000e00314500940b0f00c40207444501c203030b90b10800c014416a51403104664465600a000003041d110590302038800c0c140c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706235107 1250 706233857 706233877
    0xb070e0a031a0106080915060102012310091e021e0c1b03280615080f010f060b0f210a0f0e0f030a030b03120307030e060702060105100f05 61
    0x2a4000c0001080105000c40e4861400501001040d80e01e07020101c41002040710350101c10f074460000c64565034840150507400c00018400403030781c03200d4400c403c0d17080860321005803c44040101001949198140111701801e800380d82440055551050a4a40e001c10016003821950003c2c040e400b1003601d0349002a0045003014403901c0f031041e07299658480c00309007040e00400e60a107140c0b01852a0225540003210780c9a60a072500d060b00d1082d101007034820820849880c2e83d52b1211040c4885848415001024900010200d06001000701c03425112079400b40682e09042501c00d0200d02c480b10250399048403940355168407a0304c5485400c5001c054100112000c2c110a0103011b0f540410344c002e042d9140400c81c040c0450001140e0080d6035001c002c0f0000c1540d0418061441c507107100340c211819800780141141c3d107400c070080016003070ba4405d980001c0407941c0c0c0e11388031400007804e10a0582c00701e40c070700183c0440d41c94007010415140c030a01a10080100041440c0d45943c0a08162998011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706236357 1250 706235107 706235119
    0xd0f11011505091003020a0612090c080601051203250206040e16030e060f07050315091302030d09030308040303050a0e030c010c0e0a14131d030306190e040b070e 71
    0x414030301d202952a280100d90099400d18000340001210a4150302142c0c0d014060b1144130f071400400300d070481076140c207a0440640768242003020886021900024005903800b800d8030f0f51401c010050340d40b0000010540340d40040c0050b9590072540c2c1a440e4400c071005a0480422070513100044c1d1a1040d81c00600145402c44c1c1803013905011481c40081c600582c0d01c0c00c0120305c24424400c1d5594a046076a444801b901400040059110b14090341e040180701c0c6d10281019801c00000e001030000700c0d41c030950580210003c1082d49810413132002d0984407810030061403800d54030000c02602c1d00400c081d0506407a42c01082101a0541c080e444c06104102540c2e10740441002c018040d20f40b480c1203000140642d00980101d2800380f000e4421520740000d46540d0514000c240304d894009850840a0140e940701d2180e0310461040d84013002e0624900603695924001e8100030040e085019a40080c1d000311038148803078100c41d601941c000d40c1001c2c84440507a108a402c5610914214059030009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706237607 1250 706236357 706236371
    0xf080a0f1716050c15180a12082a060a09030c02040c0e030d0f0f0309170406080412080606180a1a0c0c030606010c2405040c0e180d0f1101 61
    0x41408480103201038825001d5503c20680c40c0c0400c950300040ea4041710100d2000c000c03000c800400c861001d44501c00c060101a031590f9070708003034050589810002d943c0a00001100600640c02204211a95080c0380d0301c1c44090042c3c3c044640e4804008080c5000c0c1070303841c3d408400b414050905099080d6006006000d02d800851005040720141800b0500a10628264030405170190504031460001942e4116144200c1d00c000c60203489002426500350408092030840c0143c0000100050031094903a032525080500c1c0c5403082195038260401000581000d0102030350399202101d00300c92561b000740100411000003d10100c44580c00020303100902047e49100d802c508000c0d10000324101c0507a170039400980113260320b4442c111403241c00900100c8030300b0700190003440c26181c0c80c0043d8481c4ac0c070510341038110701c048a40a4409480201d5140d10800051700b00b039941c2a488484498806515101050000e40d6284007451410902526265001c0024403d01654006c50798000c0240111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706238857 1250 706237607 706237627
    0x30f05010b040504051006021903140a080618090a081c052401021b061b010203090109140307150f02090d0f060605030601181503021e0a0f080a0f17 65
    0x1030740b242c820140140e04120006a00901103e149000c40c0c00b10b4002c1c3c19031036141004122002c44841c0200c01340030b00743c0c0c00c00b5810440710010700400803c41e01d840700d840c02c20600b0840074080f8039024014072003603036007040f070b4040c008112031542540c84003d480c2ca40524140c4c0300842c001031090014106d181174200010b0b10952019461405951503500d034100071280012030329a000740402d800200c802c94115501801c084c0b00811084803038a100e80750602e25560001c0c2641e000b51440c0425a4403041440240310b814000c02c0c1c02c01e0f4100c001989000199030325411314071602d121400388150b0314074007040644002d0301203944034000100303a43d6842189140140f01e680c07884da4150b800d01c4c50a6400300c3c06040000345941a2060b06160741000c03d0068840340c040c0c03d2211000c240001d140d0130010058449884d02034841e09011043e00041070303450305102c4100055030041000800c09501000112000b0030315500340c41d04001e5002e099125400c18040a030450503000c000640c002030501c1003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706240107 1250 706238857 706238879
    0xb030307050d0305010803040501090e07020a0b0702061b12070f090b1b060106031404111906050c0f010506060403030311160b15040902011e020f071403061f05010c03030f0501 77
    0x5200d41c0ea843c10440f603625040001d50364000c60090b54003040000c1030030300044203003010841c2d01a0b030920480c0c090440c9690f81e0380c10010152403000c0568005814090301c4132030841c5091040c658016031604113400b080c5440403d800192106060042c42d14001d05039038807e124100144c0108040308c0c0d5141800f58140c40001c007580449a080d024a000200c0d03e544280a20f800c1d500300c0f04200c1d8540c0e00d0315100d40c00b07000b51041a05a101031070004010300200350b014030500502191300c0702c9031100030098a542c1004a5150084942d0b4508401c00115a44050a4074181c035003602e00028050030307800d01201d5510403c04802d441a503059907607401c010405619034420744118108540c0a1809800d00041e1101d4071030080c00b0604039a000c02c0401c81145600390301c22041c0c412180034501481105041c0015508543c1500034820a80e82850904015958000034002d0360709510b07000290301c444101b00c4a018250400140700460002d05200750400740c41ca00c518402005556964504665 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706241357 1250 706240107 706240123
    0xc09030a05070f031407030c1a0403022707030e0d14250c0f0e0c0901051e040f08030910050c070f0603050703110712051606180c0b070309180b03030705 67
    0x90ba8051840440e804881702107030207030403280d02171551b01e001c0f810080141007040d5002c1c14140e050390305020000c05680e070600c0c074125144071900341400400c1c4580c0007500c602002450705060506290140031150b03c0060018040c0001c1e10b82020051842c9005032628401c1152200800400c1244801959803510030000e40e640318205c400f148039901d03624084014960312400b401d204002e000110a212100c008100c40c940502d01503290900d0081666510b06410380c080c5c01140d400314082c02200c1061030b90901600011009509102e1180e000907002d403400040c01041110110b052001d001d020400480a0000114046005511210014001d20088502d88002030420320401c40d0b040000d0100c0d00e0150700400c03140525109003105a400e54440170700814544000700042d0003180141c4030300860810006c9440001030b42d1800c080b00602c280360031076458080d00b04054030001c0d8008001004448000403036202910700604107030024110320f920607805010000e446c4040150210b4081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706242607 1250 706241357 706241363
    0x2130b0901021c0c020d03030e03031003020a0f180b1206042105030c1605071a0705011109010518010905090903090307060906090e04170f040e0703090201080c09030a05070f03 77
    0xf2204103400300440da210125840709070220306000c1c0d0300750240c1880220084458001d04000c00d920b800d41440614607841294103180b180c510407024411031030000c044100070306e2004d284840c03030b60401921081201c01c1851914240d070f03548a03010040d0303d03141118a4403482c154152821458541044202c9806528004980c1c103120fa03040f50005001d0401d41f8000c8a030170f003142c0c2c20f081e10308001034504015040d068072148240440003486a1146101351040340f030b00ca8019803031721a18500117094a030054900034861506010307030071103a40d0003001c3d030380d46400343c030880385031900160b00507650f109940d0807150f00b000c1c4201c1005003030800000209002e56054084500140ea0303200221a10b4500d07020b0321000813141041000f5120141c5a0707941c026000b0000302c0e0b035030020041c400c1030640c40407030300000c00311000c5003c0100701000005a607005070b4030b080034042d09906030300081c52038500501460b8140004510705032582c40c204042403005078880c080350030b0aa1181c16075040503129202c11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706243857 1250 706242607 706242613
    0x1c080d0608010513020405280b0a05100e0d0609050a081206090402010504060e011407030206010519030c09050403050c0d2318042f04060e120c040506030102130b090102 74
    0x1c1c20980511445110f04288141803134049000d41c20003000d46006071a490035070f40b221182102d2020380041465040011000004400c140341c01031022001d0310350f209520902000d0610030445410003844d054519080741c0d44170340c40c2410b02e8003000518003418054000d01c950201c0100304400c0c48000d141655280b031302c00603641d4481042204a000454001380041d01c244403c0241c03078000c2e02041e458030014101080300321120300c9006465001140300341e0041e400000108a281040c0504e004c2455907481844402401c44c3c07a032600920261084180c40c2e07036540c000030300341442002514514000c003810340b4401c1c409280c004005250307101140c20141500c14840c0c61840b1048101c801d00001b1440e901d001c540c0607002c220042020704003555607450603000d02140300071190000440114007042007a02c0c0c600301400204422003201d04907000b013002c030303400700003d0b203000a261940c004111800714060751080082406030040100d120748070000b0190101e030320076913200a05501082a401c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706245107 1250 706243857 706243859
    0x803060a05030f1b0f060304081b070f0b2b06081b010c0f21120501061b15020d02040f03021504150c05070e16090503010e03090f1c080d06 61
    0x205034075040384000c08070b11544003540541c1c1d0844c1407812100c2e1040300500980030303003810030702140b0158000c0720100c070180380000ea12611010170a4110301790900070001010b240303050408980e140724160007122104040420700c3c5c0b00320a0441c800001c40040d4a00d40340c01c8010061191000e42104e004000080c0a407038a6031410008050703008801190581d51184d4030380d01d030b4840342c94000288000743e4544001c1910110500000135031499011000e80d50610184440024801140d4040c1c008504009503954400a0451450030740c40010b900080c1c20f1050a07000b01180000380b058a0110344a14000314000a2513555030900504481c0261100603090a0312034401e40c080c410350203412a522020042048581d00c19034203a00710318490781c1280c84194a54010343c10041e0200d40071002c0321049506034a90913840b82001c00107100a038000c0c0000746000030629280c0c0103e0345054017174a1005400c1640399150740241503210030341d1604651800030f1b4108802a54441c0d01608072003414000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706246357 1250 706245107 706245109
    0x8091e1509151b0607080115080118050603071703210906040f060f06090b010f03060b09060703020705060f0a09140306040b04030302120f0a142a0708070803060a05 72
    0x455490740c40c01409010541120340000c0b003150840c80210450382070508107949510020020940135000e586c41350302c82c40d0b141000b800d001e8500780340e9403410052003000402407141555046050010341d070744041850740d9460f01091420600394800d40008180c4103c44400c03034004001041d03807a90580710079400c05145013110003a08001c1d078541c5541c0c0d2004001402040c0e100e014940c0b41131054801090340c00c200c10081c41a0f54a0360801c41020396a642e03078500e04c2da0464a401c0340d00c007807810180021440c000400d5041c2c06200304560040b040003480c0c80c1007500c02e00000e0046c080050859488a00c0380c204407809401242d500360104840c1305d8085110000601e480700450002801031003240d940341e0f58200300f6040503100301c0030300d80c09004442c4805201040389108000d00d0f9412009032421003484002e9507015440a505034602e603003031124015a010f00c460900d40d07441c015422094004403486041c3c820317540702034540c0d000030807440100b14000004500034401190221102c6450794 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706247607 1250 706246357 706246399
    0x8070c29090f1c050c0a0803010906090612110111031309021e04031101050a03020909070e1905150f070c0f03022d0d050c040f0906050f090d0c08091e 66
    0x820304107468200003c00500c03e200304020b104c1c0450070002da0b41e401c201130351440070f150001c0c2c05c080303201a104c00c41404180000d2080b800248203030725101c1841c0d007490f03c403842c50b10210801b030b0341005107036181112000130420454092030050f0500d141600c0c0c1d14004034000750064a808030741e1000c1e04010846100c2c0210549068a40005503e00a40b85010040d5669404203903414103040d000e101800459403540605886501d880d141c01c1c510305615410464602c0e140355010020403111031013444152214595550101a840009650b55640c3c50000f0300ca40590840100745010314600030030007c0000010000720b07132003900c070342e408015004e22004540c0346810281604010300726a80880740b43c54040e082c0c0190168058808401541010a0507035222620a5004581300c0141e4010800244182641304140440807a07843c1800d070002511001d06d01d940c3e004200200c0425414404000115403040000030080e07544a0421000c080540c0b03d41a481481002c2c2e81084c20340034802c103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706248857 1250 706247607 706247623
    0x1914010203030f1f23040b0a1206020c0c0a08070303080c03070509100c080a02031308010c1e02030408060f0708070306080304120305040e131407050108070c29090f 72
    0xc003d02d440a5620000004c02081c2192100700308000d000c000015a055000902000c80c00b1040751044140300820a100c15911200c0886004500c0d0181c10060b00140c00014139085034010701c090f0b0341d001c0403500a85854031034110707581c1c0800c95510000b0031090000f20f20088910079101c00000345d8950750815500d010032501d40300480d000300010015840c10142184140e421403c00c40d844c503815440c1c10741150080070310000564030014442c40c40e49007550080700145000002400b207242840e500619044c50b00d00000d182c0310341e003202e82801170300a0080ea170151400600f100c410f0b05d03045402c508195410b0f9007a03004120f800700440d26491090103039809071401c51000390b00d4035141920581080100e0241a0f00f080307000d00021413000c41c4041a42e0259064075046210405282400f0892943c1156030b05200c1d4880d104c100020703600482601d41c41645c0d03003425441c2c14268244042e02075075591003642e417400380c004180c851440c0c2040075400ba401d40740859a0607a80700c2c69156903030b0b4035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706250107 1250 706248857 706248871
    0xd05010932010302011b1203060f050f0303090603061309050601151106150406080316110616030e0d050303040510050a060e06100e0a0b0d0c03140402091005191401020303 75
    0x203000010f0000d5401104511804006525000e485218035211024410202412040001e88900703040041c0d102504a07030018020880f144d15000007800c000075928400c054400d402940080300060040c3c0e145042c03426025100c0308240325069142c940325403609024043c85440807022219845604e101d140300600c00080b0707100500faa600e6000701c0d80e8441c411288030071f41c4240c49a4011815100034000740400303100a019100940d40e00e89441d610303024841c0e8115000d10011322140d544c81729072445400c289034240c01c166400b14040310101e040720050f0701000d8518840001404104a03000809402c0703541003000030030042e01c59400300e80030b40f0400e21a502113036072414003241091801c04c80b042c070036060a09007182c1c0710320b910f4041602007920740e1204150b030a002c114101045034031b01039102450114031f01040320b101207103800c0045540241c4064021030f41e130300026402c0c00364403441c1000780c20300070411850943c01c00400c0c03401c1005401034960000300c3d03e04001c100c2d40004240d0340100b007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706251357 1250 706250107 706250201
    0xe0606070f020f030a0303050f0714030109090503041a0306040506060f070201030e0321090d0801060c12140409090c210f060902130f0506011d0f03030d050109 70
    0x44240c944400551600748160b070702a03c0c034041c000e4141e80400030410300d940700b500c0214083c5405004007400201c02403170a41407062041d90402c04060100c212419540032001c0042c5050550503c5032070350007150800c01c18105071100021b80d03514844059441140119000e10030780d580c0e02c0c280001800b843c280c05c10403441c140402401580207400004100160707204aa041c500c07803003482c0d900c9407500e20000c41265040024021402000d100310540340c0301d103050880e91945404c0c0e0003000720000507809441303149a03611448a140c4181e401124400300d03401280e4445448006c100014000414110345900f88981c00123501003084802108822500b00c0e840040c138150737103c040b621494400708441c2c2d1a5214007038401641c4080200a4884c0c0c0c45000144804540f2184811180d02a01c22418050020300f18100c2591103004118000025221601c01805403004a4036601461104100103420701c00086038040c125404282d90443c1c510002c2710042500584c1c800454040b212010094 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706252607 1250 706251357 706251367
    0x105030a091e140f0a120503130501051503010f140f040507030602030a02070201030c0e0a05040c030605090a1a0603010608063607020c0a0503060a150302030f010207030201060e0606 80
    0x55941d008810003409644020210010060003000c0c281e1004411184000c0740b071018420aa020092850030341c44000040070350000f292030324580203825a8181041210000c00107034051a158081108268090000d100300d041c040311110b4249811030241d4025882d28420b040311010502402c066003151004100c070a48601804035900003009000351540d11400d80c000000440500c000d620440d032022006880d08114400101a6549102c1c054100306a00081c00401d0341c41c4010642107400840d00020719041403003094000e000a6484254801d03007a40801c202058190048844950302c5103010081c0d00090342085043c0c0002e0040f480080c07070303520000c0c3c454202041c400038465024056101000550341010384c04242c8804e150300504418070a20107010340410030a1036109044801006980c107000c0802e644020041041c52815102c00c250303156003040d01003640203542c003c0c1c00d07665410b0421138040d020b03521003042280150301c2c080300000c00343c8032901c44901501009080c94546 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706253857 1250 706252607 706252621
    0x806010f121a030f0105070e0909030a08090c1915050c0304090209011211070c091802060702042018091e0613021c05090102160b04031107030b0f09070302010503 71
    0x41c1029142c12041c1009480000304666040005820350350001002050f10324182400800e18120b0b00140d0b8000c41d540c01c10b0002e404804010340e140c0501a2502c0801f0760740300010f035850042c0610308541c0009044c40440c1d000d42003458204141e5251600c1140c0c003154181044030544120a60001d0540051209025443c025001000c800e41c05246c100000a148802034084500b040d00d0703808000c030000341650401544030140c50040100e0001048180600d40d1552050005207000920030710300040c21804540d650f07030040303850441c60300c1504034207801e4901c1c40600e640074480e51500c10620b0244c07038409144c80a5102d00c203000d0401d5a80c04001010070f50122814007030101c0342d0212460007040496480da02c0504020151a034200241e0013400c03603003e0469401800f1180680d0041103030440e07103000d204080c58100c0d8046521030803036441c1d09088540007007a2a09107050701401c5800000d1240c5507811a0080d0425410710f00c4544500d504590b44846520000f40800c20900000d021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706255107 1250 706253857 706253861
    0x100b0a0806070c03020a05030a0c120908030d020c01020712020607230f0705010b040f150504060f050d023c030a020a090f0b030f01060816120f0602091c030806010f12 73
    0xb840d0b10a0048030681d1000f681d030223003180c11440d44e62000411441b200002d001c0004402030300d00c0c0301c03802d0000d052400c041c0c0b0304c2e44038400d0510303070f017500c13500050803800c1e28509604492100303403c14000306891024200003912014280d414100144020300d0000c080188100780803241c001038040c0d20310300041c200300d4a1080d08101415251950b0701d001480e80381d240d602440f5100d06100d1070005107240c9103c040e025030a22a0009c501461030300c2c109000c005851000403081e40c1d81241d804414005510025107803e0032400108142510907900e007071034200300200099102078104031811010811020b15034cc0e449100d501a50104a280080140a41580c00785011840d5904003180c0c458440700424500317a048040030744075030355a040812038800300b4054112425504107080a0a516141490071101d4900d01c020f8807610350980302404101c0d003039045640400d0050150b00301c00503445491494031074409008d4003c10598ed0029409605c1002c13480c0c120f1707065403503049100d8090004400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706256357 1250 706255107 706255127
    0x90405090d02070e0406060e070e0406061b152007020a090b10200d0503090c100f0f031d010203060109080102090303040909050a0615090b0a060c030804030e060309100b0a080607 78
    0x31503540e074140224004000b00781c1c0c2c0d0310078046032b15420b072085064424001103c41940c0558100144062440d0034000c02c2d6002c0c1d0540790f0011151842140e16105180051200b4083c0340003c00c203005404010359041c4015000345402110514091650342610f1015600a820380341c0e030051110082001c810b0141500308114100c1e050300c03203100400070101e186029803100301c40300071401c040100620104104042214500180e41d1482188803811000e45500e062901060034040c0c0920382c078140b50f01c81e500600000e0750014807902e02020a0680f00d00035401036442600003100c0450100350384505000301c3d030806401400451074140f40c485108000d10400f03004a42d107001703005010001c5102c034019443c900380b10f0040d0000a528080c803e00c11900d01c4501103018082e004030401090343c00c00720201481b45c041c100030581d595180790884220112180c803030342c082c00203c00d01a601e0f500080360743c00703466001810850b0f17588280c104031110444d8852045036500000001e8000707440303104184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706257607 1250 706256357 706256363
    0xe1b120106050301020f0d060f1401050c151305010b0f01140f0d020a031401150909050601050c0d0905270109020c0a0506010821180609190308090405090d02070e04 72
    0x8555450380b00081c00c0e03034488010300c400303a44040307105902d21100b0310464008180400403224424035107494400542d48601c030a6060140c04218000e030010705120200351722084100100a524003103040c2501c07030150071001d0b80d0395840c00f14903101505103405658100300050b151804c1f54951110314204a0f80155a01c06900409201e4446628420b002516200c1c41c0d60714040f0790501906200c011451050707000300388800350030580c00300158000c001131060350448240803c1a84e280801664035101d80d0401d540c0611031107d4034503181e50700581c6101030380d0003101c8059180f00c2c8044032040601401d000091000340c0c010040001060300e5000b4440e500209007aa081103006403100da041603400d81c040300b01604400f4500103568801c8407041042c0903501280c2d41440b80d10a0080380d8299a000c4050080c1000201a14035503a51030884982a04040d0b501d215561245800c0c880c2c2d03040403082c98000e60801e0302040102c000400c210b0141410303980241011440d0a40f0b0140d01ca501401c25 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706258857 1250 706257607 706257611
    0x3091a01064a041424090c0a050304030c1209090e1212060409080409050f0609070e120c040207061e020901140a120207120f081501050913051305010e1b1201 69
    0x103c04080307002c4101c4d0302c5189080303c80e62400240240c0760151401d500d1903248039440c0c40003003050101071041521f1000720549080c5403242e17994502500d101c80b5031032010f84070320214001031404951051010301614074180040c0704260424504030354a880c110b0b402554000301f44a40c0f10345a21003089554070010017080441c1003903054030f900380180e002c0d0b005000780540f80c000300312844100c0f402c0e054100c08161183c05136403801e40001041003401e0312010b4410f0003444d0010780d850a0401c0b8654540c0801442190f035107e11b03140603801051544d1000800071002980840c0030616031007550a43e0b10103031640140044c2c51103480503035038042c0b407888040c02084002100101503e01c043c0c40aa4402e00b0f0040c4d1558465601501d4000c81e91314060800141c0d40400144510401c5000c0d0516400e007846511040b006001400c07400c0c04040610b0a40e03c0d040030031020341c10009041c09502c1c0524001c05c040007100d0029510303900107010300441405e0525110659052012588100000c61000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706260107 1250 706258857 706258871
    0x5070507090203010b040906140109210519020a0f050d0b07030e0d03050601300914240f010b03070815090f061203090d020103091a01064a04 62
    0x4100d0481c3c00a03013004002c2400450140001103d0348550130107042c00703149a0188401c040d000804080c4a0300814480b07444c81030700c248000300d01c0001c10f44826441b0068070840c114011700c4010902e80603c6c240d1103940403800000301d035440c488051007600c44c00360600b80c13803034902d40b16542407040181520040541d01d5070311180c00d0a044c4280041d0180030342c1d02041c0b074240322000401e030701081e09070320038085800300341d80700070a0750348c640728042c28a0070201060b12481c50610504103030080070040c1c0c1d103014001c1b1416288840842102c1d03008100d030745245150f15000303003c09000c00240a8070040c03840400c0071074240c41c0620711040e4884014009401380400500100e00d0318001510b191036009843c0c07091220703910f012040081030900000081d400d00f0070b000c0010310701c1e882c500c00280c14596584141000e110356840ca40e55802c0c1c07500c038608107959582a000f01283c2c0c0940052900071a29881c01e010542030002c4e82241802000340003884071080020036582d22684541664030940d00c0305 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706261357 1250 706260107 706260119
    0x1020a080a020d031b0903140304050a18050906070f0311160c210b1f0b0304050705090a020c0a110a151e020a020612130204060e04050d091505070507 66
    0x34000001281d01a0050200d683e0000d402e9802500307105070354416400310454525848003c03001103c1e04140d9455080c40050301960852246822084d0052190070021907000381800360364040210810040016076a020b0f481b50f00d514090f01c00e000001c0f40a80080704261182e00f00c48035200714000c1c501d160a41641c0c508001041c2f030142102c001000d0f0008202d414010002080300c90030f40021903145841664662103510001400e054240e0713418400100800300420f41540900701c1420107554a08050600596034045846035a108000b13031400585003d030720b0700907594185140001449207801c0c40d40c809002e02c105140c842d400480060000178088103040641401d080c0760740780c40340307c84070202025000454404a140c1994030429000005031a41411074402c2101c03105410744503120420a00c4215041400195000b428034001003034030140e02061038000ca225404841c01d68200d51002c0d00c0c0704003c0d1060480d0105600c080311821405031008004847c80303401603401181e101c00b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706262607 1250 706261357 706261373
    0x70c08060f04171c05311e1211100912050306041e0606080a02030121080906030109061409150607051009030c03020d020309030715120911040b011d010e01020a 70
    0x10b0b143d644c103629202400414a041d603040c03052010b106019544101030f072050702c019200305035401001c42408205400440e4004802c5a0001d039220200102e8562000b6000f48040b090200403c5280036134070352a00b40f22110b120740b55000703a100000f807603042000c00e0180c405400003400d103904152103003140346d04002450003038050000c50040c0051400c1c1420801050100000e1003044d020344100300600584120414020108441d0100880b0f00803e0385403410180c01054420398000002000224078050203412060654802030000410881d124003007115651302543e48000d50840b45403100c1d0036083c49001044014011000c40700380d0070506440008403006550280c00042c0c940311004201541401a5028800a44011402e101800f80041c0d264981031044551804103c500405418081c42a03c00e82c50342e1001c007040220090b05048650495030000700d031003245819104c070125805203103070905101c0c84200c84e404060f010001501c000c0307080359010703041d0300c80c0064450000d1640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706263857 1250 706262607 706262647
    0x1107031e021917010b01030504020906090702100f0c110307030f120605060d0b0f030a1a040f12020a03090602030a0801050603040c0308041403103b12070c08060f0417 73
    0xf030580c0000350326a01d41d040e085a039201001c50405040c041440090b940e48400c080d0040c030102c4461070f540c0c41e00e45040e460000039941207001036007080280d6020200640c4102c030001425101e03994030784100c44050b46c69200390440140803c01c188190009148143c02e810416210072500080b229103403c006039040c2c101915100c0a40e4944000746443c2c01c0803c010030840a0680003803119080340e90341d12888009070f49190b03940300401000103081c014004400c103021504031088925583c11440002e44030f440606c015800310b440d0704170000da800d00c008100c0300740808654038903040342d00b400d08000e031941c0094002d0340c00310302e80740001c004544540010030003080480303044120700d901c0c0b20516040048655912280c0d034601340c1c80131500300c0000c80c000400709080140817519a51103000f1401c0d5907000d18819054819903042002040ea454010705880e400b83c488290119641c54001e50f07a1384c3c044801350740800c01c2c000410005500351007070354000c91090f16540e06000311401c01c404800e40d9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706265107 1250 706263857 706263869
    0x4031a0a022704061e12050307020a030b0411091605090a090e0607120c05040306022101180e060c0f0d0902090c030105120c03060c091513061107031e0219 68
    0x3002d00c42220f207064841c21000f00300450480040840080210b402519180306408504000400020402809108864150b54010007101c5040d440781084020580129001c4a500c5502041000300786400c0c0c001d00d22038a0407000d186509004250b0460b141c1c0c101080840e000080d031240495038000c02d00030b01c0070603144100281920714040c0c0004090140e8010f10300c60340c602e0300b00c603001044d80c003208460550b900070b0340140e41e0b12245848102000800c1714280d035000716400002c950410030034607218900601c06018000b108200c2d280702d8035a001030f03c000006078403c01007a501a00c0c9640030b0520480780c2d082c001924034480c1c0115120020440d00c51b54005000401804240703054689914480b45650041c61a000300c040481e9980c44080e10207620701e603005c1601400c81c1d0f1403a105410082580900c00c0d1914441900309101c0150b5000d028042500085482441000002c0200440707401a0980c0d403280481c285408601144a1007a0f03040030322880004042d101c404040802006 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706266357 1250 706265107 706265167
    0x3040f0905060901060908030405012729030f040b04030c05030d0213120c1707030501060b0931090c1215050112030804140f1209100504031a0a02 64
    0x180680800c0b00640d0160004c40a01882640511441f440001600d05440342800e05076904494019215041e03000e50b901c10304080140303800466084240c81004540d07440030150350084200109005540d8041100c0741a05800b0000c005000b140c08040d000d030300980a4101841e080826454980c2035038001e610106011f500003440d011840d0040c2c070810300a004003030480c842030019660700c501d0300c20b40d4490441980b600c0c510b035841c40802403019000440d405002080450395909d40f140340b607080102001e224192050903143c1c0301000d4078081e0300e030700a40446011001f9003c121030006002c1480156201151000c2c041101300100c10b1802205004181005c020003507500d044042d207405030007440320b10003410402c200180e08151080d03041507206440420404a83e1030892900e060642169418401c108222119448150042018103010707103da04038208000000e580d40c1c4103502c40100303415006404124594040301d903054201c41079000140c41c00540c0070190026030702190000207005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706267607 1250 706266357 706266361
    0x32a030212160e1e0d02061b070302040510050a030b07020a17120c0406090513110f0d0b0405061c020a0302090108100f1b1103040f0f03050d0206150f0303040f0905 72
    0xd410000c8010f0300300d41210000e504007036a4040000c1e04501540180c000e140300c0b8a24421940d60505171026202400c407513000c2c0d80340f281d403d80d9031401c09210a0380628600300c082100c0d001107020840950b400903200c807542c42e20310340d2a000d000900425000450156103660030000790440000d980d442504400700b620740c64410500d00b0702c44806071410100700003c1104100c41608450110100c820859480c40080706164000c0003400d50669801c03004880003801ca080001e000f8064102c1b44a1010100200030032841800121076040d6426507100b40040d180601d48040000c80004040c405810045041d50782d502017000e5903c00e0b00180c2058000d0a040e80c2c0b40301d4180305582d05c1c503403912010300c00c0c4c003200b05911851031480880d880400440c0172a25400e606c0030001c54004040d60084030302216980c1610381c60840a502048549000d9003440a00b01c40c03002450b14001c0484400c4d021075980220104440d400f240820141c060000340800901020140e50140013000910740c0400c4078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706268857 1250 706267607 706267651
    0x210c0d082a150106020d05090a080303090d110703030c32010c030f090b0406020703050c0d12050702032a210301080f2a130c020d080106032a030212 65
    0x807005000a02c1c0c40c0d000d18074010401c00d58002021200e550490510642c1e460588010a030091141e410000040c0302c008240425807000241650610303c065941c26014504500304640340c0321356100240014800308942d03008158140c1c4a440c1c40140c500c201c48000d091034000f000b1000302d00342d0900701070b550350f12402c04d00c942500600300e4a105501c0304100c0008941e6a4080c010350103400a0314003a400308090f010980600110707803012440e0000c41e04801d2071030100070002e00103032401e101d00d142020701180d096400002a01c3d0a103101c040e44081c540304982042c91041180f42c0c00c00b08078840c00d50a10060b48051084160720007402820907030b02c3d13041034020380c45d2050982c2e40e03200725070043e401a004160380719241892801040d0303010390501c102030001070644c1a1108400261440c10b440041226000104c8090701e85198861042d140c3c2d170b41030700307904451100000102d429250540c040c15540440e21400400005080041c2060504009400c0d007a03012107551746d00c00002c070080030407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706270107 1250 706268857 706268863
    0x5090d050a110f01050313020102070f03080406140c060a09111801090e280302010908030703050a050604110405060d060b0c031309020307050d05040201111b210c0d082a 74
    0x1010300f0b54158100400c8100024014480245418180e0241c0200001160710921100d40200f03142001d140d80f054072800c0a140d903601c240301e0303400400e0090801c4c0c841012100c0c1520185503a48019290070340d904a401c0300581401402114450b4442100304820f13138030101174080341440c1c60012019507040020f00e504580c03000322029080e600c21010035100c100300f0602c0980c4111040c00d550360303202080c9426405401d0703c000050001902004100030381d40e05900c501c0c801e20030301505000944400003440b04503401045223480d0010304000a10150030004004d084c1d114060000190756555500c41c02c940d0b81060321525080d400029100380001d0000c000395024001040c0110301d542010725000d031482c0b16040d00001e1070380d20b8200140c25603003e40c1c581b9040540900694140704040800341c050b4610801056204101481100a805e010301e00090a000a20402420b42c000da1104004440a41c10301c00c41d20700400b081003908403482c5580810b0400000c881009400400381d01d2182 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706271357 1250 706270107 706270133
    0x102040602010e030f0306270103110108070906120218090a060518060913031707080612062e0f0b030609390706050f041208040302150705090d050a 65
    0x20f840d50081c0405640c00401d442107a0300b100c0115070384210ba120322890b410041d0001114141c0c441020000041800710031803540c4d04a0400b680d580c01070742e0710118142d52101170307800343c000004c6042c10296a42540b5078020860b90302d080a03045140c59901d800126004d40485110704103540300c040c100401e0070300c03092099400e02c49150640d542d141042c0410b0307100d01700912855002280b881040141801800020f48a4105681164075440d1002003e000c4c1e00342614101d020707a0307000c020b200c1032000115106016220785400c100b4200c3c0500449024851000d1a2090740301c0004000140c1e56880398015000b401040c0c411612890008108009038400502c03a128207c00d41074013007105503406100500c44d00d0114400d0044001c0c540c41d140050095140c0188071510303007005c1c003005840d4605028444c620440d140e036102c0320b00b03003007c03100c0350820385000700507034010914900e00054004002e0f5020600d8a0910304183e1402c0000d207410b0550310040d6482e80100440c00240410800111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706272607 1250 706271357 706271381
    0x30b330c071415250204021c06080d05091e15070302071a030717070e1203030405071d01120318060f020106060504061205130209270106060f12110a02010204060201 72
    0xd0410385900c541d40401c1c06180343d800d107480c03130f01e51200e401c40d92a9030688d820581d000c0138170340b5070307140d241a004010819400703041020300c03480105d11041c500c9003041f01c42c002406003520311034064461910803801c4900314004d40c4401001000c171020007602001e0045240a0350081c4581803410943c2050b64080c0c24446074070b51410010003035820b402c500c9480503c5d50940516041e40d59038081120b00e04c6150311010780c800d0010000340451500040694020360240056998503540d800c10b400881918000c6034410314264001040900e40403a4004c0381d00b4044e0400c1e580c0c08000c0e81c024045200190001d801007094120b8084000354240b040c41d018000a0401b14546410084003402660b440480c00c400291120001002403413407004c2042429400b800c422410b003071070752940a542e80945860441c1080ba002c0b0340601c28414050380c02107460b191a070801c50305039403208807562050351514400301c680340e500461908003e000100f0505105600050b265824010024251040c000c858 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706273857 1250 706272607 706272649
    0x20a030209430f090f060f0905032803020a06021c05062e0207080d08091006180c020a150b0a0b0c0d0507030c12030c030b330c0714 58
    0x90364600d82c05809401c0c0004641c10100008080708200700d50064554004614070590110002201c0d90800c15144070760380e0310340303403040140c0e00d5a007416a100350600c03a20319001030a03c4031526402c1740024108c5580e000344180c46840a40340c5400c0140c3c3d02c0b036207148803041c0030502d100e40b102001d84074058002408a0744c5126511400c9501001680404144a40815283c8801802034001c21002d8005c1050b2800d42d141c012001d40041d02d2400221602152405183c624070100c40301446900c05640301c0000ca1040e054001d41d583d4020704500282c2401d601ca420718440114030203140d051101003241c2004595002820180488414107900124164fd41070100d1680780d94041003106d0744450078917060703441344040e080c120351180d01e5545c040c0240641c02c0d0840b45c040d034540c000011041c40c17a14103211081e41c00061205407961034207142010004000300758000c002d8042c4052106844030340403400d20b0005156103007403540c25486150b03103541440120750030341010310b50100241c4000d80c038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706275107 1250 706273857 706273951
    0x11e08010e0a05070c0615030c031a060303040b0415030f181511090d170703030605031c0f0c060e03040603050a152601060e090d110105090712020a030209 68
    0x4c050031010f8410402400e0a031200c02243e44030032205200c1006581103100c41240c02d0740ca0504241c0714141c00e901750346140b4503900140309410004211012924000006858a80303403881d95940e0210090302502015124810414a00303201d02031000728150b08030b0041c1d080c200914114000c4600c0b20503d13452141415540c488810841c010b50301e4024003a00d98500110340c9180011642e0b481c18041c041800d4080b070000d048c540e1642c0540d040d500e040e0126a1540900300034418403021140003013000414801e00240c502e407140d162040a144541008902e01521301c00b00350864200750049000681c2c1c99040120303014280c000c100c500820841c03101c1d0b00e642803003101458801c9440e80d02014410200b1403000804007544010014058442c45000c81d05000090f262a629a9600c1d5030014464151107021244103105550241c00030000a25506142064900c0904040001039910014403040000035888103030916114450316412105624050401002c0d00c03213402505d40c0c40081341c0c0403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706276357 1250 706275107 706275121
    0x606020118060f020f1b06070c0206030117120d091b0312050304110a170624010e040f0905010b0a0902040b0d050a0e120c070b0315040b011e08010e0a05 67
    0x40d8081d1564110074045080850208400041c0c46103c1141c8400c460000721035050811501400ca41c48035203106a90543d100c03c00d0449407c0c91151300a5030100c0700300f004120410700300f2080d4070400441c0058601c4103003d030f1072809940e00956150080c3da91201075039000c00125030700c0e0211605484842603d02800e6444980181c91443ca44805018001001c1030038010401c0c0402c80350340c4020070005e4210740f9690040100401c401e180c171070600c030710004641384071010f109030200c603001050102d00071038000d00111150030510203103d40117903541444516040303182c004c03901014016000800d400d52010148061503540d9800f400580e407044c0801d000c0c1c0c900d400c044607140a107103503005c5001d40703400d080203000340746c80c44490710f07184141448480c0181c140c0f0050451007400f90f0569143d0341d690300400c0c12501c801c0380d0a45150119045404491a15a002e02c1156406142c6240d00950070712104011480d100e04010209811400400c9000d1518800070360211104000f840103050a207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706277607 1250 706276357 706276391
    0x3010f0b130b0d1b030b3a110a0b1204080315031005070f0507030e150f0f0705010b040204050924060f030906090a050712080904020315030106060201 66
    0x8020003a40100000324010801c1c115400c401c06002071950156503003001082a10051840704010401000c0e2a04103101607070003842038643c2400c002d000c040f0744560b241d800c403a1402d240baa00002d84070441984207240c201d51118403090701d101c2c60441001e80b09000400001c0f0345154848103d1440c1080500044407d21794a1600705074045840b6880f510341e01c45d10314800040f00e61040d01403140c00740300c142c02d08094000e0b03030107105c0c03a885103d80c039000c440b001c562a00c2101401750100c0c0150358055010300301421400d01440f588110142400030340740d2103140d150b00180742400400c002049140a0000030710440340c40b050100c80441c0740074079103000305007000c00040610600c2c10761202020003c20075280c0440941000600407603940341c140d00111180d4000b40c070f07110b115100d000c001604903100083c03120003c1c2c1c0c21400a00c00e43e45094040c1e00ea148041c58205d500040c00d1012087c0b0751114006140980054400180f2000f1500141421100c0581c000000c580c145083c00780c03e40030701 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706278857 1250 706277607 706277609
    0x1061710050c04090f09030e01390f0c0602160e0f0603070806090a152313020409141c05030a02090103090c0b13120519020118061d03010203010f 64
    0x8503a000c1041e50740e901c0d00a8041c011503000900540c10041031070169801984000c0085120742c88110b2462150001101d110440000111922606288d000300002e14010b0306404880319a445515420965035005400014411304680400c0b030f0702800d00810f40c0501a003007417982030200b80815036140542443c0060000f40800034240f44400208049440034449540540551001c0350134a003001208030346c1e1050030380c0007941c030075908500c1842c0c00c83c2030780100b00e21440e00b034544e602c92005000c0c541c00b200030040d2400784a401d949211b10f006850f14056404045c0c011440005202c0600300180d003001d4481e102c030946081f070044c00310700458004003544e0304500700c40c01c010384034004500140c009009482006c0d0500380c0b26036002919a50b44402001c161000d2401c036510b1955818034000d0001c1c0c440c0b4000d18a4120b650400d12007031b80e200c82c00c145940145080b4030700b9407605202e68014061604440c00040745c0840919505100d010a045000c0040c0c008601d150315085503144071200c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706280107 1250 706278857 706278883
    0x112020a050d1a010308091002030c030d0b010c050604060911030109230304080105160f08100b07020a121202070f0503060604050c12070f030506060f090d03050c10020903010617 78
    0x2844080b2018407001a56410300440480e55042c0f46503100d04040c0c10301d8009000040c07045085030340c00e03c5032500c0401a85c02c1003001400844c10820307ca420380c0040c028048095041000c0d120b146004181c00300720507801607005810010340140c0c58140003800e6580c0074a1903001c1d80c146020100010b0806640c00565526003190020b14020b42c841c40b4158841d83c0c1c00240d40758284000d2043c51100180043e40c44213042d11800d2948032010416141007600300d8218503010b40300002088401e4101000b0442a84000c202803186a1910300643d5101c51014040c2c5000000c0084229210740400c083c2e4003402004418081c61441c0400107540c807800100500e00803511360740030421840020301607d180f444a00b0301207001d0319140314000e21901712a1085c200181c10000400c040d402c0560407100030608140c1307814a80b907100d01c14844090880b160031070400c00e0403c0f503a4400c200030310040304000c01c0c580c000369035074480c0d20801d42941d5081d00f08180c02104000c040b822920009080d1030300b0703c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 706281357 1250 706280107 706280119
    0x4051c081602030f1b03070503010905060c0702150a021b0402092b0b040b091501150302160c0f141519020106150302040914091f09020402210112020a05 67
    0x80c0b84003081c2440c41e0302441001034841e2102945085107406050542001c041d821150003580c0d490030517082ea08034160141032078100b1004100b41c90725086c0245100380c00074100e00d040c18446607076000e03107600c200d03135110058000389540b44401e03191080b40004402d0460b41542407203107150000388017410580740899202e00091180407102801101980c5072070308561160114138150408460840c5d00301d98041c4540108045c803075a61048000a03030580e0441310031520f2016400e14254003d6000c51344008480403c120040700007036051106001901d507600c96501d40c0c07441c0521407201c510002c07940c0d41c8241059a101020f031843e520690341044c08220040c0c1008201220680c010611a0011101860200707278054031183c05800a1080f100d0005040100c100a0191913511078001d841c1d661858011401034074600c0606408110007992046000030b419034182d0000e000c0b079119815800b285507944000c0c2103012103a07886c450061440322180c0810600580c00507260500900580313111324 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 706282607 1250 706281357 706281397
    0xa09090f06180b04110a020303180102071208180d0917060c07110a0306060e06120f0d030f1d07150219080307090905040308090d09060c11010c021504051c08 69
    0x13a070340b40c00c15601e4105840f603407640c460529000944a90040302d9081c810303c030100078244030010500c2102c0c12070360401303081c100d47c1540076800c1b14011000342511500e40125500b179089100244080c1c001c0c2c1100b40c450345040c500d071a075044ca02d40f034030080c0750b03059400410401c01c01c2880c6100307d5602039405040340c070060100100142541c540d5410103401c0074980080440c3d080b000422445c040d22044910b80b2280c0c00c00d5072410307907440420840c410315030400e614181d00d00d4002e800c1000c0417410f503070740819106c0c06002280941c1c1c00e9a00c160340b840e44000c00030007820114403481e02d04510284041c00003440651002c14080302900402080d048000000804080c0b04003000b60245c4540141800641400d00300140011003c2c1d825018a004580c402107500e0300030191001150300ea0340f100c131584009515181007058511003d68180b21900c4800d000594a150100040340c240301c0f241d548681c1400180003110100031141c401c0c2018401c20301001c9401a4191945102021081c0c180c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 706283857 1250 706282607 706282609
    0x12090f150a090c18050a050a02180d0203010e0d0e0a090204080706110a080a0e04050609130b09010b0a0e0f01050105090627130f0b091003260a09090f06180b 69
    0x3c1d0300203511284910060207501c11441040340c1000d0b0007850201c2060021740c4401d80440124840c01002c412104202c481d43d2055081c4040d40ea070300240001d0000401c1c00003001d0706400e140905100500140c000054080545413101c9618050107142c002141414200588a5510341040c003d410520400c00e5110050000400a0000c1194002000c5440e000c0100c40606840d403200700c05c0d0310582c2404c0c00614241008204603202d40381c182d81d03641550410751215581180f0240c005c40031552502c00c482c46a071900706415004100403403e46c01c4a01c0c000f100049824010380100741000003c1140c1c100b20b9548500f52070ba02412900180d1f80c10500702200b01c1071451004082c1d811046014640c0440700e441d503c603020b00b2180200902c200481e001c2040f0502208940070309080415440500106040c07009032810b6142100568407207201c0d10350190b006420101044c1c0000e118a102800508604d00482d11000c40c842c0c418045d5034106400710078288240c07488080c0702907036850f441e909 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 706285107 1250 706283857 706283873
    0x215040906150f020c010801050d11060403110a09050601050304121205041103010f11031b040909080409110304050a03080a02040504020c0c01090e010b03010302060d0b0612090f150a09 81
    0x40c486210108015680e544041c0c1d405504a0680b02c04980d08210507500d460022031400d03014141690390300d200b0f81c00c0c1400c10000c1d0001c0a0240c0b10212402240c030541d8403000010805580912240141c40804008004900640750409002c003030074101844030a076000400d981d0440c0d400348000500c1148400300319200010070400304000d07400c00b01070000f4050050189080c841d401d5000740540c015402c51941650481100544803903810800601c0e401103d00c611490049410344241c40d141e5503050103000c4c0c030303202001601c02c82c4000500700892411881035103003d03035280c60802d0440ca01521a981c07981c40c40d0368040c0912140100213182c0e0202e40d4110380103014018011134503007043c0b1420b039540d40d0008071854040340e07881c7c8010440c4110041c219040311102086180765030f095600344480303a000a281d000e100d54850500e42c2c80355607144003030b02c16111003600921062400b45200c603d82103184083d079001390015601d00081074a404407483e4092a00300000c1031444c0c0d1441c280c82 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 706286357 1250 706285107 706285109
    0x708130204090b09070915090c09030c031406070c08180a1707090507020303060a060c0203030708040b0304020109090c020312100b0a0f1e0504090c14040f0302030610060804021504 79
    0x54824600300c1a20b08220440100d980a040a0b5080f200b100751600c0d098421541500302c0700e110340c02c11070810004822540c00000c500b484c1d6190014025540740c7d50300b10040761941085801280e4100d150b00d40e4942007014550208607131078000b480700c1440d240c4100c10311030300c20308100005034150703001c8843e225800d0b031500511070304c2c40d0303800708a03108a030345c47d201c0c880740c054404101e043c80e02081d45103100009481c01000010300039900b00b4903088080d07400103410042260140001c0c03100001080700710002d8001000041e88442d80ca1070140f000400c2203e40b600220035240c504504288199070000583e41902d2417500d1400f5152211a43c00f0000081c951206440d01c1000541508441e840020b01d0f12020b4940c41b1b55a4099103140c40d0b054560040210b440050401e12040040385e6840d000307000c00442c4c80c2808150110001e80c40c050550141d0000b81c0c0d203150020041085003402c100f01a40202c20b0f00400c0d0070035041c1200140a0134014201a01ca0000c1ea44141540244082294 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 706287607 1250 706286357 706286359
    0x62404021c0209121c0e030606030d081b0f0408060f040b0a0903020a050a050304060f020d02150a020c1506010f0503090a03030209120303161b1208100b07080d0b030a050607081302 79
    0xc1c10f5851703100c5039281003007444116400003003407100f603503030541800a0300714002c06c4004e002d444d450b04203001c22205404000c00d6107075006800a80d441410480c00010036248102d1a00640d1352414400c0312442c200010f4010394485072000c040002041098460760b0304000b00c0000401c01c44510f041c200c2c80d11052a80c09030160140c0c081d05420020000300030411540c294a0f00242c400d070f00901607842d13803045620030000d40c01c10301d00a00300740382c0d00d2182c0e0f500104c2d01c00010704000c6007c5090b03240101131108030007110b1005003806007568000190b86103042c220f2070703d85d140d0b24100034115101c14400e00001c00741034000c0b904d0344d81e65549080180303865034141c040b40e85a1400103011030a500944510501090348801544c1c08007c440c455000c2c0503403c12503a01c24401c03081c804440103e4018181040030000020100e4402001030003004a103000e41d51b40c5440d801c1e80d00302c0408688180009900c65480b00402d0000504045540340c2d10410b14149043d0390340c1c03045041003076565044802 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 706288857 1250 706287607 706287613
    0xa2a05093d050c1515090405101d0d0917010608120703140706090201030506010528140a090f060306030b0a020f09180a0c091a1b062404021c020912 65
    0x403000040848240c070f4030170040840c05240150f014018003a400106580140160300421840301d0000421303006181c900c4141d0716501e48540c0e40040c21400e10300f24603089000075042c0d5a04104904003800b003842428490070080003014070380005540c2c1c6180000403203850798004540801414000ea401107440340680703100d241c0d9004d091509000819000508a020a14050100f4429482201902d00401d07050b40103e55021817140c955001c0940504001c042243e000b0081c000b50070043c01501882c4566110440c2c950f06043e01c61601c80b203203400280415180c04001c00200e0031010a080c0c009081140040e41d440c00030302451007074401d107044c2c1500051a000c000b40c00103410100c251044200e840300b0000b900b0814030460344007246109606804914840102c41400c00000078414035804010783c0881016810410b1308002d07084401c0104807560401d81100e1076100e9131070a0013500304031011440d0004014814100d200c40c865148403072580820801040c1c1c03520507002d00501005811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 706290107 1250 706288857 706288873
    0x51504051b04120b0907060c020d02032d0105060613170703171c140601110c10030903020618031c150312090801020c03030a2a05093d050c 61
    0x901060b0f01c415042103914180700c40c00030b120040c021a040d42600e940d030703488000100264080000035101d522003664140240004800004184d801d502c05140302003200c005265060068a421944000c1005004010820000b04481c9032915008140c0b407032820687c0c0b141d0b0010103100d00c0e14069810041601d00b021082c854600c5a410190202c005d5180984061440c2c00740600141c4e031026051030307030b0500c810011880707540c085c03d0704062041c03100d0304494089082c02c3c0002c1111041d08000c0c1d010075514072030101855814042c05510605032180716601020303c3c01c0c9140d8902c00c1e00042d01d0b003e8019241400070200039048103070340420303580e09440c1072512030500d070030303106003130341c50000481e8503594001201d65041c020764001c111500091411959892818406003064505240411042150449212180c030140030340c17002c40c1350b03902d545512080081c000b00107013250540301d820001c5004d01800b64002c5034800401c3d008010b8288010314a1074055490780161681e9070f18600603001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 706291357 1250 706290107 706290119
    0x1050f010f060801140621100306060530030d02030109021207180e040305120906090f070b0706050a02131401120e1b0103060f06080a0b0904080304030e0619120b04051504051b04 78
    0x150920035203002b1001000a20354600401800036a036841300d82c0302c0c0341100c0546d40b0090000200141d200b040c20240c0345000c3c00c514849040303030b00c260000340c2210790200d030701548031281000603940020582030400c0e030040c0940007892403402512a580791000c8420000d001c152040c03040c0d03000c0051800d00c04c56541481c402c00394882004a50070782552044800134039403c44005031034011100c0c007280c0f240c03a0168944a03400904401030000f4842c940800051602c2d0050543c076400620390071000b0148200030b0800100241c24001c0d40d218880c0c00c12140d1000c0d002c0215840c05d042065008100c5030048030320050307000d003e1a034804800c0420f81a00012850f4214400c0da1041d070085904106504c0b0b42070402c0780440098030054502d00003070000a002038011720004000f070000900e2a420300a9010302650700101d410f01001c00180e6410402209513071034020f550000c8800c079014002c81ca48107500d00f000110b84420320303108580b2440410800c0c50ba00707600300c0d06d02c440c3c04595030359191503035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 706292607 1250 706291357 706291381
    0x70b0d02030f060906011d03030903120403170f090607020111011a0901080303041e0c090513030842090405033006010c05030c01050f010f060801140621 67
    0x451041c802c0032aa800501075161880c02c10f44549070586642591f80d25002020041c0d00c07090f0719050309880700300003520081d5020401034101c0c1030a4034806035506d0842c035114040e5665040389944039141032040d000a40048410744203042015200f443d02c8091a00041740c207401c08030042d0b4030551034460a2605400300e42e03412840648141c56440a590b80c50290aaa91208a0f0094200200c60b03000b00301541e0820044da410500a4410007805511100040101c41050310748050020554400804050300920b201398481440c0030700c0c1c0c2e219210703012480c007001c0015812400d400210b0000c0061001c090490540b0340d00c01410501c50f5290038034007917590b0b5102c41003c10a0f00068031115800c100c0d5050900d030281003440c0b060a6989425005445250340014222002c4c042800040c01141091003124455011042c80015a52520750119007280403504524200851140140004c4402d004070386030313070002a030700e003030385e40c100803c02d00441811410301c01000303070310394013070241502c402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 706293857 1250 706292607 706292611
    0x50d0c030b09180c010e031c050f0301080c01031a130c0c0f080301061e0905060318030a0801030204060503010204140603060a0510030e01050f190504060209040603031106010504090c0b030603070b0d0203 89
    0x80f50485180309004001510002c16000c03105034141c1c40804c60203074070340840030300340c0c81c2e02180d0030202d007010000500c045d11a0030076040940d10760302030319641c6895039044c000c1d40707d1130080c2d8101c8614610b40c0030104264982c0340090346d02d402c2d00d900c20031540798411106015078541140c014081e0020614024241d54070038444c01d800107000f041e84c0444042c6080601010380740c1d503140d58811a01d41001d210360758000134560150b031b20200503401030328113041c001400c00760040d03503c040483d8114410032085840c2a003103075019a105210034450a035030500c10b008110340c00c88500352030350743d52000101d0300803098003d1178001c00d159200844880c3c01d40c00240928001400038001c694842080d920320714011122311506981140701c0d60328046444c2c0c04103801500480002d8900748080300400d050f05c645030b00c04c400040401d005050700c15814003650b03014103c101c2e001e005918554540c29140c440500039440214000000704603039650800c0600300402014120a13250300321240480029082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 706294964 1107 706293857 706293901
    0x14091e0a140105460204050619030e0a0803130501091b2c0403050a0302041e030506090606030d030e07050a0f06020f030a050d0c030b09 60
    0x94810444192462080040341d281801c504c0e08001156420b4150070f4258000744040c03d01d4a8160400d030000b84040340308041c0c030800320008000344103a070302407940801300182c51a04a0b1052907007404856481e242000101d8a4040c42910780d41c0100700200700c40e404000148400300c0c42c050716400d9901503400000e003030b0319682e111100d0038a1104501c8144005038070070422103c120142104d180190032130f490f4580090300c100240d00001510003000d01a012400d4403042d07110382c0c151001407449004039114048403444584100c0114041070760b6034014100025038403900050b06a014440290050a203003045a1040f00105415107055195000305d074000540b680c1c8240016025100082c1200e15891600c50043d2030503141e1803036030310942c10600c6110380b0a6046410350302c0d0f00544a00202d1001038581048004002c00000e80b0b81c00348100050000d0031221043c108600a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 706115107 706294964 := by
  have h0 := BRFrame.cov_init 706115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 706115107 ≤ n) (h2 : n < 706294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
