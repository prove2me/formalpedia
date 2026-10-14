-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:28.383716+00:00
-- url     : https://prove2.me/submissions/4e1cbc34-d1ad-4c63-9dff-6c7c1b2ae2a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 556115107 ≤ n < 556294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 556116357 1250 556115107 556115113
    0xb160c080c0102120703021305060d0f0c021c03090b1b0c070e150108060d0b18030331050706031a040c090e090136020312030103021504030f1b0f08 65
    0x11513444101c0143e20050800c1c41014010703c244500d1540340c6901c1c0c01169400c0b24900d43d40c44115250344041c020300040030704120b2500c0031908440780c001c40c650003129080201c00c20044c2140205804584070104c6c003074641604d04d0b0000700e001581ea442c91458000009a0504140d120180985846915001418907940c0d038001c0c00240c00040b05000d00c100003d00b429101d0b890b1400100329810080c01c00541810000400700f001c2d00c20202c00070328082c162005990762813803c0518000d2040c42c82440f64106004e080e001c40c1500c00c42c0071242e45607a4440040c0110501c0c090044000d0030443c0c0300702e045165403001d040b13850368492140b42d10303182c0780b0380300c460a03d89488808950044020080c1d010740c0d0502008042c0c03066420450a078000b0312542e502c0d2260403500501d0f401c81440e40c2e0003909441561019a0315aa01f1000746048271b108032121b59083c0040707420f0b03400c6809140700040c200340c0c140c400140007445507407403151581c000d50840e10700540c0d10344110040c940580d0011104e60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 556117607 1250 556116357 556116367
    0x1020319090f0b03040803130c090e1f0501120f02030309091609060e010906050f0408010c0507051603033c09090501051009060f030f0203010308030618040b160c080c0102 75
    0x403a44031a000408460030071031300394941510380c0d40c0a07120007842d0607400b03403550103c5010040000c00640207800704040420203010110325541e5102c04090100d842c20310134492020440c6814002e0f9810707207100101450910003190798009800221500407649400180070301041e41d218075022074802c021141501c2244a00c210001d821211260460f00410007150208012a600180c2d19411140c4502d07206a450809040280d000d00071508024810f5003000480006140c1c01005490b1440c003400656001c401c0b01030310403060009900c030007004030321480b20300c44c05800031032111806007540080e9012075080104601c82d40da20304614090100d4031100d01807007035103102d02c2041c1c094071007a20702c61104455000c0c080d0011002e4400c07403080020061080c00094400d0308403185070151407909545039610380c0341c039056582040380c00c2030003410b1071408c0100d00b00740440e501d801a500044181526224950140d40b01104605064103000c00204000e00041c1044000e00c203904214000603203134 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 556118857 1250 556117607 556117619
    0x813061b1205220302030c1209030d08091e011b0816080c09040e0f1204061103090a18200301031106030108060c160609030801080106050a030c090b0102031909 70
    0x7200c03445811840910300410484480b1090031104a04011803031106400501131408038918890015000b0a078091030485a80d055451000790442d420f08800f41c2c0c1c106000c2580072034a208003183c2010603684030742e41445202031912200e000c5624413074004260600000c41c030f5848862081c14540c0000c0421081000c4400345000156041d50146405665404c1012940140d030041c52101d82c80780d035961187d6000c080c0f0070410042140903000640c0c0120741040d03104080794005104840229020010703030100180080103c44a005000f400c1c1c0c000310f402d00f1141580d105c0c84141082c18590355480c10644440707621100c0030b91400d00215550340707605518011510034401740179240141c4050006201e69400800c1e0264010564080f803034941041748a8070340014401c0360060912464403502c1700506a1220000f4141c4035032034028402141c0d10418030540002621000d00a03642901c1c091003c441c41c0d4204402c00301051048030309220840c80070440764414280c5840210f00c08007010846 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 556120107 1250 556118857 556118867
    0x3050706140f1b0414270f0c040b03040611130b0d11030105100804030c0b01080303040b06010813020910030803090703060606030203040c0618090f0c030b1e010813061b 74
    0x8043c100e003244203c10120601040c0c06030041c0d0040d10740541c01086100402e842c2d41c0507500b042c00f003200324509810540c10400000c510300707039118142d0b11024400074642c5000031046500321401110340620b150f48070386405000b4010300c481d52610030810441e001002982e00c407a04050804407503000e582e40705902680c0121001041d00d1908440248010000d84c1e46503003403505085150300745100c444e6164901100d04540c03c010041a00d44040c002081c4450000042c5100303d00c0790f40c031100180c886400564820008032087d044e809808084000103080000d54036410000c1c025149415540300d5454807181e4100b01c0c0c0c1d0840545c01180c0400620156000e000010b21090900718a14249a2604554078605005d00014440d0301d0700211005038442c5d210340300810001c0c008000e01201810b086000d070610364001800207050020b102e0403464002c070501c8110546100c046056a1007100540b05075000400442c0c154111a0b41c010114600740100c401203013628100001c15800d034900500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 556121357 1250 556120107 556120111
    0x71214010f0e0321060a0302060c0a061b0e04150b21010306021c020304020d29070806040c0e130b06130306020901200a080c0c0303070507050a0b0a090b030403050706140f 75
    0xc1c0e10070840c040c85420303104c2c6d0b461706042e2501503079000d070f40b440c2d11803440d03203040d50b00b0f90001e103c185032211410b46c82c100c2210700000401146d481d0029850540200020764a035602c021000c0540a24108240400d040c0100b01c0b0031013296001c8400c1c824815540000002603000b500e0342a00011a007441036101400d401c090b1000003011400d40c1840e4012032801002444020000100b0720740703103d41c2d0400005110080ca00f0305000c80103600e03208030004c00303022003900c0c024060350800d1100741142d07010781c9509040301030242403c1511605000c0c00e5020b404510b030380e82e400c07403020050074554551502c161130185010303030000b40c1d032055008001030032400325035442400e800e286610032500000101d488504036410225158031060060b803041d007400c03100a19554981b00000d4204104840420040c1c02c50744100c1c0c8410609607140e02c048094402c0202440001e80042030a00480034032a003d0340d0014064138006051020f03a50301d210445680c9060003100c0c1c20450300b0071501da4114110070b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 556122607 1250 556121357 556121407
    0x301060e09071a09040c030603020613261203150607050f070b0f0a033206030d02010b0603160909050a0b15090102030d020319022a071214010f0e03 65
    0x18403c2001c1080303500e0301582101911480c1c60301d01d0310390764511940120000d0350f00240820380c0d441038410302d07a42c0c1c3c01603841011360b455070700404800c0c00c02e0800300c0106619900c3c0b001d41403854a0071040901c90340010030042e00300b44030710f03001100c070f445080140c02101d11400c000d09050b080758083c0ca140c07110503482030400c02800c00088101c242d90b00d0980702450541e040110b41c81c0e0100c0c0415108511130740c290b91a140140c4404403032445120312042c0225020340c00d4456402d04180201c0c217940102030b940360002c00400104030760350b012134440e200d0196903203018500d043d150200301c0150384095a00074010340d218140c0540b6480c00d0440c4000c80101c98008a00d0b1000400010f0740300d01801c2640144658082b0010b2480045000d099070b106040000842d6908600c0400a890480482c0813508041200007407804580000801030243d42002105c02c00c000010b035540d80d040700800c0d00500d115500c3d08100084c0210343c4c001c0014403842c28001d191510b000008810b60329588000034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 556123857 1250 556122607 556122629
    0x70b060d030f121409010209011202040303200f030f0d0e0a0c0902130b0d02040f060e060d020721091401020619090318090203040b09030a14090a050301060e0907 71
    0x3140000d402400600c0c2c00c032034504100c0b0842c9450729010f8002e04c10b130741d28058010701400402c14002c4040d4010818024262600b40902802c0d0211700128055400014041004d0301002088140c0d200d900c1020b0000c21400c48282c3e4401150240c1160048001d081d81c103079001c501125a1041805910499902134000341484e000c03545071926401070a104640746540c1c0001c1600e440901254100f001d815070b141d016603609003240d1818000d40c4140700740c0304441d4010601080d00b5100302c49207441c111000b40340500f451015a000b400035480323030004540083d035052019403464002489220703501c00035101e0701c041c03d142c68403c000c000d09000034541190004010401409240c1003e035204002e500c600250000d01c0d860107a442c0807130f04c1400d660640c5001d00c00262080c0540003188118482c4030700ca18142c40344600c040e81e80c0074120200340400c85041c81c0c00c0e0080303a400003502140800402c0302800da9941c01c003081c212403070354001002c00c0c42190700b0006580001c0150b94010104d4400c9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 556125107 1250 556123857 556123879
    0x20a0e0a1514310207120e1e030f0303040f031427060417010b030106122a030f05061b09030d0e040f090507030506060109030302120a03021b0606030d020c010f05070203010f090305070b06 82
    0xb83e52340401606410082034140f51101c840c2c40820003405141c40000880b503890403d1b0800c0c00c1e074060019001c03000103c0704910014903407080801e954440c02050007080d40707584280c4c051094540e609040a4115800b0300001034001004030754568906071800000603903413a824181400d403011a0032031030701403001c0001113000411860741c80d03040d4244070700701020140070500000094601d81d40090f0402c403d0001e10306c20301a0109541c1c1c0540f46080724070f032281300c190004003418041c10040c550300da0802810801c0c1c0c1405060304a4001400801c001000400c0c0360651044451208068950b584078800500400000b0400d254000c102402c0c001881455582c000b941c0e003010300f00c148841000403544050700d03030003901650004032880524240500c40717240c100c0e581d060103c0d0018030912403c1c140401c02400030621a60134001a51000c0407010100010356042c0d00610b41240c0640d41c40d0342a85d40350200d03104902c2c41512903942c540d40e41c0b03e40e082c81e8150210182c03080f840381da5802d01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 556126357 1250 556125107 556125109
    0xc0314060a031b15050a02010e15010306050907091d01061d06060a1119111203160302070803071b140f0d0f020a0e0a1514310207120e 59
    0x1e030120382e80014110018246942500020b41140d444540200500b00c400e40c41c840d00400600b8002000303a0080100d080344075130f25a601c8030704c28004800d8004c80001400810140c0c1c00c0750f903112003030380c0031200c2c901e0f50390821100b16600d10300b9214440300c442d00200074880c02801090000c194031a2583d0340c0e803011100c0c060750b1341d5015010380d1051000080250516000301119202d40740202c05568032611604070340e02c0749241c0e5000844044c49180c0044a25152030840e14900d0380f408070003103003452110101d046404150440c103400b1b502c1510000150080200010302d1030a100320340c0424426004041c0c181030000030b0300072084156101110f40c2c1a603c406040c42c406000c119402511007035141042c402d07402901c40d001c0d41042203204c02082c41030604803114010140b038030080007107038048404107004010500981c42d60541e0a5070386501c0380741001e800da00c04545d42600a203c01030310040d09040345014840100070b560040ba00405002d130718000c00399502d000d070920343c400002c944 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 556127607 1250 556126357 556126369
    0x52512110705030c0319050a3518090c040503030c0f070b0c15070905090a0e0c01090509060d06020f130303020d05040e0714040f0308030a0f0605060708180d060c031406 74
    0x68403042000c0d881d403540c020701030100100e561154018440c08890a20600601c90000103400448407000444854002c41030340c00044a45002b454146900304400c0c810400c020a4009403945100c05c20510000c1002ea81c1440203224100071031004051010100c42d010b401c0080ea40d200050200061003e00030701100440c0d94107d1038a09000000e01341d56006080d6280c442642025130000c0f00c1100b04904203a055000c0b02400c0701c80e004890450105000440300320906004454010b0b01c418089170090030251120507005105644c0581042c0d1300c6241812203802a00350060b803843d0130403080080c56010f000c00e450340191451319903c2c0a05000907000b00c082d01401410401103003980f80c01c0c0a64150040d60003409540c00c0503824180d407810190b0700b0790010b84404403210310b011030000f1155128403e04c2c00300c682c041c00d154100562900c6120f40303500005c8224002c48080728008400303a540000c0c08115610408000404440607140103007210003500480c19104100c0d018409950390315 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 556128857 1250 556127607 556127623
    0x1707031212021902030d05011e03061d030309070f0e1b0703110118030e040911011412160f1404140d0807030c14030a052512110705030c03 61
    0x2420075200341050040300700001e21490384020864040c1000301400541d010000b042c40c4620a1028000c903600d82c1c125171241c411038103015a18070404101040020416041109030710301e85c1023241c201c0340320020304c2401d59008680d0440c554001c41e6090000300c05d205050406009082d03c1c030640b0789454080c40c07050940480c100845030101050b50b00415104802001103290144000d0080410340d18004020384030040d07045011918403400c402541c105482151401034125441448204000d4015100c80341c08041800d0204820058a11340404001080e40070700302d008072a500c81c4441d101c00801c0e9400400010b001c00c22440a0320501c01008010f5a05031401170400031280f2030040e001a0242c42000e2000f0403030b8402081410030300d90415800c241540c0142010108210200c00c016201d210381055007010903c01e121010316445c0c00c00c608402c0c0195502100f0303041c141030311100c0001d02c10350a4400002e0042503110300d008400e111401c010001036004001c00c40e249d000003a00c0713004c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 556130107 1250 556128857 556128893
    0x405070b1611061b010605010e191203090e0907061b030c030f03091704290d050621010b040c0e030a0615240212162415170703 56
    0x2c20340c0e00400d01e030355040031900385911550364400b1608140722480d02902c0c141c030946011496202c190540d074242a0465117024000062100c240c5040845801c0340a4503460107400700006242d000c5100c401c0106a10b00610301540140a00f528180006009200e908800c1113142900d00c035420000b0740060201c4102541800c00c800074480b405001c1300201030098001d0071100c6058680c1d4103212407417009000740c5143e0303452111004541094100343c01c0081c00c00c1c2201c55420440c20607144080e90006800a90050190046c01aa8290120200d04102d9079403907995444085450b42d26140c4a0f0645100041c2042401a0414000a41c94010180780540a0b40e00c801e445401003503004054005010340040e410702c10b1071907500035079552074054441005849007981085010751040c0540340300f24882e021000c03c94000d50703213507414041a1070710105484841d4620b8102c0d240c007401046281068501d950700803501e04500d408060958000211140d00301000a0011800350fa002000b41e02c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 556131357 1250 556130107 556130123
    0x503030706110c0a1103060109050903180d06050915061c030c06150b0c06100e0705091f050705010f060503250510030e011b02030406030e030d0608060405070b16 71
    0x40340b8030a4100e14440e000340da031071034014040c1c0c0c80c0410001e0060b00121300401d0b01180c06aa8980c5164000c4400c1900c10460030381c800d00151244080f408080c107005140034250390f00740d68040d07582c581503d4056440450540210581d14201230750582c0095210302c08644290365003420249008445c41400000390401c8006403000003407015540041122200788082c01090665030644011290011000030034140201c101080110303040f1800501681c42d00c00718030f609074407035400603920780d8844003699401205200d605852003918500441032034000e510f4240c1e4840940c83c2c01e600f124140242194904d182c14002d10880c0c40003d01003555601882c94900c03410603980000c8138120351688034640c8902c004014074025680358000380b1800e8211002401703c40e8100400560f11100550f0003070040c0c2c0184010480940300e42c0080c1c072803043c8001076030b2600c4010442401650b00540100c0c040703601007024002001401c00c1250010301c4003080c403a003001c0c500c16001300030f01c914490141c6407074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 556132607 1250 556131357 556131371
    0x8070611011b14160206040306020705060f24011106100501030e070807121a0103080703090e070c06020322080403051603170304080c0607030c020115050105031b0702150403110a0503030706 83
    0xc0c0c18403e05041303854000344103545840c1d03607182510103507105030300c00ca503107014000c0400c14004401600130700401c5c20f04071a10103035400040403002d004211200c103040007c80c1c606c0e00807805092000354042c030046802a0092170a200003d400e0340d10040001d4056403044500304081c11010510707500780c800700000c45041086a0603c03403003082c1d8807140a10710140c150000800c0010030002840d01d14444d1311812000d07a520300544000d07410403252000440c0da4105a40006409507004545c0100b044003040c10140840c84400d004078100502150059000502401032101c10480801c2008a003c4884451415551a42c595081e40e14407402c1421020010604001081c01030759007071118442210344a00e80440002c0103459a0030011026501e0805003003410080da4856109865040c2c48592641e03d510f21380f0a106818510045140003081c01510011395a4240040381c031074480f100030340c4403030850400c1529028815500d030321481d0712031340c1008692404400c1c0c0d074590750010030001d140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 556133857 1250 556132607 556132627
    0x21306261326041a0408150c0c0a05061009020c0a080a0e1017060901140d060b091f050916080712020d02040311150318030408070611011b14 62
    0x504181400b00803646550810000014001006842201d006038159594030582c01c11041e8540718078000c0303103126000803184110071010b030070480d600030729000055803030050000116424448896411503280d00500240810440411020005004a004210300d0600c603807400a0f03035001d01e20710080810b403000c00d4225101c0d0080b2428141c80502408955404c1600400107007451a1408000020881c407800300300d0310305000c407003d816249500c551304241002202004803600352807900f00c0b0119210b1640c80510f4580c200307040d0151102c550f44900040104a81280c600e000307400c04d0303005107c01001c012008241e4604038111100b81e0506a00703e03200c140081300e00c200ca203100ca0385000c0c0005140c6405e002254001c2048902584281d002004404108800681c07031103510001828244042400601002020307482000c000040740c1c5015942e120142c204962540043c0104000301010a080403080c010310700c1e1300069881da03a905207044040517281c01e43d5045040c40e00c2001190400c1a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 556135107 1250 556133857 556133873
    0x3115119060b03040501290f0301060906060305060a06111e1e07080c061804020a050706091505180a030f03060321031103010e060d060b040213062613 66
    0x8900a00c41841880e8444080d440140d00603035007102c1d607610f01114030304100001d0f138404105076401d400704a501c03500042003003004402180640e40c195030b103010006005000c0d00c50180141401c0c1c40100d490b2401404000882445a0000782030150910200410400114134960402c0742c100e03110501c0e100b1021034500d00000c644070035500c19410382540054a9001401c002118030800031150042640000d20500340284020041c44019900200f007252500c0d0700a00f1940e410b62900506125007a22200251a410303002940c001420310761104000007140901a88403040030028242d20041084582d0b03100c0c0d982c00301400300075419402c1031049204e500320000443d000f1301d4200c1c21058242c122000300b000075004002292400401c2054582c2000c01c0c0c1c0c1c121000c04041050b5607031824107019030721440c42d0040b9880b540c1d44000d001142d83d03501c050700c4080c0b2100c0c0207041c094106100600002c4804400303003000da4884440786c0c0c6091000030b82ca9440144c500c91103107d05902e140141c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 556136357 1250 556135107 556135141
    0x7081605071407030c080d050d021b0601090b030d030203010302012708031b061f06030506040902060403050a05060c03151212040b0d0c030c050403030309031151 71
    0xb001c100c1002010302d41d52000151802600d01408110310319541c2d03284001d59410a61380d4900204000b849241c01c1c0820503809051155200c1068840c1c090142540600340b410036000000550799450403d0304506040190401105007418114550350440d000684407681420810721998010046844440204403070301c4024a12182141c0e2107103140003901090f41c8103c1c00001301803140200003400701004101484903e034a150700090480c0c1008812405000700800003600300d51162038a0b0b00507240c0c030001304000c50003100501144500e500d4442c0c2000b0000e404140203803803e200b0702c0062130b014020204007034000c88035000381c00e180c03403c8035040c40c103008039100580001081c00651441c0c2c52004001c000c101140400508001e01020307011140f85111410008505200620001740203a00620750f05000f400e00c64888440c030002030f46041e0b40e054000c1600d02c0803012064554020141030920100c60201603280796200021b555860b400c1d1011b40b40e2035400074804030304401e10030502d0b08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 556137607 1250 556136357 556136363
    0xa0e0a11030c1c200d060503030a05041e05091303020c0607111507200f0307080d03061d0403030902060f1908180d0f030b270f0708160507 61
    0x986902d44030007914041d030800c000000002000c01450580420244101801c1484c6080031080e1204440325503d000c0c5c00c049810080c44c3d035a41c0000c84c2641c1e041014002d5044255185c07a076840c01c0070100342e00000d0107142040c1c0016414401e2081e6902c0102c6680d0002d0184e0300b1201202190030101c0c039120492040542080c8002421801e0180301504d4100b07110003590006403003c00c2e6542005984560f03c005007100007040900b0381c41d411026260303e4014401000340e07600191400010781800d62540c4a810181c0c07000a6858a043c0c050041c44000c080d05411016040c000340e070101049100140020101030f038403ca180115650082920500c000300c040c815150400340a601c1e05020312060b081e008110301c0380000300540e00301e20083c0200e510f10000303411161111031054403410460007414003410f80390301020000d03031030b0102c800000d02550b0560001e114040c6403e29a207a102610200b51500800308102d02c04d5041100250803501990015103100c4040104030f402d8010000c0023 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 556138857 1250 556137607 556137641
    0x20607031e2a020d0206070c171308121303060b0d1b050f09040201050706050c0409021309270f0201050d0c03020306042711030f01050708240a0e0a 65
    0x35002c07202000d8012040c0c51125421804940b6015005a80c3d400500001c40700581c0520000742e2401c2c0704868002d03d480c4a02c203642c01d48a020303c00124a904000d035048500c0d2540d0b1000c010700701c4100300002600303918002d440e00d0060501319000c28080071303000107400c1d41e032034024802035510341c01102c40503a40c0100502c600381c648048040c119200a108091145405404801583c0b40000e041801780381d050f103d07580f49c040c680c3d8030540601002446806a85024040050f880849000600e50140c0c0c04407101c03002e5007030400000c01c5500f103070316405128200300040c105001e0302c02003800766650081c482c10000e1589100407a894814400071104031403d0010340226603030560091809080d04803000d200d0308200a031032510955600348200c1101300d61031410302c041100e00c2c8011512000103030079100c0054086088509542007658100d0010b68008200800885400711000740c0409490340141040d0000380020928a620300908070408129004242003980c0e03035100e0144804c03c0500d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 556140107 1250 556138857 556138871
    0x1305040501081006090b0d060905070b181503060a061101110d02180f030c010c06180b01030201140406020c120102070f05011a0402040f03080a02031b060a0c030507020607031e 77
    0x3a83e89600103c500c090b0040c2c202500410040f480303010b41c459101007e461740d4500c5504d5203030000074000c4004256400c0c0240d230710204e01c0a403404010b00100c04031540c180c0c0113980440c28056402c100d10500c588a2074148140032095a070700400000b103e5407890f040da2110b144001040c01001c9074807824050540015003040d00e1940781e0042c25032400c103040003c5802054100b40450301e02c0303800007103a05400034034034a82c4640c06000d550920a00501001540203441054150303802e03004c403401e07208107139101c00400440d0b91145280031859207441480b800c251604102035500d003000d48200e0b104140c1c1c10030100b40c81d0750940c11341701c001d50090081d40546001d030a115008005c140d0014095080080041d502c0341803a0080f83c04440d10105441402855511000c01c070342c00111070481140002c02004006016a60505500849440285c4014188090803400311240d1910f4082030500b080100b00010303401280d180d901504500b40440d0700900220980d012004003808050b050341341600c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 556141357 1250 556140107 556140119
    0x21903060c0906030b0a03080d06030b0a05040c05030a03050406140910120f09030c1b0e0114090f2802130909061802030a030c08160b070807110d051305040501 70
    0x1000a009089031902c82d03000362565802c0701a105002d40c05900034104030010070024000000070110f4000100f0005405030312655481044c05040e5400100c10751182c013401b0130300c5000310101000740400c40090182000c2c42e83c018012780214402d8009015030302404401c0010741400311207414200a01102ca54a01d1002c041c1001d000081303068039480c82c00c0c0d81c04c655105113100b020290b940689981300c4451140e607a8050a862802c4404020303000b00000056484940314514042d04404541e244080c610f601400140c8000802d450400900344041c010018105c1d5011200c66010281c903c01c0c1090161503030001e40f00340c96101075151600a000a212806980000c3c0d60510810040c42400d9402c80346180c20101144082d5240e08100c1100000070701806060307481921035200941804c0c4030100284011601c0503041d9000b15010040001182e402040964086000e042c0004011801484030b41e40301280c0c0411400e0210000390f509082120101c0e03140240b400500a104a45e1145 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 556142607 1250 556141357 556141361
    0x50f0f0907050d141204230a15230f030c03040f021207030b010b040803030106080a1e050103030e0306070f0c1511040518090615120d05040f1706040f02190306 70
    0x28102c4020b40585d400c00100720800d00b0440e002c0340c01c1e030008540c0180366403000e040d850f40c1c441d07840350b408403000c0d03400200c0804505046030402d01c2034030f0b007a5200c1c4003000b1051100800410b5031201c01d80801070206040d400e001660b400008201d201600c070b0b40c0343d10304081000c2601d0400b0754480001c0001840f05540001c0e0402640e01c140740542d036030390b65440b4103401800342d4040d02d00715400910040c400381344078120003079008130079041c0440c450413504e000c8000b01c0ca14009400c4456207940040c0181a0422040d02ca400d02c1500207203a2854140c1c8010000340181804104128607a8000800d00c44d40185503018059014402c12081c2e2074911084200e602911529024106043c0380d1601b01d01181c0366544181a1b080240446076038185c0c1d081c210030303290f0f040c00d603105c022890b0b110207200c1e040000d0544841c2d1a1505079545050100940d00e58650380d10a60191402c444081c074000d601140c1c10350040c1c0d0004005d84070103143d1001480850013821074040f0001c403180000207005e016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 556143857 1250 556142607 556142633
    0x16020604020a0e150411180f240f0706020d111329031e0906040b13240606140f090d020a0e07020a060606090e1b130311030709050f0f0907050d 63
    0x251f144c1c664074152074801d010800c1e001011003540115068001521010400301810410f800f465000d80f908800f0104002c094200440070f0350342d05d0380400d04010b090300610465400316540c0310b00320306049881c27407100745202c014040c241c040c01d440c00f40450080c1d43d551100c0b224144401c101612480d007900d0220528517044000a18140c2641c0402c0c44140301181560003540c01008940d480d80d110701c5140d0100301600c2d001c41e50b048141d540a80c0078490b4048090501001d9000880c111340303004402011030400041d91003039a54200152920760111100b111540740701525000c1c0c94110764000280700ba1342503400221100004000c2041d0a130340810341445542c480c0340100708064540308102ca5402da05c2c095041c00c0d4032980045860100d8031400c820030051824541da10300903040c0c01048400641c0e0340200c030040c81c4880c5d06180c52400380700c010007400c03c0503800c0007540742455004005800141c80603403280b4100e0081b4807602d006002c2c5d503020300b04c0074041d000001c03007034138105c1840355103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 556145107 1250 556143857 556143877
    0x5071106181207111512070503060f040612030909060b09130204050406080304090e01050601080703022d13080111070210021011030114101202090f0a060816020604020a0e150411 78
    0x12200000c1002ea19000c191070300104151b00445080e40c828105440d140d1003c0c0145500c0214550b0881072661a400b03090050001000408840030300d901e0701406a10994102c4120207060500c00d116580f5420150707038140404951403c4146020f042240091046400140d0081d0170302c072001c80e0160000004008a590301c1d0b03030030095428490092404c0f24002e41d0851f0005190303d0104844034402c0c2c02038007030034010180800034025088070b0100403004440b50002020000304401c1c060603403803401d1030300034406000203000310041e500e8400b982c1e2040100084c816440c141d400090030380300700304410f9541304030729082060011249900c1c0c8980c00034800c5c510700b0412820b41060b81d00341300e540034400212a4642c0109201d91001000c0a504814007507034011850100c090b0607541c8058407600101203c0c0c0720b01e0706900348204607e000c1d18004401a0030355211805100050300c0b80c8016208031a50304172094425101c042030003001d43c112030302c011b50107802c0c62502002c881d100c900804403000c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 556146357 1250 556145107 556145119
    0x5010b0310060308090105090f0a03060f1107050a03050f0d0c230c0709020904090b0c070201180b03010306021b061512120301140103061a030a0507110618120711 71
    0x294212805660b41c50100411050080c8048070761035000c2c41c041c10002e10f0050101e240c0500003004580c035141075600c20f17900d06498503000741031112188202c500c68003031102100c2c0303001402e8441d5946c8003c0d01900900b0000b00044d104079412400064500311840818144800186c50000a00c103580c80380070248a803074400780d003003912032442e0120b80340704060780040c080341450804000006e410222001c0c3c1c0094403100013100040381000454420380b4002c198544400050000501761603241c40948001001c0703d409000201b0344c14180e81c1100d41c004000769903030f8114142060070180401110706075108030024040500d0950050341c2c0d451000340d6006100704800c200a565540170a1a2141c3e1407000f040140080c600341070000c581000e040c140460b003a0343d542068644003802c0d683d60f45030300c0e901005200d450307104da0203000d4005070146401404103441c032003815100c440c0a00000410200c10302d1107450300c0c02c18000c01c1000c0a003441040d440e00c0b090f0405000c5001c4480c40c5600c50b43d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 556147607 1250 556146357 556146373
    0x91306030507050409110f01021c020a170f0f07050717030c0111040b07170f120f010806071e090b030709061205041205031902070c080606030a121407050a05010b03 72
    0x20905102d981c3ca400c1d0403100070000e8000e030109000d41f0300c0c90000d6890450007843e4160705035184251010040701a60340c0102500e4000303042821250700000444400000b08120483c1181000819508040c03810051295540d0140c680541f6048445c1d22480c012201511664848000032014152403601e09000381b120104c2440282250707c030324001e099108105000c1c0742d0108103a0b07850014030102d0b00101c10300c1c0c407004030300c40281908001005a2001d40f03410410018805a0701024014150407004002d6818114806032580e010850911501c000106c040120356105080c0c0714020203480c0b10841d07407420408001081141d02d4041c1202190344090448a09440c5118643c80b0f6900b02c8032413458042c2c034140c00c84850380302800031074550080d0350501000c0040362000b00040d610030b0f400c28280070f20b4480c040341030850080c18184241c200328400710115400c840e6440384002903141c01c401d87e00c0f454405078414000c200300a0b126205030461300c8104a01580b00802e003040071402c4901300c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 556148857 1250 556147607 556147609
    0x71803151409070b0901170c03010f081203150d020a0303030f140103020d06020723010c09150e040f06030f0807021c080d0c200105100b2a0309130603050705 69
    0x1036800b980c5542c015840b00104000100e0000c000e045d4941c0145020040c001e0305070007005409a00fa1041350b90544008010082c605540c810b090040c0844009810440860700c0f003a0303800d010040950030340c80401804009503695020102c10103613030003403005c2200c0c0e80300e0a004004021004c0c203117810601d4202150006440390070300e40e04a0361f004013180710700b84c000d6882d18040e4100308001c8400d17a21407514019514180481d050901198000019060744e80d280c0003005e901066104440400356003076026003055008506400c0b025051b00c0110b00289070f5014440148120703031005d400071802103803d108000e0030740c1c01400c406d402115403203290317102000016400c1c0022480240710050403c4420900e230016000040d5000d0703070f800e1003079034a00d44460008012482c0a042509039640703078104040240115150006410884003541c00d03c842114805c000c5000590b401c0040e001c0c031030180c3c040c000208104c4640038005022641c1041400d1040009000580002c03169400340507000b082d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 556150107 1250 556148857 556148891
    0xc0b06030a05070302040e03160308060102072103032021181e0a0c06050c010c03050903090409020604090204030515072c0135160804080307180315 65
    0x740c182c1240140c0308840c0f566003004002e1a402c001d83c452404240300d15841c001c00c184114210324001d03258402c0f03519003600024248030084d000803001c0b220910101e01c1c28284d96550f524003039418100040c040b204200002190030044203004180c840029440a207a80818000d090340e6107030013200e01c01521042445040d03102d09131410402c84e8442c0000b16105080d541c0540702c045143d03c19070380c103001c0d00e441311482494607400203004204001104001e8032001d200c0e4001205407483c0802c640d003030080c607594a0344100c4824520943e1540c51141c00d554500d021140244109041107548540d00d24010f43c554400c0212040f24050450000301400e02071004120780c403250020a18007508d440c0352820445800340c2180e4100aa00041c800388240140e05a003505041c0000c149443e82a0300f40d1510812801090b100803041610324003401160428a8035030041c0d0312510403a240d039203001c000c48003024010344200c00e1380029440041803141001079800c007600e403101c0034001076242441d5591 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 556151357 1250 556150107 556150123
    0x7320c0115093806030720070305030306010f0e030615010906030b0904020405040302030d05070207050a05060c030301141c2d05120309102c06010b0406030f06150c0b0603 75
    0x11450160f4514809481840710003100e403040d400072805190511502180490300112091303400310f0000281c40c405500c588144c900c10646c210020f1041505542d10b030b076124000034202c181440f0761038081c0c42e2840d024a0300c07998090005011a40a840e00c005640701e8160411390303941c0410703181100491800e10a000c2e201c2802030103000d02255850726400d00009060090044e01140004c5c00340d15450300c3c15000d014040e2000e6030040c0011070034a0200445409582c3c003403807064404119005402c1c0c00401602d044404411003150b400d003480c0d01065001003410951450b080c040c000c02c070300300441441c00141d8090003420014089890b900c0d5110040e1404801a00a50100c1c92a282240c2e004d001103510004d01d0b01652409582c054801e4180e40105a501200c100e55528a42c03100588502200260104000600c2154900500c180d0302d0311990042004040e03d4611050f003601660b006903004080c640c104031b81020618000030003149542c2c004842900c400008154240740018400e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 556152607 1250 556151357 556151381
    0x50d1515110303011a0c010f050f07050405010210050703061a03090613020105120a150305010b0f0603040c03060b0a030b160f020c0646020d0807320c011509 69
    0x43c5140d00b031860b07583c46030841a40c542e007502030410141682d03010a0003204c5540c01d1407a07002ca0302e070400100b40d4086990003400201000340c03e01c010001c580e40081e00c42d40c0001c00c400009102e488000c003c0300a0003003a0001b00303007176116032500c00310f4144200c01140b142d40750740d041e190551944128414200355800010f400141d05008102c1d09045940c402070300081480070000d50148441440501c1e507517103038001e44903655589401061800c03d8807140d071014004440e00751440c90300d0f40d540c8801910a000203003105a46410362115611000001000745801c4000c41143e840c3c60841c6140c50401d01000d5000a2180c0f0198612140006a542c0100400034a400e090000b4a100d803c8000f0b9010304100044488000e001900b008800140c1024141c21165400528510302d01910b446000c0c2000810016a01c0401c041c55901803030b25005118201a00c000c202c01c1c106c9085000105400b80d41e002c1c40c000580001d0403641544025451192600d0302d08400382c1c2c03905403c045a40d10341c03142c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 556153857 1250 556152607 556152613
    0x317070c03030515101107050904020a0e07020307050a0f060e0a03140c0a12030501050a06051206010f0c020910080f160e06060403060e0706030f1e0b01050d151511 72
    0x118000038001d401c802c0c0d1240d8484a0134004e100d00d0300c001584142854260380c04900611240d000b8000c060080c81c002e0002500c0f190240e04003a80816201d6030700c0d100c4e0006d810420804500024824000c980a15402000329108110319080c425007051000500f120031518101421a0824021448425480d015220b0a0b0541d60304143c00c0455480701c86d52140c18010700c510a000607041c0c4003a01c0084405540004080d81000c05200040c10584c02120a03c901440650030180024404660040c0b007843e14002d0b0214040c1c065580b6203d40c50300a5101c00220b00700110504101500c03011202070340d0449000c601400c41d2035449200040d02003203a0300c08048280032a121210001d0380140f4040c1035149016542e407946c01c11100c02c7c0030000401d411060042014030340c10300812540d251844410031045622450300c084e01c01c0c0c10f14000750266140c001c0c00c13911745c1c0604141c1d550001807030018031a02000c1e12000f0fa0309002405885108074580f107400402520560010130036002e41001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 556155107 1250 556153857 556153877
    0x31017060a050a060302030f0604060b0d0f06020d0902040509010f0506011b1e08071a0c0f09130f09050c0405070302031e0a06030c080109140606010c0305030606040f12031707 77
    0x101c0014000060403004801c0e12204000010380342040a903a244050801420050038140780c511309403503287c1070300741c1721716612600b01c404078030010290b007a007541c04500166208105010000a460032410203907100d4600810480455019084400209040d100401155072000c005540c0d01c50448941c1300302c120400034010014070004000980055000603c01d20340110355103a803c0340e03020b08000c480160016004c42c410b140544400d6422006a80a0390305119403544040b09034043d04c3d20840c03081b401405035001404441d48001485905d07039a06000c02e8402e82801c60b0b40f100c50240c0702d030107140380c000041d400c0c5100e4400e89010b8010064520780c0b0a0f1541c12070744120b040600600c3c0a40c7d500d14000001420110005000707204117800810b000b001c030306220103461a01405512542c21050400c421a03921004000005038036007002030300c0762911030115010f80580d0b00a0082115a05c4010030404100c1c1e40710024540319036550240000d076420191140101a610400400c1c50584 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 556156357 1250 556155107 556155121
    0x50406090e06030a0602210627190c0e030c04090b1317040f06120c080622050a0209150403030909091a270c09010b071e0803101706 58
    0x81c1c181e00410000c2c01c8403003007911600da140c00c070b034001f10b4441b00e0486074682c0c038100e0a0410a02d1903001e28122401180c860062401c64000014200090440c9501500181900c4a45004031810500c49030040007014001b00024084402d441c5c0c40390310030320a2342c8180380185420700a0300c003501e0303000502c144d440c2c44412007950120542403044a0548500060b00c11054041000d00000c14071014540c0c1c08902d449006015080e1021400900a0914288000058018614a4106c2402d41c3c0c1400303c50100e8485200104526845404590412017070010480c000e030080d00c1254070444045040391804000020301d44a640b100502298480008000c040c805500016006029440e002c00300e8049a0301201c580408842c1003400a04445d03000786140300e0905001c4594441c2e400401c41c009001000404621051050076410100019414204a042e0040c0c240d000d15140c062001c0700b5562070520070f580c104413002c0c8803003238500c100090107405102c0c558510b0711206c005000d10b911060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 556157607 1250 556156357 556156379
    0x9060702010c170304140c1809160906050102010b1002071401031e09050c0301060e16110d110c06160f050304050315060306090c090c071e03020a03030c05040609 71
    0x2069041c00a040d424501060108040305405907010301190b90303915140c40e0204104101c1c0300075100c1c5500c0310140014548600d40d454014403c05028a40f0550b51603e1b0319203800c0e40d040085800e44801c26000404c400780d07410040a0342c00c240c0003404445001000d0210039400c0244c01e40c010b82c03200340d00300800f00400030b60002146c0c0c107150204140440d00300603403851143c440d2460700c80361760302000307010720505120020724034104600030f1100d42d00c1c049019440100103400800c50600b0034400b01c1c0e01502801c0000000c80164041e00d50032440046e01424845c440807010300e0303501519100700c0107031904c4421620410350f1181090b0800d2910b1701c40a881a001940c101c4080c4010400440e507640d0030000d8402c4a2070040306030b60300e0301d028400c0c503041810207800d0b81c4583e032000031008a25510b48415a81c00000403081545075006400e20b40342040030000381341d14400da011809400d055000c114441d44900940701805103410108080350795215030703c9810000788501800784060100340d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 556158857 1250 556157607 556157617
    0x21818070f2003090f01031803050904020d050405160e31020301050a1a090108060112113015060402130308030703091412191b0b09070504110906 64
    0x42d2611050480c1c0d00207014109a010311065541580040f030b8502d4103181032403604c0c01001c002e18050013400710000300341041012017900101408008181c42c0b40320344490307064494100e1090028456800c103424850340f00d900701c9d968075844070800040415907064040d444e90040c580b10003034107007050040040c04d480d000e908070300d5410092140c85450140e036090140c50b001c2d2007401070004132141c8180d900050076201c680d5083c010310310300c00100013640d004503010341124617481d030a121003801e620380382c0744802c050003200e50b00103200c11a0003007614105804d40344800200d2030140790181c50b0111196200c1a00780602d00d600404000142a41441d07006403500c003151455603006552603130303194241504201c4004d80029902c410610a000c1d05241e444010807001d00035204068096100080622591101012403038100c511401c40d00e2164003011240110282c0d20181090b192400c1480b9041c161740a90041c8101c0d8004a060300e000d1044180588c006070080d464a9442003e002c2c041e000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 556160107 1250 556158857 556158887
    0x10e15010504063e2503030e0109080303040303020403021e090402060c0a06020c03090a0b07080306010c11090a05060103060807240e0604030303020c01060902030f1302041b0302181807 81
    0x134415031484e0300d40d16890300300c1e03400b00002e00c2e0241c6021482c007445c1c0203180198500c0400c1c99882c0d40c07001e0030f5180380364059a4151a000344a41080001660545a00d9108020602c800001c0100741640351740a40300b500d108440d00018415844104c025110b50b60168590042c6100b01040041c9010300003404c0d00200300f81991601007154585400b00d81000610140c1c540001480014034549a5016800340c584202101d0a0007029100c00680d404010b01084c18003511059031010701c00d07410000e5200b0345000340000c03141c2c03400e0b1000c3c4020b028142d130440d0119080000103d4010800315000054850010b02400e500c41840d101c00c031501c440350044424000300030014101c80c0c40e09070081015601903240565581c1800460f142100e01340e50141d844184140144140d402e00e0b64003154208422640c0403070905014000107006005840c107808ac4a0360029004a142d60150007404140300d69620040742070100801f413151403c1018122003601d07084400040c041070041c803515800b403603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 556161357 1250 556160107 556160147
    0x30c0d0e0c0a0f140103050906010603050702030405060301030f031e0203070b1518011707050904080903150106120b0904030e011803020303040303030f0c020a03021c0c0609060203010e1501050406 86
    0x1c42001040c0d848070300e600401071914072140c00b032081c100c142100041c0d090003840c003081035241c945c2c40603480d4103040c020801010340302c40104044074401c1041d14040c1038010041c950301d5a40e81303441880840c6d040d00441c04900d0300c1d0380340d540140c01025440036000294019514040841c2e4548010f040e00402c05407800b0005a03000e130a689410b51205d0741107514001d01102035041c04801200e001c900c2909403140d602803602803165481d40c194940e00980d00c443c0302900c0760094000079040035a00705c40071161a004900018025900c100202e0f031403a081002000000f04070028845882c00c00c84010700441d02c04070b0f4640682d4441c5449618004540710819002516a0b00181c2160b0050b801900069212030200f0000f51031407180294005490004050115480d90041c1d00d4002081548039150820341300c88581c2405140c4418506500032800c0002e4080d03407404030006e40080c01200214032103c40081c0166040c1e00e00c1c03a040c0101611401d044c50703e450404c403901c2402c0b500d00c045180e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 556162607 1250 556161357 556161373
    0x604062304060830130b0a0c050d0905040c05071709130204080102120906060108071107080f0a0c06020313030609020406030b091c2d230c12030c0d0e 66
    0x1820074040750600900400d003282c04c4809801c2c00550024404002c490901400c00c070b041103914210200808592000c620207840313112400054442900f6600d024000e402901d0070703070540b0740d07101458030706a407401c407806c022696540c0320456050140c40c0000300b00041d134000503194004201c01506000030000c01d0041083c64a9400d1001d0b6002a80403c003160f4000c600005103100040841d40d0101d0044010320b00c616101000030300304c08010306a00c0a05c41000e510515108013804001c000c1e110400c101c49800c3c0488050319070720040c2c00f40035135907800c5140c40400c0c56413001c000c58020010509400035014110f48a5500a00340b00d402261b0066441000000007101d1540c03c62148003185d015080300160301d0b0f141e24084e4403500b207507820040c1a08104407a210302c0c2103080c0e21b1481c40704499407000c4c6a0300040e1245551520107042d0046807461108480100900418050b80008140c135100d4000809003601c500081d52503100140d001c0c032160f03d4a482a03444a058040c141040354458 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 556163857 1250 556162607 556162619
    0x40f0b070c15210209010e090a0605040606020309030f031218160902091f0c140f12190518060c0c1906020f0613020904050a0206031501020105060406230406 69
    0x4002c00300c1850001c03e0300c075040d4611503002d10441ea00d48040c102c0c002c0d480c140419000070110781c3c44c210001d00c6196544003294414400d50300a42c0900700c00b8001f0850346480d000e02030741d44d80010444034400d1190003408450214084142c805114031070014012945a03050002100b100c4280c602505101d42844e00301c0c400c4548621070b0040c1000d02c0c005030341d210b002c002e002044ea042602e10401d500f113800f262030405d80c4000d0543c0761640020f5140030f07000e901101035050032204154100644243c00c0c41d0844401810003c04c0c10b501a50343d00170014200e51016162070003240d01446e14501030405620391424104002c107000d071b2201d0b06031805007004a0000743e810000050215203a11000401d03c940c0341c0401104060842c070f18014800e61030000920303003d4840e01a8000e005080d424040350402000304821414141d00409103a00c0e89080d0f0a40151000451580d60040d03080a01003206424a0711544040d910030f02c03203d0000d403a55034510001a0700c14042c00b60000d41d601d40c0043e40d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 556165107 1250 556163857 556163879
    0x70c0b0a020d0b010305090613020f03031b190f031101020c0a080a090803031911120a0b04050f0403090b09010e0a0306060807051512060d05010f150902040f0b070c 72
    0xc5080844001a22004145003007011946000706003418149408180720a0900008440c3ea11014261640c542c41507a480401d1a071041c0c0d509182c0c040c480841ca51034840f0409802c13501807003101c4100c400306020620400044007401c3c03806041d51182090f4240424410a1031482078031880c0000351604542d0b0141f10303e0110061010b5520400118010f80c46981c042c1e043c07402040920001d5045040c1542c0c20010007100c90211240d465644060b000071081d41c0050310703584440302903202c52602e840300c540d07030140480b8500648034501d000300046d04001c05461241c0640d415564407000f4505000300302e451580580209810300134050071400056071000700c0035020f10300c5004003250329450701201603d0442160443e034401d220800740c0c800388001c20415110303034040b246011011070b104d9070b010034046451602c001d0400e500301000005003150a80010210311a1003140140c0f083d5102000001c80c05240203c100090201004016184440001d4a099805601082901030b555040104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 556166357 1250 556165107 556165111
    0xc021e100e030f011a0f040b090a0504061b0806040c23130b04060210020a1218110415090b0a0801060f09060602071805070e032406120d08070c0b 64
    0x3000410900c95040c603414140108507900840d540280044268080301c0f500070b000d01d00559004208603000b52025950f90b130400e00a407071000c1e11040d16814001182009007000700e80503640c85080c03c10b412520065000c18141181003a034031940c070758075548200710280c003403107003428100403803464807042c60004403102080108100300103955440340010719000c0e00072103500403504044207110810080d40c010803480ba2076040f10700016941d1107c0d49094500b20710030508031b0350b0136260905d03565640c081d01240000003402840c011001c1002d100400081c2c840212520fa240e4103140020410041036801603100c80b400141a0007901341c0750791005084500b0707640841c00307600410208009900aa20800021708694030282400a041142c0c8611444038502140003d136a508006100c09108140e0310b140c0d00c1004060b940c1640c02020500d000140303102030360660002d6035010036010310b05140001c1141e81120041e0030100c10841c8192a0500c004040d1700c00d2007200d000c01030010783e107501924 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 556167607 1250 556166357 556166389
    0x302041a011106040308180f0105040303021c05040c170a02100207051011030714030c0106060207081b030d03020a02150703060f05041a090c040e010905061f0c021e 72
    0x61100c4018400149811600b122540781504040c06000100781d010000d9030340400081071044d841103090710340d14a8201c0303e840e0780000354a08000e10040580c5500117109071224906a400802c4400e00d20000b01c42003030b070700200703802c0741c800c0108034542c000c8545d24902c40210b000e948000b00250081100c0e403510b040910016000326406000d01d2815055200d06030a031864546840d0780940445c0c0d90301d00c1044406400400d0035240c4405440382003003100c004201e48030080c09080e5450f00301969440e540d00498285004000c04954044900c900030309480000038000c08102e101c10105400940c0080319450441c0a00f00d14044c4001b00301740c5841c00740c012640c00180c041d01e07000c0040f01e021280d4010034402c0742880800301c54108507070804000e092084a43c4078035034541500c004018407031640301f580b00d20324220000841f41c80b50707442079210311401c1d941141c00c03d81c0290302351485910b080b400c84c04a5014803480015040070454910903002100201c0c400445140004502283c050081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 556168857 1250 556167607 556167641
    0x29030406090c17030304020607021c230102160f0615030b010504050f06010e04151d0a0606030b130504030e1c0204141003020d0203100c0f021b09060103020310030204 73
    0xa07040040c02003078000184289504804070b00a0710031041d449220140c4081d1203210301040280c1599240011010106009403041180441c01d107400081d4a000502900241d41c160401c0e41040c00c040c0210340c0128610408a40320008940e85c0039229800003100750750440d911640160002c81c1d42100101850085041440f1585820100019030700000d05c0202106010780500c000c6980164800442200403a00404c4054582e118800c0e100455400040e45d10360000b00b11a100d100610707624060007608a0501c01035464160036402e80d400303443e0b41e503003144111030000c0c03070032401d9070123240c1162003480c00e18080000c80000480303000bd2a6444101170241c050004114509486032113400c07655440142d041e450b28907108500c0d07268078440640034141c10109034003195014080d20300049a0f202040180b01d81d160801061034450000f03080141c4500141907030801742015110a03120001400d4028a59030722004401a41019080300003103080c4038030120050f5918090500b03110090408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 556170107 1250 556168857 556168871
    0x11040b28090f03021002011b030b01021501080304290f0c0d08010b04050607030201110a0f081305100f020d0e013801050906040e27061029030406 64
    0x48240520081028030244840d01400704190090a00711404694046a01c40c00c00380000c402640588036900c01d445c00e00d001150310307002081c2c040c1d20074100a0000e908541d01140d0082043e5202c0d0004c1c01003894a60080c0000c01030808041c00360344095802c3c1b10301000090100c050110140c00c110300d1a80c4400d40400c001848800411469200c4001450481d00d030354503017880c0365840e1145004483c000e0000040303242c2811700035008a03c4040380f05000320b82d18548080002c100d080c10a50500016a0304008501042c1c003551505142c01d8204000c1c20581010142200040c401e40201134001c0d60244180810096503105082e10074402d6030011420004146184403541d402c4d484d03240884200c1c01d4101090a2004048000c015080c01d10596440c148070001d003070360042c0da00a62602400e40b042207a60904030b21054401e0002d03000700c042c0942c000c0b90300e0351503c01c03c441424041741071050800c0f482c21228180a020142c0b44218481c0d82400340c6491807550080342c0a03100301da15070f15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 556171357 1250 556170107 556170157
    0xb01080106330302030702030f040e0106020105060303070b070309020f1f0e040603030819090c080705010e120c221103100e010b0414060405090f3711040b 68
    0x1070500000c2500020142a803810b1084402c50071140310070a108040e070210028041078000c008955800031035880c9151070f6030780c07503400b0030700b9500c00d00400005500703000201d01182070010035600c007950300545c01800d41d07a0b400c0045004040c541c00030b0b41c0c00944101c080c84681c50b5108090350208078503d210742ca5507800e5001503c6510f4903448140039a00d0700302c040000c01c0c1c1c000d440c00e1b0846030b044500640040500c42c55800b2700300c4c03030318064012613404d4400602c00c1ca000034000200c0e04c081e00d8110804800504101403884120789038040c58102800c101090b2900101031b403251103a502711000d0101ca03080e5031104070b1314451072003245854008180980101c1c0c0c0d83c0042c008041c40c0005645640c1000084140d601651160780d12100098501d030260340d9a131000e640203400b01520300a024902102c81072050300b01614509411860404e50781c0d0042805200301003c00300c5003045903074201d40c0c500550000c0140d2162176280c100107000c040b41d801c0810b401442c40c0c03000c100450303a0700141c0e10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 556172607 1250 556171357 556171379
    0x6141c06020a030b0402190206060f0a1809120203040e01090203010b190c050f010608120c120c07050904030f0806090f060d020604080115050102120405030a0f020316061e0203040806150d0b01080106 87
    0x7410a5126400741d407441d40c481da951240003030070340302c240324441c0e07080c015810540d02038000d6800003004281070302c044202d0fca90010182c401c91707540120107801c0341d90311190702007240310a009150040c0740070008400c1041501d02c00841005491511565030811610364a007001446105c0e2125a5110300c1d003008100002c0204d401409403031000c80340303003070b9104050035520301c14200e03100b0fa0442d000c204010034640070f00c018001004080d181402a10f058076005050161050310324010840203804242030f030400c090980e12890401c2a84002519100d0070031103c1814011304980c020410000403071540001c0c000e141139000100f20082c11182818000780c24948400b130303842103030300b02400100000c0e5070014002c0480c40d000280709030344003080c0c000320b4200240d034880d0b03085160709440c0c0020219070090789008a061010f00a0b800e00300c0c40301049840784a01e22130899076174000c0d004607000c001c544a0b400100348005007020708400d43c95aa820600c07009034000c41d881d075564a02000060800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 556173857 1250 556172607 556172611
    0xc130905060901050103091e0c0911070f03201e0c01020d0207031506080d21020406090e0901060f1820120c040506070606141c06020a030b0402190206 66
    0x104180040c1c600540440d40d40c0d0014420f0301e04258a07082483c09110703222441c41c08400500303240c00d20029a50401101d1207909202e540d4046150200d20380d07480344c8040c103603003415521074103110f0113030840e44045610703039500c120b400300103030000800c0e11060101304002d41801c2465081030740c65094088925051485c1040c555055400c6024000c0210354045120002d803984095415001c8120601400080240350414003070740c421005580030a5130002c80c211003944105907907a803402c4011500d4410382c0950320900c000320760380040c244880007441100c10340c00f0400e00000141c00356100c0c1c034882241c8855008481984400307034450701514150068096220703942005100e945a400c540d40c800c1d1203406601e0300c0740f04410300802e035a803a406086a00900004060a0f100c1615081100c02002d40e4441c4030000c0b201c80c088182e040c20288040c0c1302c041801c1a10214007019503c0c1d0038080d5220358803003002c043c0e036014141442e40d968800f2304444000e190380311000c0305d032070319001c1c2c40c00d580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 556175107 1250 556173857 556173869
    0x6052a0f07030b010801150f1205120a1d0321070f08070b040c0b03010b1204020111060910050919150b06030a0501030b06010e030d0e030a1a0f100302030c04230c13 72
    0x10406003c0340b4804140c8c542100c00c58503082c2881c0143d070a205041c00c010b5410f018088034001001c81445034001c03102c4011284500c2e084a803e501c0a04062756030011801901801840c2802c1c04005c0c10f41c5805050071500461144070320800554030448039034000d000403680785d091242440280541d0481070390145c1031240159285505115500700c045c015203400c2d442d060801c00c000380c216442913040300c1003076508508031a080c0c10305a04185d243c440d41e2481c860356629107000100e03070b22400240712238100400710200f1a548025150b080d1100d07074030500c40000301d40381c503080e0815072540c2c0300841c8210f035200400581c82d410361828070203c905c00317880b02d81001070844000c0c40d15903001c1495164680b1a003883d500c41d0004c200440e080c804501409024590311302c00310fa0200c0818038000740f02720260340c84000c65954420840300080d0141c04065010b03400070100c07102e14146075022040d056040810b18005950080034012900c2003241c801280c403401042080c446120741c5088805090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 556176357 1250 556175107 556175141
    0x301020c0d11030a1b11090c04090c02010b09070e03070e0721090c05091005132f0a08041a100302131e050a02070b0a020703080106052a0f07030b010801 67
    0x181362074008100f014071100004c010301c1904038540400c0410300d03000c104802c000d0461001c3d45041a500d0301e00c1c0d08244100032046043c40d0f080c081561061140902042008000780f4490b12044c208648500022038140d03014450164042a4407840c0c0032802e1082201d40d40d401c5010006500945841d114521000f41b11424084040002402041004180c60007903841100650f02d0070b018102202c20342e8003082e00b00c2101c2401034448162070b00b140204404211820b07600c4110074003030142c200e00115400f4880c05043c4042540c0c54403540741d141c0c0040c00b402c8030b04c0383c2d0000b01c041000d0b24030b0141c07402c403044510b07184101b0441c04d0001343c1450198104c4070820034040709078003800c000010150f82094107562100000c0000525505845185801c049200030b07910300312008800a42c00380030140e001c59009000050b141c3e01c11001c6408820303c45101c18055201904a0f644502d0081c450307403040d0195503d0501d18100c00c00c0007100640c06030014000f039500d06031940e030850b9030010dd0204804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 556177607 1250 556176357 556176367
    0x11b080114040504020312070305041410080103120507020a060e041109030a08070f1205071709010c08071a0a0f0e0105010305121c15060831020d020301020c0d1103 72
    0x703200302014000756202914045210340d902d10000382402d10f407000c00442514040b407060180b40d440303809081a035007076040769480781d6103040400c01103a5031b4118540018420780300500006481c00d1140198910f107040c50f60425055600003298107402c0d402420010f4030009000505282501801025203e400803683c80c08440002280c0c8a1400c0076000e0b0004000048075002c01440f09851003031103801c0310075804010504880101194890142521451800d042c89840000b0b00c108646812034140c40b0b51744956000c1c0d6400e0a80e8102020666140002942c0906030f191503050b0640300c5c1058250001c0d210706800c00d128101c80429290040343da24003001800000c00000e0260352001d028102180c90340145441e940c1d8031281e0291700480c8074144a00030382c0300104c0c040c0740000d0341c0c016240c0c80381555484007a80c259500c1e01d80b1311850304003070000701c003402441300520085da01d0028140c500c0f0740d40581c011900fa0791103440b662002d60300440219040070f40c4174045102c9501444003a51405d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 556178857 1250 556177607 556177619
    0x150501020c060901020709050901062d050d110d0602091c080706110408010f0f05090102180402090a0815040303050f040302060c03101d010303031a1e030a080705011b0801 75
    0x940c10750850103014400004404205038004c0244500509405805118911782039200074041e040700e104441180c1d4042a101450340ba1500340141c2d1445400114045680b5040400554114041054a0a852520a1030342646a0002d007104d10b5008620140e0b070358800c507042c4503991100000e01c0346180b1f0500f1118000802c00021581950380210f8040f0340e030200c55003082d00b81e10a540c043c100d15031a264040038200324a4100c01c0c076803190840d04010036507034130440305d00342c0c4103011046140e41d4018411500030701e09a8003400d81500094603898503141c5550842c0c4c0380c605c9030315020702848560410001016418042c0310f604c200c6500e1070000d6418955400ba5880c4001340c41c40d180fa020100005080c140000729201c02050300380c20000c10701c0e21000746d402e4065028041900007a0030140340f0041003403a4802480c400c00080e1095100d0780c1003440b0052550f01100d81c16500d80185140100480c88100103000320074002e1000084c2441010091614026200120070521035440010800707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556180107 1250 556178857 556178863
    0x7201f020c06060d0c170c10030c0e0111010e01060902031005041404030c110d1202010f0b030c0f030a0804150e0117040b150303040602010c08012412020405130b01020115050102 78
    0x1125044c3c900128110051400010440031034000d081d8203e001044030103400c2000a444550310b006440c0d400c0f011104120403829580150724600c04102680a8001594829103107c03450107021000001c03100501407907103080d1503850340201e01c020f8003c0240008901552014002031200315010844016041b8842e1401e880c02000074041c00b0039011440140b054050051a644c90001c01404142c411407500e0b0b00482c0489220100542c0380046e00c00600038540314072803004200500a120117118007080190144520142d15054000c210a550004540c440a0b00c0a0060007142d03c0070208020340c010058241d10300101c0c10851240050b0603100b41920941d600141c004d142000c141d9140a40b01c2c1d00c500c072040c400c6da0035100000d40011410b9040d405243e000c092030760b441e03d15990780e02c200520042e04c80d00000a08032500720a4400d075014548040d40140000c0c0d015041540c4c40b03000a094103030360440031a5203603c030102c2e0310803981e0a1049600715400c404020300005d04141c0001e513 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556181357 1250 556180107 556180111
    0x50106110717060f0c0705010c0f0f0e03060621010501060e09070306060c0f03270501030e0f030f0a0207121208070302130e0a020d060f030309080615060307201f020c06 74
    0x40c4c42000300d004141c0c0f40710603408840d0080e4001c802400383e0b6140d00d1004088150300580703040002c0501307000c010198840d8044048414004009110310f854405c2044890b85025038104001c010400b01007031411820f0003010b008125a0f00c427071074280401024041e80c4400144940304161a11400303010241d0000e800c905816081000e80705103026900d0242c1301110f1004174050074007107400e4585092070001c004241a101c0a0340d050202c01c140c492001d503a11a200e03207901007a00b0a1042e02603207000070001e0320001c40c1307510445028a5a07558482094128110141d9002465071400141d0341d40100056402441516086103850040c0d105108601ca09024a650070b4400b1008030708000038580503609141e90f1910b00300b203080d0f55045400d003211990f11080f00824600c1a00150410022940c0c42c801e510810202318141044820440f00381d0000380807900b442204c17144d6084008500400340381c4622040024402d046600e8240c10105070402134180300d042c010804481124004900a5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556182607 1250 556181357 556181371
    0x3020a2a05060f070c080a11060a060503010c020d0507110a1509060f05032202030309041e0509030901080403080603071a0a270504152418030b01030f0501060905010611071706 77
    0x1544441846408940341100e0043c8c0c0301591052405110480c030035580400103e44040300200b254552191050740c9030303805107403108003182045c480c05021550107202d01c422070360001c0140d0921503c0d10003e240042d84280c0c084d000401844003403182940024400900041d00d003052801c628208403541d0079031140008295680d00c80c10781000464404205540c00080010320034040203041140000f0442000e40084011505040100703201c03500100c00c50302d0b0b0000696403c00d5542e0b5a40b416548800040c00341034140c030a1200004400c1e100c1c03105558100e00ca0340d0040e941d104041001002012041d0701c04889150401400c000b080c0c008101000f10f41c0309031000b08070150004040307503d0400642c000a850750a000c01030f140810301d0340c607041e03c4901d241c96131210001c400d0840c041281c01c83c0002010003485c9401400400c0c0c0d11340d81404a0741c450070011900c1921800540c0582d04d0a07802140400ca0464004140b80003c0c080d007006041c080416030894921641c00c10f035101c4000d0702e16 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556183857 1250 556182607 556182623
    0xe06010f120608030a1b03082206020f070b180601090c14040602010207030801091104090527071401020115050405091e030403020a050f09040303020a2a05060f070c 72
    0x300a51405112030100d801121082000625500c4020544951110802d0b0300020095034100300c60a8081c0e216404840d01681d40c00c4040d96a641c1003081d0350383c0141295181e580520314003000860b940000c1000c400010b840b151140c60f903241400400c40060686c1243c07940d40c2c60f1000500500003401c03030441e20038950100d66148040001d880c400c8c00c0c12050142c1810004020078500d030150000e100440c407907078a4225980c0d07103041c00812215140428046000104003c00260790760350400c54025007802800c0801180c1040d8034030710000141048405a0400001040703c1a040c4410503012003080c0024400030007508a081d04044040c000c4900ca2940c0b80081800242d00700024000c03101130b1a020390850300c5618405689030410702c0128440c2c11600710104e40d0b0704080300941e040260291180350240c030b0b0340e541680170750010304c003100412121101c41082000600c0d1203d1720424450390720b049400381400c209007031100040040181030041014440b50f00ea0088114820399000200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556185107 1250 556183857 556183877
    0x207050a0b0a060509040b070e01052122200409020a03120e060a1701120305090103090602090307240305160c020a0b0d0b010306090c05041e030204062d0e0601 70
    0x82c41c00800342c981045401140d140204020070640c0d450150240000791030304c0584032140c00c0112220300c00d07034030500003101003490a0361503c403051240c160400042d8405401c1070710007880b1041e0209981005603103101c0303107100000303081d104600c44c001056000e94080c4001102a00800c5282003035100c028646d072241003610700352034807a103120448800010001c50ba94905e5500040c0411221081e403d01e80c0d180c039000103001d15000040030040e0f075040e150241000d0f01c42c4015002802281e034252401c0c0e4080004401a41d800c0c803019001d412991032030703840e4070707805801300e540d0703182116041003417525000602c0030b0b8403d11304626111741a6881d0000f0034200a1001c1400c0003480d41c841c808038100480c40b41e00c2c54105800140c241c040aa03010040305a94201c0801581d040750584000300d4000c020070700401008000101760306044100c9004070960725408141112610352209028040c0c0540c080014800081c4100440400e5034000000302d042810030060060040c1034907040c0411904 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556186357 1250 556185107 556185121
    0x60c1b0a0501050f3007031406010903060f0902060f0705010b090103081b01020c060f04050f150601031a030f030405090a060e07050703110a0804050102010f2009030f0d20010207050a0b 81
    0x1503038800c1441e0301145c1420042d110b00701c40e064102c00f5075402010034104020203004800900e8221302c242d405035034280500e403658841b040101169070030713644840c1e1601a5180583c56141c001c00c04029940720300c0e41c0d5998135081050850f070307030858587d225940000041021070040400d65008211401c03000c0c241d05801104240240300d40c040300e80d04c0340203803020001400400d1446d144641d004001b69403800003100d0139a600c032080240c40040c0040780c0804650309521903403044140341c009003001100c00c3d0700c10000034544102201010b0055100060038000741c140a00b1060700103c2d1038006206a60420000e070750b820000401c094100300001c00c00c101454420030129040c00307550020345408881e5401c0040c2c2a80c8680216405503080120002408405218800d9903625400400c1c83d200700015410f8015840b055009926119072031100303d42c032005105400042c215521056009090b44400780402210042c081030103074414403019000c03c0700802c0402100798004180001903a840c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556187607 1250 556186357 556186387
    0x20601081506180108031c0c02150c07020303040b040f050109031502160209100302040e0c030c0f03070312031a040615080405190b1801060f030807050309060c1b0a0501050f 76
    0x1240c100604544000085805c000710003040091201c42603046003071104802c0609540b143d400d21801a4440c240400002e0f10302d429070f81d00b0401500300c6034070740f10803500003034a181c001c0d400c0380c0800007002400b08000442c0307120140c0100400c4c24100c0303013a461910b9040150b04580e005c06140b41d00016618072002c040b801282c3e289a0040800c484e505000b00082e03407000b207900080340a2440c0c0b00c040d401203c0c000030500200d803801001010720210b2003042c08001c43c00809102c2c2c00d480755030301c0440002c4c14030030110355003042940c0c001414451070b168040d120039803000340360180d4500740c001c0c4800691680031129403a00d6061200440e20342e172402c40e141841e005141100c0d0741c9000001c200304000000310703500610011480800000009440038202c8030a88a00d0422602c4190b00300b001941701000703800703198010025607042c810b107040494120351050841221940101c41140e0310085140340c0b00b15100b1003a600b900290b41858000ba1191003448007044464001040c042204243d030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556188857 1250 556187607 556187629
    0x7060c2f040c020a03080a06080a0305210906100605130603020310080102031003140c010207031509050601120204051b04120602040f06030e060c070209190b18070f020601081506 78
    0x340c0104803403445282d00030340301c4607101c41c210005420b20000c103040807828000c0030260707032102014116281041c0e43c1525a5803004804040003203680154444041c452020709103d1018400905118a046412805541c14030f422400031310000340542e8202c490080181002d0f21380500f00140c1e00d494190180b26000320550102240398000810080c90702c0003d007002d012644580c80b8a52607035940c412030380c2c41307007800f095081c01030703012040030400b04030610203000100c0070508000482c400140c0b140c07030a00e00c00341c2101f0303003d40c40940c1140c210705080c443c0950200542100e200f801d010901418080d120300e1007400c40501c0380c0405c80c01132011983c122001440c0132060030344286c0d03655a0145c00303406504920880c0c0d010f0f000006054000001c11180303000d0303004100c032000741d44038090340c40c1605510510306c0e1982ea40303240203506529415103122405500b510f61102518040c0b400820103540003010808542018004024204001a41c00030728420340442c080143d484501041044844c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556190107 1250 556188857 556188859
    0x609080702030109050102130b09060d0c0c1a150916180b22050a0303020d0323090f010c02070302090105040c110a0821040201080a0506031f02040807060c2f 69
    0x40e082c4c00c2d200300001507004061801e8000804c0403240c0c1c3d662202c8650f801228440e94100a00300040c0b449640650b2041d0340c0001942801c1000c007060303403140146080300d40f50004065500724203014900c0760125120001c41d0003183c80004910b0a0041c500460380d01d104c07108140201c02c1440e00c03400351060112000f804040402e951180720340300400045c5c92221030000c60f411004140440c5900304529901c0030799030940c0042441c0c45c40c440f0708400074021903a0079a03181040d03142d450f61008417064540d003e0220007005124607100e10420500315000c10308101c0075907024407030400c016160003d0086c116070044500180c80750702e9007000e480e0190a404a034020f4080d041524040107140805030013031121540c1281046225103150320000c140030303140a030204690200043d42900340340c201a921400150a40d004280c110b6101824014000741c1c12180340d40105041c058408100a07520040480303141080c0c5244031500c0b050307648060441240083d403601071810380340c0744110007541b01d2444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556191357 1250 556190107 556190111
    0x1b030a020d06230f01120503120a09080a0e0406090e0d1101020712020601060306060e010503150f1c1103120702011d0a0f090c0f02100e01110309070302030f0a05030706090807020301 80
    0x18280d614104504401c8480045048801c0300100ea0310a9070082c1521b1658808001c62900242c9a400500600700a09c0c4450b420348500b021341c00078440310064510620305444000b020440401040291200c82c4c0284078445d140c01101c0c4450b100000f5802071106407800d00b030800b110747c101100e002e0300c20300101602007031401d0b585044095000550a048134540d81e1704104480d210001120151140c51207140007410500c0800c0a0280c1c180c1651081500102985201c05000001c510030034000c03941e410941140351242428042d881c45200b201840407005043e0282c2840303282021400751001c06030401c4540c0001d191a482605a140000180104031070119a83c03405007031a03c0000b4040c080009042100310810a802030300207045044c1d00780c010308a410300c0c03900c400000302224680c00100790f403621780684680880300c0080d03000e010190060007031181980103051412308034103507510306a0302c001d041c034003c00e10200940d2021380e13101340d010441c0340c5a8203011341140624000a54594 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556192607 1250 556191357 556191401
    0x11d040603050d080f071409010c0b010902220f030f020316030609020f041407140d090503070b1e010b0a050f030f040c17120903030c0d0e031b030a020d06 68
    0x4100043c10001e4480180e4036601a81c0c0e480e040300481007410380740030f0301051038402c448134005010320142c594010185450340d8012229191420020803c0e8003c0c3c0d492980051580440603409441c050031311500d42e0b0f00c102080c80c161144003004070b42d100140c090081c00d0b01c20011940d00707010f9001c00802a00105103090385905204005100401c8103e10807802c2018015150a04e0f010b0a400800d01c0060035280c0e1b500c261040e50801048808841e04210800000030b04401904c06c0b5541640a41c009544480d003c1c600600c032220081d10400c5501c3e940c40030b040704d00101c2d03608941540c281610303980c0ca0b000f0402e0140d03000c1c01841c2e50200400c8003c0100000b10007802c1115100390300501701c0002d402c0c1d640c0056168219602c0701c0000a420010100c907001e5060f00c000d00080001070203c81c0340c002c8200b103440c10000c5891072100040c07000c080900d0140f60030009101c000303041403410280c041d03074500081c3d0f413035400315802402074804900e50810b03c142a488059084903024400c4002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556193857 1250 556192607 556192613
    0x50d030302121006030b0f03060712060503011e0501140604030f050a0804030f0204050708060f04020306030c0d0c080606030105070c06090303060f090e060c2a0309040633050405011d040603 83
    0x3c1c502c60300901d00081c3ca00310030300083e860181c0b00302c000c01c00041d019101645900f03104942c1c8140b240340c00c0c60525150f41d0700086980782482102e4080d516a000545c12201c085000b00070b0300c0c030681c881d01c8800f94128a1180340d03596441150201ca0b070003c0c0310440e0003d01e10303005042801c03402000d0f1081401181c00006e21000551a01d0303064800c23941045695907884094a0841c1c080e070f6a1500410704c403818603030f2810940d005541089004040320403180c070010004282c180804001ca5810007a030408110190b000c0000e5900801c7c124002e104520f0018002070010800d0000904050b4a5800034410705000b0f9101d500501040d050303a6805c00d85850554001c0c0608505c944254445e80c0c001407207203141d14081d1800c0e0f6081a018061741601c841031825a90035148070001d15020410070038566039601d21408008045469a0301640c9000e00d0050441c508942604c14a42c4104c0d0200c50009501c80201d4003601d100742003160001034902c903180d0740c6406c4804001e42081c40d0032804014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556195107 1250 556193857 556193881
    0xd06060e010603061d090303150a050301020c010c08130f062708090a0603090c0e040c09050403020a110102190b0c0c031204062003060f040209090f0103050f070b04050d03030212 78
    0x180c40c0005d281c0902040500c0041c121072200312420b100b2600181b011030600e0a84452451000400030b00c5010f41d56140d000080c2240d110034a1041940e5685440d022640d82140702a544540e05c26520840c0952648640c401c1d01c2c03070a40c00602280e600e42c5001d28141c082a103410640c00100f5030640b000541d0b107044440c650200c0315282c405e030b02030800058818402d00032144134030350201d1019000c502d03002d04014050f03006001180c180032803031030108080d8020711480b0700c5140690b00600c0392165505140d40104220b54500b811074101c8a03500c400206000c508192181d0300044950440d902e200c1030583c83e025052000140b4040001c480041401c00c90007140124080c00301082060400e01c4001c44403401c943d840302c07040c0c2090002800c245000c00302500b401c003014201510b001989000540c5801c02214649080d29a035030040c0103101c02002010301c40040c18004201b01400c02032038940a01491180314820013075070740180d041601c00d40541c0e60202c081004007800e070030300d1001001c0f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556196357 1250 556195107 556195109
    0x17060103031419021e0325020a03020d0b1b0708120402031f0207050f030412030c0602210f1602030409150e01150206070f0503012102090a060e0618060d06060e01060306 74
    0x403070310b180c0c1101078040e003008001c07243d4000250000f00b10340642041040c1400e80c0c3e142048e42c3c066801c1c1c000001603284c42d035403001c20b544502c41800191904482c512840d400a010483c3c03505401e00038000090394181c01c032420a1200c451444050f6194400a0301c1e0107401c0703031107140480841c2e150301c0001600f41c024100c400d1051003610760008501d940180d40b40602e10502c0b007621100b41483c000b090295000d10382d11401008090303d441480ca05152100c195018034034045100081004119180601820b4100c22406112042c1102d01030000350349020741c1c050b0b640f54544d070b00c1c44405800086008140200040d02c1100007941c1e4505100c1e001e00204408017025005040008020030701c141a1400e00748100e88415003141d003030400c803600408a809000c01d40080e40140c1c4009656107030350092041c41040d00c040b840c02c1c204449100b40302409000703540501c250000101d801c0400110055002c501500d0210140320035080900c09004107a1002c007800c4d05040022408980c9600705034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556197607 1250 556196357 556196383
    0x8011707081c031808070f06382d010c020d060b0907080613020306030316140d031514130203010e060f0d170c010e010f050604061706010303141902 65
    0x790704036004000c0c02100f94002c00500c5210308010000026401c2d020190300d242c0620b01c001380301280c9401c4207504840410100030389913140d10001ca450500781c12000e22240064401c4208088102200da4806403040d03507080010000e1455043d90344d101d801400c4c2c33003540080c407624540f08030f410800028214144003e0240c4000e01c001b4040038010140c45000301400b8004d1484c000304800c41500941024244a5050000b00110390120010202403640540218403609841014100940c600344801310400285820020100d51a504c503041c5102101c010800201058103420300144103d0001c44c15160881e01c080004241d2080b1130480502c41e810070303160781314031100c100d08000041041843c020a20380c040000c2c6800c0e58a50000703028801008000811601008010b040c02e44030340c04440803060b581c441c02c000d403524250146071300404502c0c902c021103031030700d00c0d6082e25907105010103800c0c00110024440c0841c0b01e08200c07810300d68402c4800040b4400322400035125010343c031540d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556198857 1250 556197607 556197611
    0x3030a0204051c03120b010e09070f02190f0b040c0e01031a060d02060d11191d0a1a0a1b080309010c02030c0d0e030102130807090e0c0108011707081c03 67
    0x443d21009030300d1024200c560300342c1c4600441001da107900001815044e407400f4100070380b07260000d06030f454442c29103005101c02c0d164140e281c1201c0f400249001c2d0701c0744042c81006c00c0c44240714045040c00c00e40c03148541d0414900081540d0b1414080300b0079039546c0c4a01c103680182800042804034007000d4417080c0081c64030701d07841621120200859011481c602a61041c0100040402125150703c54858040e100c042d003800d103a4400354000940e0100501540400e42c0059501e686408210380c41c04989002c5a0b042c404508103900400000c9604c0f4000c18003032030004840c0040d40c0a02946480045849441d200c0900301d4984105c89810960303480d501507080a805103055400841510403402d0781f500141100c458096040721040712049071160103550800649030341050201c402c502600c601002400d186240150103030489084a00b04400c0d42c000b01c4800032241e9018a0b0700b4110b404000f403200100003404041030400c007150f40701e11050300c00c08003004100c0e9443c0d41c590301e200c009a141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556200107 1250 556198857 556198879
    0x1109060c280605010f0f050409060f050915010b0a080c030a0f020a0c030806221802120109120201020301080c010305040206130e01051c02030a06022d040f24030e0f03030a020405 78
    0x4c8000403031b401104001c1c042d010003403006040c00d90205e840103002c0e02001c14081c2102a010707080311425509000d26410041240990401400c080360040c00a100018903102034a40b00801c0c04a02400107600300f6000404150010400c2d00070a0004101b94811540ea00c61141c001e0030b09122000210080f5904200060300d500c5d2030801c01641640d82081c480d42d61031045090340040c10f100e4032848050174422000310158480b10301105100301c108000144403105400c060340480900d1000b4400c5a00410050040a0000c01d4032440e50a007800c1c04075083c1c889100040b814000d103901140311281d04000040ca552207450315604803682520449591008074602c8441c82c250742002a40651101d0080d800080d000d90082070840700c414201c56a05a003260f00042180d050f844200d440e8501190a01011481c2c801c1d500003002c00101e032046a03c000b1400c028010303010103228046c142d4809441001d40020700100c4920030090003a81e41d2454403140b490000e420500030903004d6441001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556201357 1250 556200107 556200119
    0xb1603112803021e0a17070905040506010c05150a0609020403020303030c03040f0b1005030616020d0f140a0207090e1204030807240902131109060c28060501 69
    0x12a15144061070440c001242020181d400d4400c00c20001402c140d07003004400500080c0180c01c1030743c4030820350101d940e03e0740d4840040a061032415032107450100303c07041c0a030007600302e0083c01c1120825a80810300e0754403180141d80900d03400307201070309501801c071b40e4040c02000080e030b0078030401c421282005110b450b9010b1a080340102c1c08003e4245e402040801c1f41c4100400213154814411a0742450344241c99541140307040e070075a000700d54401140400d0005240a101865020a20042641c001e00008000940d101d02c0403601006002c5103143c0c99425a101c0c46000585000d00c0300d4140e0358560890300290b44031014403801070001c0c0b806444d05140440440c5004008500b8020a410300d411611034210550103004201d49140028040c9054040300341c1c010344182102d100000b81d802464018800030401420031035160a2400207548181450f1000f40d6288060070780d0596154242d040246180c074018050700c01e81484804040c07a0104901031483c1d040c14450102803200381d070703280 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556202607 1250 556201357 556201391
    0x3120f0910020712080903010b04020a05030109050109091101110a080a0f02060906011412070801060b12060d1716022e030507020712110405190b01210c0c0b1603 71
    0x80078a007060b00d41244c844011880c40406801402c400400000701d50308814000382c00c036409915504040ba2011004000c060143e224150041c207108100b400040c0059503003041015000c403410381446210340410f200320303004000300150180d0182a1550711a20b040703000c0c0080080c0c00000005208080000b0080c0c071010032424101d54140d04404000e164103000c001d040e03810380c4403140840c800c400000451280034020f100060002401c103680d2030401d110b0210b84030000070a200d0203800105013070310000e07a42005110080b407012000540361301d80003008000c015214a400382d4011842820200e0204460599007040e110640c86074400c50503010040e4180d40044a002c000751700100400c100401031b29003420b038542c0c07007a0205901e15940c90005401c0740d07403d4034805040d0801302c20120011009210320381c41d4000908052103032440c41140400a215103040c002d6800d0f4450f25409034190140000cac41613183d010300d038101c0c00d103011108610304003100101407000a0508041540412806c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556203857 1250 556202607 556202609
    0x60406080c1c0503120c340204050606090901090606020114131211010c020a03030c0903050613050c09010909050c1c0212070506431103120f09100207 66
    0xa0021020340d990350310851003407001c90390140c403a4081080004505250840224400e09071115021388628041006a845209000e447c04034440c450303240c80b0302d10642002d2110855412940070480d503580714040b0b560b5015012420390803400c0d2100202d001007042e00004c055400c1a4020444011041454040f080041e192412840800111000410f1607200201c101034a2420b11030354084151705401c0c210b500807000c0c900143c0004024000300766050046001110301450015000360940d214181c880001911440200c04034060700401c206061080c0e00040e4402801c03080e0b1582d40d01c14000c003800000004940900030004100320605c0c220f444070350044100b03031000c806000c04e036090005060b002525008203201c1c3e00000a1f80c0d5842500910001010f0341c00000001c124448081944904a03030000c111511810f00c40d20f200702c022646a02141c01000c0c4c0c1c82c2d0703c108a070119007000b002034903c5d1070380c80d40040c468505648548c0140b40804c801c0d03030000850194040120f8403025a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556205107 1250 556203857 556203859
    0x902040f080c0f180a0902060d05040212030a0912020d05070b04031a010f06030c30050903191206080601060e030f0601060503160201060b031303110c010909090305070c090203060406080c 82
    0xe0180c135180307a01c2c04600e1140e00a0700854002074900d8070740c0020310b40d5003080c4814148541c841c4100300450404400c0355841d6420315005604000e000300340a420132441e03001e000816070342c40010a0565403845556104550410140c41503151144901c1505600c540400d075004c840040c2c00445140045080c58100c5991480106e008c1c0d042c80000c402422200c504001009011a800c05a51010038100b800002c5402c031070501c0001c11201220550f00e00902013031f0030760400e010649207801908402d402c000080d01d040312403e41c5403a800c40042c11150402d0b04584140000841c001c2d40107880340b40c602c0c1c011812941e403040000d0741141c0c0d480090088400083c0c0030b00129410702c0d000c000705c2850341000e0002040e42d5072030314a8890240c2044806020a2a081302000141034125613141806182e107000303400c10400160000e0000c40061251654440d540c00100091610400c1625036030350780154405481699400060069082500c1c1c0074812490002c0c0080c0161000601040c0d41e48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556206357 1250 556205107 556205119
    0x40b07210e150f0d0507030b100201090c0b0c0a050f07031a1e090708010509030a090f081203100e130204180f0b04030c0b070503100527100902040f080c0f 68
    0x460b0010440c190000c202011444005120340014a03030103028107440b40c09a40c0d0001620300101003041810152035400000b03591400344500f0101d20504040c0c41600e8209252968510360f41c280203241402e4008081d049000c2c01450001840300485c010084034041c00c645440020300c440006042c82c010350f2607900b03002519481090042c0010006503000c0306020940303542230355840c50b00303080d5181160041c1079a000000c0758420716801a6641c0b000c0d05e076100550364001c4c1440310750b44d0b031250364418132111404080b0010703641000d160080f9015103024480c40322a1b050080300305907070541044c030407840b50b4240b0303982a640a030b1041060305000e4024041a0582c00161a00580b401d0058800d604124450030300c02e0124103412485405003c5980c1c030242c4c3c1e443d001b4418002c40741250881442880340125050349440103082507100114100c0c0314034401c0e00c41403024001d81c01d00b0381c001c0044500220b4001005221039041d00c080385e900405445011041c5802c0161807010310007640d80c401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556207607 1250 556206357 556206379
    0x2071d06040b060c25080601050d0b0411040c050a0807020609100f0b030303010b0711040b1e040912050d14011a0a0e040504060203010305010e0111031b040b07210e 72
    0x89000c0d0001c414412002d4405480c2015403d0950f0811496415641701d90714480c0146500350b41c040c41220082c0350301d40150180c2c0d41000c2c00100741c0008203101500310545103001c20107215007415614420704c80104200203210002c000a40641c00010520380840c0c03000c000103201c18004100c8a200d2a003000180030036108600401e0001c08921201c0d015441d603401020401d40c0301040207502804500e0304158a401030340ca04050041100d90346a030259003011001c8455445d01030080c55565000100340304072298000204000341003204000e84501c400003000c22603280c000008221743c1e6880ca900744425046164480c0d40c403142841204182000803034141324a52401e40a0088000c191400011020513940000e007500d1068405a500c02c0d030010040003048400d110300d04481c020500203002650314111010310705d0000900e4a0288002b5683d00118003070007100710780103840d40321450f41d140d0a41c0d082002425070b440c800c41c2030044080040031401c90081c410031058900091480b0052 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556208857 1250 556207607 556207609
    0x6030a0911040c441f0305030307120b04050a02030601091a030112080d020406030c0f030c080f091207110a0b07170f04170a060507030212011202010509030708060702071d06 76
    0x32034854484840098512201d50580402801d900e843d85a84e1a40c02c00b0681405800c0f05904e0a1485030a05d03004040e1108100240000c0180c941c41152810140c1003174001c40e0301c11000d01501a2800e0b0311500d020200044004075034055801070400381c3c1c414023455110807035081080400200d41c40400014001002111003058030782d000248203805060408034041400305c240d8100780c20103400b03c3d443d0304101c40c2859003d001820300000341e203414080c02500e1031010384010f8002d0700c28000140c10200041c91240104800038241030040c160980c1c404150034079480c429105802c9901c146810600018081d150030181c0c2c1d0066040005100e000107450442d1300705906c010000c5040e0101440700003400800d41e04d03c40d001c1c2a0450103880320035910310300801100c0c0000d01150602d807040c800441407500014401d4150b880b401e00c0b402c0040d540307000680311801594030440d418490b01c4d2020a501c08045007003030040d0056004c4809040e1190840302d61220220302100008d00d40000103211 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556210107 1250 556208857 556208897
    0x5070f050a0f08220522020f0a05070203070504060806071209080d0e0601050a08030403030503061c121409011b1112031c0911100e06030a0911040c 65
    0x845114100322424200a40d55615000b05020b6054421a90104001c03446900d482c8400c1045550480703d450014100000030302c0d440c070071400d0b218585501c218690003609850341112100700084510303e4603803503440002095940052401c82c0240205200010755003024080c1100b0f0f56102e60160585650311501115021802e8a00d00760581d11000c121002c180f000006041e084400c48003c10034140c07104a05103040d1042c2d0169004034070181003008000c00100a40b0305881d80b614061b80d681c1c69680011702c13103117181c2c031005c0c01c001c0a1076107607020084c07401343c06024150319484084126403091503e0b1718070301032800440d021407c00c86501d01e03141506508110054403600511441e481c2a5001c00d484600f4a01c840001d60300009001070040c0441c00080c11002031981d050082c80450340d200307a51946c00c14080c5000705414105100d203180201c3c1040d0801001400550303d82c9021405400034040490007500c8003000300640c8052030402e0b02405100f15400d85401b40440074840085034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556211357 1250 556210107 556210133
    0xf02032205150f040b060306160f0207150e0108070c1707080c1204060905272503020a03050f0f1b0f0c070807081f02090d120207091107030507 63
    0x40c28082c41402d110107140c1c000c000c501510403d480c0300c10354909072401e4001c140e000307440c15200750b01c61410041c40900e03211848216200300e02e04429000346480c426481e000c0170b0340000665200c03007200d805100e90302c000d64240301c500903a10031407143c032200340c143c90003408500051301c0c11008009511807004050000d04c425132281080900c1c2007400c200d1641850700703040280100140c0004d08100c6554083c0d983c01c0503210496088211400080301e040700c009800f4107000c01c4000180003c1c004d0704008130281815001e0020203511800b8000000300258041051403002c641b4002c045112900541c000900c145400c074600201500da0a440c104403010036102064007041c2040b1303507007884250801900400704e082c00108241c0b818a130700b00d0705104403600301c00b1841d0301c43c550b031401c0e000e104039a400c00494179120042c2d0b60660880810064400154040c0111401c00101d0a215a0008580d0115035807204208486450108160300a00c06c0040180c0044d00921442d80420300c1d03954446 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556212607 1250 556211357 556211363
    0xe010602032a0d03061404020a08130606031202031c020301120201080907090f0f0b100206071b351603080c0405030604030503181c080910020f0c010f020322 69
    0x402c202c460003074014a00415507582e500040c1d1103100800480c1842030502c1c80e03248080f50194280320100308010041ea0008000c1ea4065640300d0a00080c0501903110300b000e1034220802e10719222000c039001c1c0d41c07a4400d13140801020a12400c04118480383c2c8262810f031101c0843c079250000320354004650307951002d0f2282e80e16015111000481d20712522030090800000e490224900100070844402c44507c003000740d009111240809654550204031141c2c8000340741070100301c1c03500348886443c603814030703102c0100300c44c40500f801400480d04000c141912600740b40001c0000b031003480e82c1e60301805031142516542002401000c0083e008035130340e90f4000503100480c0d040035a2900002e1810368161002d40204100005104600d19a4a5002944103444000701102c040320411381881c1444103244008229540e80403c503600c0080c00034200080345010195140d041c40c2c17001110592000c1c8810081d0342c6000004480b051080c02a00d02ca9408948081104600c4008120800d03003071000c11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556213857 1250 556212607 556212667
    0x12080403201b0a0b160510050c180a06121116030503010f0905060307030b0a09120908070f0f0b070c0812030601080f0609151c050a0c0e01060203 64
    0x10448040d101c000c07100c0d003161424010b10a1503982d0004090b00d24082c100c040c000c80c9000018000c080c00c6a0448030345100803001002c21030350a080c0a03050002002d04c0005a50903c01070140400a410103071480218407801a120790600004102031b00d130040c032480340818406103680c0054180c941c0000f50b52034504501500e810742e40a244d44400340c01da4401c502003071000c40180243c80f1a488900c0103007e490f5010400b50600d580020380e180842e100080031401c40d0000604400d0068000c041c0903a80405203203550f155005010304520403a010b008480c1c13140e9a0001071a040780b04030b010464105002c8040400c0c1401d06416069103c00c0c41a01c040c02000c0002922120030044520710f2030340b0008480e12800c048000410783e80c0301400014902c1209014819076994a02c409501701c86084007c1080307410700808076140c980e0014210007a04008c1c0e0b44541130250109028080e503104030300c5480b4032600d41c44c80040d005400c3c015040168018040302c02e07405c11480c0360380aa184031682c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556215107 1250 556213857 556213877
    0x80f0d031a0a0308121b0f090402040302060c0106050102102309030906030c0a090f150e01120c09080114131202120414040b06090d080714010e0604050708070312080403 74
    0x400c0150b00c0e55801201da08400041c060f45030b08040f120a500a20300400d22115102040c02c180c850380902c1055442d4004001840c103c0740d540c0e43d040f10019540582115200c1002003041c4d4001d0981c0e1050f18007500810503d21745a101d40e00c03d50f0203011484240e60403002e8011004408480000d007540820710080148080766074400300030394801d9404d60440f59030381120b40b00080c07000c0c2d0700d43d0002090340e8520f0310520486426401c200c145490600d00082007240708001200c405020039900010a40340c0318180035900e920071614401d07034800100038010b6030800d484002c10003500310345020100c0c404a403500d0010316070483c80300d01514184110340c0000c400c0024800f480d44558408280115989940f044504150040e2441c1c1c0c2c41c2101d00706d05100780e041c003107000e99015031002402c500b00082d0321002c0191003a00d00d00c11070301c0440204683d00c03c40d598640d88a105035000e413000c0c031075250000740e030500000d02d18094070342c850b40007000f9442c15481641d05284c0a40704400b88403015030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556216357 1250 556215107 556215109
    0x5270114150d0b0603130c140112021614010c180e01060507080d1b0806041103070e01021207060203041502030c0f09040b03011e0e0303010806220506150a080f0d031a 73
    0x1c0994000c030740c16a5554040707403c0b45007c004044407980116603010320a08408500d0381c10852403800c50031012070142e91511611500c10803410901c2000b04410b40340d0702c0b5600c40340b605501042a5060903210441d498505060680c0403142c3c0344036120f80e030490300300144200c61048000d0240070313108115041c00e01e40f1072300440d001e1722800e0704004500840c43c98401c20035544640c2c1160440700c03d50b410400b06000c10034644503031000a1484050114400b001c0500d40d20801a2030754001e281852a41c030340c8050f00d015000384d481a10b068881704000f6050581c501481c0c421203004809800090b07240c041a4080b18590303810030189554050f5440c45a0b0302740352403e000300c540e1881850142e0141d5004e04804804803010000414500c1d4810720052054a00c00104c040d005403040304000002900802d0891150118920088c04c502070032052244042100305025410320003105c1c60850113485404040d036448031024500242d038802034000040c68060ba00050410034040c0c12403144101e150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556217607 1250 556216357 556216369
    0x23010f0b0901090b1809181b06070b0c0414120303040b04020a0512010507031506090302241602030c010e0102033c07150501050109170705270114150d0b 67
    0x4103041e51207039001c1c2800e041c5407420740d0035103921407130b4940b03100d0640c60718031f0210b640d07441901e160b51242640c9451114903070f0b80b044207a8101d582e121061803114a09241e0700d10a5400510607058808074109214081d850b00034440135910200d03400071401d5640b00c0e2207165030202d02400913a00480b1551010400f5103c440484001042c40c00c00401c007810500001411100499100a088501c041003030040a03803119240b400c5075012924080d6600d001401d90000ca0b40703a088503802c4640000d081a0300030028452150707114021025940344154800040d03409940c01c0d03006a005030010403e0b408d0f500012003030320088000c4106e42e806016480001800c0c03000c3c081d20380c032004030f1000c03a13840c0c10045402400c0c42482852034090005516083c00600311407414091894164403c03071020140708400c100e84401040c00400c40d80b031010700e44000001d05040c411011000d070320310a001040008005540504800014001192902c00e90361700f803010f034002c1020b48150503101c52159a2a554003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556218857 1250 556217607 556217617
    0x71e080a0203090109060905030d081f030c0f050a0e070c06060e01080c090c0702180901020c0703121805030d050d02040e0a0203091903020d0f0309140123010f0b0901090b 75
    0xe8004607503030740a203c0054140d0751740380e0021040282901c024002610040ba24400705551420b01080c00c4d150707c800d00346202c07101944240c010743c080d400002400748260b02402101c04c48a060300b007180c1c5031018403003072052070701a01c0300b20483c0313201003025584161080c808450142c000024a0340e00c0e41008840e884080e88045140d5100800c0c0300da0515006044030b41040040e840f2074079204095012503000c07180707001518000201100051a801001e40484aa00410b18281d07001c407500ca1500d50a9001c0c0440d804d0005120400f82110000c0f4210781c400503a50000c0c01040b40028003c000c480e95400010040c0016400b404002100202c2c1346d55180100f5449002685a142c0340b81d03038a25240c1c0040841d81c00d02d2080401c0000700740c0100c1c00762051546d9180422401944034026400f514054000500d081c406901c000d807808010761082d803400740c00ba0319000442c522564a40b50412081c0500050f43e012088100606804400240441032060500309406aa500e01100440c0c100d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556220107 1250 556218857 556218877
    0x2502060105121009050c100c0c0b09010c060c03140a090c0e190e030910020601030305090d0602040806040f06050105010f0503060d031103070f150501180e010e030a110d0206010b071e08 81
    0x1001d006c032001460405c0900c0e20303003402e40c64079800480341500c0300880c945107441012010100080c1c441e00d641d10031004080925007007038050140f00ca20f142e00400928030040b6804601030a1400700b414900c1c20f01a80100980204101da09942070584e00040c200d0081c050b580b05c41c0740d4860310700078038003a801007106a103004405541c0311542c50090001c80c14120200030b0454006400500001ea0410255207600f04c05a0f05c0ca560206079141485c000e20482e00022154881c210030402000104290b41440a01c00d200a001d2030f640c800040d144403001644034000328009000088060500c1038540e0242c3d4082c1c940302031400294143c05045902c4408203840310352030a0b00f0041807180030380d1980c0100d8043d650400c2958500b08000f0480700b0104502031049032242041620b2400c25080841c41c01024829030341e0b140c82214002d0541800d0803c3d0000ca80149141030064070300104001c0c1c12101010159441d0001ea0f540c0e28034400d4111040300c1070950101c0b14540455515000380c884402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556221357 1250 556220107 556220113
    0xb210604020a0506040605180a09090b06011215030209060d0b010f0e09060f0a0209150a090315020702060f0d06120b0f130201021b04180b250206010512100905 70
    0x1040d00500450090355008075004e43d40030032082101e241d001c004c440303040800f0860302101c036000f1b400144001407242d11120300c2604164500d8140b08509240e54003030402600c0b1031136144055400320050311340112000e400440340d0001003001d401c004681541c0304800914800d460011030f6a00c0e4466582a0403203821000e4003401404459110310459801444120007080286490301c0c04403000c0500406000b510703900880c0c480e12a4035901000d4242c0c09104828580745c010400c402050b100c0c41788015580d8001b520b9002e20081d40c0d40c803c8504c0603801a10325840d0051211404003583e0009440ba409980d42d040006a0a50b4031032110f82c4c414825003004109082071866071381d0568000e0080c0424a401715070050043c0c1c3c0002d46d011001702086261003100d405c010000340103002100d40341c0c0744003402e80d883c074041060100c0c00c248102c0b11a401e0f00345104841203400e12442000e04ca803405030384040014485e0f8601041e0100c4c0750388014080f039005051a000f00010740b54500011150f581c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556222607 1250 556221357 556221361
    0x10509040605100f0f0206151203190e0a090207080409021e0c0a030e0f0102070303110f07030c06080f0c07020f0a031b06021b0d0602032703040305150412030b2106 72
    0x40e800050510820524401000182807046061410703242389903140f4071407600c0303e401824520080c825140c000842d52140382540b070105401503c0990340428143c450b0f20a280007090740fa01038030a03254000d81003082c450501e401c060400d0025030040469480310005140c0c4030040c402024000c150812501005e48841486864054144800c890130076114000d442c060b10200e0741d002880c1f9048035054a0b200010402c285d4559040003a0301881801070701400c81e0100600500c1e01c01441214182c0d5035140c5540d58641c1100e902d003400740e6801030000400c2150b4800b500e85404216480c0f50020101b0400c241d60381d5803400c10a200d51300c01c11580305950700401c08203405002e00041880286405074001c0b60440010f02c5000580100401340740d40480402c408425007090150f0102c0101c10b404d0300e90b400500c4c455600d411270b101c11240c0c0c0c4140901500781c8450111000d01641d88419451100054000298090b028401d000c0d40c00000582200058814203100b0042e58540c0f400944218 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556223857 1250 556222607 556222637
    0xa06050c0403020d02010807110a030e03070b0301080619060906120b010504050112063614030f0d0203070212040b1c09230f0601090501170111030601050904060510 72
    0x560401020105080010300041026840b54034082d60266030902c2c0c152103a84e100c10040c0c801c5400a0a0b2458910524401c102015002100301c0500c420440443d011250f07100a044503a120074014400303940c0141c0049036410442680180f510440b52402080c043c1c1c0b40e10102c0111a001e074402e6100e81314a031800c0c2e050008020955003d041c0a94060009604003680000e08600740407000301225921104203058043c000191402301e6204d4044405100f1000c08585001d81805020340c1c506000020f484c1410700004107d503410340b401c3c900d80e8203102c0d41c64900c000a410044c03005040d40a4411010f1481d24040005c102030050786040030b0b10b4600000308040c0f021a00411030030300714034050803040400c0d8458400a02d51040f50341d080445440091914140a101c80d400c6801d40303c0c040001c10a0226030b00224140c07100c0c5102e441c1c282400305012400d0302d90076000088640f404002258495200e14000c005e0300b0000b91010806031307550f0001c207004d0426413640d80c00080e0504048000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556225107 1250 556223857 556223861
    0x170f0c030d06051c030806060702060c03070311101512230106080708030403080301050d08120702070302010e030604120302031003020d1b0f1512090f0f02030f0a150c020109140a06 79
    0x8420913038120550100240c0d64040e222032006040395108200c0455800b0031036407090111040c95200b001640c1d150421032074040c007101d21800c0080c0850080d20444c000050461280c40b802101ca50801c0d10750616110307100080803c05141503409e0040e0000f2283d0b00600444e0407007042849100010381c0b141b0300002e0b1420a03055401008054008110030004155050182e0341074030022541c00610300ca840c904450244a1110980001d1128008210742250081a26000c4070f000380c0740c015804ca041402c2545070301007250300802c681c40004e00746442910130740c00386600c02904045218050b440c0c0d0001858a0746042080b1040c102120b11103c160300040c0d07842c4024045004a19252410000045012403610b13000b081000480c03800b1041c41c0255810203241150000300740a5003400791700f400d6140c0019034005a00034400c0d20502100d1900004d1402c24031600300500308031055107102048050710294840e034086640f00c214103400704a40440e04510031195100515081095140c01c6003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556226357 1250 556225107 556225129
    0x307200c04061406190224041205040b070f03030608030d060f170a08030901090606080f070b030c07060504114c050901140a0f1407170f0c030d0605 65
    0x200300800000f07460355203514043d10340241101001c8000d400400204034580a02c0c100a0441110018030443c0900e0702c4003900760280d07004454010a5010481003605c0a104910842c004003a082200c580460340c40044010024880d15020803010f235a041013503d580c005038980c40c21166141005c0000005103600180100002c0202541d00300c0b4201500341c07108000c1201501c01c500010005070b5080303080d03001442c1541d0040042203190740702c0c0c55441d40c400b614043c12102d0701c146000420801d0bc10b10507a44101c40b51030720146005855902c0e04080c12018008803811040100c040c1e246584a4480e01c1c038070728041280b602801590a407101c0001c03064070020100096140414080e1550300d44409800c07aa241000c665403109040103c422100110400c4c00010b80070610092042e0311446103190702d40180d0341d0010001c145c0c1d5086210744a44a001448810b5490056200b0340c5a480500340d03e601070240f081c107100400c0013503403d5922a10280342059900d610500c090306d02004281 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556227607 1250 556226357 556226369
    0x1209170a09080d020309060304050c030109060204080118110f03010e0604030302030f150901030b28200301050603040221030c070f12030e04050a0906140f0c0309120307200c0406 78
    0x14003d072007050041d45920492058a000301d000000050500c0b800300005800b00c8000340c0200b000c540b03e03041c001d00a41182c0280d05855080801c00001010380007c0005c0702a004007404590140803001c05c28846840d06041e074141d502c400002c0b000c20014001c4901c264001d441c05139480c90445803003026600000c112120409080e0a400313182d0703c80c05d00072419644d000401d0700c101d0310717a1014444241d1620103049002e041d0092007100118042d0070290f2803144002d901c02c0076084442d001d000c217000074012280c0107042400000c01510741034008026a801d04209148245070810416082da07010340d41c9400680d2120744100b1002c000e40b242d14009162954900704e000909036001083c1d00c200120442c440d5480e68045030700f0001d554840d82403598451001c200c0c0203000e25004540c114100c40e13018800d140900011281440034048030310070f003002d402030401501d080c061100c080d04090014010006414003401107524100d8000075103c225000400c140702c014000c01c000d94090760444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556228857 1250 556227607 556227613
    0x20f071e170a030e1f03060f05060403020141030702070b090f010f0e03010f1409030a02060412172a0a170604021207080403031a060304031209170a0908 67
    0x1c0000400031902c0e50ba82da0341071400e0000c0080050014041c00d03564004216152001e0280b00001505607000c40e04a0320081007000031940d0b90410495240101e12000e808a0500316000c03980746030309940100c850181c10084804d01e5a01070b5024400d030342e400c110490101000092003082c40c2c040141e030009100600e034503840e248079600030401c800c512a45050501450250900c44540641c12481c4005009002080340351100b034500c4010340302600e8002c40708294030000c9802b07003a022088a0792110150014215a19583c0d910105c0046d41400d040c00c21040c14440f002c130140d0303001d0442c0221040c1d003005059440e5100c8a44a480b45950307110304800b03081140c52000c40d00b26074103041c80010b100c84103459641e4580420b001e4494100d4030072082100b1001c000c04075401c00c0c181802140650360801580a48440000e4840c0a1700c52803a80224244001000240320b440400640420f80320040340ea10104e40c5c5041490303142c0707801104641000f041001d0309950010210004008620003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556230107 1250 556228857 556228889
    0x4080d1b0807021c020310060e090f030403120c05010f061d010e3c0405071e0b0a110601030503041a09060f0c03040f0303080a0501060e0a06030c020f071e 68
    0x34141240302e9100000d005100b44500040c0b10b4030090072940503560042d0550304680449060b040040100c0e004e0480076040700f40110380140c50000b50204c020351070000440c546829610303002030108224800c1020041c84036150340001d0800c2c02043e11340b400e20400814450309102030342075150a01c9090002200000e1700400108603030005a9402071a400340c4044400c1d00b0b00b4414031907804880800400000c4803114414609866040d10f1007580120251003070f8540f1410130301010300c1d082c1c00d10510f03a41d03900f10a008100312800105501c0b0702c54102041d0b80b5450940701401c00d5004d9000340c0b02500049030402c107004801002131005004d17010782d54500b103100c05c0003036140c1c0281440c0b8001944049982e800e40b10081003110041d064000c400f1042596900c3d00600b200c0b01140d101201e00d0504000041c41401000001c0b6500030091a000340e0070f0420300704900a10310b0b85111411489001c2041e4201c11050190b2005000000c3c00002244080480324075131001640c0000c0401d01c40b100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556231357 1250 556230107 556230113
    0x9040b1507060c030e16090506010224150d080904150312030b0a06050408061b040521011401030209041101090b0a030b1912080f07061113090606090e0a0204080304080d1b 75
    0x1074806c1942c0d459800001c3e40d03115000102d1414100302100900144042000c90703400645d030715102d11811000004290032008031062009030860030100910000c2e040c0100a503a103442c0e0408609006910f0302903107100e6903611160b03050019909500040707580c0c2d006070b040e00d00b02058084041c0c41d00e81060361402c2d01c2c04800f11350b40c22001385114014011005019002c210240841d801010020178080f21030070380350700840001121140d0b44660b03600c0c00b40340c2002080307081010742c12650005c10170011540d44d034840300340c601d42e940609810041c1c81840410806908009003001d000076a5001640382c0e1841d0900c142065940750070f81100000400401c00001106543c2c4d0041d80d000e9500d40d155a2208040309003805003200040102d030501e052418030001c4a800b03810922080c0c003480c40d203c0e40d20b04010f4115480383c000c010008070003003810320855440505050300803100c090018649503a0301505400c5030419048000240c0240c2000c0f88465031050001c00303001c80c4200d800e285019699 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556232607 1250 556231357 556231393
    0x3061c0f021813150605030a0803010e060d15020318010e0a0b13242913062916080c060f0f013008091003050105030309040b1507060c030e 61
    0x3001660075004244600301e10382c05c4107005000140c2200c9035602c551400884c3c641090241119101c0214006032062401c0c50b03500780d80c40e0704544541102c0039900700907030180d44010141c2d18448200381300e09032306031001d1140241080b082c001030031050384645449001034502504501010741c99924400101d0003c0b00707030340c0d04420138058113000185500d145502a1000d035102154102c00d00711000d038a1146146c2d0122a164202e615919014440980508440250083c048088564101007100c1c02c0c085484c40c0c03c54000000050501820110003034100d8503545040303910800102d00c6c04130382002003144580060b26046034285511f0029009240e9031014881c03020705202054403102c441943c5211f201c00003a04605445402003e410000990b5000c0081309000d94940000c8000e528400d1180c2416150014003662508608034100000741881d07103e42c03a80004000c02080013404e07000c0c02010100e2180c0408a0101402540601103e0640b406054107410104058400395015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556233857 1250 556232607 556232641
    0x10c020c190501031e0911010e03012d14090c100504140f0a080f06070f03020a0e041d0307053712050f16020a06020c011403061c0f0218 60
    0x3840d0018840d800c4410742407500301c0c1701d9a544112441c1c000600140065921446600d400a0701d40ba445070308484140341c2216008250140341d01c4001c081c4401811410112902560b0f5403040410b20460a100712102003005440c0411140d00030106232107941403d6501b41488652814501c0c102490711500d0001d07994151921445910b020119840564500c0440c1d4042d069180898418502070203103180d440c002590340f4000f00d00e0001d07900c20428440c0c000c54510060996424400c0100c14040c04040d000c1d10b4107580c00f035a411a807900030070f41d0800140054501400040c031844201c041c11f6003804450900086075058000c01d03945141014408031030540c0d6100f034841c1240c11030100c0807180c40c0640000207200e00c2001841152262402c0400c1290342e000f154107484543d9502d609a0340e0b108513410382c50100e03040d00c421a000c00704400155504c01000b0f45880c1124085c0001042c0300031910300f0272900078001d514148150308040790110080c0301002001502814180c0c0c40c200c00d1880 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556235107 1250 556233857 556233859
    0x1c0801050928180f0f02010e15040b0903030c032a12090105030403020709050c0d050c03090c0d0501150e01150c020f21030403050a031404060c080a0c0c08010c020c1905 74
    0x1c0300c480460f010b10007002c96802c80c2e0896444000222186010702ca00c0d01801e9042c0d000402640c102200381c81c1c000005103c0c80d00c0c6030891740c50039240c005400c1c11a0486030806525010a0040030b036141410f100a001c0307207000e10740800390f10302e010104000c0488039001e60415580000c200b85036100c1000c04407440c18400342030240d00c0b5601d84c5000c07441c0070b003d5005661120b08110503c01c0d00c4a032507020b003000030040801031202e595040e030151118041141c99200c240e0016090007850f04201601030002400740002251403609e100c80d52104018a070310103004080700200421006541800d4144d1024591902c1454045103400199400300030100b0280705504841007060009441c0343d440814070b5681c3c09a0703840d591b0300d007860b41c3c440140d00c5003680489e048100c840e4407007800c0403c8905503602610394481b20540b176281c0d641203400401d114003d2080048616010403250714013040240700400002c208070012190003030601c052455030600403001300651640c00c800640f9544240e0f40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556236357 1250 556235107 556235111
    0x6050a020d030f02160506090d2a020a0803030c0306040e0a11041a040f1d0a0f241503030e041e020f07140109020301150305030d0b01021c0801050928 66
    0xf10400190300a10428a10220b00c44010040c8802c020022415503c50144074090750311141140209440710000c0150741480c41418201d5980c410148040803217105001034000c640c00390710340c03100078070b07607401911400e80d0711b2408800c1103010b103014000c2c540c035007041c1ca0103402c09601c10356480040f5000318003003c0c861503c640034030301d107002c00d01c07201c0a000000410611940381005020802015441c98400c40c41c00380206200442c503002400c83c00300d60b07018450302d03290752160b00d50354010303d00400d03121070780329090407105180481c901038120161140030950b0031240c510b14028051150440e4200d009a05000320701500a01c50032403410150815076016035550350300740b8100c0091040020041c0b0580070788501c000410350542c400c16104d031080d0000c20240c2180c0c1c01e06145200703e8071004009078010010240c7c006c03102d0b040f078810400180110b5a5564807150301208441d00054a040010b400d040104158070f00508141d030444510010021031700c00c9003100500d48400c4541c0340041d16 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556237607 1250 556236357 556236371
    0x6040b01030f0903030f0b0904020108131505040803070201140c090d0609020303131706041e0c0305100c02060f0112140a06181a060f040e0304050618010906050a020d03 74
    0xa40282c01c0540380e00400031003044141102d15003d40141001c01d107410a4529128100c40b040c100364004500540c0c05844084103951001c110824803441c0d03200403030703130415188003096901ca1513005050080b4454000940c883c03910040c02400c44210400c0880300500300024440d6214417001150382001094030070125480290a0502c054102c0344402501440002000041c4400e010071100558100d000d14445542c10301c3c070312950324801602d02621440c010300a0100196038040c141c2c400c280304940c050105035903034854a0405410b02c2e611000c413515254120b0800d941800a00d900401001c140715448d410036031040740000001c0001820903007115112a45018100001101140e00003000d210060600034042c0c12000078840840307903401c41050214200e9280c03e01d20b03208070300103040380c60541074240420015000c401c281c0036050108000218081c1c44407070061500c0751210401001088c1044001080d40c590b951104007000010b20051200da680031418501c0c0d4451850046046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556238857 1250 556237607 556237609
    0x501050a02161212020c010806040b0409020d060b010e120a260706021810120c030f050a0e0c0a12060203151201061509050306040f06090b010303020105060f04060e06040b 75
    0x10000840a01d440300030014400034141c0d464000c1c40c0700540c410042c4104d8210380d090b050340c0d5044d074030710002d01064449001a80a04003944281c0a102e00140080340d55800c80d004102807440880d41a28425120708001c0e0503542c20418a4448640a441e01040160302d01502d0342c4400d20b403400201908180a0140540f50120130608121107110300526030b104032500d0200c009511000f80342003400500c410070080d5203041c0d11188000c20300c07901c442412540a005103001031250142c84000c1c50780c0c0700310b0842003c41c0c41c4201e92041c102c60600190213401d46610078509401c407001c0302e201d5489040144545601c8040e9800260780c4214050b817640c441500d10700074103184c59441d61300405000d079a420000f805412100480312002c2c017602d909041100111507200c414000c950300b5a01003400b1600048040e440030b00250f010f07207000943c4500c2c40e1350f034440f00740081c0c0c8160010303915841401000d203040c00c59451607040c211001c00c5810f103001c0400f140c824005190500c60350340c3e40104401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556240107 1250 556238857 556238863
    0x601030f0507170a06110901050307120e24060f010f0c030c12030c080604051e1527060f090a05090a0203100617070501080c0d1e09110102160501050a02 67
    0x9060780c43c0026a60401c00180d5955500380c034031042d2421410034120510030303c103100403100f181c48182d44031461a51808002c0c2c1d1913103002e150301d02c581030707582d014124101418004e81451010203110080c41908918100c40c00d01009001d840c420303113007401d86000f240c1e000b40a110503100d81c0d041807a0703405070300c1c1810b8403007100d0002d025040c40d240640f4500d005506038070241c507064260300c41440e0354070340000b48012100100c6040c5441039002c001e5001a0421004541e40054003245100d00c1025280c0410b40b0b100d000900c41c545920003c12101c40505603209145e030001c0d09440d604110160f00001515a030f02c0a0001d0b4010f0f80c0e25004030f506d2110502c001c80689030060100c0720f100c44401c44070802001c1a200300e028000850f9241c00c05c660b800b01d000d2003180d40c141c0d00c0802c2034807041b45003080e945c050200c6001445d580d914a0180700409000c0f50f9410541040c0040c3c0d10a0342e0812078101c0a51a0006046401c80401c8800480342c1340c0d01d0806550080c41d00c2c0351294206681070b49 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556241357 1250 556240107 556240109
    0x1d01152114060c0c060f04030206190b030d03020910020a0c0515090409110102120301081b010203131404060902120703020901052206020c030a0b011413021c110c0601030f0507 77
    0x1c401c1c001d400410903604140d00042c0040c40074041210525607807289914145c050039200140140c201c1c101040c5008419031038025610340c0714400003420012080024075102c3c0002c0c510380401d40120700440c0b1450700d0102840c900c02c0900241218408903070b60401d02c02e086024540c800c0440c500c02c168200c5002c810381e0b044000c00740080005050794101000c211004815582c010300c07034800300c42010107000c015207040350220802002e41111280800d910012201080d90443c8024410442c00151400240009001c0f015402d0700d044d204c00c00380810340ba45500020f201c607004006103c00c62094804032030f4030005a2600680702c14080780102c0d91031080114020000010001400e111485510104100e49076502154900c018642c141a2504420103011345000300c0180100700f180100300f80d00e1001803005000c1180b068000c3c1e4580704030381240c046c02180b00b6030504081c032040100c5c070605085009031646241020b540c010695901d400500000b0044c0032920502e02c00c000040102c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556242607 1250 556241357 556241393
    0x5090f1306020a1b0c290f0a021c030509010c05070201020a060e0c040e07091d03040e1b0d021803120f090a4b061b05011d011521 57
    0x100800900b80702001c0c2e45d15000b80b40389611042d00c0d6103206a09031000c20f0f032428040520700c0c1468403050401880e42c00c00c0b9911425405050b1602c001d0b40043c8a00ba100200562000111030505428450071608080385120620004101000150ba000600724030314684c05400815108402c000f802e0600c0c0c0d040368003d0300141042c2c0041ca542001107015015201121020042c100646540710901e8660034900c45068204002c10b002200c101010b00c0c0d4480b0049406040e26a18a039549400d40d2140d00d07072213071056020aa05180100f4614254804032013100149824405124251b40c140311f0846c0085034502d00041d80071607509e032022118010640013203c120140c1000034586880c01048003401502c039241c00d43c0da40200d42030203030b40d0041e44801d10134081d030ba4140340c01600c0781c000340f022480100c0c003401e0907c000600e00b4000c6500c02d44182d0402900c0c200345100c0c2d6402d42d000d44040303043e0380d20025070512401c503003402d45c071104e00c80806400a4024407814001e0160f001c02101ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556243857 1250 556242607 556242647
    0x306051005120a0203010b030c030403030b09100503060907062001061e18020721030e060a0b13060305030f0a090e01060306030c0b03090d050c0102130f05090f1306020a 74
    0xd100c065402001600c80030480700084105580d400300410201e11013401501c00303446051010414a44100d0301556100d4401c1c18001101d000c07140000d45e402c031301159044c1d003043da01360080c040e504040c0902a001034400008007806424450007410000700412006950a824655125082002d40140000300408000300c200c1c10401d0302c0b01900341055000740720030400904100108406544216511542c0004e8003d0310075072001c07442990341c0c0c03500380350360100b54a8480801c2000818800300c0e019004540300041e0242414040c401041e090021a01c9400d1400c001000860804400c50b80d40c840b4070510943c2c0c3d03107400c1c0c44c15140c40d012504405602058000085030312074050740b110f01504c1c05088111151070382c42e5032460180c40200d0300d12480d6040452151110b600802c040c091211480d0005402d01c1240e020130220080e541d40030280c0020b4007a4200880d06040e1460360b00070160345507880703203440c00f400c406041c65014003001308456400900d512312140701d20003004c1c03001d0f540106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556245107 1250 556243857 556243879
    0x609020a08061905190e090703110d06090822080a031b0309080f01021324140f0a02030304110301020c061302010c06051501031a0f060915040b0a020c010f0e0d03030605 74
    0x45e4610b4461600405009080b01801b281e6803490010f02602240c0d07212200442041c1c10a0900101c000c1410044510946aa42c03440000c2d2040700a00100300c0c0310340b44443d01c00050302020804040d903030701c1220f040d0042a00389010a07030201c41140d1100801c0d021003540c0903540b60884420710691301000c824041e4000028450106400501a0702030001110720b5035610b4541c00002d21115030400c400401408140100d0a070244080e42c00c5680314030b40f01401d1507840901c0000a5100c0b25601006130000810802008014600b007074140006400840c01c241010040f02d1703840307030046c000c540303805008201401160702c00d0110750542e0368041d4040c0501e0401e00c1c6a60010b040740c00407140801d0030034070f550322880300106518002540c0140b108014a03083e0f0b003404201c0d0b100c001c4030340e004120440024144c0001e000200001d0103040c04290365600d000300002d041088914a0604021404c0c10080b50280e000020f10611501218040300c0505546010303001404250300c42d03508041c040003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556246357 1250 556245107 556245139
    0x22101020a0c050111160b0a0f1e05100305280f35032214030403170f030f06010c12180f0b0a1b08030f0a0609020a08061905 55
    0x9551040751040f0001c0c09440319407500b204980c0a14082a05140b81c1501c002c404101d1001115810880d48880000e41c00701004800b01070f01c0380041c01d0310903034100c0107101d00c5c90001403052588c04074924030001d855509584c0c602d88c8418000403106170b0456005030041e071b400e4515800c01405075202014400346007541c0341c810303c030807403628200f0440c01d4a1f20385440d0f000f03400c5420026180f50181c01d00c3c9035980b0303202100e15098200c0442d075403014205500303100240a004050860104c080001d645942c40d502d41403951081e00490010300070030610081e550f4540300f10607207070495280c45000f03a181d0744601c01211090a0a000a8044046400b800c06442e0300400010400c240d04100d90a00e0794980000341103a095a205021010104020514003144110035003c0800c2d802a00001403080c2e507111148140c00968803c150801c2050a100308500c481c4102d4008045c21101541445000c01d400f500441004007c28010f1000600304080f4030890f030303540806048000e0610011000b050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556247607 1250 556246357 556246367
    0x52b0e0d0615092c0a1101260a02191e0f1e03060608060307050306011701020c0d121409061503030f04180f050c070813090c020109050105060a060903022101020a 71
    0x105100349054020b0f110805024130114041140ba0340000d100c610790280c00004440c0070f401101e41e4048090035810b0b001c291302038845014040c0701c8180740581c4903108001b6a20500b42070300200020301c4601040c202070248200c1900c410300e82182002050480120b030150b400c214000102a000c5d000c09011090307041d019030000003683c540351b560328025541c0340180f5556004500415605034000700041002c2da4040c5040d11502000d000094200041e12601a01c0c18811710340c880046410b1072a1303034140160307603c55001032000421aa1520341442601242c4843c030107022071600c1103281c440c03c041500c08004030f0b041c54070204602a40c0d1342d0b03a007411240e0480c185c889110141e08140741c2c0303014a811400382500980070401701c00c0c9010090f0791441c110f0f6018004411110040404c005013402c854481c904080040e40c0000c00c05007000c1c0303056821943c3c0101403610641c07000780103021880c4e0004401c400c1d40e505498513140d500103500608580390b2400c140400a40c00020b05541740341d409 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556248857 1250 556247607 556247651
    0x60c05030405010b0405190203090c0307060906020609150c0a020717010c140c0c0d0303230103031106012111030a0c030203070b1c020d09052b0e0d061509 68
    0x80008004903c0315504005c01d031103007507071200084c0d40c920641031110040c650095030400c10281c00c23110001c1020000c641402c980358400c4011503000d02c000c000f1141c0500c00c135075210040b44060032001100551140d000000a40310b5068850045034401134140200180e502a1681c40462445d01402d8004640600054213001e40020420109000c445d4002002c1e14003030030080b0050301c4802d42500500001110070a03041d400c244e2185410b21019609642d003c000341c1c9400308890715903046003000b03440b160b07104540720740c564406c00c01008078407100d001041c005040400141c002032003604101812034030b0001c0b000e81c14007462482c1c004000c8441c0e11002142d2013034040d910300c03680d2085510520300802c0c6140100707465503000410b8000e110f5006140c20030920000060134240c1d07441d10382c609001d40200d101c030480503201c181413221010a045092216914103a00110302034801b0560340c2c50f840a008200302c1d00d4401c04a4040203495450f80900140081001090b0201c480040c1074224 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556250107 1250 556248857 556248863
    0x20c0a030c06030c05041a210412080c121f24030b060307020307030e1305090c1906120f14070207030c05040c050306090903041e050906010c0f1b03060c050304 70
    0x180200840542d4003c809503000c0320000d50b0002c40c09460107108187c00c0c0e000141c41d188000451000000c0b0444251455000314009e0740d481c40200344c110800382c03c1c200d002c1c0c40f01450781c10500201c0d000175480607034650b002c2c07801c414107074407a5140740100c20b00550f40c0c1c01c61500c5030a03c44829519030300c860a680c10f911038566045c024884001c060208030311081d100200160410803118000c05d01491424400c0c00c0041d0101420031039200d41901103803c02c0d29104d071a60080c002404451801240781c2d107d980c19910384505103032401c0c101400c002200c403c0718a1946d202c0190001d4218541c0c040340ca03030800f00c400402140761591009480b0b4026000480d030360b00b40c031680803030346003424454484a0350198039054a9511010308002070142d0080810040707100411010504074010300c1051900b41050003840d85071410081008031581004000074104800c520086000c104100c100c030103102e40083c40000007a081c00e0304c0d0681a011a0806481d01e0b0600090118030342c1d20800031403042c0c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556251357 1250 556250107 556250111
    0x3190e0a1109070302070c06030915021c150605070b0a02160b160815040213050a23031903050304030c0206032d2809060f02071709030319020c0a030c0603 68
    0x1403030a0f81035003280610440a0440d488200e418442c150007648400c420a004041c880c844007a10035640059038811807009560140309481c1c50b01d01c01050240072050144426040709103403c200c40206070740504031303000d00203464080c0410010f442603412580420f4110008039110f00160920007074188068601001c1d407410810b001d444540b04210031802041d8100840c4081c0c3c0a0408001c065080b1844251400020505c00100e559914a404000b002005000d2052a079902d4114902c10820000725000e43c11070242c280c10354404061014030fa50345428080c0d00c949650508032000840518001c4d00b10300000140401000003019681d035601208508101050203c100040d05003419114120201d0a10041c01c04901000030000c907996484400000c498541d91a0740c425221103030759400c440c5900103010400d200d00007001420281000d109540341401c5800400d5680c440d0303040d01241301a0005c00c01260032310070321003c104a00020300c2c07101c4003a20b80c00c01f6010300d0020f22901c40824 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556252607 1250 556251357 556251361
    0x40b040b0f0402011b0302010e16090b0405060612130503040801051006110c090a0e0102030c090406050114030a1d0a0b0901060515190908030705031e090603190e0a1109 74
    0x101000107140316a506079104019016000041914401080c17021000e55480d0a00050f09007030821040602c0351103501d0b8078904c0d900c2c0c039a0100444081c10941e6005500380420001071340c07106011039603e40174070218544503940d04d8611f03000c00e103464500103100d400009400a95031605410640c040c011558515880c2c1d5614202502c20407119169084d89410a81c40c1040f9440c00c3c160456001068100208420306000c9402e401c80c1d00448654203403460204103500030303007410f2080340c0c0a41021b0901e440c0a0406012080641c08010444000d080d221440c050f903100080c10703c004d4001080b0121000c1001c1e515024011003c12994203440d50300e06100001c3d54a828024154003a070170349500c03483d0030201e90002085148100c900c0050003080b0900080741c800c104000c00e861b80c081c0c40a5501c88950852003040548a01c000240410080c04913008590300d101c2203980205148040c00d12200c4510b4603030024180c06900c00d00f40780112940031061201e01d84001c42c01d010700b220500100c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556253857 1250 556252607 556252621
    0xe0a320f01060f0806060c070303050409150503070909030c02090a231506030a06150807030f051b0c0709060f05030f010c2a0605010b0c0c01020a020108070e18040b040b 74
    0xca1424030488000500c0360241c01115030085a0154000780050170035450054482c011074503100403a88101c002580c0014104240e101501c900d5003000e80805441603194034200009544190034041c1558490341d0b80c2c1070204140c02410310300f68081d405000b0412615110072100c00801a0400d650100300c00f60060110003103400400b184568038a158524074401c65505000d0300d500001d010340440b41e551180400e01100010b040d10001450780d03030310306103460030321801001d4462401020b04030a052006100d45a01c0c01a1848013483d200c1d07821948809421045603e000c100c2d030700c6140700702d1a2035404203803124909100b105481d0f041c0c080345c00200b000d400302800c0720307100300c40d540010340035610462007400304020b480c04040007000103000c41c48450700c65900f2903800380e100c442480c80c001881044800c0600c4020f02c0c5103800d0001d00006055500083c00000c40200800104140520350400590f100304c0074465441800c1c140050710700d4145042a1500d1090383c09640740b400890015040b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556255107 1250 556253857 556253881
    0x140411040507081b13030f03171513150611070509130209040201022e0c2c060403080c0a020312190503060f060304030e01080601050a05040e0a32 64
    0x40200c0e5445100950751100c000c26800c00100041d00003800c10041c0d1030b00c0d05d030307030344448400307103010300c41144030003005207800340003643c0e0f10034030728443d507181406c0104907140711140c54441041580d41e040340901481030440209030100500201c100482e001250642d030142251800c015044216280304e6143c4e401c0260204040340d02540c0100c51140c02e10043c10508407840e00148180111003003140203070980710000850300301100243c3c3d0340c660403003540314241c020118035140d941004c00d410700410780700101364ae20010310026100b0410014001941382c203002c0b40c006507005010191208002142151208505041030b4031038464140806510069181222005104c0d07092050071542d600304150b40a4000400c0c40f98410040000c0700340c5502c40900444c400c80c1702e69240c440c0552b144001400740880542400e0410009000c581a4039412604807400d0718020f4a1b01d00c3c4680d80d040c140000703030040302c03048034055603801702602061500383c071021280e004003440041240e0380c404070054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556256357 1250 556255107 556255111
    0x120b1e030f010e0304031511030711060a0605100305060f12030d0507210b1809010213090506010c0b10050607081b0118080d0e0615010e03010605031507121404110405 73
    0xc3d143c004001c10070004d2201000381032510390060012810380091090501c2e2904215400008030301c3d100390702444141706118899004500340c2d0108051814040851580c1203000241d100b031658a401083c045c0d5180784045404600007800b40100f084c490680c503449421100140100c20300b02030204582e0f60060712040322071008118202421b050400d404030192043c09112500140c4c3d50008602c03034a0317080750a9100d81c80c480d0016a48001d40615800030702890744c801000303207142c0414841941e900944170300101340c12884601d016114010b00c0352804081c1e43c81250b1000002501c0405c00c00c203100646055517446581c1441c82d20000001e509a683c101024440d00c101e4004100018800402501041d00d09100008020200e0380295282c5001641c001c0044a8403062844041d0380c80b1035103c0c890842500284469440c200c0440e0396034032407500500d010113107036002528151050700080c1516581140500c85101d9040ca15045140c0075a401d0f00c1d00840301903a031030103043c140a464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556257607 1250 556256357 556256381
    0x15090c0307052b0c180603021e0a0b09040f0203040c03030206070e09220c030804090b0d0c06030e0f0a030c0b07021c0518030a0c21030807120b1e030f01 67
    0x10b5001d504569071140e9150070b1021200304c0b1604901207103e0500c002d900062104820002400d00e04500411000c84602e05002a4000040b0030303410307054541c400c040b81103421000c3c019032214404c0e40000c010b00951a0a4990300d84080304210501c040d88040c1011207000c1e8090300c403592550380c01282d451801ea620f20390030103000408100081d10240e0b918480f0b2410311340b040c0311041e0075139844001c4a42540150390804c000b00c2c051003050141c0c81907013030041040300d04032440020f6940f200d0a90700b8a01c1440d090654480c1844850b007400d20040c2e69035104903041c2d60f9048201c0c6000390064134455425076000480c840002d01040c0000b0340800b80350108448500068203c9204540c154030800c0d14071b40e17680c0c250081091a4070f04000240ea0544503884103000345060000d1040340c1c500d0035540000040b880803055000c65040241c1030b420010a14100f141407845000403005084028150740c0c21050004041c0b8a810095409035140d05044094a4445001c40d413103c3c240c542c00b240034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556258857 1250 556257607 556257649
    0x108040506071815090608150f04021e030405100c08090613030e130e1b01120b0d02060d0903080703020301080c0105030a0905030f04140114030a05040515090c030705 73
    0x100b100c4901644a482c031100d5a00c4202c00015200c4510300340c051210a050710108029a005020ba0750b049050140e11682110000b01a58111800600b00c923400c07404050203507178002406111145040380f44544a0706405440b50b903030400d458820340d1440c07040a403005442c90006100c4005209884c0d9900a0000c000107144580764220601c00001c1100ca044040c00305241020405449003c0b440751840328031200040c00c0f40b890403c56041940c1028142000b031180f02c1829042c0ea0400100004000740e00d800103106207941001c6010280d2200c00070358007690206a01405520135005020454402d55134400aa2220711003941680001c2c050480ca982044945090380e502c0342d0083c5038072400500010038105010748819046500c08540041c0e100c20000d02802103c2c0f9142ca1110009402e10308900741c005481c000402c030703000c080c11040c0d0b0142c40360049002c2c024100030004400b08007000000c41800c00b8000c003540c9041c3d05001600900030800001480d2400d40070a201c800480070760 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556260107 1250 556258857 556258861
    0x3120e0109030602030a14100e010b130e1f0b0702130b06040902070204021603090e16080c090420090109170a020d02030f0708060a06080d020c060a051204200108040506 74
    0xf840c400b07504020081003040b03607a591540f808262800c8014001c3c007913070b42c6d516000d40c00d00801d0119100705030032180c0d01c418100004205039510301c034002c00715400c405802c0c840c0c1e2a860040506001090514504450f0141d40443c00c034030000004c1c04c46503c2141e01c5014060441001003c2d280c6e400780080c0e000c3e900740b0003040400c0b819001009950b00c0240010f282100901080819686c08001038000440340c400a02180000a2080d80c0000d26121450072451201800900b00207004052904000000c6092052a21a6044410000c0d11030b28100c0c0d20048100f44064a0f0700700f4020700e0300144c03581e800010407a61144000450ac4880009070030820170702d800b8415a0380c02d50a0072609486400002808051700340189009405080b001e030040f410200c1c402815150203820402036500f0944804030350540000b00c0f090103004c281c2e0758039120480aa415030380340c041c200900f003090541d00e0810080001d00425410700d007045d03400d10584882d40100440d90240c003101c00400950120f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556261357 1250 556260107 556260113
    0x51b09060310050a11030108060601020f2803090b0d0c020105010f08102f03061503090a0308040201051b030903010e0a0b01120809060c010f0c1b0305030c04050d080403120e010903 79
    0x2000b030b4802502d04c80890401c99800528030254400da1242403039400070014040a90f0b814032051140032030032002040d0040d0741d0400d00e41000100c8a50484411210300e025007014000c1200300018105a280329480321a1a0084c40181c106007540c10015480c000001c9249000008820255071a04000340600103004100c80002c4c610304c01010304402e01d640b2a20810306504021484100d406607543d91641490000d00c0b8803104090758452040b1014800c00810040c0005c90806641c0c051904054944442c00142d4040c4a010a240000004030800711031525001004101c145016002003221030160b5442e5525500f0a420081c0017294190040180078041c000404865025159052070514210300150490707110500585840c0d45540401c080303101540306508c0040701d282482084109119603640c000c50812074000c00b4802c003c00400e507892606001c0d01c0c042d090140c002120b44000f41840800350308140310848100c1c44148580300660312481d81216002e0060f110f47c00c40d00d080d84c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556262607 1250 556261357 556261361
    0x9060f0516110a080d020f0c03070507121e0f0804140a0524031503060f07030e0705010203040501032a052701020a060b040f0f240510030203070903050a051b09060310 73
    0x20041c070105c2902404040c4001001d40001c2890880d044011a510340c9140351080c00e00c0141c0e80807500058200e00700c0b10210700c60703900808a40f5003140008103101c021b454007025000c0a404054200d00f00420f000c109500c1000502507114811202011411750724800c110b03002e11680c094281c01e401d40303159401d440485501541c1c001c0c00a1801300d03800e8055001103441c240b8110340d0400c007001c0e2003003403002d1a41c25104e024120010b0402601d141c1e81000000b035034038444d03807041310b04069440070400c0003007660041c068041417031119540340708c2101c1c04000380340c2e42041ea0401031902c0c0e4441410704c91800180c8100c00480706070040c0480c08040e03221607005041d240d8400c1c3d040703a100c040791248ad400074071030981424501e030000107021591000201101820741e40145070050f03409402c0c840c0d9a101d1b840064050142e03c2c025950390741d00e000c101d4410f8400c0d44014214440c0c09a40020000041380040007841c01242e609034214000c030400099800c00e0b121290150030150071402c2015081d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556263857 1250 556262607 556262617
    0x5040e0a12030518060702011a1f0509040f020309060403020d0c03020d05130b0316120b0904060e010b030d030f0c0f0c0f03020708070306020c210f0306010309060f0516110a08 77
    0x40d9070740c10b071300d000c40c540b0702d410f1140456400e40140d554081d00e07174100b40342c0c3c00e4205002d10181c949503507560240312420481000d200c80c090a120000c140078200b60b80307070f80001c000119805002c0d5201c1c1000c0c0742040d607400d4180c2d000c80c00340c00f0744d44601501c2c80c4500845880d00d81c1607401014051045902694603501c0000390010b104c40c00000420306480050065000740c074140008030803030b040c01d85e00412101e990841071001c1c2d0704040003100c0c55a81c2c242e80d10b030040d4000d400028102c405030301c06030050086c40c00300e84c0c15000c0c51b107030f080d0309130b4140e07102911015640b0000d22444d144502e0880314038203000000380102d1200d00d80f9130302040c40390500f550345c00c0c40780c0109c0b44400d4072441001c0c6408420303070048510303075000101c46000140612081100054440101040101c0030f518401c20340a09452174400520100026415038440d4002a041680180b020014000b4202c0c102025110445084910398060304484464900c623001c00007440600f01c0143c600300019a031400c80592003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556265107 1250 556263857 556263871
    0x2d0e0712030201110a18170d030b0301060510120f1512330f05090304030210020c0603010f241e17010b0a1b03050f0d200405040e0a120305 61
    0x19840c2c1130590481c14000900144409840d00d0042c0000041c44500e000e10a4005038042c65817444000e00f51500060300c2d04e40203100c0d0401045480300400820f0040200e94071142d0301c03810310101e0703076007864000703500ca010ba20030170200f48040301a0080340000c1d2400244104000d180ba1030013000f0034103002c50409035940c4200c8052400180a06501c1106400e8031650038040840040061690186115020003011500c40c2408a031074150320a5449004521010b030060170844c184038201e034800d0245500101d03000380455282d5842c2c840d81031414140b0b00030301c0700d0055000351500110514040003600400e45070345024005c04a01c205038000d5003080052000d020381100800030400f086e0601c18080c001490f072294485892321b90007824506d00c00d2106a003e48181c5160740440d0f40441203c1200c141407420340e60fa000c03003214190040c2601903038419042c8a10443c00c0f0359a9078400204122101103405001c81c40021911076124a42d40c2001403020544690a41010f40260041d580c0142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556266357 1250 556265107 556265111
    0x3060105070201180e06030114100b0a050408060f01140f03060109020f0706090f060b0d1109150316150e0109090e0a080c010917040b030f09010f2d0e0712030201 71
    0xa5004e05500b0030041e980c00412081701001c00300301c00790500344070300004810b1502400c61141011812443e2041e90b074000c0642208001840c801040c0c000d4085500600c03401e42218024a002d008a48203007400f0300501d6412542c80000c60300500d40032040441010b401409031546901e0400d503036009607c41c861030110004203110200128034a8420302180034040d22442070303144903c0c94050102d500c07002440348520501c010101c04180c01890900050409590b4034880341c4030241c1d680105450141d00ca64540b00310701081180203038030507216048400700618038180002495044e20710f440440b08260002e0612082000a42c2c6aa004029081054426030300b1414650311503c81c0f07940074580301c40300c0d03031344a40c8031500f08450b00310084456220070184508290606500c2140781c400501038009012054000c17441e600e000394400d8104516543c0304009016420149881180205082c400e0444440d40c1e0070410403a90300410f03404424200c060700c192800c059200301d0001680109800311340d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556267607 1250 556266357 556266377
    0xc0501060b0c010930140d0c020a02040e0c030a150209042306060f0306060d06080f0106030b010e130305031e1302031b010813020612071106160503060105070201 71
    0x15181030003000b00000080010940e01c0c10740c200303c288001810340b404444609200f40590a00303400000b804200518a41000b40703003001601030055004020040c0c0c00d00d8945aa44010a038000648441180c400d903030038044502001d00729621000c8011580781c168018015031000a40701901c00b4000e034240000040c240030b81c080108048507440c8009580c111041030007503800c50842074413180d110b101101c5151512030824904585e1340006403e0768081c030008070b002441610160030100151442e1011101e03000c44d07400314035000e000284000d07501040100004208401031420044c42000c16401140c000d041990301220503500043c200b0485106801540e01604283c10702c60f40601e00d01c040034401140316004050034543c2c0547d43c10100112100d55035030f40d0b6007003114180c0c00b152611100003010910f002151403442400e0714a008040c40008001b91542c1101c503410421401c90129280c82d81d13905a0071500c20704a14186000c01d0040c800035900750300c118010481544103146c002040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556268857 1250 556267607 556267619
    0x2010e010f060503160b0a1b15022106060304121e0905040606030203060d020402030a09051603030906180e0712020706060801112107032a08100b03070c050106 70
    0x441a1007401c405807526007200704840d10b01000400318520341091216101c501d0048041c8140c030403c00404188002e4042e040c118800d0780340c21002564200c03208200728100c07a61001d0007980718003800d1920000701090708164a140c2c104281c400d06c0d01034181440c684454643c0c00002605102d01020803456200112101d140c0718503041403003086807180e8085500b45010442956056008501090b10610030095140d4600c1404241c0300d4054038016070301e031640301050000d4001580054000e1040d40b00003a0a00044140e1000701c80c003c0c0d4035003140644501c82112465a104120780ea008000c4109203e202c4004c1c20046e001842420b1074a0b074201c0e904004802e03a001a0410740740541d603408104103505080c0200e02d001c4540c1003420740b408044844140c101d404050043c90110801300c00200c8540c060b43c40030703408500340700a030100000c004413a101451036a5204100046a80c0e0209122000009100d07090315049801035086558140085984410990060b40d8942d00c07090000b1b14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556270107 1250 556268857 556268861
    0x30d05180706080105030d03020c06070e010201060f1d07090b0f090d1505071d011704112d10050909040f0c1401030e0a0f08300a14010807140102010e01 67
    0x2c00e51600c42080540c5014105800c01c620041850103050041200058101d4046202d0b80cac42140f0b414201c81c022240301c0103e004003140d401c046a40d140c2d03414041800780e550106040e061400040c4421180d5071090111766455003031144c0d200c420020b100d035070b040f1003c100180c28901005082600ca540c1d4649030a0025010041c1001c05540d48109000d040e43d03004594004042c2d403107000b1001c040260000030011161400507a19412101d0041001c00a03141071000d511380c1c008111903c10702a01d1401004140440a400e94a03426002c0401c5241000031304a41191300e9501e4041c1800c40c10380034084640d10040c0203c50210005001100281c1000d134500c5c05048800288240f9400030320000d0103c0d842060010100d85c88420060001042041c0403911560701c00381e116240e070f11014045001c640e0551100e800b82d007101080e0b9404601a01080d4440d1b05d0b4002c00b400b00c01410745001200500a000f4202182c21441e41800007183d00e0b810113070303140410f100004d0100422202142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556271357 1250 556270107 556270109
    0x61d0901090e15060603070c03030f0c020c3109032606120303060a030303150314030909070c020904020f031e24160f05090d0308010306110903030d051807 68
    0x14500365104481e0405440400000c00580c0f041c048140c1e072070800754000b80302400020503c10400203108107603020148070b600550003041e040725040c4403490a038400a9180e004645200f4002c440440f07180203419100c00300c1059418032a0350440c0301241c035040090140440308416810712044006461000348104403502c41e041d50f80920007814200b00080011074545048200401d07842401400166a90100781c1401c495050072700081c01c880003584c620001020b68006006892100703040c07440514041300410448904807000d101a0f601e500c0e0aa9149203080400f07504800200000760041c180b020402c507880400804407004a00a1102c42e0705803500824841c00300d4114000105c10b54000d0710f00c02c0e0001d00b28402802480c5410080e0350810400710a801007003082964850f00f9188c0214211a1200005844000008014100034084035400e210446100b484c00e041d00c0940c034289403c0d5520b05000038051403500e2580e41c0035601500c405081d1408004e0210080d198a40c0d00b00281c1d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556272607 1250 556271357 556271369
    0x30703050108010b0604050108061905060307090338040c0b1303051506011715210c100e0103050c04080715080708060a03480b090307061d0901 63
    0x12800758105040b4a00b550520704685006400620060002d030380c003c50780c00e83c05001034514620980100c18840c0805d02c07640c1c8696044040001480119070340208401c056a015080140128014200da030f40346580c03c402107941811103102c0b6283d901d004240207500300d03008080c1000503944810340c0210943c81100b10400c54032510700d040003004828080c81d00385c0c2e0711105182d0b0711341c545a000603240441c29002080207604090003d82e940c4091480c000301e070340300505544141414844a018a80e041c0a202c94840c0b18900449001d8607000c20003200e5541e26503a450312a92942d0019806040007803c600e0824606000c00b2848a02c100010741c0144090072440e42c210280c10030241807008003414400c1000301042c20003515031076506540c000c07654001c024000010400509404c44c00c102c054841c0d80b6900501d408a12074202025901c0c0302d46090700b07030421666611702c100d03201c2c41402032480d010303000b80c1802c1061078090280810080c1d83c40300c014961190300d800045031514241c00c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556273857 1250 556272607 556272611
    0x80d0e0102030c12150f13060b0d0605040e06161d04020c060f0a0501030f0b040305070c030b06120601031a0709030807052b08061003090b0115180b03010b09060708030703 75
    0x20132400c60031101103420842d030b04100d01d900000c03a401314481707002c142c100390f0185403a00746010307450030143c0c00140102011003e540c1c540c096030344024068205071242c24031543c1007031413074000c1c2e06010030b4140c000c079015041440400301c0b01c101a1450440385030b581d603146120840040c116110b900003000742d80e20010280c07030140ba082a02d0012040050008040e02e0303d030000520010704404544401660000140c0906a03628035046500d07206008004040504201001003004034a90f542c40c0100000c481101c8501d90303061450303a860009210142100c24180820382c2400383c0782d0440d0307401c00c80138030742140400d031261103204242d40000e104844a074029401005503821a030a070070b0807240400a040750413050f024000b03104a43c058000ca21070000d524080320060702a40c060440c40d58011103001d100d42c0d49194643e110000b600e0b103223010400e414100d00075408296441015103803070b004258116408d080381014242c0107441510b4012208001c40004540c60740c02452180510b5030340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556275107 1250 556273857 556273867
    0x1020c0a0f06030608070f03030309080708070b1909150507020304050a060e0910060836241b0c0a0c080102090a06021c030f06030c0602061807030807080d0e0102030c 73
    0x107040310100d1740003441513040a50203000e0324952580341011640c140c900400d4400f81401e00c0e5840e031255520052403005c001520508016004035018440c2d003ca1101089211040355203005907000204000d144040840c041107441d0032070703070005070000d40c03a1040b6800c26407104c0100745185929000a800724500740001c00c00307403800c038034425401a006148000c806180c10704c00382c1034400240c0902d4866404c1c1200c0041c560210746828801100004901d84242d1501005034070790118451000c0b02d804a206040d040382c40e4020814001c8c100440d68404d0030f01c0d031940d0291960450210702c0c11600840f6150004034040c517003040058018040010fa454038014108900e5401c20380c440010742d08481812903030060040032202d02c3c070440f42400b1880100c0c801c0180028500e5410003490f280c43c04c07802040e0940e0000d0a1031141c0c581080903807025007418401543e03429648001031034501c0c00c10450000031100c03009410b1005ccd80305c40100340381c040b10390083d003039030411102c0d9400f203407000c51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556276357 1250 556275107 556275119
    0xe040e121c0b030a150c0c0c060c03091406031b120a050601080603160501031104031e03120b060307030e010b0901270b0a1a041a0702040b030102180f01020c0a0f 71
    0x3140c41c0c1460380460040480032a039070b5501140a134225111421155106c0001200074024082440c1031030380014100302c80c7d6200c00d07000e003102042482c1a4005504418040f550b80001611000c20440c024001415651000d11030861070001c034800041345541480110130790310506000c00c0c050585c0c03070000700d100e14100000504a2500602841c0301e503105119940001c0108009503061740c0707080c030303000c10001013129000b42c40d0302c61940003c0004070388d040f844c10b6100454060b8107960b4030980e60b01c406070302c45008070400d65610000503644042c040010035640f60080d800882800d40c0440045685030b200800210b84c000240d0000352407001281c082044040149003a035021b0038410030401025000c031020441200c2c0078041c0103c0d000070060004c1c55020020183c82c02000e2044c0b4540381c0710700c0c081500c403d541240004030700a0307080c20082e10881c9018009da444403150880e14000320031034401003101ea0713000301c400141036028065a09445888140c0410081c00c04041c9500c1c0c0baa00e051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556277607 1250 556276357 556276361
    0x1b1e010c150501151704110307051302250b010b0a090806150111010e060412021e010c03060e07020c0409020f06162a120c0b0301150914010e040e121c 66
    0x158603010030808611740e8114040c24811241c200e501308204002051081002c40c1c42d0451a80150742d000254440440004541c0d4000348081401001c0380711040c610740403800d8006124030b80040c8090078a00060000d11242e6014000401d01c82c40e0087c4620364884000b81071a00c02d58000d8044403c01c1c600324100c6d6001461b541c2c550030590003c2022119010aa60315902e01910080c0074041840119518520805c100e40c8120045c2c220200210518130b1880c3c001e010b54028440440d06107074001036880c2a4407000352042c00c4030340281244410800030070004000c516012a8002d650040181d0300b501d600e00981403009051000441c00782190915012005a4902013100400503070131400c7c100701d100360840115440000c1c411408011464008041d01403504100d200c41004000062132a900c00243d80a0709415142c03182c0050b10b03940200c0ba10b41d041d010071400300d690140301c1d1015080580c404021541c40000361b6030b1078a55410450f00c0382e8071000c50f15081100f490f950445040041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556278857 1250 556277607 556277639
    0xe0a06050a0f030201030e101407020606010804031b1722230907230306090a0501082d0a06050103021201050112030c02190e07021b1e010c150501 64
    0x200c51444040e450b0504140e00c0b4000c40c08020b04068070791040b003465800410811702c18485180e0300380314550140a8803918603800b01e030707000014400c900100700194014440036000341d030581c0d25081525441648a0315049807440c0841e00e000551124440d0b2500c51006815a0b002401c9841c484082c40c2c400398241f100e9a1f04603940083e034010121810703810a150341c40c07104809480350480ba07a00c2000954203224410050003854017507401d09005010b1140003140f290b08100c5100207951203400e40c1d8811607009004114080e4000700d100308550301030050340e0003079204c5410143d206003c0101000e0601007041001c903007580d04ea00051046242981c8088800034619000300034940c944289a843c04122003400b81c02c0c4180208210b0641d22100070040d4946141068021500c0d03881c81032968140085a403180180600c031040f07800c03d42000300010b07001100611600780a81d01c08411313040b0908204c138060500c09944e514034006030300b030041d903000031728000341c0024190300d000741c401584448 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556280107 1250 556278857 556278859
    0x9260d090b18070b0a080c070b0a050a0f0c020c060c102406080c0301030f0c031202150105010311031b040e07030b03010b0a0e13060e03181203030702030a0807180e0a0605 75
    0x300d103d0a214084003102a02e0050700a8070303001b40140c0340c46059050511031407034080d0420011030b08001c010322941c1c02890280c0d1859104000c04c8031101ea03034004440c450b081d41401600f000031018a070703184c0440641b010024490a45114044000d040c800311002403550a500407a00800f07034070716580b0064044000c01107420074008038a4244110011403205000081c40007094000c61004d01842c003482d140650380c0500c500903c00503c0f5800703955150015100010510749030700119055100303000c0d5555100304554018291b848031b84190940c81313a940d10070407460760140800142503824141c154010101e9480000322407480c41d00303060a4621840b4130324060701c0d002c001042210b0301400708030ba010f030500c2404000d082d9285013050281241c16460040d03440701250300e0140b80241c1e11600d410200807500e44001420540d0355640300d0004681d4180943c1090190754000c0c0e018051595000c81189007400c2405540701d094490228030b9000845d0701d18015081040ba408580b040d1b1014080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 556281357 1250 556280107 556280113
    0x1003020403210c0803040302060f060a05030c0904020d12090815012103091a040f0e09030f280c050c04150504020702040b0904121209260d090b18 64
    0x81103031100c8850306858004a14080ea100c030364148030b58840d90b81800710320361141415039a420300d810000c0d903070343c4c041d0788a1001da885007001c00c91501e40703080c0d10030032583c014020b041048444801c1007205c0800038010f031380080d41000c6090000700080c8854140c000e20b41c03101048a411310120501d13180b8400448a024400e440c014030030903241e9030203900b0143c80c808001c552035030306207800c03508200c1690001c890318604c14910780c8110481000703442030741d00c2c035400c0360282e5a8500c820702c1c45d10010b6410300c099800c03c22001c82880303034540040a04801900710303510100c15001c422031f14034021404400c0001e00c00310510040090038004520110000c80307061148156445500715122118424148216400101d00c421911681c000b95003d480003001e06520380380c64180884070700e0b250808034001074181b044868003d14070b48138040300c85070000041031054884100c00d040c41c251101002081400900001102549078061803020300d114500c0300c24142880e0b46405100c800060f8981c085030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 556282607 1250 556281357 556281359
    0x2060f0a0309231e210408010b010201060311011107080706020604020a060807090611160f210c03120c0501180b0907181104120609020f090c03190f091110030204 71
    0x84000111810412140168060745042e40e0101324500420401000b801070200d000c3d0b2a540d908100150085030403440090102c41c00b560012800ca4449010007400c1d08418000e0f1201da5204020582d041c901001c110f64284d03481d4107030640340c20861b603c01d1005a220b041000114280303800f144000b00800d0504104500f401da45c05032000c0701c98000c2c030b010810459100c0e071110a003045807014010980c80c180044645400040340c0b440080d0280e0383c040300c65100d105102840d0713114480491a0851040c4016a043d030b515942d0511242d2000c0c03040100904401021a90a21400302d155522070000b08400c0c20a141c50340d440b400043c04080190080c400800402c110503000310780d16440217400088040402e002c3d400c0d1402036401003051000c480041104020302036021400c441d0003110310740400c44000040104241081715090189481800450390dc4a0341c2160f121501d1045480441c10302e08500800d41220b81000c0c056079240a01c8410039858104030381d0640e820002494154501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 556283857 1250 556282607 556282673
    0x1c0603080a030c020c0d0515070516031b080301260715030207050717030d0b06070201050d0e1e070918020918070506030103081210180902060f0a0309 66
    0x60080c5441901810f8840311070003e01d070f10900030b25217091030041c010140c807441400c0459075000204856125514100d0104051501a5042e01c030303030800081184400700511ba40c11030b02281507c0c481602403102607001000944004061406088c40235855070344030f00c0440020702c040452040c00740b0310303030003141040c420709591164250402c001c0d4140076944014601c0c00b20300c3d00703166500c8000c041c100c5c01861412000040024600100c3d07810045c008106c1e00400c0105502c2550002401300d0f0081121294082d602e4114481030105581520040c1a00c101200503002c4002d00c0c0c103c0da0b40003a1810b008041c8688142c50307000040d40403060101155a000c25503145000d000c2000035080b0760202c0e0b440c644200010400391401410017a01c0356503034070305a001c40d00070580402c0c1200418000078400150001c0300400c4403009403050f500c580704d0348103950060503102c00603a00b250040000c21580040f250040440040c5541e00080c580c010342400100072660903038402d60040d07001d03051110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 556285107 1250 556283857 556283873
    0x311011404110109062a0602070b1006020c01020d140d0c09080f011404080705031905040e0c0c0a0602220f050103051803090f041806090b0702030403050304090b0a1a1c0603 76
    0x10703038906c46004180d81c0a02c4660349290b0580108010070142c00010071804000b0741d01d5a10b801803480c44e240b10301251712000203984444074507004034010b9100b0744200a00340c1c0320708220486074208845151400c0e1820255a0640e10310080d000082154040208141042001b10703c140910040c0200442c0404604005203050080e1016080d0407000c00c4801c1404400d0040381c0c0b010f030b02100c180089a040c040081e08640051254010f401c4400000590021010342280c0343c05200704040c000c0c44905a641e10b0094102c4481004103400324104c2c09602c0f0f80034001ca20207414000c40c01401c8a01e03040c00181552002030140065425131008090b19032400401d4410030102140c40704a109901008075006011b1400400d08a03100b41500c0b0b01448104d912140e1640d00072124017000755200c040c140d079a4840c6100c02015036004020811581e48182e0052158030301c000d100891190f83e0701020780f0441502c0d810150300d2080050f50800090036502111540030008009028507481c45d00e603054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 556286357 1250 556285107 556285127
    0x1b06081b030c13080303040c03020915011707030b0a03060f0b240307020c040f1d03180111031b060109060f05011403040303060b0a02150a0212060d031101140411010906 74
    0x2035001d0049001e4100006200008015226a40440c2d8882c030745410b01d43c0c2008d090b40700c168022400000800c400307286128003241100d01c1a111105000c00c0c040491050250042451003095500c5a441c000d90380d5240279a030081d0300032000410307450540342207001140d0340c40640620414588464940c9116040b034a02d010050310f4001c1500c9984a003000d07802c04100c0001a0f5110b4074044400364940e81e00e50200140e07042004005d2001402020555070302d104e41c5841e200301da0840740c048013896104100d18420162800300781d07418003030002c0d045880c00d0b0741041200340640050340180b00c1c14045114400c010000345210761311042c40c0c0703c0040c0ca0b4003c03a64a90054440c00800070b01814026003002c2c0c02080303040c41169640d008100020340f80c652803070fa0500c041c82a0004120306142034020b451000c0d025400121650f2690003c00c8583d4281070400c6023400700c810f55141d86520203100f040c0c401894000c0740b555a1030701d4035000c8060200d008c69070703041c00700082052001c039034051641d00b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 556287607 1250 556286357 556286371
    0x15030f01050112231e0f010606080109090f170a1b030f0f2102031603050919032a0308060103050910050703020d02031005090f130b060d1b06081b03 65
    0x2131107520134040100101103420800f04c0062142002d00c203007404001540400000c0d07040103a031140c038075041100d8207070340c418450000011035a03c014400352146600c00c180b03291207a40303841034424080d078894410143c0d00c4004c112030355000c10359960581d000340a5690b9100b114106031600b44450f94054000d036200303010402007004501080e04a60300411000100c0801e06180101200b1078010b81406580110349080104204032354003a1110f00030b01a150062641d9806131140d1011400c4c0d8504001142c88150100071980c0713585800f004040214002c1c50380b800100b00741041a84c00c010b1b102c2640903091504151415081116a900114901030301c034004040c003141a480e00700007140a8014a1003034400d407840042802084401c1c000b103d0b081b00c81c203441c0486c450b5103c207074120103410111035041c005008001050001440345030580d5000c00028610600c5000e07503103a0101c00c041e00030070303003000a107101010f0101581000e003107544a01c142e81039201003034814106050900006d0300407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 556288857 1250 556287607 556287623
    0x1180f03050a1704060e0f120d02030903120f010e0114030d0e06040801020d0203090c041103040b04170706050402191d040602040806090d090909030f081e15030f01050112 75
    0x510b007910b100302c51460800e00411003a8030f690425042840c0105141078800d070180c406d04030030b0804071201103604114484401000da08080c04049c900010b03500041c201c4100740020455400c0032003d1540050044000160868035581084005c000300d51060f000042076000780c0b00396a0307642e60001800210340006240c41d4041083c81c002080c05070080740c010f01c503154000b00e01840040410f6000e1481040d0580c215a00c1e44030300814401201c02802a16074120820400600450001640d40e0341061299100e200a01d00e99081018580c2010341d046a01e2134459082c00158078210381c02060034981c980034000002d281c186082e459400352044207481d038070b030030b800103042c440c05a0548000303108202c103480c11440c090503001d0b11103036941d0039540407801d0070302d011880041c640b10315080c19905403151101028908820355071104000c3c8808070700002c501043c00016540460a400386002100035036800c0c0200b420103003444007081000985a16040c01085a125218110700071140c0001c0e00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 556290107 1250 556288857 556288867
    0x6071101021e0a031806091a090a09092603070c020f040203040b011d0108151503010c0f03060e1003060b0105070b04030c020a0b090f040209030a02030a080c01180f0305 74
    0x140c0c00e145541d1449410454803400b002c90042002c21038425207807099a031800c10442444034500d0150080c002c8400160108500b44031000d4080b5070011a04d81d2401b1141c2004e071020005480d035003861b000031002a4840d0b1380d4404005800020040f10040f8200c4108950512030291189000080900c3d0411400e03c4552040d52030300e0a49000c1007a003d00255030301d00d890f04181c40c0c0e040007849400c0310251202a8100e0320300a0351010307410303100320001500407501c2c41d807502c014008001d071101040d110b65032000002d6960034826a90f11806a80b10000440e404103000b074100c40d0568452101803a40341c0800200920001034603041ea130303214400107190200b60300101c1d500c0c09910790040034a46040c2c1400141500041c4082a403442111910308850f183d13450326605002c2c1000c4280c0080b031413182c01c00649880c0d0060304201c68003a0031283d0310240e03031300082e00d080d8040d40191861840054101d000e81001c0c0200411744600c2c1c0280030a0412582d039119480c0606100036040100103e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 556291357 1250 556290107 556290109
    0x80919081309020304121b08180108131e02220b0f03030a02100903031104060c050d0c02030a12050f0f0304060b040501030206160602040f08010c021005152b051b06030105060711 78
    0xb0f120700303504607072816209d241c440700b01840c40e0104a0780c0c501203041030b00082da6804040040404c0300d507001c10403c1103409844824040103419550803079000e00b0700c1c03084200c0380501d4a86030319406080d0701d0100b81130702c03a0350610983c0048032141c0c07802900204500e00380d281e000100c081034842c0403880050400fa450400700c00404c5031000700b0804c0c2a00080011302a13a12009030303408a40107200340d03141050401000d07140005031b1080250160444001900070500b40300071040424007608044ac41d201c0d00103041015940602c114059210003c8144001d100c0580704110804005036410007e81d4156000607a01e40150008104004001c44008041200c150161002440d80c445403034103103138640d00442d002c0c00740250120014483d0b0510f007940c8100c03600443c0e00450300d5241c0c1150102101c4144404148054201c03039020b9821004042c4a510030842200c0690050018201300c800b0760440ca0301160808145910844050006100666070302d02111451540b00c501c504019028030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 556292607 1250 556291357 556291397
    0x90609100906091d0627181c0203160606030f0305090418030807030209010c0b0f250207090c110a060515011e08091908130902030412 59
    0x1549400c48505040c4414954014184070151601d81e100c01c202d4548948488491000b800110302d012002d00d07004c0b40311400c000030149110210002408043c0c0b1160011403603581007038603080d0505400c0b802d0010349013030910680c10b48018941002820303440310319000b95030f8081c0c00101200790b111058040b081190550050000307503400044204111010b08000e000c5800c0301c1501c03409a410107560346100d84008034102a0b190740340e142c00486e511200e00882c0203401141c4001d050010565948011841c00d045481c40b40c1080b10f4104654648460781c100200412801d12150340800c48104d549c83da004030310042580c21981d030024603000e07100c1b42240c2c001c010b0b0640304a1030040540c403600703100701900301d50711130460604201382540034000110740705540025240b000044103e82c8000d100d11441040e604901c018044400c01d4440c001e1411019281b146c1c2290303490000038604d812080a40318880080c001c0290071402d40c68a52640361f5520b140c55410020000180500d078804a900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 556293857 1250 556292607 556292617
    0xc1f021e030706050709090507030501150203121501090503010608031b0601080703032d0206150d0302120d06150c0c06080108101508160f0b091f05070b1905060306070c080906 77
    0x7d1400d010170300305910081e004107028040d80b000142c8404076140305600003c2100c4070000400720007034040c0c1c0c448a071084100180d4410328100030540100113030940d0300b40074800252144002031551801088103100c1e243c400c01e011060150014801000f18000204880e82281d8041c1012405030748141e00c110411982e29444400c145c409810700003019600240f12449000004100c8040e01e1000080001424000b1b0b0000d00690101d00c88581e00c5980c0340142c80500a038410100300542c4460300600318282d0f1100741000144003488002c240f040c403804a1300205264103154486504101445450740300d045400a201070b25040703041040048226150000c041c0f4100b0381c0c4034040c44100700018030f003462244e410f00001401000c101581010101d40311480020b2141e8611001340303480c00030666113480200c0c1031007002c0c80035070049600c2c00d0400d48150450040b030120110081ca07643e0441b00090481c50296020343d00b00308503d81c01051088887d608500d10981304e05090000030098418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 556294964 1107 556293857 556293869
    0x151508210426010b0909151b07020f21070303090e060906010c0303090807082a0d0e0d02060c01060f06210e0c1f021e030706050709 58
    0x24507401c000d030442607050000c10501c0000002405101044500060603000440803900315460741400d16804512408000c42300351210b22000054000c0d540002c2c01107a04941c10540c2d942c0b1140446261341d03181682000020101030750980340c81c658807049000c6005c500000c160340b00303500c440e14420a8054214506ca6641000460764069454000e0f01415a511146c20116045800916100340164000c542c0c1b90b031041c1da007c400c1c0110910f218000340015654024554021a01040e10016403038841c580c09540f00000fa03840380c00c101d000358000700002d20544001810f400030300403a5108001d507a01903543d200107031200d1038403000d504c1c44001c06901001340395207160301c6400d2820144003141c503041d8151001c40c1c22a0080c402648092200010400ca0540e04121000120300010b0201d5942c6003d441c2c42070342d80c010054014201511400040d0810344140100002060 = true := by decide +kernel

theorem cover : BRFrame.Cov 556115107 556294964 := by
  have h0 := BRFrame.cov_init 556115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 556115107 ≤ n) (h2 : n < 556294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
