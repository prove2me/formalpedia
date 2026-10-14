-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:26:30.336759+00:00
-- url     : https://prove2.me/submissions/fb40c9b4-a8ce-4bf3-8755-461b7d469feb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 65467628 ≤ n < 65647484 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 65468878 1250 65467628 65467657
    0xe0402060d0c051e0c01050906010302060a030b0604030210030b010906050313030c0f080304030207140312040b090102070810090303140403050f03090309090705030103030810080601150201020c01050f100b03010b 93
    0x10b150300011119032041e26400c250415001d064040c1055400c000f0b060800c041000801460b1654803400340d4811003440025800582042140718071442500508603140c0058042420151607038000383e064001200c0362000240da441c15a54203680c060320710700040c81c00d81032461031070402c04616a03cac2d100c11007024003402801220701c400c01800d040c900b410035801144013601c0e4209460000c3d211499849006070120100c55500014500800c40801e040c1e404005645424900b080c0a01c1e070350840a90380d8154050010001341c0e90030213200d41320307100b441801d0005e000c0c00640350150460f151070000c00c806210f03130000c001c00031383c2210032601d040d04580000c0e6100d60b280d05200340b4610031214040d030420921404c2c81000364001000d076058074481d44404013203544074920f071942480944540090380c0c0c420300c0100320045c80c0c0208800312070440e100243c0f5001c15150081d0a4800617246542504030900810620151800414000d056507105041c59945400d03003004a40c0507102d010155030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 65470128 1250 65468878 65468891
    0x9060c020d1b0e1b030f15150c07081212130c060801051503090606060c010603050303130302010e07030f02090a180f0b090109030206010b0a0e1302040603060e0402060d 74
    0x550301c40c80d01245841e07100c0c40c004822a001c4040c00382100491040d011540c0ca044081240075200216100c00070350180c600e07508559500e404d035002c80320080e0032a4245d41c80900a40a0380c1c0b45c1091105040d803540049540d94182a51050714000c0380d6404807444e038005486001d0300300b0b2414201e50b06501c078a020801507890b125507048800641000c0106a0b05108800250180e00280490304031401195160903801002c46080114482140d64184503001540094200d1811202400c1c0f000450340000070699180d44d03c0500c0c5910a403034000000800b50061410158240901054940c518004d40401032950b613510021508100000b0300c6400040d002900a80f860342c005600305101c00c0b803040c00d003449806c0c0000c0505070328034142c520400340e00000782d0704081401034808055040e0b0040016038a4444a10803681044251508208038000800300035696201c808006010350100107903224074007100501125219400f0000c0e00042b10100005a50b0304020786110145162010ae0310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 65471378 1250 65470128 65470133
    0x60509150a03110c07030515040b04023c03060a0c0f050a0e0907030902010e030105091905071205070e09010c0507020f0112060b040807090e0309010c1e06020309010c0f09060c 77
    0x10f0040300345440802c00c8003044071401c2c03110000b09542100d0040095078101d4280303d815130980c101c1102c001e411a1000c02c0802c0040c2070100b04890707030800003501a60200d400302400c1c0141000c04008000c40440c8202c41c00d1f4601d02030001039041040e4600410840003010805400c525100c0c03443ea007400700c04119220035078014500401c50120060038600d0501c0c0005000d0005c10500c5416800110303109141e4486080c144280e502521004000301074489910a00602c2095605400c40d441e020303008000030b600f11080480754a0724450005484090308004651600072402081c01d40c032a81082d02c45011239420004039113110f501a100700d0368240c00b040068440200c0d2600100304c140c035140c1d0000e034003204036000d44107541d68030040c1d8900b070799500030324019111480d408400c150420000035060f58060380c00540c2052240031a000f54032440c01850360817121604003561210f800008010481c682807042003000b44640c10101c44a514a01001b02043c48502035a000c3c00652080b840c00d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 65472628 1250 65471378 65471381
    0x20114070206040e010806100b0301050d0206040e040609021e0d03120e061006020c0a050303040902091c0501140f040b0c0a09050301051302010e010f0c060902040b030313030201020601060509150a03 87
    0x112500070b801280d495581c0c0d0712041c030340c03074092084008900455001ca41d20001e042c840703008454102503450704503400c20f82008000d00464904981c841810000010f401074100b8410340b20360f0181c000051524001e0043c84400b004000701100324410402c00614243d68114449403010b8052400315a05007440070300130014202c0307140003800c5110f140c0400860b040100c03c0d500607614141d00395500c1100710028041d007c0c0403805002c0e89030300188000d00c10100b540d030140c651020010724643d100a00300c50041d003c02030049058801d651070701c6a010014243c0300000d0b4004504d22042d40043c50680c40301c03032629202a041002d42076001501c00d000750b20840c1c003c005002c00130300030041030400c02c0c0d1b8150000383d1040b04a01003420b4642030b034129801201c2009101950b91100006408680e076544020f01038468100e9201e9980c01044040d070b1401c0019001d8495a000c0d0400b00c642180006444c201050740588100071007001003500c16199201c03208112100d0400c015100c0c1a9030400b1760 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 65473878 1250 65472628 65472637
    0x1061b0209150307050409080f030403021f15150c030804021306060203090a0f05010801090b0d080d0213050301331505040306110906090108100905270c0d020114 71
    0x30340c803510314028031840c46041d110303219202d00c0840480c0e441c141e54905120503a0502c000145c041001031103a1001101003070010340c1c2c0310344071348103136021845012050344500c00d0b134070b522000e069940c050700b2040610310080040909180c181d080520000c06800802003140c031400181044110400701d411505d44151403030100441c1403040c00810784811000b5903e401130f90000f4070801c80034200040e042d0700540740e90203a030300603540e0740100d0307003446c8140d80600812107000350050481c41903c004511aa005007100b80c802c070354003603503900140140c1d200c080c20b1900320900c20791514140007c0001b00701c00709188088100900b9030031003503403814032105a1465000f100c2c58046d4443e66050700b07502c10004c1c41176074842c2200700800000f0300c541d49603a00860342c103d0340020717007003108000d40e6003d4590264004103407010782c9081900e60389800e040e40c20030344d4007034a0146010031419503084001500d5031828607400081c0b50010300000000c1030800c000e400a81840035081040d01042a13400c01c0b036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 65475128 1250 65473878 65473883
    0x306050324060901030b0f1e0a020309010e011509110d020703050c0618030405041e0f0e0c06030408031308040b0310090c020c010804080d091703010f06110601061b 72
    0x4508420052891020780241c55000390401c61090300081d01510302030004070305aa42002070407000b652a4801d409025001074103228812070341002241c0c90b0000c0d180058461540c0360b1016899040903907016081d26030740c00305000035905014a000341c0300c2d05001c07980708403500c2c0c00c400f02d000205100c148049203c1e06030034000c1a03000007000c00078550443c0040c005042217000b140c2056417808031072600280e19405031401c540041104218a14041e00125100c281d5002040705410442d040c0408852051032660140d580700c0c52041c01c00030060101c0541030f9010b440c11881c51038103640380e0405100040145c2c0559900c135114505010301c04007078070041c0c284406403e6880c20221070f0140b400d150b501c01c488040b410a82d40d0004180701207901d1a5242041e15940007640b96a5940ba1050704403000114005569040d9140400c045c10b880c030b5050170860500d680d0b2541001461100c0380c50b507400100502c841c10b51700400400c000190345044074040d203410303440c07030800502d0580e1030300724400003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 65476378 1250 65475128 65475133
    0x90207122102220b07080f0d0e010e0a060e0304080715020109020d0b0f0606040302030a030c1106070606090c02030c03070f02042c0105010501030b0f0d080c0303011d06060f040b070303060503 84
    0x10002c04031050b250f0030103061694082541c0761035aa44416a0a00c280c400c002d0440f9402c0c0071851444450034041d01002ca0200804502041d0303040703a15007102c0e8440701c000d00c5a40088460018405c8520483e81c14402442c0954a0941418242a40c0382c0461064405941d40546c2c0940c2c045e200394002c1d582541d00808900280040d030600c000d04903c291540444a41408040380342440c11504070f4003201c1c0e02802030000b558807505c09031000c4000355800c2d01c00c00003082c01c160030399403124000c0c0f0310a03101c1c0c6000641182440040800c07030f03003c1c210450540d4810820081d64110000c15601156030101e1452008100e900c0403070040e1001480650000700c00d1110b006e403400c011400c01c1516403120f8000c20490780e0790300045081d240c20403c0e00b60808001003480e041d07802c248194040c4240601d0326140340c040c21400c10f034a1540242d0100c045154203c060f65000c00121b000d0302d030844d0084941e103007003c00030740750f2240502c038600c00d42c1c200090008a45007054085d030881001004014107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 65477628 1250 65476378 65476387
    0x212010e06090d0909140703020d0605040501060309060f05060102030304170c0318040e0d050f0d0605120d08010b03010e0a0f09061104050102070603091a07021213030c090207122102 80
    0x140369a543c100c050304140881c15010010525502e2403095098110480d5244020354542c3c920940c000d5001510241200d903c8850200d96a11140106c0c2e00070304944e50005200015428401e08692102003903d26103418003081c41017580c1e001003500c0d04030b5007026100c000f00ca070710301d40ca0803544140120b4034603900000c980045210040a82440c440758161000c0c405c1c0c400518803981c031a214203014202154041c8060300007400c4410280c4503621f59400000b8400d03880340d0000b09190103000c4600c2c00c592000042c044040c0c0e00400c4603004041e90030700b0310b0565040111504822100401041340550340d4071040c0300029441e0062000c041d0003140410814803000c002a031a54042c2c003880b8050b219001002800900c82e1080480c402d4101c03541010f112015032514001c060041d10345030452140a040a02401901c0d000344900c41041c1d840c070814914515007246010106e07840800c44074030601604000c1900038119070100c040d00d180001400f0401c0f8044c03100a021081980c140ba4404907 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 65478878 1250 65477628 65477641
    0xb030907030209131703060108090c0a0303180b0403060e19030f120b1207031707080f03060f12030a0311070506060f0319060b0405060609010f0c0807120e040e03090109030212010e06 80
    0x5c02940280c60a9036880901e68501008075500c080c0c2000c2240c200c40d000700100007091181301601000c4100701c0c41c08041658408940360b05400c113400c00c3c0d41c1265200c240002140d82007005400c504200c1041440d51440740d2030181007116590704d80d105102005001c1c040c120f0305a8044162050000e002c0700e04629990051070340c504250008407452002ca030106e2008151030001d0391480b81c1d1041c0f0240c5000441081030b54690409850907070040300c079114000c00703a82c3c1c510900f00b8141040e001140c45130200140102070f180c038640d244030a041c0412681001c00d5020405179401141aa0080c500132950303008681b501e1481c103804241280c02c0040c0c03400f04046504451052402184c080c40307a44c45080c00c00000340314904d1228007081508541c07003040360140d400d0040c1c03a801018030078201a10303900c940000c0f1030b40011110000344c0500c1c40389024074141c0300342c0008030f03c42c0004508010403040080c010000d203000203482441c140c00d5203520003600f500a05102240c140646003541400d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 65480128 1250 65478878 65478923
    0x10902060c0606030c03010e0a0303091b031b050604030b04080c0a12050a0216050901060f030905010906060303031406030d0e030307050a0f0b01090c0203030a020703032409060b03090703020913 85
    0x382e800c14030174010540c0b929041d141c140aa030780030320800000380980800a0760700780d0040404507000c95600751508101400c0780711401c4040c00071409600e071420821040550015504690303000307148102e070140428004602280c2d00c0b103501582c003031141951065504d1340329160014103003005011105001c0c1c1070501e00d52003405498400c2481c0c003201c900c200c84030407a04180e2031900405402862403001002001e22500010307074039295034240018450b40640b542403d40d60f070303003900361141d07034407002d0400070194140b107000302040c1014001110780c24141d000a45506000505000304244905929032a5a00380122681554480708442c02852245009610142108419030b05c030b007101400001c201c004c6000d589041a02503000d0351565545e401c1a1009400641c4150201a500c50308403580584004034110244850b000920005142007020b030203540050300071180c04c0300c040c414040340210000d0307040e050ba80e040b600d43d4100c1e0742d9880082c01c42d03080301001504051540c80d00001d0310401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 65481378 1250 65480128 65480131
    0x70c0605130503030903030904230708041101021b15160b0907120503041a0c0607120c09030803041203090b0a0207110d0515060402040b040e0603070501091a0c010902060c06 76
    0x8110035110709540e0401c244d228003440c0f4000c2e42581080180654a242c2035002100100c010381608261030810b04040031110030440b102c9011a0a1409110030700110049061307018100b48024084058011481107090320a0000701e4018400095216100c0c0c02007801e5890840100d00344412040090070a1074001e00151444a6540150000455900910405440007a0b08080214900f624100d1901c2c81c1d50f041e41ca001000c0c803000c2c4020700700c50b2802e1000034040e45490342c801d1a0030981d0b6003201c04488004801d2800c1c011001c40c100000745405003030369806600210000301e10012100d041e17010b028403001c01400e0310040b1741000700304040c59000d401243d0058071030015000243d424080e1110300401c0c09440e81d88000d101100c0c3c0b0144000c0503500410180015007000e5440c100000103411a8206200780243d5004000b514181003042c000189801d10f045541e46151180c8003a03e901640e21a200e040340005078441c004000b5001200c00b0781d405054590b940392010b007102d488000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 65482628 1250 65481378 65481397
    0xd060903110a0c0509130231050a090308010806070f030b06090a030302030406080f011404050a0b0316170d080117190602210f010b0c0f0601080c0907110a060e0102070c0605 76
    0x520b0011800201d42c0081140d00b00d503010f002c251200b9092580100c92046000200340d612314a00703058074014074180105806804030941c0400d01200c0b92030041c04c1c01c401600b09d44081d60029042100d5030380d01407480d244404582c14001004400180071900344d1042415860304125004000420581c2c00030081048030030a07070b41c440d855122420740c02c10341d034020b204028624580c40c0e4601c0071441d190b8403094001041000004440e42c095010a0500c480d10200b24003119902d13004125101e50000040500b0302820003800020b00382a4028018202c10300403595038001c0ca101402002d0010020b180a0075000a05c40e410a030035441e00001a600c450034644030f0060420009081740d0000c41ca541c06002c01e2190101030780e00301190883c0c180c0081400c026184110810a0702854003031104030701070094107018000111407041800451180a040301c010040f041808822804011030350240c40c1c1c0e44a84042810544040050b019014109000d0320200716594002034054001e00103040245 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 65483878 1250 65482628 65482639
    0x303041b0806070207060809010f060b090f010e03280501020c030d061202010207090c0302120108280f1203020f0c0c010e06070209061c080403080a020610050d060903110a0c05 77
    0x81d00e480700181c460b201940c0c00e00169008900601405014020880c0d00901d170000000d0000311660007401600c42c2a8000c040e04100054181c1c580d0910200300c8007800000e00b00007110800c1180400d98070b40300c11121081000d2450081d940c41e803002141140010303003200007991107140d440e49541e02e81d44200441b030001c41c0381180014014541d04642000c4139016009002c0052500c12404040c02c000c0854408045c0e0820154070001ca4080102d400381c620301c4000d10700c03a5140320111626101541954004064582c1900300094014500140c135550001079500d14220300c20059020703001d810300440d00b211b00440d0750700e000070000561ba60303d00b1090380c1e038061a80603a4113101d4035116940e0041c0d000300c0305c02c0002c2d1240c10405240b00b40c101d01d52000010600843c0c54081c02e075003158008407141d440008110115035810846036800404a038101103c1519140004c0d2101150281c0100215240c449813001e00d405000e030250140c0d40482030382c6440d0000c2c030b80340d410b802c03080c0906807084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 65485128 1250 65483878 65483933
    0x2150105040c0c050a0c0905070806010c060e030405060c010b030115050d12140408060708010906150311041a041805070e120106030203060702030405040608060c040b1c020a031b02011427030304 85
    0xc0e11441c0d14ad402040e060b105d1862030a800d441e00409000304402840c0c171072204200001d000d803981d400400e2000701c403500000da0000c0560401d4207680c01c00826904580002d5014800c41d030354014002c84a0354841c29003038440341466015034000038802c000300c0c06104042400110315501143d194032480c1641d46200391680c942e1108011a01d4070301880303407901c030190780c4003442da4000e900140e0070804402c0c40038241070303454090006010000070050144200810304110410305442d0581181000e504240107500d03020800520303000c1d44100440c840c0d0090204110620820340c0244003941d0050240c075014504210040d40c2c075840361240317078012494100c001450744000308105009a56041c812881c05141c810b00d65542c0c2c0114a45004280304600001b03c1c2c0c6030b85100a08420016841c0855042541070003840ca8200303c400602c01d59040514161320807041340a05684448446105040001a80c10b1341030a0640d0700c0300c0d8680c0d80300000502082c04151014210008900e510701d1062 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 65486378 1250 65485128 65485141
    0x30f02010507050a0c0206130303020f061e07080a0b0406090209190311010c0c0906080c040605030c010f030f020c01020d0b420f07030c050d02150105040c0c050a0c0905 74
    0x89400455551001500520007030321210b21464890291a00013007d00e03044c560001044d90201045501c1100980d00400d0349170b20760715003408400c0e80444800c0c0c007026500c102400640b1000d400600100c20401c05000250641d001c580c440c040643d00540200a042c0d01d5108076402540400b066a2246001580b80360b00c0081c0807115100741e0342c0c000300c0e5040b0501188010749000d0400d8504481800b0024008103004a0911030b01c0c00070701e0f00301d004010b45401501404100c0b80c0540140f1302941020020040c82d0b600003000a140d00141c1c940001c0143c40001c002000340079000e02010f0b5940001a90014401a60041c1c0c0709550300316100c0c103101810102174204009030900048070003034801d540540003d8003050000580c950a42e4032440c06a000302c291455074881402140170074201401d240a100003080208a6104580000e00204940000e2140e00340e6051060f41c3c4a2a115000f580b030880c03090f610f04440a03400021541c00701035034030b0184020006400303405146482e00300080c29 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 65487628 1250 65486378 65486381
    0x102120a0609020f0405061602030f0703031412063705090c03040302060406020703121e0f020406120e0a02040c1d0301020301120b090703080a0f0207050402030402150705010b0a030609030f0201 85
    0xc903441a20501417800745003006100094006448107411070a8141e520405607c0c1802000810a07000303000d450f07400d045180140010404041c00e15000005020f0071500311103111503aa080700d0200c41b03080e04240a00c4243c401c2030b5012011818051510060702803078041701700c240c81642e60445000d64035540e8120380211314002254080c0060f13003c800420041100d40c1d004003446070091401402d00c0c0710925002040d92060900d884851038000c04c0c100c03102c030300c0744507980d61030303410580c154074081c644a802050003003800c08044035181e60707200f038401e00d00d400c202101d0300d40e5010700144103220712448081c207150030400f40b88861381245062441207190605c05c80341a11010000500305075400c1d15032a5000b0002003482c2c045104c2d070030011021402000180c0001d9149984507003030741c00390040080c1800d82590180d0701442c0103005120040e6901481d80c1701c0a10307881441519450607007407032800740c04285546600001952008418000d81d90031000020707002c3d40b6a9019034444030400ca0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 65488878 1250 65487628 65487637
    0x50a0804090c08010902190503040c0807180c0e0108060609060d0608010204150507050a230f0c130e03040603051f06020c040c1b060f0b190f060c030801031209080102120a060902 78
    0xc540e0007641e5443c0707507c9000b100a190424001c5000589458031211102d141a62071380040c2d0b01030201c50342800100d003c0d8000d003030103814185040303e030100c183c40018181c018007501041c8100804100c140a5032a064180d806d0620400700500510741e03906034650007944030740100f40c2640701c03454400e0440d6018104550b038151f07002d402881404480c1d290f22002c45030030042254000c220302c009000c000001c00c226023030103500300c02421290722000208041c011100705800f00140c01d2108203114002c01009440885840c0d00700401d091b0b0703031300e41002c4e030b104070700c4021a03520ba2080b031002c05c0841d0300040c1c98141c1681076800304035000072941d0640741e00c0140346800754000e4048902d00000340c1c41d60001640682c000001040740c1b030350354000407054029000881e03062110309008118000309601694001e1072981009000d80d403854078001d2a1140c140000b03004040000b480e801c40d284100052001009410001c40d00d45210544558101e0010b840d1a0110b604103c40070800c04000c1c401ca4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 65490128 1250 65488878 65488897
    0xc08030f0904180501050907171501120201020109020a14040c0e0f1e03030724020304020d110a05090103050109120e0310050c0f120f09010903080103020904050a0804090c08010902 79
    0x1a040c103401008000c090048508024040300c940100e07100007034424022640501d4800e00600341041c1440500e08611845003107060955102b00440f0020280e40180720703054400700c103017003c80d00c000ca00061340503049440c00290002c4080c03400294550ac64140754416820855060200d07071621281140d040c03001d02d6420342d004c20822814804e901e80407800440030160507407000003414165000030305541004800340c441e084083e0f403403034008965110400d51011016000c50450038a0380102c1c602c00f400d001d00601c401c0b0f455a4070003040c0c1c0c5106040c0b004210041c0703031043c15a100d29119018040c1404103d5100003041900803116015140051050f40003800506c540c01302d408548002d014040e02600b1800401c00045501c2000980100310460000c458aa19418615802d400d020002002c80300070b83d24090400000a600800050469030111803480351610f8500f0708500f0a0031411009015401c00640000e00e4030040d0080d4001c03000c3d54031a20080c2e80e032903010720141e110b9110311 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 65491378 1250 65490128 65490157
    0x408060a06030b1503070806010611070806070512040c09020d020c150103051207061401060504050a080703020603040b1e330d14070f08100b04090b19090506040c030c0803 75
    0x44e0b181c00d036110b0800c80d00c00d0000c2c00c803003c080d5914222801c00500780c2081000502034102a4201d2100700400c20040108074000c2001d45031170200100f150084004000e4000300700c10100301484800c01b403003400b0f0040c0d078604565580d12002c0c1c0034000c0d07212207007400460181c481d00d0b182140c0480850341c1242d4200e809800c0070f1201c1c80341c3e04029408002c0c1211080c5c0d55424a02c000424144081e01901483c1c035015075450400d010004840c0b0740e40d0001405a001c20000d00040c0c45070000d4030742050340440003c40c542c03140101e00712400c8482c52022801c8015404104010340c10706600030783c22045024142c0c4145172841e040844c0050030380c0f001d800404100e4814002855101081c02605c0045d050b00d001a4880401c103141014a501c4840307554800c505600f00e1541074402d80c8841c07c81107804000c4c22402c0d5580c48800d0000400b645261200e024085651084982249000d583e1050540d080f40c585490481c1503035031a800151110230310507a0100f042c0100208480c1c00842c0240e6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 65492628 1250 65491378 65491381
    0x11704030e0f01030204120f02010921080f090d0c0e0601021209190e07020706021006051806060d0207050114010501020c01170603120703020102030901110412110a050607080408060a06030b 83
    0x80c00280200802c00038101582003000103054100e40800c0c1e1500b034400d8440c0220010980001000544990172203249001e03510a5540c01224072003804942580c80b0329515141c1c55104160200e038021000b00d00d0b0065110b441410401a40388804800e53b841d040280300c5985076440126511991124868450107040000d150b040c60480e691050b0407003034580d60103416859010720000050292100405071f0300401050015640501401c2907014949a040141074500800220161402c00d02841001c00044c080ba0355501d51500300d442494014800f035550310700034a00a4020b042c0040d01c10f580d600510004a0107603c04039444143c81c00c1696640340e418001701c0c002042d1071001d44840c2e0f06105004521141040c11070160284601a800040e101d05d4541d100c9070960345040c042030741400081205100080d1240d061030030071904000f074a07603994150f901048601080d50011580500085100020821420010000d499440041da4640e0700c0700f0700b880084e9801c3e40002000a0700410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 65493878 1250 65492628 65492657
    0x30c08061605130e0c04080d080a0501050d08030601050307020f0111180405071403180d2c0123070816150203090316051903080105010f1d09070210020a08040201170403 74
    0x4d000c0360401c10401c00b16140c2603540c02181d10f030902ca44445000f040001040010211083c402c5030300610382030322000e40781d4845945440403884010009410b0001c04804200181e10070898824158140c40c002c0003282111807041d20543c01052103448610490143d410b5281090b00410340183c0c140e84880c043c5410010b5100301c10341005040c2201011015480040d0036010400e90700d01d201c8580740d01036251184c0b0744c0040c40b000c02451500440070281e08940b4a641c0c40064008001004c40c5610702640301c1b01005801881040809004024080303203040801100480084550b4070654400741e805d508a8011426408200c07280e1755103410500690b0303002a01c0d0030a40e07003d11700c600244d8401ca01c1c48404078144210721041900000e8641005102658008007022003642840c10884005401070100d0814118032004840c010804031001c074140074001c1109004104c03101d042075481f011049401010320340200c1d03081e8005001c041c400c00011403500c00f41c5020f16050b5980b00303140c50024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 65495128 1250 65493878 65493899
    0x5040c050c1902010c1b1505090108190b090406020c01050106020706050429070b040302010b1801050d03230306030606120307110a08010906021b03030105091302030304030c0806160513 81
    0x8860a03418440c900628600041c052426051405030310301c0104101810087c0d003600c005034050180091050801c140106681c00403000c5901000e000c40001c5001c10101d681c02c058000072a0340d5402429280a1004101c1d0b550081d26260704400000c0050b0fa0307841d0401c0b40d6442052003480045802000140400140b2900150014160072101444035180700c1c40c1401a40c410a401c1d910446c036042484100f5508cc014200410b8084a000b07240c0100c00708400d81405d0188505441441050039403030806020304000c0740da4003c0c0b15503101113400c0d5031540720b0069100303d6102d44a0b0185100045461070600c100c4074168550710019400e11620ba0b99811146148010041e40b040ca840c1c40012001c03002d001d4500c0c0d4a03c1600d01507110380035502c4030801d03905048030044035070b001840144000e4496001235a4009002c484613000342c10359002003401c5128581019082846c1114003007021003002880c0b0b4001c8051034880f24000200c034a04031128001c1c051114910598540c040101c000310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 65496378 1250 65495128 65495173
    0xb0a0f0608150919050a1505060c100c02070927030305090c0a080709140906060607061103040b01060f0f0f050d0f020c0106061206050108060411070c08030405040c050c 74
    0x4400800d8281200000152044508031003000103130200c2800300d0391681c65401440c0d0860b58418040c009112484c84c01004100c1a00a0704e008031408603c143d200041081032a0001030100300400c122002c0c03d0b0003c0d15518107005d4074011034244051000005ca80b45a001e9141c03500b000c801c40d8161640e90214042c01c009088001248030300c3c0701c552490307951007454400600b9100700805550b44bc2056400c05c3c3c418509031000c05002080403c05c0700003020482650006040310340a5880d44c540c500080200101915070040c54404020081013028072020319069410b40e880d0704040d550021000c84801011209000c006611040c2504403a0300400c080c0c1208100000c000c41c2941d854a4074800300d8104042c140d049030744411040040c1ca030008504001c2034007a680c28040c050600d40003801008026100a004076600c0b102c03048000040c200351115039900c500b66044e415981c039000390341c0f504203000300341c401c0e4900b1401c65141030294040b28070780899078014020104580800d421030380c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 65497628 1250 65496378 65496391
    0x7030e030f0d08070e060301050d0f0c03080304080706050604150311060702030a060b090603030f0f07030516050105011401020f070311031203131b03030e19050402040605030a0b0a0f0608 82
    0x595000c81105590521815403181441e6a500703d40b407500e12402400e90322840101c60040340100010311443e01c490700d4980c880740e0002000400460319181440c0c0c1c001c11a4805800f192000c0180030401c0000c41c010035106004520600103a00c1d104104011144c40000040800d00314801c1000060446400e884007540d00420f81401c004964000c20704240e42e413001260001c1d92a0a000954541480c001e41c00034020307401107043c5084d03050202e1040c4030b0303148803070b4080c0350202d520000c040c41901101c45013801d02e040380c01107061138904507010708000c0c043c00c0f499010507240424654400250008146d010340014031803a0714686451507110007103642d15400d8040c800c0350001c412110310040d4003031b007051500c000454480e810b01c500301490040d11162000225001017000c41c1d8401480f0501c254215081d0410f9401590854417030075059103c0c1e60401d001040008880e500013010714032540c3c40800600200c0f100c2410008020b000c0d000307240710b41013400350902c00c16124218082c0e1060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 65498878 1250 65497628 65497633
    0x80a0c02100c05041a0a0c0303110f070510050f06030304060507021306080f150c03061c02030601080c130e030a0c03020f061602010c0f020c04090204270209010609030807030e03 78
    0x20103a03450002940d2410701c0542c089400050104824221301000020390340e0090200c1e13084c90141d0000034401c01402901400300f6272503480a8641000300000c480c2100703d91041540c4d00c178000d242135034840d1100342a0700700240c50400000d101020034000d0310300c43c54008025500d0a4140f075410b403959004601d05907000340810181108003000d83c42104040e00702800100b80d50b0980d01141450400700c107030144e0102c5c280313a05125410030b00b0000d407508044200d4440ca03203032000c07424403c8a46188840650b01d0b20514000003036503480821408850032040d100384c4080504182c4240a64208903c1400ca9510410040d00154854032403a0022840b902c10307210450301c4485100d14192040c1d0350a05000080c143c81e8081d81c1c4c091044c003c4a400030709046a09140e50040a5100c0e05e8204000340a261288208021542c1710740c00205801003a041c00c038034050381e403226000e14140411080340181954400400e240d4003508901d0112a0b000324101c0c545141f566007141c600c19070249994052 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 65500128 1250 65498878 65498893
    0x51b0f060d0609060e04050d0c03020606010e010c0501050109051807050d03080402061306050d0b100906110f06090d0f050301141507060c08040209011401050d020309030412030302041d0106080a0c02 87
    0xc0460013200004c100c030314803880360f038100740c2070050411401d0b00501b0b0a110003141c1e0400003940115000e0350058007401c004815900701c02c01605c2207090344800514035444e000c0041001882d640c01079010b8060640780d50f0003050140340c00d503075600d244d000f0716038401141ea01900009125428203a8007c0c80074151030b00300080d40705910607a40f2640c10080100e1408140c05400e2142032085040f124400c5483d06480d04102074060700c0c1104034069030082000d005124254540c04200b0f0600c6003650100f120441c3c40c1a006603503c1d00c02c2a8409000175a00390404844188568142d0b416030300030010a045c0d00000720200404204121002e50021100740030510105e805441900d40080700d41d2111603031032a0910411800a90580102c0b8070502c44c0344540798541d03400816540804100d00c0c006a603603d0701140a859802690b02074032842054a01700c008060781900600308803122484080341c07210200e45c00c0168510240980e00c0010080000207042185540001c0f1201d56540151a180c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 65501378 1250 65500128 65500139
    0xf080c07050303040b090f010c08090111010e030a080f0a060f090e010b06120406051f0902070c081903030e010605130903140a110c0402030c0702090406060e0103030804051b0f060d06 80
    0x219003007a40180031101000c541101c6604108440400f0368000b4a00003270407085c20b544441c000c2c062038080d01d041005450000808034000d50007000b4041c07109084035118280e4a2004044c904110717200c840f44c00054000c2070440300030f0700ad00390030703035214400c00c440260a000317903400180030310700b0a03010351342d03c400b03243c805038403401d00070b000d403c1c000078200c00589801d0400000713680c000307030000d6105944020640c900c1001c4125410580d00d04a0025a844015082c0366030440846d030810900c03405130600e000b0f51100001017442c806407182e24148070080305000c1160881d1002d2244a4201003040310000384803210360311054206200b410301c51200710100c00ea031380049d0800d20048010070590522100016010880303800005004c40e1700303502e189400300300c08045008100e4001c0c0602c0d0101d000c9810040a60821000390412f05502856507039070b42801400c01a0036501900c1034043e0047e89008001c0c03141e540c2c00c9041c0007505144074201c080c4144005548461201e0041c0341d95280c01145 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 65502628 1250 65501378 65501383
    0x41a0f0d0203060f030a122001050106031b0309020901030807061b0206011d090c090402032406010905010e091f0906030f170406080a1814070f050a030f080c070503 72
    0x1461410444016103e00d804400c1c00000c10004800c0c40c8a07174840e010b1100024a511042603180d02d080c6407104250950302d400ca900386100040108155003000c0001c28801d80c141c0c23000c040082d80d00e0549040f10b6040d0800d40c1143d00e00303d40070b50003003d48001440840c0e440c03c000d00c0ea241c07090100190700068170884560310340404840f000142c00c00401001142c0c245504800740c56085826421141060549959a40d0a047d5a1030260a55800003015550280644d14900b54072064084000301142c683d2008018225400b030b02040c4180c0300800c041d481894401000038010701003165030384407540840300c1e818080940c480624030414001c203903c5001c0c003540300110310038000c1d5407004145160685c480244c0b4010250518000e000c1001000d5004c8000c036000120307140c00049203003a0302c8254041514810b000307060016800100d483d6034800052120840b80d90800d214030071501c1c1d100b0849074088500c0003604071082003900b4400f00d012100103022004a9108607101581d846c0c021a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 65503878 1250 65502628 65502637
    0x60d0504060e0601060f02071703040503030a050702041d0a1112010c020a05070905100603020705030f07080d0506010207120209060d050d110606010f0c0b090109080315040605100203041a0f 83
    0x1d64032500e608002074041020081140900f1490a2101d0b03405d00000000350743e20300d28815040301280280703c0e0728602d0020300c22500a403002400783c2c4da40d00003112001d03005601031001203024a1500d4507420316100107515580400c03440c403001e841c41440c691100002c0d0b92180c01d21552011501100d0f805500003441403068264468001d4403400c0802c2c1809400c1c2841c0d6801621004e040104100e00711020b440c1420546815003001600e0f400c1f1810000e1850041c40744040c444d0100107124800d01078140043c007015148030340305114550340c2900480e1581c4c540d11580c40100c41c1c2c40405070041c640304a481d82c0c04030014000c96034029894440e14945002c0700d20020124109a8001491403000d0000c079a0003802800c0c80417428107082d40003800000e030454041d150b4074000010075081c10081d0490708410b908000016100e04240c0d1070340c5000000805518800c0c0c0c90007800080d5820407c400102c107500c9030300590300389131505031141240c4841d58220907000808006c844071800d041005807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 65505128 1250 65503878 65503883
    0xd05032e0f062a080f040308030c071104060b0f0d0e191208060603061509090c0a23191709010b090105060c1e0c030f06090d050c060103020d02060d0504 67
    0x808502c2c000c0090070200540c8500070198160781e25150208014800309007207941e0142e04c03255034140b6600b01d1840c500541e000180301003000400d0080004044001d040490300034000c40c003450b03101c10108403c60b02648500903540c0c00038400496505014005041e010324400b5000c1f50344240048080d00b4100912007026030700000c066110306122480a082c0103051003810088898100500010302e5400010201c500c15040e405010a41000c1380080d1480801c02614041c0c650074102007049a58010101c40d00018410903049079460030b0070364076400d10400c03c0300000c0c40c0c00394850b071019004010440c071409001c5041c12000c42104100b401d030b403003800181c000090964002040100002c8103a211390b101e95802d2000043c8090046a22100005601001641080e600740c5039410f01c2808a00180e06019000c0016000d08000c01c3c02c51040346c940f07080e00e03401c074605030064a0500500c1740d140c1882d40141e00500045c00c28004641005000408060504824517010300540e0000c5504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 65506378 1250 65505128 65505149
    0x50f0f09010b031015090504020f040e07020604020310140a0c0201060e0a05040606050402093706050d0c0309121d09090d0e03010c0c0209060f030d09170d05032e 71
    0x1040b01340b0905280b10000b502808001400643c499480140034100b00e00a0f18840e95001420f840c060100308100d9009103400800c80c41c10746041c40c00070b510344804a4027070b40240605140e005545030176108228251006032240344a41d2a5500000e00038810504140295942c5480c04501e000032119083c0c03081c88003820120b210b161610301601541ea15900580c05640180259903042c4da603020003543c040c4d0140c0d010b0704041d611020403d886003005803880242c00e454600802c00b10350220040554041c00201400251240401101100d20401300030300304a0b08040039011843c881c0c200d20b0302c00162071903000c207420900e900141d03000400350354110081e80001d80c0500007e8011b2074a9203045000c80c020002c2146a80026180811440c0024070803c001c07000207102d90355440640c034241e04007a045600c3c0c10b0720b490700502107640702d00411710391203c6124040562540000c000500e1002c680d81d150444c2c94030200d914105201c8194840c042c140462514829011900d001000f0504401d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 65507628 1250 65506378 65506381
    0x2406030708190c05030d080402010302070f021c02030105060d02060703120f02300411100309080c0105010611030405130c1101090309060f051614031c0501031106030907050f0f09010b03 81
    0x14003000c80f411643c000743c0079070040700703080781c40c00e4101041f00d60150302800c002d44d581c20580b40c2114407200e100f0000391f0003010350742c8550b48088584682403c00340b01f90020000d60303d4580410004502c076607070095100e40c04010303440000b44a04200b105800c56150007244001603841d40b48184e801038490700340860500d0300c207609007203176403490f881180380400245605030404c1d4440c440c6085d001481c0718040d81031510074140040c072a40c012110740f03401c003041507204c6064441c0c190182000380304600010307404076804015803001100312021108003c0c0074440300700c1400d244e5000b512402c441c405c14000721840c2034030007010a000d05541d41d842a50307082d80145c101f41000d03102c00464003103075040000c180994849040520642504103401502da1071101241c549828518400c0c5420760303491043c41e520980501e120b603048281a00d209d101d0341305031241d00c08140001c900040750091502d6011182c00c000e24108182c0c02c412152024004c05230b0300941c2008074840b0301081c2c2c00914410f00010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 65508878 1250 65507628 65507633
    0x60903042124060902120a150305070e040204051e071b0b09011e0e0a1b030236090c040b03030906210a09050d0f09030209090d11240603070819 63
    0x100c3c100140c002d0740c000b1400c208000a04039804400100410ba9907a541d904030941d02e42c3e1003600d24000c40d44042120030031030300e03207007d030210110170b6904901503801c007070204080c26000309910742d513003680440208060381c854200301c640740d20a100120310b90b0411150040070031084141d45200d01100b40010a032050200900e000c011244280c100d9100d02e41303608264240d4010804403022504020360f80312804024100c0d5a40d41081c0c2d000952048590081002c004100780103100c4000b03c2e07a429004d0041da005000c9554003048452024980020031001014038141d8048503c005010302140c0c144043e900c00700f101a0f02510f1300c4403c0d000350560400381d030348945424584c0301c2c10404050199507255a00c03143d890702021002e800f40515209902840340c8142030040086400526010450415203902a101d25464142c900003842e20440443c41500015082c08010b02000c500100f01e14804684680000c001e006075a05001d00100065200380c1040060149036407218540300c1241c1c9813 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 65510128 1250 65508878 65508881
    0x807060f091511090d060b0a17010506010201020a0905060307020703060c0c020a05030703030503010b03130f0b0412030b060301092a0905120106060f0804021801060807090503060903042124 83
    0x611000844604009483e8640c1e0200d100391800b5040949a080c01c4405074030340303000505048111541c06c8000360701700040102c1c041e480c0b8103442e500c00008010948950740128281e02c6288181402300e5040c405c10040c50031301e0401140d01c00e1007803050b80c400c00e07184c6e40c1d008141e4540006410000d030441038010158900300c103044005000c00c60003803451a03d1a40c0180150105210b17600102c8004000a0034a400780b00005d802e241d0300009094180342240b801e03224041040c1ca0030349640726110384503800c00b4064481e940068100030600307811a031808420384050210003211000110b102d1001b0a400c1c81842e152064a102c1610303480a11400d0005109a003e524107103140f140c0c0c1810340c10000107401500d400c20200d81441d080c00c06e0f9a450000c21841807080c4e007445500750740900000350f03095001940d64018811a9216414a035480b010036a4601003910580e00c560020001001414a2030011032500030000c04c2c940c900100e81c0d01c40c1c144001e03010188002a114400c100440f50045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 65511378 1250 65510128 65510153
    0x9040303021c0204120f17040e070306090207030903110102030d110c010e061014011b030e0a0b070507140d1a041109130f1b14030c040903050a0302070807060f09 71
    0x1850b5003142401e280c004000394101d54200040c100740503180c4010144548030481d0300e00c034044081000c3c1da486e520115903000400c2116070701c001a00c0c260012416003440d00884010a400d41ea03950181419070702c49450500d21444000e05510040203071560102c660301030b503050801000400c1d074413103000420031400d40c0c0b0080741012803508140c08003d401c1c00c0c07c410315000c0c0c0c0c1d80f0030b0460f06c0b141076000040e500c14050310702c610180544a4004010141d2103000c101d260001075442c07448056403043c012105006002d0002c02070f801c106c9060009030440c6045405080c001004034411914075150058000815110040c0000d8040104002e01a205c40601500101030b0f40340315041c6440b024554940d000075030010702005006c40707140305000b20f4800703d0a01149007407000140d41c2c2c1d61481450343d07041c0c0c120594024050f5210750070341d0307140912954541a415031200751601171403090803130081d400610102c8584405000c044003041d09407103071050006159100085541c1e032400c1440902c3e51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 65512628 1250 65511378 65511427
    0x2070b01050406120605041e080a020f03030c0a050c070b070503030103120801150509150c071e06050901210203190b09010b090f01030b040c02061008150c180904030302 74
    0x2042c604200394420801c1100d41c01d07030000000181ca440f249041d1a00e052169230903c0c0c50006859604140b00c0844010710310100340760201c907422143e0320f81403501c9000488035104c3d0750000f8803502810342c1c0280c004000401254042d00e101d10f444000c00300c4207401c0f64400382ca140e40040010b108200f0000200c110350709032403e181b1015850029126080700d002c0d80c00f8010040007041703020181d158400089005a02814410780b101d0f040042d9596506040c840e1003d10402810601e03560f06c840301c294001d462241d5942840c012400005440c1e1241480914021140300c03100e0070410b194500c051401140d8091001c0e55150041c2006800d4031b03c0b42440714032030598030b0010400c0d50152400c4980c100800d03204096480b41280042e0001e04140300920781190034061424660340d0b0104400740702e41214080c0c400c2042c0c171520301030307070394100d02484098004100300030440101080000d071491070100c0c2048940050b40034081a101c66050b902200480e80100c1c2100240f46141c0c9101480300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 65513878 1250 65512628 65512631
    0x804091509151520030c010b180703050408040b0c03040608010503160509060a180c0f0c030804320703060c0e01020a02040203100509040b09010c080c091905030d0302070b010504 78
    0x60b240e00a41d680320300300d031107603c80070421881c0c9800a1030040c03800b45501c91461100003a500501603110740c51780c0c4402e0801c4065441c001d201e00861502080c500841d9004580038181607640388020303401880c000d00140c0c5d0f07500b024400092031800f5200104541c464810107982c4941c90308401502c41d20046e04000d210b6002551140301042d401c2130310390111041110b0502984d02c80c0c1c00030a101070032a801802000c0c5410304244180c404940140e41d02c107203159140c44400321035070000c0358040500f09000b030001d400b0001107400306124103180300a01c00010361102c1265482c0b071a00702c00d800354914203522504a800c0800c1440107600c12071000303c9090412265118001300001d440b140780400091103640e01102140080c40b030003440001409000c4c0a480b6507013894103202180b820103e0740d5518660a040d080780c4005d00c6045224000c254905849050500030f504000c5a40420904c0c458031000005001503690b5080100fa0b12030740d050384006075940c0940c02e04100c5680140c1000b800360b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 65515128 1250 65513878 65513891
    0x100e06031501050c0f15010e09070902030411060406030504050c03032109030702060703080a0e0a03050a030903030e0601120b0928030c0b07050306091302130f090804091509 76
    0x544406046a92204441600d121000c000c840141d80d14000c00045080318810314851100d010400102000741c9286c1c1c4d50800c0850380c2e5000240e050301c8084407990415044618100102482e540155800503c0b6070840c0890350302600108280d030300150710100000392581f0500043c80300078041d45010700742c01d6015525200004000381120240d0f26030303410017850240000b40c209407003401941c1c8074643c0105400d54640740c1d420000d1142e03030207480007104646030140c0c800300f00a00203842d81c0219416240c290070181c08180a900070142d225040c0c080c59181c1100e4040300c10140b0695019044140d9845202034440c14031408200c40100320420700e0384990f0301c4040c01200c2c0c10009600d1342c000c00c400302c1e08144500d012214440107603001400c0540d8501407140154204000d1842003005aa000301c1c19561300c40c110b81c2e1012030244c0690821109a1600c0224842c0d80182100d4400c05001041406040c2d03108141a070169002d0743c500d56960300120411054102240020882c000c42030200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 65516378 1250 65515128 65515157
    0xe07021c0e03070801020309061807050d02040c030209040603050601080d050c0c10020f07060f031109130e01090b090102190206010803190e03030c01140c0a1704031b0c0510 76
    0x30044840304018030248800a03841a50100309110282c01c03401d00964507820040c50884e62000191800f41200a800d01030411112000412408844004065000d005402c1d003c0c403000302007503a0240101a000c12004156484d0b43c002d220040d48542d0003010150b240110407400d0642d00c0390040e0070800b04000206aa01000840f4480003030f003150083c41d4003141d650289e03c0c203a03c642c0e40b460756002e5124005903158200398807030586c074140e4a003400388950050442580e07202d0525010342c4030710114141d070202c0180b0b0b0f100c0442840c0602c000204007400e903d819601c260b003140c50f422180c0d000100702a402e84030340c60420040800b400101383c654100313200c1a0302d90062882d5412041c0c500004c0c519220f2040c000000d501b81c019080d60303136443c0309808050107020120240d6204c0500c10000c14600e003103503021030f114881e059503826040003004c880a0703030340b84015100398104160915041100e4000c0201c80f5a11807149841d100c03850315110a01130410700310384414007170209201c000c810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 65517628 1250 65516378 65516413
    0x5010b070c181b0e01081305190c0906090605120303070504060c23101505010f1214010609080c0109050d080a02120c010905150c0a050a0905130203010e0702 69
    0x594140d4400c2000c098030349801c000003840200100910108403400640e43c180d00310701d26180a41c802e9840144d50364610a21858000310340d1001400c0d41d110041d200c80c0741c00001604285144100040c584641e507815400381901c074503801910440d655158100110b18109800401c0c98000c41e01850651400d4900034106004a210701418415023302100070000002448000d4640c0c41000c3c078201d00c81025015500c041c0c60624481035458441d60500e440c0028030068100d071030585d900d445a45c242300003101e41408400c40f249a242d140d00700840c04218100185001e41116940c80f80c4051509901501d40030038900800d05219008105120b20b4a40381d01d1082e41541241c8490342e54880b2400c01c0380780c03000c110342040340d450012649980f026019005179405902070003c40c1d00c4462540c0c00560ae20005507101164803208106a41d482d0b070040c0c000d00030b80d4215003031060040d07039148042102201807031344c184010ba074008014803000011005168000150384014a0100d038040107106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 65518878 1250 65517628 65517653
    0x9020108010302010f090801020f0a030e0609070b0c070f080f16060c0f1103060906090d110d0c0311010203010b040501030e01181401240303020d0c0308010b09120a050c0405010b07 79
    0xb0f0401402d0030320245498024146c000041c50620000c6690b12018110f0041c190030038001075001a0600c4540d03010841c1c0041d01c9030007010808068003410340390007602c0300c4650008580310b909001e4040000f411848070741080005005000c09800399214644004e410071614241865003d900800f06014065114018402156004190f002c0300d03201420180b11102002c0401607040c0307c0d660030445500c602007011030058400008460302c048070369100350743c00502501c81c1c00c86a03000300c0560202e148a40c49480c4c0190090400c40a401e02c0303101c0301400ea80c003d800c10340d450200000d0800403940d061050381c0405400f0340081156030b0100212402075401070304090001e0400040d1810107540a6026940c008101d0700070320b000480f1400c409941500500c010380c0035000c1d50512031480c3e40074103084a0020340c141e8401c0c50356824101c040c1800c0c0c2001001d0b540023a207122001201d0181041000c01f92030040d8010590004d0703400400098900c140c120326061036090001c07100050b4480d41d00b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 65520128 1250 65518878 65518883
    0x609090309090c0705010903030f0509010902031f09050604120906090b03061011010c0c0c060e06031609210b0c04140904050109061b0906080708042a0815060301090201080103 77
    0x1102684a81c010480203004e4020054980d520780025101007582682c0700c0d1421107800388007445160b072060b900c11b007201e00171480030f5095040078007000b150280805001008400d2054000f0f0303080155101c0354500031f011281243d0b1500807002c04441c468000c80064028405490284061801e14029107910f02011f020b00b40105010351105000c1400341045030a4454000300070448091204070040000d01c0181e0140d801c04241da00100da020300c2500300200303c07180500240e00e503440d20303801c120610102c00050420400c2c2d569003c80c15100c0c140b55101c0e01701060300c0d0100120050300f00b0900000014208034203031301c41040100111200d01960b5996607134115140c0a09658030b00b4541e01411016100412451900003c02c221050b05402d4900b200d10070780e00c04506a03140c84061b10b0f245c00686040c00800d00040014001960000300c400c182e16280040900b80c440c04020003140070400c2d0000c02141d0007102100102c0c560500485031712080480003404000302c03079000648040d2060101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 65521378 1250 65520128 65520139
    0x303022a0f060705010e01020a0504090f0b0d0308090f0a080a0e03060405070512030c070807080d02060606090603040807021f030c0e0904030e030304120614071106010e06010c020405010e010305060609090309 91
    0x100c1842001c0d0301038401b02d40f0720f0380290b56802080310000c001d6071080c042c03a148149403200080b40d410b00740c03207809501c550180094198446a4500b5924903030002d24002c410f03c184001c03211007403400e10800b9050307441101056220940224094030a01d000440540241d000100308804110700058010858206444880031350600c0c07142c2e10306504c11890780c3c2d0b082d8814007800044041c0c00050080440320580c0c107842e415210904102e0322400152411507000e00c1c240040141840c11400454100b03104078003013442c24165a0108002051803001004d00082c0e2060344840703141c03d801481f40d10042440d0030030300f40030740500080900c04040d101508010314400d6040c2d09860030030481d800707405110030b03003103050b20246040c00203401021480307540d881c4508049011a8020310100100341d245c2000741610343e003400ea042c451804000c1400d0304019003040c40801603105c41c41014082d1580c210310345690740c19418214900600509164000c0c09081c081198400c408000e907441d05408564 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 65522628 1250 65521378 65521387
    0x1608030f152b02030105180115080303070e01090914040506010602010209220e0610150504080d03050627090f0309060d0b01180b0d0b010e060d090204060902040303022a0f06 76
    0x1201c15030b9038903826009400d58030305001d12882198034000c1004404290b4000d001c40d203030400007441000518811000681d00900108010f1805075140584540c8185014402540d032801401d081d030b400a046404501c0d8804c0601c010710405006141c051b142500003940f401900c80c01288000c0c01e600703a081c111681540540d0404c240075085500280640c00880301641080c1c828031140301614480d40c083c2011000360848064080c0094500b1145c01c200a05070400300c48905401500c0000c0900c3c0d030024426120985040c0607542c21312441010300c030408154504150380c0c6141022015200009034010320039aa1240d980d0030864401500c08000414440c10101c01654841c05501d614800084040f030040703518079248c4007800746400b103e0020b2120010b48001900c0c2854207414007600309004000d160400a02034004647e1603202400003d001c80ea80e000c405c0890304190000c40c01071b000005d001124080c10803501e0382e83c0004140c41e074140390049001615070ba40b20410180215400705 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 65523878 1250 65522628 65522689
    0xe0603060a05030a0803100e0c030103020904141006050a0902040b03010314010e030a050a022e02160501090c03020109060e06031b07060c08061503010e0c0f1608030f15 74
    0x2403500020403003d82101c882106510380700405070400c0301c20705004010400700042c00c0e03100b001074900032051084401c0c0b450f400d540920604541c001d00517242c105284208414126003041140c0d42c01c1808000004d07524107180c1003049070500340c0d000c10317281401804180911804001140e045940c0405c040381c1c0b400d00300e501d00d0302400c01581c4024050001080e0840819001002001e09014550960303009601c1d0340c40802103060705180d101101541008004044030b85a401070070700100a1404203034003069070380e07001d0942d02c0c046d500320313000d800f04542041103507003100c1070001070030303141c1450018000203001044071070000034441c0c10003071000003030038484550000c21218619002007090040700d1002202070300340e036000d0310701034008d400890854641002400c1503c0c16101c808041c0002902d40c00302011340b58110010104841200300682d1004600c400700340821180705184036a01ca2400c8682e103d0001401000c8521110500134803509030b540b07106441e05104107445841c040d05400c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 65525128 1250 65523878 65523889
    0x810090302100c031b0f020c0907140409020705010e030f0708180418020109150e040903020c131a040e060433020409050a0624050d0f0b010f030c0e060306 68
    0xb500c1d2240e08903d0690740e03540c180c1e0b05810200c00328102ea0300e0400602070b01e0a040b54030700449442e01c001600101c400200034a002d041550300050741d4a00380c1c0000e082c3c1003169420341d0150b408071004941c006030002c2008401c1c003076007000480c82c102860903c80e10029403110b510030200b004011200014420a00410551240c3c0e070400e0060010041d0347c14403000100f1142c1c01c854180c0c0418640c000028440c07001c0450540f6280c0c2030303a030340c02c1c05c0e02c9003409010140c402500101c05500601e403d400d0300c0e4581ca2101c0c43e503801c4083c004100440e903030810b0b0a022103500303d030710f0045061645000c0320301d40000d0b20341d40085c3d1000c5118511220341030740c1202d03480f1055101007000f0140210140b10300f070035006807081c4d404040e410442500e1b401c081c601192401d1290405d001300404000403800b00540c000d4122031202c2c02c043c0e01d0048a5541003040311102c0b039460a5040d0341d100026200e5034001c507400488009414200008010240064030305403010340070501c540f0000000958a4036070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 65526378 1250 65525128 65525143
    0x405190f060e0412080f1302040209040902090903030708010e0424060503030c030901140705060f0c0c010c03091101090f26030301030c05010809060f0105040203090c03120a1101060810090302 84
    0xb080316040ba09151070504807200d4030100d50000250780c44c0115028580d00b050560080070f04807000600300e0b11030f6003408045e41005400c40e61040e504c1a01c032025071907940c0c200d4032410540000c0d5a6915200c8806031541c00c0c10307080340c040c40d5542410000080c859843c001f54901d040c2c84d020441d0030b482020000504025008241c06010108010041940000c0588880301090320340251601c08010000e259019900014000d644560041074001c09101d06c0030303410030300002c05180340020b0f800c1c1c041d081d1076040d0408400070355a85020814440d034941c10164440c0240707005005d49182081000714031030a40038100c0201500382c0d06243c0d03c10884851101a42004241c0780c40c0c0da9a0704100d44010b403035100700e6001c580054002071031440042030144c4901d2401d07062504030303402e1100f0f000007900001c04203d400d1082c00c0009050b80d84c1080583c0b69000c2c400440b503034408a1040c002d010014055444501d03a0400109010104002c41d1400c00000c1d410070011300c403c0f060070120700d040300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 65527628 1250 65526378 65526389
    0x6060105030a0e0703030503010815101205120304050a0b0105010305060f011b0506010e0105010f02070f0b07020406030f050607030f1a0603042405040c172505100804050c0405190f06 80
    0x581e41300008141d045030241d4121100702d410340f2071070080030032402c145150403100380d17554102519091061074468044051305500400851f03002210020150320142d00540341038480760b02087c00001081341a071116405072030300303103401d000f617040403000319100240c2000c115042c84004034400441000803108014040d40140464402c2d51351205a8900c56900707000740e900080c11107420395145400081d000e400c9415500c40d80b800700342740800f400250340100e80c04a0b0f22a458900000c04075200c80c07000d44100d030050001d0422414582c0c1d01a044500c2561000c0100d414042d01020765105000e0a84a011060303e10300d43ea035856103014107044c0011142c2042e0380c2589e1680e0296540715a100503c140d103d01c90b01103280340c60f405080b102910034640000c0c0340d480903950b08101e07030410340a41c9001c101d075501c5055451b1608001207000011040020000e402c202c100418040200060a19824181c0382080642406404001607041d40d43c0c8014a030b544804204000c0c071003641c0b2000041c81c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 65528878 1250 65527628 65527633
    0x3020a020f0402070819051908101e1a0f0d0c030b0108150f04090803011e0801110301051c0204020408100b0402030405030403081b061006020d11060a0e030d020f12071106060105030a0e 81
    0x8c09041c8086c210000541d0316004038a0641c0000c9081c0e49022a2a42c1118010703048003e410700d4075100b2024884843c28603040c55000b402111302d44804017002e02054610800701181c91a80d030742e4001d08882d41071151904003c480c00902481548d00c44421582000546440203403403203010100703001d84000803006040460001c00081ca8800000028084442450014210640d101c501900341c845600040206400400c0100841c0c50f01071070002041e0750302103041401c510941c00003400ca1b00554480402c5410000c030503442c061061041100140048030214154205912415543e00981c000185190400620380325038034068441c0b0780039220260110744441c0340001054203c10118423600d0090720a07180f155028038052401d00f07144d108403400500071383d40e03441c2849018082035400d1500d5230001f0800074948001c0c50004110f42802151081ea403070300c0784166440241401400f18082001c0c1004513100180013042039600403009103840d50701c0f40c03206140c0300008c2190590107080b0341f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 65530128 1250 65528878 65528917
    0x121a09010f05010206070509030309090910140a0b03010204181e181104090f17040803031510050c03040e0a1404150b0a05090a0507051603020a020f040207081905 71
    0x307050700c81410068030003e0b1300b514100d440b1904252440d00501c800c1907410340040c8008e500a040990890340d014000e03074210383c64035510702100005c0352019030024840e8980d42041040107180b80c0102000807100354021451f161a115445005200b81d41407c4a00d94660401c01c000343d0b03142d00d40040d4040b01480c2040a9450400840134501d1049421103d955011084000d1841d141c442c00d190140c0082c045100c1e83e1031580c5180010f0f4142500a28013007081c040803a0841080010710f110300034218074180100c4200d001c001c0d022542c04411402c00408100d10800390801000756011605011048030781034a40d030500c040030340411982c0c4401c41020704100300c18442a1001000444036664040103201903000900c401c0f441d5500443e5080007080011541341c883c50b50000394000176501d042424540032404420032410390000540041c1d210388900019454a55034070386c034001003210114604406680c844001c0e0060701c0b03201100c1c454026940030058021411916070000c2d0300b1120590 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 65531378 1250 65530128 65530139
    0x150f100512150a020f030a1d010c020f0c0a03030914030c04020d020919060c0807050a0b10080607050310060e010c06050a020c010e03070302030f0703030b19060e030d121a0901 77
    0x40382042c414881402c24900c0200e03101c10744510890b21200c03a0004040e02c1e50343d50314070312005800c5005642100041000f80c11107204806e00ca1060501003a6000d06515001e000c000341c50f04100c41e0929100303043c012020000a80c1188c064000c4951141c83c40c104003440d000041c0c00c1880201c0b9040d005800000c4030a810382d090742c010007541104407001c032104044109181103000d40c034026500401c0c801100300c80480d41c04030213405880e103e102201e4090800740c3e608860701c001614085111800110140900181400415400701851a2a608510b8152600107504120340320300c00a1140750810310bc0702d64400c007007440e07000c3d40000c400c0c0041d080c206c1c16100294400c04401100754a851140d000c10300000c4200c822064241c1d00441c02c000d1f411844800790751100200324141961100c004104d902c13061820030726880c070101e002c2c444500d4040050410782d400011f5038441e802843c500040c158100000001e0f5440303555001034420f04d0310800c81c5c1410520420150b024501e03900010300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65532628 1250 65531378 65531383
    0x60919030519090e0a0905060622110702100309050a0f0501020c1509010608070f0306052203030b010809010903081f0b0c070609050d080706181a070f02150f100512 72
    0x3c503540c04a03082c80c199945c110719401c5a00718080244243c1092011508a2802a900010610121420010448000d43e00d4022110000c0703000030030150129034002035103031003100c07081c46480702e0405020101d034941c5e5483d00c2e100d0f1104020300c50740d9036000c4030007449402d505698001d060202260036510300880464510b90742141d14512a40c20144042202000030549100300d4800450000c2400d0442e603d5401401c4010802e521141810300c00101070700b000e040f403481c51406520005234032030005000411469000b821407a45a06000032640001d5011100d154031261515009402d01008003403e0007190f05070f44600f82d103035004a40390744001e0010491038100c4550b500d401c40b00f00c0d42d8006210221900302400380c04141c0512190000ca5410341008851102c03580f25800b03042030b26034034903100841e40f80075841100007034020016425000240408081064001001444c072819204a900b5a0052502a4841025002c9800070840e41c0f0400041d100c0100f5001c40821b009401030b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 65533878 1250 65532628 65532647
    0xa050108070602070e0105060a020f070b0304021c0f0f08040812130f0503061906030c061805060405060a03230403020303100605070804060f021213030303050603060919030519 77
    0x14850700504a00059141c0000303681c000f00c07499408646042d81c83d280801026800070f0201d032056000b8005102003403442071004502070b18945441c00c2e107a08050060002c0d00360440040750141c094200d4180103e00020088110315901060311100320f0614030304400ca03405a50b00c4480e081c850f0000c5504109404000303000a000d0383c500094117942d540d00c21403000616031003600d406400c2140031509070091100d00d2401010361000200e0002da403070792101d814500b81c3d4003260000e80c103410444407860940d0216401080d08584680c10281440c00107240ca00c50040c400d81032503554031601e040e0008001425074855100d8040c9074083ca050305000e1b4481e4011200485030701001d140103d0746a00850540385815003182c0120b04013400d2074025542e139000c280c1c90209600c145500c0060140c4960001e01c04030001643d444200c1e40f541c507010f000d44801502c034901c242c00003010071100300c40000c2d03220b8515407952800180c4280320300f0191001c0c4507424000385500420554500c0040e081030056 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 65535128 1250 65533878 65533889
    0x7140610030506060f0f090c04031208010510020c0310021308060a090c170d0f12050103060e1204180b12010903020303061206040240050a0c0503131e06050a0501 71
    0x243e0459a510013080350f00c42021084540c4410304202949060401e00403144c5e00040100c1d12524040d00d0f0340315200c0700b40000300d1803c0083ca03548010710403800c2c500700b0b010300940c0d640010003050301050002521200840044070300c46a020440510f86140c540d001c00040c6016000e481030b60400000080243c1041141540c8141c40d401c40000d450300a854100700e03001303c9502519044401880c1180c114026680d040c0810400800c01c5002d03a2043c403a250003180704000c009480d00ca244015401c0c411012700b00070018106010030822000317440c41c5a15000521140000c0400c28103001560415907901074501d29860200310108141d0000011400394604485d101c0d50304100d05000b65aa0380c00f203d009404c001072107000703110404580e420383c0c064080344005030034010308505411201400104000d410988032014012408003e11880601c1034091401510710310b049844800d40304091034005118100003400c031000250b401400c001040e81c01102406182815401078002c1d010a0180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 65536378 1250 65535128 65535133
    0x406090209040506060c06010b1b06070c0c0801020a020a080d091b05030c04180b0403140703030203010e0105190b0904090209010b0309010605040c09050904050703050f0610060507030c08071406100305 88
    0x1213182450184140c80490554000500c000d0f030074014007103a69008602c0d04001100754820302a03114106124542c810b4000340da038402440914200600d15400c50b6003d0312840c2d00c1040020074081d03020414041d00c03600a4117041d541c02444441c400201f04c000c8001d407120007620b072050001c0201030201401c940301102220407000c51101004225800300008043d550106403403000010b503150442644030f800780c141604600b0301d0354100c41d519402020100c0c006035001005014414890800c0350140009540707c0c0c018180b400c1303650350641400d025110100b4008141c100320b50791a500000300140d805814480b580d6034035400780d0400d0f0415a469555542402c1d000f20fa44c0c02d16200300741c001c485940e6061900c9150070306000349900d002d0015a080c0c01425030200108001b0040040007000150040c00a483d00076a02d11300e4407803a400000400204009000c0401d81c0000200d11031500501603907a44d04071883c0249460180c001245180c3c0103100820050f5118011a1700480b40580c05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 65537628 1250 65536378 65536381
    0x150c03070e030102031e060a03021c1b14061c0204030f151418030702040905060402090c0a02030a030e0f1203011a030118051e13110916080c040504060902090405 71
    0x100340c02e0b03000445050641c003c803206035460611146c0c041c1d541002000e4007212050b1307140c0d0041451440b8658241201400881243c2d0421070301032a14a0403c1180b108411f070a820901065001d504060095118010100748000f441602d1550800c294541e04003c550380e680c0d9161001c081103a1010030384003002c440c02d030031082078094043c0c103000c0c204441801126503501921407007142c4005007103038040e00c001d200c2400141c031507100700b02c03805008200801b850b241c240b0400003000030060800b10ba130101480b5205203940c0001c1a100316000504000c281c4032101d14001e441c2081164000d1042d119280403800400000070040d4140c581200029440410005010343c0341d10081c41082103a2000c850202601d586039444a500250344c1c0c54a462000340c413090b18200010145c402000d240c19103811042005000803001503039090580740100b0602d0240e42900e40c540c2484204428852007030000f84401e40040f04940c054800240200032154a5414840003034215003e0903018618040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 65538878 1250 65537628 65537657
    0x60e090708070206061905041401030605060a030312020306150a080103030806150403170f0409020307020601050d020f09060111070905090706050405100f0905060705030d0c09051008040203150c0307 87
    0x140c02902c250354030740080000d07440b03401c1403200c0c0e070381d00d5041a200e80c000008041180c2d95580501426031b80340b00c0e032480300e55066040c510201c2e20041c00152080b40010030410010360003051103056107140b02d02c0140c4980e100004190603103c0246440341c0d00c00c00255081d01c1301d40005450707040c2c034000e035200d0100f9070300e01080c40b0780380c0040d403480a4a64410f020030400207884d41e00d20141c460f00040c07481d04020010b40c0c10246038001e90010b01c0c0030743c1c01004100c0800c0d41001202d00500e000c545d000449402a00401c00c007042401705140150100e1000601c03590040c0c92044000213400c0c110b81045d0342e507012400c01010262900507850040e100300086440c8100c0c00e48080d02d01c010001842a100d0380c0f0103a801280c0003001c102484144480000d0301e81e900c0c400f0b0058140584091a40c6565000c0c540040300c0340490b05c0802c0c440503900900081d190300c02c600d000d000761030415007029140c07800041d150680324030700114600c05041c1001080a0f0740406140501ca02d6140c3d043d8048091 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65540128 1250 65538878 65538887
    0x60601020105060f19080f0f0c03030a05030f06030a050d110f0604170a0201090c032a080c040f3911060604050402280519030209010b03100807060e0907 67
    0x151a007541c400d4406846620341d291640d4814411414482003028160b035442c4411f0030104c1e58071078a03005810001c29000d42e07000500240320b80800c1107000d5460207144000244c0381c2c1c00301500b81c242c0c03000700e9070000d220b0383c40802c21240c2c03068001d0200c5031700340c9a009000740300204404840581c1e0003060300310030b280304000840d00e003d40c0c3e00c00041c00c107508071400280c80c29009444501c04540d2240005004600c0c5400e4100185003d0f4290304410b81000038004d50904c2042824207072107110590800c51601c000c12600554a012280401c0b10303030852000d00b000c0c042c041c4e0702e5010310b40f40c65845040b031a400900c82c1800c1c3d0800e2020418000100002e5412601e4400e004c036907170700302400088642c5030981c403c5030b00074401411022184541c20310f002c101c40c004181000042017511040c8098540601e46141c0341c0240d2026806050441e404954010010304c68804070000101c003141c00c1c00703003607052400904075060032204855552540100b420300c00c1d02860340240090404520518800c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65541378 1250 65540128 65540131
    0x6021c0b0906190b0a020d030e060402010903021014041806050904050705010309030c1a0615040305030d020a140c01140703091e0516090207140610060e0a03080a030e060601020105 79
    0x60602486030703112401d10500d041c4043c03024030400ea80c3c1001040350007602001c0c24007904e20340d006000030400110003500302c90729807041e50b110354011410003005070ba1010f542c805880e81942c0f03401c5000601c25080d03911405403148040501c0000c503002c580d0440416928030500000b040500816903200300707002c21213000382c801901c1500301e40c038144120350103a00080d040038420300d000c0102c00000d40b100d00503050b01901030340d5104600e800b8085607203442002c8043c24840c10400528045c5990707606a0fa85c8a02245415030303680204641030054081c812080051800800681c0c1e2040004003090081004981c08140703591180c0c0801d00c502e101c0c0c45410f40e0035034841d00d404049803c01080c02c406040122044a0b24410098410400403101400000811941a001d6280c0c00c0c1c601e4036003034864007880e000c2d04603030210302000b0784240004903010440e04542403c41545e100880441c41d1040c0d1a00054450070002034460110741d8075a02407400768017002e040d10810340b80d01004909070b030340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65542628 1250 65541378 65541401
    0x6030602090f1504030803040f1709090c0406020318060d150317160201080a151403210316030e070e01170a170d02070215030f010608010e07030e010b040906021c 71
    0x40504c000e20000d50040025500540517220b00b107010f25050fa518950017607410414000000d0219a120b12810500c03005d40d00034520001300d0742007a044c5000255070303002e4071244450030a149900300d21691600c3e01152030b400203041d41405128114040684a0781d4181700c01c60f1101d0170342510000c80c06000041d2000000e09039010f00c080c8240c0e0700112a00c030006040321401a55861603185a00c0907000c0060003405200880c40345424108100b600786007040310b0003e09200710a00c0322114005450450340c0c0502c040d07050808a441402c01203005041a03188400240700b001804201d00c14a04480c6040704c05c411001c1003005145042c2584484007040300820039410001484051500c0c94064409000142d10050400030b00d40c0005400c0314045c500907005400c000140a4101841000d060244c03500d41007003015549040e10488440a009250404140d6900090038181900b0b40119140090041c001e1000e689207007002c10095000d1030354218807440c6010413600304c00940c02141740111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65543878 1250 65542628 65542669
    0xa020604031101030b041b020c03060f0406090f300302130608070e1f02060c03040302061302040204031a06030c040603020102070506070c0f030302010c1d0d060e010b0406030602090f 80
    0x5107141c2e900c41d061269091001d05243c0c503280c13440295150361180d16402e03801c0a40450300ba4000d040301034182484044000e0107030300803d00300640c0e010300240701a00a503000300006070b007a180c0d08002c100031100541c010002a45110308010b45000d060312003d48003450072405010b40c680c1d0030250b00300e01c41c41d0005001101c048100300f040030b0165000c07551202d46800c2085407a2907200000780030440c2c031402d0a100c011400d554141e40f83d41049840e03407010044a00610303600b003a85001e50b807080e000b071040001d190301d00c00718811900c8680580d402554460076032002c1600120016440e8102103e080d4020701c039081d005522807815006420841b0b4040e0003400085041030188801640149070070761310401c000c08001501012103d030400214029800054070940e5030100070300341004c0c0f01010260300070b002c410500790f941341002d059183d40c2c002000204941e415140c0307030241084c0c0201ea5442807070140c00000380300b6290028420090200e506240440c0c06804000079404050240450103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65545128 1250 65543878 65543887
    0x20a050d0213050a020f07060f1a1507031b05010e0d02010618150b040b030403030f050103120309051e07080f0f0a030f05070203060a24050105090f040b090f040308090a0206 76
    0x142c01a44519041040280054500100b80f080303106c1690210900301c45542c2c0d5685e580342c001d501c6c1d2242c138044003544d2440262050407840000d4000b02c810f401d03000c48940010301f96082601403940741c80c0002100852a4041c070701410914028401c8401072141400741346035440300700d032062285900352549a0b48108261084071580300c0100380c41c031083c50008403990030200d8030340880d42c06800200403034400c03959a0701e031034a401800d590300360302c0341203180d801c1c040180000b5010010041000c080da1800080a42c407908205180451034200540004500c0e5020098403101141c000b050b20352103030448102903e43e42c1d11030303500c0403085101d013119000010240d0000744108410080100203203080303401c0014940019081c01415510f24040036070310040e0080c2c0130a050f2903548040050241c58800da894000060010322950324003074030511070440ba108090340d49610030701d041c00025182d24005c2c0381501083d8810b4100303882c02d50210302480009064403500065062200340c2c040c25240c2030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65546378 1250 65545128 65545159
    0xb070506092b050c03030406020406021c081b070f050d0215010f05010e03030d1802041107030207140d1a060306010519030204110c030c0a0b01050406060509060c070b03090307020a050d02 82
    0xc03080c4040d0104200282040401d13600d10702080514092030090740010390b500d15049010b803404025402408001040c1e4400080e8150882001548803085100304404004800700c0300250f880344103401003200c041c807054102407080c000b803404000300e40b58080f61aa424030504c800305418007480b541e6084050a00140402d52183d0b4940c4400744028044030b0400c12141c030294241c801c42d9104070807604046104600b0751070940130f120044032201340f48500d000101e0310029250406801400c4a110103205507250381d4450205c04560070360412082622601d020103d6a0549401c0d0b459600c80d00c1410700102e01c1d4a0804400b0003000c0e0003410700c03c1003d185034280409440001d05100e030001c1c1c2440941d0344042e051000340031034241c40e4058000c800042ca4000003092040c0c10450090380351820600490750040100d90030903108846440d12442d003c00d00d249055050380124646070808000d01183da0000070162103403910803640071040c0740c0c0b0b441c1802101c510307486029500241891a0109 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65547628 1250 65546378 65546443
    0x5010f1a0702010e060d09030f030c050d0b030709140105150f031501030906060b1306022d01060503031c0c0503130f0204150b0a09080a020a0303050c03090a0b07050609 74
    0x22020302c10b043c1440d00b00b0307100c030001d1059049400180461130300d844245040540c09410010f0104980c1010030010342100b4008256000704100d00d540ca580c3c49040c04040c1d50100403910041c25450b41c24040c41030b803d000024141400e1242c18011000d480303140a21844003819112201d80410006080d40e44c0c60310394440703d0702c40401503414141c0d0790291501068260280c400034110500c40d0030783d52001286480513220403039000f0811904009000c1072140a0b650b01900002c030410720040300381c001e40c1a014014520ba602041d40f500c00040c8504000b1300c070b0303089002c0244030042e0420042450b5141030300c4030312040780d45400341070054070383c1e0700007607114a00c44025a0020f8000070305c902d56040c581200d800c043d0001c50035a440810014a42a1720190040152121002500311800a5030100c5d02034006c501005060220110311129140b00c20829100d5140005020022980da540300c114030b254050007060701c45010b00b6000802c14000001c40030740c01038441c10482c656249401d00e150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65548878 1250 65547628 65547637
    0x1d01020606060a03091502030105090a0509060606070c08010615090801050402060a080a1815150f12080c0d09050a12030905061b060f06011b0f0b07030605120d0305010f1a 75
    0x18540d0302e10585004c1940201b000302c620710701c2c4c000165a54103107410802c002c40000d04210070b04d8100800c0120401c40030590941143c82541d0240d1510303040d1504002810254125220540c41c209001440101820f82c2d40a04010703610350030025a240c0c0340c4a400e036601102c020b034114a0030050603d1031340c0b04000070399010445c2280060485032a404007041540700386070a43c0c150780c4011402d51080300074442c14035450030442a141c0e038980351441041350002d04e88291041c10309012942000d0000e00300c110384405c0c3c1a2070584404035400c3c580a000c03210240100390164a0240307002c103c1101d942c0100c0039103609920b17000185450981045015805510b0300a0312841d46085240741b51401c0000c1400b9000f01042c80344140750440006007032320011010030b503252000e409030034046500c4040e92894103030000740054055666400550141c001c6520140c2c11030913419900c5894440032803040c200c102d00381d40c140060b990300d880016076003849010340098400585d0108146144d00f10081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65550128 1250 65548878 65548897
    0x4210219020a0b0307020607030513020102100911090f010602100c0e041d0712050d0801030b162307031707020304060302090301110c0714150d18050708010605011d0102060606 77
    0x20b0340c8903920f590007511a60020394070100507a0002040c02a016014003810340e00c602400c0350401c4002c91900000c0d030380c00107031095400182d0382c1c0c40c0c00c01c24403050189229000d40d010700551160708101000744502882441a200140a1201150910200b9026083c400100c2703603600708e82541114104002403c40368034088810f1402281040180000d00c80c460050581504a51010ba0315003045810080c8030100502040242c600500004903040903042e0440034111482004006c44581590390307100c18100c454501141c00380411884d0240340042400c00e101e695055207002240d0f17002c0c40455070580b500005a0002c0c03000780f0485c1e2003903028044d000c90040001c544200c1c04601e03034480d5807281c0c0d03c108068000d40320511070032020405200e805101503a02c004510003040c10402e4a0044204442106495036000e101a5000056081202c0e80040540ea12030740d480c1c039014020403a520803076001c103041500f0801000060303111510b0075041a005404c1507030b43c03401081000d501501c0f90 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65551378 1250 65550128 65550139
    0x21903060f02040f05090402030613060906021b010f0902031c050904020a020705280b03040f020306101a03010b0406030c1b0302060103031407020a2306120421021902 73
    0x490814028101020010100107a0f240d00385100c01c84402d019405c60360003541194248030040e1000944c3c0c0d43e000c0710051101050000610b828800380290880c00350180d80041070b0701105106a90a0a0512554000030010204102006400d8500c90f15029501d03800890036040c0f100d03030740456900303030340c0e02803038180d141911b280001412600b0902200d00143d101507400d00c0030b41420390540d1401c0545070a02880c10148290112407130000307000c0c4003000d80e0040045410401200c0091521560081c161000d910b400f04503c0d2500320b2502c168034040d403a100641000311100c0b000c482c16507601100075468141461020380142c216002c0a40c104550080040c0a21445081e540039180c82640503081a5155040017403d03c4a00c1c18400d6a15a00f000008010b0b80d8881c21903003102c2c80d01c40c085000c5260081200390350340d06216030b580c10450011303d40c101002c07040c030310911440c030030035000300099206002120010388032145000545c0c000f04c039800b81c0058691443d01414402400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65552628 1250 65551378 65551429
    0x1030e010509060117070b0702040b0607080a0e0f1215060d0b010608090106090507050a080718030f230703060b0a050612090106060224040602040b04080a120504050d02 74
    0x268215281219002c070580c10020050044032803101d0030f40450850b5900600c200b03420300860042520a83c40024481c9a48030030749149905d45209031070070b540d00080c01c940c4901c040000078188800e815100c0e480307800c890036600200c7c5001000202e00400c200014043c118100d40302200d040000b400044c1c0c088110b0218000144031140054040e04c2c44c0e95a00d8098100128031500750b0718039801c0a24802d01700020002016408070540b883c0000031300c0c080d01c0b240c480050990f417082a1000c01d48140503120070100500407010706414000f4410b118000d038a021000010325058100c1d0304210490300810300c00c10100e0940e40041484160090140710303c80c2d60344000451a030b0117031904141c500407010400440840c28407500b40101042d00290402d48848010b14401c00f10200320100d000d0004008903080c4000d65060700c001e00441e0070b440703580b161074040599850b68040400c0340c040d5881c03000061001e1141d0190f808132800640544900c07006035080080e070804160181106038590340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65553878 1250 65552628 65552651
    0xc0b04020409050307080a0201200a0507030306180b0109080613080a020c041a01170105010504180207022107060302040305060f0403020312040309051005120105191203020606010806031b0108060103 87
    0x40101600f51041d940d42d80c1d200c0d50051f000c0d0035030b0140e0746045140000160b45903d50f409080440702040e020f80740940e80c44981d4a000c2e401050180c1140303248070000016443c06005a5000c12840c80098940c100344660b94696241c4e644d10840d0f01824850310300d040c100c00a9144030140801c03235454019556401a6940400c0c200d41603e00200508540b0b00d03c141410b58100f402c0d2100024030403525500c0350b040c0300003e011840750f88100c00501000c801500a06502541501c041076401815100c0710045030350001d5109030100341c2c441407402108400030f00c0502a20031242143d6000303000d007000c0d80d601d50340b119508200620603400d60004010a40032000c650650b04d208510a46035441664100b10911184a040720803030000e0210820103000342039078036a1560b045440498001c165401c0803002c401410006034800c080c1c54080e41061010103801181e4640700d01d2080c1d9034079000d555004105560380300c8540302c4080009d148202400c0e07d5206564040e8003120604000c20b0041d40b85 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65555128 1250 65553878 65553883
    0x21806071716021005182407050319020d0c11040f0510062015070507080c070501031512060b0a080708030403060f050f0f07090e07020604050708010203070c0b0402040905 75
    0xb00c8011601c1c545503206800c62800000c0200100800d24050f03050030701e0031001a90501415440c80e00c2545061200505560407403506210721201c968010f4442d240c40c41d110303940c1c0c1c00010301c0d41030402c0380283c07002c100c0740b0000d540441d1030401e036079041c2c3c2050251031341e804a5054140003034001d926984412004c02090041c80e005454000d0045102d91824100904901740f06020021181d100d95240c2400800002d0b80c42284c1c085000c807840c01c1d140c095007951030348030b4500c008152180203c1c1c4c08103014000716624040394400c0e2028486224481194948801d81e801620b9030021000406c070045100d55000c3c45004501034050300080780c6901c80a0300e040103580c0f0030031140c0c0c00010140308002c030710301a18141600300c4009002d1800c051f400ac01c0f05000c02080c1c1e54035030041100280c0750740e00c56503190006200001c0c01150908100300c0003529100201c0f01030b103051041c42ca002450ba20f05108880c828800b03035840c6001081595200b19030f0050241c02640e00c036803560420008103005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65556378 1250 65555128 65555137
    0xc0d0203070507030905040606050f03060418030203040320010507030809070302210c0a0f05060c160f060f0807020c010507211808010209060706020306240306130218060717 76
    0x3900e6290f141c120070b280040c0b4910303181d000140210708111040100340e8229060310700f10300d1003910a948076503803c40890000c1440004440e2009801800c0506142c0c01000400c25070b4018403c004c9900c030b031983c2e419002104460607900151040140d54003183c81440c0711504804100d06075900c81b682c9400043e01581035482020094031010401c50168008100c0009903013016a03108000c00c0c81d203c080f4240489074441c49000b0b450001d54501c0c0401d05108039050074520310320014030346865801182194803240a43c0c40851440b00d6103400d1540100c100602c5203145500034800b0f548182c0045817650410707002254003000804206031101c0410351008007400300c6540c0d401302450340407810558a5007a07441f41d90142d104110000340ca468400031a01860340014000d40d8907140c01c40800c45602c1049901a10b100709010346150602202005500580d07080380c00d16821100380d0380407801c9204802541c4502c6155410101b910306000700500003003401a06100203189c801070a400c0d46600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65557628 1250 65556378 65556391
    0xa020f07150908010504020d0204111e090108010e1501180e0405151e01061d04020d06061e0801030f050a08040b0715050405060601031d0f1506010311120c0d0203 71
    0x115100c550701c0982c1e12203a0140200a01c000a106500b069000700e4560950b501c00a0301a41c1c850400c0490100340300116411000030b80030f04c0c45c44600c0042c10215036001a51600d000941c000000110940030100060144800d0202c10740900345120055590040c004214a46840c4004000455440040b0068810f43c05103001e40032443d042c00905156080040201030008042c150303424002c000da01c640303410745209052501645021400806444801c25000c65110b4000502e00d10034008540204049034041e07168030080c541142e0803411046800c0c6041c20001e8104030042000c101c2100407400e0203400f50007918241401d0b81c42c0d00d28282e01981010060100c0010001c0411449003a00030aa054024040245040a0740c8881d102c1501404003030400d52541004c800540e1006c0f61941c160107050121001080e004180c140c0780e101581c840c03d00b40c151480002c620394000e00502c070205611f100568903003d0303140302e40a09104064018802e07200207010852080e00c06200540c001c1c031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65558878 1250 65557628 65557649
    0x13170f031006020f060712020403020a03030c0302010606080c0a2a0b0f010902030f01140a091803030614030a030c1103011a0909120409110702090c220503120a020f07 73
    0x542203072804200c51003940560119070100b88614a40c000104001d50071460300d20b860b03107001407242e00700d1010307000b6508040d51282d8407038000010150000103050803075100c0d800a201c0150354034400e840314101220b003442e01c010104200040303680300c0c40e081ca0031070179004640d01c03104400003d0840c407201c2420080352426494030501178000b91150000d801461251070940c0b45161031503c207007400c10107201d40c004025801a150517a961000340701409055040801c000c800c0f0030069444084519840c01d80200e490f0150106201950000c40140304d0340c05401004151126502100e44042045047c0c3c0c44401400d2a251559002e00400d00c3c91410507a84a9810300104100442840b0280103181c0d59448a813960301003a8680c4140c03002c070b488005d0005030503203003070040890520035000300a5101c111402044605a2518080d224440000129500700340c20f80200401d5411580202c543c140d015149200281c030380d0100400901c04903205980c0208885c0341c000b4540390480d0060745001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65560128 1250 65558878 65558881
    0xd050a0c0c0e010e0f0c1c1109090a05060f0307050303040308160807060207030f0c170307021005010f09060518010513060e0a0b030d091a0703030612030c0605100e13170f03 76
    0x19084400e9900803d40d80046403801a404017047c48501d48114081c0c1c01c203890f03191891451000310180d56000ca8090200e01a6280c0040c403040184411605248102034468550185090000e400c0080d00c0014000390316113411034507041c10a401415000c250b07000c1c40c50103800010040005006000e00c645030150319041076248c050015020055004108010140c04001003510b030090801d548240d440100d82d40d40311010708038140180c0c041e4101003982004000203a80d10300c410380c1c00c101d5243d90000c21406481d001000014201403008000d80c0340b0640050040c0c2c6400202d044e000d244403000001d0040d5503400c0110f1489048800c12074203541c0c4e2034480c405003400e01c000303082140d41c0d02c0c10410880c02c00030b2905110004d003841e200000c40224140c0b04140c00f03a406800940508008109400c1035458010034805040344100c0b801820000800c00c44510b4042801c01ea8011035811200703a60342106100004120b02010398501030241508031604040348020b0618030f682a069560300d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65561378 1250 65560128 65560141
    0x6060714030c0c04020f0a08060f0a060917030a02030307080a02070b0705030415050c040b03090c120709110301120816020604230901050d0f0c050a06050408010b030d050a0c0c0e010e 80
    0x51142070301c3c80c0ca00075801000103900b41010402102c1c43c2d400c450400301d4140e128040800d0a8081c0c1d5625947c0000559102090543d00b010b2024121140030103491140d039600600103460f03008131140c1d0000759200380081904140142ea50030ba1082d95604011304011260715103401d540029110303075006c210000240818810039400184c466000110140103c2c10058295901c503c00d1b031141e0110300a0200c081000407038140403810b10400020901441505072000c41a1518854071408080500c1c00807000300f01001c40090700d0484040d0341d10540c000c61b1584803010190b00002c40d02d8501c0780c502100c400140c2c3d607039018002a02c0d011400440f201d070070030300340103009514942041c813804042c6c00403c125591105c00303c0210364070604041002406190103070500466400495014000c0d181c0030a020f5406400f401c00c55240c08000c3c028a1030b01e80c1403644036980b40600030f00140040240510304c901803001c0c03284d01441244e00d100010303a038041d00c0320080000c0e00f200303506400c03c6003031000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65562628 1250 65561378 65561383
    0x10308030a0b0d02010503011a070501060602010b01170403081801020c0f1b010c110114040902030114100e090601050c1002040906030605100b030112060e01140403020601080a02061206060714030c 86
    0x100b0303450640360021052540d400182003800140701d2540060821980c081c1d00c0c98400c13050744e45669105000f0f205c0552241e0b0040e0203003a2514003680000c02d40f040c2c0c0142140e02c0a0711501507501a1110300c0310b61101e820f102942c00280c42c0d03ca040351f4007001404801107080001920800004002d824445612941703281c10070311545050307040000c18408100407400e07603a90f04400d800242048114040303007080314003c9001c0c961001c0d030140c1c8080f000184982054000030f20140382221031080d48a001d4506482c103031400c0750b050f5007201d1040c00080b0726501440c01400003031001c40c00c07980c0740041100c03000c0583e03000d42c0221002c15111074003081004440c0c0101c0e60031480061140407103900b442d0511030303140014464078900e403035502484024041d8031b07405417a1f40c281c064001c6c4114240d02e00d68647d480e1090718220010b12a290000961050105000c0c603d2640200694902034907800041c8041d00b01807c1a03034008000c000d400300180c404d40b6608034030030384007000d152500100a80d460 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65563878 1250 65562628 65562641
    0xd0b06030f0114130203070807060807080606040e070e0415030507031230090605040308041a07020c04022812060f050a0b070302010b060c031e0703080402010c050c0306010308030a 79
    0x20850b038100300400e04a4401e040c07400341c2c09113601a00f200182418000640307010038541c02003000b8010044080b60003a440704026100d019152259003481d02c8000920580380310f1880340803541c14203d40840c0d1aa407040d6081c01c00c0440003000820b0828111401110405a44e80100d4003640170840400c100021100080d1004000d07041584000c008482ca285003445850300300115540640440350042845038030802405820100c2040245460b10f8081d09440040d94141d0760b00e09031104803001080c10010481c4034880d5940941006c84645080c80040c0d00058031400b11188400d40032203411180441e070b09108142035440300b42010303104000c034040b120305401c69244030061000520040c4c0300e0f802828200c82048105d20fa4421136424102d00400d4500c20340e5502080008540524200c004041d20404400e03945032580242481850007480c4140e60340100410007444c001801356000f40200e03600c0078055419030308204440c4000a040071401d8000b09d480840202c10710000800324401c18 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65565128 1250 65563878 65563903
    0x60405011202010c0515070c060b030106150309171810020a02030319020c03060a021306080114041e02280f0c0b060609060d020408120f09090a0207020d0b0603 70
    0x20021035040c03010703805601455210107810b000312a58000200041004a0101d01007941e21003d464101440000e2408a8865060360080e00b050b006400502d0180314039170440d4407904101020003403010040e0060001114107850060000e16004842c100384002068110b83d800c4034101070b00d041d6010442e0718802d00c0d10000c21940840d0803000140c0780002140e80d40140307000041e00300c0c4002c440480c07911440c1003016405010351014042c048541c3c1c2c01601c0141542d920f1a14036030b8070fa038000c41b100341c000d2198156180307d100310756100c1d080c10f0f07002d5200d0383c0d12803032801120841d059140090307910860105455400c801c1481300d00d041170020084c0310094501c7c012102c111500d500070000c546281020308144100340114801e079551004031112048041c00071600c40c8565030801009401c140728040d03a40c05410900785240c0003030000c40348408138000c24141000d03e00c0d002d10898940c01000e880c1240d07820011807002d42e440c0040341d4903d62140040101c2c03403604800f41418207030b45805a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65566378 1250 65565128 65565131
    0x80108030703141b190506280f060305070308030105100f050306091503160f0503010608030a08090109140a0c0806060a03201008010e0601051305010305130506070c0b0604 75
    0x1da002980c00821081c081e01c28040440e11119802c140744010040091214050b1245412411043c10000750102d04503014505079030450fa00c00f403202d44941d203188080501304e1590007210b40d012150741d00910703051081c42d43c0000c0302916560b51500d40611500150740900f004001080907140410748103242081901c2c0000200b0440c407030141150202401c114411440d0300300081182003505100c200c501d100800722214600c609a2a2020003900e0054242003080010082510f0405000d050122111080150315007c3c420900301c40600340a000181d880d521244148080342607100000d4020311980c02400e2030309200e04d00031184d03001a038480100c139008141080400e54403401c0d124102d9800a40320440580b42d159040c820f5000700c28002d50010b80302c248010340c031780d000302c81a0507601100d65400e203544031640151528081c1302207807118100b80001c1889554425040160440080229005240120b56945e0305006048842000149682c3d540c1e40030310641d144a47d40050040d1030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65567628 1250 65566378 65566387
    0x703050c030c0d0308190219180f0b0703120f021207080f0109020702040f020a0c12050c030315041509050702190b01060302030402010c0803150f1008010608070203090a140108010803 80
    0x100d1a0f0720880745015090090781000109000d003000c04100304c5c2a00e4002c00c6644484202031200d04032107012031540090b01c5c41108490030503200d403405040d10350340500030600514102e00f00445e50f2000780301300e04000b04503e0480035031505010320200b03040038200250b101c05420f5450100f8480c020400010046802c00340610f0403044041c0a041d00da13000700141e921041400402e000d0310703202039001a150300c001780e18189280e21a510742105480f0303803e40301d129804464211040d002d4020071031100d030020004540082c0308182c40604050b409040466200808039003c10085000d610220340c040e20780040207441a414404600d81404407010384503900c040351116649480305000b9003050580c0040880d00390380c020441703041481d40c80741150b65240741242d05131020300041102030303004518046004040d4903000d00141c612519a684004603a882d049040b01c0702c1401038620700a42c003007000b0500071502d8240b82600607021804850700d03030380080700006000c0001680b0180c1180c00520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65568878 1250 65567628 65567653
    0x20c21120c1c02160212150a060801061d06101103160b0106140708070204270b0f090303040f151d0f010606050d05190207060b19140904061506020703050c03 69
    0x4502901580540b070b503070489108415000d07c0c000e018024a0841d1503034008224500f10290010303000e64a0030320080c0059580e5203140d1001200c1c071481100d10510010010305c950910313000009060b08146481d44412110303a06d40c03411a4020722400c2010410007c6081c04e1180001049004290b54a442528038007011803c241078080c5001c028078908000a0310400c0d5903a0b600301c03100c000e08442c0500b004e00000c480c03020150103100400c0305c030b48040340c0c00160fa0302800009140305015075005103282d59210b03941d400a61401540403285044030300404800d030710740d500c04c2d0400d02d00800920745110006007105031600c91401c1120425078180340003481500c0c5d01c0006c0d140034a04107680410540caa440c080b21041c001d00700e900002c1403011802d04c0600001e41c0290094080a40e0b10280002c00010b907101644c200d40203010004c0d840c80040c125070f050a04c1d4096015011315000203407405410301004210140d40d20480060348401000c0c02880418000c140502c842103008020444441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65570128 1250 65568878 65568907
    0x504230304060c06021308030406020d0c020a0302090604061802071b0305120f04080d030902010f0306050a0506070312021b0607030c021e1510060e04020c21120c1c02 73
    0x60041c1d80410000c3c03843d0000b0005560107603004d03104011440b10301e241e10340034007554a400610481c1d006216000c08410014000c9034081515a0050a2800041d0170350b024000707400406044160850703a204000034401c85007101c1d030f0b0418010b0f000c02683c2c410712401c110600c8455a48048a10720840e5410400610b0010305a1040d25000780c0403030b183d1000640c0c000b82e5000b1684000741ca80240e1120007030300e941c141d0007042080e00c01d0321258405600054110203c3d1181d011340ea4120050080030301032840c0032400703413010b50320914040d0b000c1105400d009040c1e8204486242c02074840c50280c0c8075207c01400120351001c003506e81000414640100255604030880400c090380894080c00305200f5418010340f40c80d80081d640304191410274162885142903684240c40000d0501c82041400780782c00d000300c0348829401030003405480c242030240980100d0300c0048201a5100b041070052090140c000584540441c03026140c94110685412201800d03502c040c0f000688100440c400c0080030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65571378 1250 65570128 65570137
    0x306030c010c03140a0302070b0c070c09180c03050604060501051008060405070905040c080a050a090203060103061112040602030105040b0402070b1503120c06010302030c0a08060103060e010b120105042303 90
    0xd00e00b104180c040c90030301340c1340380f4280c0d0004d202c20000050744201d1a601070b0001c01407a44591000c5800760b8800c1e042480c3c074080c1e100c0007401c0c8034013550300704402001900b00390800003110f8551081c2c0a865035540020ba1090b03030013101e0a401c07400811007848201e108142c01002d090740c480808420740103004102e03600007400c8a02c519560008544494400d40402014080142080001c0301d14400054003140e01100c0d84a091401e0000080050030207000360564140e019004201907401c66940a002c0e050006441d826481d0500c015600500841c0b682e40c0107030701a802c0140e5950600041c0070995204651141c000c2d801008840d0000c3c0d41840b003107030b000310040c1800041ca02e041c030000c1d0420200c41e214105070300d03021402c10000b40d0b005c101a412244210308407a40307100f0140910051040d28401c095440e00300e40010000316000303030805101203003107900000341c45203d2800220558292a09401540c0d5504100010028071210504a6038010703803010010440401080350789118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65572628 1250 65571378 65571403
    0x140408070503091203030a1b020a06050a0209040212040302150408030c180402040602071d0c0a080709030f03030c11060609010504020705070f0303111606022a0d0b06040e03030603 79
    0x90000d9014148a018402e5030322003d8010032500c0f204040e03140441e620b03081602c007030101a15102c078181c7c2201e01001412001c90980c0c001d0130320007006403031300710007008018802a00c03e40c003005803040a550300e10040c41030603900e4008104505060030020329000306170300700c56072907082d40040c4000700c1c900c4810b40ba030203503110002681e40e40030b02843c2040040b00800c4e041e0000e0010501094042d004a02c42081c1e92950b400c404500204e15180c021045c0107691008004408000d00d03814544121a865440348490034800089a66580d600441040650055000990f2104e51040030359200100340b0200180400800085c100b20000031081340040c803031144161340c002801020014148108070040a4002500b1101c66603410013810a0f05450b41c0b6102d01d0003810200c0e034417101d400300f11206031056a0300511540d407070001c00c040140d046100303d010140107d8010365540d907580003505c82c02c61080880807074504056003807205494542d2000000c9800c14410443d0a41700010341000d4000f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65573878 1250 65572628 65572643
    0x203040504020a120e0c13140f09070f1d0109090c0605032802030402010f080709030b18060a0b040c021b090c07021810090b010c0f05010b0d051e011404 67
    0xf0b5501d402135422214030310141c03c41c94200a60780d01c1e000c01c00305822400c20404e403061400c0c120007068160491718885550b010011544000c9445003652450084d8803410b414100c0e91001d48503c0060180d000075844000c0402104c0100078038510091502c500500030845e00740400d1465955003030311100c80d030040e041040f50100005044503401c448540d000021960204414485544500042e500495059000c600399081100859104600043c45410140da0f01d4100d1130640c1e44159180c80060020075a50440032180d00e2003440a103c018000c040300400003038030145071424002a10000b400500035504032920b00d20002145511840c0103140403111418a80c0d55103a50f12107900803401e010b904951081003140003041090318060007040d8040403000403699484d449000e4030441004140059200000c160020701d40c084140c01161050001180640c40040840c1d0a08841d60042d22594000790060104a00503507510b001c1c50303d004000e0002d400a44450050514003034001032180c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65575128 1250 65573878 65573887
    0x1030b062a030409140f060603091b040f0606021501080303101a040b07030503070306050306040317100503010c0504090f05010503300313020909010c08070f090e0c0c060a0507020304050402 83
    0x78241841110060800480100b21201c840743c15a01030000454400c072190003010003143c8185896402c1e02d00c61100701004041c054100c0254610b9800d1010300a40c02544a140452080c3c03094003031400a4030113036000348100f15808080c149800c2042e400341600e03800403c14801c00e1409002c460054901409d04008280500380d2440c0301446103621804c00040041120820154000d0085d80900c1c1140d40a00502c2d031101c041544400041e200203001c80d00d124029140b00c03e80c146200c0c1d0000303410403080c0d500c56464000c2800e440c40c40306018009440040c5c1400304007540d214051444542907010484c541c10200485e43d500540f41818818005810a030310b055041c01840c001004d07510034071b464136414490440828288403000892148000d0400665400014450200d01c1200c82c2d813a1003487d218004d0580c1d1041d072040c400320401005140109200b0200b0001d20f000b0000c0c400782c190354440c001c1d0a903080c260702400302d0b400e25041100307129085a00009603403d0340d01c11134005a44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65576378 1250 65575128 65575207
    0x6100c020310021206010f02030a0507030f1101111c0b030a110a15030b18150906060412050f060106080c0a0f030209090403020a05070503010b1f020a05060c070201030b06 75
    0x1080c0300c2440b29281203000054040072400c1c0c1403100e81c099002a00d5007400149881000d903140d008044030b080c0021018003040e030229210f0380060b411401e16040605c4008003901d5018256020800b00c903903904800210100c8400d000d41c00a103800307001c10820082604940002603c420b2045000341140600303d51140030b0340e944001a100500b60f18135a40000c45210b0380c041c0180c526445241d20440c0c680c580780c881e010413008420f100b0711040400c07080340c10046041014002c00940641e0300100c040c080414483d611141003d0080d010784001d010580c4681400c1d40741140507000301081000100521413818031250a407400c034101400c02199480c0025400c90013402500d000960010004081c0030a03d5004a601d105c2280070358251644151108240341c240c0c2c00c0500c4280c0c20000500380120703048021988030a4001040c81595a5044180c0b0340307602e020010b45654408010016815003150b82501c01ca4040002c1035414506110646000101d1a0f5116660000e01d0f0605c071480c144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65577628 1250 65576378 65576383
    0x303010e0601180e191407030c050418060e0109060308040e06030a06110a03060b0c0d0c060902090103150509060601140315030303010609060318050c100504091406090f06100c0203 79
    0x70350206426030900034995460510001c4d0f4802d07159010003210f80d8a058200b024203000b8460702c1c0100701071040494940d050120010500c9414640c00c0203c280030108000c46101199007041d040101d01068250820011010903041a409001094684481000040e0502d41900c0403a002510000c3d11591040d0100782054518400100202d140c41100380030689420040d10709181c0c1c1b80c0c0e08220b25900c9058941541c07003150844015540520040035659100d0f030000c21005209070740104c1c1c4031205a0104101e030f1804c0c0c0084400d0715510a65104800c83c3d4403402e988062200020001c41c103180c4006810074500c20002c2c1c289001c0080020030700100c41111071074072a80034044995a40c0c0d00c00000f0148a5140602ea002a00b41302c1d0601d22840802403600c0c074650003002600c003102c4d40504208444804000940a200c03062200150800051103a1942050a540020034a2600758200010000c00800c0d0f50141d414001c24080d42da10344a00c0700d8000042401d04000500b06400000e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65578878 1250 65577628 65577647
    0xa0909020d15020c0106090e06090f1b0111010f02070327031e0c090203061206061f1b05070906050904110f0105040504050a1b110a03050915160201020606120303010e0601 75
    0x702c0175824802c0028801c4403d500c491442c90b02030090b20388035183c104500d5114100107490104542c0710b901542c200c50190704030300c1202c80e07050424030502c16655200c1c0d829200c0d8140803400041c1c0c0807a101e000c3c10b4010300d1401c14681580000c407850740c0c4880600c1c40e10b412501000e010700804200310703102021510030f1240c0550708800c0149589a40d24158400b0f9441200d4450060b10500b18540d0391080001f55280280001003016001203400540d4000103006002c41e0801c00003045001c80c05c0c03140014900c44200d0148020744009820286900c0940d00340d503201d1801901074034100030206124000000c0c0c4800215502c0e401b8661080040780e0070300580c0c10207035000340f500082c000c0300c0c282c9030f12622032005603501080b20620b090380180c03003003084103803002502d4000c0d010300d10000740328000512074104010641e200c001508080d480040d080400840d55040c81003581005644c1c0400025900101c22200b014200484080154480c0018411486401040b03030100c1c0103a0300075031151 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65580128 1250 65578878 65578897
    0x1a160309030f0b040c0f050f040522150c0f02100c0504050a09020c0601240f210f0b190501030203040203010902060c070f09020a0801031b030503180a0909020d1502 72
    0x1030750302c141c560500c04900b45042d50200d03030380c440c1180c0003c2c1c114541e1402030110781e4010000c0c500440301d0400c1c00060000100b6108241c0c5029049201d548141111208101d0040a140c0461000002d80d00c003150640c44c20329050181c0c1302c030b070100107950005030ba5143d4400102c000c207020031400d17029203003400b60b5002a5808000d150b03010030003c0d0716a028090814844d41125016603a5120725850144c1c181c03001c4440340518080e1001035409903141c1c00462203180b5141d00349010100121120380880400c10101c00d4440f0700cac002c080c00840c002d02c480305800b2200b500c0205900c0f107006007a03007001d01c81c5030706140d000300000d81555400e61001003e40d40181069903900480c2d075070245c450255000c0d0180c2c5900b0f142000c5000c3c481c9100f6905a03c0140d114041540d003951984000760300500e0108403400740c24040400000c030188007400890b11744400c180300750300301c00040000350201504030f030211910307098402e0013603500c4104000710746812590800d003c3e9031030f590f424080d1103138681c0d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65581378 1250 65580128 65580143
    0x10c05120406110709060e0403051e03010b07020102060f01052202090a030317010f0302150f070510020c0d080f0f0601020f150708280b1c0606030c1a16030903 70
    0x1506640207094000f00f08064415103540503100c41c080000c1798268040c03030441120000006002038003d000910b008088160705907500c0c030320181200e070264000d801554861101050841c06c65804010541c3c201c5402c6510001d10360400e804074080c6446d442113042c40c0d04040700340c081c1c10319055044849061001d000381440507101e04020f083c0d19086903402242482200002411281c40613007101903030781c002c22641c80c2040b00d003101c00858001402002c1104c1041021a000031410031071034483c940d11410268541503240521410001000c9811092100c42420041d103c240c483c40e255120400c4101901581c44500040b480c14825009100d064860310280000f62106003d56601c01c15055484140940d41c019000c200075407903030760010310412401466840c59050342c100340c00c1080044c00400600e04240d4010342004004001a901e0301e81c0c0710300600500c03181a0419000e0300d04100010000400d00f12007112501c20341e51681c42034012003004034101403141715500021030f0003119 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65582628 1250 65581378 65581387
    0x60f06030b10030506010608100306020a050408010c11100612061d031201030501050112110d021507080d1b0f0c020d020d050c03070614040509100f06080a0e031305010c0512 76
    0x804071030307401c050000340c0b4207211703004c00000c5981c880c02e0850312a02200400801c054034550b1410060b4014010080900c2401e11004c19120001d203c0d541c0000c1540c1c0c1c80500840178401003d00f401e0100707012203401070600c0c0060080a54019031401900d84c8503100088a0001c0d440c2140455511015031030280800501300c42d0002001d14414182d80c00740e03000700200d0740c0e269280c1d5a40c40d40d101c0700401061a0342683d804918000c0b94a1010500281071310034540198450106d042e07200c504100c82601001c01d201d98801d003d48101d403410654002c440c2080c000c030200113000031198201000400c44680c00440440d00c8016812010a60240060726030502904e840b54072070017101720302802407040380b00008050b4070a1a407041f214007200c0406292505100500c84038900c001e281064034507201000042071a10020100c000b0101661015801d0070214454000e54140c142e054048d9131060103500341d110710303400500088030801d081060300740c5103601c1c2042c108895005032034812040441c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65583878 1250 65582628 65582641
    0x170c040305150405010c080105010e06070c09020c160b0906070803130609060605010e091b0901030b100203030702060a020705031801020a0b07110705010203030108030409020901090308040306060905061c060f06030b 94
    0x6402e0350141e84250000c2c071180303d181030110f9501400344602c60001d0f01c004c0c0a003032142005001410384500880800c41d0454944100005a034000c03042c02503582c0c1300d401615201600ba98502014000041405240003054400540240644a0081e00322400040850403180c551201d4005007070380700c44d0034084444a418500300030101c522805011989040f010700d1141707400d5102520031107542014040790259820221b083d43c100d90340d013a050656a142040c140c0c0c0e28940700500d0f80e14154015a62460700c2c0c0c00084c100355020785003007d610300500c0b4100010f0404010394080e04071103c2d51085909a100040b0701c6c014101030050f0030031039020305110703e5a61210880e0b00d6001c045080f240c030660b40d18012079076032009115100307aa400521052001c450302d074006204000701490207002141d120348503c111944558411076102c0e40e5001c003001010207078020075511160840d03140c820301540d80341085480c0304501c40189065aa0000d40400314420782c09040035580282c4181258501103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65585128 1250 65583878 65583913
    0x40e070509030f12040e09150a0e01110f1b03070c03030305101809030e030c180606070213050901050115020a0303050a0615020105010504050c0c0706050307020106090c021f0c170c040305 82
    0x140283e50310f010080c00047d0b0094000030350214601701907406000c0955406011500808002e02c80c407030310355241c812841501c001e031009009060b59402240c2c2e13880c000215540c2004e58803415404441c0c01c140411008110054100c10031a50103050204281e601e540d90060311303031025049108149010076040c05014540e6001455161003520355036100200b000405646800040420360f10400810690451000c1004100c2d04014058002424280301d80d0020ba1003244210400e1101959842004511f0300c4c00d028650040441c481500000e11141000944840c0d68080c05020b0588030000b0904400d5664029802403061074041107c0b040c0321a0028040c00083c1700340c40c440d07410500442c2c859001501101c001c4844000103000c890310780202074074103400041401056541e204000100c00003d80103035074000507180d0203803400d0700030035452808480c40200c0d81500245403103040d107001c0740c21840140459181d01145540755850341c3c0384103244c0c4a01d400040c00d50198200914507011007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65586378 1250 65585128 65585137
    0x702062a0d061d090313120501140f07090b0a08041b090218010201060b03010b12070203090d0b01050909070806010506160f0602030709080d09061b050106170d020102040e070509030f12 81
    0x1c3c0c80001c1c2040e00c0b803032200d6607207000c0d2200c1c03c0300720441071508101c1c0111a000c40b01d19503120b1000840d424901000c1500d00c0c1d0b0b4100d0b00110305107600000c01030f0507940501c8942c090180c4001203820865107038002007540e040140000c04000300704840382d2140600004580080801c040150768aa442d16070304881125900d20490141d800c20308040395900c84c1e141500e05036000746000700d091050002002c40d464102074a52421f41c00100900d5282d922030070441001a401480740702000d516000c20f2103038018008284501d05e42001205006d00900030a1140c119201107941940752802d0340b101c1c10540c40340c414001c0c03d40071070068003000c2040d580c002d54840e010301e4440c0e0761081d94032020b00f40c0384d803040e00c0c001000902c41c40046c4902402904201240303e907802d550880f111140e40c425007104c2d13035034018495003021481c1c00b00010b0310811441c01107031402c1c40258101890801800146503001d030011042c00404140303032207652030030800004494080c1084a0366180301741d0010300180d11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65587628 1250 65586378 65586419
    0x80d2a03030e0a080c010b03030304114f0509070e3301020d050703080408030a09140601170109030905100c081c060f0e040323070b0a050702062a0d06 66
    0x204228074610b403402000b07072b074415504898800041d40c688820002c00359200711040307041c46041c103000640c054078409807142a1b0080b44440584a41c107020840100c1001e206ca00341082c10101009000c40c00840d20b681180d012540c0c005294841901b44000d40b2043c08500010384801c802c00d07104c3c08154540b20680350406c0e006e50b1042c04450030219000e100d00d00c0301601040c119008200000c15400055138003456a45000a6141d0740765a641008120f020002109030b00ca00018004518510b00082c101c60300b80e0000c1082842a59025100f2091840346a01c80c0d032020480e40c0e00d00d401850912841c07680008403541c0c800c5440d4100d500c0304211365a041015150010124070190080f0010050f6508280003180c640d94603a0101c4161070f000d0b08014940c80c0c119000e0301000c03941c00180c2903183c883c01680030946804e4012000302d40c0002d0241085521110a1200b0b80030b178500d8400d928892080300d170005d203c45000c040c10b14851000341d80d03081494454000b419051003c100030b14440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65588878 1250 65587628 65587631
    0x902150d0912090305070b0c070f0e090105070302090f010806031203010807080c010f120519020307031e0c0503130501060e040b0a05100f06050d091209080d2a03030e0a080c01 77
    0x282c4684116070400083c00000e2041e4030001c3c00f44012810703880a84529460b1000b200c0e0402e454020031200380120360310030080c0e29060000d10550b43c038207001c1c00d40e110005107011801d0002d4a40014000c0c4501d801141c144610f46000c100303252000d100e00f042141c12821408d540356034940c40d0075991407940c40b8a881c4c03405103220718101c1d503101d0310300c4d2110140380c0e5842c41405002e42d1800b600500f070180642c3c1800d144241e010210841d00d002842c818601c92300e0004a0b0f14400420880d00694580c0011000c0d00d0020551b031065004403e4a4100941010340342c0c52900f9454914018441c0740c0000d4120407490040008221142800501c501d0415600340710310340300d6001d00c2c161402c07035000781c0e0004269031109003c01441480505044800e42201059903044e503102c0803052100c0411450005800d02c40038030071320208000d03280100c50149000c00d04880d104030414020a80c1b070b21104030751a45e030302d603d20602d40300c3c2e040b010149104100b076501a42c00c0d403915003d641d221503060502c0c1d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65590128 1250 65588878 65588903
    0x4030f030203060d30030f0606030b030706050a05040b07060902042906030709240207060801060f0302030402040b03010c0201050f060102070303080105040905030c030a0306060201060504021c0902150d09 89
    0x8510a00949015840151008082c142641d560701c2d08000c040000c10b0b841c00859441441207110781110a00c4958035807000114100300200d583c055a94a41005e01070506045200550707032000520312044816a20302941c803407400c1c8800300c1e464415640303e100d0010700071800f502444150b501120030288200e4003084039030b000c05050200c05905e00b0210100c03a4010307002048505184004513404540da00c0c1030b1807803d466040c400e5480c40a0f240ba01c01e001e10101200555940400c0803c018140d0340c1086911580350420052200d040380c0c800c90101900031000c0790864035281c200c0d0008801c004c000f481004a1090002e0090108986c0080c0480c4010041400b55001085c00e800790ba40640d80e0380c03d9a800c1c2000c5c08090403000004a60300d02c81001a40b2900c4014005880000891340c0d000ca0382c2490528004e0944055400039842103204021403a03180e600d0115000f161194001c1c045000b045038000140c00006488400004800004083d1000c00007a406810300300e105014013141d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65591378 1250 65590128 65590157
    0x60703030221130b06130c020c030d0302034003180e09100504110406060203120708060d060f0b130b040509010b0105070f050c060a030608100911041505060705060403 73
    0x101c00b030075228030b038441101081c881c010600303902c009580705c2d502a0000c0090303d1140706d094100d981184200300182c125001c0c183d030f40d142c02d1040588a005a1a0a60943c104030100c00766101e0b00441c840300d500007404859a40c50292043e4141103a1003000c20703c0c084885040c041d0109041040f03074800c02c0ca891001180800c01720103454061641e0000030f0000d01d50924803400207001c0a017007a6800c0c0c070029040d4456580d41d00811000c1c2c00980d001d542c590741c901c20017100001c009401c0b03c0510a0420421a031034540540c200e034140e4008001240c043c0b610b091030317402400440c414503004040920302c0e81560700c0c5500031807006441603904010b00d070b8030030100c5400c84504210050004008100220100364105080040307a40110161107154503071030700140c4503a00429200b004640c55001c10000c9010902008950340d002c00014420714119640300b01c034480b0401c01e0603200eaa036429016a105107990046400b41a02801c415943c0181c4c0c00c03c030341c0c0c801046404a00152981a40d4844c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65592628 1250 65591378 65591437
    0x30b01030e0a08250501060902091903030c080a18090605030d0804051e12031f060c03020c010302030a0222170706050315040e011e1503080403080c07050607030302 72
    0x403030360f80040e05141000400c14210045420100c060703540500e8040950010034004e02c1144001e11103a1801030307035090345000b4480385041003202e030f447c0f840e0901e4080020940040c3c0c89200341f030380041d0301580c07000214000d483d0503051100140300000b40c040f002c0303481003055001c0710581c1d50481c1110742d480003400d4210b600d030404940c0100315400c417100341c0d81d405120207180315035103202400359811a016894191900d400c00c5409680d102481c4000441c0c0e6416441c102c0301604030f502d883c80d40300c440c1e40c801969071403c1e030801504150340080068400b001c6030381690584c0303822800e24047d040751011180c20000c4a8021741c080503600e101c01c0c440441001940300c003181d00c1a11240d096507100302c08015221110403680360015114901c1280c1c0c0314080c032507808030b04042d400c90241d0071020f0214400300c1311414216103031108880700030302c0403805030000e440803260302c840030554918400b1b00085c00d0042c0e03a0b020a410200200350300080581603005000a1070302c4c01c102c00e07143d1890340d20313028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65593878 1250 65592628 65592643
    0x10f1205030d20070804090b040227040204090903050903010606180315090b010617011a0f0c0a0c150e04090c0501030b010e120703061109100f14030403030b01030e 72
    0x50459008211988200380190011032071695142c8843c90400c490074038016181d4080e000458001d480003805114078565840b4648001740c05071821400d180400040d05003401622501501101145114600c1a6200e8040b54080c0104a4040c82038a0030380c9800381440d000b00040328420350a1040100300b4611031400d0f000c5c1e00070010320b00c0546601d140c40340b980307128103031501c2d40341180c6400c88600401d0551031403cac000c02d4290340344080c0183d0381c035082156040680040024500300042010760004803001d8620000c2e0320300b08aa520340b91146010f1809080c03480003019800c41072000588d5204981603134810180380d403558460352600f003003080211040440005e0811010200038040d81d4460b50009501610604040b001818031500051141c01022200c0e00745900211040c0108400c0c0d01401030b21802c000d125a0034110000f0005100e404440305c81380c1080400c01010310402c0c0f2480f95a1035441aa0202a540c1d08050400802138000d9204441c0800d00340b8540841c081d00c00142d80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65595128 1250 65593878 65593883
    0x41d0403020a021507080f0406030f0b0102060c0c01060801060b0901091d0a091509080d0e0304050622032405060f0310020f0f0c0304141801050409021215010f12 71
    0x18000c0300c5440e401c2104844d000c604e0380f11420070510504001405e0000180040c00b81010903a0710303180b51904c001d06072401d01040d0810341c0d04000d14000d19076000280c05800802c0000b91507180d045e102e600c14018106c50740004c0c2d0542c03c2481c0040d0210010740101542c0400baa6545151921001c100840d50b007501c20352440c940e030400018450194981c8591001485655042c07080704440402104bd06c02084043d00c6600b00080d800c100c83c0001e12640400c5e940300d002071401c140c600700c0002c880b8050301100d489155201065407640b1071503030320301d2000342d0b9011403000c000001542d075112000d80040e2001c120145000301041c80c516219000085040300100208042000c4228080182d041301c0050700260505102a420500d44d0102070005402c803c4011622031f442d260246002c000c0b15425280212406c407034202c110002e4548603415030300141e40c0414401511300c046940c01101c2e000320308140c050602c84d000350008105c18281260f2203185800e10340c030b4950100410100c1203c030300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65596378 1250 65595128 65595133
    0xb0a05120a030c031707020c120111090f27040b06040204120201180f080609060f1324050901050403090803090f040e1009240c050306010c020a05060f041d040302 71
    0x2000034803d550001d103c078407138034040d040c0e50716070900c420316403c0540d0042c001d078000280990b0503003400440d51418402c0301000740120b483c00c41511038a44541c840c102d004079044080101507407607200c01c00d50341c01460400301c0c181c0d078058401010407074401e0300c0440348000d0001c0030950b00c0c41c15009803015a41280410340c41080c0c039038015200180c4e528142d00c1400e140c4500011480700003c0740718011f04c6044040c0501d0b1401c2e0180314184040200000e180e03403603240600400c070403940380c080301c040d07400384007c51402040341d43d819038412404c034081c008038203203401c0000300541034004e240500c0c800e49071000120b1b1640851912802204140c40d0864030a171114035488c60103811008260701600141d8000180b01580902550708442050358824440300b00022b07505a040102c040001003204104440e80b903a60000b000381c400504254104480c0c2075140f402d640ea81c8040300018400145100d0391040e4050047c086500280724480041082d032052140711004500080e1050703915501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65597628 1250 65596378 65596393
    0x2070605032202030105071106060405040b131a070c020306070309021e0d08030a0e16050105070b0c0c070905060a060c0804050d080f03040f1103030c0d0509130501090b0a0512 77
    0x8441604a810b600703540900b5000e45000b07000341e1820300c0703264011805955180411022420030a10348140600490b0155140000f00004908409603442d00081a503c0800f01c0f1209401c2194220b000040680b075000c040c0d100340200c0c076420078040d4200c680700f68203951256030b407214164110341c8a5200650490301c450401c6043e2048000d40488c107d60080190000b02869103540b425500111000d50a165135821400c290000030040e03040c51203003041c40f141d039060070080000d016008034140101b100700707410701144000c403011081d5503003c10801e0032100410b03078450103d00903200513100c5a000c0c2520b401c020a15a11501c55001026041100759150a140c0000d0252441c1d0114007603030140c100b80950b0030fa070b01002d8000e50184d801102d006205074018203000c0d14100c4c40078001c920a0f0300c204000506168003041081700401d4908280b9151910034000c2113502074880d44c01c2802c0f030320f0302d17001144030381585e4880c659100d81500c1c01d102d00ea480390240090b070807014092400c150300064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65598878 1250 65597628 65597641
    0x10f11061b1303060509010b0d20040603050a1a0702030403031b03090b0d020a03060b360a03050304140d17070f0f030f020f0c0120010632010207060503 67
    0x81d185111079152515a004900a114042035007048440030344510900406030300c240100c4505020480d070364281d02c0c0155071080d110981e1004080d1080800d410411150b90700c1d036205400035500034085e00c3c110b14040c40c0c41c20440314407c0c0300d062003400b46008600550b01c004140d03001c0d01c1d41a1910302c2d5074140b488142c0c0d0300c28046101201000441e92001c190305100304083c28031204000b00158481c202c50704054107854842c0c1044144410038000b0500035401c07030b02d03609261039200d01c0039115403941c2086001c407141c00080d5503030040c0341240c0000400000000401c2101d080f1210340c0000b2800700c0420525110010f80a4015500d80d4604589203d10000402e90107100d221400711001107642c42d5071603c606030300700350007103009420101c5c0703580d40500810040202002c06070004c2e101402c00600a24100281c19200a408100c001c48400c42540300c40054038a07035550307000c4907442445003c201040003a030100005c0c80341d10004402e50001690304d040d19016202c8900750364401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65600128 1250 65598878 65598901
    0x9070b0309033906070e040b030c0301020309070302011d1513030f0f0308180d030c0c020d050d021c0f0503040618060204091a0a210501050108060105010f1106 70
    0xa051040240820088081060b003104511820000c0091004000300d05840c00000c4000c1010f1259070b481d00240d00301714406600800c01004007004960000e00c5540480110b40b601da003211847d6007642c1f0010900400c01000200c48040320b100742d07a41d10030322100f0001200040100802c03107800c00d040110040c0381190040183c180c81c503010343d00e0100c00750b90f502c42404010005500341d81c840e15000c80001410340c00800950311a81c00c141d00010b0901c0c102d0103556034410710704c000e17082650710340d40242c10900c0303201e008200f40c0d0020400800c105460802076140c000c2020300300c001d03110308060480095035582e41b10300c00300302c161181c8080d45561034090320f15900042c41102d0550b0344401140c070a00300c401505150500811006884034101001d51313007210868844820a00d0041d49040110b40d18400c03014241c07100000d807507010240c0d603442c19403681c0980030010119400c1c0b03400490701e0750f00010603c1c100d550907620510310b44480d0400340d9a10300b520320940c40b5504034000141c0a01d808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65601378 1250 65600128 65600131
    0x14070801060311061b10090309080102090307030611040504230108060910181208060901060203040b0706090c0e0403120f0605180718080705030c01080c0a0305060402130e0402040f0509070b03 84
    0x422904003003001c00e140b146401c06402c039046064451f1398260020070b0503804061311000d0700d4124001c43c079100c14100000d81e6000c851000a04407500c0700e11405401c041c00055030000c01c3c000d041404100444010851120314142d040d180420320000005072011740000d00718040c1503202c0252400300c40250640010f4030012240500d01c1903a41000000910031142052107090355981768200303401c1c83da0801c0b00c4480c040c0d1215003107502c207003c1401005114412203005c1640001c001503c804585020000c2c100c0b1507005000e101d43c803404000c00c1c590400b00c29428001240e10402400e564180301d80300319101401141d0300714181d02110b801c4401c3c07543d0400d41007506030400c01c120407041c0028410000b01034102100580000d40104102e003020801e140c2c444d4002d0170841c46615291209600e64040d40d0700321001c240d260301c0402d000c0d403141c1d41101e0710a094003043d4400079854080100e044102540d0882c0114a4606d0046040006108080c081c0b4040d501500c002c0303240902c200400d800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65602628 1250 65601378 65601397
    0x10804060c0c080f0901020715021509070b1308011107230c0907030617030307021207061107082a03030606071506080604020a0b040521010209030106031407080106031106 75
    0xb54100010104481001074852940030454160ba81c9101000090404040b9403080e0615910341c656951000e0f0003044680c0b0720440e81602291a03691480380c039291904903441002c4542c0000755091140c01c1c02d18242060b60300400003400803a222440303c4440f4421131a02034450940d40700c00c802c50700401c5c5404800840590300321004200903100065031000260780b01307404681d17921020800300383c04462400940f080c00000c0d5045190004003e907c96140c2d000d441501074000030b0003130401240c0e0b4440000e01c101054113944416113031a08080d070380d003c480c0c05040c003d10400c050200201d00c090513140040c01e00051800c43d01d605c03007800007607000034808540003c6140585407094809105034802408000c2c000c0c216030405005220400e00a034000c12401481003000744085d440b03202d03051803038910b0015002025604500e540d402030140c840d24503032550924078008240310007040c100c0d08001c03c0340240c40c04580d13a581c025089a181d8030000702681194000705540e0300d0003c1c040d00700c008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65603878 1250 65602628 65602637
    0x60d08030721050601030c0e030703110604090e0318030a030c03051b0102030f07030e060708040201050307030f0e010608010b01030e0a0209040c030b04080304030e04060506070f1110020f0c04060302010804060c 92
    0x80000c4039504445002c0d0201031106642c3d641044038a40c0d150244001a080f141094004c0413503680c0441d4650780320303010280c00585140c000100680b00c0070210780082000250030010601c0000200392642d106602c1d5949603404000c401c040d030f103000f241108110f541510303044003800c80c41c1d401703440f10340081483d20440f00d030020700408144401c2c00290304c1102c1d240d5440c03000d45403c600c0541100c0d034030b900f03c003070541c480800c11201c15008180103402c15024207105850f07542d02070b4120041e0206002c000056800c1c01c0b070105a50105400c45000d81d100e42c002407100309032071030045040310014803c102c250340c8048802c00140c14103a11140d003141c050406d03800e1040d281d88690300c10300400d0301c01b1a00e6000010820051542c007031545100c00b40101d5040c01458602800a141750050001c00f9040070382c00850361041180c0003c419821a102030420700c8202d44050010751903822105900c45680554110504545410300c00c10f0213480e4161120000343d111916103200500f88400c9a40520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65605128 1250 65603878 65603897
    0xa020d120e030a020c10090302030a0323070f0312020c0c0111030405090702030318060c030403180324050f01080d0f0302040509190e010e0d110a1401050405070e060d080307 76
    0x31081800100042003c980040c040d110400d001d205807031307101541d00410032840341010700059901103404007015825180005400e80c03240c452f010301c450420b040845071500014002c0070054080c400c40b0501d40a83c030303a90010000584964240d11818446207101d810807010300c045503000d0316007914480c29003021642050348032004038118840c16135410700568400b004105510740200c1c003410200340c400001e04030900f001e00302480c0034040508000c09000500241c000c1c0003440d480d22800464001004004000b00c400820180043c415181584c0f41d0501d400202032a4581c00c1c014100d454038801840500d00c000c808984100494001d0307010190204000502503480c021882c5c001d601070041d40800940c00d43c210b4023107603540c00584003540d05141c041c000d0350f940030403074505074511030424180c3c03004246019410000009802409010b030f41c00d01000ba08415841030740b00e5403081c003c0701c00c42500c3e107085054001086a00b00c1c1c1c010140b0b00c040c4001000d900146410100504100c0e042 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65606378 1250 65605128 65605151
    0xc020307210c08011401170a032a0311100911090606070602040f150813060209060405030a211701050d0c080f0c030d030b0a09020a0509100201020c070b0a020d12 71
    0x40703600f6070020390315a4590440c4400d2981802c2170314010301700c1d41c00640c0d004030845492a1521581c99003d0140a400c650381402140340400e03028007401011804031242c049450003500300c000005816405200d40301d5400307020010f920500d0043c50b00b145020001c030507990201b00d0b203010f0041013190003810501c41e100014503240090009803501001d0340001c6401c145404196000b13406408040101c044107004000301c441080e461050782100f030141e81c1c2c610003404502103104941c0a1901803150304036032814040800300071360038042c40300c1c0d220744200c02461b0300710340b003e624091021610290074010021882c0c841c00d8071400c035114401e10a003c41d686c941e00d90420451440d0f0030b0441d046001d4a01a40c941802844994500c1c0d00301000480326604c0841c5e08450301e030007000c0200d540007513054060f5000b0b205a4940b1300c8018802c003c1c907145000024083d41100c00c00f8000c030310a401d4041003140300c84050f6040c108856004000c0d843d12504110703400d03460a101c14103080c0d5625800c481 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65607628 1250 65606378 65606393
    0x10c021c11060a121113030f110411041e090c050d060b0c0705240301030305040e01080111120402012102040e060901030309060503090c09010e06100c02030721 70
    0x203050201168580c00500242010044800302545040c071400040191030319503500183c60340079510901000140ca500000303920707030b150710504401041001c1c600500000300703c25002d10300c603000e00c280d00c10113201444405101c1a0f0349040da4400b501082800107201c0f254004160020181910a03840022580c82e080b40c1d04840c03200030f05c4070004000007151003038500036009500c010130000100a00c0c22081c1008552103074000c1c0601c901c00e6402001069170348a40c07403840e0f10000c0e402042a692540d4a140240043c0d003c3d1003552031030780342d280c00080c0005041c428010200109401e80e49868040b11a80f0081d540080c01207040c0002440705401d441c0d050083e802071600c5c600d000699942c2014291050100d00612003403040e030ba2000180b00003640030480d80122030050810903280d80b0b54441d0035040c009001116500410f41c1000040c911044244050245006507005400180030010844d03a01d0071103c0040c0d01980f100004002c40304c02c10501c1c61034094000840380c640480c6d5568500c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65608878 1250 65607628 65607649
    0xe0405040809010e09010303021c050403080307050a0207080102040b0304030e03030c0f01020d06081209121510060305011224020904020304050304050306070206010f030308070302040503030a030c120b0307090506010c02 96
    0x31425100891980c2c100d5030084402c20003444215151803541d07145039030007175807204190301c1038201d102c00d241d40050742400759054401565100d68005e4881c942200d00800d240c201120301e00040c880c642000070040418400c4405607031460b0840c52031642c590320182c6294070074414442d010310040000007124002031080d450005030380710015036030744007601803402541c1254105590075001241840c1e4030020300422100540825911000045100c2c8851030170907440c2030300d2a01e20b841c010b0401007560145010441602c40948080015036201e480c00c0b8040c442540c00100300410310700072404042504800122010001b40015140c5203c00c4081001e03038005071011646036001003001d1100b0702d428089980d21003143d100a2285615214801d51340107003e21014050000c2c100c042070302d02c0d00c00c0d01220040c1001804407659450a150010300810715000c030303940080d641111403d500d81c6140140481100c00030000d080300c0f400e000c2c6030070040c60007420007414880c6030f4980300d006807144400b15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65610128 1250 65608878 65608883
    0x203030a090809030f15060f0108010905060a0e041119080c040b060c0106030f0210020a03020613030c1202030711040506100e030102070209040c17010b01080f04020f04050a200a020613030e040504 86
    0x4040e01c140d001a04143c5546c0a0031451081070b118000c2c2d00d0700e0344e1150409045036402140860503407191404518403074050703040031980030803060405c003d000200000480310f06056661200b68848020219040003c07802848025001000d13841c003e89066003200d02c000c2c1c0c2c0100b8a61500081c900b1041c02c49909901c100c4601c0943c0804105520b06841e45100f00f0581c5c0c0003901030f0305460b9078001d4032100024501e10a03603000494480505100c1c0c5c58809a80364419450046a02c90050295403071700031520860300130352106603164460404c6d004050050310060300b0200c02d2100924140d561040075141a0740641d82400440003590320300240078000c50046080078070003420011144c0f51111070104080a40c0e0415070041d19a903440020b89034002c80d407410707501e02515180b0000f00e004642c40c01642e4803074100710501c1071320302030faa00c40001d801c1c019075819614582c0194400c40ca02420761400d0260700010001186a4004401807560900c00e2400ca6405010240000d040350310030b5605 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65611378 1250 65610128 65610133
    0x11010e210106060908030a200f0d030e210d02070318060509030607090b120403021f0222031a07050f0d020306041a0904060c05091c03020c060403030203030a090809030f 74
    0x40003c1500461140003820740c11000c2c0d49400c078030400182c9100109950250f007402c100320780c2000c1d40c1c0305200e01005502d0314000c2d43d0b08100c2460009000e44044400c0c001ca601034420b005c11201d40440d2440403c1e01c1a4082c0c03800c0c814038060440c025001440c0036000d00500440202120450480b55005080e9984840f5140d2500900b4545400c1004104034140001242d061080c00c00c00307416138090500c41c2990080c15941d5180c124200a0001200944000c00d160704400d00c41ca582c001e1300c8010001142c0d1081943d41908a00404805100c040c0017a5525040d040c048401c0080c03241e405a46814035a1408020500c07a0000c1ea0107030200854190b804014080d461406014042e041d00c00b0a5030300c602c0d0703086100050201ca0001d0030041849540b445090302d80b41c01041a200d0040d00201860034155002282d2150050036000460041c002c1e4000c84000d8a01b80341554296600b680c011030a541d100e540e410002c0504101c240d0b000d6605021190f80340e90b04018130800c46800501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65612628 1250 65611378 65611391
    0x1d0a1b170a0c080f030301090207020f100e040c032d0603080a020601091103070f0c050709180c050108240102120406120b040e100506130504030915050711010e2101 72
    0x3000c05201002e500190b480f600012120b0301c1008000081d070341522004000140c4d54501880020032088406890907017210804060035201e42d000b15045003009801e8400348401a42080100e0441c2e00091114584820b031441c01c1841540021480f0312082c004040091015100c1c1c0307600c02e903034015541001c0107a1142c0700522408a1500a01c40121141c074031140c10360034038081c0030b411803600c5101d031810005104e0001017480410800300005000b103d200b08505080204885e241c142000c40c26583c80a64036800909035208140061040d050080118681e12034180107590f408000c40c41181113200e1a2503040559800100410044c40c481c1c8418061248078074040d001e0f503001d5138081e4071840c07804550080c00e84020441910801420b007000a4541d103c00000301e00340c01c1d464228440303524283c2000200342d080354040c001c0e113528450f0b00380300c0d07061142d0441c0d0074030880800420341900030000c90041d50143c00c500112205c014401141c0042c05000c2544165100f03811011581d100c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65613878 1250 65612628 65612633
    0x8040f0c030f061b1b15050115110a0b0105120a0b1602060601020a0c06050c0a08040909020108010905010506040e06060c01050406060518090c101e0509041d0a1b170a 73
    0x80703003500b86030000c0c03003c05050130340b00d0b4040c050040314104410700001d105000020440080c4030703810381c4500c43c02e0030411940c40e07000b0345450345469180320000c00d20071a1414041c41d40016000030b0303198040c2c100390803682008148408403000220078a0944108010600040c4031803155a100745426404d1420740814a40c00078074105016002d83d0554220114810124140118800640d0401e061280e6284da8100901d45071403c08240a480d4450100e400314028540e904044030342170007642d610100f40d880b0041c0b1400c0311002e11649a0111080000708600c031240054030740c0c0030100406407414800700304200c50a50f041104c1c00c4604550700c0c02c0c184201c0c5002c6911440074a0202910b841c2442c00034602d0b6a05c41a5030304141c4aa481c03080303810109407040b40408841c2c90407410100c0e0107012008064559002a58100d01c920f0800d1980d1401c0c4015842e00d02e01080500e00070a00603207540c640e640c40054158001d00d450030a00c1c0301041c03603039410803820740907644e520003454080b0903070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65615128 1250 65613878 65613881
    0x501091a13050a060518070803071a0108070e0c160b0105031207020901050d02060c030703090503010f090302031e0409062310020607050f120109050723070308040f0c030f06 76
    0x388054000c0458a01c8100032803000901a80c0250f032014000480d0340b1504050603030020032a801d040c091044140124003408044082c00e5418480d020300704181c144034002a8203008240251040c1760b100740010070180c10342c020f03e15041030140c0301d035a00c3d1012101c03d0329030155100e582a684c181c556001044030f801d003004072040c0b082d004141d107820701142e540040c41110041c46000d2061095144280c15542d0300b1303040343c00e01f41428040b03907a64101440c4c090b004000900c40c00c2e00c69480c294001c0340c070105900588440e0750341603000c0c0d807078005c00c003600400039000e420880200c02d0061201040c4660741d480b80d41c0152024040c100c58005183c402a6003544c40705038454000c11032080390040d003d40000320690016224100180c4583d83c042d21508503010742095510381c1040030b00001740001d4582d01c142d0203610307103641d03903a08000e240c00300c2c00c00341114884196803040200310580c0864441e40106400500c50004a00140440e4a803072510400580007503648001c0f0031002030420105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65616378 1250 65615128 65615131
    0x2040b0c06070806060f1c02120a0c0203040b3c0903071a040b0d0908030f01030203150408030c070203010207080c0102030f090c060307032a09090c05040e0412020a0501091a 76
    0xda1400c61000d00e003e8010461038001c881c506c88140e400481e00341d03103600080796810310b0000403003421500c80896400981c8684030941d01003c049160900003410343d031020040310195902d00b1b5044e03113421000300d01400c001c103e0000700701140c0868110b02044541020302607a8074071011101c641c48601d010205030400358141e1048015406ca02980c000d40301c40481500c0440341c200d038005440c0d051581d8010b0184c00c0040d030050549100004220164200a49545c1038a0003030b000c90b103440104154020044070f06a601415040040c030000c0d2100018000605842c0d101074005030400c001d6030703281201030700b2040543d00c10741d4002c800c00c49100392004000e44d20180d81d400400712204454003203034581c44007070144400c040c0c0b1480c400503c00300000c1d48541c408251264810302c0922898000c1c4004100e01500040c03e04200c000446144148161001d407200b11030104282c0d15191344501d242c1489416110650003208040400720b0002c3c400c80c00c01902986140700341105210007031880040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65617628 1250 65616378 65616391
    0x9060f04150e2410030207020303071e031103070309090c050408100b0906060f03070503040609140c01021b010e0907020a050304061e09060c061109120102070204050f0c19050d02040b0c06 82
    0x3d070307841100310a84c2c0f1071004e000c100e0414240184d90310350030b0001c281103118842002c1d00c00c41c03200340d000f00d240c2c08590142d900306009079034041c3c117206115080c5461b44228a000390028450f86414001c001103540b0601d98900d940c01c2551515a603114541d041a8400c3e00070740c0340f6a6a03503400310181c03e041e110030380d101108456061a01c000940480a1400050120001c01001100140400c0083d40c0600a580d41110011140c4e1090510840c1d4800102d0440b50050080c4004d10400d598640d41038155080d0585a00302032a100000784074038a4001440350b41184642030b0b07400b000c2602407000380040c0c122030b40c4c0d04c1c40201520700b040105c1404080f402d42044000001000043e51155140302003a03481080030500c85108030014029025202035580d0100c2e0040c02514420340550081182034400d40e000e2006603181c26440218a20444403040044010000c140b0041c0c54030790156405215070510f20709104085199030708a80054000f005120000180c1112001c41000200c0c0e0241 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65618878 1250 65617628 65617681
    0xa050f01050307090e010609021813061202060c010209090112120503070906030203130209011202040f0902090112140d09061d100f09050d0305120907030209060f04150e 74
    0x500d0140420f5403640d03940700b011800b907603c42c08503e511030300390050001004988029912214100d48040d1482c1d60001d245208540d00d800c050b00000c1a1300030785003200d54048040f200055150240030140e8028400000c1e1035508102c0f40f081655811040d901900a0b41c04440c060803140c50880750031020b030303a0401c061040c10310810400f9544840141c096074910b00c0c0260310390312140daa2401150003000700952020101c000800c0031145010f203060014022941031103004a40414141110340120000c0d410500200c01804044451510b0000203442000f161030680717070703c5521600b0112552003d0000982e0100304001041d03002001190044031800d0000340c03084050300181d620600c1c2c01180d004d120034603e03403089090007520f20390300815000d028540c05051510b00280168442503121481c102404003003010340c28006154000d0f658007030511501038447e00204504400310f02000c5a01c6600c580151500410344014a8014010660800321138100030740b1070300c1c00304e0004d490340c040d81 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65620128 1250 65618878 65618881
    0x50901060816110a1a060301060909050703030f14040602010c080604020901021b060f0d021e0a09090207080702030a030e1f0503180f03070c09060f14040c031b0203030a050f 76
    0x20080100300240e101d9608004001810343e0740060704100e60204040c0801c0a4411104424928514081e214100c120001c20101c0d8943c120341046039031f100310207081c2d54021401400041d0003000c0641c450045800d0125000000c011848a243d20941100006035100d00b11030201c60381182c1616000442240d043d4140404080002d60383c1020f042c20400c0c2c058404101c0c0101d484001c110b4521420500c0e000e03a9038610720200c400a540030400301004940c1d810b031015441c85400055854102480e510384081c240b0f84180e10b0003941019a040d54080001c010794001a81c041081d9000c20740720744c031106600c448240800110804500315030607c5501018100319a90b170140c1100d90010106800918000340750303145500d0440c0c202000780c020300c000107100003444400442d81d070442e81545001d009a90f242c003c001c02c5081103100d94840b151a012100640b45051b030403284181e002d03880c1c0003c008016021040041018085280140c0c00000600c03e50822902600b684001105c5010030300b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65621378 1250 65620128 65620141
    0x90b04050c03010e042d0507211a0408090a06170105060301181d010510170c0105030103140a02060f0705070f030b070f0c080d0e0f010606020c060d02070206030408040509010608 78
    0x71154005e00040c81380c0459a105110f19080080c5010080ca02e4981214102020300e0603e650300140e006031010000e440c0e1984d841045c0380c0203401151a40710301010b41054501180d4601e03404081c0c4201c1d203154040c050044ca03600e88152480c000e1880e030f034a20b8000512828000c41110040c0c01c8140250710402c0107000643d00b6414004080700e40d0000003452041300381c0c1202c0d80000c02201c1119035400c10f018041008090203070502500c540030035940310030755240c0380d459a94042c0d40c050790200c0c0d0180010404520503282d034443e0b9640000680c1e2039581568005100366000201040041d000032030400140721040001c0005002034080f802c443c141152501200041c004203060308021200390484900ea20907801800c0580d489460320b40c4035020f83c210200a800e03820b81640c01e6214204600e140c005c81405020201c9159802a001c03141c040002c1c014242e00c941010004641c08205020060321001e000310300c00c500409409442e142003008002e00030344180e20441c1000400024040c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65622628 1250 65621378 65621399
    0xb030606010507030504080607110d020303071b080d0e010501080f0703020604030627120e0f130f0617010605030106080a1121010228050705150603010b0307090b04050c0301 76
    0x411a00074202243c0f40c11251404440b80c6c8200c0d0000212805614188049250464140c5502c282d2050503501005643c000880e5a4082121120001941c1596090030b800c1035050400b060360080c90070504d44030502c00e40d24192100e810320138144e699038600402c103045042c0413143c8480081005011040c1c41c64000074000d000394013010700001e41d00ca020701d00c004940305a450200c0001d528000c0c0344151824031012003001c07030610740081340f940d0403418007a01c0c104000f224900001070034001010001c59520000340040c4219040c491380d2408049600a01c25000124440e92a000880c003241000c080c5801d50343d20354058040c030b0780b00c015641c00050030701c20310030f0304c0c034900f91810840002024200b81000c001100c5c020015440081c600c6500c054400d02c142107854001c2c00040500301800044546100d5a03030b01600301c1d0007400800344c4e005030745c1c41400c0c1c004c10006c001040400d0f070754000a08084442e80040b0203103544030342940e020300301409956031040428022906543c0350590840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65623878 1250 65622628 65622631
    0xa1203091505070506100315020307022e14100f0b040b130b160c0503030c1b0d1208070f0305010b040e090a0b010b04030b090111161e0b0601030c030b0306 68
    0x1500c041c0328030301914510b84294240d9143d01d1300103040f59a130341041304ca440c941c544a400165240c203c585104100c121036802124020601c690007401901c40d070203052100302c1103104440780621410b0f02c0d1301418010900801c000d2400880701c034107403810610f0306402084200c2c0d0081400145900041054905602c113640841d010084c006c1d55032403a004001c03c03001503a4100403180100440d142c60612031a00b54941080d1080d4509840592107004040e42c038018402400072540c8020b071700558000000221400c1000054054543c800c0142d0714040c0500c03100000c0c0c0c0000f51420100240355034000d003071201c2007120f41000c110300d5040400d540221f20603030003090544180000031411744102013240240c07141d00201d0403070340381d61100d600010700d07401448166102d00701d501c0880c3d1a00810301c1031000c06500c55441d50300d021002140c0903122008154103680c000c54450785541650003010300008480e01c40c4400c04106e141c404000760481c2ca00c006100c017054030708000c90798940c800240c3d99 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65625128 1250 65623878 65623889
    0x3190201050c0f0102030a0c200c010e030a0804080d120506090105060f1b011b0311090d020d140d0f08070206070806040204031403040e011e0b0f19080103020a120309 73
    0x40d6031400c2082c0c58038940010790107804410340c030010070000750400c1a8070407a5404070070307a41e0408034240090022081031042c030504289400c11015060b942d0300a8090556421000d010741701c0441c0681c440503800e0700a90f11412150b04880d20103c0140d40c040083e0340301003100d0008006c0c2c1d00300100454006d003014024103000300302c001402e00e40030043c4403ea5180c20004144a83c0301152a002d05010b0220100e0099103030300d481240b4480c03a4002c0c000d40810082d60202603007410020300801140809402043c0e0300910740c5120b10b0003050030912000707492070b8410024201c460010800405000c0c0294000e010400320b941805412603010486a82202c15031406443d80e8035100000b500030300c515407004003e0388135078242905500703022000d00100c59840e403c0404980c3c0c2c23219140c2c0500b008254044c8100310020042c0009c2d9400340c050f04010119406a600b000100c0703808407122036114100c10082840800100214544403e802c005804640200754510b03500b941c0190021015002e00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65626378 1250 65625128 65625137
    0x306130f03120504110a0f1202041505090a1b1103030f060109170a060f02040302030a0b040501020d09050c032b1b050717060601050a090504050604060f0603061403190201 75
    0x80314181485124204000200403108000342d00b85880c1c5441042d161056150007121004000120122034140d000101c400004911a00200540c208070041ca2005680b080041c12140003251980702d610401d48103e40f0070100289800c066607140300d2803203030580e00b0020000c4541d00301c111483e001c025640c200c0703101c8401d803a0640304c10b001078900d01c04075007107011800107030398414106c4000090202c8400e40500b508100118007c03481006034481c50102940507801003852100080e01404080d0340a402980014106100700c5012020380341406025102a40329403400710240c0303400d000d40380005000001c400151000d005506a05030402a80802800300c80c03a01c100481d60340c000b94002c0c080c0d00c18241c44d40d1540301c940c022030002d50300090001c8d43c45060002803041d40900c085174003001e051340300c04018601d020208800313460000d10040d002501c0308400214401950040700c00380409460126070641414044601c512101980601c00d50000508007020a40c600d40c061350f40da0280391 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65627628 1250 65626378 65626403
    0x3030903020f031c02010c0e090108030403020105030c16030309050c0103050f0604020a091a0322240e0a0b1b0301030206030604090807080a20010e07062102040f14030613 75
    0xa41003080d200951340008050303403a001035541d0f040d4824012000c8588803c520700150605110811400b4080d109895008010034009580034a0295922498901d44186003444210080d950600450000c40210ba1686c0c0c002003042002d0014600641c0c1c20300e82009503142002003000180c074050111801268001039640e241031142d5101d50192074901540c0304442206c00d0a444139034001c86459120024000e0100c04500c1d051501c0680c90f501320358a01e00c18014aa104825088409a000e014a42c4c0e40c044001a440c107001c3d5040050090180c0400c40c40d0a4485614030502c01000702000c8204000500c0140d9909054942007207050750000b5610b001d0b894241c01500c1424009020f0901c04141c032800c0a0344680c4112011401c2034001e00104050242d081c01d841080c0365132825500880d1003801f02070f2044019101081d60003890307004101404808504170380c0680c01400d40b20031160820f1241342a0b44500c80c00b07542060f0000c1416160001c0e40b0014912201e100600700c904d00c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65628878 1250 65627628 65627659
    0x903030e01120603080301031406010803120a0b090a09050601050f03070e091f0b01091202010503040201030902131103180a0302030a05070206130e0f09030301060c0206130b130303030f02040303090302 88
    0x1003507802551006042001e81d0f01c17424107200070f401c24407040b41c507181c3c0005500b003a41b4012072803038100d5440d0390041d13080250758080c81c550701900a04100d642d42ea43c000e0b411069980f071420600640b002c44000903000f00505200c2d0600c4030503040380b80600e648044050454600181800c12200c041d40000f010f5120782c0c0c0902d05104031484001040b8029940c21034400300750798082024a5001d03200c0350700d442d90712200c1080300200314001030301151041c07000401550182d0403147d003080c07008000d03864140310803007100300b140c030500d01e03081c10a04003200304400c001444d2a00440b0545000050412200035907009507280b0980c02c080f4100840811a4001c54030b030319003580d0400d408040e1600010780c07104003812595004580140c9580c200b2004200144c0c40401124107a80701d568480354488680e4090001a50013801c601c848510300d100c000076503d01000184c07448030100200355418900d1810010103440e01c032003007103c0f054810130042000942050003c0c08583d415500c2d80c909100b6034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65630128 1250 65628878 65628887
    0x806062103040b07081b01140402060702011119260403120c05010f020a0206250311070b04110909011b030507020c0301060902090120030a08060a0f030302070e090606010903030e01 79
    0x142c0c04281601c50100c1c0390704c100b100400c09480c548056925441c07082e0094026603003a40c000180186103d07070b6030000304025041032802406400e0040c100000750401e46056646803902c8804002d0181c480b076200340e0100a08860032030341c00385511900c040031a89980c048800307403195110040c00c504c070b5241d074074112902441e084030368039401030003c010001541e590716010794003144030080140100c030b00203030603200700340c42c4086e0003181c0c1c000340f22150550764429002001d4800007000030440a00c01e450000e4045010329114904c61000090325142c0c400a200c883c2c0d002800c10f5080740d0620902541c0340a00d0101901418010318001c541c0380c444510603410070b0100200c060b015401c1100205407800c0e42d40051951840a0703a461034107400c103107010703540000c3e007440568282c0c104011100f003851145003482e820400c010408040c00365510b903900340c4c0345100d51044025030080d01040068075440300e8295803061407a1301804651800100003801609540002014040c0842103d122030340315 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65631378 1250 65630128 65630137
    0x30c040905070b0d15090e0d0302030601090b0309030a080601110a020d0f200913080313032d031a030a0b04060e0102220f0e0f0402130501030b0405070806062103 71
    0x38210020b130b4401d1141d41c1e8001904001da8030f04240b403805000010030000a01c54015441400c20203081003020800040b0040e620162555041042440c000705105407640300440c02588118001d583d00c00f10031a014103890360041102c1d05101800d4210b010606012500214141d4102d4580003002c0452401d034010410b8064054010448900f0186214440d2031640c0582d0901f00da00c0601175941000c1405200503240300100a12402d10201e000c10101407600d2560768400c0c00c0100080800d40a040401052441402c40d00e0242c40c1e240c2482c150540310306142d51030380d0011040e21030035160120340e0310385908500600c140b44d4100050b0902007160311124640d10382c00029540c9042d99140301c0030303015040b206845214080307080003403103a120303c0b400c60484050301c290654580e41c2d840950740c015070080c002d0760041488007400b2225074603407140754082d51240d25014000d080a0030002d1034038940c3d4200000030341c4810140700040d51440703000f18507145400b1111041d6240c40c28680d045024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65632628 1250 65631378 65631389
    0x307030603080d090611090d170706020f0304121412070210020301231801060809030c07090906050604060b0904020a021e0601050102060a060e07030903020c09040c08010b0906030c04090507 83
    0x7004580c405240c3e089402c0b0f80c0d042030040c4014444012948082080b0303105180c401c40c2d01541c4e01444d03100058410700c1e040d07092040311352442e04190840d100c02c0c00f0f90f4450340365504040e000004000c204010304034400d01ea441c0c0341ca482c41c1016580740c07030701046200d0690703840862508200014540740c0701300800d69081c42c003900c09540b00d581d1030202d0407900d010a040441c1780c800008650002e41003603050a221000e00007000d14203a4a090300641e0640b1004c4c001d140c15000c100072600054030100301110003041d508100207038410440c1003610440e10080c0c21035228909090007040030010341c1082d91f0340507004650050b5181480442a494100c5032901114400345001c80c10584000114205048072400e0702030360b030b05903155069a400c80d06c003130290444c002c10180118925038800d50282c3d509900c20300450f501000d120000581e0b01c103080390100c4413141d10680c1400903000a020b0781007010000d03650113000e8204540001d40b2022501e54940c0180d81e10b0b600c404c140801040014000e00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65633878 1250 65632628 65632643
    0xa05130f060213080304090f02090a090504051e030405010806030c03120d0906060909060b01020a0b01060c080c01020c0a210c1509080d020c01141501030504030e100207030204060803031b0307030603 87
    0x42d5901244c0d9102e400c68440d00c02102d2a003480321483c0d403400d008503070000000405000301c90b41404401001004003030400c0c0c80910406104000c0050304c14061400c110020008640355490140010140c80d0001c12041c0260001c69090300962400505030f000300c50b0f014161030319a80ea50400c60020b100d003410240401c1d052800000741c413045a8400140c13980503607400e00c60086000c005a96031101414002d0207010402c00410015105403182c4035030f20311542015190281c1c014415007683c01604080000f80c02400514042000700000750748034020342c007040d5071030001108018003400da0a8030068190070f00406080c124a8066104507500d9900c40100fa0311a007c50394a04025000710324414695882c00b6400045140b4407600303a0300c40c00081150030900d141030030044014010240c001c078280a41100032450030303941c0d43c0b00d05d0340c11060765000f0074400303141d0b0041100ba210b9a50018149030070801c00d01807240c0e4511550441c090a120400e0b60340e0712010b00c120020441507001130700b0718 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65635128 1250 65633878 65633917
    0x305070e0d060203010510050306090a050a11070506090d0201062304020c01090803010f0e0103020a0302060d06050a06050c01060e070203040b0c0703050102030c0405032109010e030708060705120a05130f0602 91
    0x2c207640c0507506840041d100d80100c5803030307030905541501c8141e41c015800341400380000d105100707942001358403401080c0040b844221401d2160482c1c0c124900c100d44540201c41001508603041103094403170035440c4001c0c0a490315151800d0340c60f00c9003c1000c0600041c0e50074104460b16141c0440e0103a2610300d0007007004c00300a040ca90800d40081c02003079441c00b031a440000382c0c25202c00d203a5040e02e170010302094a052940e400c000803940030081080711240c40c0c4400003816524004a03800400a0b03482e41740c2d45024292a80d070031504d541e002041d44088003414070900903030020079241030711320700316510ba65088407070381d5103140c00056400100250300000c01c001d01398085501800440c0d50550440341c49000c444943c20f0041c0319902c00780d41c0101d003405250b001358455051514200400f4081d03416080d142e019090428a0803030380d0f2008220700040c408507000b00e1001c4590b008595402c00c00a60826401c0103000079034941c006071080b5580c801100501105504460745a0700c194031141c4d05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65636378 1250 65635128 65635133
    0xb13050715030e07060f1b030c0b0f010603180b0708090703050115030c05040e15100e01080a03020f0d020c09070302090603100305070b1602040e010b060a05040305070b0f0a0305070e0d 81
    0x6440802e25a5045009951002130800d00035100701949031001d448002c6950b078400c0346558980c7c03002d030058042068001c1003501142e8070031201c6c1d010704080010141c6640c1000c0010342503c01e0a10780c01038125a022145d40420b025042c6103811403007503d40540191100c035071081c50105141c001929039440e144011327001a498903000c004680c4a280c903462110385e02c074100422544009502c00c241e401108076044103020041026a100006207500b00819491b01443c00d804c1d003098100300c025a00500d068014560104180103601d405a0000d000c800d199a200075182c0391400c100300c2c09404400041085c003402601601c104d21406010340e07460b864400310380818a801c0344015141c134028100c0116242c5c2c0d080d0b08407401c0c1c2c4089003400302c02405590a010081140300202541035580c5c14540c980d5a583c00c004104c941c0d00c990b5519120b40c11800d043c0d041410560226030b59000c201704800369000d190302540c1882c203090400007590703540d00c00c00341c86c0d00300e031200466402840c182c0c15408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65637628 1250 65636378 65636381
    0x40311061302010207090c08060f120a060b0a050901050105121510050a0f020c060f1b060c04170a0b06012708100506030a0305071401140411040b0d0b1305071503 71
    0x1070600036802c4811051741d80031540308864020340080d001500303010000d10503041903608025001400b80640c803003d01080121401d0600c1071000300d4800d40c440c0010a5180352807107210340900403c031844945945880000b030014030a8034141c02c201e558103c001070f50490001701c0c100050b00003405441002900704070041090740724800cae540c01300f0886002e0b50301041c40040c0768030511b6405016a4030780214044c90603819041240d10802d50f283c110810b285105041c82014000d070708071840140c90324200802c10030038010a00103141140d01031118400451098035101c1c0c0c02410030b0a10144c014200306241020008010b05000c2003a20118002680080080c1455509031380c0c5108202d0703612850704054842c11f8640c2e000c1d00260b401d002c0d440c049181c40382d074103029501c81400045c0031490400d4614200f41d0465041c0d81d004001108800d0500701400b850b000014119460b446004850381ca20f010f01c03201520384044000031406a800300709003000100c2c007804816500707401c0500c406030000d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65638878 1250 65637628 65637661
    0xa06081501030201110607022805070906051c050a0206030901022701030b0a080604060203100f060e010809010902150f0405030a0b0912070804030602030709152a0f02060304031106 79
    0x340000c0030102c1d1205d103c03e0200b0ba050144080340d0280c1040c07407001140440d6030340c410307004234020a030042848000500401400005080320130f40072031928038060800424544051810741c000d40030040e0040019070102c0c480b191190304844554994540080641c028041c3d40b10342440c0010440c0c240411092254503086008800d0ba401d009583c440803d2020b00703040d62150b0421a440b49010500086990f0007440e408020001c8000e84650b403580340110700c0d0080c1d4030840100742074200da11683c0d60300c60081c03580152908000e21802c030303207030303001c121080608180840086804070300c14407400e112204581c01050000d04440000300389007840e81e84102c0540b443c840c03034852851039102c9841c501089d59002d58102d0b10041c00d1520750384071b00c4040d50005040783c04204542c0804106103000d029817945400b101e0340e541d401e400b00100c00ca100c40601001c0c2c1400c0380359400d400c50004151110811080d45e0503035a01d52a51a00e1409441c0302c0b04940741c0e07010031300421041148041c070111000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65640128 1250 65638878 65638883
    0xd05041703040b041b03110f0d05160312030507051e0c032107080403080703090507031703040501050c0301050607020618060309030310052d01020c03061006020120120a0608150103 79
    0x1000072945182240f000000f0b03444002d01112601c51040c290780748c05400c4d801420400b601a002d408521f5884a0030114080441d070201c40e0255000e10901c80c2d0040500380c81d8025041c1000b00e400e2425001c1d201d800b0307042249509014001d0480100c0e10340a0540364060100c8080741d0b144c0b07030340c0320320617032400000070700c07a448281003d000401031031140301007034000c980545480d907440c0c803228011005072203030090a4410b441703503003800000220405c031405007005950764020323120309040c5025804e4802c00b42101c5a00102400140301d9079940100302c07201140e046940c0c90b501c60020403003031610109a086158080c0c1c010040250742000880254030500100d155454100d40710020402505002c2e01200c6400d0000c03030f80c00f00402d51446d0385141014050048440107124140001d19064088441d001d0701240da60b02002040d80900444a0f041941d0013180f01e0391140001c586001c0c0600c5000f1202401c900020403880505644000041e00660040d13816000316980462003420003071004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 65641378 1250 65640128 65640143
    0x41b0e03011107020913060b060720010906050412060e01060807052d040f0b04111305010503060916090f090209010909050603060a0f2c0c150d05041703040b04 70
    0x110b42c5040d0a1208407105698010507000040d140c3d04e15450101601250484156603101003200c1c07243c2c0d690002d41942ca100d060801e4244404114044508110541150501440030401d205903500001510f091b6010108800075284960034158054885100088007a5207802c201058404001c504007003500c10907500302a1074404100a0940318682c42148a240024014044501d180a800032400c0c91545ca8010852040303890000d001c990001d070345890000d000160400540c0090102040180700c2400c0440c01c504d0018040783d030640004104028416440071a240d0642c00b0b00c04610151000d149071522036074079107814070000c0d8086400c05022400740400041c0111080c084d4034403e900c0078002d0581da031245845400641424082c02c0001c644405400c2190300c051001c2203c8082c1916000741e6681422041905210801c0c42c5640201c51403031080305c02c1c1d4007203401c40301c0700b81c40c2c04c500144c1e82d500c0d4102403400081300300e1010140030001084c8418090303040070141c01a0300a001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 65642628 1250 65641378 65641391
    0x60d061103090105091614010e040f0f0b010212030a021614100f0504030c0222020c060f01050103111e0f0a03051008010b030c01031e050907210b15041b0e0301 70
    0x30b1055540700d64016106400f503181009000701b47d041d401c51020071790f040c18203e009030015000a4151401c8a51100710340c0c0d9a000103000045580c01f0f0116400828000390030942e140302c82c018281c1c440200034060082d0001404581284804c01803180e1a4002061607400c01c0d00d682040d484003075011040404a017464201001e0a5241c482d140c001c0d981501c0d40c1c003115807181e0078890076684107410000886600c45c0d0340040c080c054001001406074450250a00d454008003a04006006800c60390403d440c10790595940723a1440110344816420b000b081040d003401c1d20541e02148a01150b40c0240720300400d401d041d00313070160060bd0007803a000c910b40105546600d281800ca40d600134407203615501641000c1401d5020744e010a005450110003440215503c0520790191001a25001c4060b48114020001c05d010010285200c1d1506e40c804000b118590311000400c4a000d80400d00d1809a811080c5143d0340e90b80c00b0104a00c034068541c400c1e5070302400084c0002d200070364402d000754203200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 65643878 1250 65642628 65642641
    0x140901050c070312020a1109160f2a060e03041406030a0603061b02010506010f0f030c02030408070806090d0e311b12060807120c0806010e04031d010207030803060d061103090105 78
    0x280e08d18402c1c0c0680c004101041f8450b00d08980100c240e68034030060000000742c648201800001c9140d00c01d10445071609541100d00c0c00e501120740355004007071160000d20090240c43d200094201e001c0c2c90442c1e01d40e44031385a041ca105d000b0492640010070041c40c00054000840001c141c811140c85690000c01c59651504015210203620414002c001848220702c60341f214082e601500d400038091048a00781519424060304e0300b40d5176001503017180c2c03080081241c404e00c00c20001c60000c0c0a854148a0301200c038011894000b00c2c1440504a07601a59030954021915a180851500035140034040d030500103a008a6209007407140c103002904001107000303203504a0140000b269011801405500d160891038586c2c0c83c84000205d03617814003075600142048040203454081c2c58115085c07111410b062074081d000c4c1038030340c500101c0e03c0201c0d0091a41680c0110b049022290422200d1f81d5940e12900041c0d0302040d0401c0044c8041e00d0642642a51702d00040035520030744100000f0041a207908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 65645128 1250 65643878 65643889
    0x90b010f120312020c0a0213061a0a0e1e04230606090a051504030c03050601060207060905090f0403050f1201211e06020f0309011b140901050c070312020a11 69
    0x19405004540420b10040c80201c090380105010040301c000d0351006c0b401c940c0000c0038500160000086151503c409001c076404420401e501c90440c8840249400d0850102400d500c080b8511a4072466902900e034130b00c0c2400303425600404030000c0c001c00540d031009170308400c9100740400001c041c03c03000700010044e0a0101c11507031030410090440341c0c0149030904005103c41d41003c20200740c00144400400030713036484d2242010f18418400380540b07604290b8000e251500c01c0e0320440422420000400480d200c00200d1a0080a42c0d00d00c0d811580e160704080d1881d00ca42d01e000c481a000002e40d000742130307a0009089050b21113a40300d5848040c5107801c4603c0c0d01011000240c410b8048140c2c503c012030402c41c42c8642144074071009802c0c00010000d84509400031a404501a51940c0c0781c00410000c0b503005107014210b6041040040002008404250140c11403690501100080e040c841d0b4000f000008015544041c500c81c11010b00f24000f034562004030021107000b2684000c0000900d0f10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 65646378 1250 65645128 65645159
    0x10f050a09090807120503040516060801061206080d0e090105061809070c0b010311090907030503031503010f0f020a080117030d02030c0c010504081b060105060d0905030c01090b010f 80
    0x8040424041c28000741c68020300700040103d0340d440c002c1100c0000143c0e150b4411880074841c1d20f40d6612440d050034074604020100c04000107010b4480c80511569410442080c15204e0915028180036006900c460080a01d0340201c0d44903c509054030301707602d90010f850190a0f20686843c40281d176203205000c01da00a14100d0019414881518449400c04001c0254420030070719140101070344640f10182c9030542a00162190b000c07006801c01c9c1d6003418403089400000c0c40008001d1f1601c1d50700c0311600da0101404a581900c40407640350039a940c02d4000e0300022154203c00c0000c0c1500e448400d000f50300c1405881d0210306180c000081c0c0c00f503220310140807903040e00090f61504210410303a00003580010041d00c1c10340424890044001c40900c1040e108621030850749548201d0100b62901c0b200314074940115986c0a040144281c3e12103c058541201403198040b0b15034002e86000c030b0860165000c141c1d001d62828102100744043d4860b424120350700d0280f46000d0b940c58900c400c114081 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 65647484 1106 65646378 65646389
    0x1050a0212030a1a03030c0606011b0203030c0606010f091203080a091401060602100b03070b0f19020c0a0504020702030a0b0c0c0a030e03060a050717091203011d010f 73
    0x440c03560101314194210300460903c41503a990f142d1b42d4400400c2181004440c03a0303110000300384009205291036008059a8840e400c070801c86580303500c21180513000801304c00020030454080c50102c015a000314084030350b004c1007034405882009005d4503003509595105884e0000c41d54210000c00020101400429071a113082d2000386032100b00d5080411840c606035203034082d6500010040c04499140e510f90f0b0b01c80c561025820300341e00540321018840011032040703c4549034089202c21182034112110702c4e600d0381766005d00040340036042d4025050351100c882080031580c01d280659004100c24989450044c2007207501781400d07004401100895404040d90b00685014042c060784060031400070002d910301030390002c00c0315a41d940c808581c078001c100481c164601c02d0103c2031500c200890300580d2035a603160001c501030340300c6107900708028840002051007400701c28030808440 = true := by decide +kernel

theorem cover : BRFrame.Cov 65467628 65647484 := by
  have h0 := BRFrame.cov_init 65467628
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65467628 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 65467628 ≤ n) (h2 : n < 65647484) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
