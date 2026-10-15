-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:18:52.897257+00:00
-- url     : https://prove2.me/submissions/fcd5b473-dea3-4688-a784-6dde2bd6abf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780755395 ≤ n < 780935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780756645 1250 780755395 780755407
    0x19021011040302090604051807150e190605030a1d10062711070210020a02010206130f11060702060708030412110c09190213030b0115172502010906050a02 68
    0x14803150711a0f0000c3c82561b00040645c1c0c0d540c11300f40c40c0b404011140181c0d1184001c00100e01c100340030000340009850ba00c000000026000340f00102c030400313030184d4440407800400d102c0c20b849038001c0c59100d02d20b200045020840c1503484118103081c10041e80b4240c1000f1181070905407a400b03250010302240d4103070480007110030085401390110071035001540e52245954103150f9510070030b6a400580090290b40066107408000c2d58549518408038054014000040c03080700d02401001040ea030060304582880ca42c030b546810030000c0c0034500070b074811020700954001d038075810080c2880e14484c010140d601d040c5810a0100e565400080341d08000c03400c26690095200481c00012501c4243c4035194183c840701681401c8030541d0580080340740c030210700d50107007100030b0810310226401421000c180da42c0b1a286800150150f43c862000300e04845941e1140840d40040b881d8445185c20b40f003032044210809801030401ca0061480050303440714681c1d81401114480da40d00150384402c1146010b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780757895 1250 780756645 780756649
    0x90d02030a0c0606090f051005120a020d06060b1b0f0303061305070c0b0c04091b08070c050705030d08220b010b0a0c0c0603061502031e070819021011040302 69
    0x482106920000c0082000c0b45034104042500458081c200c0010140a8100488240701c0204000c5841c91611140034100040764249149000c0c10b03004000c1c09402d403600c19409000949409000c12070303445a5800b030010f8098500c501074025030188a01c003040719036200c0b81c0c040c6010458102100ca541040042c82610b50b500240d85860420108010410365601d050aa0f88110440301c0540301e588044100502444d03202c0040060f02c03c070b084104014025000d0301c802441c20305140a010030100d1380820b000e18080c907000105203125000b2942703201d481d140440c1c20300100d4210200410302003001e00c030342d094240806a146582500c084c1c2104907054841009840041c82454103030100020003450042c07040c44041e120310340100072010f041c0c2e40d5890007001040c41d84507000c00c00304400e01c0404018801320484907803000305113400c04c0316810402c0900092b80300385400c944940c0c08020701243c00d031400c012038460030150b4002d481c0c401109000301c01a01c0c0341041c01c07a400302040105000513 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780759145 1250 780757895 780757897
    0x206010501170a0f090804050307230405090703120f0314090d050a1218050c060403110925030e100c09170c06030c03040c0b07021008062d09090d0203 66
    0x103040c980d282d03501d48400380c801c8014503039210b4071100700e41002d080c00180608000248111802501241d0b2402c0d66041d40da0032801c401d031007601c0300000421840d2545d107010f801c040d40241c01c42040d03440c425906e0303580d2010070000c0244070000c144141c84c070301c1c0040c1c4c1600c903044100300340c4d40b50982c4500d848070303840c1d4881120710381040501c400801c180c1801c80c441c1102050702d4002c0d40c010803400f024180300d281c035004440d00860700c0c0e2291419115403414080143c4080b00d50200040c4407010000781040580040280341800f401403132030708483c0c1080300d001100c1042c52940c0700020034502c0000c140d4208812040c0d601c421508140c42000c08507840f04a000844005041c21a440c1c290394004c0c60400d802c035840e2070f43c0604040b003844409035007a00114004c61149144a462964442c0074504034002d080c0007950103041c2c0c4c0d08499a4078000c88845600c5500105540400c8230080c0760704100303440d4a0080b1841108842101c3d14a00b4640991030b0807040e500c000300b000c4c84030b41400a507a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780760395 1250 780759145 780759167
    0x21070903021f0e0a0602030d0513021507050c0604270b0f150405120f1c0c110a0f1d0919022202030a0b010e19260307120207060206010501 61
    0x200500c031040b0400550b00c210001071041a0082c114140b040d99010002e590360040d0712031141e070034a4180401c061036a01050a022164040c0c0845800c0e4601e65003084035401204090700c650043c241416072640da0170000704040e201042e5054050481e0440e0311580042040e0682c85841c50700c14804455601c581e051401064101c458058071501d0340249801c07405191302103500b14081d680b40000a00c07010030464480a903101c01c6507030f040040202c41c001d10031811a044041000c502003480801c8403104403568149004d00f0304160b1540c1e41841c29440400c4c4d03889000c2402101d050244000d0409080a8104500d5801042c4007518031643c0b503400848580300a2142540b215510f0303450b03210139040d0894504101d000c649031301c0d00f440190041c0030340305641400a095911a101c043c40d10048049000d080e80c500c4000c01410691204d40245400c9040c1c41c160000303003102513007030a08100030308115204d401d56001490380304401a240012580060082d900700b0070040c400c40c0d070301c0240804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780761645 1250 780760395 780760429
    0x50606190905030f0109021f050406050a0509130606020c010309021804210c1106120f130203070902070b0603070b0f18030607020d0906030209060304020d02152107090302 75
    0x3a03014003960080d215012141d0219826002c0c08080081c5410306600c0034038924000d99041c00b44862542664103d031410b06110303000300348240400d001107482a000781101c11107a0420300e1600b62048009400e00c091020b1081d891915580140b04240c0e041c00780c081c0c910400e09041c44a216107a0000303500004011180010080303607000281807103c9503074544052081040300c3c0c10b500d00100f41c010100c100034903080d603e10040403544149401c1c24002c840d00304010f0b0030700e1200c689030002900100300700503241c031034524416121140560340602401004005010340180d46080e21b2500021032600140154801d4001c028200b1a101ca940d040315440741040031020f544e01c404540417408481440343c2c1c99050310500d4100a101500050228805a09601c5280c0c1c6560354041c22410b03403161441440d000f0304280049030041c1032200400090034801454044a16040080303144180c100200d416004011425011002031b0bc01c202c46030450070502d00400341c03900b142c001c40c800301c003030001c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780762895 1250 780761645 780761677
    0x1063b06010212031005033a1e02101d190609080a03021b01020405010906050d140f0a1802060f0310050406090c02010b0d020120010e010618050a050606 67
    0x24440d0b0b00c2403110b104480b009018050716810050070034801400c03113009403406885034420310b5900002d0412a040180000b082c4141503844015100c000d00f602e548800e001d00011201606c41d00000320321010a903021503005002224055007490700b03961b410250b01c0348081841400141000000c20b002c00003c0700404802000c44492400d540142501c0300701905685020030420300f0540e040d001813805031640700712032014400c1c106000d400c0384030b0f51003000c0c0801c1c52340c80d01704000b41c0554080c01d89001c581100050311f85002183c1d1440e0841200d02040f0584800108005290701e4403402d0708a41c0100c0f10914041140d134085801485900c0000412030008800201c0d40d0f4004040307500a070102520074080c4564820000000d0f140c00441c000c05542401c100786001e090042040300c0040d016503418001801c001e048846800c14030b140b0a60b15522140d1182d43e0703d409024a00c000c02d41c0310207844400d100195408102c3e940a0900f1601e9030520052142650f00c0304161500c0d42c199240c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780764145 1250 780762895 780762901
    0x90c180e070e090604031116090b03160b0a0e060d09110111062a070c030305041404110a0e0d06090309051512010902090d0215030411090915150d0501063b 68
    0x70078544290600502e1400c044800c010822101d240c0ac00d40e6045003d8040f218152075121031540707810410300600c031412105000c2000304510449000580f001c002d080140b504440c1c403018030a0742d551240944994070300701010046940e00c005101c0000442d0b4010f403405e414803940a0403101c12916200080b014810702048401c0340ba04100d403000c0d607000701903031080fa07075034900a000f58103d440f940b400c1e401807a0540c0e001d0700b0980a068910035440581d40d00e402c6101c01c0690741c48041800140d0001461103046001a803503103d00e9140e00d00a0715040180c03481c2104202ca0011200c803150081d45050107c00240c0303a941c0403e0b810340307409482c0561200403050115080c03410049000c0c1d42f100200c103003900d11688a80046000324000c5883d480c47d900303084280718020382c080c1d68500350b41c0e01241d20710029900e124422504140c070040706083f4564040b00240000310a48000c2d500d07655605820013080c4194582c05a2610081e07044050405254007200310301c440c154176020104040d0000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780765395 1250 780764145 780764177
    0x507081606260405060703050c120a110412060515010302070b04030c023f060402030304090b03101d060105030c0a030308090309030604080d0b010206010b040306090c180e070e09060403 81
    0xb40351810381d440190041528260402d241d039084c0179540700340445d01d40800300e444030241108540e011a1500b00700c1c2e4207034440c160040c00070708051020309801d400610020400f1256807914805003805680701095a0901030b08110405946058450502d8030411804002840041c0c616510603018281542d039600fa82c0040307007201c1900403e00c44410b032407080c1035407080100301e0000c003c4071007040c4842a0051b10301b83c0581e101003c0e035010394558000e000401005c20180c0041d50800009015621040940340701602075881d03c00c55100481a402c50650500c441002801d0042c8412070040c000d418412021403502c10250002804210a01001410a10040003203c8a100d4094201d4806140034100a215a00021040000d07141005000d03521076200241650507144001c1c1d03018680b40c40e6640d00d0009000b4480304841c141c0742680d0010310580b0340030764440c0c241480e04000c620150000d55080c10b001d015000b91044080900c10702620b90000180d0550241c0e05043c458035281007420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780766645 1250 780765395 780765437
    0xf1106031303051c0203180f01020a0801180e010218012d0f030603020910030b01090c0906110c030106032d0f1b15052104020f10051e070507081606 65
    0x1007000055000006000d20241503810030141d44600e8408d5400a0340024903442c00d07445142110700000f45000018400e8107015800303002c005a0a0000003403c1e003031405000d0a80c0c00180c400031540c4003d0211801550b00711180d4011006c1441d180302d06596880c001200048620070380c0c17800c100c4000d62041c2c6081c0240c1c441000b4540081c40c01e0001d00d80840c174102c030021140000c95070303004600b000003680a075034014820255215107410001a01300031080750000c51441c0e00c0c0c2d00c14410080504003584081c4107400256014195880b80c5003c000e00e0041c2c0600914029041c994215014501140401e042d09001d03903886a90040032204010441c2804007032500000c4100d828030320003032003054206008010316109010b41000c11440c0c01300720490000129006500300c0807100c034142080c03a0020b560440c0041c00d0a2040c1030007051100b00401d2021000000c091160000b210703410704c4002c1001c1c0000700004030003001041076101a001e401e581d0b602ca8241408500742101e441a09055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780767895 1250 780766645 780766687
    0x60102010e0619021605010603020f1c1e06050a0e010c14071b05120c01081501080a0e01020c2508030304260d1b030605010207062a050a0f110603130305 67
    0x44200c1540ca0050401b5030091203188012446241e482c07040b0720301e40c03d00040b60503c403051615583c1138130700b403138850003106440d465080141c003030904150000100c0512845024a03216000010300a4800f07010a08559040c40f6100600403841209482c08903d88115401c0c4c0da805050709181c0e010821440344400c8950300403951080310310000541e074040c006154602c1070400da9605042c8c0e220841d001c50f54440c2c101c1d51071300080130240040c201054680000f0342000c4250001840c2101f40200c550602444500300b80803803001d08500d0b203921700c09400302c074098172001018514505113992a0484105064061007207400c10740c85990007032811100340d4a540342d2030b010601906d081d00030070b00c202c00000032192300800e1801c0d4010803194070014104040d0b4140e030301e07180c00c40a82c0341c44682e048414a12042c403413406d8035030b56100240c410300056071540c0c400e071081c4020562034034000410703421211005011704428410040d0051540302c0c2916169003604205541c1c00c012014050040005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780769145 1250 780767895 780767917
    0x60f050411090907081923091e0d080109062105010608010f06051002070b0306040f1116140f0703170912100c030213030b1e1005010305060102010e061902 68
    0xc1e0040040c1c464020290601c106c1e18001405991812070044108682407905114442c030075a924a030302d144080070f0b01a03000802001251401c0610041d0350b58808201c40520800d074100c200c9101c841500070070b80601621a600f400d01140c1c0c2071840101d480c4401c03d008444002071410300200f884001c9d80840090156031000340140080701040202600300c500c5094018204020420001480480c0705003d03500d0407446d0502d0750f03e6000070803029041540b09081010740d50030b25110a0000c0c0401854000c040300d07031040c03241480d0300f845111003031003200c40341f09500280d001c2c0790b265a001c1440015207911030001180100070f01c031f000b1954007601e8090307500315844480c0310444107130004640c072400c041074030203120042402d10200d0503400340c0d900b4610500c0b5000e01c14030004000b01509548450209a883c140340c1203c0e903240701c55201940c40f2620346520260522541d43d1502030070340d104c0f0b0301307000a02c450b0070140c0e40710f5a251f500500c0c8450582410300300350301c080d03003940446419003130b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780770395 1250 780769145 780769159
    0x409210519031d03070f0213020f03040f02030706090b0d0c2c0a0504110403021509030a030908150601021005180d1707030501080a030503070c0212010915060f05041109 74
    0x8030740720141c024030414003031112003e0308405604001c440001291092944074803403900c00c025581c01d115070075211315a911030b403580034003440d1044a15140a988100c1c00354074945150030143c0185402c020305500301908004000e44140180c000000c00c03600d42c0d08000c0c0000030360120b41c020458403100504606458070f03803c0042e005400030b40110143c40c010003254848107007030795101008101c170701504886d903a46500b4401040989091244102c80c1d42d00304803c60725000b040e0740041d042500c85902240450b40100092001031400c22105150454108034038086050040020303660b950f1a00c4241412030300d403000510005941c0d42c041070a2200301303084032111400030801900884000380d0035408640783e1000a08094030901815040700e100c0f0740034000f1502c580e1401c58951380300800c081705010200c044000143c482c8043c016522032003c00024000c1c1141c40e20000b924158080411481d00308a4244501c5041da4050000c0300d000300c40c001080402404d003803042c4d000e207801081d80145 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780771645 1250 780770395 780770437
    0x18150a0510110601060503101403010e070e04121403060607031e030911030313031506050a090518060f150f060307020c03240f270309030c04092105 65
    0x3812610307001c0d0030340711035041d10f8144c3e0300d410040303030342c0e000848440c0c00074084228100f0050303c002028044000000e00085010704181e10102d2a01e0070740da1100c0e4a9900003410007007800280010024200002e00c2c0c903036030015844164004034000a414584507641c002040420103000300c400c03c03510340710202050750030161124068010400342c041500c0d040e1084600301403a1034044200c0d5400110302082d40c080b83d0842d00d544024001489000e000c0580e01e0002007482d90792507050400806007141e01007950319060012a0340303550302032103040995003d2008c1c00a0043d039020b0140d400384485070309440e40020040002d0400143e1440150041000018804170a078040742e90079030180140d007100d41c402d40c0c407040a1400041e020200000c88070a001003010315004105803034010080d141110103a1020511400716150b41141a038051b030b200260010243c00d06118016800130220741c100820026a00c841010700b0f030646640465182d44001d02425030300440a0311440d030030409940c00005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780772895 1250 780771645 780771647
    0x601050d0e01050702030c070503010b060d0908040e13030f02161a090405040807020a0611031207140c10060501030218040b040905060106080f10061d03030423090618150a0510 77
    0xa070104000c1500c23805100400300d064101405481c0c00900003411042c0b410500c100200000c1400c49001c0311800f00421000420300c008040c114003401001c8100c0101402620b0082d0003008030106d102c042d07401c51039169604c81c207404140411180c40d800f01001700807511880119902c035900c1a10752081c80c0c02c05000c240303d0041d014081c070744d209481e0b510607181c40b42001e5801100501401c801580200000e90b104138442e00c0319174010750141030113102091600210002904071100d81417540e40540b920784581c00c818042c5c00c00500382800c0c00c5280540500c652659480311120f894041d40e00d0725824911034446038000c0402a4010082c0ca080c0d503155540144a00750586102e100c110782c2e500403d40b100c03110580c21088900a0700c0c1e1b6241003480d09a061100e001c0c51000701d906000c02d000004010903004001e0b041c80004140b0080800180300c20030500c500c0113014103014184960b265083e07226800004c039080400d0b540c4410381b002d0741d04001040c05500350801c43d004681c2c00c61006810b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780774145 1250 780772895 780772897
    0x90f06030203060405060102010e10090203071503050702060a050105030d1103040e0426090607110d080f09031e030a050d09021309440403140610060e01080601050d0e0105070203 78
    0x440007204c0c1442107454410049007a03d2602c04101e0103504501e545141008403a4070807400c540c401f80980e040d040c0e992522031600c06400b0f2030100403a86802c10081c260b541405000c0e480b12020008203c01d5061501091f581c034000c841404c06e2001301c03c80c1503940241001950700602002c900c410444c0342501d090907030000c8452128019002c0380900e508010204003e9070065040030b0f0644c2d080000b81c0d201c6207901c6040d129104d4110000c07070b0402012942420040003441c143d50005603503035003010b0600d440d108089002100c03103092189400c10320340011080b5220740c005840c1c4140c81e8006201e86200606000c18000d5100000500c0281c0c000965001810340c5805803601c25094401980c03d0060400c030725003411840c4843c5c200294a035410203070355203c06d081044160742080d0b22580c0d8401070a0040201e15101d92024041008151107074900340007420061616654001590740080c000041c0505000e0600802041d20340750004e1070b41c0440c8042803420024421f07030070b0a083c080d4903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780775395 1250 780774145 780774151
    0x10218010f020102070f020621070914030c0603041202120a020c01030c110606010302160203060f0619060509010f17150f03070f031e0c1706011d070c0201090f06030203 74
    0x21500c0030000c001c40500601c25101d00f02c0c1c0026020003074900960801030180d10054107010600100c40c00540180350340201d403841025944c0b1402d66041c280300c064202240c500324050b100303900400013113009407074480a482d08170b070307205003403041e42d00100c1d8050303052070103d000d00c40d01841c0c0420000b0480f40c0c00241c0c0680d0500a1b20704001083c150201158000109154000d89900401c085541b0794803d900804070b00a0042e12064500e00315400a41810030644944c90340c40500070500580d4034040415210700ea82400d249450342d8980900580389004590846060112491290f00c0c81c40c042c40d150f00054000e440116814605250480351f000002344441d4014403100c007800322a070034009802d6080c1d6040b00c2e101c62030704c0d14540d10140d00340010904108828014010a0700050020100c240a0a4410401901c583c40b59005501e8050141d00c5441810b98015000028124680c2d0140d0421042d1414000c601000e00040e144251160f1105040800960001501701e60640c00740d40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780776645 1250 780775395 780775397
    0x4060b0703032a0c320307020901090507020709090f08190909060506040e041103060f040b0603060114090a110301080102070c0504111c060803030a0518010507120c1101021801 77
    0x2005000c68680c0e2001903c02e152060100307242c01c0c801004100700820207078003648800f1110681a88500b80d48403c0941d4202640050f4400f0801100310310b0003a844602511060008003d94503007004d0003540d501c043e10074240d00e660744134081828455180f40110300c085e0000c4c1781c0e50f40d5001c40c07038400b091820756290300030001d450744102258442d00c500941c2c040fa507004140c14103041c1484042004000050021134818540c103134065600e4405018061041d81900b0000c04c080c41c0c01d00b07162001007001040d081c466002080140700f010182d05038411100d40c02e54080c00c05540d8110202d00a0821107030052440c1e1b00400002404070054006109081c881d81c030f035407016596081440280d0304180c0300c1351185c80050100c40c080129514203003c6224000402203030032580ca50310181154404e0702c3c0302000c582c6400030082640243e59000c103003400018000c004601d0081c01c000c020803059078526000f19161450044441d20039000c18046111020086580e4840344810782440040c0300007080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780777895 1250 780776645 780776681
    0x31403090f030f0c011503081902070515070308010b071707080d0e0f120f04050f150c0304140d0c170307051504120207061b060609090303090203120703021b04060b070303 75
    0x1c07606d80302d414129001c880e8410681e50509802881e19080022029803c00440c032078140001525620426860300342c01d03641c050b00307984960030704000b0803169058103e110082e004208a5000500420031203911086403070209072228004d01c0d0002d910700c2810002c100990900c440100d0100c004602d034503484080e0012201c4840c0307180d149152a003d084440708200d0804d010400c840c0c1030070703004a42d00c81d000800c1041c1c5500082c8c2c8420340c80d0446400e00c040d0340e03c08034060010100781c0d0900c02a43e40e00f101d1010260645a588031260b03501405012280c0c02c5411040c0c074400000c00507030711403c0d0300000351154907a406914401d41841103400b83c0362100c03983d0b400c40402d0b00204040302940c0c0617a0360040170248007002c0120b03100140074221502503581c40000b07904c4540b1703c82c000d49184250390105650015004252400511364065000a10100002c8000035000a101d41d448410800807010110040300000d0061955901c00e00c914100041d1a504140d8140d00402d00003042c2a141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780779145 1250 780777895 780777911
    0x40f1b0c03120902010219030806011d030303070c06060b07060f2f0c070308030f0402040c0f090302120f1e0f010c09030308100f061812031403090f030f0c01 69
    0x8840344900910098082201808003440c042da030764106076801d50044c01201c0c800304c40709000c0c031a40600030b80182d00040e1140c003800380325a809840b680350312102454282d10031625000080e124800907100f4018000d040c46c160080040d1340d004500113010400085848100c5801c000307001e4100c00038003903c810f1500c500c1c1184c1400c00072241d510220804402c014080e1050040c14490b408a00ca03020f4034031a200001001800960082d48121050110031565091600c1840240c892100c4402c092201080c020340001e0303030101c111004c0b01c0e01119001481d510002140d401c240e07007034459065602981200c85503c0d0702a40d00282409095401c8a04d0205440d990ba070803201010503a0740040c241c010204080f030310030202c2c00c0c0c00c2407200c0c180e482c1d4181d4503040c40f8a140b540380c0c01500403460245a5101d031040488240c8010310001c5518184101240d40003402d0060350300b1051225907000c0080b4810000400428005d0000c030f800702e0f0350340d00800007424040c3d042161560095170a000304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780780395 1250 780779145 780779147
    0x30b0d051207021c0803010b07030c0b040c06122a03060801180c170c090a15032405011518031a060a050111100209010c080301150305090304060207140f040f1b 70
    0x704030302c0704d5001041c3c54210f90a011300c4400c039912004083e41000700041d41c6030045090007200c1030069100710300200c113003458400090030707540201520013849890401e403420590314600c003407600548001042e4181d00c04075442031703000b40001d13007064000d5803a100268070000410321300b08240c6130086003108065a603c0400391084480c01c100f0171141e810000c104515810f02602850b00401e452402041040b01481142107a8040354000d490000e002d541070401503000070240141401e8441c4180003941c1001c0005a0780030030580c4c1801000440f1521400c51a8030b4a0444061035008503038640301c00c2c8445140c0b0031418140c0d0140d104064500c000681980035822542001481c000a0040d481007001284002e4118a8003903042c00344d444006000919200021806019114001d90003e030000310000d045500080001006034401c00040c0415030300081c04c0c1040380d21010108001181100205440b042a8250302d50404d00303000e040020011981c000c00c100490b441c0314030a8140d82d590b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780781645 1250 780780395 780780439
    0xb061c1401051e0d0f02061305120309010e060307050c150709091b11070906080307110108010f030f05070e01090b010824040e030c0d17070c12030b0d05120702 70
    0x1004040c90f80300080e080b081d082c0000c6818499010300c485031000b24894001c661654001400c00358089010744041c0315900d02210071f100e20030a0440190305150050001038054011200c12a10604001c0000b9482d40d1203030045590583c00c190540c0d8281c0c50348100884070a9080d5500c0c00450302041001c18101c01c43c0c880c4020214644010040d4503c034804143c540a40c2c400c0c0d031214034081c040300032520360381d140108001840d00c10000e6a64941d9420001e03900c00741d200d540d50400510000400451008403003a00c01c1d43d410905418241e50180751152500c1d0155101d4010001302c1c07400024200390a601c2003200e24401c2e200c500d039035502d11108145000c6030030451a10300c42300706040d18540c101584040300328889036085a00d44070f07182c6007562130200300508420001c1d19114846060301001206607410007018180103440761740d42d54421a00c0203464603a1402c0555038208084c80303a130f51238400d8081a8201c0252040507229003018802640128070690040004247e0904401d040c62 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780782895 1250 780781645 780781669
    0x615010807050307030218121005060423100e1003050f0705060d0e0f01150f06030b010f0806031501030c080708240601090902030109021804020705100b061c140105 72
    0x342d41e030352842d615440c1c1070f0000d4000178a0481c0103256409440c80d151034200c1c8003021055024000c040034284241e840302511001042c8030701550501e44d40d800005000c0001080e05645992800d0465441d45a01501640140e104114008013641808030b0144070a0000c02540e001d44150f9130b0001c9200d080541c0c42100f03100e4240c20071403c010141e0040a19403050014214580607201000030015256080d55000132401086c2c4941c0c0e041000500072400742c0724010145030806008001d1044000391640c0078140c4401e083c003a00c44009940390340e0030f0204001c400c51401c840081e5503100e0809400c402e40c28021b208051040300d902080e450000100703580c640d821aa00c00007620800104403c41650140009050100078040032520000d0f41c0042c40c01b0f0243c1140c0140c4a024110440005050550b03615000368810401040407490104040c0d1100c10034039404110030300b072200418514480d523100e076012860701c5600301c0c1200510390825071104040708510401e81c0d80700c00030480440b16039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780784145 1250 780782895 780782897
    0x93a1a060904030e030f1e010c090b03040f080d0509060910110301050d060b120c04050c07030c0b071215080c030f060a050a060b0406020609120910120e030403050615010807 76
    0x2207000100040d03c0b0b190b601c0c1e00b007032019003940c090901181c0007a01e00311281c1282c0030340004192607200c02907001d02c9482c410001c0c600d4000074641c80c00782082250311014001514184c44500c1840134071010004640c85e0706034400c2d00300440d00d005240b03d9200c100542d1246182d004d000c1d1001c40302003103400340170700000403080348514503440c0104106e807400d030305201290a50707104c1c2714842c1d040d0748486404458140050182014036000f0342000104c3e06c008085003202030003446400c0101c0d91081e00340c1112940410245460307101c0103c00d440003c0d09584c450107040c10107510000414082c0e90010440340c0240c11120f0000b222001c06460b00214900324041d0b80c048400615040d01ca6001650010320011000807450340f281110307526030380b140d00030702e000d0390010050000701c0e40100281003141701403540840c1090b245c1400140c11503188616142000b1000640742e0003403045034030055410420303008407590742c1e1b624604182c951108450040700c407000403040e40c549500a0f04414460407003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780785395 1250 780784145 780784159
    0x815100309050705030a0b010303090b040e06040c0309060c05090a080d0507031d03120a1e090603090c09061217030f0703091e0506100906050303093a1a06 68
    0x10244045000340144102a1128412808000b0b803030388050140c0c040b401e0103200d038481558194140504580340a0740540c407241020001000740404c0c03103042c95004a0200c0c0d0104052a8402d800c5014041d09072001e410381d440c00030034000f516001001840e06081c19030305e040c80a5034032103082d0303250f1444074607400114200b00401030019120f6292012044014641e5804400080780840d20b440185031518840c81000240001d40e103401a507624021340812422254000800c100101030129900c1040c01b45a01c0b21080c1003040b094088a070040d00304075200b000300030354541452403407408080c020b440c18110000d0403149010f01c40d0449214030611600741c481500c400504400070000400b050719407081c01c99118401000a0100c0c00a0310b0182000306002e0600c484024440c00e41b035888000881d1030031000f08401e40b004010741c2c0801008a5611600074800a01c41c3d01e0064111103103202c40290269928607402c85080d00040c035401562034481110350810005041c207c191902c0b940840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780786645 1250 780785395 780785419
    0x60b07080f03090f01091203061e090e0c040f0f0c2a020103020c031605060c16061d030a020f011409211c0905061b040b09010509130203070815 63
    0x303250003143c10201403021a1403240c2560701d040c0c00c640b03140404880400900c892618221340c94001d4001401c092008001380581804100c1c541200381d102c2c21404540320340c0c070300d162980144105d04032045c0261045c800007040a44040090040c071980045861819541000311803007860302d01240c001c4c09015041a28001c44e01041d08850780400300d0405408228100d2880c40c14805490f90080c002695031081750241381c840d0400c1c000501280c0f802c5418810084401d46503520112002c2d0810070000d030241180c2c00c1507903d010040340c281210300c0005207200c01b40d54006604c68030009034a0007000315410703403504618401d0054550380303555030100000c0800e0240c461414014070003601c004600d00007880f8401402415681880d2030760170740c0d0b0408003042c050107010540e88811280890903c64103007201100c610b001e2400745010307941010620181c41e134010000c075008010002c0c000b0001810041d030450107540201e40d440300140315000410301a2110001110306401c0c01005030304415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780787895 1250 780786645 780786667
    0x1d15060703030f0207150b0f0102060c0a05031b070803190203060a03020f0409020a14010215060a0e09070b0301180e0708070510030b15071703100506030403110d0f03060b0708 77
    0x21141d80f00300207580c2000394500044d11205801c00d294022240400d8595152040112115001c400141076402080070050078000b548100c0341a0121810082e072070361038060907a01d0700c14490038400c40480e030020700c0100340160540918414240c031404401034660310200c090990106503040d6810104c2c140040c00180345c00b51148610080181c00025207200640000360f000c0d101ba44800e102c50b0f0781410881c055607043c40744924400680022000c10709001000c01e1540b08244610710105200340042130040d0320038400940204070000c6102d88070750311414080c426180314180c03d4000c910b004000c03800030102240c00c0040710365501c05001c643e8a0b04d01400b2100c486407020404043e940c0c9a0011503030340301c00c4030400c89168540d0b10b94032400369160400003014041d451407820482481000600105821028140c1c2d82c260380d032988a440ea494196514440f9400445480c054040e54401255010200c414030031030300d90702404150382c1d54102e041c0c1c52040030f0001c0e041d11810802a0840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780789145 1250 780787895 780787901
    0x12011104050405041b1415030c160302120f12010602060403020d1b05100b0301061a03370c0816080609130b040c090b0f031f151d1506070303 62
    0x540109171180080c403030380b0309400082401d6000040c540812122041d0681040294507405804001c0a0303451424010904811401248512491070652941c40410588280544801c0e804403200b1642c490008403801c0c00d0710303003007450b9406414451900005201e0310000d40e281c0903d07095001b802d44100d10740c0040715864401c03103080300c10300d2000d80000c0010380c04000d5503581c0030140d000090f6100d42c074010182556007a5111950100720704800c074145003004001c0b00e40001c1700301001c980d1000b82d0540640f084105417000f030b0b0001c0c407914207540b01a03c40e410514010301c059480b00d03000e0751054641d1480419103050000010700540000b030b1035042004200b500f0801c4c80c0c4459400d18030301ea07140051b03510201d82c21a601580302034104000034903400b42640304101110070384444501d1301c01080d030300d03500c0e455487e21942c0d1010b944004c3c2c0c0e07640c0e40901110360b030402c5524102030b00d81c46e141e4442600e00006804032485600010302600c4000c4081401e000d00620051070300203546c03000c03800f07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780790395 1250 780789145 780789151
    0x3020307050d05150a03050303010e0105010509150d09150902040621030c0507090e070f0815190b060f040302090a0b0a15031113240f051303020604080a0212011104050405 75
    0xe130842130a204581c1c41101410080d4400c500443d03580d810b06541c0c01d005603042e4855810301c04d09201d29400c80e680c0001c200210040c0c00b02175130702c409048400034041c0c40c9a0102400507180c0a1405800c0c0711242c001d500704d01d0007076a0510110750f0341c2c44911081c0c842d5205118000d094140440000f034454401000000c2c042c82c110f0f90f0058035031004c3c2c400c8071800e4408054aa0100604220741e0342ca441c0344c1401071600c43c0241c045101170715a07083c400000101195400585d01c0321340c0703648040070b0b0301c04180c135034010b0030f00e41c1c070b03041c554580b10f69075881400107a10440c1c030074000609450700c034010719071458070141c446201245000c105060003d0410181424191900c00c81514000440080d1101032003080f02001c030645407a01c212400102700e140d010076842402c802c07013407142d0051001070300c1010a1134000d5540d14400d00d00424180c007600020f501c00c400140000b40c9203000603144d044d00340210707a00451580600b0b8a10300300d07a041d000d062454501484204202d03d01980010740c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780791645 1250 780790395 780790411
    0x3021f082a030a0219050c030d0b06071a011d04080d110d0e0106030c0b0304030e19170706140c0a021011010516021605090402101403010e1603020307050d05 69
    0x154807440040d201d103603081218003403441607002c0744000d00804440c0c07051415496600b880c918181c041c040c46510b07841407880e07000d921174580000035040d80f192011100c0c41900880d10040d0302070703204e51541100000b80300340003400302d644034078554422000d03005500841c6c1c88202e051900048041540140c030094041c04481c1001b0f1100c40d03802c42031030048000b1319048100000b10386081d0b10306800e401035603030050203a50b90103000304400a9080048810820403c0b0358000020304441c12641010b0b40d80d410241a1702101c04080082560000c0c031017054528603160f1000480070460030800b00d00944c1c5002d040d036809000e6920142c00e014803100040c00032450640301d50580041c50b5400e603a025150301100040c000040110140d0500410040c441a4443c030b4900f0ba19003800201054000791019106500c0c04c2010b5031071600403101e0503002c10380401110307200d60b03492200b503001140485095070442c80082d08644091f200b80308407445401c3c142c42d118200700020641034001d00008103066 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780792895 1250 780791645 780791701
    0x5070e0d0f1728210b010f0311160c0909031e05070807060504170a080403031a2202071b060e03030906030a02090f0a0909021212070b09070e01090603021f08 69
    0x20039141d04030701362034003d00b0704144041342c120005000103180c1c907042914482010315202c0c540041c46019411035000d03031610050380c1c00421a50800302d080c05001e500c0010a986001a00741c105500a50140f0108140080d610710040904800303503070038801e0050040035102c0802c0114000b94070f41e0300154100d0700440341d00c40a0300c810003104805030b10611084000c907400e40100410954103000e10341d081c203407069011040c0003031400401e42d000a60150b0044640091150084c80c9042d60b040d50034803500142640a9810355180b44007086045024200005420800041c414107000040301e005120103020103140d6510000351800a401118a075940a0043e1010002c5941c900c242d08011342400070000a8042c075520400070580505040b410042e0020425581c10f04c0b0540c00780c44849030804425151555070b400c032039040464641000784412019400030071865001d51180701541e00c01c0e01d2410720a0741440326049501c00100100c000600c030000044c803220925850000818a550200303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780794145 1250 780792895 780792917
    0x6050a06021c05090d0807290c0705120403030806091026031608030a060504110414211c0302090307051003180f060b0604030b070305070e0d0f1728 65
    0x18800c0321a40c1d209031019131020901e0310034482902c5148c012102030060000c05010052952815200014115900707108041912810b01c0401d06c010b401c050403007230f111039030340b0307200e2030083c0a1590036100c640c00b4101c00c00000d03001051010b018005c0e80c520f2100200010b40001d242802a1314090100179140410b0024050040d44690241459803203a41d0030f0345c480ca030828247c01204c455600043c03040d0306024800d5a0b030030b5004112001e4915803003000315034401040c0800c800300701c0011080c50340b100c5113004403c00000801d81d10f5440300a800720b4081c410149408070145d000307400802c1d40c10f4108074010026450545a401d071480c40031b040202d042c00d804074070510600781c40c282c107859244020610f1010001d5500c40c521100404036007103410542140c41d50031103005d0050103041070580c1d64004c60300ea1070084c5001041070710000d107004421341039403405100380c07400c113407085465140d940c8002007141e558a00b56a100b51484200403c42c000840d500c84442e07141300104001d110440c595 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780795395 1250 780794145 780794149
    0x21050c0705011d0d09030c031104060510020708060c0a020616120609020306131404031b12020f0c0405070c0303110d060303091503020f0f030603010e011a010306050a06021c0509 78
    0x83c3e110b000300746000c424440c1c003028142c64140310700c14040c80100b0102903401e00000d41100703415801d803600030411031001041c0d40302060080005030804c50b80000742112980e4850760004e0b50005850110050300c08640780d0307000c032054900400f811000540c010703000003200c41400e1400a4052002480c040c2882d9502c068904120b9030b054104140c041d40000811150b170400c030f4400101c402240c4410404022054211100c90501610040030001c40c1030704140c0845c2814981500c0940140011800107810300019582c1c0c905142d0600f06030150068a55075450b291248074803c01c01a00d030680151201e580c100c006151040c0c1c4140c5810b0701340000079410b1090300c03c8001851081d254501c4050409100c01d800388041f440f130404150041050300640601030003907555810200f01d550b512500c8041c0041d0141407401c49424856182c0b5003070140d00d401d10000c00b07400003c20f8804000840d225010300034580d5460040c50b015034400d0300c1c001e00c0946402007003050f4400500d012410400c0b0540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780796645 1250 780795395 780795401
    0xf02060301090e2b110a051b010318080f0a020a0f2a0b090d030201020c1204140906100806150f070c150c020922060f060621050c070501 60
    0x311080540c0e55540d00d080e42903040000a07103058440c4c29002c50700e4591401040500100005041005040515460062420460002c1540d40441620404483c0040d102240b549403d04107000a0030a480320300c1300041003c11000050300301003e40d1904003c55440f0f40d040d032104e4075000451150305000740104020b50346d103800a40c4200c41c10405c2c8508400002c1101d01207010b4841d03c515070002c01c11103c460401210001507068034541042205800c0680c028044c601e503000d814024140c4501812286000070029038088000740b4a14506010610a000404640da550001c88119403030014030f00031000b003680204000c014070041390b5051140030b05900601d907580815540460000108010340c20780b40040c01c000101a4890740b41010020204004841c000e405101130368082031985c0b4a0a24540c00c1c0380e00d03804148110b000b0340c58054000c1158001b0703020349918103400451064410603a01c003400464440c010910140c00c441b0500400c80505921400e0390f00b040b041001031000c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780797895 1250 780796645 780796649
    0xc032a110109050d030506120c1005041508163b030706080403031a22060b1303021f080a020d1b050703020106051f03110702060c03071118010509040f02060301 70
    0x43c0c040c0400c5100500090243c03032003d0559407140d1102411036a240000242891940700d00300c610180b6410b0a060564043c0b0458000c12081d00140400d100c1058010b403070a0b0181c1040211444c0d444c1c1c00300b03022a00140000f10b039082e580c03401e0441e100220000482c40c1c1481030040c1800c02c080030707403000007450841c095025001160b50300f000c20080c15003600c1541002d80900e806800b0b2102e4420014448807010ee500c011180c1c0c0072110b00341d9028503940100b001d802900b44c241e6503a1152102c0b010741c92083d101c228800d0942c01a080e0308030344c0b0b000c10441c00d0000d984070320000d85c41d02101c140c06900188150100241e03200c03c440380401880c2500c1f6a080403940741c8981e640c205080c000e0a484194101c1809013020f400c01510904906c900c031002c88a086c5000a0580c40b10f001c6610b0364440d094000c0d40c844400704480ea10300102000030040340b840380c1c5a80c0a0350051506200484811755a0440703030240c5000100b006051021000781d10511403001610258030650000b00799400a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780799145 1250 780797895 780797903
    0xa0e010c0c0b0603071520010c020a02030120040308210a05040213090209071b0b07050406080106020106030203030909061309060f0609050925030503070809040c032a110109 76
    0x70580000a0091011000e50031401c154050a0307001c0c00c00c0705460345201160440410890000030020301407a0200944e5607505001c0d00070311030011107100007566540da0301000c1c0d10039468602c40107521580c408500c041c24034552001803d0a1441d12060f80e5a00a058a0041c1107051020140081030101220b886140603480004042c00c0600501030780480c8441440c030001d16010752403000d80d4401c10b0042c0d00803250310305120719408400c0034400420844000400660801c1e052018242c0c0000280c825200c030b950b194141681d940d10b089003130b44d9481c80041d40582007080000411300300414155407008c40030b07000540c2d0100c16a0f01c1d604456025200340e48155444484102030300c100d004010040071900020322642c2807280d04a921040761a040c1244a007000034200488080e0926800045800ca8103481d00c4422508080501c0d902c00c00b0100c1c0308500e000d1a0380c0c1554000d100300078042c2404a009004041c00c2c0882c4050340c002450020240301e04504204032420f000d01907146041c0c0300b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780800395 1250 780799145 780799157
    0x190f050f0a11010e090105190b0409321b0f0a0306060801120213021809040c060e01050304200a15090f05010801080d0f031508150901050c0f030a0e010c 67
    0x614200400e888140185090401120f9820413049a6503c200541514021556100181d64280e0100e503013650f240d2110700b00000118000500b07602035400103a030420310010106002c5445500d107c558036a402c941c40b24155840046405080c20640b81c91811480b80855480c0400e81c036000c4050340c00880c2c8040019441e450103022403980001e559005000032407440c92061035950004130007924806070021860360115480a5070040856024480381001d0042040f508150409110308041800b409000c41c0728080c2444155208804070391180390000c0d5040c500520a0580e006070355000080c043d800b00305072002140b144a5100c0307264460003523480c2c1d19100362a0900c2c0d01c04450466004c40d0500a620004100d242c0d80828038403000e41c144d00c0d108101c8491542c4c1900180151f0b412000c2008030072401044130f074800100303003c2c005a00c030346011a030743c0c0341100781d0309031881120084000c0070107100c2804500600006103030442080d241c003150305019108900d0031604540312903400038070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780801645 1250 780800395 780800413
    0x50405100e0c010207140a2c0c0715050406110d1d030403080a0f03020d060e041505071209080903060a0b0a0b0a020303012102030601090204090c11190f050f 69
    0x40e03184240e070302008541020703004403408100040d444141912401181451104020015039101c900b910058208100c48000c108222104525400b903c44800c065240741040422030300d0390543d040c1d4191641c800440b551071400c00c10442c0c00741c54050812600703103032545281803e4125a2000e06081d4607039610004880315005400c03002070000c20301480e0036403c1040103001250500c0119800c007051801c011010407500c04003140207100c0c501000b0a09807402e000460b040501111542c01180101034421000e45e174080408111031098400e1000306401c804160340160f4550000174400b07014000060410841320040380c100401194000c8015545003411f2070141340002011003d040c41030841828940b010001a41d00d02c4103024161442d80040e01c1e074600d03550000302c65248241d01801b85d4640e560f40324003d2020350814000d59002c06d00302000c00da54280f1032120090160b40a100820303001c2c01d20f11000e80800c0c81d8000a40350a40d21010340c0012070b2081054002c071020850040030181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780802895 1250 780801645 780801673
    0x60c15050106050c0c0f090c0307111606090e15090601020708061009140f0411040603200108222d0308090709050c0d0506030c0a090f05160909020a0201020d050405 72
    0x1101c0446544120746d89551407402e5111208034076442002c503903500c1d50f40c2d213402c04152016102c0440004040c0f0444810508441c403d030703181000c0f1942c64480342000d07611840c004004440c02c90300c080301e082c0550b0040e8070600d8405902500030b14180140c038003207512540441e0030507008840c1c942e2020410303079040240001071704c0764038200c0c5405c0c00d4505840c00c00c50041c039448000070788054004022240710b41c905a41c0d540c081401180c0c00407005d0f120341180013a05424039904022980480c00c079900080045810300c0c0d41e2401e00003d030038a502505001d5072003040c00d41c06500c0c1000b8601840b0324800750411624480f4401d1402030321050307070350710300f15480911381035264001018150500c020300108511520941e1050140e006010a4542d26500401d16291401120310341c00344400320000342d11a0a940300c41c400450000d001c1c0035960380e1071681c1c140411040762442c00904c800200700b19200e610360241400c1c01340c1c0d00c0090302e0050084444810741c3e01c1940c0c182c0f42d9402501e07440d4540c3c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780804145 1250 780802895 780802903
    0x16080f1303110303030c19020717150106030501081e2104142b240e250b0f0405060307030f0b0427030504081207051501030b01060c15050106050c 64
    0x104500f00e00840c41d52401d0308010321940207100816210040341c980340008180244020406840cac6084280c00d280241c41d00541d0340d40c0c4402d9554041e030004800402e08134840d00030b19044ea2050700080a6281c11034400c1003210707412a851100728010034200c0071442c9150a41c101400c5840c001d0310780c0311070415580c050411804240588511130345640071248261064007480c41b16445040c11004079401d0526203d200c1c40e00f400002c9082250340800201c0b1400ea01184049401d14100c903182c03040410f240811410b60a01c01c0c0ba0f0100b035000070800c846c03011008041d032200c00b001b00e038141682e0302c020800640080d1118004241c590440070f500038201d10500f440c1e080304403400c0c002c1140b01e801507141298802030031400c41e003004001c80706040c00360007141e0040020300c084828000f943d5030149095000694102d406004444c1c103d01c0316501c0c0041d1030f040e2600107094450036460940152240240384804803000d1024007400c0c1e03002d0f045442024024140c40d02c420f907031004038480450130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780805395 1250 780804145 780804173
    0x1120b1c0b010b07020d140c03060a020307030c05120115021c0e0f0f090c090126070f11030909041109070f20031818100302091005010516080f1303 65
    0x1608605215140161b91a0b030241c84110303812110704010b101d51100c800c2e05144151808540521514092113000d01c03035640290b2166186075010440f10305a4202180d46101e0b00c101c00243e039403600c0043c05100000940a81001520b004a8070150b91140000d00002c0315103116501180c8961150055811301aa40450b20704040f50a00e41c001c0305c0780c0002d0b10401b0058001c400c850b2002c1140d00e41d0f40d014035030f9a981d040078801d00a4000c03510500d1041a407000b01c03040b00000d00a186403051487c01242052031036035119020b9824550a20180914210014000d6510748240c03490074440d80c0355584214041d01640c0e4a001091420400142002c0c0c00225030001c0c02c2482601040103500220a03a42c2750074038178406081d007030800c40008030342da400f10b092400c452025205000c12800c2c82001d2504507403003900e003540e860b82c6400354002400c465104150100f24100005200300b15041102070426100e1a10030b800c040e02445001e0311a00411440b1340003c13072400040c01886160b40a40318 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780806645 1250 780805395 780805409
    0x60c0903030215040503130803030108120a0503010e04020d0804060314090f10110405030607050a1d100c020a180603030201060f0308370f08090c01020c01120b1c0b01 73
    0x1a540c5959402035940d844031100c81401560000841c0c1045018030864041416402d0480c40d09a121041035449034400e2044000034030810002e0424000b140c810b640e540c940d10b440d42415a07181c5902803e14540c0204100d030701445114500c0002489078000d480a8583d41e40c000491042490010b15140005840c09800d540404040380d5001000518159080f00014000c40c0140c104040e40300b81e4007440d001643e06014400802080644c440e000d011445190354544107110365404100540d55000382d1141d4024030f0030300c400c241c00e6000e00070090049102510080407281c1d6513000d0000b004100200118054032540204281982401a82c0c0908403400c428540c181c9581d0f03403030526100c0d000d038880005030001000d0300ae901e41c0c92910610072035226a9410b00300d040721001800c03d800e00c00744202050780702010844404001441004202040e0000c065880c0584010340f80050350b4080c0140c1d85496030042c0b0440e0306c0d00c58284000c0309024034520005003252070f00c6601290144c11080e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780807895 1250 780806645 780806657
    0x31a041202060421050d14071202030903041215090b1501020106080d03051f030c17030a020d080a020412140105011a07060c03060816090c0e03100506220603060c 71
    0x20004c2002c200220140e99041ca2050544410102068402d4010f20400380c000a103410541e048100c1042a0710307100360003d41c0d920300080c200c04040d4040340001c4d18401030b150701c01d106c180705140300f80c000f802015000d50380c00721101c078450055100f5100b41600403920030440c0300c10721202d5408042d4204600000340024440182490111551940500c420000b01074640700451f010b4418440c1400c00304030100041603c0c0d43d124109520f120003540326603c41c04d201c440d80c0310b00015012060380d007a010282d02034150410961421600041c016182002c440d508000000f001d801e08000142031a1180503000045101040b000b0700f1100141d00c5000d12a54505040c010000c02c81e08035090540d00641c0010884c8151400314000c141940142d1082c0c80340103c20440d15000308000d000b11428840300384200d8000d40011506015100c98180d050b074000516050700b1841900420b60109020b0b100410305c100d05e50022610541c0150b40c042d4555a8910034010b000b0540580d40101c0c0040c1810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780809145 1250 780807895 780807901
    0xb0a09030f2102010c0e041d12090319210302040503070305150a06120b0a1104061814060702091801050f0a0c0c02060306130e03030106090602070e040b0c0c07031a04120206 76
    0x40e01d40da011064087c452582d5000395036120000c24200100000b03900110f44403e0301949101166502102c001c81c442c0c0b240d201c4036884039140900036481580e110114421140c0e0082200141081c5072407250217050b001c0c44041402c0e2030400c140d000860040f802080c0e2451403006249200341c0180c92000414281601444292a000c008441e082e45c459007840c040d0f540c181c0514001c0104c80710b02d4a6150b000200051001c2d07100b0410103038016018803009a4554528102108030056a021900030340148141c8015203803055180c0c1e484200300321142c80000081040f14210b0b481200c1c08210303e0002400e00641000c1c6200d84041c03958103084c80701c004001074000509500004200501c01d1000104a525115150b0800310020b1003000c2282e417a56101c00c005001e0480c940100801031081c01e00c006159884910300c0c41c05540c010322030705150307201d413003400341154840c07800c4c140944551500000003940c948406070621140181d00800c03401c1525140d01c410020389151001c5600c80414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780810395 1250 780809145 780809147
    0x12160f0f14060c010b1009050316030c052107060c0c0915030618020a030c0515041a0c031c1b08040312150b04090f060812040b0a09030f2102010c 64
    0x11103101e40381282c0c016112840c00c003015000d04040c25030660410449000202400c1c0c01c00c3e600001d0324000c5040da00b02003c0804400c820000e41d100203024941c00340f00402071400c00e0440c11300c412410100780c80400c0007481d500c1d0303d4036005a1210340060780044841d010300071800c0c00c0c40c01401c04840709001d16054031182d0981c400050202401081c1e86018140950400f81345a01380ca950150045c1405a5281071000000c10a840f400b8058a10005404101d40e0028211003d4410081200c80003010000d04406160082c62418011344410010340c03d000c035401c03072402c004010160b00443c021254200032105079040b000b1301d0007440305071018480040c1d013200400d5841c2000707000c0003e0f40d06e2400c0d40000661090f074001c2c101e00000007800b044480690300403000c4026116014020950394149683c0d40e41554070022403050300c1403105000e01280800100306160359481e0a02c541c54483c1c59844414101c16801c0303c5c1c1c04402c07a001c0000400d08101d031840e103003460008011000742104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780811645 1250 780810395 780810419
    0x120504050c010e0a0b0915070212010920150c0a0b13060f0203040b15030102040510030f05010f0503030f0304031205070f0306090513062304030810121a0612160f0f 72
    0x100305100c0ca141e0801f840140ca8070605484070690020940d540d80540011071078000d001e202402c0e58850002c032141401040d00c95103d1342d4160000d07202120801209421421541210788058454020000c94502203040170083e0340c081c0150805042031394060340303000b00c21560300c5040082c3e080d006008006c00305484041c4151710507c1c0d5102c1e003c108181d640005d00a1089805c40c82d400007800e165444040e51590002810303028124042003640d8860341410041c66a0b03100303a0768598410440458811100c002440e003042c03007402c0c07840885d00703a942c103101642c0f01145c6501c0051164841407817000d40c107004500052641600c100854108403d0000c86040c20303400103005079488246501c0810f0500e035000220300d0007c1c1402d945801c3c1440d00900d20a819100b00740c4d910400f407400304d076142801c214905016131140e5040000140000c40740c01d0990300030000781c1e2140c1c10a50911009800b84803011005001d0a424065141010721b100260351954000e40b0983c80303401c0051000f01c0d1500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780812895 1250 780811645 780811657
    0x1080a0b010e070309140313090608060103020d08041a0c011a01051806090301050a0506180c1209010902210d0305040510021318060609060309030816120504050c010e0a0b 75
    0x907030500c0183da6850303041c2d002e05203407140180b102000c5011241003501c0807000d044c01c285100c00d07440c8d019a65212010594496008144603a006000108014944801800034151040100505050703031514001080c01d4500b8070440c14680000f003c2d94480000c0c41001011080c100c400c201c220b100d4070008180c0d0240716a107951318040703641c40110716601c40007078030398003003004009003e90320b024011803018180542e4150300581010080c402300d40401c1e590703680b003a102c2045550034452189403010300c0100c05041d008495503240160400b60302c0d412564144150a0b08071055a41040a0200e10b4600b4003520001018502014840011170102d000d0710004ca44010260b25000310000c4c541c42980603030f200d4004600e00560441601217250442d608403031f03403621254161a5217117810b900351107204400400080c1c01c00009000c441d0748079840140505c1a19040d010485c00140c10021a2070680307090750301d58065a00d0140a6030300c042034940000050b0741480c001468101c0c122080d010750 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780814145 1250 780812895 780812909
    0x140606090717011701060807150f0807020d030209120307050c121b211c1202090d0f11030f030c06220b0603210733020d02070c0e070801080a0b01 64
    0x880341c1d4000e4440035081b00f00076040642c140ca101d1070391a40c02110350f10b80030203080d0204201e800015403240c0168100e91107010f142d005018545540c9100f02c00942c8a0032120341d2000800300c40381803001c0100b001c2c00c04c1038424001072001d007a40b0010010803484002210001d5403200e200c0309400c01810184010440e81a2401c100d100f0401687c23040b859582d4421180030300c030701c8083c3c05848001090103a089000c6840342100400740003015016881a182181e4200e03003400c2519000508d010100c1d00c2d598050700c1c0b020180640c03100081d04081c0540000c40b01c170307440428050101c4401b4011103801010ba400c44010101c89011000d00b40300b2210030181c4120b20302000201c00791802d004038007a500701d001c00c0801018984d0804001c40d04600015500c003044401038004030b07000402c048003100803015002c501482c48009801c041d40c0b0041c18224884d809100310340c000f4400419100117000001036015461400d030310010841a0148d0050007541c2c48103203101c01140081d16943d054901c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780815395 1250 780814145 780814169
    0x120f0c150c0a03090303120c0e0f0f06160b0c0c0c06070501090c12150507021c0219050d30050405150411040c0201060806130f14060609071701 63
    0x6032108048240507541c0301c94071601400711600d0806034444074100a81e4800d480d890003042c000100041200d031008180c00104554902c500403d1074105d011009421004041d14040c0e40e4072404a511900301c5c10703c041d16082a6452a4200861513511a50100c0c00e1005103080800c41c4007250340d14410382c02154010070001070340b60300344035007900301030030744da4019403505602a0780748050103030750724105c01c00c0d40e203420395420041e0445c20b24002c603402418964000c00c1170a07404c2c03800f0031000c0e0f07001410401390310821040d840c402d600000c0d441d1121f4080c0d0064181d607001050094442c1003aa0302e4401d98111850032081240200c3c01590304440ba2140c0001d120380c1c862800b03910340307007240404901c1000080204010041c52141070b4094800981d001d010109140c132042e420780301207000e6100d4a030010b500003030f81c460f48521902d5800380140618013102c480303500d80c0140803500e0030b21003206030040700c100251400c00c10806074001429242c040c00c28860041c250440071b806004644400320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780816645 1250 780815395 780815419
    0xf010e100b060d1107020406090e060106080a0f050406061d130b070c15060819050a080d0204050a0b090a0e090604240e011a0102070608011404020714030702120f0c 72
    0x981070103a500a1a218004002064605020781324541100204900c07960030a140421036400a020f070b5049981c0500081895908140b01500c40e060014140009683d46003120700e075501f19030003400d0060740104070018000f030800c2d281c108640884d85540140e030b0303c2c2e0018002c05024a07020400f03101d4002180c6011510341e20000c455221040402405284480034203a5803a0a994021412603c80504441031764404502da00326000704040058003580100d600d003001700789508002c1204821281c00103281503150000216064640d800030038003400003013181d000c0c50820084100c0a00028034000c40c4503c0c1901d400f590711301005000400b1a031604800c50b9020b103510580080c3c410358513405000760324031000640d00138028821102800f43c400210380ca2170754000b249440903900c603952440d0040e130070044501403030841410229000381d800c210f0700000c608100302403c080000203000d180d807840d440c01007141c58fc0650200400c1500807183d81c50f094034001441451042c0280ca000d00781e21 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780817895 1250 780816645 780816649
    0x60207030c0f03080a0f0c0509010c1a01030f14060c090d0c0902180301060b0a080103020d30081608011206090218090f06010608040201051b120a020f010e100b 70
    0xc1c05508006015402c0100302104058105150034490790354a10100840c6d4064011103098807001803461000c10810040c1402c254400e50389901003601418410034081c0c08080c03a071111010980c8265069101c0e80e5040b8200100d000400e804500c0c035034000c2c0581c2c107102d2420b030326520550710080d1040d144011040c2c00c0003140e2202100030310100b1000c64886414034031101001c40da2a6555110303529010000c80c1180107007058424204140c0d961981d50f038256424030034003021403881522269901c2103014040505d805c00143c0350441a0404003011365803150203403030840c010305400031340c1d00d41e04481d44040d030780003510350f04442c508410311042c0d0300b41c0e0a261009203004c84000c1d4008809042c0390741c40a20311503849000e144510100d8901031680c1207141c0d200c220030301680001820300d0010601540c814005810484d40c44240800c8846403d896549080f01106000c1c40401010942c000305940500044070403004280091186c0300190345d21320385404d41050f10f03901151b510b9155404507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780819145 1250 780817895 780817907
    0x5030f0307170711010b0312090d08270f0108190213090e0303070e0603010f030f0201050c0105070906020f0304030309090c03091401020d11040e04020f060d0c0504080115050d06020703 81
    0x106a80000005041280000b813804400d034003014410f40c01e100340031100e401d00040c1446540340f000507540c1044405400c010b2200071566050758440020b003e401c4940001491940c01c04503005000e00b29414010180054112400191810b05c49090200140510182240417003071110440043c0c2c0d403000c030035404c004042c01d03801c406007180ca020300400011800200070350080c031098a07403a41e21402c180402c52036100034062035200140c202c0040000603800c3c1e03080140d6520505090f810800240d40c0039007100d400f21207040004031020020000f00e5014400d98500c001d040c405503143c6411030b20050045421440364054607603032070007400300d403a00c69030000c00c1841d8130204106251400c0740049000c0d4000d10100c00c2d891380f40038134605440750f48008031021522a04203071038841d138442d001c00c490a4800070b50ba6421050401005080c0030452240740982401515540e4071241000f042e1802c540003c8080e1039074041c034210901c015595480300700d40f00360307100d040943d079003816240071911 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 780820395 1250 780819145 780819167
    0x30402280806010e060307030f0314040b030a020310061b0b1008122511040906091205180d1e05100c1e0f140d060312021c0c05030f0307 60
    0x8103155060001c01e000c000482c8060480d200b11040124a4841c4005c0640b1440070740300040041c04050303290f0000a01070801054059000072000b403d107960b5165080248d882180c0c0c65030119400020451072403107001400340076201c0f1707140c40c0300380740c04050915122190040380909203444280c005002144020a400c02400000d0280d440303202409210001c6500500f400306280c001ca003003040b0001c0400c800b07401415407c0840c9003040e0103900244002090901020364500740c503105110080354404280800801c501c1d074807184d80d962031010082c2c2041d961902140b00307008088407400031800c807408484605000f0310300e86a0300b21192504501d0030b40340341d803542070b16410510070090058000b0351030a030141d5220346114042403406e9040380d2008020f01482c012841084400c2c43d00441c3e100500b0030b000f403108001403110b03186c2d100c1101807d907202c680030059001d440000420b0101c0481c0e01514070440c1440d1944000300e0b5112501ca0144c2c03100070701119004000940320500c1100c07600b0b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 780821645 1250 780820395 780820459
    0x50c0d1a06070807030f052d2106030d030203040b0c090d050105130b011707150207090e03070c0f030c03060515041410080d1211190c02150301030305030402 69
    0x1c0d0716402c80c503284000313070812a804c2c1c005c43d000c0b4801c440090700a1003100c245a0b503054288007519521020341d403500c4400c2c660259402014004071500d40f07004c1c5c002916225000c038603403015181c044205498a42c44490304c000700360042c07040c8000507a44e0003c42d034005140061f504d8031546003102260b412013042402901541c2071501344880b020141800c502021702502e103490301030303881d107409601c60751400e503010740d460f40302170340c200302c0300c0b1180a03000031000c0c4510541d1401940c801607441600c0390700da8080c00e10781001594404010700b5170344000040c414500c1c581c00360b600e1030301c2d000000e0a091002421a5440c0c0d00065031080800c5103202c00e4950080080003401c900e8034200100f0304084440c034191441482c000f0404513400a03410380307607000c20f5580f180034105550307042d0043c00c0c081000c0d505104091210928984e4808815218549180d995460b6005a40104003a04400700001c10242008100600110340e110007181da1040c0c041c3c614a14401d48090050145a405c0521017 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 780822895 1250 780821645 780821647
    0x609030c2d010302030906040b060a1203050d0605100f0c1b0303050a121a1203040f0b13090903090918290912030103030c080909130510050c0d1a06 65
    0xc891039000700340c0744151140d14040341514081580190f040b0b200913204000140d00c9100000c00089003e0400ba82c400f2010f042d416460f56035880015001e410928224003003500802c000d45d5085c441e200e43c00c0200001c035241d54800501100180c042e04008041104005080c00401c050051005843c500c00d2113007048c1803056540c03401c00401d6508154001c20003e562064801218070f4580541c0300011800e00d00030b002460b000040155620301044d44d454640400e0000041c00f9054171038070001080b100e1720095852480200f080d00c0608260855145946800c55120119a10441850036a03e01d4000002c140c5401000c24100d04641d0700c0041200c05051a4401805c424120b1045500c05841505030b240d20b035080303d0b0b606c1e004109185410808180010000700313200d104102c5031180525105403030a0321180101300041021202800c081c1c02c2140c82e60300b0000c003089950070030300358050100b05600700104071001501c6444490300c100ca84842c01c08058242e4003c0251901c83c00070301c82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 780824145 1250 780822895 780822919
    0x603051009030e041b05070201020c0405090f0f060106021203040503070b040804050f0414061018060e120c311a090c0f030406020711060703031506090807050609030c 73
    0x8005090324810850004a1036504036080b414103000d2401a0410602c56014909040208540780c7e0004c01081c4d04510841c0403640d4191510301c81e140c09488004054040190000300d01c51401c04003034100d002c039510103001086150313400b003481c510400e21003408070395070b4a5034100607186000321031001c0d204041c4c0400b0700c001c01140c04000c0c81110f40c143c901404a628503c01c100c111504204580c18542a0341c1c0061914500002d0420002c9040d04010b52021807404400200420725000740d0081507940090a80c58036100388040e1800d030300000103026150003c0003141120400c40104001c1c1500343d002241007280c100405216402084e01c2005010300d90300c160720500b005603480d14010209080070805119001c41140d51010f4124500707851512160f8524000f0341c0142010389106440d0700d400a015603030f4400501400d40207550100c0c84503e800910984800c4540c003001c00e0102c0150100f00c00d06000c135140040701d408983d81c5c0c1c1c8882c0d549021a0078040b0902d01142e00c8141c4102c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 780825395 1250 780824145 780824173
    0x1290403030e0f30010603050c0f0d0b01090f1a1e122a011407030813021c11030d0c03031a09100303080f04021c02030c041128080c030a060305 63
    0xc8800c0001c980b00051131007100652a19080b1000c5000c0600103070401448a001030130010010300144001500d081d018a149485240b0f5061082c2c005007062920780303082040c00b0078103000f8299910901b0740500f2142d504400020340c080c0d1481950400080c0c1e8842030f090b00c0c0e8030889210712100c0034205488000041c010100b158030f4219a9100300c500e0004081c02103544641031095800c0e101c003c940f89842c201d62030942e40100014600c2038400824210040143c40d450301c2c652205400c0b00380100458a14070b0040c503c6000c01480502070350010a000140c143d01503000f00790340c2c0d05030800180894900030b01444000b80105025040b500500500042051017080401100c1c01b0f0756541480d510307420100c9100c11410f030740107903108151036407005020340d0110f00301c60740c0362000b4100e511036500e00001c501035846075246502100c40125081606a003c40c02c64001241408440d0000590b51103000d800b014010300140700b000c0c8017100050100155a000c2c0024681120442d501c00c184184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 780826645 1250 780825395 780825439
    0xf1e09090402212e09050c1908030f070b0f1506090a050307080601080f0f1c12060609050a09050108060c2a011505040207120f02100204090501290403030e0f 69
    0x304d40341040c500701280d598107000354403c040302d9944c010042c040e404500420000308045043c4400004601c000d8000f40c5488208020f040311542085aa0784a02450901e5142e0850040010003002d402d13408101010080307100450100b20100c4001703855102403004145000d14940040c3c0e00743c816401c01080e45807000072218100c44081d000c80310104070218255440b0810395528240c507034001c03000300c00703656042000c0c2442c040701c0d880c24140c2020001d00c410181c030340e680d000101103812000e06110a0a01020090207800e80c000288081e514044600740e48071002402c0704c00c0c441c004a041c00c10f400c44c44028403200810180003c1280c1500e05c8454001c24141388400380c00440b0240001d160f007410b00981c3c503d2a0000310280c2c0502400d8001c0d01c00710b101c2c848007800c5000c3c4006007401000307580f0150001d0700c4640b100156039810a089894007840c4c0750300d500050501035000c42c2e81c2031800800c40b825aa03041ca000c200e03550041010822031900c804030154802601420000e20026000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 780827895 1250 780826645 780826693
    0x1060801020322030e061c020d060527060d020d0c06031406040b0d15020d0e070306050709050d110109180203070e101202031305030f1e0909040221 65
    0x2011100c00742c0800403034003c64028129004021501408021019285c1800030b0309900d50f04440050384030860616807401c9034081c2605155003030ba180010b1000341407480c280460400b81400407030b4040c0041200610440001f070000e481914410142d000b117440e9030160b42540e562046c3c049800d44c0d181c0d0030103400b403c81607403408001c0c4d42007400660249000c2c090341c00001c2003d0403e050144094848013900200ea00075500003d8080203521840d050b070b4410000c411000601520501b4154680142a0341d4081c1070310f000c008003240188456520307440103203425a407013048404020440401070700c01c01201c0d030088264854cc1c1412919020301e580040d40f0604e081e560342c40f40f10800f442001161248802e1042c001800c1040044882d4102e80c011a0824401c400210018019030389403459039020a011f58664200401c070030f8005003044004000348443c40c08150b080401342004114103c0000388041c5c41030a0400768010b0b0020344041440021141d2001d55118021140b6080100c004007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 780829145 1250 780827895 780827911
    0x1806090a0b0f0706361109070f030f110405060a02010608010c0c021215181c0306150206040503182701050f030a02030a02151204050d08130203071a0c010608010203 72
    0x3005030342416140a042c0c000b21007440b1820008030708200201724200e550721810031100655104011362650b903413100e9403442008070303a46181d24100466002000d45134503001c014101340c18551b4850035017210300250f40940b08190346070f9072200e58810040340588403c0d0300c940015480c082c1040800c0e580035200e001124020f44a503e0101c00300d0481030b507604003405d08101480a04001300c2c2603a40800200c0e20108518402c5540c2662469262510180140b0b48840402c1e42d0304800c1007501c00f007220409040c0d1607400509036501d01521007e44a20680c01c800301e03031a104a40c40540d0303075241d0510210424844406070140c6118030040042d41d1020f003e0ba6224114451918629180000c1e800004503030140c00780400000c95401e1120221520588201d40c0205000007640c00200445030351040303000346d00805149034540c202a1000d000500800721508180040c04090f03203001410350101c1d40e446400329040704112403036140e24020081c100b8055420840c00140c04030054000e0341c010b10b40c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 780830395 1250 780829145 780829151
    0x1081b03340b090f1804060515060f03070f0206041a04061b03091502040614070f0b1006090e01052809020f04050301061205060403031802040e0105040c0b1806090a0b0f0706 76
    0x24000030003a89811250f0704145c1d81e0017201c00140090000d801294001c0d0b035075420110003240c0e1000213200d5400c840f02c0d000c3d10070b0012081100301d90384102c41d80c840c2c1541d40054401030400c1d0319880707190120202e041c4c94443c0410301150810200b035000020f506000c0a081800c10700110004018120b1144296458403842d0a03001089030203200310340443d400768642e00d000e4031340700d14440515005544117440d03481c030940645010500ba4459140f06441c64609018000d00b01100504245080c1d0405050801160700501c07050b22a03903031170780000d130b181c0000708a00720b190106600d00217504d0b000185210300100300c80e64101c1c26100038009a880c100c1c000c0c00725035100c0c0720f00340b054190880c003d059036000b85c01040200380a0f611500d4044201c61500c0c1c1000038a801044c240e500d02d04e21b48880c0e0307640c2d41c200030500031032a90700d0021b4408000200d1a010581c10054540100107414510030900042c0407400381d40c0709005500100044482a030301c1d010558204c03070090700035490903950542 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 780831645 1250 780830395 780830419
    0xf0c0c0a0806060924120f15011a0304030f0e03010b0a0f0806090a080702060307230a0215060105090f0d0c0618080106060503072f0601081b03340b09 66
    0x10b50980c03544840c0b0a107224172000013211410400e14a0248002e5a40c0380030305510034a1a090500404c14007087c410308501c000c0d458104450b000c050003600200407070006005000c0025403204426807080010701c0c104404070403110000e0f0061644100b0306601200c0c03054001544400d949102c1c00f190030020a6802c540d0707031702001c1c0d070307ca0320040c03c0101006001c100d92001443d200001c5d47d00040c1c1e034a0010f11a5600e0811800f040c100c8401d100b40040000c580c5561080c0c0c1006003100c0c110f1910381d0780743c0b28244600040c00341e000d0741248078420021003049610a8458008018646411003491810a030395280003070450468416500d030f44000100c008604600305000b04070880c2c2c1c099403100d1650351000b008881008040b60045501c0700502d00041402d80000d14903c09218036102401e0076524200d01c152401e6032134010389004001c00d2140704404d9801095400140c200310b0041080761109204011046111a6110354046280500400c0d001044000780155181c1500c0c40a0408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 780832895 1250 780831645 780831661
    0xb03010501030f0201031e020c070e0601030b0d20090a090209010b030412140c0307150606180b0c030903070f05100c080d360221030f0c0c0a08060609 66
    0x50400d000180c01c0c841212030f400e0043d4400c1d0b201c51101420589020400615801d060059a21040c5c1c1190b1513408a082401249201ca8003660013241c03d080821201d210031001c68200c0c413400303002a28841807030358003581181c51081c0c1d0031a070701001840e11031345103001d10909004100d48072059008205210012410304bc80c007080700e01841c0c20210301c030641c0315a158212420844c1090100c40c1c0101800040440303e402c201400702c03d8840e080d00641400d07500103403421119103500001c01c005800c02e0b001c25041400f5810030a0f101c44803501d03940d41d00340d12082851481021103982e050700c00ca4000042400311211301c40103460040f260300c01c8040380303a00210780b60b25043c9800b602c0100100040940319180341d000b9540741910f451841e50001110a086110301d10018001c07080500d034820840451801c042c11500c29521110f4000f40301102003482c0c1d1342c0303001e5544030f412510030009400c104038070304016070b4110080003807008004d142c40c0e05031a902c030ba0094445c940285078170f4020407181 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 780834145 1250 780832895 780832901
    0xc090b070c170105010e190b0d0807060c030501060504060503040215070b0901060b070c061112192a080a0306090c09050102100605030c150c15070f0504081b060903060406050a0b0301 80
    0xc1c2d0141c420b1201d151030f080780a509140b0301d0302800b5a079950340c1542008c15107402c039444640c14000c60110303464070058140340055800c014846820142790a00510916411006aa0586006151040e100d136a14070200d580300941806200203150007191100030800300c074070214852040e9100a002c51655a103040500e4050030500803c4d14070441c1c418003010388a0030360782005280f4282111080041450340754156800b0810f000900d0619680481d18181c000c81100d0032241c4041c041c5900b105903003c0851841050000200704920020b40c25540c64840d0304403101520f4401401c00605050003c00380402c0024811103016005401090891005a00c900390882e14042c024204a0032a4000c0045881c802c21100b000300c0000d01014200500800450707500c4150182c6038603c1c2c0c208440040d006d04060b0300d5210401604000074030240002250407510070741d050741640c2240c2ca904000031b489004003111030360180314800c10017050081d1030300510300030000d4080812890700440207046c00d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 780835395 1250 780834145 780834149
    0x30f03090f100225061b02030d0f050d060b030f011232010212010305070806090316030e0d0b01030618020114070602070f0c030b22060c090b070c17010501 68
    0x1c0301e14201115030440c1400e003140d800d546540c0c410b41d4040512090b004210802140e4200c160100100050011540080201d010849401c14250040d40d20354002036a48504440203c20492072221401c030300c0c0d0003981560000c803c82c4405000710b40e22502c90076895001220a0342c1d4603803503000002510400180144006a00590f20308500c555082c035003c00450409143c141c241f400d180c400c40040400e101a10b1100d0750004074041c15407450601910744146a0810250382e008901403042401c000011540e411a1f0b03407000c0d1405402c01d0500303440d0741882004454220f00307404e03206401c00240a040a050324400c3e602081810300440c807681c4840c111150003400b10305240d00303046031461040b014017840e42c030614001d45080480d6455084001c0c04080440c0c030450030010a00c100007103104441d50151841094000c1c010b4084045c40c0492100c3c0c1c0040d00b2240d0710780382400d5244c81240100b010b049005115640c811543c90308420741d070401d110f562a09645801880b403e00018010320b41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 780836645 1250 780835395 780835399
    0xc060a0b01051602131a040509011e09080706020a03021e1801080a02040b0a020607020c01021603080306151c1401050d1b0e240102010903050f07060e030315030f0309 73
    0x41400c100c0405001c3c940da5482c030603603224115410841031080540200c601140b13580c0f409401c260000010300003503d00141811300c2c5039060480c07902d0100082403004e01000c0c0729400224003031006040817100343c0b18506015251900006400060a4050300102175041c0f880041c448401101030980c8100c0c010501810b10030b1401d10090032032036224201c440e42000209400500d0305a8513044070f52181d1000c9e9030580903030014010003c00c0303a010301407062100c50a00281c2184c02e481c03a50b4000a0030a0300000344640c0000c40450700c603840d40c608843d4100d41030004030f0f90707400e0b04c848109006001e0303128000d121410a03c507108010504101ca07412604044c0c1688542a8140c1c0d07803201c4400100c544201510340c82000290b1950394000c80fa00803000440c4000300400c0d0070100c4000d00d8859030446066a040c0001d46d00000d910a046a030811080040151104414907040016103100c07040c8240c02e03c004014424800da59400c0741070319030380440840b03c1c20034503071340f04544134090785402e00d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 780837895 1250 780836645 780836647
    0xf0c08090f1e0f011a031b06190e03010609063f0314040603060611011802060307030b030f0d0807020f030313030e090a05040219030b131a0403050c060a0b0105 70
    0x414100b40c4401c4821103203030082540c0c201c400d0305a515003169070007100315a64004152940607182418480c01c40c150400b1640c103081d00b000c20020820a22458038003882010700c0c88002610301348518000400c4c0c4000400074040b40381c0d101d541740d000d06070b507004002403030711030032a641d900c4c6890072440c1021440305112003980d50019844080c806500040640c01e010170392001d10504010b54000700050070701d43d100050f2450900e00020440035071510f4158150385015500c04100346910b0030024016412600c42e9901d44c1c96082c224084c0044070007007501407040001ca2194a43c02007600d900000306543c03009141d56402c0000c9903500a2590302d05640e03041040032640a0014220a146050203804d11240c1c000c1b019000c40c1c8080c000310b6503125095a01c50a100031072400030040d80f180d0ba002030041081321b0858692100c02400940103696804009840404224003500d400d4a403007001c10840c0707083d262504000d80b0940c000700019440d03000e10000158000240d1003440980001a0746003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 780839145 1250 780837895 780837913
    0x150604150e070c0b0c0309060601110c0907050c0327190e060103090812061806060414031e060f01060206010b0415111b031002040608040b04060b040f0c08090f 70
    0x5074400030350240004040048460514000c104a074a070f0314041c0b650000800e0350703490f24211950801c02d018040307604101e244003011140b001c0006051240d14011144017800c0e440f0305500352060720030741c40d0807040d60201007038800301450100d0402440c0c50903004c0d01e545003c0c202040103000313844403240450540134508c0138822060894466940282e040c10300088040007510b4000c1e254000155105032181e0080401141c0e0a04032004516004002258249400c0610000341e443c050350050300300e607400b961410000da5238104541247e4010740303034030094200602c200c01c5841b10713012034585d000c0303103003c0c0d00004440d4800608281260720798401141421b040107001000c0c41e045006400401c1040c170f850820107402440400c15401446090380308042480050500342440c1d0040148102d2050204204e025000180540d1142c0d01402c0800307a81e41c0d5180c407900800044031071540103490f144a1203460070840d03102103241c8a4688800f0865681c40006960fa400a40103c503000c3e0850f01c80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 780840395 1250 780839145 780839159
    0x11214160201090206040e06010e01030e06130503070f2d0b0c0c0102071b090c11061605071e022d060903010e0609160e07140d1d15060415 61
    0x2656114140c510000c6010103160300010b4054016410030349a290381001481855030701f00c00484a103443c2824240100c42080a1054403000c00030302140c41418020040c408100040c801c84160ba40e10901c0e41842c481207040507813900c03a1541005400c41202040c0c80c1c0e5031400c0400354070a0507400039510f10b640e503401c114003001d9000161480702540d020701c61740c00005c8107100d42008504141080080203484d055280702524204c1c56000107204440305060003400d40800c035180d002e52400e9480f0540440000100c03200e1140c003101070885131550040200940c60001034445050003160000b12500719031801c0c50200d050b050196011901c0d200b442565410481c0190006610080000951200e002c51701420118101d401070000e07003092048043b00741071202070001401c0858010a000c0c60403100290080c40702100c114443c0602003018a505450b64111080c010300d5400396806da0680014000d0703491815122003008007502c0310000701e070b84c1005d00c03442d5025240003034417145c2a032400107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 780841645 1250 780840395 780840421
    0x80c0105070602040e04060b0913032f030408030406020d0809100b0307050409060504020918150405010f0c02030904061e0b090a030203030c15090a030c081810020c011214 75
    0x2900700c0d0010f8091000140c40818120202e20a900820000c1b98204d03000c405c0264070039000b85450a105030481c680303808030758052084210484040d05980e00c5020001d00c2d00801b1084044101ca81e1000003030100b801070010010304211541070b0202d03200003020180565405004982c0c1d684160701103051420900095005800038001c0078081e5686036403110041429115000002d491040c0c81d003090008500701285510344c04402441413005811240d41a141c55007a179490182500c2d5450b400f017801e2000a500800030148891070170041d5102040b00a516034101400301c03403080b40f6210000503500c40c01c2c440955405240046c80d245541401c052484a41110000941081c0084c0b40880161810002494490301c01d000500100b5003000a00c80265001031040c4c000380c201e2040540000d400401c18061540e010040350340314151044c0240702c26210818165212405024920134160003280e83c03210444280d071901c2000d0308071900c80050b104c5080c00b2028002c402000204000520380d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 780842895 1250 780841645 780841657
    0x605030a020739080c010203041517070e1008011a0f040e0c07120c0b0c0307020a020307170c0f0d03050702220606030b090f07180504090c061107080c0105 68
    0x94611020034000e00c100448080c000038a4802e840f5101014802c1200107041c0c6400804840000f0900c4c41300c8400002d440f8003032842580524550b82d00c607035200c24060b120b203d140ea28514842c1e0028580002c0040904c603014400f940640b10001040c6c0031144120410b0b4140c1d50245c0341c05030400a500740540c0140c2c040300d486d1048100c00c2c80302241200c10400001e00800801210341e407a01c2c15410500014404240140705001d0001d10300070004e1125168039504c0000740d40c2140e10782d5514601a424010800d800a41c580150340010804050308404803049c0d0540b4400c6842035440760f0700380f0808001c4010201d50000c20568408000b903c250000c100840c4060221030121141200120a0084585105212a45940090000640c50712444018100c102c4002c0342c14107041011401260f000350101042200d41c0301114800003140c6d010b0001000081d20812200700b581c140590095004e008000c001a01420708810190000030703a0000d440404c0058903400d00c84a0054845510003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 780844145 1250 780842895 780842903
    0x1a060703090e1b0408010603030e0306280b0306090a11030c060306060d060f0f051003020301140f06040b0c0102030a11030705120712230f13021c0b010807060f02070605030a0207 78
    0xf072007000c80900e8090016000419080d070010030000e0031480c010380220b81c1c10450a02940c00a000c000720314100a80c81d6000c40078150000307079149440080309000c1c1100354042c0e82c1500c04d501c244600c8131700005a2000041c0190400d10069000da010551101450604075a00600600104d000f900e400002807510807401040010074075130710403100713460040d50b0380202c1c5071402040040100f814820094a401003282c5003c41c0703035604200e400290007100c800024050804030305801040e0300d0b0401140c0c0613040f000e108a0b2038000810016000c0d601c01c490740d039859810030035030202c1d02c05000141c9001d0203241d101c20341484402507414000c014018280300402c18000b0350542c07482c583d03110b01603680b0882c0e0507900b40404c140039400482c9001400850540100f081008080407160100052195040303440d207101a5101043c03520391500c1080180c00c00541c03000001e51003500180c46c02c02c61301c0c280c0311a03810104901c0e050340c8890103031042c90702240b020000100742c449258000c00140b482 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 780845395 1250 780844145 780844171
    0x2205060a090e2e090c090e0a02090d06050c04090b0307061421010303110c0d0c05150f030f16050906030103032708031c182303030403031a060703090e 66
    0x3070395120032840030340ca03850000705400318410b00130100300c3c0c001c0c04060556400c1407003031075180c811950540000240454074142d40415404800d54031100303210b500300d400aa01348018200541020601e600c14824400214906800c0003110700700481c828044880586840c035044400a4003141c1e1a0b00102001f1581c0012010401510054000303003070107180240e0303a071110725001202c880e02e40070000304080e2141c2d65040b010b8001452582142064810540d000c180322100747c030701d01d00a4041c00750911030000d03000c41044036104100440c1c1d1300c035203a4905c2d100d03084600a023003501c0c00c2c0f242d0f031555130b00003100704010b2020901581010a00301c0800700300074040044142c02502c6215142c01400050b00009000d8400d864184c01030f081c00e1202c103100300302500f55400c0b030100e40203800e0f80c002c00444e60181c05024032854030301044041807a1100ba03a40e685010b01d402801007244170300500760520000218240f40c10300d01d050b82d403125816202c40c41001d05184e110038403800010003684007098 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 780846645 1250 780845395 780845431
    0x1a0607060203101a0d0f0b031e191505011505030604090827030d21150803070602030912091c02030c0a0306050103020f0d1e06060b2205060a090e 64
    0xc030388072555070070381c80300b40d590b41c1790804442da250a403103807020207a10360b43c107000c03031a40720303640210341150120b010140c090703200c0c2c3c07030300d08510300b070a00d2014080c2011801c02480d50500c0883c0c184000c0c01405140100140e03a04c2d21085400341c440d1040041c0061801c6c030000d082400c150348210301ca0b81c00380110030700b400c08032200c0b903180902c8020740080c3da148040800046040400135007480d81d4040c1000c0340d0081c40d440c0d801e074032020b8241460790466100d040c040d680c050080402c0e40941418010382e031b0b440e0b8182c10090041d41c000e98986c04148a01d02d008500d124100040e181c0c4050020f1500c0e20f42041c280651250003400c01d0203a0785409036a0400e5116a5120000c1004600c0ba05012070150f02d50300400c400c0d914440c240c1030140c5240101540002d050001d1070b00c04400103940c1d0101c91310181410740051400741c100071480b45d0006940c4c46014480f07070360302c0c1648810100d84602280c80360203210060260390540404660184424403060040080e040c0d4001c0428900c105018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 780847895 1250 780846645 780846659
    0x34060536100c0212011a0d06060b0c0f07060201060b040e09012711030d1e02491b030507080a050a11060105010e09060d0b191a060706020310 62
    0x1141c403448407070108410307032044800c50814040c0e000e100c40801008010103845505070356450080e028505204900050700380e0100900707984801d015000e014015619542110291555192101981078092240b4040017443c01d105004403400d8412002903a424140f404400204086000e44140c51075520780ba440d40f24152485102300071140c24150360325001400d400c0004121191000c19402500079a1844010076004400c100b14450100309240415203900030490500c002d80141d0380d4502000118291500045201c15001005180b540710059407403500a0340c2c2d2910500400011803440c100034050310307101941750390380907000307003082440d00758550366502c1261320140038200442c81c00700301d801c1349991006440216076010801010300794180340c000390420344200402031040344d0100020310303103072940c03020301c6801ca600c0441c45406050103000800b40460380d1426541c0146401c1080402e9248541c403900c041d8009031800740380c003e094132120080d510040007a0500700e1406000a560 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 780849145 1250 780847895 780847909
    0xd02150d0e0c010323010506130e0a0c030b0d0218060f1201021210080a02041d060901090326010905180d02060a0f020403050c090934060536 62
    0x4145440180c0351602194002600b2600992081e080e81040050050785c0300550380c040605454045078599155030741c111000ba0b0b1010340741c000e80207050141c000d00c81039810759049901203900c82d403010b21441400c2d02c140700300000c24110103540b185070060400c0241000340c1c0ca00343c000001511404028083e800030a81c41841c408100c420f0384e5000520b02c140704a00d00c541a084051503641440c02d5107051001a582e900c11080648078654038443c1300d072440000001c8040c50039031380e81590031600c0c00503140342c024445e1100c01d90114840d011904018240001200e07401c0d01e5001400b149a4244141c5400a080007400003491410340c80110710359940810541041c2d082030b50043c5403d19001c00c0702c2c0d055a5440c449009401c0c0188000c6c000038101044424009200f500e070304109a5960392014036280307442449030345110700802c0105ca901107880319140320078104019025600e6460008560621842550340c2c0c100d03460005035503200072034a00700440d80110b444d0851100158000180c1e0f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 780850395 1250 780849145 780849161
    0x50910151d1b030108030d0b010203070f21020610061b0b1f050303090d120c0204060b07170c070621020f030915090c01030f021603020d020610050d02150d 68
    0x34030601d08000818100c069001c0b0a144249036031801c41d45040000c55403070244951214225444019110080e4420020303590354541050042c4011a100e0409020000700f91902400320a0310400300b1032450f00002c0c0c42801030b0350a180410403e4a0003504540c0b4040d41f0f002204144e080c0380c911804140c854802d0340c0074280a03004540c0d00500803090304042540c2e0340c4060b019810501109501d0380c0c81001041d101d03600321101042091018000301c1c0c00b82035640000354003034030780040890100e0000340a4400c4a104004c0d0380420803a03483c001446000c0d9181380b08503a0b11840e414041c00e80b103100a510074508210300000200c1100c2c100384141c0c2c10080300c103151301c507003c03040094011040040070f914004c10f0041a003030b4203107090399a8a41e120700381c2c1181030540300c89000000e1051030341103c6c05a119680c2c2c4d81c4560300d5a01d4000e403685036900c813010042c802c10010409803800031a141c1d0440300010000c0e50040c0080e801d00c8610805150710044489081c04591842500c501903014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 780851645 1250 780850395 780850439
    0x90309150e0102072405090103090c060206090d03020702030309041d06010608061518040e0a0b130c15020a030305040201050c06040b061219350d05070305091015 71
    0x8a1031501e14002450b040031503002c10300f1964180300c0210320b0010f604200310300030300c2440c0495803032681c00010f03005400020b10007403030901c00480c0001c5855011841c24018034121095503103a40c00304408805a0054500103913042c5c00c05c111064a07031401c1c1e44403802c0c6094405480003c070302824202c0382404001d03800703000420800c8040000f0361500e040d010201282e8100c100b414004020b01c0601c03480001400107010f59690345031810315000420000701c03441d80c4050b181c400da151201403030b00000c9240c84211008140980b011504100584001c078406603181d00070728903074003640c0b421070180c08050010307410310004001c10200340100740611441140141c10300b10b840d04144003403000c0c05120000300300380c42e0000700309051003c40d000c0101c0f41131504401500d1011034a0048200c19010340ca982c5a058001d583c41c40d50603142d04406004a1111140108059560010150305542003190203000350b8101d02c13004050404d05034028081c003000c8500c403074041e90725036402c551102034a909840c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 780852895 1250 780851645 780851657
    0x12031817060a0516031d010e16120b0a02030c1903140a0204050d0b0604020f041e0f0513180804060302070c12080f0a020c0402030a020c10091509030915 67
    0xd030114400308403854001041c00e8003040180f0340100e0002e00d0f6440d44000300101502d038880194813440070301d610304e14020351310000c01081d1001406141e50703445000038140c21410000300003400e0000484491b118a8101d83c00408541c2c5040454000f50300c010284001c810040c000001074828450300c1e40c140074410b480028268209000d00101c0e00c00c01030000d05124010031060000b9255a0900d881c590340c00052400d03281c0300e110000c2c000e0700844408800a260100e00000d029400d8000b0780d519142c0e424000380c07055141d212440010407503024181c0c000c0d080380300e03000001045a1244400c84103003420820138541e280d42c1d1001742d0b802030380807900194002c2100e00a0003074440b07214006004040b440c80e00010242d40f4514a80144000120b5001d4042148401c0340c0c001c1c0a8449c1d1100002c1086580e468400c1c0c041e0020b400c41c500c0248244280f0041850307081c0e81c0e1007120413054001c072041c0c3c0b400021390303d01c00280044203411000c001030305500080300100d1940e0503c1010868443c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 780854145 1250 780852895 780852929
    0x9080a0801060e041b1103090301050a0501030c08060c030c0f130306021c022a0f060106020706030509010203090a020613050603040f050f190f020a26010e0313120318 73
    0x1072143c94a240082e01c6035290008030b9244c01c280c040340000401d85030901d09036121b450503825040d401005041131b015402c00c4100049032156500ca14103891040341040101c03611140d001d50740c0c83d8202e6649518590400c00301e01403004101c080c0c4520f1480c1d5020700e01d0104503a200d08415550b60b80110392355600458210045445007030300c201c41030b015401c11070911801200c2001b8200285481107120905a0042100701001f80042220207010004451442d603686400955410702d9200d103000003407400001c204889410b0003200e00030f900c1d0000401c1c08804907001c1040d05d03404600e40a640d403007054070004141e2a00c20166200c1c50040342d0801140c3c3c0316050450911400c15081130054102d0480401189400d4000c20f500d5a042445a01203000500c041150448070b0b03000700000e282c00080300b480350390307a401c1100b10303012140000380090140c03003400c1580c0b4002c4484c035400b80092004140425141214540300081c0a407400591040209103410001071040d0000858403c4001c45 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 780855395 1250 780854145 780854147
    0x1d04020d0b0307120f0b1003050a211704020906041e0f06140a030f0804090203040b060315060f040f110313060c0903020105091903060e151e01031509080a080106 71
    0x1003c0000c08802c004c420014083c4d42d036591105140340700007801e1050050100c0c001030320410a000155a104040303030340303052482c208411200707030041151201e2412144441d454510034458101012031440341454562a15420000900c000822403a0416944c802020306040c0c01c0411865641103a44002402c0c203140900c1c000b940c0ca250842d5404000c940e170381c6041034941c1041b01003103a803c000c01c03003021825480e00c0181c0b4030850b40907265850000c0240801c0c04020349016014810403030441d040b8001003404001512401c07030b030b060341c050492103000f24941066041450707071400701207001a081e02c0c1c000d00003406810503610580c001707880f4040b807410005148200c84001006042850074682b55500007402485030402c00c5000c3c0c8031065102c5036122040341d041c406143d0020043c003000c1c204011040d80c0b078070714030040390a441c001c01c08625551040000c003d4000600042d10403103a00310b841d4500308101c1c83c034990300595a40c90a10703000c1079100014001e2141c1564400c5029407401034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 780856645 1250 780855395 780855403
    0x3060112050f0d080f150301050709090e01050c0301050d060b0409030f170f010909030e0a06080603120f160515070306090c020d1d0102070b0309010203090601080d08071d04020d0b03 80
    0xb0142c40c6a4448405401c0700c5400002d56540016845032690690f40c442d03038500400d24008560303d030551f08200074007180d01c0d00240ca800540d18004010021341c034141900c0c6003611030a840400b401002040140491700b844038000d020503015070800f091415841022038200c0c0d01c001c5068001400c140060015141d00240925481c030719030702d0111042c181401c0041c14024123200741c2c1c150658500d0076000309401180804c840c44001003074042c49640d50800070709201403c4070064440c4c080c0d44143c420805440040c1c906d0050328041003800d104800e0410905641141400e072168403c03c16030002da610120300a5110765081d40c0c0c08240146401e083c101612401c054500954104100510100b139004014000359a81c44507440f0b903810310000140e040004035002911308481c0001080000101500294021000d030001c60380c183c1c0e80c03040d01075280c0070414142d4001842000105422911401d003000c989040d0b10044003c1040b03d038000f408a80c40a49001c1400b0703111030780c1000901d4240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 780857895 1250 780856645 780856663
    0x90d060603030e01050717130e070c15020c030d09060b09070c0618120311040504020c0a051b01201e0f0706020c06040e130228092307020c0306011205 66
    0xc05d000c0d0505c1a1996025000d420018009079810b00114009025003c8018500c005080e202034112980c10104d00040c0542e110300c509442483c1c00004801c0400580d1003150000300d4814080d500300a40300408101604584005840042e116003441c106030f551850b0242c001d41c49030711040344940951906c04242c40c41800300b1070a400c00c006009000c50080c6080e6010308815180c001804400300040340c000c1e0103141c10483d0060320100c1c0199070104005080002140034004503000100c0c05004450102d260703828903400a96108024503611740b214500550641c003800c160380e0707900510700401d0015039154011511550100180391004481031003988090302151014140c40d45a0f00302107030191099102d80c840310101c1d90002003402c40d90700095000e031079004180302e441c81c400e2081c1c408054402d119540806050210010300d10041e841652281220717014601d103905101c0201030002c42d00201680e0650090043d0300120f55020700c400303406030840c140c503d54124800d003042480d080803a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 780859145 1250 780857895 780857897
    0xc0d11070b0f07020415080a06051825180b1207060203030c0d1d1609090c2c010314190c0e100b1c231b090d060603030e01 54
    0x5080074445011040110b803214800d0085a40e920101440400e00801c0758503124a0404005240400c4000010820400306801070005002c19184e02a0448136800300f121803040320741c030000c0d500d04815030080300b080800618086001c1001d6945002d0095404912889030009a90f844020001e1030700003910520a40e0040007810003a0400e138000c0e50744d11004d040c503d03d8030000b00b03d1050001d420f800c00812008031640081e111b4007018400750703690f1550701800714000e05080c000708401ea1140700c0e00344201e4000c0b20b00c51029107403072000d03024440c0c20149018170300d1204010460841701d02c8100c50085d03105200d9504028400403919082907001070441c04c0445004a0300c3c00800d44110100c002c0d00c0303401400419079140d41100c1107100d1059440312802d8031b00411030725043c51050501484840702840305100350800d5008502d41210023180403c6a03034a99030200e40d2000200703c0f21042c000d09104080d10384480c21000a00a12005030215811a1110014820141d100041e5100d01c403003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 780860395 1250 780859145 780859153
    0x406060804050c12100f02070303060e1009020a03140403020d110c06090906041b0e0a060c3912020f01090308030103170904020a031b0f0210020c0709020c0d11 70
    0x206542d41030310364501215091160f80c83c52180c1103011014000710040b03c0c074600c3e08110360400480e0110183d0040b401c203401191500c100080e0038958107211903c90b01031005d00b45425811700000748020740020b803503402050368840c3c80902040101c00e00500441c002c1e001000180384284008026400e00c920070029a0400c550ba5000364440d241030380c4a1680468003140345540e00e1021500806214000183c0340550b005070510f40c54008020b50b802100556120107403640700c00e003e0780c03242a40c00c0c1c02018160080954400300e4061400c50001d1905407a502081021000e500b58a00000e034110707007240780c60030321000114540004908082e45083c01c001f43c00e145036403540802c03030005110140054844000784060459290122607160400800c1191101c2000800030000e00e02e510026904488c0301c4110440d02c0c2c01040b2418401506a008160000b0010800400f07504410000340301441507200214600903a4009003450804240c0100402031000c1001081002c00310382c00549504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 780861645 1250 780860395 780860401
    0xb10140715063213020d0b0d2303030f04030f0c0c0b04090608072103170a0504051905100b010c06061403061b0a08070507140c180610231804060608 65
    0x22010245400400307001300050301c402e002c5107070070042e104c811091a48104204900410040801c210765981195030261602c0c980125004039524030003640c00032100450000024002841090000000502440e1a410301100c036a1a062300450981242c000701c0380108080c000034181e03114040060040310001c040f850320740340010460800d40040e40348003a094a58000501d401081051501d580c40612458680b40c8000480000d0005480442d45806450704401d904440054040d1f012504000a03143d40c121050100005019a103030081c10300030400c0300000440c200e48103031f40080088648403841c050100301014140a002028039404001c80a0940840544502942c0002105040410701074860030802d40c0c40d07010340e0034024030010300b208c1040d08285000c50f02080d1100c080e219035000e2040941c9451f852141101c0e40c41c0c201c1641c0300314a4441c2e208404e907010070702c164080c49800d0b4203807054611082c1d00010b1408042d007404110702d00c0b181071034415240205a40d1602515600b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 780862895 1250 780861645 780861649
    0x30702191203020a090b040308092d10030b04090b060a050907080a0c270503060a0207020303070b06010311070605091e0c19080307060902040b101407150632 69
    0xd540281d8408040c0c0c00300d1005440e03400b461101001d003042459085e11182d8034640b0400c0c552007554103a0280c0044050102d011aa0f07105c014141a95000070754081c105070024050300ea4400e03500002015100d0348800d03c0d42d100c1d4403034410210300900c2c00c10f041d0300c0d01506000f842c1076140e102c0340c00303000c0e11402c0264165011b01c0c0e00c0c0e00320444140c0890745880c4444200c0305414041081c070442a0b00b2100d56601da000030041904490381038080d500c80b0396030001c00000720f0040400182d0503070003c120840c0082c100214150744004141800070b5058800850720150741c05c41da0080b51801d550b04107114a040f01000100e00e000b01501422980d010b28585090300c50340794107402c1d40940000d00200c03a10074004140080500610030403203480322a5410001c1c040c04420400703901840c5030080d805514103222090b0030f0703886407a44803c1c010890204056200b40c0c407040040e6100c0d514040102002c100c0c2e40156002480c44040846a61503001c180c079051034820544010740c2c1e526810700b00459 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 780864145 1250 780862895 780862913
    0x5032b14041e06060f0902030a0507080907090b150f030403030b1c021e22060807030c0501120902040c0309051603121b0506092d07050904060207060507030203070219 73
    0x1400040020a0b81d91054070f0810041c1c03450303070030003198807004260100b4003501a0303020710300c96007580d5014030041d160b80c502514100c2040d07030404c05941001905101184c815009142001c1d00030b000501081d907582c41c0d6070155000118040d224090001c01c0c0818198140154400c000d801c455a51031041d91800248903c0380c2b01c00001c0c000c030750a805180d03115401454000718440040c2164403000031501503100100100c04910320003a00d0080041244440007440d28281c0e54805a50b1000703504100c0103503140e60b084262030342c1c0640c96148620060301c1b40d010703140c1d41440540780801c105810313181160030001a214192241c1804103820800300f2803050012261002c04d0a005d1782e20410040c4920307407900d074000c001d05684166018440744110000d2048003045968600110b120301d000b8854800446070a401403450744100341c18043c0340340107032040b5002482080010b03c0c01907295201003e0703590450340e40c0040b990120400445580512100c000360400001100c400b0700255551610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 780865395 1250 780864145 780864173
    0x40906060f18090507031b0203130b09210a05010207050604061a13110904060806090c0a1d0a060315051b1317010b0a03080c0714060a0c05032b1404 65
    0x43d1504d440120300c105010344d00c0a0550a03d03407010440d2211040406980c0b40d1082086d4102c000b140c600c00500da035041829180540001040e11410000b800b10b50b840148682440180500448503480b0006a0902c001c02c03907a0b00c40d50141c0218601410000c0856480c110780506000001e00b050707081d951590034402c0c5c45018800002110741c103500d00c4150b54020b542c0419002840e009001ca20785000142e40351003004000102c0d08401250424408212040d01c180303007440200407088510303031a9000403d64414402c0000240c0c283e501c1e21200c900d14003c0120304907041d610000d0000c408940001003840390795511103285003078201c403440c41d44006103100307081e030380d0f0b005036240d4540c06c1d8290428100100f0062140d03407115102d0034141d803594003986084049120310440064900e2040f40701c070040c010020901818004100800d41e89075810280881da02d000c20003a2498444420045080d00724903007001541d4610b02810302d908481c07580301e00e000441c3e5440100b000240e80c9070cc055038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 780866645 1250 780865395 780865409
    0xa17191401080307150617100f090b0106081b030414060108010e0a0f060603060c020714010905090f090f0102040603020d2003010303231204050c090f0604091106040906060f18 77
    0x19045c001031034002c00400064007c0b503540340c103020040c00b000c140055103101c010307200842040001c0385d40950360111260f000c001030141000c5e50040000b540144080340c1d10080801d40d9036a14486642100d199034070880b0300700e44030000303c940d403c00740b942004020f01515040c8000c109070a40c1c1202c150769a04c201000400c81c3d800310403240f00300200d91300f00d64000c6510100501550f000d030103029482d80b142d40107445d191620507411000d690700c03030004035003107500162240c078082c0c54810804030040d8008024403402d1248850586507610244020402018103a0380141c803100404c0906046c0c800c01d542c8038040c40c108007100030f22860000120f90440f60701d42001810403030340810a2503105607260b66005030200125007200341c481500c05a510541c804d4041d80c0c00305d40a082000340c0e90304241c41c10b1591194044c0004c0c8a41010350002c1b4a036800346442a452100c005c000410980c09600a103000301d07283c0104100183c1c0050202c0c14030000c6041a032030581741900555908041403007115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 780867895 1250 780866645 780866663
    0x17150a0b010507021003091e020d03080a090f0606210812040c08060c1e03090a032006011203081006050a05090d1b0e060d08030402060a17191401080307 67
    0x4215a000b0070480f481c1d154050f01c50101c0d41182c12002d0000d04882d82c1c00ea07000e17403d1841410041c50880c8004416a40c000c3c240803880025490455001c4001005402184e540c2d61100001c5004141c4203560544541004134500d4200412412560010b51000d15259030079a200800a0780d624162a1081d0b08880d001030b40750f03180d040c043c008000c0e503403012843c0d01841050083d40300d1448002c03c4200c04003c24074006100c2096401d195100840f45078250360481d03122000040d100700e000700041d0f55041d003c90369110b0120221b90a04200b80d1095103100c120700384100425800c02e03074155100216045450002c0c7c9082c10142007449407210440400100081340301003540c0741d910020889411031011740c2c42442e1404a44810481c83c000c211840b083d000c006003003441c0000081d04c5d1503a1080406085840e0b039801d00c9580c1d04442c10900078050200904035041c0c81040441c1d106d2216201d19849490000313245c0c0003210050048240500b03800b500500c9003003000012505099405031540c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 780869145 1250 780867895 780867911
    0x20d02040212040210450306150501050a0e041a120c041404021806180a0519110904090c0b19090f030b0105090a0e030c01020a080609061c0f0203030d0617150a 70
    0x41c12482201d100c1030141b1010038000b00034016917500142008452682211174541c99400641e628051205d8040014114402c000c0030b600f402d400812000009414422010407410006107100d20814240300c1d03d6070000d05c003031080d860507008004491450b003509900034286500881d034100912208444000000d8000c185c0d00e8551540307541c0380c081c1c0351101e03040798180507140d4406840e042d640000d58400c0d00741c80681b81c1905e48103260000d140e0301801c61400c5545410311004d0f240ac1d22081d00d842c81c8000740040d9101c210802131800240c0c80d05c903d4455600310601078240711481d001002d551080290500000b500c6405071815200304032100c3d5041d5444000c41c43c05002410301c541010300003c11180a0001d054001c0c140390a03e507155000c241c0e444c0030501450800480741c155010754070060140254a0b0841460441c50245030301e56440e1500d074002c20710b0b41e4841f8880364559642c3d418100041082002d8450841910034081c05505e00c2050004030201d00150030f861071241c0e2242a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 780870395 1250 780869145 780869237
    0xb190b03131208010303020616270f0308120a0c0909020c160b0306130506091b0f0a0504090b040c02060403032408010626030f07020d02040212040210 66
    0x880e00d00e90b40e100e40c1003648101880c800a20400d0288811030151007040045010a6104480402603100b10783c1e4001020026000704400174096004242d03943c00707c0c00c40451030b01103080d404000b86000382c51059a4102510100c0300c5010010f101c0a180342c03400255220302d580c0103484a0480340b59020250300c84200a40950401810b00c41c0308240741000701000549a9002024611514040714644402c0030105030130740560300100c41c07803a44019401b00150409100804045800309400301c12400c06030391070044400c07580080440004100041404c0282541d240500594010192402d000c001c41240000c3d5035518040d0000381419116444c107102c0261040100069162001c881c12280e0b94500d041802846580101100b00030058030107d5048000140002c1181070100210310705205040700d200f45030820b000807640498201840b00241e07995001504000c4c81030640e18047d401e16104006070998110942010301503040c91984c4000034802d4a803070350100308070a10140800e4016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 780871645 1250 780870395 780870421
    0x1701021803070812090a120c080d05130b0708040e010801061406181302210402040b031903120209090c18010906091a1605030d060e010b0f0c010f110901030b190b03 72
    0x84115507000800090080c050f16180800c03c442074401034802cad90f01c2c9034804407058402d9a0444c40d181451081c1005503200c103c00500d541760140b47c020b82803036181d01c0b0030300c4040402e0f880045070b6911171405100811b0048010094000229102483c185080c4c4044640c502c000312158800e034444034404c00c0200302d540440d0000f8602c03540c0c001d000c03036000803403600c003003c00d94041c0d0040e03103003248011090800140c03810041c074100407003000102d6955811159000080c0b03140c1021a02801050340c99120000e1440c040d10394000322a490785480d060000300e40d01d1044c2640e0400242070010840c60341c005050300160703401e03400d048000c0314459140321418030420f03060038101000303010031105008020020380964881060f0030302000d0381c2c8542c403020f003a00a004d88000900c0c10019480001e01c45030041c00d40039501000850842446a01034089881101001113407042c0000c4149440da4544164801582d04440d000c50006012100d281e0b0154540035503500b805000010464080d24a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 780872895 1250 780871645 780871649
    0xc040e072408060d0201021f09061a0901121506060e100905060306011202040b0a05130b03010305060f07110f0318041a122b030f020c0604060507091701021803070812090a 75
    0x58140d030503020055050401400c00f00001c5d198145061400d0078bc00c20440100d60040000411042059003016440040c860850000f124221460400305585c030700e903801828000c0c0303419244d00340b03507202010070f100c102c16002504400300842100180403d64400c03041c1ca80200302844c3c0903140341d80c807040e800003d1007680c101450442c4045190302608ac0d000d001820304517010490303015015507403001403100340002c0c0002803d0360480c41c00a0881c00c03072035101c0c1740c1c44152464510440d0340700c20071441c20b002d80ba031a0149540c000199001040c0c43d40000c504101c0800d440800039681000c0b0301c095820340081d0420b104040b03000150095205c1000700c074507182a100d11070101017120146071003000c0314685a140c042424a6170a0b01080e80d039100f59681d24041001605444e81c030f96403a00c0040000508078006d0000081c004900301002c50805c44001c00cbc032000042ea2030406000b01d401b130f14070600105d846544030700030500000d1008218030b50400b1034140450b440b15010800605541c040d0703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 780874145 1250 780872895 780872923
    0x90b030601090f14150a0207030206160209070804060e0c01051e1902070e060f010e120f1911122107080706092003120c0c040e072408060d020102 64
    0x60400450303416030a05588500400c03c4645ca03803d40880c00f5112014014040c1d40c0000d078011000820150520324000c1502201400b105401202a0f50004148401c150341950000701da100801007008081c2c403902d404d03044184018407180f001100000c041d445176080521b032a5a6224020f0a5030111009030749040c424003c06c140201c1d1501030007035807203499200d0814805502c0700452035506050342001100c04069490550041e4400240004044c050050340d500d0310511a0708080300b5000e200c0c12084c8100480070944100c22820b1040328850b10184042c402c81c80052012200040040d441104485000e80b400706051021120301c107034080c0540203080720f0000a241010801c0c161b200542c16032180c00041800c0105032010a511042e446400350160300248074011050b601001810a183c950b00490b0104803040d004a010b07103120b001c01e41541d62080c80d091008002034600c0b4080d281a0362001540d0400b105401040d210024001b0790103594500e0502003564800d0141c014070f00e040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 780875395 1250 780874145 780874169
    0xa1506080f0f0d083c130b06031203190908030a0603051510050d1b0308090a0801020a0e010e0f150a0f0e090109050613060b0d050c0a090b03060109 65
    0x8011006074a0701100c0c84902c01c1802034040808059009803040c5000e601100082c800e28410000704907545d400132031410704210004090140c80c5d5810640d151b20071881d40c02c2003003c24641e440c0c40d500d410f00180081780301c3d400000b052a8404e884c881503983c4100500940300541a0566807038004181a80010780407420001c100001c40050f41c01c1001203030720410468160190007132503264101029240c074000584d28400401c00c9140c4030b201c034015240100582c054042d10021005020706c00d07030f4022501418003041540c540d02d0702c04078020040030010300a5180043c5a8002800c2500200b125030502040d8040300307000d5100e11129003d5118080c1210701c02a0320b0748040c01054001407441400110704982c031640051040383c0c0c8208400c009000c00b00700f039080000c0300028010040089030020901f103590382503202c8600454000f01100441d1541d9040010340e00c8090341c10040050000388020840c140c0120b80c490003800c200c4000908294a903124500100c0d89010b2540c86210600e0b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 780876645 1250 780875395 780875413
    0x40908070b0c1b0d081f0905011401020f060f191410030606050a1805070216030c06080c0301050303070308090c060c150601032c12030108010510080f0a150608 70
    0x2c54001041140c1d107403812074030950b41c0d0000c030940d079442404070080003a4003200031038000c4003000925451141c2e40c1039480c2c03030152101007074012030305c0c240d2100620740d88102140d045540c05000c0d00e96544a1302c40681078902d00380d50085901c030005032030000020302a01202440300c0d9154000b80c00c038104d00c110089039082200030004008501d02040d90386614020001860345003210002c0101d500e515a0200d845500d201c14000806008080405501603c210000c21101c03084181d4051817241c00032500880c2490700c010420301000f44140b14419041005100d241d41c000140c0d0020ba505242040c0b0b40d86d20800711504020700e041d00140c01001c00700d40402d55130004106102961600300040d01c4035580c4400460603654840100000d11170f86440819149c04512019074204e03204100f00d40403611b2100c3c40300015402680540c07203503555603080c02854400c001c2880d00508482d80184a0711003d5000c0540391700c0703141e81c01400e01199000d07201500100360024401000079109a1301984 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 780877895 1250 780876645 780876661
    0xe0a030f061a0d060e07030c0308180d0309050d0510050108010c08150603040b0408090a030b0f1602030f1e181011071202060c06190c05040302060702040908070b 71
    0x40914000c5079180d0070010818180c58042040100c40b050003030000100071003e40f01c400003000340191403d01d9000f40d40012000c0358059000000842c8110151076666440c0d03110341d440c3c541d05446a91040d00002507a0740801d42c080d51003016140c2c01c03a05d401007201c0900d0294903104244041d85916404d00d000060342c401c041d0300011100c00a500c91410035a00c402c848140c156803902c900d540094140089404074111400031603000380b184003903600d0f00c00b00c10006114108203a100f1210704204004206195001c0408a03030092166204031040442c00d03d0065228000c07038069102507503021030000304460764983c9410050581200c00c50365071042c20402d56124070501600c50090150310b000708020f034840c111000a2408403c0030b40f100d142400040d07007031411800402d0f41d00460030b1055540300a02070010358001e03140c41d403806403c8207039510002c0c113a502c078116801c2848001e1008101680f40c80307048409091b0b049900048592262500e0340490244d0803010b00701c481e10303c042181d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 780879145 1250 780877895 780877913
    0x3020a02030903072c040c140102070b0c01050106030b0303090307061407060612060c0831080a0c1502070c0b0a0c05070b0d0b0d020d11010207080d0816051e09010e0a03 74
    0x41c02e900281011444100740705c84400f40d40680d0010058508000c08011420407034180f105150306c14415184207561340c1600650907040b5014403030069540304010001983c061203060010603094000d1414030307140500080d12030310540704010034041b10b200d460a0a541420480d800c00741d000c00c003080b5a64481c1d101c0c10141c90100011910140fa00784050107203802207907058400c240c40e61010080009681000c464810407401c001c50780000e401c0c100c0b0000d0500800792543d0030130750740c50764020003250030f0502406500a0414041d1407040003828045080c0445413402d803406080368a61354490190100c4000050380f4019019000c0d41001060764006400140780d407110a580074042046103d080115050981c2402035100034041030410004123130018070001903e0500680e00400e5442c07000b2420003a01c00c80d808009004003003082480c031030500c90f4203500340451900303508202c0070503040d20120300c210b032600028210100d0407100c242c0c440c1851000403a00a00b2203402d06a4a01d007603980 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 780880395 1250 780879145 780879179
    0x8121f08031306110a0f02030c040614040c1e23030c03100b040b0702240d020c150114360a0e0d020c060708090301061d16050a03020a0203090307 64
    0xc2c00310000101070b440344060180c481c60010140000031001d039518002d90041c1c0b01c040360140240040c4000c0d41d40c841c86404020104070300e050036840c0740e00b020001120202120403052004a0040007030608501c544403040e082a8109210005050760b161660541400d1409603c0d0000004105c018040c10b8061806a107090020170311850b12089840d02c1c0c0d001368010680c01c00c100340300790b0002d442d004001e1016030045421a140d050a001c00b0811503501803e04440b49039000902041078420800180310f100419900316038031541001d602d02289509060041d10581509032011001e4100426004050199000b101d0701c0c003600c43c241e951480822101c245c91540352680c0486003c0000c9511014200140d0240024801d8101000155000f600050302c00f000248a100c501d80c0342446018082c00e0703003180c0741c20000711078540441c3c0e208006180801035019140b00d2810242c0000558088141c0d46c24013503205c17050560203d00d103020304050558548070301180040c82400d05410060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 780881645 1250 780880395 780880417
    0xf010c020a050f07060831080408070e2a0d021207080a0c090501030c0e030105040f062405040b3d0504050a0b0a090308070606140d08121f0803 63
    0x440d520f2202c0b121510b0f080d29220300c5011580c1c0100082243c20302050300612081c11581303180e24441402c40700a1a01d500311001c03584060005018002640c042182c60000c118142c20b0103054a030110703420000e00c2660610707454904074041d000d0300320310544060b82c0144003500c000310b40301d000c1e80c01101910f54040d030384000407a120072f0110394003031340500808400d80030640742c0c8080146030000441c000e203c0000b01008000c40b001c0340481c1c1d0340d400c0c0240390050b801548148012200303070405a003102c1d0031103000003440b84e50080001d0a04094640b850859600301c3e00000d070f031540c01001c58682203010800c540491010020440103030003040181c9068012520300d03008481074184141e03410310031030044607409131051030704001c02d020140050581c001c4c5031400740f45d082c1c0d5a5a03540010f810003107007107440d02e482c0c3d001440105140c440304074410320119102e45201000742c0f0340e88070610840590340350f190380c0302000403440401000307100d1854050700d400c101c002d546c0ea01216129004240610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 780882895 1250 780881645 780881653
    0xb0d14010b130501141f0c05030c030d020408010c02011401060e0d080f4504020d0e0a120504050d06050a0b0303180a1706131a04060204080120040b0901020f010c020a05 74
    0x605e01d030405c0b420122203201503080c0100c84000d405001d07282c180450300219002e100802080c1240d036001e101901811720000e0700540c0780c508000b405401d4544280c500003c582c5080307180700d40d0002e40001d0f94111180e034200140c51850320001300d241c0784e10440b00035294610000e560007500e03807400d0045c0b0121541c0300c001172604403816101c15075000e0040403102441a03040c481143c0c000ca0a00e1081c510000402c010318004103512000c065440320f0040c40d6031900014041e005010000c00408441c1805281145c41d00341032a0018520b080301c5200640003e649030000380340d1a801354014040520010110703a190340d44000402c800f2101c014106008051080740000d8054aaa894601641c9441c0150130a65611641c40200356000788081d110b110b44460040c400a8510f000c0500a41c001c0c0d030056652802d0020700e509440d440e14000311106102c8410504480c0104151021348201030021580c0300380900040703140c8501a16240c40d19460594600002d03a000200b011029202c0c0f0199 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 780884145 1250 780882895 780882929
    0x9030503161d01050c25030b011710020918010b091201050903071103150108060403170709030816051005040618080a1b050f0607030b03010b0d14010b130501 69
    0x2c40748030210010100802d0100d800d01001907000344094400150800100d4076207503000d01c04641c00d1111441c01201e0a100c113102842404402c44145000d400c030303c0080038214821128560b40c03102402440d4415650111341c07500144c0d195a00385804040d615059041540c5509a4502c2d46d8042d0181f20700c01c3c00814000c03000b0101c18024107100718811030180d41003072b40a41728a01c542d4500d03142c181d4107000d07660480b02c0700300521491502a100701c0c0c0c0102003501d0030340350207040844185001c3c12801141c2d81044009070b0700061040950383c1c0003480340c1d00d4081540600344111440c50000b000d500546422120107401580464840e602882052000d850b4111044209040410b0054940c000400c4400341c150300030b106080f00c840a900030f4607002c03406901e609040a83c100d240f1b03101a002481031101c80c40c0d0500401c0600c5d0f400302e008108600a01d00065020b0f4540400207150000c0c09041a005c42000e40c0400f40710701e800f8120303400c0c441c1c10030360104c01840709014416039681a4100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 780885395 1250 780884145 780884147
    0x1909050112020a0b0706060b0309030a0f0905030a0f020102010225110f0117060a0f0909020f01030c051b0c0a150f03051e1312020325051507030e010903050316 70
    0x9841c0c5215000b03424892810b00301940c0300c01c580e0020a082e0345841c1c0750302c030000f0880e0100009620416521001c0e548130510010010405020350790040d04000d48000c05010390790380400c1e50210a580441441c00c0808540300603800380c000c001c081e0714410407401014006402e01e405001565106102c00313400c4000c2841000500c9150071410303070000300c903995500f42c2188c420410640244009100e0300c000c680d00c00040c408900c0c139400500c021758888912100310b0400c2c2d0f160007000d03c424201030000980c546801021070140740005603240d00703808440c000f031003001e0119640f80700015001180050b110f690b000805403101c02000009101c05d0042c00740c1030310070f00c101030264003c0401035281c3d5002c0401c030b2940081c054440c0c003400b81c44049800000c0c1501c0b4075600c6900094028640311000030a07440d1581c01a10100c528440c004201c070000241c2c08140c94020702c0d0541c0d584072554480000880041c00c00e918031949561170025004140340e0403001451058200c1030341d08bc0e04a40c2c001d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 780886645 1250 780885395 780885419
    0xe030a091e080c1c02031002041e06120c0302040807080618030a02030315041b091706090c120a080a090e010b19055505040501031a19090501 62
    0x461140150031403081c1e02e106141c2110026242e5403c16004c40810380070740c00203410b044000c4c5110710b00360b07400642001070341040001e50303908020725904000d41d24681a005024099282e41040d031640d6500075280f40300d0b009a0540c2c01501c00c3c001210401501c0e09040b540e034280c00d80d5003030840341040c12001648003000045400400065019604640ba4040c4003000b102071040045d0b40907440d96200070301c04005581c481d8070004d4a80e50000303030301e141a110303c0c000320400000394070581200e4200f00d00e00500040702c4050341c2040e00c80c80f035801040801c103414890a913400920700000000e482c3c900320b501601c8201030314a40e42c0c0c11485645d0354828402c0e58400d010f16101d0341c103051304241c12498020310240580c2603d942180001d9201c105904840b9110000007901c441d40300381401800b644981c2104400c81c6009a07100c120b2180820302410501407445418100354690b00d800400d691066209080d07071101401801140c80510101c1c000c0b40c126028600030b5514000c00019100c900030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 780887895 1250 780886645 780886649
    0x230705031e19080717070201090c0602011a0f04091707150e06040201120f02040605130602030403020a15021002030a05061207061202031510020d141201060c03030e030a091e 76
    0x641ca291801001c44191001c1000528130024000720743c102800d401c907a4071155104020340e9000040203001460940d216403000e4021004680c5464034688080642c4000030b501c0c08003c851003041d41d01c402c0001401360008000041c010800041d1070404881110044c0164510406c158462800742d0303801501103560b440b40300c01007541700001084c090350290000c00004160003101145d03100325900e07024203a901c65031054000580004001d0b04000710189200c0240c60280302841c940352175500041c1e05141c86000340d1100303110b526041ca100030300800a4040b101e0344440250b440740b800f01515001040700303d8101c4e01581d8402c001144204000c500304e0241ca0740380d1501058900e1048403100250401805030440507249440c0e000d090307543c80103124811249030300600120a102e100180840004480411a00c5c41404005101341940c074402741074581700e01d0314a1114506060031809401401c00055141c0400070300d807004264408000410794800700034000000315219102d4840c1c0b0503078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 780889145 1250 780887895 780887917
    0x608011e030201050a020f160e180705011805090103061a011e0c050a0b040c0f1211040207051009200108220201170f01050907030903090501230705031e 67
    0xc004107100560003440604a1000284115607000c0d01c01e00c2002d10306200312a000011260905040180d56400013040d079102e0090101100c0310b01310031840954440b210300440c2d040c012950051080a09005100f800507c401404201256500d0800c180140040c1a030b003661003000030310203c0e080d402118054620f281c2000a05125141010100d40104c03841070120399900414010901040560340c4441c09079005504526540b49424080ba50f14000c5a01114030f0405141181011641002045540780720a03900540e5540d800d2414900300354182412042e040e10f0011014207018041c40c00320364001101182c42ca013006001e00560720684121400b07214130900c007011400c64800d0502c3e0b03c80032841810813013803443c10341c0c5c3c401610035401c6854150010b580c1004104a10341160032a8000086090802003c0701c3d41e1070050050325075005450610182c6440301c0b0b601080c000202090110382401661100e00d1803174280c0c4c0340e50080244c0403080c100da081c00002540c0c3c8004a40d070341800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 780890395 1250 780889145 780889199
    0xb43120507120f021c0e010905031c06080d1209030509130c2604060c0504080d0314070c020112050c04080d05090a090b091902160326160e28060801 65
    0x2107170000010f010b40c02e09808440d5254510500003442c2040039003502e801001410113804080250002219882e0f4800c404036400028060340a42d003007039803981001462074001c540c0329550705041e955071286107500307600100b1058000d162004207500000605820ba0740e04048202100d00c4520034407503040e00d101d01c20a0080206c0c000550310781c000040e194171400c0c15805c040c1d0350b64080d402c1c4111b40c02c10502082e1070b003403203070f410b509075a903119804070690420701603412003500001c0080e0142100460440d607600d000ca40404d400100b91001000540c045800c088158880100140c0008103e540075000300d60010a0281c424021000043c1000d083c458007503442c00c1c40b07500f04200a050304007a169003003182c402c8141680c101c605403107029403602002d0309034050280d244c40c030100340e0009000e4000000d1011070710707150f00900e60407455881e090801030003510004040c00da4001c0c1c0b04200e0815100c1c06440b00380040705600440d846500c802d045681d86200c9a2000c00500c40c0c544c10441c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 780891645 1250 780890395 780890437
    0x30a0215061302090a0317130b040e2a0c03042103050a08070c0204140103050c010305042a152304030f031b0c030b43120507120f02 58
    0x303056800303011050001170040d181c4a0f680c3d1655040984521041041c00e0b00c00500984960310900c2c2a0005204c0400d80c90b10345440c0540300303000750901418110071480c2004155000300000f4223880540041038085650341d2084002041d03483d440741c800c40c200c281d504042e24228200100b0003001c0160140c80c2e10f0701d00a216001102c000c08014241c0302813141000e03050000d603c440c03149480b20400c02540c800c040d419070410525185148004c1d50415041408110009015242031440f0450f0030000f009641c01c0d01041d100d0b04005a040102c8030001d480440c2c10017030b440301c101c000c40b528000140d14881c1e02517501100c0361003140400380c00c600e503100c1d41d00002413103880716a04003910110313110320340f1f5240d50b525021114107a00a450340100b401c18028450402d0458030083c2284002214000c402c1c149041401c900ca0420020410b40414640c46214000d00c4610350f1400350300020401307850110070142072031039009104035980d80f40000c0818200d2144c400c550080d20036505c0440700d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 780892895 1250 780891645 780891679
    0x901090503010e030f0c030c0f011e020a091502010e0102030f01050f010804121404050d0606030b22020d03050f0c012304030e120f121210030b0703020a20030a021506 73
    0x40d1150103c20300b0303403004000c158040d0000b84080e4027802c001200200c2d600007000c502c0c084103001d520340050385620400200781c1c4c040c0c1000c49501210b44d05402e100da00d07001403006a0040c030110b00104400d500000400c44540d8809480b80c0c1a074034219070701d5041c00031380d20044601e000c0442d40100007100031040040100d0181122808842060000741c1c5402d8031840428220031540d01c007100ea50f5181d460034010031041c0b25015a00007140e100301440320201003113041048002d18070190048030703c4100d4105052269089620850b45402d070955200d006c644200d008262111300b1000d1441d50000303207071500c160624154042c54155844a00e01e500c59000c10030f0010364021806024407901c0101107041100340a141c00f40ca0403045800e440d0319065800c1021002c0007016810301c094025801d00009460016854008109203030050721400c201c0e43c02d0301e02100c5518130084600106403101443c013800030003030411014a80c29a06140d00160b50b080d180705c2c055a07030341c0d03210b801d4070052001c070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 780894145 1250 780892895 780892897
    0x1a040f0e100513080403050d09060f0228020d08040e070c200a0306060b1209030c1f0b040513051009032a1a01031b0b09040b030c0301050901020901090503010e030f 72
    0x2c03082e028411283c503c92956858941e601541c42180c003504203500c440485070b007180c540700041406003840f00882001e03110007034494400192011540b807820320120043c40c6420403118040b07078042c02038403107801c0d5130400300c0301344c3c000307100b04003c10100800151100d8032881030404419030122020b81090f1844034644202e521070101e10750051050b040c00408100d490154000400c031940202e0741d206603d051000030420010000201030344100500c0d2146c000029039000d4415945620700004c0042c01c0b821009801003226596000d030518090043c5803011881400325540701d0400c480100300c42548000a880c00d805002c1d011074400350040000005500d410030f418507103910304118120706903071204000e89014180d11250615074006004100c40489140e00170b80805007030000c810b02d03144403106907201e03461031079020710b07103422400f9601d0710100700b2154501d400600038006468440d0545000703401034407507240000d5100d00001840d04041c890f0050003440000a5490a412440d040c0c090b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 780895395 1250 780894145 780894151
    0x8090904110414011d011503200409060905061210110d0219020f06041e022101090c150801030f0f0b04210509030606010c060f1a040f0e1005 62
    0x400010109107401c1561540304240407040388a80041113541420a80308201107052540162031046900500034030002000003182442c4525000c00c0000303d808180207140300e03c2030043d03981c50006c500402c9550468102c1d07420b0300d8400c82c04100540c2c1d503804201e600103401e400040c407a0060085040e02081581061222607420100c0314078244601d00303414203d0340100c2c51106c0e100358081b402c0286a49c140800c0c030898192400401d4582025114507191210400a51031503207000640032045403a9801201001035642000c0c035100c002c1c00041c40d0180c400c03503000b2180400c500034081004010880391001014941d60b83d06a1a0700b165541200002020410303a4170b440c29883c41030008034540f001d140300c1d0b44518403403c00c0b46038042581d070300217440101100503c04144802c4032161400598541d1014003460003c1c0d0711007946c00c20f0002844024180500da500702284180100c551241c0104503120560b0200300c4400c000300c01104440c3d410b030840b505a080181901049003081c1c00c00b40d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 780896645 1250 780895395 780895403
    0x40504020f01081b04230909070608060307030b070f021002130603090f0b0c0a0305090c181b040605090a080303040f080705030f0a030c120c081303030f0c0201020408120708090904 79
    0x10f0304c0c120340a507240c2142c000d41d10109442c41a140c00c0b00420b469140e8600320043c050f500050342d42000080581c45510a00034103040060040000d40f899400304002c6004580101144405041c041d01c02016909881d0340e0001611031440c0b01242d02d0313028402c5800049002008408880c1400002c6000c0e02144500761600c3c06002c08034000304008200709400b800b980b4223540d0360b0752400080502900ca00501c401d6a5400880700000b140d200c032000c50f009440e0140d074a0782580d4079201810504107004054103040003010074042040754000000341590304044413030b14601d590380c9410990328401158000e0000000c0110800080c4080e80902801849a41941c2c1065404c0c4681a4280c010581c0344000a440e45c010700c0a554000c251b03100310100c00300c003c0c0482d913000c003806002d8440103410780711081e100b003c22009062023640311a2600000520030322a030004030400030b000c0d40260042c0d03810307030284031b0180480d00000c1d01125900342d4410146428002458200000d441000304107513 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 780897895 1250 780896645 780896671
    0xc010915030b03010f0905100b0307030b04020d0f050615060408190314030c0307030e01050402030d21050c04090c1d0d0201090503010f05090105010609030819170c0c0c040504020f0108 81
    0x760107560a01030840171142041d8000784105c100d0400303510701188201c0d03c9a049150650289081d00c02194107030540743c0013104c00015484074400314201500304034002d070841c1c1902c4410b00410a010640501403200b0a524640f00312030b02c0e04202e0709206520030000d0541c02400409a00c82c01c201d0311890587c024100300d44140c1080350540c840c4e6000302d802c1c1c80d54001c00030400c01d000c0d400d84240e0a100c4014402044640340130303408243d80b00c0110b00d038041400200140c0120284041c22a100c080c1a01441407006042228848005401034000c014031503007400b2900310543d00c1401107c2040007a00e11281003008007500b40801400c40d20010390402c0445400400c0c0c80e103090103020251002c0080c0040d6600c1d15899440c01c40d5230682240081021010082022484140940301110320841d5000c1d040e02030201c2c19150782400001c0d025100455400700520514100050801140180256095503d20340d0810044603822031b0000d50091040c0f80b0340105510502090f540031b07403541508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 780899145 1250 780897895 780897911
    0x7110301201e090d1119030b150f0d0507090b0f030706111002040605030403020f0c0a03080c10111206180f1807170106090c0804020603041e03050a0807020c01091503 73
    0x4c00e40100c01381c00c06035058600c007800c0807128188200300400000e000720003514100d096545030008150098100240d0403030b500b144401a0b503540b9180e6030100e0307005100d1840400107140a507101c40c010b00c2408403052902c0041030850820340c1c4030903000ba40c014040c14815041c220292407041461600c0100c0b8031611203600c6501d0b4861000300003800d01c80d01c0c0c85480e86002c0c5402807500301c1c440c4850307000f070b0001800034040f92503c2c07928205403948001c0d0b00da01d40b1001d440c1c403840c01066072400f185040c02c01000c030802042460040658200485408400c0d0360b80d01d06000d050100700c0748040e00d828840c0000b4259125010070701e1340003201c0d02140d40504801c4100d45180c00b100340c2050540710324491800c0c0100d1002d2154400800d00401c2c2444075001040001d40783c8240204064011200040042d0401c202609042c00200450b100c0350540c26040c1801001908800d2012000c94119008a185240005000b080307075001607554441d118140120702608a10508540007890746890203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780900395 1250 780899145 780899149
    0x10b0402070c0509060409080412080f030a02070c0e0c03070311090a060e0117220c090f0b040501141e040b0a0306050718060e1c0807110301201e09 65
    0x8004081c02400c01e81e9401d810442005031044c0050000c0d4480c43c074003500400000c142380c080d03500715107a01c20950118410741c14002c00c80d2262040c00100104000304001c000320b0b555007e000c00310300441410660a880d803800e800c0c0c2c14402d40315242e621105000091100344603030003191151002000c41c509150b0080040b0300c840e1030030741002d8040b40446041e040d16581c0705a01c6108006c204d95903102d42d0610002882d100348202c9030b150820440013038018140451024068000c0c03140d00004c2292075291060303040281640003010344100e0030319000041c50000d0784160b00b41c1c410000e000e109040e00f0104012400c0b4542c1e242039410544440c1c40208503586c3c1c0740541b005500807100440c20745040d400042c414040b0031a0b000130805140c1d41070294640c0311040360801e040a030340120a1144001d88040300541e0103400901000340003450404116811003002c0c1800000e0f40240485003c000150a03049180101e0500c840010301c074142415109030b003400048602101c425242c043c0c0080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780901645 1250 780900395 780900397
    0x2031b0703030605031006061e030608030c0f0c040c051c1b02031b070602071206020904110901140901050f030c0d0504051b0609010906050a02120a0f08180705090405010b0402 77
    0xd400e4012940c1c8480810503420207000c400c1001c1048082084084c2c1400b2020300b080780c0341c0101400c000c01c010030046042c4e002c1d50002024010580480341c994540444203980c07120068035500719401803d1000340e5504150042c4400000d081e190b550825801890040100300300c03401c1405038940340c420b02a83d17400f25940141701850980d000d5a03840d680451014806500e0400c182c02940c4520402c02c10544cdc04540413040c0d80d008001c3c0c25040385181000e074064051a9510750780b142c54015110746004c03408004240d205000e803078524804d003042e0002030a5004030030341341c1d01041041126420102c810703002103501045000300d443c10039580401400899034115012141039102894982e54400d0b62071030352191380e00131940146000909000200010081c2c031810b81800000308a48211794000c0c003400d022018020b806c580c88282c402d20040900600041c003401180b10b0001095900000101241c034400c4884000d10b00d843ca00380070f00c000e24100500940d8155a1080c00c030100fa13075540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780902895 1250 780901645 780901657
    0xf0f080402040b09010b070c2301050c0c04151502120301050607050a0b0411031e0307060522031d03030405060712050403170a09170c1c171806040e040602031b 70
    0x450410344070300071fa00d800401d81c4602e40003e804407841849a0080c0e600900600b107842d0350a20b0025111032180d20510f14045d0881e0401c1d80c403c0c20190383d610404d01c10720300b040c100e50b00c9446c03c1240512600060761241b080710f1664000301010001400b071030030680d0080060b0f03407007503007141c54440e5291115076640e40c1c103880c1100c551424000400346484e00300880d4402c4200202c003075016941c0203020556902c00c07180001e2165842d070001460301c104280240516101e24021202d00d03000600d4002c1c034600f4202122140c0381040300d460389103400c0001c107550585a010341001e150003150780320411495203e1028000300202080040300041d0254094200c60714145911616515a1030004e840c0c00c950b0740240003100c4400d086000383c448d0003e07040c0d0200c7d078103a400814640001462800d0116003440241050040420352000c83c0c0202c0000e200c0d03101800c001e119461019070400c9400c0c410351268030840b062200c040380100341181d00554000901e2140c00514039082101c8180c560414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780904145 1250 780902895 780902909
    0x50601080a060b060c0303010905100312080906071805151e090a1d040f2a050301060e04030206040809031f0504060c051306030b0310021303120f0f080402040b0901 72
    0x10112002008014041c03c64541c000301e85403400c004443c0c00c0355590740814810024030710b03214004144404076100c40003001d1a0445500c03088680612000341810b04103a40504051141000061056105d042e88500c1d8910030b03c02030004c28074003410000c2030003411040c0f051100c410020403040794689404808440100b0416548508002c1c08103d034007071981d400708528094501082141c5c2000c8558690b00c1175011118800000a6090034039014940580d01040c1c5d403101e258132001c040034400e14408880c012402032228940700d07030b0f099800d02819200100964820b4001c540021201c8000e0440b80c04042c1c12980600684e43c11850000c27501e01c582a00966620244810b1240301e000d414110007003400d103246080300d400c440d0fa0700f03076856129180403d0741e10f901a071401d40e824007072055490314509055403910a4001100303045151071204580741800d410b4025202030060300941208801034990250f80e4040c50740070f0b04d007840f000b007080360b02c079548a510600a03941e1140c120302030302003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780905395 1250 780904145 780904153
    0x30909010e19050c0d0c030f020a090801050c040503060f0411031e0607020a410c100e06090409050c0306040c050f061e1c060b0a080601170411030a05060108 69
    0x110301c12001c1c907030168200c0b00300c0d242854100b0034811070039011501654040304001680072080d02048000b80b000c04002030079240002020880c4640c803041071300980d08140004c1000e0b4031180e0341d14030988100c0c0708081e0580c00900000316107007001c6600d540e005000b4400302445000d1440043c1c1481a4850070648d1400301c090904c01d944400c20072564001854001401e40310382507110b142c504202c1d2107240e055260700714000c01d880e00910408480020006418083c3c01404551041d2070300c082d050660b0150401c40c2c1e0b82c20400740304050f4500000d0001e8080742c544110402804060140c01d84250345900c5900014001034504000e00c0d403181e4042c0c180d508003182400c00300704845201242d91031140300184428444c0c1c4450603a91072102c603900800943d106d508010381d0402601c0c1e2034071421400d1030043c002444c208200002e002e103403190755505c1d500c0c0d65418010749100301c111309011a11803106001a00144c600c60b441804e00100608941c049406551414030700042600064480c2d08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780906645 1250 780905395 780905401
    0x603200307021e06251403090a0b06090c030a0f060b0c10051605040e091c03020406030f0920190f0f08011103310303091401150302060705030909010e 66
    0x2c15503804603c1101010303040300d08020102803540100007843c10138041034031060024641c0034600300400300c02c49048a90304d0385418032106440310741001e0141e0b205610b002c00940245000400c00d171041c40c5a01629085407501c40d000c1d402820010703000d10809039164004a007420380c82000e0800b2410b0760b0014003a980926400005961014000c4940302410503191414076070000e094070150380c1200034040c110750325244ca00345410300080700c103201000103100c056071165254000b08107031207031070700c0a006180100905200700d40c218a8042d00030100282c0350003440710f008020442100b001450700e2a202d0241200ca00d8240ea180d01c030929118903580104203040d401035031100102504002000040c9000181c5100d03880b0003070035400800c01c0b007032081109010781d4042120b2603400c40031552090b50749103000740040000300003d99030305031840307a18004840140200151200f40030140fa940524540c24001c0d59080400e00700d03a036010a00a00f10161207001c8460b001f40100710304014581 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780907895 1250 780906645 780906673
    0x40b07062d021305040608031605120f040303020c031902040504060f021b06010e0c070f05030403050703080414040c021b040e060403030b0907050a020c0126071d010e0a060320030702 80
    0x3e065012600070b90034085c04005404020094840e008401c0b00029882d54140c0342141c1059240304003425010004214200c0342e10081d0046c00a403032003a000c40d511007404504241d542c0c03070008541100382e61904503c0c001820141c100d2500144944004905113511140078010ba0304101c00340000c4042880c104134a0480c1040f0141c01040061000105030601c0ea10404003032290b00006401c480f5031502d0401001010400c540085400c081981c2c40141c40746811005540140f04100c452021000c0494a500c3d2600c80c1e680203c10940042c0018002d140303c80700c030206c0c0c0b0064264059540d0341580310000c014450749100c1c0d4441e44d800221450b054041110a140241441007000310038044082869000901003188940034240305040901c004140c031001b04072661540d0072160444140040260000001c0c0700340711003503086c5850400250011507081c4071141610354040724000080083d207000e43d0141c6a000c09000d02525460a20390262544d07034026158000140d0005007498045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780909145 1250 780907895 780907927
    0x1030c3c0309020609060307020304090e0102030103110111100e01020c0a050d02210315040e0d0c0311030a0e040b0402040b04080c011403070f03051812070611040b07062d02 76
    0x2100e29400c0401c04150560046079183c010940b03070724003541d000000304600500800544005160790f007018030a0b08441820316010750070a1008a8012081081b4007110790301860003010040c520500400c40c181c64500000e01030422613440d140a5507003000110f0101500b4071410780c080b03015800500d000401071900034503000301c6070b00354034603400f103100c0c50364803443c5440440303401c000324000404501c5038840009004001c1d103001140f035407103400348ac0742000740c001108400ca24040e44070791700f480c4040e4030000d449106d40d00200340002c900354808070345860300f40d110301c10045010304014203003a00c0e03a1000d0170b1035001c0d420201c01039000b61703034400300c2e90f0b480200b05400c0101050902d0071420304040280c00d00300c8000100050584450000341062120038070b401d500c101440885000f804000100380c09540030b60020389103a41003043d0384015040c540f00302c40455400d0356a1074500390440c0c41c3d2100030000114041250302c0001440c03209440b22103114540c0075074200700180c1d1000c2440c614000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780910395 1250 780909145 780909257
    0x1c052d01081006080d0e181807140a120807060c020601140f0109090c0e032a06071e03020304080709050702160303080a15171f0b0f01030c 61
    0x4200e00f0550203100281000c9060100c1c0c46803802c1c0350ba08182d0741400207561903090700707240c1040d2000c04200000340d00746d0300341804418401e4003990391458a8101d0303e00031050b10b4080f10303000300b9003141c2040110681172240300031500402c4054207000c021754462066405201c00c03503006910120046c4141401a10034951f60032040300e400e4940d807903440c00a40807a81a200d40020349a4944401c00054098091a09060401000e0f034099140f1503248401c60f02001406050f0b05000511b04182d50a2079802c560403141c21101d20350036501c3d40d281c410f00811003c4012004c5001c10301002a00e039408100d128044c110a000c00b080700d02d003644000345000e40c2a0384003201e500300c04104102194215108a80080700d006011840c1c01a01c614640120001e80c4900bc0c02e03500f414404200510100d044800c0750034606801c059002014141400d5031046407145500440000900c02c1643c001c1e4001d080c0c119003401c10f0001c2c440d041144030385480c1440c09104e01180382c0180c0c03c0e806013140340d00582c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780911645 1250 780910395 780910423
    0x603120c0b0907052202160501050106090b0403080f0a020f070e0103110103050412030e010e15070e060c070608040c080115031205040f0315090507060c05010b04021c052d0108 77
    0x14414a401e0024009660350380c1d17402d94140090301034142c3d29206804071105203075800101054902c0518110703008100034401c0b200041c569000c0070599128141c211421a40c200399518100310095a0210141c0e012440d41c0096105002404004c441c0c14410180200050900c00b442c0d9807541c00d2100900c0500441581050f10b004200f00005400c55406000b07480d140c80c00190110185518600505040c0302c0302540d0b1040e44694800000b00302c1c4201c1c403440c101d1fa142c10320000c8000903c00f690060301c143c5099a00164024840303075206004507a4082d01400140300b07603070f0f0355800a074212000308145407131241103103c0600c00c1c030604546ca1800e900c2c107031601070314181c500007010002d11200e01005200c1c2201e000300c0c00c40004583c104a040e0780d040403d5411003541c81c1806400c0b108032020849240d400c1c80340d005158a018402c2d5506c0002d00140c2800035440300320748200401004002c4d40741e0810310b52640203e540d078003d4a40b0200c202c01c200d1011941009404c610b4110100a001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780912895 1250 780911645 780911653
    0x1605060601030b0f130c020f010e010510090b0a09091104050403020c0f091509060d0b0c0d0c02030f030f180f030913050c16030509090a091e0803060d05010603120c0b09 74
    0x100760307880d84044c5c814190500c3d40c00041d45214854200d041c031003601c1000c41198200031a000c1c51120641c840780c042d46850382c45600039551840c7c8102510303886030441d9132004000d0001c010103000c41d00b004d07800d14031410429000401e080001002c985068030154016030040e020b95840342020f02c281e40701c5800840f9882d800f483c0444654004400d50380e2414040c0400b0804a000d68440ca20741c4e0400e0b99105000c00f000740341114442030b030340d0000d11004030b0361801e1505030300c0c8460021080720702c1c0902d5000f0b0030f491076449514204800360040d0104485680c401c05041c0400410700840908003860f00c0a180d03220240810811903035044880c01c207605103400c050150b800152000c40d8070702c44051110102c0c03512107060a03101c0d17004680d90703250400041400c111103034003a540215031161050044a01c020b4000c0d80344611507030784010051490788104049031b281c1c0780400b5403846c020f100740c0011078000e44942d582d05926982c40e071103c000c140411401d400308a01e00003250b5100900700010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780914145 1250 780912895 780912919
    0x50c2a01201b0301020c01020703030c1707020c1203130b1806030108070312170c04060801230402340605071103070204090c3503090a0b030c1605060601030b 69
    0x65901e801520850741c502c0001c0368041c1c04980c50a4055031504040d0b14000c54482c891420040c014051f55020040060100c0d800080e8a207044803580d4080d07002075004001c0902d9810900c004283d00201091481c0300a00c041c14400c02e0030a2640c0c00343c01c40055642d211040c251b42a410844a009902d1180c0750a00062005c140c002410314206c1303800c0140100d022404882c2550000304100710200040703c420208a00341603521700400441c0c440d940d0781200b90381da0304941c0a680030044c0c43c1000307000000e10407800c0c0d850950003a01200c180140c020303140d01e1000007a0010300da04540740c0750b070360341c05040e00c03009012041c0b04a030390000d00d40c140300f5080340f035000718281c492183e8100248110b075101a201c0c14000090084000303000c202c5c440b2000c0d100748003211040030403429010644100f05020b40c520070316010094444503280501200412410142d13070b502181c000a0084070100b41c28004c1c0c40c803100742d107106080103034000c0d00540080d050100c00107080d08c0c2c6500720180140210300b80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780915395 1250 780914145 780914207
    0x911030d23030c090303040e160318030e1302120105041409060c1303020907030207120e06070f110d030507032606041d0105100f14060406050c2a01 65
    0x1040005100c8241c14030355964511142d01014001c1841d125010712011a000c240d14111050550055403c0344a41210b0081c50804405481c8550101d0701401c800b04900000a40111104a0092001404002401034088012040303812040e40c0e60442e0200c100100072a040c10f1003000c401c1c80c03201c0c002c040c1c00c0c6451072800d0342e64200a00f00c01a640c000040200b260000c11080d100a107a000f440300f042ca04000740e0060182d04190800d6403402c0d1400102c222050180000640b980c002600a07401c01940c0d480340040c034468960160390310006850110100da840c5480540083c0c440d442e0784c0d03100d41e06030800801941078a9001c0320106898440c150502ea006142154480b608075800304403c104045800340c200310a100c419070355800c0000744104100c2c15005481940c003944060340c4101d64a4071800810340c248540c66401c8601000b061281921403030050900184000449915650b00c1c0c540540b10b40d074200c0e20021944a4044203401c1c0c2d0380c0040c207004501204086603100481c0d04031b07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780916645 1250 780915395 780915437
    0x1f1a0d03080f04050129010e03150c0903030d0c0c030f0809030412020303190e1306120609170408071d060a0b1c05010b090f0d0812190911030d 63
    0x21005800d00002c0c0001e0422100750002c40012108008031852101905000d03000c01c22101d5003d4007180841154480310304001602e943c89103a0300110350a1074441100c200110750100b17004a0701400100001d2450074a5801501d04540d40c90b542c0c4500009582070007045480b03044000410007081c1c10034480a400000b090390301f0780c0d002c0f1a480640c0070082c0b000a1a42c030404105115900283e40c0d1600d110750000444481d500090f0790350f05c0c840d0b100701c01d070004444180c0610b2184403269484c54003c51260f501c102560391081d8070443e10585941c04030712880e0415400a041540150030038040034054110348000984003401080d0300b401c200c00002d0740320456000e060611200480d40c0884c8100e010070004450703220903401c020300c0d6100c2d4080b11700c3d58001e040a030300a10320704002ca00241040002000b00740c1c0c0204001e41030102c03960845840701c4014003145000c865001d0701040448a46c8078101c20315214107421840103a11905140c2800d515411a00c10b1144c240114402681c0f020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780917895 1250 780916645 780916651
    0x80a1707081914161b03090902070c0305031209150402030a02011409060a020a020a06020d1407060b10080601090b0319020306040609020c15061509040e1f1a0d0308 72
    0x2040c418524028546500010f120001074114000030620500501154100380d0720320301c120b103640300580d4140c10345420038000d205e4240100050034901080141042c00d6028000c2d003803103507a48001441d80c0c0e40391140b031508032050340c048841c1803006100001c1020040c0c91843c80080a80c40da05c1d151680010f42c0f100340290001e4140b02e046035584418400c13613021550804130080115441d106840b03070082d0344244004080380624408140490400d000051070341c5943c40b55a5805440c90a08101c0400794100c3d540c215100b030740314040d0005954071403080720400e26046d075030041c4078500800010801242640301d0503480a00704144507000c1d03400028401443d1601502507503a0321000c01081c014001684040b580910115003032000e8580400d46007a00c184180130100207440da4010030000c007801c5ca00d0001c4018003041100001d0070640c1201e01041d030713400b050329100345480d084250074818114201004607607490400c0c0500d40301248a20125900307880094048071759a40c007824410b805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780919145 1250 780917895 780917911
    0x22d03060606092101050106350601050c070906061e091a0c0703051204060909060609050d030c06151d04050606010e1314220203100c0318080a170708 66
    0x20740b0513000206500c455291004820800030019580d680f6030040c0394240c12054460f450300c42c0e910b440c80d40100900380151050603000d031106913840b00700042d680c6500c00f001e040c032180503085002071014024881d0710018021b584031108112640e03c200808045018104000e03c55801070903c50340e10540400f45899000840c0184c0e5800d03100082441c0c50259403006005219002a0400200b14880500225941502e820354403545525a2405443e001e0050000065000c681004540f601c074113440b16090003810281640001c1380c0700c82e002d980c41508031841d00394281c003040080420781e04460142c96203421700c17280e90b400c0541d5807076120080904141d0410120100441196540342007850b00c1e03103c1d0000c1000343c074000c1048104210422a01744010480c044032080310a06449507601360a503008001d0035540881c80702c0000180003051580c6c040642e0f42d240303610504505c03291080c145004241c01521070b1010603005012020f05291071140c2132103c000d0240842e0004841c64001d000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780920395 1250 780919145 780919159
    0x30509030c0405151c05061b0d0f15080c0108010306270f021c080a030c020709020d02030115030612120e09041a09010e030405010c0f022d0306060609 66
    0x8020002407905000401c201d40c86480d110620200c46006100401e0303004080d03400003100c07800d400d80a00e040c40344900203000c0b41c00180000b1342c42900c50000b0b036148804915524100080d40b09140304980e00740828038921555141110320754011501600d004104980c0144058801180000c03c11b240c103100c001c091a03250540c2000d80211b2011a14020001c80300300a024501b0b8103028140c0464000240d01500580c00f201e0016415102d402c021a500a105035240280c0f4103012030003043c50082c801c1c114003c0e4000460898202d00082580c501c81880c003586071750401402c0801e00d190820468285071400c0c00070080100040c03105800c0760340198184c08903030b4112400b074800308010030a0503848150b0108003c1001030103601215104c0d403415040d00309a841030035450032201e4400542c01307280d1060204104d81c0d84a075200300c0345140302d1000c0d80c211446680c04102007910b00030280d8582130070b07a40061a40341410305450345a0104400500d0241001c8010aa031803240344425401044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780921645 1250 780920395 780920407
    0x105030d0c0809100504090f0b06160303060f170c0f03071206060f0923060f220f020c061501090902071b03050d12090b060105030603070314030a0f0507030c0305 71
    0x81003080d82d0300c0103c050518001c4165a0500600b244d00a004682c0f903c3d00d40256140d0740d01e001d04c80d52110302c402030074040c0351080c88040f401451280e04012420551140404110a6087c4c90720800a00c4c50b00503042030a0300d002c3c000c80c200125009400c0c0124407a450040d480e9900080c0c0b0000c652140300303081010b09140c00c2990142c0016013140c22458501400001c5207180303640301040004540040800642820104140c088815a4000c4e0f0103010401864560319008003050030000808070503045040f44070300d0880c1901c640740c1100d010300743c0c08103500c03080d400240f004642c02010031440c180404040d0740040e14004441c01a29000b507404580c410030859101002110300384501c40070b8044030ba136860450750f10201c0d0014800001e82040c00415160002d005e0008116400013806a4665440004440342d4200801e01e55252180c0301001010032040100a1842440240a15511020124007038906034400c180401007010401c03260021952200600205a03810b1030540d036180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780922895 1250 780921645 780921653
    0x60403050322080d06060813080a030605040509010506030f160b0313062d02090d060207030c0c080610050d03050d0b011e0203130509010312030504050a1a071202030105030d0c 77
    0xd40381c0d0b202c90405142c201444000e025259010305904422a032040c0112a11440110380b000d0b029140303003605502c0255010300088240c40500041910303890000380513680c8000180c20344d2021b80b071101d410b956500502070141000e1002c40c100e400750000920360503002c20610788005c444c81c07007646840000840880c12441402044000c0d058102000740082d03508030101003080c011003001c015040d2110401d040a0064500030790b41075441c0107040070b00310a8181c83d1103000c1c4d0f11291049003040071420382c50380021412940c00d07002d010103c0c018046460840c0d8065600c02d400d8100c90300c00d624500600d80002da02108a500125010101041007010a001a02d008006a568420301012010810030716580000a02646014000b4030b41e4001c0c0c0c1c440c00d00a40d21800e02020b003034614221114000380380a07402c0b80381c20a100e00204c9995400700e8a40110f0442d216808140f01e1f50408140b000190f80312050300d11501d030446003140b941d41b4100000355100d00100c400c10a00103000c517100244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780924145 1250 780922895 780922921
    0x31b010f0c0804030f180b0a030f0501060c0303051302090112030e060f03011e03021215100302180c0f0403080418062108040305030412020a061d040506040b0d05011d06090604030503 80
    0x110701c20348800b0a895100c084900c095000369238a140046d1410481300400640b03070103920304840300c40d15a01551055920124082c0400030000d12046031003554000051701d81c403d8450007041a0003882c40c00001070b10707004002408200c141c600c50482400344084c01e5040341c0451b41107491140070040400081c2ca504011050503a101079807280105216031141716010600c80040385001904038056a110701c101e140603251808043e4000f03a070700302110103500003002103d810866141e629400c1070140d0300829019803017608100c4810340046410130202d52940b0501d030b1040d110010510a141c00c00c004080250b011200b041c1c0b004e6140441b002c140201201160b000c0c5401c502605e907140e49400b850341c0000c01c021000c038011000c9000c0000d40e140305201d0254805e0300065250000d00d00700007008042c080182c055507100e996001c0c032160560f40e10040030003d610400c000702d002640c0500301d00f00b40c1200060f003507080e08104100580d2000c040b4407070380c1c06a1715040040e00c1c0d0715403254204523 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780925395 1250 780924145 780924167
    0x60620010b03010f0e0f0a21110d2609060c0d0b03070e06030c010c03141804090f02091b0d050705162609030d11030903031b010f0c0804030f 62
    0x26518004c214800d03600316421130405000703e00c08132000d40918810144ea15007080401805404510061804400311004050b2098165203400404545459a03a900f065001e02c2c0000203e84103002602c0401c601902d840e14005018070005054508446099120300c0f0080107860b0045d80003408601c0d200740c2e64002c850b500c07030107402c031556036071a010500c94a00056496034400d2140f6200d400c403542c071a07a420350381d80b40d0540d188210260318541d0f8200340d4211004c3ea81c03100700d800b0424607403502c0c1c9116401081c3c3c050b440700d4514181d140180104050b000c5d102d5010450410621800c0030007003001c82d090200300600014480d0350b14030f001c44231402880c5001320348008501541c400d100801400805807040081512450046010380c080d0902c03620032100c0e00342c0c00034100d42c4036090003010303a041409030540a4918041490000900399031140d0300c0c5031401401d996142600c00c07824464404000500704003044080d03813120340a020781c14000c00c001c04104e000e0307601404080c8180c40f6182 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780926645 1250 780925395 780925399
    0x303090305040f0b040f080102161b0e0403050a03050105270a0e0703140c010203120c07060e01020c031b071d041106070f0b090a0c09021809091e01060620010b 70
    0x115a4a0310b00c0e2113420f601078031464844a621b0302c40800c1464040c030071245a06508c4c007d10382035034455038401401560380c0c03010301c480c1c01c042c480c0000c494008404143c8030300d00c0b07980c0d415035031058090b0240480700103030005d40c066000c80043c180040440e000c101004140d80c1404402a995130809801420740d60070b20422902541c18000100440003902864001d07000c000c1c0d880a000e0b14004982d40d00401c40e0601140c1160380c04200502c00600007056a14060b00011880000344102c00c0e09aa100410202071984002000c11965202d070700c09040b03201c40e032406000c880b0301e843c150655031284215940411202c5101190070000510312109043c40c024004c95100d1f441030401410240c50400c0c10fa8525006400150054501003142d03800994482c0070900d0003420112000000c0d00303d4440300c040d940642000307680715695201d1961203880d0403402080215000d8182c0061038400c0340022510340e0500d030040c0a0345411052200710840054000d01d620b40122184501500a06200325 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780927895 1250 780926645 780926669
    0x60522030c08060c0702060307030b01030e0d090f060c050c060a05190921030804080c010b1c02040c02070f18020d0507080421020a0b180d0c0506011a07030309030504 73
    0x4100705141c8032a000300c51032401550416034510760782e24024480d0650081d071005081002490742c074003d41c0a0000c7d00740601d400107180c800d01000d030b8500944030780800085030014134100040152441c00e00003030401403400d0b0041040c075581d002d65035040001c00522803140420030031042131044040d540303455038803c0020005545024003030003542c183d00440d40421b02d40404070718108001c42d8008071455041d5501c0110760f0b13480c2c03907501d015000313514003040725522040d02607007554401100d03c628000f100c4a480e000249403040004807900d9443c043e056400c000401c0160148810444084034401c401002c24455954800c2000384031750b1885900d05071804052100d241d030f105007000e1065106003a0340d041140d401c0890442c0300028079290005a1002540200040e402040650094803940c6441d4051220844540c1070040c141c988000144000304040180481007020358010510700e41c0b0400035a4550641440501c03681401030241929407410000309807040080798000c1c500d0b071000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780929145 1250 780927895 780927899
    0x110a0224121b090108040308040201032d0c020a0b0c130f06020a021806060a030f142814040201081509010b181912060212040c05190e01060522 63
    0x10a07500109580070806030034000140caa444032140c040b1034140505840b036005a949a940489280900802c05c904143c1c1320f00f1031107103078103014251101c40900e540e007482076000e80c4000c00041f10024407800c0c003194480d0400501090f500d410444c0c008200a0141e035035503005640032106512170f50311000152000754000074000b03a02080c0800c225100f2a01c2103100c5c1c007002402111810146e603821740c000d000300021802d43d4003aa101c85420f00c1c0801c0c01080141043c160398255020803640092036101001810404000080d000d01001d07910410400c1001a00070514500d504c2c0200001e05000c01a000302d460014220100c456802c402000c0c00071541e102d080272003441e0001034401d000c20911310782240051a02c2b51624069488220390402807034030700402e54420591030442a21030300da08001c040d011541d045442807146019034800c4004500c0c00081c04440400090340c02c690f15070b95081402000a0403000d00d044a03d2850a1621101c0f2040140c0c1f000c1015581200440c14031640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780930395 1250 780929145 780929167
    0x10503090a05160e071706010e13060303271d0405010e0706110d03180f080c0111071226220f030e0a180911060c011506110a0224 57
    0x500400d48030516112130300c0d0380380c1c2c5030283c0d5003105003440320302c081034040300040d4154801c103c42510044001e2140180303000340c80d407440485610b40c00682c00602504200b40c0f80891100311040700c0d801c0796480340086481d04402200c1544c4080c405040100340c007000ca42440303002d401180e9400d03c41e8083e62200c65460401074003282c0800b4110b900e60050400701d440c00c40c041d114582100c035130b008402c01c1c1401c230380d95201d40107040b100c3c080b80c9030324040c809002030304024403640c80d086c0c0041e6850356a444041c10042e05949103218075004012042030702224064025004110b07260380944200310381e480c1d8a4801c0f0b442d80d0a184200240c8040220180511500c19030854095000352030f022010b104680901000781c00c6400f5814110071000240c0d814411f240c1c1c0080c017054060329070513030b208403031000103005a0311602e0148d00310b0391102d24501c40f444103251034000910803410407185444201891544411310702d00064801c0d07040e00124500c0840c8440112505890071b100e150b40d407803ca580d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780931645 1250 780930395 780930433
    0x20f040806160e120c060702031c0206010302010905042325050316110a080c0c0409051b03060106090302090c071a0f1005130507030e071203020c0a05090402010503090a05 75
    0xc2a0009043d06400d81c00a003028038460400382d840001070301c1804111005d02c02e980d80200c4013260107104003602c0a00d4000c502004080c403107a50750103400b16514500005101c80300507000b1510071450840e100555683d00c0240c05014041d08090902669400d14038682942e401644201250034045007a881c46a00c50020751062421201c4001502604801180c481d6001180001c59500c00003042c0c004c69082000b03040881085000c07100c5032040840858280c880c855411034007030784404c111b8242c1c01c2c2d11a0554084a405070000c02c815850220020400916444003078024003c01700403030200e24210084401e22034100d620030700f5802100c901c4e010000b5044030410120208000481d80100c14810704004540c2d009110f60080d80049150000400b0041d0280c014150380b602480c0895205021311401849040640d010060043c00d000c0e04110200700d5080c480d500440d0f02348034903560f001469810075020300e08144c4a540c0c00f0707401303883d182c01100090617503c140c07031890f202d01030616 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780932895 1250 780931645 780931681
    0x801020a080109060803160f0c24030c09051009050d0812070c020f1309120f14030603070e06060708040f05010e0f031e0309060706020c0706140904020f040806 70
    0x5941c9808680ea5600701800300c45071401101c1458200700304101d011011103812044003030140c0000c224a4816645654500079240d10600ea04031001c00041590200e18030721010180350f03401d06001e5440780c0c11005100020a0080910070000b0059140710039210360042d0002d003070301070504039103142d59041042407604000c10360034104522000007408503200307042d22a070f4658088c0c00005a074248908200e0102c0c07081c10311003180e43d51146510081004209070446840c007d442d4601d51940040c0c00400c5080c7c00e8030b030348021020401c01d102030b54400048034405c541405000d03580a80746e04000480b14032a6404c00783c064440031401054400c2510210400c46200b6200c1c00b0310702140c40148400004072008903075160300900054030001e090001000e01005440e000c0d2447c15140c03a0020302c603030700500d0007612000d501162143d48864100b04120107840c060600e443d843c5181c8070552003c0c85000b440d240500e80204100303640e0a06c00040d10f014050150995465140514a205181c0c402d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780934145 1250 780932895 780932897
    0x80a090c05280b302406070b09061608040605040c15030e07090c050720130f1401050321040b0703020309011710060c15150611011e0905070305010203010801020a 71
    0x1031100700c003007898190f00044131100d40c0b00b04148a80d070718105c115140032464202600695140c0001d4510368620000f015100c0c8901c0000b8810f0038020f01c503500d031800c0284481c00000c00c8103040104103400004840d07206500a0011405030b4462600b8511003c25a100341c64082088000803807454040d001281c54184050841d80c016640d0081c01054842409000020810400440c004a0340b003403414141e0240140e01c2d500000610300120b6843c1c51158000c000752a41c0d44000c401020003070080101310700c007414000d4002e5041000017625a40300c000104c04038400c07107109440f05400314050701c00904c100100d55464110f581406900d80d84042d050900285000504444491301035860340e004100100c104040c403820300c68165840307905e480087d564103802d2800516107222074001c1028400480500b100c0321894400094200c05603441c80d01070507414205052803d414a49042d402d29002c01c001107510065400c0aa040c100160006049940008004540b001054000381a402c00f1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780935251 1106 780934145 780934177
    0xa02030c090f0a1e210515070c08030a0518070b09040b01020709021b060108030c0303060f0d060608010e100209060708090a0e0403020c01080a090c05280b 68
    0x20282031041e0a40c81c01c8005e00c82000110044095410105003404466103281da582c1e40300c9088042c510301c090040b0700080c1c1100c0c86040860351441d00b1168090792810400600c42c00741c207080311003c1c1c02103d05d00c1605100710700024880c00f02d41c1c404812608244641041001034401d000e0381074114407030b0394008680d40c605c0e403000b0140f19440c0b1804100191512141303604004059001c1d40c041c1c0c00620200191400c040700720b0340c0c4180700b203c0765003000702c01c24000b41e005015000e02500c41454035501044008056004030075811240003165860314005407078005a10840007010b802000c00d20a01c4009010900513002c1400010107007102103407240d4203140030300000c82d0207800680c08481c5034011540c00a070f0702a04406056001c3c0030422854803113030242c032058440e580c010b88415988510350701100d82d8404828031190300c000c2145a43d86201851034019100c224400381d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 780755395 780935251 := by
  have h0 := BRFrame.cov_init 780755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780755395 ≤ n) (h2 : n < 780935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
