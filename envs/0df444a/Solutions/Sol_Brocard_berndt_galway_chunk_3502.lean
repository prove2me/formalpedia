-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:48.469978+00:00
-- url     : https://prove2.me/submissions/4b19f32f-72d0-4343-b67d-4ad1e25b8e5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 629676258 ≤ n < 629856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 629677508 1250 629676258 629676293
    0x9040609060f0b0307090c050405062208030a030b090906060d05030d1a031b0a0b130e151e03151b0f0c060a050c09010c020a091a011403060a060c 64
    0x601401201c140c5030342e0888482c4603c280d0840700c000355a4081e40054840300031041e40484d004100501240c00d000000348180c002400c00401800050908280d142c07403503074004010344d00045461036059078180903644030f55504407044035041c14102d042d59201c20340540a02e100301c0307006400208106003442982e40201200008000f051482e07205050fa1000c0c141c83c0602c02d006151105000c00302c44800790000c0480a021f06001500301100696107a0100300040f000c589090400036491001c90b02080c861248848585980344120050005034004a940012841403110521b05191800034104400c500140054059915500304000c40d110744290141e1180100084410303c00300c0c503400a101c10140301c011103420356074080f01002160000e8540c118407520030840002c0c03540c8030311891900c517030004200510f03240c0d803125100100c407030503010303095449542e4103041025a0032141c1e100c4a410300748403030f901d98900100000d420712041e008181c28400350780114414405034900c1d81c0403812 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 629678758 1250 629677508 629677511
    0x30a0302070311010624120216140f1f0b030303070c2003070501080a0f0c0f0f02030403020f0405101802070611090102070306021c02040308090a1e03020904060906 72
    0x10100100501a60201d40d080c2e001c100b05140d001030314101441910b003254851140d000201c9a0701001c441c3e42c000c52142c84003004140001a05506103a20081404010a07043c0040107030b00752a00c1d50f4600404030340179505800522850340705070404140c160800e480b0f100d41841030700304104c40c0c0004081c41d01c00290188404000c00500302c2e048144046c6240c05402000d4101d07000c2440311030b0b000d4018420701d03095048000b0410403540605500754000d01c20f44808110890a000e054044a1048c003031440002c1d40ca858049507540c012111841c40017142c80a0741c0b03003508640124543e240401d10306800345580b24000303810001c422340d680d4042c04000100351031302c0c003000c03500d0006504501000d031007030703880d103003040e0702120b004001ca034003969068003c1d0064074a540ca520000b5000240084050204800c4510501c4041c3c0700800141d80300ba111103840790000300a0142801c0750750820a0b2043c2c140031013103100789002d02c9a4086aa04035004038040d03445203040b1003d000c1c6002c0040c0402d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 629680008 1250 629678758 629678767
    0xc0905040b06061b1203220c060507032015070e0a0b090a03120903050c01030506090a090c0f0308120a0203040305120703140f06010806030105070f0c080712020607080705091e011103 80
    0x7105c00000845c000c1c4521040181a2488980c44640c40400b0040c000c01a0446c507004111035170041c2c020b441068040e007459040708040c0720300c24828144c00c0c40710000740c0d0000441031440c0030f01c03480300b40d41003038003898560451000880491142d0446004400c1c08040100342044195500d124503000340d50300c5401070714410083c0d84040c00c2c2e00180d0000b207440e0701482d203811082d948203200f440c2c41400c004080c0c0354980c8460101c00c00608103200b06448400040c20042034a50035250010019442081c08039555000849401007402c005869031003000d00400a01000c69401400d583d034041d4081c0c000d0280307032240781064004000140b9101c8000d02d80d4410014840c0010b0603d83c4210802c4c0c0b1070781800c0e0380e80b03810103003200c104032020f0010134442039078150402d00c1402e42e00c205600c00c54166103031100d1074407110303810b074404054070b00180e00200030480142d5001400a4021002c0e007405814904203400041071070303007031000100c0fa20038018001e80d0960712640902005250110a41e6540d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 629681258 1250 629680008 629680033
    0x6030606130b0c0f0604030c0b34081e071805030109030c0203010506040510170705060d2c06010303030b01020321062e05070212070608040c0905040b06061b 69
    0x29041200c07250064044c3c2912610844000316240780729035810341d1120300341c03150b940d10110a90383c0030345a190030042c0034042c0100101908400d14188001c2c201060448091410060040c00010444464040100e191030400c1c1a55003440350030031554202001e81400724050402d203980e0759070141d9403541c2004040c00c01e15400c800c0e01e03450306e80290002d0045a64440910003a1603007543c0500800042034810800c48106428130000c3d0741c00c82064540e1103964000051158102182003511580d90381d9802803400156809a0011640300c0c002100d0240c1022016803150014803015051540b108140c80c440ea109104076a0100e19200c11407801041c4206c10707403600350003100d82a0003104485c3d0780345240d00b4040d400350310641d6000d50000c180070080e0400c4800da0800d03042240c00004000e4111100c283c01d22548020304850703501c02e012450282000c030846036440e03011006907803400e030501010401031515698030000688900790f860000701c00303d581d180d890150f221502c1c040d02c00701e0b026 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 629682508 1250 629681258 629681279
    0xc010f170c031006030e0601061b0b100e090a122303070207090c14160302070308030a050a05010e1303031a0d03050c07050604120615090e010507080f01080c0603060613 74
    0x40d8500c0d103c02d18880f51503900650490703002c071121b51711907070000004106041c40b820180c6050303408082076406043c6a5030320310b01916401d540360b01c1d00e055044010700502c3e8004104a61200c0700790010804402561101d04c01001861182c1c02044a20714411212a000b06880900c1c11041000c1907508d05d00005c00035100c001c9030181e042614100110310514502c0b4000380d540b10107203911164988001043e00300800c0455234003c13400d50003606000000f00300303d01d000c0c40c42400544000319451a21211f200202c6105030840d4020729402005e200100610303604910406034982400604100a54400b02d54180080e00b49944016002d068900301680320340039185c01d401400c200c601c000e442c0e07420002180241d016031554220000141c901207245c0d0f4010910b418a040101500c0513100c613803000903100491143c60031a03465405002c880760303003c0d030207540c4040020010140c55040c00f0000303071944c0c99441014407944021022413160b075115821a01100243d1451408842d0759566012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 629683758 1250 629682508 629682511
    0x61b030309010606081902030a240816030b0c0d1d0a060e0f0312070e150712030905060106140903160f17190503070525080106080c010f170c03 63
    0x311942404000503000b0302481556000360920001c1b100c120300450035910003504028128806192500312244107a40c40a0600341401503040e60344031403a040c2444e192030805840b86a40c0c880c0382c0624200082007806031030347d030401e81c0400c017980c1e1058001240f801808000340c002e14000880d005010302c0500004421018500c11b1105100d414400e50700c1e00c1e1201d400c26020100c90708104001a07280c4441c00c105648040300b0f04040480070700000c04511000c1440111010810380042e100c0240a00712000d0174070b01d01d052600b0300600c01d441e0f6400d03071150f8040c40ba0300305000310918200b8101d2010170954004000c09001c80300130428114005200a0f61403007014800d100101021882c010305241804a070800380700149001c0d861150689030707404a041055481d40030901c800000200b00340600e1100003414814041c01d003501c040b5640d001308842e8400c400680c5801410042c0c4940860078110003002420005504142810199030390103403110721160340c4140ca0308021070542c800010b035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 629685008 1250 629683758 629683771
    0x28050d1104050a08030c060a0b031609050f0603010b0d060c05070219031e0503160c0503010c0818010b1e0402070c0303030c020d031a28080102030612150f0402061b0303 74
    0x207186156480003413035201d22425410103c2a0405000241040500d80050b01a10b030043c08541c0011009050250000e080703401542000d82c942060080c1400c4020400b03400c002c08400030085070754208000307204500709607001000c5685400203115010b010700240c50b101c54020300340c122080440111240c2c0c864040c00f0440310825400205ca0485081c124054071581c1d010008520380400c1001c501030b8100508c2088513400d0040c14049480c0e04c081c09034500b5180e070b980320b032040d030304201c011440001050411a1196803506000c07003415641c4045008520500501041410605401040103440342280180c00c401100b4000400c143d030641c003100001c0c4040c0e0a0ba804590944c0c41241070700d80e84081c5805400000c241800503181080688450028038403020f414114442100901900030381e00521080e58040f04010b41c43c200342c3c0c01c0300e04d48440e1b1000b4040303c11008040c00000c403805408843c0d51030295000074210341f83d550485082604c010360300101c81c82c14032510b681d698802c4a86 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 629686258 1250 629685008 629685019
    0xc0503130c230414060604091a12060f060609030a0618120c110108040c0306050a1b02160f0608011e1d0103031709070b090118240528050d110405 64
    0x500c0c01a03200c2c004e100c2c5c0101c0c8010f000b40d103001e14003c2e413000039007405018040d2a81045402d00c480c1d5a41074190381046a010000d0140b13071904458000c1c894078014801400340f003080013800358666003c95850300302c5a20010000742c0500e04031000c40ca4959460005080d02d01c0c3c407400d898000c7e00a4044030443e4420118036000f40110f81c011039403004203a400500520181006000088864001c960f00000c910b40008542d0002910340c1800e4030448400340c007503040301403030301048012440740401800302c2042a1508510b00300d002410074105203d00aa006401c0018000016500040800801402810780f022008400c12900000802c0c4400c4020407892120b503002c10021785202481102100c0241c4081d41ca4201e4202c5554000400c01b810003481c0468002c03501384562550300507142400030024005040928a555400100900c400b40074007800001184070b490301c3c0c442040310500700b034031130360240f0101d041d901c50140101070b00d007041c148031040d5802e07501c8002900444800b101c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 629687508 1250 629686258 629686271
    0x1103090a0b0108010c020d21090804090c0302070c030609030c1b0923010b0a1704060903023706060b0307020d0e0f01050f1303020604060c0b0a0c0503130c2304 70
    0xc10b5801c80e07a1411707a100c05a0451421412401d014541c1c030b01903603140701c5605294003890004001110042c072000c0b42c10040104081c0140a100d100d0100c16402d0b6080441ca407103403540b1003500000c0c1d944002094240c56403200c03400c1511448010000b80e602000c0c4038022480da42601c8030380c403401d010340c01c0064070f40001c041000000041e0051030000000307203040c080e4200a90a0f4059210114030b40a20400f0961040d8003180c03071141c80d105a0041000080c0d01180345002402d2003243d5407031002e9954901141a80d000507c2c801480c0c1e00e04510440c0001c20061601c03402030b002c290f02003103800701c01200b0003400580104152290030180e0b82e484a031400d40030104031070424240e0700700b40020740030f00010000760301c581c0003040fa290380415644182a40c0f5030025100c0da2185c0c005a00081d01000c1c0b0004004003490300540003022170409004c01599054001c003607005c000e144000020803040c00c4418403100c245010080e2004005e055910b505000540000181040015000d1442c00f403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 629688758 1250 629687508 629687519
    0x2090703050108120702011e020c030a060f06050910290c0604020a0812160f0f1203060e040803160e042c01020a02030922050106031d1f0c031103090a0b01 68
    0x1401c8072940356050310345403064072002300080c003008100400780042d48250300095486503401c110303940400c1e00c5040081034000c0704002c80c100740e03240da51145000c0d00112050043c1d141603511250286c81c90185000420a52940380505000030b4540f20002040e00262030410f2b01d6010905600ca28020794104801d207a031068803607a0341544565200d459001401900107880590698202c5640251154240340f0a0342e00c92021040c55000225441c00032690303104025074040c01040001c00c1003a0a0030304601c0d00307803900e0940c4d2000500f004021085041081034441c0910031381425424050407c111800010001c03811511100000c0d800c1c1d0794080c040c22a0308030050080b9940c0d84050303400b6500304282d48041c001c1d000810170340c3d40b526507201c030f10410012407107228160003441690360110300301c032980100003c0c0c41183c104d620032940064a01786082c102038501c040404c1100302c0005000c0721280d00840040c1b41510005800800c00024421044d00000d40101140d00548841c211a607850 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 629690008 1250 629688758 629688793
    0x510050f030d0206071b05060c22030b1302010c050d02070602011a0d03201b18090601050f06040905010312020c2211091f031a0a0311030a02090703050108 68
    0x2280030b90010b0f401500013900c480c0c403d81024038216503102e071200704100169182814210111780710780041d5400303d101c601064060700d0403146a42d50081c019405130840d21085510000141010182403442c2140000c40e446890030b81e11a03a0400b09030740b80c840007014000e46031441403164400560030041403080144020a5442032030900074094500f07241566030a40b94107071092000c440000806150700d8040c0303402d000444691070700344c5046000d018810704204858208600480400700108200300802c1030008040e4103580040310403004a1a07118009805031203250040440503062200001c108111004080f110203416000c0c2c030904440c80c418090030700705020080f890500390108440f018449070340004614440340b05458640f880c0500466001c50035035001c600480c4c2001e04503403841d0361503c6800c24100c1c10103061405400400006065104d8500010341f544500540001c3d043e50100711213002194003030060072807464403450140007071100b48551411406101002e83c402441c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 629691258 1250 629690008 629690023
    0xd08180604020f040e030703020d08010e0103051515030304060509090609040b0a0203040312110d0e01050105031f060e180c0109120f0303091707050c030609120d0f0510050f03 77
    0x52004008581d119001c011001c5103482160360426a01c1044c5440020140b00501c50240a46c0041144005010b001041000142c0c8000348140d80013006000081300410300900c608482c8040da5015140c14030012004694400d0142d80340c0f000080026000b900700c4060400c401d4101d41c03045440e55048240305503040115001040d0011040004194006503030281d50410300918003182c139500b019409070b0488511a0210760014001f1440445440e02c3c2d01131014100e6040d4000c0c000c5526010100b60b90b182044411350741e0114682510030500c001d45d1181b0b0003445010030107800c1d8100014013010f43c20325001d101a82c1d00800392003492039401058260215001900d10190200d86502c0740440100c41e40b40440400d5110303052803001c036120703d4400d0902c0380014196592690030349401132420445281881c02500305a081003020000410070040701c61026250b1942c039407940c0407990080c403005e022b84040707074508001c0c402c403420340d5030000c001d031142617400b408c00000420405581305e98 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 629692508 1250 629691258 629691301
    0xe040e030a120608010501030f0b070228020112020a080412210f1409031b011e0903180303020a02010f36051c050d0c03051806040b0c0d08 61
    0x100300ea01001486400b400c10001a1424001000340e2104403460035500300781d1060340c2c0c1c100c0b1087c9000c01d1002040d001034000750540010440c41e030088042036410302984120240e03040341420b0700e50030759010302072410f403c2d80d62174000c66032000c81305c0740038000350000d03503054954508100310b06c0301e11409000c060800503102d26510b401001c00414410182c1650280341078050b441d4492240c0b01300104000d9400745020101171a210262820710701c0143c0ba480d080100a170317040442c040c118204030440b529103600c8001004c101061941001d8424410a20305403d940c4c03503000300042850380c08581e00c41d40c0c51003660342c0007820781d941f601140c10440c01d115603101003854036221504030940b07248440b40c0000d40420940700d550b4680000301e19028140040c030032002c401c042d00d01040418085c0002c2d910550924000190b5640c800800900a100c682800140403000e40103103a600e400071b035002052070400d02555291100b42c95138541020700b200c080401d80c10008030f07102500440b401a40d447e03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 629693758 1250 629692508 629692513
    0x90d0f02120904020706180308060111030a1e020c090f101a03060d023105070302120f040507030f05010f11040515090409080f04080606090606042310030b010e040e 72
    0x800c02e0301080000c2d404410104c8055981c1c1184e65152440c980e03404c040f840c0a92981400c502c2c0c003400140c0b03240da618884d449181c00130400e050450f0303002404020300350b46050001850328070055041e4034003004007111540c4540030900b04061707199405841f40c03140140a010b0181c603a6103030b009580c0d00300e4000c13640c61948424000030f011403c2010401540c0ea000420400f0111038030740b001007107441b110001d001d10703a07480c0d440005407002c00c1c06401d40200103072400310301e080c00251410f21801c401810020800c40000049018064100180005550001714540c207000151506030300030035401c4444500700c0d08207400d0004a85403401514222480500341c111402e0251043e400c0b5540300c1c10405030f015640b0401d00002c18140e101800ca1124031001643c0c1c1c95081c805c4091425000800300c1d807042100c0d50401c0b420b038844071b080e070701150100651101d03555140c140004220f44a105816001516440b0800c019607054216000c0c200c02a298600c3c8001c400c4140070542c0c032000710410f03666 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 629695008 1250 629693758 629693767
    0xd092004050601170424020c070f0f0512030c0d0518040519020f12040c0f0b040605040b03090a0b04060605151306110715030504110906090f060d060203090d0f0212 72
    0x20321450804c3d41c000d119004510751641c8600181c4032035065071101042d02c9502017809080001b08100e03203005080258582c1162a1818142c284140380d2409681d000b00c104c3c043c0c1c0c1c82d442c44200705856010101500303075164880320020051482c0c00500c4031f000e01c00c400700c10724040390400d44240e41c01031000c240000c0400003412050806503101038160043c0001c20000c0121103100300c0c04203402103100f0340625200c10b1800180410074402c0713401c41d500d078000c2000b04101b41c0f5040011203044410b568003961300c950314110142d04042c0c10400117003031559090304000412690364000c0040d80d008075030150480013044900034050003040b040c1c1c058010320080600145008a210503003c140d10340490340700b15224032005a0f5804a4454180070070740394000d20040000d68402d4900b189401d44001e011071400e54009010510301814051042c071a003004140c2c5a1030b482106003055401c00029541c070708000c0c40d001d03038403541110340a0009a00e015103004192003c60148400646c0140c0d107800c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 629696258 1250 629695008 629695037
    0x1303060b0f091618030c080a0303140c0a03230411040507050a170402030115090207060c0e0f1212070503071502030f070305060d020406330903060506060d092004050601 74
    0x25141c00d0320820840b140100000000e44c55070000310107014207c0142c418540d1a180c094183c5203613200c000d045214510400500c2540403050324408030b4280ba0100d041c0e82c070001c0b5110320a10407002c12090f41034000401041c010f5241a20142c3d43d42680e0400265039401c01c115100d020308a54900083d28880c1c10006001d0740250540c2c0250008000160403040d00034981d03242e00d520f6025031141c54001c030700310060007550321a0044010fa5424408120f014510004002ea518031100c42c0c82900e04107460070280c50200403403040e02242008665541c00c050900303660300d40080c801110354035107100545040b03d80354025240900601403003507505456040055003c0c04008100d150090140070106015076160b004400c01401c04540d0518000345c03000c0d41034840c3c080840d80035480e01c40080d91044043e41701c00360400b1a030304004006015220400010310f41d10a200708140305900b411164401c0c007940a0009039450719950034920310007420301c1400141c3c3e00440e03c2e540880c0ca203000007600c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 629697508 1250 629696258 629696267
    0x1f09021b0f0708071e080d0f02190210050a0908060106092102060702100e04150608160906030e071e061b020d0b0402120f0c010e0402190c081303060b0f0916 69
    0x10985100c5c00200390b070342c40b10031117850100207140d2100001c0c104000004100c0c0c0501240c4120b05204801c444442002d801280700c020302c80319070004204002900c003824910a03070781e42c0068541b41054504550352050028002340f4240909100c1c41c2d442c1d01ca980c03400441100800304030758054621400d051007034082050a140008410003400810f81591109131b49c0d0380f05001c40340c0f10380019184403d080c17a8005005100c010000b80030f12070060060025039030041c0300042211100c0c9400f1582c2c1c000507001c58205007071588403c04207221024044060540000c2400544042c0c0d135030940b0316a42a00b00d5108040004c50285d082000501000c011950038030b00140c0c4070380007400404826000c00703055403a1400c44200307200d4542000729119465a484054000100d0044030203604141c10080003039007440c4820900018824240c603030f5403c0000c40e40503900da034440481c2d4018a1566801c190b0081c02441d1816032090480c519455428607080103414003842d5018041061200c48500544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 629698758 1250 629697508 629697539
    0x606110a060c090806012601092f09010f08010b010203040b040501051e03090c090a0b011e2f0118111306080a0c1a0a02061f09021b0f070807 62
    0x81040940f54010a5414080009034028000c00d1103102201e50001d110035950601210220180e0b410108440080b030301c0c00307507406082c045007182076070424202c00761540302111071241c940d048a18480006020030354460340c00102c4110000a200090010004a0300c0384190301440c42032001c1030200340001e52141001d803944070a108000015108a4001d01003541c00c101c504140710b0b8401010304516050050526030481d801c0001800440180070010345085034144140c1c3c2901d8450351020b0f011845027038045500c050f01c20644c82c402c1c0000307822803850b40c0001440070096090504403c0122130490319a40c0b000d8020980b180110040c0c810416031f81050310364ad10006480b00f0011400000a004605200340300310446840f1710b18028407910000200d18001074044030074002d25603003d8010907140d038040a80030301c03c1104599104510304d07803055600003601151001c610341c070003040d088003018404089542100e43c49a81f0003622950f40e845405000c3c2e190704464010441c5002e54406032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 629700008 1250 629698758 629698781
    0x6060f1a0c030f0d02071203020f12090106051f02070b0702280812120a18080d14040c1d070905010c02150a02070321050702120102220503010606110a06 67
    0x143e15203076002084051640140300c00c0c3e402c06500082200030020070420400040045040640c28903a031604c0307990840c041d4019942d8043c0745000000c1140d4001c0d44400040c180c01040c2c040b06414054801c44013002616080300540f00f480408580c9085042c25102c40c194000d24544e1800e141084120959100d0044403481d41d03807a400c04100600d0078055541400c5c406405991242c201443c02c14103980c003e0000000186412000040c402d0012502c042c415005015140c0c0c450007040c0b568000c2041c081121410b0b003074007050204109059100d40f0842e00d5035250000390301e1051341034001142054a0340004034030100000c0101d0b50007540e0003603140340024a0f003a0600d50302a031410459001c4c819100c010b80204c6802d01c200000320310714802e03030342034030314a5100326103a028060454483c040d0b010f1703c50414600c1c440b071251000d40444002034a03084c500c2014035582c200ac2a0b024080b4000c03d0b10950a0a20100d00103106425502080764428028080f400960300c8210041003a103400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 629701258 1250 629700008 629700013
    0x30d050d150b0d0f0905100203061518010e03010218040507020c09040c061b17031b0c01091e1e0201090b0313030e0405060906011d150706060f1a0c 65
    0xd0000c16003040515000a0030600d8000f0759980043c0c52a004071542d0301e90528115203040c04400205500041035040415601001030faa07071905c40003e500c8480640c6291584500003500c200104d00b548840d20b4020b03820788501005d070324514200f60070f0740111860b01c0c0d0a00c03c0e00c04910b20902e069040940c00c0300c5940103480d40e07640e051001c100c1c41c0074101d909444442e2010000c200c2c150384030341114900845441c0548110301c155a4400c1e001041c0364982c0e0201d01c010000c40e08a89942900d28580030b0110400c50b512054407a405010701b00c0c801003556405441c6000884030010340340402c0d403203580041511021a04082d100b113000107200383c141c2c10400a281d021440c4d4003040015802901d60700c0896010240074540140031105142c20640aa42018140291034880701140c80e08540c007420f01050030511080c02c0c5040a006c1700780f00c1e520440c004083c8500c551000010406640509001d01100da10b54480c0e034200505d510882000e14080302c2400d00c29600340c405424294104403e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 629702508 1250 629701258 629701271
    0x815010b0d0b040b060f0310082410120b1f1203050f121e0c1206040513050118200d140c03070303090503010f05060105040603021803012315030d050d 66
    0x10441540020740c06d40c0e0000b40000138030400d00011410340340240710701d9004040100c080074010b480514000d041101c1050020081540d00000d458413002400310010300710403002881c28a2440e050050b00c11003031180c41000489002e0606808003400d480741814000010310050350200ca4984c0821a030f1420180103018040765104c6000d5000d000303055419200003042c1094100240918000c0c000011114040000c0440404180f028580c440d00c110380008103550f80418211900c90500c034018500d501c0e02e5061300809411003074217031001d03028158103250203016009034080110002c0156900001110714040060204021640d40300006026611907074041004a403a001480e0001c0b4040360020200b40454102442102d4010503044803d001c14242070f000070b00035108038044c00082540016072000c51078200b9260310b0340070202800802c201a04000090001401e524025440301d503104c0208150760103601440068040040180c480d02004000646880e405031f00e00425550b203820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 629703758 1250 629702508 629702531
    0x50c010e0d06091a0f130201030515040e011a0105092404080a060605040507051603081b12060f030a0c0b30070207081501051509120102040815010b0d0b04 68
    0x900c1c1000b038810f0402c0c00d1802d80c4181900042113000b40248085000c0108100307201111001810f4000e8080c200021540c548030b02c0c4094410581c0e10b0180c100e424156030800910741580135040401000e841800d5014000c40110b449101d81c1143c01d50103d05074291446081500302c14004c8002c02c00340031880c15907115881070401c3c10f135880c01c0d224281e80d131030104620708187c0102c5600449501e041840c10225418800b904488840b01400300402c000015117411494401042510a02080c00e5101d44400c10550041103048071180d00503040000c0d2801c0500b0000f5000313482d150310064601c03a481c1008008a210b03005103040d05000c104107001e001000801121000d040c200c28030070203501e8500098042d15017416540005640d51114000d114400300130404141580ca080b00c082c801102c4405046c8014080c1300c00e05507011240391500d0700e80b480e0540c0100119007825003602c4282c0c82c0102138041400092203103140111080002020404c02c2e54000f120020f00204001414680070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 629705008 1250 629703758 629703761
    0x10215100f06050903190f030806041e091a09070e060a0902040602210901050d0207110a120312272d1709010e3706081003050c010e0d06 60
    0xd901880128070006503601c0d0341c5c1030500005110b0603401c1a89040490f0f655540b1402c001d0204002e010011854082a040e81e25500400c0e16100b0200300700900b00850282c0c40020154418115000c410400b09102510344040d0818440c0840001500c0800e1501307030006e200f00d9008244a0703004509220200301c850b801d00c003030400350000758003c0540710010b125209010841d0080c40d20104000e0160305040d03a40941180d0a050040e2070160b1070f1203240c5401d440c4e02050310f00480e03000a0070117000c603030360a40b030200e82c1d2424040e56030740700d0b160b5402c46403200300d801d11804050408520a00105064040300e00c43c0c020b03a1181d05c1d0b82070141405a042c4a0280c82701012814680f0741c0030a036030600414084442d40107224601c400c1c17402c0b04090028103d9603588050500034a07800d070089401e110f480c40c4c21901580c1c0c081c20001c0400a60710044503112860058001040b0341c1c001003038440e02190321440580c1e5004004000500307100d00150359689017125000da0100024103044001a000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 629706258 1250 629705008 629705039
    0x103030c15090303140a1a010e150c06061c0b0411030a05060705190e030c0d08070c0306022a0604150f0905160501170610031409070509060f01021510 66
    0x281e5000a030340001d40c1c000540410018281071100c501f418007200060b1000c42d502c0400034002d0030500e84050004000c149040c0303120644c0e015548000c103800c0c440f01004030300ea0348507440c00c030303010b03101c4c01d09a0b904200003580512028001d4400000050300081001c0e80c45440c020000b02240e0072600c10f540c815240c8802110140d0000304081224070f0b1140000c0e9504a001c5120b0512040e01c80107180400e50b1402428100c0e403040400c58407c50601c1a1a41220611500040c040024640301d04282000c1d60242a00c940b4011440004601d11754030310700701100002420014080035141c0d611110154076054070b100500075036460320b205540c0e41611510081c40e00c01e2014111108581c0c02641819505a00050500000141d5a105041541000c3c0d078001c000b103403a91078149880000701c00910f050221404014521130034064001c43c001404011582c040798554119610355050001c84220251400e016038880c021000710307030000840847c1e112140060901e40c041e9101d040c408000d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 629707508 1250 629706258 629706263
    0x170406020a0c060c030e1002040806061c0506040f030905040216030c0201021c17010605040b0304080c0c090708040c05060c10090f12081806150f010201060b040902090109080a0b0103030c1509 84
    0x130744501c0c844000401f844000c0c0082c840340000c50802d4500581c2c142c8910b03008144520441c1d0000a00d00201120400e40b800d070758121044403c02c0c945490880c1c280600c40c5015008664400700004242c581402202c1955030f0071900394504900c5641c098500420b6504201d0550050300d100401350480300c184035070742d10151756072601c00900f06424140180350681000c010000200000d0011010202c21241c01a61029406030b42c0c004061101d4104881600c829500500710018040c203980d1080c4241d00403805440905030300e541d12020000d1600c6802003001c1940c014000c04c0707922040340c0d07200343c03201405441c41e03000c46450356484c9a08003402c00c407280042641c3c4c5090018401442503017600b20040c02d0014020342c1040091817440f83c00445456210f07509035580c1c1d0751139074803e40192004280c82112982c0356500c0e00946c001035007044a5450024000c07102c005101c070710011f80302c2e034440d400070b030f1582c4940d09548040300d03006085003082e00d040c26900310030f00341c5330b02c03d1080742695130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 629708758 1250 629707508 629707511
    0x303061a040317030105010f110a060c0302090103150e01170c060c010509070e040506190e10061a21070207081902100c0210030b220912170406020a0c060c03 69
    0x600710f02d0310f038010b1a454003010b04100401d00060200da41c101d8050b9890840b9400c2a160300248081a1494180c1601d8010580c82c00c00c00710440607501900038000d500f05c262007c0c0001032500058403609409442080910005035004024050200d00c41650b981c0040e01603440760001500031481c0780c0e1000e500e44d0341980d5284104141914148811406404080a00e4240d410181c03903141e41c8035009480e20310740c1e60700d0700d0140c13203100103990104030000d0f100ca0035240e0b1150303180c0202d001401030384a001d040900200c0a400d00940590407920742c9402101100010000a1043e10000700c0c010f00e054117603c600c01000c80c1c00402080708000c1d0003c00d00300f03000034a0046c410302048505d000150020b20024091560060b40c444580a07a00c2c0401e03c0c00198400b00b00d07000901d8403070b0128961200c0303c1480d00e0091800101e4118002031130050a4842600d01101e03800c5070b2807100a00041c2e51111010042000903200390018400c550091420854010464403501c003103500d07070700308000840d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 629710008 1250 629708758 629708767
    0x30c120c03060801390207031118070215104b03061508030306040504020f180406050f040c0909061103090d020c01050f0403110a0b040e010f2c040303061a 68
    0x28204400c8459a841001c54417042c000520185d0b462816001c0209000300d103c803035004030b0311442c80c005c14000268190004509007110302a484000c0c1000700201c41d80030a0010f00024082e6034500221503810700601d00b01083c030328080b505e60b100c25030494400c03884400c2c01111228100b0001c1080c003407650620b042585145454012100c0c0c42024000c103c403100303000c103c850301c04000d5a074030140994003c81c1959a62000030080340b05510711035441800303c0b10b465840c40406e00d103540715a1203100d0802068807840c1810140c40d03002ca800410002e1280ba051120540a400c8035040c54407a80c004900401d54030501401d50300220f40c071490540c480c036500c0403403e070304004140e0841000e0070042e1400c11104d08500c85840b5601018081d5104e90240f0807458441045000042070512061606c55464650390494070f8001e200322030a1809246000c2566550301210084121080428004140307a46859115481d4010300039818180e8911001810004000560b180d0300c0400f07040941d207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 629711258 1250 629710008 629710061
    0x1e0f0406030b010905062d0c030d0510030b0103140f0307060903180302062203060c02010903020d0905100311130905070f050f03060607020d06141006030c120c03060801 74
    0x111000c202d1440d0402140440400258550404503902038480040b8400036000612101c01c420b9400000d0300c0d91100000b942c2c11352108048081c3c8032046041c01c061046481c3d080e4071210813651404054020b0318281e00410000e41d081900f1001d4005540503600e0310820103034801d0558004480940d03005444005c09020141c1c440d0035408120380c44036003e103180c0c1c1580c02084150145005410075050580159103144569840c00c50055510030f20500c0100e50b08400203020308000f100c00c5002d8030524035140d030003600800da510160707040644200052015844100d01400c1c0c4485000714108003003000d000080ca1902e0994068508004007041e10305001100405248130000c8841c208032040c031141510000107401c403504404119a01034a4900d00e00000321003801054004050030314000260781c04481065000c3d01c6140c04101203070304d4a94231003059060303404d03080c0100c0004000700500b121040d2203500448520800d45400904140c80d600c1c0705003184c0d1a034000c03054010351038861f44034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 629712508 1250 629711258 629711261
    0x90212220605091f1803050a0905030304030609020301060e070509040c0314070f140a020a0b093d0e1908040906380409051b03130b0702030901020d051e0f040603 71
    0x10201d84031007041105105c0b0284060020400c00ca005040180010f010900b13140b04800c003101500004003580d5456a40c1e1034040000d060340b681c100d01950030300f40c0003d1091034040c0746500c207400703070745509252103540070030031005000700d4402000b490743d5814090241d81c0c01c10500e43c41038000f038813280480150105e02a042d040c07420000c0b48144030421980c910b4560224000000950121840d005603c54188441c2031144e080000c2891142403c000407000d001c00500d102e940160500720300191034203941d4001610284040740095a106a0b01c181ea054018040c610405004090003070500742c0740c0518009035411640300c24981d14aa60148071612400031445446c01084558480074143e03060144020740660311948140300d5070b900c0046d0200601e2038a4810400d4001600390703491030911800c4048803d0792106550000c1e002000420903030000040300e00c1e50718160010040721a401000712070640c0500f10800c00c12440703110560b507188404010300b803440e215804664030340b810050000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 629713758 1250 629712508 629712553
    0x41506080606010504050603040c170a03090e06010c110f060c150606030f0103030f050d1103090105180c100e0409061e06032315070305070909021222060509 69
    0x354541085050180582c3c00c0022130f0204c0e40107954840d12070341c550405038003502c800c6e8490f422485021103641c00040c1c0c0894007403c0e01e131298480c1d905180d254121b00045600440b491070105240465180108001c4840c005400500400f40c5016042103408195280c210107407c1c8420303031104030f18020224200c60001c0c0c0c0200280d030200c1c20742c9019140348851100612014003800b6a0355500c00c50079200d0310840d08240d024040074800c4210001044d5040e80c0111000540b652030100800e03020200070514175502e248400040c010420000204003605619201c01d0091000c40800421207807668040c010303446000d2807000944141c032100c03000e46d140c40d14107400c00881c42c1003414800500c02c400040c0c00d1041d44034040c4035134401e1040e558076003a0640c0003c0c5039100340b0320401541c0c1e50305410040c8a0405556411000f5a4496141c42640146100404015030f0f85000848800210b00d404000310f92141c0d19452651490300d40030700f00c0b082a144100c0c26004a01d84094000c1d1085e00003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 629715008 1250 629713758 629713769
    0x180a1a100e04020f2106010b040e010504020313060b0402090a0b0a020f0d05030f04020d0605040b060406080a0c0510051b0715050423121b040e06070203030c0d1103041506 75
    0x1c051070194002024000ba00c03a04520421700e604850341c880035412541030203001c0810480da21075031507080184117600288200c0c2841c403042c1d000841c8500305402500e000b1050b08070a00c1c001d01031303980d900003e0035181d4005608141d0a01400e0566510008054010044190ba45a49005844000b4100070691890741859400380070710207003c40c0e01074222580300030040d5484c92292110300c00908500c0040802500407402c143c01d1009004548130a01e02914003101d0811815641d003654649841d071109010b008905496020030450500003084a4101560b152a5140203e042c6840c0701a0311034100c495201e82c044841407208030740e500b2404e0703504441414864102407424204690003d0301d85103030083d4624100881d0030b80d03102c41c254814001c808005031001c841070b82800e40c1040d107485012900ca54205011110502e00c04201d05d8000c040039400346107107039a0700040c461640d004c0b001c8001600d1740c46801c4045124041d01650146129041282c095018141800240c62803904007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 629716258 1250 629715008 629715029
    0x1205010507020114010915090504030e1e030a08031026010b0f0a0b0c0f0f2535060403030504032709111905130603020909180a1a10 58
    0x396032040f1341e503e94141c1183c030150070120f14580b42e4518a10411101c3e0321142c18903050909000815400680382d01c540c0b44103455110261030684c00290902c80152849501034005124120114040c84015a4420070b56801c001d00195511103840c0301c040903440c507045901c49414410026007080c0101095100c00300c1f04110010718140005410013690320980582240000d150660356105100c00c60900601100351201d2004800303000f6210b4043c0c180799192080c031003e11441c01b011558501d001d4400010100401c5180c40c007091051515020341c000c4502d0000b07904100ea07031010410b1030701c03841c07096501007a10b085c2407402a1950011400524000da040000380b040300c03500c1040301c2c003140d10301c80d4041015214000140350500c034040040c034030080b00b83c004000c09038009000700f40e400303070008813031000c90795641084040340281390300a584001c90030701041c4045807454641c0703d958294800d80e00c1540030790707540c00d09070581c03d665001c06411541c1003128104000540754020440280b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 629717508 1250 629716258 629716271
    0x506041a06010512070320030712050c0409050408040801050405070609060c0b04080306011b080a17010e010506070804080313050a08120301090504080c060a09110d0320011512050105070201 83
    0x600a800b400c050210f0f1110300da4000350b2101d201b500020b8002401c1091f0f01050400e1200e410202d9000721031800100f56641c1c8a044800f0b40d03803007003030303c5080859003840c00c15050070b0140d8040c0078041c0044d94290070500c400308929100f03100e03d900a40c810002071519914112002c0c02210f060707407200b0184415022410f000c50403081c891540a40c5c4158425540d58904005036017003541d40d032102031040755841c0c94804016a2000600e003020041d2190300c0104c0748800c070042c0c0b0303038424001c41038510f054400400860a000000c2c0040520550304607041c40c0d200c007036042c51900001c0141d2654003125004010a0402d080034401400300b24000d0480202c0145580c061440b040c4902c0d0340b41503450000034244805c00d02a603040104407029110030741480003c1c10302402608100ba108114999181805850103400340711045a0580343c50500840035004280e2418030251042e456548407641c901c03030403810341a40710191a12000340c00001d1124200103086400c02003001c400c0d68034010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 629718758 1250 629717508 629717521
    0x10c030c0e0306190f11040801050a0501080d0f0309080d05061f05040b070f06020408030d1b0c0b090f0d020717030301080c2205180105070806011d15070506041a 71
    0x1e0200d6008443d0144000c0c50020350900700001c3c031505c2d04c2c10803094074000c000700601d41004005c3c0304540011000b032003991190401c1d00300f00e0300288142d281c240d0014403507000c4a8010032880d11107001c1800c0c0003a5404058862422941c07240c8aa85100c41e0b498080081902e44526080078841c1c0c0d406203001d903240c0c40c08000d01030344240d0003107076480c407004241102000245940002404ea026900390340b82c0c0e54030000c0b00d6598028a21141c1100d081000003a01030790405c0b50b858a2807681d5440f92081da00c01d8a07000556030b4041e04403c114000e20f1403114551204200c40d0100303101e00d90007450303284d141040180c290202c400e02002581c10800c0104080600010703071894003401101c001289904856403603101401030349401807080c0c204020040c02c61800380282d11209600c0e8008d0120f03694400342200e140000325601404119064a162000c00e080c140200c90362802400c81094a0002141414640c1044230120358507401700c4104403c0004400c800c058854450914080c10709290 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629720008 1250 629718758 629718763
    0xa090803060f030c0a080c030d030b060406030c052a0c01020106050f01081008010e06060a05040e0a060b030309060d0b04060e010303020a02090a0b060d1a0307050609060f07050d02010c030c0e03 85
    0xa4240da214001074600b00101e0340d001e00c281240d04000800c508007940c0e58004281c0c80d000c0c0c1009140c40ba00030380c40c85080c00341c042c0c0140141020000c00051409040032025802814020210b104000c8180450040544610b600151130454030440d9102104c0c4004140d1070f00d0401c03801ca904590404c401006291140c8849101c80002400d20100d50b03601c510740321603a0005507004481d0b540c2068200c141d03802d40400d44c540124029200300f07040585550900c0141c51407004640c0740c1e03a01140720740c004629164000c0107107507002820303039161130500c0e8006003160f00041e4111440c1c80d502d025400a03803809104a170020044c00441805561464601030345403000e243c2c0c00303400340c02041d00003030651803c0c6e403140b140100001e0440351181c0344a84813400500c06901140da0002d440b101e99846440c000800d0402c485005105601e0100d05400b4007995803c0078084080c01790301480420000303801880140035001050340001400f1644030b1000b07041c1e801ca44110303018080d83c0c1c81c8880c81034070003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629721258 1250 629720008 629720011
    0x105040b04090209040e0714010f050a121509020409020d060807061e09120b16020705030a0609110d08030906010b0a081602071e26070e1f1d0a090803 66
    0x103a80141c541364542e0105020f041a55810007180c0610f5002065850080355030304100d1302d0a80c0e840c0c0c3c1280c610482940d05200e079003e1000030420040000381c46041c00d400684400100c2401d0500c0140d0317038050041a41c00c141c10500c145a000304242401c0c0b00280b041c8001071a05000806450b41b400401078405161051481c2c40c031440c030080c2c510054000c0403140000d02072030407440808502402e18414482060f035281540b95182c0d030b111138070a8030000d00117050f00c0d0000d028040070790160384d4050042c441840c2c11118043c07800c50b503904545d248054800c615001e11412642c5c0e203441c011a074100041600407203070065040c0b011010f040d82c0502026031098110380d03081000c0c0000c00080e40b400039030342d1283c54503981c003610b03034007009080c4400c80045400a6151500181088003810321048045250504983c0040d41c1041255021002c454000700b107081901c1c0703103007c91441d8400c2c01034035400210710221407010a00008d000484c85580c40060b58800f0418109681d4400c0340d41d120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629722508 1250 629721258 629721269
    0x1e09020f06220306021b1c120e010213082e0e0c030a200a0e0402041d1207210e0411041d0907050102060108030301060f0c1b080601050105040b04 64
    0x100480c0000c1d2508010994100c03a50301c18581ea24095542e10740400690300c03403140302c01c800c80c0c0080d440c8000341c000250001c7c0d144108046403514280c1c604112180942107501c080c0560722040d0102d0314540c00e200a0140aa41ca8018800035013401e40040c5401e640c000b6604080800d2485c01e001c8014058001e00c50200d0800041045042c0700800c0e403628841441c41549402000c42e1482000010052401134403929100204940e002c0e408006403008548284901c006055000070300610701a44406042008004200140300c29200807034030b0074220454280300c44800040f07c60034044040d64418003000d07031000041155450600c010801d070b1100f1070140c09241c44290022020301ca1005490151050f420308014560b01c9a2a141c0a18019100290180502100415654400f00e00641a18140802989142d103021001c6600400f441100c01c204111101610b00007031400c50204920160814440111030926020b103040103c180d01150611000308400c0040c05010015201101c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629723758 1250 629722508 629722519
    0x30d120c09030506342003130b0702010216080a1112010903051810080403081b030903070c090204051809070f03080a090b09091f03020402030a1e09020f 67
    0x15200c4a080d2002052070300b0040c1207000d0381d81000001800f0354585004100400003000145000c680c041040300c01d044003e000080320256442c480280c2c40f0b8103691072900c1d02e800c0328901405441d101e062902e8641100100e00f00000c0d4070b00039503030304001c0a461101c0d6081d00074001d5141441c290b03684e82001000038440c0700c2c040701d980310079680c000c0000b500d040c49000a020356000d0b89001070041e404031040c0241c1d02c112102c100720505004645090281148c1c50b50307283d50315191003d403044a0300401355040c01c100c1d680024480c0000c1c002031405480c1c0a030065850304928a40441104480e81080051601c144810003480d80c1d4401005805510f00036040c801d600d030100640d0030240c0b5a04100c07811441c2c400000200540c44001300400c135071a1f40d401c000b01d038441c40d468001e80300780022541d0080700640807030410007848240030400003000c011402040e03581e50200e0141d8000712040c4000c25640c0801400c5420041c07070300194500b008a08119101c05a40050314514902c54424002c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629725008 1250 629723758 629723771
    0xc0108010e180703080a0e031501050117100b070f0515060a090c05130f03150b01090504021b0f06371d07140a0902130306050718090504030806030d12 66
    0x315018080b401c00781d81c00405d1155500c03070301c4402400020742414950700a22134520701e007507400d80400c116816150160b49222100e81d4440f414480c1e08409404100f402c0c81d800c200240002607107000b041124410340b801201001d480c1812420042030b00280110409020b0400c0095583c1c2e0603100706030ba21802e00007600d00310401007200e850040c2c85c0c0041c2007981c02c1e400440d01181251000088030f11940c51415003041040741001920b03801480e907030119081180502c0140703829000f5180780d04c07440703900303032040310182d5a4a0300d8600394400001d85070b0484d1b4140304040716405410102d00c050700c202d02401e9002e1100083c04050301c000c0e800030655a910005c8401100b50b02d2524541e01307800e04461190307840f4100c800320017000c80480351148410800003c1c0180c130380d0080c1c1c0d05200d00c500843c4a03041c510740381d140c0a848014800c004000f070b6a020204031000b55103018014045000d00041c51b480c1ca4580904002c0c80502618426802800c0c08201a0790114229020030000240031842 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629726258 1250 629725008 629725051
    0xf130311011d0604020910080c0f060c0a060e01360f0b010305070603050609130b0c0f130512120a0c05150c0c0607050906090103180812090c0108010e 66
    0x103046804070844038146a2000c0070a21034001992802130740215100d9410f92140e48099448010502c91411703da0000c0341c101130f0038641181c085801034405466180303008002c02d0307028201241c803c1d003215055070340c5078080000c03038091240d0340f040d09098014032440030014030469480001100e581201000000c04401000216540703244083c5d809001c0b107847e540c492801c283c982d007141c003c031030000f0f01d4030b40026100e00e4030802240c017560028071b64048120b0b0720f4035151803038000184041c50241040000300014820036004004031518540880310890900040200b41c02d4214402080da41c007499441d061240f21100311140a482d500f44090306122a103801da050400c040030040910305400200701c0c1600c0260014805500c0304070507504c299640e42029103050045041080d00201d06001000c165402039001c0d4480b101941da43c00c07102030b03981d61400f915030700012400c29030031100b00600006650800003c0d48500c0d0908000d00e10f0340c1000113030082207000402c5240800040c402890380b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629727508 1250 629726258 629726261
    0xc0c0b0f07020d020a082e11070803091608101811131103040b010302010e370803040b0a1b050303040227070905210c060c16060905090f13031101 64
    0x102075103c141e07048904c6d1000d0484007072150400000d0058800f541c11006003007948116000d5002e10721038141003009c00e468101d03ca8100500641d0a0700c0307190100520103036150701c41401009840000c00380c03c07140d02503c909a032a81c0003142c200c500311400c80400120031951106000c01c00b51a850703100408041890094160560007640540300001404240402c1410b40c40c180c2c2d0003070302c80b690751200c104184903140042d4000a9070070070045c1c00c00310400d404c0040300000c1030041801001032035141c00c8142e00356030083d401508454400500c05909507040301030600d4181c0c240c000c0c1d504d13144175600d4887e12440000d0009110701d11074460401c008842668104260340008402c41c003e1030403c5000e0b0a901c05030103618410300c0c800045014030701603501140110540f00003d803265000d12410302400d600541c10703900450088010b00c1c1d602c412944010402041595103000410b86040c0c00d10041c1078002e401c0180d002d17210720070800d0318007156981740340850f4185810240744203d1900d160 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629728758 1250 629727508 629727529
    0xd050a0b10090e03030603060a0e0f0304170c0a08070311042702030712110f0609060a0305161419030b0301111e04030201080705070614070c0c0b0f07020d02 69
    0x80c0540a9541440010407407a28510180d40444408000b02858403a0256984c0000c582c2c03503034503500200000b80d21981c00d03080041c911442004480016020f048054107540207904a170b04003842224012402401c200f2400880f05029521800024103101860b515000385000c0581111100052010305407915440311800134a0400034101e016660b9070140714588405105038407031310900501040b01100623110140543d400800381580b010810240640c007902681c00ea0f500003024810310300c4544500c0f0042c0030744c60342036a001841e031410082404915540b070100504000309010192011481c110450ba0900400c0070600b0442f10f181c1d004401401b105003c198055080464445c042542d01e80036010a0340b81c4028482041882e0f0842c0c90340740203d00c0060300284940c00860700300390280303000341685402403001046030b01c01c194102944130360a07205400001c01c0d40d1040c001f84a15012000b01070f00e01c03601c0003031400401c1b541420480c0a2241c1c06403080301c0c0010030008640c0d80107400c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629730008 1250 629728758 629728763
    0x5040902030903091323070504050d02040603050609030d05090d0845010b0411191407031713050d030c11121c1e02071b180c0201060e060d050a 63
    0x2169690b03d6040d01c0588402c800011103203645580050526104006e0103100386860303503589050510300300170080113004a000990b005566404040003180c2e0920134148103030650001540e031208516031341011618010200c08242d0071548000f02e0103a8400c1ca003035041050130b00c0d12066902100d14825079000908260410700c00702c540081e45001d03a030032041c0700c1860040020810805903106100c00c3e0f502c44001e40d04054010403030018030003042115564070600324a011042c01c1400855076440e83d100c218246d0104a051100034003c00c01a40b001354020750a01e40e50000f01c80d05d503901551282e4003d0302c0000c5c181c0340d6141c4109203100b900300d0b091380380c0410210742c1506005031688880c3e5002d103134014491444070251030640000c90298028405042215080501408207610700a400c0503108840c2e0f03000380303040c2002600b0800b1340200586520103007403070001082e00918080b1170028480c1401d40e410a0b5080110700a80210180d00200c240c03001c105481180c94007600b00141e60300c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629731258 1250 629730008 629730019
    0x4050606042a0906030f05010b12090a1b0e01080109030906081f09020c16080c06030c07060e06010501021923070b03010602010507121404031808150a0b01030b010504090203090309 79
    0x240030310030703030f201228001316040c0381c808110355091901c51400f9540c09028034189444208000580c01f09800020307139100b2045410707680705400d41c0c2c0c1c6038041030728100020307c06980e100c40188400740000300d405004061302d6008002c0e4591030b6030040d00401c003900c42c40c0d00b88a4030b034000541100c000e103060201b030300c0f0407401088016201d00b5030200035080301e2007040c1c01d07100d0130182400c0c1c3d1010030148800d94180c400281051401d4008100e5994030003003100481100502800c0006555400341c1801610194081d0800e581404002071500000034a00080220041846004103203031007030003082c0c0b10403510386a1011019401a03031900c5031f44c0c2d01224103820000300000350140d06611007806184242d90b1035111499120410702036a030040c3c1c20600b07509486022800207130003810300d215441040c10100500c10b5440c05007504001d400e000c800b07500400d0008001c0f6680c0c039031240000c101307000d0030b040040400d0b0000003071044c0207500608100703e41c000046210300340108165400748200601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629732508 1250 629731258 629731331
    0x1204111f030e0118030207090f0b120c1e3003030103050703050d0201050c04060806030f0715030605031204060503041109010b0c01420e101d0405060604 67
    0x14001c00426118910140741e51a094191150010780c003d03401201d50035034001c09085082c910250010000303681a0590541e46040142c0719032100ca0f4400b0100c03003502c01411541010303000f403251155039111307400d9003da0f4007055680560303900c100c00f41401d2082c03045083c0e07905280c2501e0300440070300781d03580d041480040000000c0080c0018090b003901e1103142900c400c08048101a802c1c3c3d4020340b140400c03100e09110510002d441880c0b1140c1c0301c9001011980051607900d440c504100d101e800502d0901c10006850100c0c41d010702540004000540042001002c18890b84050340500c3c00b0381d404020740003011a051200300c007101130712890014190303409540d46400e0b0000c1a070148440000c0d5500300400f03107400070444a10241050142c480f00b0b800210300c0d8a00d0148002038502e1031001040802d0041041e040c8122018070541e04100d9000c11a400c0c2241403051400f80750b0b02810340d05904003000001000420b0301c40e000b4000307840c00305080b801134840c0c00c0900103101c50590705d07031284072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629733758 1250 629732508 629732569
    0x9030e040513200d0609050a0f030203310b0a090306050c091305041a0a020d0e0d0219030512041110020607031a1f0e190f0506120411 59
    0xc000310282da1040d4030420030600c01d06050803a0014581c8540d60200d1600980c101082c8a6045000b0350351041c1c0546900c000719540e100110000144140d00590002c40c210402d840760031740c0034144000185001611000c1c02202c42d60701c680340d024012202c800802d10902d600e00801010010315804039040c441c51500103568070483d000700703004030b1042d000c2c20024107541025201e0300380590b401c05a100210588171072031a04c9900041e00d001300d2242d08000c2541500c00c0303842610108030300e041c0900001740e1905030003441c0c00d030f00240c0d4881e038400c0324580200080d00101210b0900c404842010402d80c0c40e41842e10305900c0c100c1800750458034042c0342d00c4090380d010924500c07805c40340d01e0400811101d074841524014071601d030366421919088184d4a441000383c04d046c3d10f41143e10f022400350301d520380419041030301118100c2542070324030410f0140104008011024200648150703007000c4200e41c034080301d140b005d00080d1026490201c501e100e82c940d2506c0c400e00803520358031440d02032620b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629735008 1250 629733758 629733781
    0xc0303070602071109060906040504050f0a0b010e09011e0b010201110a080402120f0a17040306060e0403140310030f02030106030215070b0907121b15091404050c0a0309030e0405 78
    0x200ca0103400700500c8038117440d1038040a0301a40014003a10b0180e40c0e6103080c040180030150054405215000024821603402c00040221502c51036003011a545090745603e40c1c0400500041c9050b41001c006a901c5600c101c10603615401500340450600c46101c0182d006142c42e0306510410400040c1c0c070545c11381c00146450140f0310035240400700c04041c0707178078584401c8614503107581c5400205508000c10a5903000c4205100448a00741c0742c15030b65540d00040341e13210361210a50042003001c00007455040f0045840c4204411111440d40c81c09107403050340040030b40401403851044d00250f10954a0943c8003a015580c0900010380b4485440216504c03508402c40031200020454000307012200e01182d407000300d52032581c02031403460990340c43c82c01c400714519101c00e903c148187e0008070745c0d0a01c4810240300104e80c5480200508012501c01e89882c0c400c0d00c54040c60416007072140300822042240d611508501d00004c0700d401600c0e0031281940f080040d5980039040600384400ca14a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629736258 1250 629735008 629735017
    0x10c150603110907020a0305031611061003140714090c1b010b030c0301020c0615033c1f0c17010f05011b030e091305030a09060f022a030c0303070602 66
    0x460f050105540d82d404202d070340350340c40c0d20300400152041c80443e00ca0350704048014a411000e0a110044034094845945031510460341c0c5111940c00200030401e00000d0002c180c803222514002c0e020300e50505d000d0f1051940c010311140e014841d00000120403403400400c0d225003e0860050f00401d03100c0000b0603000c1c21180850a01c64061956400d04902e030500c03c448a0346002c502606951307407082016031051501c18002d030f03010b010305031301c0400e0311425801000e251840411164240300c29900d22001943e41000b200402d1750000c0c000c0c403400700d800b00c25925444a091800306590024440484a070344c0b07a6041000750680c00400810411038050320441a10b0003030b0307074521154251103103910702000d40075005800315501300d0525606040c2080000d034804a82124072220221a070b8410b481c540c8180004000180c5483c420300005034011114000c40207280f0040011000110541d0418480d405403071551005141c490a0b40307843c2809a075004802c01800c0d80e0700c40800d400c194000c0e600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629737508 1250 629736258 629736293
    0x403110105072a090e10090201141201031b0302061902030c0a0b010816051e220b0405180c0402070609080301030c08070506040b0a0c030903140a0b1b09010c150603 72
    0x11003c0c0301090519862041d1a680c1040100500f40009040c203101c00408030020164108044000590b81200010004101002c0c0414000c01c05600d1030400d0151019041c41e8070494108044040015076240703801e540d0400d010413407140314505401c1e81030f451845920103011682c060050f8800a1040e00d000c00d034100d420007410307203135055406401008010b03aa030103595440204a40d1118038183c040c940541583c1d8054042c0100b018a880540c09001c940000004000e07114100d80141e41400e02540750007841907a05c1d10340e0301d518220b8140d03d80b900d8248050182d0f9000c40d902061007455002815202c1c4c01000c0c0c940c0e656181d00340304000c12105d005544c0d1500c030f41c10340040d55042c510100c0c0c04072898007182c5401c0c007141600455680300650410b50402c000350401001203407110000010000244001b081c1d00c41c0e00703242012101a0082c0740c0003030042800c2010100352482400c0b075089140034a048840041645008040101020004c5040d80d190401c00300820103140e255503003488 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629738758 1250 629737508 629737583
    0x5100503070f0e0f06030703081b070b04150801060e0f060d060914090d050304030507150c0e030c06040f0302060a0c0f060b121903030f020904090503120606070503040311010507 78
    0x13a40c0124060001c1000c1c0c0d4000d03010740c0081402c0011035008405090240481c03e69a1400e5030921182880c2080541000d61380f01d00001e020440804031b1059200944d24905040300781d50300d4100042d1400c0349a0803450301403050260001790729510003084482c2d25550306010055503403580807420051040712100c4503441f55180104004100010b041d407000c2e6a40c0c1e561a00e1641c03161f4040b28070b60414242100d8040301820130b042119102c4c003840c0300e19101da55a400000b44490105803030700305800031060060208000601c04c040707204d44a901517980541d44079030b85842000048880f803480d030388060301c00e5050380401c0d030420040d50480d0070b0012044031040c441111002c4203d45400c40c01110910300015001d0100010713002e600300601c1025502c074010b0400c101000401d041d120440300131030f1070340c10000b1182141c00700c03a840290131110a442c10b5003008050341d41e80303030782e44910b001c050080d80d420514811668801c60031100c400354007000c001c00060303036540110b0201d590b00264a9000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629740008 1250 629738758 629738761
    0x6060907111630080f31090b03030301050d0819031e05060f041a06070b0103140c0a0603090809040207120221181903120305060d080702010305100503070f0e 69
    0x4441d8040755603150f000804040c00e039050f071940c4141c01036008040d0283c40c11024402442c0d541100c241c0c02200d8103a0044860484092400000740c1a00340e4100d50740c01c1d8a4050417040315103001082d00e05643d02030b9000307000414039091030000e0b4056a034145101e10300400f42c1d0844c03141e058014044003010035820400b084540041c94080d81e42c21905c0c190840c498034074800c91840c154014800800c00301149004e0720300b405002c5842c0b9446882c064034041c3e070b900010801c00c5490400380000f5645400507000c0e4004030300011352142c90754400c207002c141d02d030f0703181c0c0e018480303508116042000001e000b155100054035024803c00d8580303503d0000b40c001d41d0a000500c145000b03070152001410903003c0d00d0151401c020080581000b441c0c42e400c6041d0010b000d00b030240d460b41080c0036500401c4c0d4241d040884040040646070020103444c0141000c0741000005901401610781302507090801258035078441016424040c800d038041603162007440340000f0801c1401680c41d003541c80030413811006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629741258 1250 629740008 629740049
    0x4090c0302040303170a060b03090a02030f06070917160609050f01080403091e08030f12251116031209050d0b0105101b1b08060405060609071116 64
    0x100c2c000c52002501040f00500f001900d80440912543e020840d1000040c090362500c511660703075001280c1c0901743c0c0e4445541c0c0420f600c0c2c10007243d210380320100010b2900e03192007900204610780b248100000154030380d600c010080010310031901440d00c0d42c04420b200b19501e2500920703c0c0030074410309006141c0c0d440d183e2102c1d4411000544201d8046d25801c803054603042152451031f0b500701408086045401c0003107084c0006100424200095120082c1c4070900b944109100c510f003e0800c810001031050440101c160b151024000d03002d060402c40451182000054109604c002d44c240740e490341000003000b0000b0705136040b41361040581e0741c4107125890b80180031139813642440c0a040f035a9403c3c0100124540340f115903050201d01c0c5005c1c03461103c04000c042e80c2910a0400703c0b001c1000103c624880d901d80300c0340314010b208400040002d42007503101c854403008040d103003074050300f0400002404d290260003044507c1c0c103d0000c40345284090103a07800200242e0040340c0310180302e440103d00703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629742508 1250 629741258 629741261
    0xd0318030b0f10140918211e03014a01080601150929070c060e101706120d0201020301080105181005040f0f030305161d0d05011b0504090c03 62
    0x3041382c041e00c00c05994841c0c0d01820110221080700303c0c0c061007104580207034403c0e440010f5241c410100070755a19a41145040c084c030342c0640c24051159030051004001c45206002c00b000520300100300c40303864845441241501145158419541e55511003042001107203445c0054101c48240d01998216600c806400c1620318158186d04e000900018052180c481101c100c1108001d0080d04100001580084510719802404003940d01e07500d580350401405400c05032030300100380304541515420031071450213004403003510b002c10050400400001d03000e8455134540c00090900c5006c0b103000220100009020794001d016401702e41d400d050100d007a91481d002900c1d80300b1408405405004c0c244041c1100070140200207945214402880d500400e0f01c003040da548a40c040d9030042440c2c9031042c2c0c1d001e162139500c0f6500c0100117003100120151801c01e800300c1604001100c21101c0c00c0400d007091400740480f248a043e42d4601d0159500b03910760030600500450760b040c50305000b0304240000660 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629743758 1250 629742508 629742539
    0x809030c031606211b080901051b03070210020c01020a140307091707090c0309051e190611121605130b030a0e0a0c050411090d0318030b0f10 62
    0x1210a50448043c8203a82c0100f803010b6801076005108524540d4215141c0b05039218201c43c01c007180c10130340c1004592070380092400e6110f41c42200078421400c2680403110030303004d2501a20301c0701a0201c00b080c03443c2e1080c0140001e1305103455041d500d80c40009e000034000c2d8400019000850300482520308031461301f1003170740d200c1c51a5440c1d650b00d0360f103441300c200e03000c001c0d012552805005052011402211922410304141b81c90360f00014606002d2074910300d0700c107010340001c8803c2d5569043c00104000002c601030303c070082c2d192000c490551450458040c14400102c9004980040340c07690b5001070420b185231062048084500da40041a03005a60621884505026103100b040701881104d00040045401503004032001030401802c4204e0707400c210b2800012a20514030840401c52851715003d42061407480782c061031314011041c00019015000032400605001d82060441a044100e010140003503800c8a4107000f1460050b240400841045806d5103c9640550740400c80018954009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629745008 1250 629743758 629743783
    0x10903051c11031521010f0c0507050a06022d03060a060c0309060e0604031407050a09020903102307020c0301322d1e070923060301030809030c03 64
    0x2545141c84421400c0000310b5130036036054020700440c0b840e500294003011241e04408042c4000181d444210f50108140d401103070304101002004d10800010400200e581346004d0b034440300040e56109a90080d28450445c99415050aa0b0701900da40c1642c6500b80210300c034000c01c480d002005501c8010540b80b1004211024001400721041806500e0054040814000000b040305051507a41d40d02c5100e030800c442c402290031b811a00e0100254103004540d4000f42c4580e103019800d0403c09000709035134841c48094403090940741c25a24540511078590b000c808180c880090400d0315209101a540701c2044840500a41c68103a40b00c00000c508000c1610060340c00c0041000300a28081c40c2e81c1c0035002426490380c0030600f01030078454841c820301c500402503000f420461185000303695403000d0541c41030308a03050700c0c8032010000403030703407110011003a03500221041120441c8010030b8282c20790003040003504000000000f00c01d202c07903240984400d079411800c444640c10a03200781620b1740905d8265 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629746258 1250 629745008 629745041
    0x60b13030b091515010e0d051c0807020a0305340314070c060309060b060c0703140714060c010b030304090902040e01141302130c09050a06050406020d050a11010903051c 74
    0x315481000d02c0f01c0c44241004c0514094088103a0400015030451190383c04a4042e48900540c015445a4060380c1100c24a10b0400f2102d03450107003c06516440f64010003410000c000845170f05104180c60341c1105540075030f812031500190000c02e1216601f0b00303101900811a00f468410032658420125500d842d48a08580340c468030b070034002d40140c680d41c14101c03041d64440180780410744403c030240a0320f4040c0c00040a04901e1801c10a0314071101c82440d40c400e03040311505010080c540810103502d50f5054807043d41d1071080f00c030150b0050498220896046c0000070340010414000c0c0c110035002030084800b0403d500c01807801c142201c4081900ba0005101e210010701c2c040c0c0450744410301b131400544005440f50a64001c242201c06032003181d00840c2c096002400b2504054a481000d80000c4c148035240900300312011355241c50b105160005c20200003078400c00079100c1c0d5842ea02049804000303200640eaa40b0b03001d025a0070a9203510808032040c1c0c0006d0a004103806856400c5001540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629747508 1250 629746258 629746261
    0x10509060906150d020402220611160e0c07050111181e010305130602030a020a1b0b0412090b03270106140d0501060302120a05010501062f01060b13030b0915 69
    0x3400000c03c01c2e29000c5c1c0c2d20650a0090119506604140c101c0904507843c048600f01e041005c080d10500b00c410f05c101265001d90940c1c0b007280903a100074010340d210f00402c400b882d5107002d0411201c0c494100020510350070044820201c0f01e40001a00d081d1001031503040180e12000148503071085401c0c0c907141c280340303014121800c0354025406160803192070401e81840000c2c030740b11030059a20a43e000b80000d1360002e24504651f521680c8070942145c0e000480510000359121001000009000070706094410480040b4080c0961807440082c00080b02c11512072034030071910710502580c5200d011444c0b4030303180d8074000d5180620520040d00e2102c95200b0420141506100c504201070200f150503640e2401e0100150761998480c882c40202900284a140070b540f07070150950f40185d0044051154070700131928061b0416903000d050303220341d80190229410003c0d4050140540d54002014058001868400303c0402c1e00d03540152401204946540d480c1c1c19050340c3e6500698506000507a403440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629748758 1250 629747508 629747551
    0x80601051c030806031908180d0c06110c1206070908010c050d0b0a09060f0612050c0909060409240524010f02070302040f0e061003050c0d0501060e09010509060906 72
    0x18009400603c050211000c1511840c45441503400d445000e41e442e0101140351010880c403d400656449012741d903001c0a94210f513940e01d00c0314024040c03c800d10107001c01d1317132800c140704208a00845c2c3c0001c04400c0760300e1544a00d1520740500b0b46050000501d101d1012440540501401541c003046684140c42c20703d0b1000302c000204000340c0c250750701c41040703107001490007182c1c05440090a0f0603501e00179820b103000005820290503402c0c3c2c4200c0c2e0309001c10007860310780e1401a90070603d0190780c036401e1681ca4030300250040c810250010507103103485503811800c0d41c426420740c070001c210400800c096210700c240103008030340000313040b600c1d20800340340c1c10115449003000419640441c0100d8015903200d500040544040e00c0b0340d4004a6a200180c100004007082072a0f00043c0f21210103451307600f1526610388484000d1840d900628222101804001f8250301c00030007404030025403401410100f581501928042c1c440c040301d1300c40c460210f050340601040c41070260301510480440d014102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629750008 1250 629748758 629748767
    0x30081912050a380f0105090303040807180612080d02090a0602010c030b01080402090606090a0b0a050a0f050c0c01030e1002030a05060306010f0e06090415050405070e0109060b0714010207021504080601051c03 91
    0x744d1810042e0a01085c41203440400240c00600403400180207d18101084440301d2020351020048050811030708001c1302c09001088488103810000195403484500d01e580080d105201000d5080b4802c40400903103640c1c10745c000812034186580a100f036441490044900b01402e0750b010f5800b0b910341c40452014603080c001410121009440c550f08107a82c0c42605481381c1140c0100d2001c914006400207140703901018040c4103c28a050650030800e610003030a81d60001000d0b02070606656074140480c8010401aa40301d4004501007503549140500e48403001e40001e540b418024030038034002041e501921041c074429034144105050705a51544200500d510001d8000d490100717058410b184501071b107001e824407a6008030002c00350365180c0f0100c40b50314441644840c44940c58600280a40f02e42502228507480c0c1010b46104d1458110080900900c90000c00035800b07000c170910044110000b41c082c004580020041d01e1f40c5030b0f1395030240001c804000442ca100140301100c00c4000074000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629751258 1250 629750008 629750029
    0x7141c0b09130b0c0702120a11090609042001030f060602010b18070203030a09060207020d0f050601091b1d090f04120306060e040e01140130081912050a38 68
    0x1019a007e155075010541e0070110044800c1d84c0001c604a0892600e0410a80d0213030412015202c20380d15140540701c41d0070001c0444104800080a0325901190740e11070340040000307801042d010007113a907031388070042c1c0244825603034180074a40c0b103450303901100c030b000c2005446103005030041c600c1c556a01d0314413402448484000c0703e8190f428005000540c95019407451000e00c56030410140e41c2c01c5080c51031030507405a000500060404120040340121a54898620b09031414480919400c446000b5007480f40c8004560f0803d40d0b203020007884080c4960000d00541c007980510b00c404c100301c14100c0c00d0710401c0c0900d00200383c01030755201450820b03030f01c840d008603103800000030500c906401401c003442080c2d02c01511000e0040d503552444105902500c0005140b40d03c000c21035069640c0c49181b4080c1100c0359078180302401882d00007034001d240700a000c1e00284410001854440f02c180d008195041c84a10400340418140341202a10a03281c1c20000700c2044140049086e48200001d4a41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629752508 1250 629751258 629751263
    0xc0617100b0403330204080c09070e120f060a05071106090a020105072f01110f0d0810090234030914061605030309060f070807141c0b09130b0c07 64
    0x72042554000d8641302000c0002c01181500242c1e4980c645240703079203800c0c501c016a078841e55442061051094011000700030750b01003641c1d1048071808c9086281d0808142c18400301880c010b07002003110640b1340e03512503441003049840300c00c602d030289241c0664800c3c044500711080d070300080c8820090360084000d0008107200d400120b0507850104e4400c1030b840040c03944502149a035a68a00c85c035a0490045507014402138002c1003c3d103266085035648045092509060041102c08648000100d601c150b01900c0c2a450542d61030b641400140c01a14a0102c0c50ba813034101000c0303011040060301c11a039980d0b42c0658a43c0c1c246130500c2c5450014410301040158030020410131240340d8a150180d40001a01620246880345042500f040c05d140b00141118140c948031410046480d8015180c1c0f50440240c0c50040c0307400381c1d130b07088450603841040005048100c46003010001316510343c0150604031001c0c0c40049654503401d10f2001502d810010040c04040d600d00062404001c040207024400e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629753758 1250 629752508 629752553
    0x203042106090f0b0703050627070c0b0705041e0509070e0301061809020f0d031d031207230c01021b030309040e061e0403080a09030c0c0617100b0403 66
    0x5030740ea6400c07640c0c0c01c1520481d483e090a00c200714176260944203003940300d102910341c6080c1c080d80902c40c43c4041301e00c0b42c80ca146030f500b5038040780c502441611b0038102142d00c040c0510b4141005034000e011741e0041e100e850500c0305000450302e405541500316008455011700813444607100c40105554900686a901d80c066513208000252a805600c0fa21b100301012840001ea5000f0f60050100d00d9044500050183c0d02d5181c2140009510070074401d4006410014010f040c0c10707000000b81010208000c0d42401d4001240480c10701480c1c0c2c2074004112201e0b80c8005003a5903540c43c26456025403040e082c0560401c1c042d810700c400b01c2c00c4030710007170f01001001e591901045c040082c04070313000c0c41000d0b1416800001007004951400310f030921030b2001000d030300e5601d24295034028469440108840d01d0a6110154101054040d219207003103103521119120083d510b4080c000c00114283da81800c030802305401164a400b40e03403901405840381408860314150540d02c5914070210301c494001c5002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629755008 1250 629753758 629753771
    0xf01150f05091b13090e150106050315060424020115051003020f03070e013905030d09120f080405030f0c0a14031206040e070513020f030a0501150203042106 69
    0x384038600084c10444803d0060078030942c1401590400c4604a522135400b603840342c90b8070080e01c0382d103c00700750450740181340207561b03640c6000c04950040c1303100c0002c82e0484c0c1d011030b0200d03802daa1a25400054a180080240100c1019504034207035658085440b0b1800d04404040c812410607050100d01800b4074280940b03400c5000d040382d035860f80210b95150000311a84140c1d80c00d0b40e4040350120784048402000d40d601070700a00c9c421841fa0043c030103c0d4030910309403c0c000c10000c0c06d005a0b80003010902d001c11a81d4151b0a00c004a2004034586a000440c440700d9611030a014400282c05950040021403d095000c00c45030010b40c84401c1c256924440d03200c0e00d00006403e04120f080d50116480915182c4411b1404aa6142e5028010600c11810311580034135050b4009010341c2107c404031481d4000503121041c0d0b2000f48a40012968400e000204110150546801c4103040f1400413030740d0000700b00740403c00ca882c0d00460280307096801e00f6075000810049d552288002e914064400040c20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629756258 1250 629755008 629755051
    0x30b102001020c1b03120f0a0e010c020301140603120a050322050708030c10060617040c05180907050409020a0911120103050f0601060f090e0c070c0303020f01150f0509 74
    0x2402d46010807400350301c00401c14481c60f82414803aa43e003080101c1d1806d0705018140c8002c444502440c01442c3c10080c0d1030b819504030fa0b2007401c45100301600034008000d420f01c4012103000c0601e084800034044e1151401c08030342211001d045400003a02940c419045d80c840f207081020078038040a030003100c036451b680c2d480081542072151000400701e82d801141d42c5d001d203407011410814260100c030312840c81d100382044900d40084440381800744d001071001c120783da01c2c54044c01460450b002150411103885103062400c20204c1d18900030f170950821129500e50b40d4040000340e5a00080094008003101c2d42003120808039007200000d1120a1440da0400142d5020980c3c0450b00340d2042d2499800202c4081c8104803e001c103901410152034000b000c4021244007822207031143c8100c2c0c80c0600c401c0700003001e440824055030005031b44141c1d00858155a818000c1d40d070403050000c82010751030300c03501e025104921100042221000e0b508a03c03114985400c10000c07441c0181400202c0740e0b41d00c6100e16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629757508 1250 629756258 629756263
    0xb030903130e0705092e0f08010e061c03110307110108060a2402010902030a06051023101205071808030403080415140a090501030b102001020c 63
    0x4508040001540c80d04040880c00c50300e01060707480010203102c0308040c0b10f003082d4808110b0301282d400b501c140011145400c0742c044800b280100e14100d420540240c402a1540089002c6806049036114031080e62a078440444100080e121154070000d803500c080b0728407800020b1400402d00030b091102000e2100000c4e241168005103044401c0d400c007510200340b42d0b030000300d810b800000c192030801e04281813444a4450509031000c001003611101c4089000500c02d400066010358040c043da5160a003078580440909815900c88541100009000c500300702216405013410600b1680c40303004403245010300071541d6800c0e0100c0b00b00110b601240c3d14002d19402868000c105d65614030071482610440000d003030f00903401500d600d40081000308085101c0d40d0590341a11400e00c124000200e52042c00c0e9400c8801c2840201030003001700d0400340090b0090301e071b4811030314203072002c2c031010325801d04102d5407903010840e05000c00c402185450550080c0026142d100031a00c00052a10817244180c0d031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629758758 1250 629757508 629757511
    0x18031208010306062102091803040f1d0903090603060f060304050a02040c0c111c1205041e0302060a18050301090c03200d0b070302040b0309030307030c02060601091a040b03 76
    0x50114031164010001c021aa01c101d00081c40950032540b9507190300a8032a0b4240c115000292044a124012410f502510040704044602500490340d030f6994640d5140e603855803a1181e1120609030701481851001602c0f0024401c2c1c83c3c0c5030103149443d101c05d040101940010b8401604000750650700070054481d0001140110300880003000d0b25401072040106503070310f80c00c0c494204407614030031100241034010140f00b003003170071103040410429030070f28034007108009038000e8051107007036511000c100d40000082061351f0b21903880481040c14560b65034030348401071000a403c01d0b020000f0b080d4191045800008000708240f810f00781c16944c00c0000d0944030310000980c0e0b08103603603e08104204456105504580055416401c4407241e407000a04190784070300007521490701c80380080c440034401d504440290041041d5941c0ba410b206840303d0303582e00200e4a410200b498a050750741c1190001945c00d204080596641a120f4240700d00d1846200181d440040542002c2c0f00110300b0f0030303202010390b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629760008 1250 629758758 629758793
    0xc0f011b1b030501091202190f050114190b0d080f03070e1f03050a15050d08190801062006130507030b0103080a14090901210f08040f080105090d1803 66
    0x720300c004030350805a030504074040e414003d541c030030241c408c111884810010406130b00312402029504507401e02c0c5014140341110341414807081c8080040c007101e103103034240c41c10341030590400a507810b8500340060143d136002d000c0e10300c140511140110501d00f074029540300402c1d1800071500c2c1c0e08040810860108043c2d007295440607034040084d8240c4c1440340580c802200041030045550600c2940f2034003215024107402500701319250780a0003000400c440191a105480244103d0b890074000c0201d40203014900019052000c110051a03210081c10900303111032024200d0364844c93301046a51451410840700da0050000000204d031441034200e000754041ca14440e07517010600c070700500c81c401c030340091780710307060188240b07202c2c0d45840b50f6046c190341000981e9006420600c250030f80022100100401118540402c0c0e0308126268005d0021215200c260301c50454481d0040c0d800c5e150100c034008901ea0000c1140b048043c0301b182c0040e4031200a4403510351458894881d8490141c2c0074544 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629761258 1250 629760008 629760011
    0x23010503060907030902371523040b0403110102030a081501120906020c01050106230d0e1b01030b0301270311030d06180b01020307060902032802030c0f011b1b030501 73
    0x41100c6114210350741d80d46447c03507035640180706040c00350840c0701c12008603007402000201040030041c80c02d03400703215901c1150002000e0303e583d13980d19400c103a035001d408100d50341030544420100650000040d2860903c0070789500d0711f640c1c0c90351015030f5141c248070040780c10001e070400103034442c9440e407003190010742c0200070141c1c0d10200c1240712420b50340c041e0b00140c104003282011000c4000c0c1d52000b0910803e11140c660307a24030b40e0b60304410181c1182400030b5070700d0160580d041402c41c3c0300541c01101410a0300c060003012004001c0600300c91103000d00c5040c940584507584240c80031040c4011340c0520a08240103400c4400301e4031855500111842c410455441009204190340990303400d8180c242071000323115100500000035100e0184480081015440740c0c448411580c2c10300c0303401054844030594072502c600c1c5201c100c001c660030080c1030b0301034060556440700a0804000c108005141a129001d541c1c01250b081d0680c0314a03003000350b0700703244d20715210040c40001c03010071001140110b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629762508 1250 629761258 629761309
    0x1e03120f070b060d050303041101030f0608030c0c01050c03090607060e0106030c17241017100f0203010302010207151101051611070806070507060212040b0123010503060907030902 79
    0x14a100c0d084400341a80d4495904c1a9040001500000840398000d41c1300f400f1416a81981e00141c010b0107100003001c03840390402c040404d0100b030000c0500081d035013240444910b1208000152000c1c481c1da00d00e03100c140c00c10000741d20242880070040000302d1145c0c10005000003c1c134600340c00c6807911b400880745540704c0402000003120346a24140380c98894030203030401c0304c00360380e01e203200c802d1486542102e41b00040029000101780c10032100244204d0540e10503650002e80450380341d400c0030f1201c0c130035203143c0303000c5801c0c14011f0f10a89040e40c1d410380003000e81904011860700000d158890700d000b0441800440c8590300c80c01c1c051a8044d01c413440090054031a00ca0001c0c03d103100410300c5e455144d110503010408240b0015002d904212182891659a40d0342d0a0003c0170703104014142c1d0f1540a454184000c214800704158102c61a0b03a40c55605003142c07440101801040710b02c01e90003d0000d00c042a80c41c58688012070f004965818001040302c0c9a07070108043c00c10618400284501c00720 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629763758 1250 629762508 629762513
    0xc030f07051309050c0c07031202121608071b0308071103060f040b09070305011a120708061506250204201605030f030916050607021e03120f07 63
    0x44080d004005030034500d04000040d460785a16038002c3c8a0100866240c0011030304900920003160864402581507688040c1c903402c00b01c0b421820181d80b0801841190402281031080d038054440b0b2101c015503101518000340c8500500e50401c11054940300d510070312210349602c0544001c0001c500c0340e6089a2240024101004010f11001d2030b2070094004504111002c0080401150f0090707001c03984140b50f031901245940381506a0300001d02c0c0390300c0e00312602c90304a0b01d20000c6c0c403c940c08941e601d5000015102e825141c035070b14450242c1560001003c16aa00003d0079881440c60b8007610f01420840400f500100d0100d641d0b01c0e2a224154142c0d200d070950420b80607501c454042e810b65208811540c0100d0004ca104419480b034074109242c8035041000800d100310790720120700b01c10140d03d90074003511554807100b2113002100d005a41141c00603641c20541c0c16100e003160001c10042c0c21001c201c14000c1300407145001d05505019400032804410000d01c054070b181c80324000d0f40d41d114045807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629765008 1250 629763758 629763781
    0x190204121401180f020d081b0705190f061409040f1401080f070e060d02030604080a11010b150a02120f071401020f0a0f2604050607030917090f090c03 66
    0x121040c46030f071941c000c206008119400c0ca0403030300326410389460806007401c0c03c150245004c1d55481c00c02c0141d132143c00051070f200018500c1c094502c02c603030083c681801c0e01050340c0302941a100c1c040144240c64000c0051500502e1001e00003c2c2200b05039281c5889500018212182d030000c4420f0160b0350090310042d01c3c02404601d01424040b801000d841e445003203001ea45051621560380f0b85580400064142d440c0c1d00382100d01280c0c05412038005050620300043c0f10740154422000041c2e82d625410034000050050044640e000740012544200e034000c0441150b10240134031003507214441c03007071415031088402031180210085006407038008510300390f00e000780010306864850380188040e0010038505d0049480c3da40031810007401c4000156000c1e11000318403207258050000e2108054011b8440130482840b82d8428015101d4a0741d0303074417054084811005001e40003465200c0190241d021000c0102001d1074001c1c4607500d01503011000408194084480130b500290210502c040081c0700e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629766258 1250 629765008 629765021
    0x507030f14010e07080303060f0406030602040803070209090712030f180e011e03020303180d0803040302033f0910050103060b01020f0d05180a03050a0501060609050f010503190204121401 82
    0x201805007030300c1ea20b010b43e017a07503d00029140500c40e200003544480e680d0f82d2540240000e6900c04015920b555442000c1602c0307400148060b8011485000090b8043c900400d00c0000c2e90003c460364000c1c9110350710112400750803070010206108079003c00708207804203104294000e220801c0c04100301e42c1000044004188000c903500d04960807414203200682d4044140c0301a84912068020503000440001c0c2203003505940141040e48008144028181d02200400040d85415a03141102d012403140480030100f11080c010341c1024a94100714881450211a030405c0918013160315134640d4882c00d4080700c0081e4012035115a4842d0400869601405054000d091a1000c1c0c03800b41181e0901400307a124548a08940c10040240d603443d90307807003060410203150082c003181c0c401c50035440c0080c02130810f80a80710100d8074030440015a860100940c400221040e03680030306540b01c1c00f00010324030110100d1412055000c0c000030403c0304107015000000350040004141c14198010b04a0840e0203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629767508 1250 629766258 629766281
    0x4110109063603021023030603030901120605030118020a060503090601030f0206120f0f0c160b131e0c090204030c0b09010e0405100303030506030105061c0507030f1401 74
    0xc080c404140b0540c0882c40c0d20b5800c40d07111080c000301c030007507000542d106201c58000a40c003107040f42d90104107903841140c8818032101d0f040410311071101d920384c0c9905404112805645540208102d29075540701c0e075035a00c5000391451010400585400002e0b00791a03449444a5000c1e145519000962500d403ca0400a041d541002031950a0030380000303480306414000a04082034242e1100b0864440000f1038250f9040381480c55906c1c24120b02d0f040d49410151100880c2d11800b001040c0da45000900b00c83c0d003081400300d42c10703034451269a40c42c40101d00a000301c00405200004030b001c6282c4080e0610b0411800c00d031100d00039003d25014508141720f401240080c0d105000500008100d01a0311040e40c5805100903141e41000004803928a6400c101c25000790400080c0440c5d1105c03d8030020a4038442d44052041e40d4075241851300720f8034112020b0340d001d4a400780d0b003080c0c3c9448422500005001e1000e441c1000d490361104145042c0c640307400c0b146001401c40469070110b003071181808984 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629768758 1250 629767508 629767517
    0x20f0d0b220b010e042705160b0910020f0d030b0303041a030601110706080415200a12090c030f0f080a090501110c031f02070501090c092d050c0903060411010906 71
    0xb80c2ca0313086c41c00c0c13151212130b10750b0203d541c1507001d01072090030010500304181c1c0610b50744805440d8001c03441503400000f081800b03081c62207950300c41c2a002141024080a4681c020051800b851400302d0203001c588860a8150100704000b0503803001c550120903c3d040d44560496481c10100001044401e404045240c60317005801c4c05d1103041d901c40341180d00160414400d5a940600044010013013040318640e41c450320b040c0340c461540c207961f140600000c82164071603e00e40300150500300140c40c3e41c050002c1050f0a001010b20000d000c000d41c1000640c044d600c86520b160161b40e624500b41d2010480380041806880204940d40e84503602200780d06110010300202001031001c01d60707400001e0703441514520080748103803071640d855051f90841600b00000740001007580c101841c001a043c062510000d092800440f1240103455400c404824800000a040c015801c0c00704010440545a002481402c100d500604c0c3d03020000075025a0090f44448644098040090f0549110303500060501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629770008 1250 629768758 629768771
    0x9050102041a03150103050606090904051c03200d0204080d03020301030c33020c06070b0118020a050a05030402010309020d0b0a06150f1b0804080619020f0d0b220b010e04 75
    0x3440001303202d020f1040130300703020880340c6811340003031100e01a001d240751700b0110b0710381004148080000c10340e200100c4040c400b0320001c0400421015203400329402e80810340d862002011079800180146101745814034014206a10380003070508000755080341d000025000300c018014460400c038400000c0c800148032140000680d0100d074200e600b1945070311100301610752500071050003409926100d01000b40360a5a80c0c10710301e060701103141c0038042c154105001c02c08031100642d1500c210f5a1403041500c0c0c49003003000c0c44508032455030004200301d0405848555480042c0c541ca83c0301110103216841d41e603401e2030200e140101301c40d05540000c01508101e14000e80c40c50b00f01c44410076910061902070003103560307041003903207020b2803000080c031007100050002103410b8003080c1c541c0140920201261f40010150b03d4000b40d00074000e03001003040003000017034803145d40ba074400740e03401d003020b820000d40c940c1c0704118100c4014400e1105c1410340c0c44079080b80c0651b9102001d6180a8411201007000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629771258 1250 629770008 629770021
    0x1e0715140c0a021002011406091012052802090a1e11040509070c030801080604050d03050a090c060201020c01060509010b03310c050a090212070806060c0109050102041a03 75
    0x114415154040e00480015006000e610140b040380c50041e0040c200102191400d9002402040480c00305c1e0034034904103001c00c00341d03c3c0c6a415075002d0512201c903040141d04001c5070407900710581c08211501d20034a4425503070460b0075a00862405007142c500540b03e0041c3c014010341c1c0c1c8000740101401450401c0590349044804100f640001100030300042c0004d40c0c010002d56403280350070850380308030324508015a980d031040300c10280510075a201c0d0700c181d1340e440b8074540e90308090300c00605541005046010403446175000b287d01101001c00403800080c02d80f203149040f0b4030381d0407000040c0d40006680100403030034000c0308028802591000195803406100b0252030101421000496203801c5806902007684400d826403203824403100c82c0b030507d89181046440d2118802d0354014046840c00280d40e444501c00c0e1542030141d070240300200d41d1020f208980001000382550b40c00070060005107402002403081c0c0008070b102d2000165a20f0900d02c100c0c0c4030000b07040d07599048940c204100f228 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629772508 1250 629771258 629771267
    0x5070513090b0111060c0405040b150901121107050f0c10021903031d0601091a09041103030f0c150a06030201020304090b04020d09150b04021312020a03051e0715 71
    0x48410500c0001400018540104c0c0d107100f440c8140070040c41074505200326204120010300403502c3c200c40030403202140d0400d2041103903e00e4560104d822082c002c809049d409081c0c0350f14003d58045000171490f040302d682c0c151039002800259050360100f050300340c0010041081707820821088510041e07d8041d442e00a6030b400d0304a20500403180c0c10307805441014041d03009607246145103003044a00e2401052040e586203824442e01e480b403800e0145001000c10040e503400d03040000608515403580c0e032502c1d000c001c0c250084256815200402070703014a0300d4480041c05581603618050403a0325155800030a4010001d0000001c0c6490b00380e0801c0140e800108440232512542c2010400400306000a0020300800381011050350400c070284040150b82507045d904054034640c1000071078510410f02c800c038000d40344007400048000b00c0500140030000c8004a0301c5100901c01c1d01110b403250749050524015240c01130340c3e00d06040e0303031114400003401001c0217060541201600111503000090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629773758 1250 629772508 629772547
    0x15050114010c140d020a0314120c0c070e0901020d1a06042106090c05030d0923030313030302330f0c0c01060f1a0403050d0f0c0507030f06050705 64
    0x40c1031000207201503080003421100b807000d071104031043c4c0b50180c1100da0003946510140c0001c50001d210004000c6000f102c00c003c3e2840500825058040c55031000811200c580c402c450182e01c900c0b0315040007601c00e41d0030340e1007842000000c00140e00c45c02664052415101806205402c100c0041808442a01c80409680440b200b282261f000e44400090071000300f05009805412541004203d40034024000380312811210250100e41002148240489008500e4007503002109040c1003041000d03405400c08507482c40004017138078600345110242342c2c128a100c4d4011030140c1c010304640c083d2100b035070301030f044440031801030448420b950811684906034004c1090400d8000e210100707102d01030042c192004440d403180200101c588071031113001600c29034416000d8003244028014280402039003580c04032a03106004007081c1104074002d860242ca0701101c2c10801a000e4110130100d034007049104000d60044101c130081040c5d80c1446400d54070014186000c0c09000c1114409412482a058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629775008 1250 629773758 629773799
    0x90a090204030f0f02010c0c080a031106071e180f090b01050c03040501140408010c09090b040b01050d05060114071203140f0f0403050f04090e010e060717060d02120a150501 76
    0x101340c01c0507280b0060301e0f010400c40e0050801c1d6440f140c003180211001417415055806074451b0300c00d1070038921096680303c00455143d0b0005522600482d9844a0340718240c8810000c2d081005034804c12003200744140701c1030351012500c8420710b001080300745101c2c0f05004c10f01e00e080c81c19071b1508900690540e5a4400e41c800c06042180b240d80c0b03100e00004d842e090701c010300030302d000031302103198048001444404a07028820003645001d01e007072850f01c3d00748104005d40d1010b84816003410b44a100107001818010b10b898180460185060100c40c4550001c0109601c00c0d851040400c040200060866110700c45c51001c0501150900810b504840440e550102071503ca04125546501e81103890380034900d000140380c400401e02040f0024150405000e22118000811401d400d58040d55074410043d00c00001281098103103603140d0b24458000c07540520f020b00f0724041c205c0345501050144c5440800f80300c0c250480804801001030313402c01c1403c00007141c0e030140001d50410440d89020f15802002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629776258 1250 629775008 629775023
    0x161a0f040b1810050a090210023007020a08030403060609200c0c061602011b030e0607050c0a0b030708090106030b0a0f060306050108060f0906070f110a02090a02090a090204030f 78
    0x4125844100f00700300a516540b03440184024140030707a144001d0301e18101d0480c420349220741304100c024400034500824070300c091092203440d425180c01c01c2c6018118040b1041ca600104008070246e224030b80580b000f482ca01d001556200e15506000003214415040001128200035110140c0c00b90510510003041d43c917071607981c2c2c80d2031403030340c8925001072005c4440d0080b80200703c0e01c41c51030303540072130600c094002e8844019a894030b0401c2c06445204520080100d00061031414039814084045d00d0141d20408c1102c96010206001030000000c40c0d01050140c800001003001095001d8080c80d0010010f1009000050030343d03503041c60b182c0d8000d04120003e5900c03a00400081170b41c0e0007410003590003900c100304950716400c05a895850441e00d10740300d040200045070504800082c001d10940f8940d4a0454003040800c0484a0801e803480f040721610449544c0c0003da41c5100741c09006003030344240142c1d0342c51440c05000d503600f600e0b840340c40c40901c1403004001284206c0c84060185601542 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629777508 1250 629776258 629776291
    0x15280e100b0421020a080309010e09090601090c0c15050a11090102120306060d1503060b060703080c0901121401061b11040e0f1b130509030a080705161a0f040b 70
    0x80143c000e10050344069440907105100094080e0040f0003418040340030b030303513603c4003030341001c144050071000b0ba8590002d03512020040291420550298100881e5840d0540c821000c0d83c440b00030300705c0b4503a5a40b00300d540e21070a00012680600c01d02066200340c1400f28108221000080c0d281c03051407081d801d040d0000000120a0341c1c0d500103e038800c9035100300c200020300141030721a090201d41d00040710038520b0903006110300d25140b01600e0b03005902d40e5450b42c20340d541c000e05003d2a041031012605100c3c1c00c802d03043c60a81140034141144c042e41650092a6141c104c0050041030000f080540c0000d003440120041742d11040400d43c801c60554020820079690015240390004010b402c030706a0160f030800100c502400200b2520080c4201d4161480c02140e00c08881102c1064528103103507807081002500c601e00401d4425440102405d06c181000c1d400c10842c040490b0006045400030040e6209522015228a0883d080240c1c2c52403284586021380d1800180100078040c103045044189 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629778758 1250 629777508 629777549
    0xf0323070b0a0e03060c03010e0a020705011b0e10030c02030a0509032506030b06030709171c0c0b0a052e0503070306090209070c02030615280e100b04 66
    0xc038034001080181c04103a6682c000601c01004800d0340c2c01200e100b4083c074008a024080d8a100381e90581c0c5044159001a450388a0608002e40c00a4421141c0e0354030381c4d044d00c03404402c61100c0244e84903184c0343d28505503580000c00c0600182d001d5404141458a803014000d02d5000095680d4000c49040543d030703402c5000002803919842c50350380c503004003a040208401d952400c515108490301c540701032100d4041300e41003000034041258440f0000d886c101081000d55942900840c0a944405c161a030b10240c0801071068516408204c03808180b8000c3349c402044110000c03180d1062009204205606000a014103641840341d03400c1e8501d0703c1c915005180501e8050750340000c140c002d0441d4990b950728504000a40001c4500784d2240b03c0a8000031440c0b40213100e50040780350b00801410141e5104a0303581018840030010540002c65038001c96004840407601c08086e2540d1400d441403640381407403504400c40700511031304024030b014000304a210300450135942555120680c04c403545415a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629780008 1250 629778758 629778763
    0x1180809040903120e010e12040e040b04020d0501050109051603230606040906080610050301090c18060b0f07020a05150703201b010306080d050304150e060a02130f0323 74
    0x684e01000c507030b242c200c2c0140c030343c40b0560010442031952000c2d200080c09200714041e03540514402d542d031740f10004000400190503840d84070303400744c80109400c1c120002038950360700316a0240c0180312140c0c0d8a40900c1128681500d580c0c8034044a4076080c068004100625042c070610318100000c004002400b20b0502c8c1d480c0c2c000e90f405007034104000c0184907a505d4800d95650790544084085880425000c1414101805010710312900015004101850030b012051031840004102115590391107011503240648002458a6100490790320f460307100f0350040101e4400c030356000b24801d800414010780c4120b0603d00703840a680e0582000d04800c01c05d1801481151020200c0c401c5901400140305803c0844040158007e1004c2e03804010643e1a00b034007542d01c400c4440b8840125200b400045d002592a03005543c010010b4240410b0014442412500d41a4181c61400c1c1c0d10703401150008801c0b2081c1b9917035006240d480003402445166031540340d60b001c0d181d1058040503c0700d114001c0452400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629781258 1250 629780008 629780027
    0x120d0e01034a0a030c020a050d21050c0d051e0c1c0e300606030703021306050907050d18021806013e0a031407060b0402030103060203060301180809040903 68
    0x50040e10000c00044c903005240c644614422445446041c00c08103890130300c90782d5403003110f52020704c0c044a4004e9010f00e43d81c5041c5003c80342c0402c04108640e040600044c886511010115101c13143c0b502c10346000d4010074650035071400c3d00c2400900490001e200b0024012840025440c8500d86400000b507044600d03800003104d1039000002c90052040c0400400b0140000d403406078100070108014610003615550161a03281e89688030f500184090301d0203a40322170741148091000103c06503104040740e00d44200710f80702e02c0801c0001c59070181200b92402084000c100c1c0d00501c150700505980003845401d00c8a4071844ea00000750000360f426401449104240e0312b855001c0b04071610359070081c145131001548180a035600341c5061107060000018450100c0e0fa16440318010800c13034004a44498010102c01c1c0c0c1c1c0705807100c400e5202505e5a1005501a502400f0003513a2440c105080c9425100005810186200c9810300140400c41507400daa240c0c0104440c0070945407118102182e52160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629782508 1250 629781258 629781401
    0x2407060507052808071209060c080105030f010203130311010f090501020d0c110d080c271513180f2a0f02030a0e120d0e0103 55
    0x945000d000c0340c50b0708000030302404145200d51180140c8030300180410710741100041000b2900f9000411140742c010100c0c01a0119610000035409001d0384a01040d50703401c1c276801010451800050101d410709000e0480c170344440c81e0081d417860038598540410160326400c05003c1041c54481c1e015102004c0d009450341151121003449a07089034148507000354041280007070414689018109400d0140c004c4c0c80c03201d29600b014200340310009805540d14240104043c1186034100940103030000c5010750b1076040c1050003041a031140900c001d2003811444500e0b8691162400c2c0010b21110b08107405074802d98804041504411292880c210090141da40c414080c0ca810a040001c0c8440c40410540511941100c008002c81041809680c5411804d11020040e00b0030414100d88074041e43c0c11800c410f0303004d011241d01d400a0130441e4240107400010703d0014200d001481410741e03043c0559031000b0342940500c03030050303d500c0c0c00b00710241003060206082440102410341c0103a212070010100030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629783758 1250 629782508 629782511
    0x3140904110304150501050f0a0b0309150702060a0c0e1c030332010504090f0615050901150e01180905130b04050d120c05090918030d062102240706 65
    0x1080e1810740003044c440518003000c81d2402000240c2c40c03400100c0c49140b07150107420660801c0c20803110345082d41c001001c0500e984210380d988030b05803000032135640c42142c842d806064141018a0054291810041480d08009850a10701480d50f20509040012208241400c500c3d8000b4903040e0080c0c60900c54503021b8681d0600115062900950b0f0f5500c0d0ba0031241615159a0326003042000b1241c4112018014407a5a02e00e240007444a034004100407060403402d0381440da441000400381a0300342c11003d0b03c5140071074410585a000000103000c4c00f024240043c24010641095400c0c844501c5501092910b82022440f8045030303c0c1003461240c0c100024030792926040c02c15959030443c40b1140400030300b01e200003d545400b584034000030303081140d8500c0d14218156040264104018100c0d030408401003101c000300080400081c10000c3d0703141c00104601e41f44c00040800040d008600108071070308400e01d040140d665403941c41c9821405811046c0c8044400c111110f1806000802040325 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629785008 1250 629783758 629783761
    0x108070908011e0b060a3912180e0c130b040b120c0a080c0c15090607031401030c0314071505032202030601050105220f030b0112031409041103 63
    0x108a601c00c003c10b00c1d01c2510302400041c3d80d49007401303424442e4100503000986a2220060f80c001c0007001d04502002c1d04000175001031601d8030701e188821159104a5403900d0340007d50302c000e5003000400c143d41120034070142c10146844201d01c00c4a0009102003118400010103420781c41c502550640030b046414178075501c8a868141c660060380c8159004461040880002214481d101c4115001a0b050799100c4000d912608082c440300e4115140444103400344141e032003002ca0742050742500c0386000318000c00b450308015402a089a52099099211206000045c8040352140d940c2c07804803903011101d40952150103c0301410100c10b50402000b03510242400d09590398000095402800000d02c1c040701100000f0600d841e80480782e6009426802c864010000c540c0600c0103003110420011880d01610503041103808c1407282030f00081070740c0002100a105110f10888140e001d401c2c5c02204000500f0f1645029110104031141138101820008480e142a00c542e001115030720701c4a504503499 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629786258 1250 629785008 629785031
    0x10060306052d1306030c0504050f0c0702190504050a060f12050c0907030b03100501081504050a1704090f060305070602150a0507020a140d030b06090d02010804020a05060a110615010e010807090801 86
    0x2e8006e03900c81d15118030300b810301041c5014000c1c0031403405211026505c45ca41101307542800901c3c0c610301c002e0800c4c180c00c40c4000480c0c1e116405098402c401500000500905040c0000d85000050b04060b22842c00524440e0024000091031020a00115100c403510791744c00c503084015200c6248825010700410200580b4401c49810071030503112018140c401c6c140014011125841088402034456445000864003144078183c40d078170351aa410f5020b030300e003075100c4000c1c00544139403c82c499045030740d501040051010910941c0040d201900c0a01540081c0c59070740c44003164003411a155841d03503040400c0c0c0950003003001c1020680c1c0051004000c0c07042d1052a5202d4135000c8062012900b8021499010300c0c0400c00c0301c09425000f80074074594100b41d0011262108010030032a08021f4941003c2903076038a40340a00140f070000d90f1041080d03000c4280090030440040d18405a00104082245149c2e80102022940320340a2078030300c08035646c3c0481141d00c942c0035840200c0b103503e00484103c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629787508 1250 629786258 629786273
    0x905010c210f0608010e031b0a0b160e0a120b0a0207170c070320091f1401120f1e11030a020d0209100e0a0602150721020310060306052d130603 63
    0x100c1140c103410745024030000300703025521036180b27440081c4035500450010300001d00c02c0e1120080c0288601e8102e160040000105c1d02000458110710013068000210004101800c401c0980c0941c1d038000a505040d074540c0d4418980000701030340c00d43c1d15400f0468220300030080000ca4000c58000040c1d808a0220080c00740b190210400d149004d00a48130015001052205140050400303980c248a10a07241c10582c201c1c2910b031014440c10405618686000020203001c0c0d26040c02000d02c000501155101410000c003004000030400141000504800f010035281525802104003201607030320184140f842001f0300c20760590a0744100c4414010142035801980480751400640c0c040303c480d52503440580c0d0300d4207020300c542852860100000c01c1503201e081300d90007000c020307140201c501003030301c800c2016a08100e40907407241a4003001003280651500a2100522080c1c1d4451000300002040ea62030703441000c4000c0c55100e8040090495845400e401d249c440000601003044c15101c2c1340049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629788758 1250 629787508 629787517
    0x20903120414121c08101805071107060c0308070c0b0f0702061b1e040b07060e0d0525260912010606020a0b1f090905010c210f0608010e03 61
    0x103000308003400c1075141d0440001401c4c10758052500b5a00b40100810004560006004000c0a828150440009032101d036004008048008080000c1158641801c0040402100301c2104216500c1f0700c80402200c0d800040807141150107140c400e442e0350311820141c4840400350801080d0118a100300562440342003009401111245c0c25207901391a06d5916518002c03480341c1400381107204008001c800c60740116116400d9010072000307400c1c03964450a10346142c0000c4015502640c5510010b2407425050086800102e102e040c154140071624502c204076545040c09a44440c50b204001c0042c400c0002c2010800380c075200d05411941782215080500b90403240c1c1c66401014a1050480d0140e018005c07003098900c140e00034046104252256440c442d4068442e8944000200c0610030020f845004900900140c010124001c51145012400c46691450140411038800d24140d4002c1080110504c00d0244030300c00300b90000764681000043c0760503403040426610b0f00030800c46980c030101c05030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629790008 1250 629788758 629788799
    0x403022806060b0f2719030b06060403032a060c0f08010b09030d1202070209100302010e03070e07030f1b0c0b10080307061d0609071502010b030604060209031204 71
    0x14400300d5a1280302541e9406110030140240078180560360030003a462802112103112a01c103601c1480400c80811102010006e8840d202c0800c0e03201442030002d203a42e80c5030000c7c8155452458685140c8009000468244544080d07642803201228078403601c0100e0301c40c05d5001442000f4001c0082405091100c850b6589004200d80d03500010300d9800d12803d0b60407505014001e004e00d0707088180110750f640203900080d2100b41c1e081c0701560160f10740c6118241704035440e240d48080c5d18154000580340c240744046071842035106080501000710745030842e41d0821000c0c140850551f40e00703a0600060f0480ca24402000e0041604c2c45003069400801140c0c62800783e80c4010072612020005007914203c1d00440c400c1d503104003c9440043c00c1c6a00c18040d0840c954640e0103440035450446040110548100d011075208a02c103210b44000f401440524000d140000c00404000e0400309440f40802030028044170f5010a6594044c0c800348041d500124039a00c255540b15100c0c061980030031b162321180c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629791258 1250 629790008 629790011
    0x90308030c0c0a121814060d0e030d150f080d0c03080c09030a060b100f02030909180607030e010c1b080a03060b0d02071a040f02090a0b0604170f010c170403022806 72
    0xc0c20404a031034124003101c042d0080e4036220400208c040a06141603624416201c20001004450340c94170811040d0313980e8000c540580c0d0b1611082c40d0151480d5008a20f2a41104465a000a40060980c80c200c5c0d03160800032400c0c0c1c1d55882494041c06200d85498042c05640c1c2c0c58000c221456202c0d04420704211150720b101086520201c031030030b010010040259204001c40991480c1a0306055402451400328409404034803d000307041840c04c0c6e541030046521460007004c0b0880030b001d140711341c203050f20384110550000082d24080c000c1002c40a424014000b03505203038544a50001ca01600c880050943c2d6014020b410100940c01070a09440d802d5004070f84800801d501600c0d40e0155400043c0c812207580d042c2c081101100c1d020f0840036050b40d85450340d40598a40c2e001600040900b07911501c1a90300c825007a0b824041d48419139040741c0d1422481079480fa4004018020f4106880100c14495846103030aa25000c04201c0ca107410b48034550803694000c0b012840d155199104040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629792508 1250 629791258 629791307
    0x91008010302030615150f0403080d05060301060b1c0e0118200303030f010b1804150e0c0909040f03091d010512070b0f0a09030f030519090308030c0c0a12 68
    0x6865105d40e0008030039070b101c4074080800314210680c00140c80d902103130b01d00440c41e1940e00d80c2d407008164045c00c880c02400717884e02c003000b19604d001e00c103250040030120007951405904101c401207844651010700085a55000d086003040f0b0b0075405001c6040c20510715130803880c0e1134101400008010040000c00310031b00041d9000d41d00f80401681d0003103520600224469080422141079900003608149681c0310100c09141c0f40e40d15400384000c45800c0060040c1c0d0316082030a403079608640202000020501040000e555071902c180c1544c1c030035040004a0001040307403030116125900c07613102603404610309141c151080345c10007549040780d80c1100c42d0b82c00d421000001e0707034940805106940310300505028840440c0c020703500404038a8171f00e00e00740b01b44603141c2c1e8400003c031501c040300f903000030004200205034828104242410800a09064041505c0d55a03542c0c51884020417034a1820808244c0d4180c1a104002001d1030b542c1c810401885902035010003010405511101100c00180e400e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629793758 1250 629792508 629792521
    0x7060603050f0f0f0c120c090f01060201180822030f05010f1410050f03101404050c1f0e040207141506010e09010b030403180603020c070905061c03050910080103020306 74
    0x3551320810f240314400b400d5203020a4003040300302640c892030342240d802500f032404915510959201d00c030758640c0030424615410440b009085404883c0c5d1081210030b80341551002ca900316058624490031280003480640030350303000038507a1001e6440100200600c1c40c10604209064104100841040504020006516203400380d4080c0943e001404001d00c04001e0020707040c0785181c24180070740a4101c9000c1820f840344807049480400712010451806401e01080200a004080c0c5080c1c1c201c3c1c2c4118a03262005070b00e10040000340701e00702030088078041849103032510f405581c2d140340c11201c1d19036914086c2c002c0319290749541740030000744c05118000510640c0244008445d066020b401d40007582c1c00d0000101c829400540b0503000e010300c1004104d204d40d8034440e01d03405002103950260301d450a8910143c40c04c09036801807a001410f103020048661944850760140d901004000c0e03d4840c1c0508040c0c9007449014601a00500641c844031040390b0020303102412039100707900305e61080e65641e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629795008 1250 629793758 629793763
    0xa151b03060b120603011112060a09140703020d140c07022404030b090f06070512010e06090a0b13061d012102060307030e071814090715030207060603050f0f 69
    0x5010b00b0ba078821040c003610414209400000350f004c000540001f5001480c007005110b5a0408100c0e5a09064a42c04104440c1087d0710244000c205100081c0810044940783d801e41640080901d41003582c00300b2040030114450b04420800d011994031400c1c5810540302500b0140d00c88072059000b8014080841004103400d141c00c05440045001c1070f04080c2503940d2140100f2020f4030f017010a02c128109201a0b6501780a81c50141403540c503825603582c201c040030001c0b01c8050780315a40015400040241584503e0462a8000000c240c0003603e0035450000500c4610403c00850a5034a4004089901f01d000704096041f00c1d03200c0b10a56860380c0e18655250101c900d013001100c6800d503001408010f041006c09141c01821508005c9280c2c505078843c2440c0802a910500c0150768064071207a03012261300c5440f101c400b80d140d64140034508808000e50380c6160303102d20740c00e03000c410103c0400248a40d040daa2416030016041c00003507030702c0c10403668998404489072301d2070151000100101200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629796258 1250 629795008 629795021
    0x6060f010503010911040506031515070f1118010f0f0e060a054005090a031e0509030105010b0d05010e0f130c031a0702070b070807140a151b03 63
    0x5940d601d10750f0f0700f0441100d01410007170004110400302448080340c1a52030308040d51081581d551002202d4030300b0b03000c001c100003600c070302c0301111801080760f000400e0324064110b0b10643c21100740c0305a560300b0004039070300142c861200b600780d60604001042a5105204120484422440c000640786d128403071603500950544209030b0021070390804210b00d08000c9120090704e1010040c002c06500c14580c0c00c02c1a15000c1d10780c0c007284658071606588901c061148542020120000384070000395644c02405482c14006015054070b004102841e955104000b240e1000c040030b4028440c0356920990741d10190000c99040b007040d420400041400314000580e14070030300384142d0001141d207074a41c10409104070b0884c03d032002c0da04984048003040a03000d060030151150103644400e0b1400b804000d040c18490340000b102000100006c0020850340d1040e5401d140c1c120480b80d008039688035032545402100302c002403290407014002c0b0645500d950080490203844c88218940d210112001c4003111071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629797508 1250 629796258 629796289
    0x6120f060102121c11030a0f060f05060319060512060402030d03020f1e0708040b090a090c211d0706021002031905070909050c04080f0c0d0b04320606 66
    0x600748000d14410041c801c40801c003030070300c0c600000c040c0010140040c4e1541b04a03030103039038282c4032000c4102141c00c0b40f14100080c41058150405103040000003032451001400c82c86030b0410643c0070000c0001c07194010706c010280105000d0a500340c00c20040d4035190101c030260300c203019003a0ba10302468064003c40d503801080c81d078078604d400d01011201d4000800c0c010308a0b00b003181803068800194014008202a2800b0400280c4861013030003040409840d0ba000301075010b040c40da141c00c050742c0100c5540442940c0030492080c2d544d4400b8031b0001010788072003568018907a45041400850007103240401c2d0380c40e503801c1e1440c0302d020700d86607130980c401074540c90010034858400032003991155001179080101450711007d040d42e5007020f0001d075801074500c2c3c8843c1100142c04c102011041200649807034405001c0c105081d0b40c000051201340c0c2e885c40207000c18a4000c001400c024002c01403001c0000481e81002d44903402d07294031203081d190100d000070580f0900c00400e0252410030784402c0407c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629798758 1250 629797508 629797543
    0x2d020c12070f0c06050711040605030d031802060a030b030615010507080c03120702010b030706020a0804050904170a09050906060702100f020a02040e01241a03070e06120f060102 78
    0x105204008a0a41d111460a507501c00440802c0400030346855482c000519843d5210b03603c07004d09050021900c0c505005052241e4a401410482500d0100700c0d110f150202e420f00040c90f10594119a17149590560029403091000030020174a980552100703190400c2a02152070360340d115804032101c021811341060104000344440400500b5100c010100b4a44043c1602c0c204244029081c10130403055130424003507519541c00a4060508010b120010030162008104070011505c1f0b5104500c41e60281e14000c2c85968009003d01c0b0500e040c0361003200c000d4101c1a903035051080010116180c9000d421b205904c00004113000346000070540c2d000d9600207050410304084940c0c20358000310f1002d05101903020300000040940d40302e00c50002440b8980001050441401c0c1c20790f845010b403110000040d4581d01d1080c8401c031031000e0345403403000300c03040f4640d90784e280c51100b07461450142c0621070b4003410000d80721030505040e60115005206005160700f40b6142c207401641c468180a81484115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629800008 1250 629798758 629798773
    0x3040204020d0609150e0703020a090902090d02030307060e07050f011d03010b13020309060601050301120b040215030a1401050913060504080f03040317130f1101030f2d020c 76
    0x1031a0690040c203200c0c610035400180340b996040820180c0714080d005604615800c0d404202c82004008186d901c81c0030fa00e000c40ca084000703000a0700214241c01204a800d0340826070004a07201c000d0100c000c6a002011241c6961561a2450141c0000d0700c2000c40d50141d4100042c060614202c23040341e20005031101180e0318981040030405141400b03817294150340380e040200440c0c0340c080c2c1c005802050300b00b0160f9a4030744000c3c00c40c6000c0f005080c15040120400c01084414010140d14070303120740c00280000d146e03c81d03000145105003117203402240c03510300109000c01d11419a10442030240312100140c426a40c2d10108228850110b80d600d4040307820fa620302c1e0003c0c40075400642d0151003000b010b810070146401d0440990405c42c0c04401003101c501c0703c0c10b12144070305109a44140817000c940c1c0040943c1da101000030381d04810080c01039420802038001030307010350000500c00100c6902040007594040c0254412403c042c42c21076441d0380300c440c071810807003d4003c82e401c0aa81c10002c1218 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629801258 1250 629800008 629800013
    0x1707092007060b040f020703090509090705062206050a020c090103020f1003020d02130503160302030d08331003050f011406070503030f0f0a0213090e1f05040b011a0304 74
    0x300e600000d41101e10701d079a200c0e001401d607201c0c822a802e04001210050711104a0314001d04001c2070341c0c00075441907085600300700d440d03000010000c0a03a4425545541c981088000c0d02810b841d5249410b403200c00740b03c2c000700e240c0d03a00c20702034140400243d0031030300403101d42405d10245000038007000c1d4103c00740300456959810301d86900400908a0701e001880d0000c0c64005500703e81110001001c00c85800b0b42c108010300d41000100c0014890b42e402001143c555030000b55541d580c03298206c1400f45280c0080e44203a46290710400030000d03031190646a000022040441e0001d140d1224403c503841301c3c03100c42081c424070403680314143d02600d01000743d080002e42d1118440c1c0070b1920341e208400300440d2000810606c0038500614075000c80e035990b41071065500118207402000342c4009441841070344041d20000026404403403601c10001009a49455802d0a29805511051303130f040c1c201041c80b0104110b503002901c80ca001c0d080010b03150b41c82d50610b240810380303c8040704401030700b403020601 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629802508 1250 629801258 629801321
    0x50c1801141c0504140d0c02190e07030f0f150b090a030f0b010905060609060a0f02100c020601140111070b090103180b161e1404030507170709 63
    0x2640d01205403801d05041540826501619902c2014000305403070344240003c2204080490807800030b2003018000a00782103000921190030080e0180c41040d28800400701d80341710506a502414461503802441d00d46007102a0143c10608020b1503071925025034580c0c0414684100601c00c4164411260410728244105810740c01020002d03902004034640000003070480c108284240e4807401d0005419890111f038007003101d800800c0300e4041c4408005640c01039a4010807200c5001c030320b003822100c80307003000320072840c25006850b500f00c03e503d0280a0018280c001a5090490b44001c0582c000600000011a400c050a50400310582c3c4490400d009900c12803003e0141250185000100e4032258a024189007983c90426070b070407040142444146a20a40c00d082d8200c0c15003450ad00c3d2042c0c909208500941e0503035074604024146101800302d072407500445004540040c12503103c1920740074414003011889440ea400c40c4602000043c1c40b580d039003e215440c48651501c2c000c2d0800000e026113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629803758 1250 629802508 629802527
    0x7110d08040c080f07080105010506280e040c0507060e16181506170a0b130e030c1006050a06022b110f03030a0605030615010f0203070c080604020103050c1801 70
    0x94030030150b000c0108420408000d03514074003900c030004240701450040d800d400c4610680141c0d00481c0d04100d410301c03000c42c109504501e03010300c840b2420400070542c0100c5003540310380100c41d44907043c0007503400d04039070140c003600c280340c000e0500f0000c3c44000020b15030750303a41c8080c40c6c3e03080101048080026040352842541646d0303900e407007c0b039442414512282c414602e6000b01020880c111007a040308460300d5003da038086810034042041c84d080b203000800c0c1c1911038202c2c4a8a5481d0407400282c101e060054460700720419007140e0325000b030040300308042c2203140681d9000e541810000100a8400100300381368102d619070524900c000c4e031001d6580302940903100030500c1035003400c01c030001004200c40540710105034061601da060034407812003500c0c442d80c091442a881f0402f401603d0300c14034619040c42c202405e20f82400070959400b0b07420f6006c1c0300d002408842c12903000080311100800d000e481207100b40d90030459941c40760b881d20b00740d0080740001041125010000f520a500403448807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629805008 1250 629803758 629803763
    0xe0a020309190309090501080c0f09070c0c03052b17130209070e12030901050d02130e040308220f020f01050c0f100b0108070203030c1c0507110607110d0804 69
    0x1c44440c02020041059000342c288110006031000c0c10802040c000c81c0308403800f60007200040e0490304110300005030088600c031905403007030340c1d4400480c1c04a40191b840030f0125030b0120703071810481c0e603904040d41ca80e00385104451040d220900018503485c50080402c4242e4026182d031b00c400a5216041066003100401c03240c03140a261010360301594800ca10a0310030310940c1da5102089445500f0300c440b0000c510650705181c0c3c003d01c64907025a070040f003030b42c4200c1d100104c0141c48502d1082c10000503d115884060690a440c05120516031b01407400d621544090192400c0c05500000c44120350318549009407103071039054102c0006191049001a4800051420304c3c00c21160100d014102409501c094005a00461202035004114012030b9130202003400c00d8200703031900a601948074400203090080c014000180001000700602d0006240c41307500e1001c003d107103809040034085d02d21404000b040c1d8400c1c80006031130389124022080071100442d019001c002c0c00c80034103403400b46028004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629806258 1250 629805008 629805013
    0x201501603110c1e06100308090609041d1912050306030a0b09010608060903040b0406050313060c2a0507140111010c020303270303060d02040b2d06040e0a020309 71
    0x101e401c41000302510201000f5005026003903045014038907101015010740318260084000c1003c0c0c40c1041d0320010403660800941591141d0f5500000d9980c440d0035156a032080c80e148100046184540c0c400e010031581004403102c00e49200150302e00e154a544000b07003030001081072030072110b00c207402940c2c0204010702144c4041410790b0307440e9044d03202202c2d1741083c0e0390f4814080242002c20041e0a400004a0700954a020300b8580c1180c2280320740d000c0c02040c440c1c0000420020260315403400d60841e004942000010b8801e0360040c50b0406078a2411024a07170b5908100007070015803404c4511590042c0144040c902c1c00c41c42e502c0c1c00c00ca00c0c940a06003e1408401410f0072420702030031321b0241451b406540c0d02d00d85201c1d44d04c480d00c070714004082c0040389254000503c0d00000112508200d0441d0740c0b2105080c00d10000f800b4101040c041d5400032107007401c5c0b2200207400d401414643c0040c440161604840e803040c01940d00076423141e400406020408100c00300d442ea401550061015400e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629807508 1250 629806258 629806271
    0x1802040303180f0b1836061c02060d020c011b031a010813080c03121008060f180d09030c0503030c1e0c03031603080f01050f100201501603 61
    0x1c0701031040d400e00c82e4020b11b40b00640e9820a01c003441192100303590941d21221400e0640100c0c07104c45112922802ca98444444d480656841303030160303052140381e82000c0d03607500c0d001c00b001030203080008026095003080d0701c1d0b658051342c003d0058440c3c0c440c07a0030000b54102002c00c0110303442a000b030700c1c5240340c41900415101041d42c0500806844280b00011665019040405224120028892000c1c011002c9080c0803c10000c501540c001c56940c41c01100303601d80840800c241c519000c0005141d204801d410890b00340c011f9025401c0f0fa000d201041c0200e552001450344078452003c4182451b08000c0c40c42640c10001e0a1340700011302000d044500610f0804c0200389140d0014624100508200781d030704040550080150307504c00c1500d40c00d6440e5501d084003044803201c485140b82e11400320b450301121650300c00d45c450a5030100d41c201c1d0183e14280312200c2300c1180c0d008030400c10700400d885080c0e015080850f01200c0780c10310301103104000b40c0d80e000014005010010480003010b40701d91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629808758 1250 629807508 629807557
    0xa0506060d09080c0d0318060c0509131d061b0c0a0209010e1803130506071103070f03021e0102070b0f0408030307050415020a0302030d020705071802040303180f0b 72
    0x2c2800022442038549650f10100303003a86625005000c8880d104050030300c115400c081c41048030010259500c500041600369180d03030280c9030703400b070ac0c0d43c083c1e08402000400c840242d0b0f81d400400080038010300c02942040317005c1509442d41d0b41102c12040078040f00c5518070004039841c000b03011118001e000c0d11039045131540000c0400c5000c1c0d01c82108012080140907074031460200104680040400440c0f0b0188065082107107000c162081e18402c1740c000c44e410091100c0c030840c260784d011000741074405843d15040e0b6510020807501040c1d00900306a0324040e0000300041c0178809121058005044062810540c4001980003020346c43c8800c10178040003481800400c051401080b4684446440340c0c105480003906e40c911600ba201158440580321000c250080704986405180610140e604c030140e0030160300e42949540004c0011001240149040d8150341c00340c07080d60702c80da131140448600c034403003030202104900441c0310a41f075101040101e50410401004d5506141008660150700300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629810008 1250 629808758 629808761
    0x101202070302030c120c1005181005190204050a030f0c1701203402120c03011b0e0915090412090501050f09060f07050613020f0a0e0a0506060d 63
    0x12802107026920100d0003c121410600030700c828440840300301070808207624191590303400b1000d5a4407145aa0382c0110700b8007003414201e2940d554150b01110484122505100300900c4111034005d00c5070001c80d0a580903c5050003250105c07030300105400104c0f0b0858482c8003041e103009001700d48440407414000f882c82c2d0240b20302e0307180f40030b000c2c0001401c0413003046800991940c07101820300342800b0000500034118114a00103001540c0320b800a075441c25522602289402010280d4040c0ca4084c96080050000035080c0e08520154000c2c01802a20000220a40342180c0d405021409200240c0007600344690404d900c0a0300399540400c0d2030b100c0c8003181c580388007a5000d45040004110241a1640014107200200400c3c070b461460406141845841ca000300d0284610440000514038049016035055806054204003a6412421701c900c0702c0705441030040040b40110381800c03001c01c081c81d15030034a00c11a400707202020150341c0d8125074100248030080600341e00036001d210305407260009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629811258 1250 629810008 629810017
    0xc01090b160806060403230f010e0115080309220b121005010b03060307090911100504090b0102240915090f010f0509030a050d0633080405030405101202 67
    0x80980c140107844507010007000340304014851802210100b0040001507800300b0540f4040b402081121700d40f44100c100c0d107042c0901c40d44500090360815807000960b03c4c0642c0923401410b80186c52040746982d900b00e4030b80701e0140300d0308581d04c051020461a010f2420f500700c000002c00c1c903a000a8100100c0c0d001407071000740725120060f1944420014045542d4500c00c090240000d6080141545462800280d491120303020390703440181c45548640401000441d0101e620500804008800030700d10fa0080c0a90468420216810300f006180d400302d50010a03030607100d400b100b40410062a1140b18030b42108000f500021041c1710f04102c0624150f0b00900c001e004071482d502401e00d4038640c1d411301e400d40d0100140700d28207628000c280182d00d0750010850790481185c0c1003803900d81d4501e00700080180741c2688a01401d00c0008a0803440d5143d62500d03050800025107124114144003408480d4944105c41c000c0559004000c1480103140401005045481910340b4624020b100c00d00f4500f039800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629812508 1250 629811258 629811271
    0x6030b0f040b0702010516260a050619050f0f1f02060a0e0610030318090203010b0a11150a020322050c0307150504061b02100c020307050d02150c01090b 67
    0x410809101c208150500344030b030080a140300030700240c1040b50440c01841802070b50f01081c400503400d03900b40d1920408400c081c150250212496174075081601e540a0402100c40d04c0c8140f80030007581886d944288107100030748101904010302c0c4928001401900700903400584d5000c0d445590740c18100101030810015641c080d8041c080c40c0c20210405801d689090758071111541200d0200401c0310140c22408040b240c162405000341008040810304a40c039640101d030810b07000000210700e801d5803400800c4091015540e54600c50b54140b11103844400d10255101c400c24094003042c04614582c020315046000f400c09490441c003281e0302c22901c41079110040314a038000705e4103583e00740303400d0210b4002050010207440032080c030381200400510480c0078140030302103288402c050030b40c452440d500c400f640c041c107095801d8043c0c190190451491800880c0302c0c0c410914045001d0406400c0d0554003603018140c412031041c004074070040781e00204910801503607036a0b4800041000030b06424080e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629813758 1250 629812508 629812531
    0xd09090f0905011521030e04090305130803030702060c12150103150603060810021c15150c0b0106050a0c110612130302060705160230011521020603070306030b 70
    0xd14194078041781c010031a6610900400351004c07000800e800c5a000080e60300308850000d403c00a510b400c0c5c85902403a4003440307031005034020200350504004020340c020300e001d400701ca400380d4804510070300314892000480d0003801150041782004406c0060a40300f40c00504021401001f0300090710200c03150f59000b100000d89442040081620a20540002d0043c4420952400400e102141030101a00d1355818030240d03105d101884411441840a01425011085a58061000c200207004005487c001d50310f80082a0000032900d0254080390724010040d20b80080144080c4c1360400342c0c40c14038031004d4102400300519075940d2050303802e06104200d80c82c2882d9585401d03040080c60a0002800385052000802101c50000d124288140950b581110001d00c044a040d0106038050311080909150010f924044d40312000c040d00220080c280c00c0f0103401c250744d038500000da5030b0b03006030140240080460900364054141400290b074021000d044c0460426034a54075008420811141000840c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629815008 1250 629813758 629813801
    0xd06150c06060509010e0414030702090411010f09030c05040c03020f1b24061003020705120901030e07030f082a0106031104022106040e0303090105180d09090f090501 73
    0x102542c0302e410081c1c50242c2d0004025814030390a501415400340c8050500a4460a03035411000108100d980c540d170301400004039801c3ca480c1040601100e8440140031031208114a00c0151081601104490700300000c6d0502e20b240c00c00b07002c000d1004231211001c0640802070a4110700500c4000c1940c0202240c2107810b0f2288800c0040c10b0044190105111800c0090382c0b600c030100030041640c2190007220000242c042144c2e094009201e60100100301c1d00030194030007040149400580702d122402e881c240322180c030440d00c00e601d500050000038800520601181d01007241d0402900040d0b540c62940c4940e80514140c0104031500c0e650110140d82d1140700900403c0188554003030a21002e58080d8148000c502d1400d002d408902c00340140d0750710300c40000d1407036600c0f5004a02401200c801703487c1c4c0c908011443c02c0c0a02000c4503840310380c02da04105000c000c0b00c0080d221000b0b9501d41d55107412a42401a160041d004500f42190003036100c07480440443e80c207200340d00030840c2e4004004001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629816258 1250 629815008 629815013
    0x603070509040f0623070e1c0605010f0503010e120d06030507180c0c080706110d02040b0d0507050c030a1b060f0f0c02071406031b1614061005060d06150c 68
    0x2170f5000a041c880c4e41606000c14246000e90641072190040280e0a100d4683d9100d0380104080280c00d08600f4401c5000204074814840036a211a05882000400100e0a61204145400c1c0d403041c03182d42d0700a6204800c06140c54a0131000740c1000d9500c00c2001c07031402c5d0790340c45003490204250000d400c2108068030804100380d40e0306c00c040c1050182d003040e03005050304d40c55241e0b15000d0604003800302903d9203070f00c1150114500807500c4110056408540f940d858640e000c4c1c4a421440a54082c2c0f072405010030440c5000da41130ba0407003980c80300110301d04800001c088a0059540444029640c148405034000540f1806038840c000c0e01380e4000125402c0071550841a0760050002030299003009005100e1241001c1c01605103000c141d840d0750307507a203510203c4a00b450400d512a140e6000119120380f4001c200d02c7c0803004a80510038030100740c0f91301640c40b9103030403060315a842d100d900c1d03140c01c000a08000000d0100307080ca40c034001440707581d104610106511030030030820000e10703007007510001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629817508 1250 629816258 629816261
    0xb0408160e040804030206071103010c090303090f0b0702130e010c05030702061008070b0906190906140f2b0606020c0a0801050906070c021c0f03030b09040201080408030603070509040f06 82
    0x51460710640c0505051075207810324184100d01000c1d009101c00650038007801202c15400c10150780160007041710a6200100400d1440103000c2200041c24006001461102c40456281914088180545004140e50800a0444071000303244034054581c146101498000c0c42022440b011f11f0300d4095403483d01110003401c20b100100364000c3c1240c00c210510030100001406010b9640c0500125a10480710001031098007841003007403400c0034295a003044241e441000541100c0c031f20303290500c0c02c0c001c258039240a805005255403440c0000d1241402c45541e014068060f080a00395401c1032020340760030f40050b601103800200150740404039582090801c0080e1100800c2c101000b0031003403c03e41e40d443e03281c40024000004128848042d0010340d03948030b514070b50208a0010008c17900000d4038101c094070302c0000054020928041101a06060850170f4a20540d416954041140e446644021040d000505890b405102c0c110700890a9103840440c2c03070107107008030340d824031000d0340e440e0440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629818758 1250 629817508 629817553
    0x303051b070b0f070c0b090a122d050409020309010b010917100902060f0417010b120309240a0302030402090907081e0a06020301170f010203090a080c070b0408 70
    0x40003008108101d07000b04a219003402d400c02c0021622541c5500d03090800c4440000501014005020440900807001c5c2d000480000582c422911440240f10011054401d440d00302c030040590201c15001001c259452480100380c1e103800d050036400d00746c84000d40003ca0300708071110000c680d5546035440c0c3c1d940e00041c0d02001003518140f40c40518001014142e01e5071090b1880c4044039448256040c11561000140c8098541017a00d1344c0d19155107941400c0443c40e00400000e40c2e5182900c000a6814858800888c414500000314501500d0100b13100c011503035507050105a060000003501c071002c41d1030003010b100e92036035005078407400c103030040281d10032001e072411200368416001007004800c0840d10610407525890030f020b1120351050294200080c004009050910010002c14050306520681c285092070701c0888102d641c440c0342842c200d100507201d003091984410800c41c0000c0d0044001c04030300c0603040035200703030075581c07403c81c10380360004c1c1c0140c05140c00040105071684141c2c603500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629820008 1250 629818758 629818801
    0x1e01020a1e050f090a0909050307060c0c020918010e070f0303020634020a0609200a0605030604200d0c12020f030609040f020a06050a02160b180d060504030305 70
    0x2001c10500d100e00645140f2585092141d100c01c003040d11500780d07a400c00800c00802c92010144014803c0e4503103a070311b0b6403080c18210b5502c1d24110f40b15080a22550b8140100356024000140036120380410340d54513010503009aa2543d01d502005d9010802401150010008100d5019000f0706510340a410500c0003401c00740c982c55100785840003920010025040803641071a030b4585450003400403030500c041c0b0800944801e00785842c0804002040000144040030030600c0c0c6001c002032000c11000c2403241c428840000c5041c80881c4591405500c4801110b90402c0620141c4216040321032140d001400c01700e02c482e030390b11460000d02e03821100c1000c0100c031500085203403072044910913600f400045c000750b01412800340001c00b00300c040c205140b61035800814180c4400e540e4800240285d00034500907005014008520075041c0c0c04580b941c1c1a101d003150100c1c101b050440064240300c50443c3c01c544c0c0301030442c0075003001c20040e21442c2d018034000d950100d010720782015908900740c10360000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 629821258 1250 629820008 629820047
    0x80d020f070e060a23180702070e070909050f01090e03070804122901050301230c0d091218050d02100806150d02070c1a0d0e1e01020a 59
    0xe95040c200400c6000949a0b921103001c01515504041010420903400c0b68801d0171004640d80543c40d5403800b1000c000700101c0b21000340b091031a821030203814041d1000d01c0940d100d03113030a0003165601040e8691002032b0b858901c100c243c0d00c0021109a9505582c0310641e03001500051002d6101c0703005240d00341c03041e20001c44c078202840d034880016101d82e00c11407101d04c0348a080361003000007051080c0000c00110032900118074603a01d0740070710761a0a1140300d20a610340201031040e0b000c0020045030780c11448458011039a200c5c80b140c001e03a4400c00f04000903035603803412800020425200c02041c80c04030f949410700000900a141310180d11a0005442080e041601400592300c0c206044124452131400c1c1c10f003a110000070030011540c1810718036102c140414400341c600143c3e03014003442801283c82d81045503450054884000054007554440801040802010743c03094000604044402c0102d640524401c51110504514001c000300980d4000803030b1030352507901100ca040715008580c00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 629822508 1250 629821258 629821273
    0x204060501080f010e060d120815120309121005010f030b060603042f030601380a1b0b010608070f030e03090f0303090d0308010e090312060409020f0a0906080d02 71
    0x10083c1d24400511910a01010400014841da200d049039042819400442110303904803000d005448404225071409880805130705c0c001e00c6190902e0740d440d00d440c0440165160040c00004d12440124401e1440d201e881042204c50300c050300c0e84a80c500030070740b00d83c5c90036081d8114035055100d480007405c1240310b60414000d2001080310182e1445265034800e540512644021000c403060034034054180c3d5060146800020704102501540100020900c2e1410684134564210910704100104003a69429080c41559a018025a2001680580d10078109003001c403e59402540c540240c20801c009a02e81c400d02c147e45401c0003100d030032891181801e00c000c07241c5070409680c034041e541c0041c0c4640101d0088441d030752428011141500000307011208500d40504000e4030f03008003881181c410441e1407000426058021090f50100280180d1203007107900c60808101c007070071000da07060383e202e0700e51a0180c4141e5501d504140007001005000308045150089003803d2008000c09401036402501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 629823758 1250 629822508 629822521
    0x807080c060906101502210c010b0a080d081f12020f01030b090606030c0c07080303070e010206040b0a0203040c08010f090c090b0307120302120a0216090b1c0314070807020406050108 80
    0xc0c1d0755005d950061002c51896220700408a10380038101c1400244400c054000d840500c8103040201148104c110007441040c0008084c060820168440d0070b0769074209041003400d0318480e4502e9500041580e0780f9800207800000d0000050941d517100644c400d084c0041c060840c24030035030300c00091200342800c0100b00030580101c0c55015004008512652000000820400b804029220356494001c221401c0d592100030301075580e84103840c4440410100e500d1316050798800603000c1e105941c000281c50880d22200d00703070f2001c1d4102a200305c2e1100c6201c1c40114001a0920403041450076450000c285606a0b003416000c2466035001054001d04040c104003a58600090003c2105c680038240e0f0106401030408a0a1500e01d0b51502096800068800300c0d5960001d001c1d025210400202540c031560780802d20304690050243c0e94001c80c92020b040800c0343c00c0e109100001d4024100395002000c01c000200d00d41c0d010b803030100c030307806408100e040035801c0610074840604021300700b10700c4c20b06265 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 629825008 1250 629823758 629823781
    0x6040c09120f03120c23041d0603010b270109020307020a1106040503070b070b15130e1f06080601080c1c05010b06040605030f0f06010906050a09030807080c060906 72
    0x44101500d01c1d0303840503112042501c14039001405a131944020404610004070040c22115182402c21022194600c40305012070484c040b00d045407404950601d4102081d40d402240354801070810740c1c955643d0880001540f00c001c0c124082c44060040c110205180d07642c0103030782c44010307040796450300e10600c200051103030000390700d2504d0307500001e0350504a4810400901c05102c0d680040b50103001e0740d940019201c00840c003828100703104500041956a50b1102c600100c0c1090b13a41e00d0f0700410b4003074180302000b100c3c0c0c04402c079004103000b03440c2448805120345a4121101401110040d600c0b05d040000803401d00c00e0030701610540c4094052540745d00009660812390141c00000310700396809840400c0070951084142050290441d6100c50b6110742c06001c0f50000c40b20f040c5089a8280001c000c904e42e01440351207a041610750014050400c0c0741100c19420040054080c0101c03260040042500d00c03001d0a409441070140b030b42e0311117207070301d405082420180038001140e200c40c080c0420031204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 629826258 1250 629825008 629825039
    0xd05070315031e020406090216120206070207120602190801090f0603170f0403140d08061c03050f0c06131a01030b040809040204032f010f05030a051015030506040c09 73
    0x250f1100c080c406401c2c0001001802640d0106041070720016010307e03043d50f80002104507a001c2e15844050744807206040c3d860f00011640800143c0007401300348201c04ca2a841c0c00495030060000600b0002e44583c403600c404000c49180003c10094001001540c4450007551101c0c01d41c220240940c170b14507520586560341c2210881184030008c988003007a44420800d880c011500540041c20300c8003000e1307449844c0c2da000784c010f034001203804000a0590401600702208060402c0006206039442c0c0ca0445c5d641d00002d040300e032584401c00c581d85141d0810803540c0c1c0110b41e008100c090f151802c0c035249010301d8040749403100250602e030041000c101a0100e8550260304090220368030800030b00080c000707114036080201140a4401ca04e40c124111005008000f4484000588a1b204007001501c5907030b0851061030006204100142902e08250096a005644540c45081564980c1020200712100481410000e603540e800c1107010b2400d80122070841d10702e8140f10024038106509456030660 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 629827508 1250 629826258 629826293
    0x3080105060c0c030d120b040c1e050c01060b1b06010f03030e0604030804062c10110f030705030304030e0409080d050907030b190f0209060301060809070b0d0507031503 74
    0x9020401d6185100140f00d881100c0350300605664107003d800d000a00142c9541030800460380c5444803181c9107051a210742c1100740051386591680e1400686002506d86c0c0034003c91041100c180040d2083c2c0c0000d006100c05001411083c4c1d485070380d0106200341070301c5543d1050205910400042016041c0c1082080a4a03010b00d807040d444402c00011503014880c90384003c2058400150000d8000e43c40f2100481520800040540c804001b002145c400394400140542c02801d0224000c01e50780121519880b100a40040e510811108014141150403460041e40d2a400000802c070806900120201c00c1d11320031601042446000e40b40e0510314001d1080007200c055443c2c005c220218400c00c20309000b554011032418452901042c2601040e40040b00401c42c01d0811300441da120b0344074001d9683c01100a031156046a1030464100c60582c8081c0c103400c1a80035560002c41c0010f907160040184256034003011800e42840e0b0b500404460700b034a0048070313910442c0d2040c0001f03000440c00c0364510b003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 629828758 1250 629827508 629827519
    0x9010510030207080d0b01020c22020c010b040207110918061602150103051f050f0a020a09081504021206060114030705090a030f1e05060105060714010e0604051903080105 75
    0x2105001d600900c2181c0000d450b400011039004c50361025a040441001400ea00742c1d85221540002c0c0300d81850b001918030481c19007010204181c0040d98050000500c1c528004940310740d201c030204049901904041e1141c0040040045180c00c1139400c5a40011003070003d414001c0c6480314168490788041c040000200c46000704555681c030800200d40d842081c08841c04081d45d503460000d65541007002e030305103032000a0b424a000301a0510600344254100100044103688441d9440003e511201c50704007407021454000ca480b403820404411000807500761516942440c0c01042940d00c0c0203100ca050940c40b41e010400103980c841c8085c2c4030790083d610965269104d049056038240126181140c001d0200388001046c0282000c645d05924080d091100410b04c00280c1c420040b20500802342c210341c0641c00400c1581008002800943e001e00f10b5484000b1050541500b0b4402803861800350fa44240d00b804180141848803401d1146840184c044d0142c0960300a450514140305052040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 629830008 1250 629828758 629828779
    0xf01050609060d0e0f16060c02060a0c05030a031a061c0b120a0318060c0c0e0a02160b06010f021c0e13050c120c0708310b041e05090105 60
    0x94503103106450b0100306088060004046642d201c0d40c1e03900107540d0098062080c00c0e0706c1100d418001c00c66005940203640d60004186c0d80d40c0034810607910204800e82000721020144021403011f00141184924568010400340d001c0420440340c1403500c41004d108220801074030004c6503c200c02d6048183c4440004500c900381000010020a030383e4034800e95030f006200c01c580825a0021124a642c501c3c43c4081084548a4030200c1d140d040c4804002c000c0c042804003400201004a08164020030321000989010382200c1100066105003500b180e0383c42242c02031243d80d42c1c02604080070030b80c0b944018000c500750100450b0651201c440650280941c5261030021521402d00e03003108007120b4038061200c2d08054003118103980c0180300c87d1200b1042030340490249a103d204540046411108080c2044c0ca5402100800c03081c07031240903e044400d00880c10103101c0d00c40325000501700105029110340c50031036150041407040f914221940c80c030304010300041e82d500151a054400c1540c0c015070780c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 629831258 1250 629830008 629830027
    0x1912110906011706120d050703091a070f1b140f040938040b061c0506010b18150d06050d0b0a0c11030c0115080a03080a150b0c07050f090f010506 64
    0x81d61088410001d45000302401c40509a41110040c0002844ad96600540680d03030181c082c5080494051402102001c20011010881118003c058a0b000c1d00304141a00300242140010101c00da00144065039400d00646291501c02c40c908104502614140443e6a40313950700c6008217042915078810700500345105100702c854107508070004141810548060400e41003428010b20201c401504c10507034569805100c1c601c4400da207003070540c0720700200116428480c0c1d80350a908402c0e01100080b2921040d4040c41e99903000345a45880032a0715a40d8840d000c2c64500240c8465800450043e0b030042d0303010300003905c0118220f500c00d0400400080d0514040d03011140000c49055200440c4004903000c1e08844040d0b00a00520140e48411484295901e1506445026412000d000f00c1c1101d03000410000d0990000e901d140c90785210701d00340507240c0141e01c1841d044440c00103640d40c8501802d21050400d801c40d102045000c5135112954035210105107482e003014011540a0307075010944009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 629832508 1250 629831258 629831269
    0x102040515030a0c02281a19060b0720010203091906020d17070806121e01061d0a0b0604090915051f0506091912110906011706 56
    0x5403000405145a403025a07a80c501d00d50030594004601c54648800e5920080c00014801c0b02d01240d41680c5001507440e41da0010301090450043d6a4140d502918180e020740c46100302d1700c5510004003c2c3c0180341c0d00f10f080350482d1040e0300f0021602c00c040082a021030081004100c015009020075107d45051000407400d50052041c0d580d00111001c0d48052a060800d0310041642d0b416421104180ca10358030854051342c8042d150682c501034500400c140c0c512420b40941e00ca24003070499600181188400b03403400c288040e200b03650244608482e1900d903420b02481e070003400c00108400e242c1c1d108180e40704944030050011403250b07580b0320344100a0b4994005540c020049450100318030b82c103909100111403001d940194105180c100014a20709610400c5841c28500d02280d00c2c3c0c06017094148540ca9101d03510b12507100c2e80e40090541d000500d800d4200240845d401d04420b004461b250030546180f41313052081c40750000c4010824140d0b4002d5071300c1c00c3ea1111031b84c910140e8441401261 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 629833758 1250 629832508 629832517
    0x90c02100f020c16031a010b030f070903080f0a090803030618070c05030703050d0b1207090221070309051905150414060103031d030111221e06030c0e030a02060c0102 73
    0xc81c3d80519406610102c501c2c41e407607030440340039610012031400c4103000035a4210090280c11400441440031030741c080d11121459500c02054200344c00c4c169140d4483c82c0054100341c0302d100d0703004000114840c0c0b407903008102c2e10041841c03000541c11741c02d10700c0010b181484042e0708450078800c10360019102c0c41c130405142e014250884143c80d075500580c200106543e210b120482c81c1d00e03041020a111508001c005201c82403881c80240c100e1a0518855801070740c0a80030840101c03071080344103036540500c2050b881c05000140c900290303003070b0146062030030304000d0030295810340d0b03141070642e020900216101a40701c041c40307410b41c0b2030399942c504045201c6040011115038807030790002008040e0401e40c00841844503084018070300e140501054240c1c2c0495140b014010400d0005101d02d1641c54816034008000400c414040c0e9203509480c0500c14000310640d0003000034960800096416102e0842608854078019130018008008a0f13640c00000400034000c0e030740004c030588203950a40c1a00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 629835008 1250 629833758 629833777
    0x612030509150409021801020a03020c01030c020a0b0f0105011b1104091719090812090904020105071a070e010903230304090f050a0e07030b01180f0e010e0601090c02100f02 76
    0x216141c3da2036242100c02500040070407012070740508000b0549600015529021542c07541c01013010762044801103000d4201d0750366100c1584143ca13140c1000910522000784074206c181c05054640d0300d84000101316002e423007205901d0b24051005000401d05503d0202c030402d9040d18086452091071509480d40a241d4a85104900d80443c05440482c0e41000c035084a240781e59807001003c1c0c845000301d88900b10600c0d1344184a08c2001194090b060241d0a554814014142142405202c0d1500001d03403154081c0010000d001c44100000990010303404006074100f03280203d441781c155070b00c00540d0b0010551020300f0b40c0c070380da402c10210300c3c04000711405001500002d201045d0075174521006004190780509003a400c00b000003440c084005100d104031303500082c080400d64a010303120305590080c103080c4102d04d601e4141245580805005c0c108128403500c000140e0410000303031241c1040010380010721154141400a800c0c940c0c0010000c002042503140014066a4070f54040e00030b10030462032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 629836258 1250 629835008 629835049
    0xa030204090b0a1109011d06090316081519050402040e010f090b01090905060f0403050706060f031506050127150c0507060201050f01060309080c101508010612030509 73
    0x8001005044460503000f01101041800409203a07408250a03019503001c850001c7e52a051100d0b201c103e400c999022418060865403402d41c215021034105020381000002461447c0340c2013000240070820383c4545010600b6148080c10042c204400710407e8a466000740c0d920740001c03400f9550380c1e0f4000c4002c040003200130442003a80508000181a440b001510030103820000041e140007207024044086500401405003552200031030081584080c0c801e0303080180070312a01d80011078034400d44025101a10012200c1807840c5404880e420040700129100741c03d0000402082c1d13040094900f85c00307002100300e02c00d00c17841c1c1c58140c541c6038690b0001e065107170442c80070002c080d0400c040021007401442034512301c5031074000503400d072081600e80d02504a50240100540c0d4803a0340100c51051103600017510705503900180f1131811710050110640d5a035030344030f01e1141854629484000703140080003407094500c1c3ca0340d043c00010741c004000e0103100700001da5450568609526a03004a4492803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 629837508 1250 629836258 629836271
    0xa14130905010611060405060a150e01030b01051302120402210a0b0f0f0411010f0309140c03010c0f0903020409020402040807060f1808101104050a030318092007020a030204 76
    0x414000d00000c3c410a40840e006074200c03600654049941c51107036400c43d00a050a485180c13501008100900003400075100f4a507010958210f00301c0303024000e41c0241401e407c554140401c01100714001090050120b00c1000703070300750200c1d10441c04c5e44e100d9011501c1d00e032507004400b030384082c2e180807800c15a06409030015101c2000b8400207010300880510480110a81d2a41401155001c0c182d0f401382862004190080b03266100b11001541400903181c08103406001d47d8811940b0360304141e00044680000c81d003c0c06c50709091103100c002050500e007858000324040c001a00c0c20301c60b03001c081e00994a50b244035003551140c0c0c04690091050200302d07151a40c2c3c48600034810544800a03500060501100e82800484150070009603409607000e020210304050001005200340d1191340688401840000341c5030b40c507034001c81c00950107901c03200281020901c00340910140e41c0c01640c0b80604e001421080f80c4089a81c6d480d210700c205201d55540c06c04c40c000142d00d4080795000039072240c2042c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 629838758 1250 629837508 629837519
    0xf0b0603011b0512010f18020c150f070216180506030102120c030a0e0105041104023a05090d0905120307121d0906010e01051e0d06170708030a1413 65
    0x140207050001d0003640344107199807503407006c2040030014851045100c01764a09403124500503802090307000f40010855000007020304428581c03132001c84150321108444030030071007003507014020982035814065010041c075050000d00460b4012a03940f00701c1080d0f4a000040c0251000d41c12243d40a4122030300c4041464580742d42d240f59032084410b00542402c1420402d07030356005006a138080c66111202603203054031601880001d4104a018100f00c0c0040861121328000c16481c00b60b016211440c82111424203c03141002c1e140007804c0295039030720150050004561148080095500448008110701c210501091541c014070a01601220000010116040c0c000600ca00c00490300717101a80c10000180401131044d00895101d4046a045000c0c141c0ca588140c00034100c04046048030038403010700024203003142e0001004074032559a14242403041e801c965071161550080d1030000c09016043c04071040d07c03400382c0041c0c2c1c414421054555003000c0c010100340c0342c101d0320070342c00c40c0074403503650 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 629840008 1250 629838758 629838767
    0x170c0a0305031317060403030b040b090901050a0e0a0b061504030510091e02011d04140405010e06100f060f12020315010f0e0616020a0312030b0f0d0f0b0603011b 71
    0xd040380441d060b0f5050b0002a400c0d5001c44c030414407620503001d420740742d031141c4080e0081c1503507064284d44103075100710005203035942d080d00e58012a400000014545042c50080d800c45042c201c110b0403d0348240a844000b880c034505495002c0400d8480b40c044441d03c1e022100345010b01d40000b8414000c030364200441c9034017a4841c00301e450080c1400c0b002c00e010001002d03940295880d01900186205101c0c04a05400b20003007207009030b019100050380c04981596103070902d0b0945080701d0b165196006020604010020682c0000c00144a441940e2500015580f0b405a9208401c00d010701ca9600e46403d90180c800c2c1c090301c07107448400395541c2c80e21452507103500142c80c0a441c0403503d030600486003688030b040740b1000c1c00300140c20a80b516088010341110861128001c9038004061040800058118412000500600d48020404406034010049010b201c580303100d001d24110300031140031461480c80019081c1c0c0045e24108540c03110700100c0c2c0540442000b000741080800141070b08150300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 629841258 1250 629840008 629840017
    0x5061b0f0309061b0c0319110f0303150a0e0103030804081204031112033303012307020a0b0705031e0106121a0619181401030b03010b030304170c0a030503 68
    0x71641e0500c0050b06118555881c01003085215186d4401e1000d80515034200e00c180810f007109041061a407141141c203a07207002d0031001d00030001d80011040c004544031500030300e294810200d070f128524a05200e04c0d0303440c0600510020b405c1001920108052166040803101407008001c1c601e5054034103820040c148080500d1401c0007407090012103080d41e41c949050f2400351100f45020b01e95170901c184180100d17811640c0380814800f0728241a035196801344250303920f0b0a14018403040c5a84100280c41822900030245002e5401c44e000031400100d51550f0030707134800c809042c43c50301e13070f161100d840588810004003507070a10300103000800c0503170b00b120365a01c6d003000c000001d000340610480629104100d80c0022500070805010341c1d15000701d41a4110360801e5503261005903400302c11503010035009680d008248100e1040e40742010795908d4041c0c1eaa96141c103900a02c8508180340200341c1ea442544a41c00391300000d00500040d07108244950240c1201c0105068195510b90500300c0d100c0e0300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 629842508 1250 629841258 629841271
    0x3081f090c0e040504021e130f0902031c0f080406150605090406060c050607050a051312150504030c140109020301020d0b01030b01020a171b0f1b010c05061b0f030906 73
    0xb00340c01c50162882d0a00509119a41c05030000800d0546180c0903400040d001c240c03168490b440f00001d14071000382d03110395030410000030030100b40071402d4010b0504201d0255220707009580c0a100801c0041e4000551101c0220707945010043c40c2d803182040c42c01803090080c0c80000700f00d101f00004555602402422089404840800205a850700159808050f640c4001c2c0960070040000f0080c2e0700035000342c194001c01d4184a80741c00c1d4071142c0900c0040058001c075035120340d00b600c82014000311602e83d040c04111108100003a0810b5140901003550421004120710018050b400350880c0a411007003545501034001d40d01c038401901034a01034141d544640303001902d00700e0342c01510362000a121081d10f8100343d004034090241000c82d00b5a5002c84840a004050540d1040390305400b000541c4078441c41101901110120b84625500d503160500c90b41e0400c003c1a4401003c200d01103441a088070546040c0754240c0e8600904883d140540410440483c0f030200c104003002c2c1d00810040d10801d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 629843758 1250 629842508 629842517
    0x70609020414010f0b090a0510270e0a1103060d0503042102040f09030c0609030207051005030f0a0510060c06111c0609110405210d090611010b0102060403081f090c 72
    0x1740c540041c04114003070000815031002e2050350401036810044107190b071036103d07481d1103144031240c108040040b200c0d0921141032030103504002c008540c06010707039075002031125406010401458100345039038000504440d00c902e45e40146103041200410071140245041c00031a80e10381e0300300c803085c601c00d041400107900483c00c25a8840c41c6030014440e81c40c42a5042c2c032000a1501c954582c4030003003404c0c440450651254004c0032405a031030484030b2080031510343e50b0030707607034501044103035900b19016000d40e940501b04018005007010103007514042e50310320325240903d18810f0a01001030404001e104c8015440000c04442c3c1402d15081c644041d8a40d44091003410743c0c1c0c4c00b805045900f144149060650b041c0310a02c00b9140840b540000311290545603001801c0f020076150400b40c4511000c0f001c10700c8400100202c680119454644914401c000c03c0b4800103980081e440f01001032009040142420000e05050120a4059611601d0013031042400342c0754200c1c0b078003c022602126011a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 629845008 1250 629843758 629843789
    0x2070614030709231c0305030f10030b1303110a020112021c1104061803020913081c0b03072103030b0a08010609020915031b0901031d06070e090c0f07060902041401 72
    0x5540a00e100d9031700381d415a80d092130350b40d521034a03600542000d46440303401d020014000020900d1954018040c2005050400384e90300640707405814444044406d201c0d40c5c0018458001503a080400a119513080d00c202580d40e0109543d500034505200444d800580d2500c0c540e0f640112003c4007820645029440b00c02c980c0d000c14a03c4641c04580744002503210118000103038544c1540d80c4410724840c411288907003004c56000d0b40c0b80400840781d0031410840c0e0742e000342c1038862804100c144001d01c81c0100d02c810215040d0a00d42c0084081310029003410348170401540c46842d8101c2640081128000070440c803910b50028901950003118024880c00b10124034401e0b50b00340200b140d000750b41000c3c44110100b0700c0c0c41c0c1e00f46a034100c108007506160740e07880034103d94401380203400d00c02c51000004d0040b910707200303c000d05000d0301407600345d00550317050040010b0440e070742d4120381040f8100c00c03a032500c40091b0318040d0083d00d02d01c80000c0d0003605110720462444091a03200d4180c80400c2220880b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 629846258 1250 629845008 629845039
    0x70306050106090e1504110d090b0a0e0312100302030604140105100b0703030b030304180b030f0d02071a0721021c0c06020f0c0307030f0e010207061403070923 70
    0x1210000e00135142ca00300e820300450503c011000d403004110001600204101c13590344564803040d00700c010301500050700c50641000b0072001141140c1c1c00b0600600400001d84010b00090ba60301654aa2000450080012403541520001740c2801158010100e682c01e203010715112907101d003100340354038266003054042405205202100740559407030250903400c000903500d080f0064601401d080d9010b00082001180d015414151044030711046980400c010100301d050520f8172800c0c20b4464001e400001d00b42500c1c1d54003041da0030071a076403000044501b00c04e840301300442c1e1140f042d004029020540e1000307a410704201055000011580a4410343c00d2074110000c440052800a000024140e445110001c0c040e64064541905403841050800340c240c0000c51440d40468030030b4010503052103030780c8446907015401385045107080c40a4100d2510f003202c0a481c030b080001100034058030220020318800c0c4100490030040c008581043d000c14800e640c42000c440e400d6500a004202e0b08000510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 629847508 1250 629846258 629846267
    0x30501060f140304140f0a02030f03040308040b07030203160b01080d141c06120c1a090303030105040905010905060f0106110a2319030503100504050912030c1209070306050106 77
    0x45145841e1070744107400e9101042c210b1980c0c002841144c0322030f044c02003030030011000c01080020407040c0b4014009034041d80105840c1104040d00c2e0815680200403c0c400980e1003001c1d00d0803100704038a03164481081e85801c5c2e0450141415514840507480c500100f44200c080115041350343d032a00751040880340e000c0445549905041c0c0c844c610320200300c01034140c441c00d9015038818080d01c00000304076885d00f06c000b5992080c0601540c84804180c0140440c0180c0c400414070015040700b00c2e072030040f11802003a01c90005204640c80b46580e2003084091010a4004150b49a808401d0b94828503145100d107050250078025100000c01003a0a0300420900103000c2c00241c0c0c02c00c01101c0d80380e403003001c0061140800501154140039140c1051502003422000c1e41c1518400c0d01d0700c60b2689400d159010700100d0a5201e03d201c0c0c2d051805000700c0202c003007145800300d050943c00ca0340e40d80e03681068200300c0c4500800c10959035046410002100000303d40481520310850f418801d9980e10036040300d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 629848758 1250 629847508 629847527
    0x1514010e010e040f08130305100509060705031006030207060b0d0c06080c092b0b01030302010501050f100e1003021c0603021003052401030f0c020c031501260c0307080d03050106 78
    0x8144d0101503540c5070114042401412082c600320b01c1c4802d004c0c0d02d9a03a42c5081078182c2c0c0a05102e00c1d01c50013030110780d002c140f1006502014601c3c05906500d000c400e1005400403d01c1540d0074181d000440741c003440301030b07041142d01590180845201d00c005103440304100040d881041c000031401008240b43c03985100c01c581080300010400f00c071043c07000c9111011111010800c405000c0c02d1035000c1c00160040c1804d5000f540203400001d451f61400c13090007001110a446a880740011540c600300c0303240c01180b204030b042010740341c010300c80002d45002c0c1c0c024450111224103034010200300042100310760304590162482910849140c0c41c84150036020b4481c20b442c0d007805001122100102c0c0d603c1d2108244220780c0501d4041608200800b1480454841c944000010b802c07001e285050390031b0030802541d03c80300400c04808698034101c080c2c002500c80540d11080e42a401c194541241810400705007544c00c000c00703032042d042d5210181c603620042802004003081c02c04000180080c051000138 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 629850008 1250 629848758 629848763
    0xc060a0c170412020609030c0909030403060608121b01061e050102010b180402092806031e030912030201020405040501081e070f060309031704081e180d1514010e010e04 74
    0x51030f00c083d9080202c1c0782c0110400c213815201d41d600640d199641c0b00b030200c0c050300c2c40d48040e5580c2c505604149041c0c03103503500600429030010649882d500b21810440b000c04460081407401100030f601014050700569112407494803400c0480781040e00c0501a140c102c6100340c008001c3d4003d6581849078140302441e800005404603030028015040160b040c42e80000a81d0307281c030300c9140c1c801d40c800c100c0021044500200c1d035038642c140304020025401035640c019091380c003140202c842c0e4000780101300a02a4808440d40e6201d500c0805000750140c1d0041c000052061000d9a10303100000d40e16029518030300000742a030032002044000200721241541e0020424800160030080f054019000984e400c034100207c18400a8107100400000c9015501c9040c1d00c82daa500d800703000201a43d4400155540da0344208a8200441402c100c4018804030070b45003001003000a05040b01e20030310f4840c00400e00c90500301c0601007040220101da05944621142004c16600c0d2a40c0080044084900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 629851258 1250 629850008 629850029
    0xa0b1c0614060a1704110109080c030622170904290108190c0e010e040605180a0e07080601050406090e030d1a12031213150507020c060a0c1704 63
    0x20907076142848002400b0480d420f0804100d2030003034040c1503031a03030710849054501c0d821007510601d0560340070003c0c0c402004004001c101c251070700c82c0000c0d141c101c050406500c10020b02c55902c0f800c40c42110080646400c80e41401000d401401e6006e00c2d0340c42003400d00c2c4102c3c58803000011410035022140080e40841b41c02070344104a10005444812020b070200c0e0892010210400c00c01e22036015281b20b18065a070b5100c6503a032800b0015108600b07030a00c007441981000e03014415030b210000d40b40455040d004c0304142c07686030901c60200401e403003000c12a050140003808035007424000b4489040b00e10503101000b03002d544100710b1044414801c6000a260000c101c0c60b1083c0341141c00040380342100300c1da148140990840001d040381505002e80c0c0b403d400101d00503e4200000c070303040b9031120794401404001c000e155104183c250fa160307081007009a030790020a0207540b0800c0990f48191015010319a5404410000380080c170459070115407d25107600041000ca044000340d41c21952518030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 629852508 1250 629851258 629851289
    0x414090f0a020c070f0902070302100501120b150301090b0906160906053103060b040c05090105160f320319030207050102030f10090e030a030902010c020a0b1c06 71
    0x40341000381d4000c0014030b0f81446011000701d1380701c6031195500014601503800680d610320780d01d00a41004c0800e42c0644085260000401c0340d496006030401640d030b8001601c8040b13503030301503505401000d15400b6030781540c640b90003501088a000440c50190600c1012a000795560f144215600445101b8880006a0300c03c01040440d00500c090107145110b090048003008400510310b10b140310250a62030720b507501260030000c6c05518072a1541c220011b4070144003195803000f02401c3c1d486004071040c10850001003107480d000e80441507044495104200041c3c0d04040c0c00d0070309480381b800c6103002c415420050104070351280510115a440d21501c00381d41040c0314008400800c0303550b0010301050580812140c0000b880a00c003d620034038000c070030352216040003110720310510000c5d08090b8010340380204101d000c0d880081a9090003619190100341c0c80d1c441d100480f00ca108210300250044086800070a900c07a80402400b5a440f0f000b4032881c0d01d003d00d42d50007060381ea06200321140c1e00003034103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 629853758 1250 629852508 629852521
    0x90903020a060b0607120f0f090b03011a1b030406080f0f160225091103070e0616230c040902010909020a03061e0801050606040e190b060f0414090f 65
    0x1000f24202c42c034002c0074241018225200c2074001084001e080001682d200f0b04201c030f09811920700c5030604c003546081001d5608003402c0d01540c0c84107001d09444c00002c1c2c0c05003512008a002140c00d4001c6c4040000168070302500c0403640d90f0890b000b43c0d0081186240041d5680c000215211301c600f20344041480561030711028054001121082181180100408000041600501c846002121038500ca40842c0340c51440001c86880030000c00b00710404005021000368040c03e26201c4201c21a40749995695030030155042c80b07090640240b0300001241d4002c610310b1407802e0710f00c00e111420203981700c0d020080104022244020707030090110316103020a0242040950140194600b9410700041068540c80524446034503140000740c280b80048040c0080140be00500385c00007003d4842ca0308180c00c0c402c01d10302c8040000c00440d85910390f601a00d550003100d40000e6800c08010b000749503161841451507000b80d001e0f02883d00c0c00b0300c4100100e1030604000f400e2900c00c2d1001c0c0c1c900c04042e216107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 629855008 1250 629853758 629853761
    0x1c0b090f061203041706010b03010605030f06010201181b0e090a15090203060412030606050f040504020c0a0b010605071424040f15091505101701150915090903020a06 73
    0x7030400790700004000700d0080014000c000520140040c0200c2c2c08034810440400362501405170817080c500c560a0004011103030304182074076080b2009880c1600607613501c000403030040028405c2c6000c0d130380580c81d2000034420040695602c4c00e80d140b0b901a20346446040c16240c000080d1013008055000e14100e00c0410380c029a0704001d038004101c0403500351441c0d00001c0c41c005041d201a07558a01c1090b03a2111a0f80601c070b4074000b03180f43d007002803c0456541c00e003c550300031b912820340101d0300003800703011203641070000030b41d06036105129014558496030024420b4209040890302142d4801c01c00070000c3c07001840c05031400c401d201038881c9907004c6507544c50f105000f0300121800880800240000ba620b648200c034129400c0e0800144120681091008803a4515283c0313066480c0c90240a014246907001105a41900348004a2407a001017201c0c01084244194001c8a0034494040744166031900080800740400942903120364a5004410888168a8004015901c087c14030800034046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 629856115 1107 629855008 629855011
    0x6060206012103080c220f060311030405210408010903030b040c031e051b070503122d070306240f020a08030a02090d08040b1c0b090f 59
    0x1843d01c002c0c008010103041c10150200000300000036550400c0d11a0300d240d2180710000c20715603620f10808094981d4042c6200003400c022a801968007441c054034081c42c0c002d000313002c408841c4984e030311140140000c40c000c030b01300522000481200c01e1054684240c040d84005c603004480300e0412040f240e242c0060303000c1c946070084039845c11a1902c2046034566184000041940381d1b041d208014600c008029100400b0001e03685d81041008405460b41c8442c40240742c116844200d004001001004c0d01c071101031403c0340c4480110b114400d0080d401007564240095655142c0b290f4108040090548600d840b484200d08001c00b5801f51181201c081248094030324406580e444103114400130380341c01612600410b034003200e5a21010f240302c030650302221055a456803201e1511541e08070180401d400c40507030090401d513510034007035003c801d000108404079a50b42c491505010000 = true := by decide +kernel

theorem cover : BRFrame.Cov 629676258 629856115 := by
  have h0 := BRFrame.cov_init 629676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 629676258 ≤ n) (h2 : n < 629856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
