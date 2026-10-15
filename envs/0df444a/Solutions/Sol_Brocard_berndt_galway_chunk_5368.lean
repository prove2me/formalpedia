-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:26.24189+00:00
-- url     : https://prove2.me/submissions/6ab82a9f-0bce-4e42-9959-47dfb8e0ebfd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 965287769 ≤ n < 965467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 965289019 1250 965287769 965287777
    0x20109260f0d05010303110a15050402030f0a03110d18030602030c0c010903030f0f0e0a0b100e0c07030e0a080a0609081207020d0e030705061c0e030c0705030d03050f0a050705 77
    0x30160a503640e03040c40340a02c0300074140910040d800704802c00c5034241d50702030201e510038410364840700e908103400d0700c14100030045c5406041a601031003950805224900c00b000904070385800307070321100080d44c0d258110a03d411001c681c0002000740070302c4124200108185501e00b13903540000c0158803a0303034101c00c020142c000c440e0009003660030680100e09044d0940c0c45240030f031414107014407140c10280c41c004155074145c2c1d01044950302890710346010a601c10100c5801840e07800f016840310359a00d04a100140041d29104481c1e030000032081c0070542c010880c0c810700e8805a86110103e881c241842c0d403034208aa0000c0c01103600d030342c8950100803045048a4105510003402c0303002d400c100384000d42c1c0707a04170211300c00480c040204044040c0380c0000d0701011102c008103028600201c5801b44030718600e0002c604000c96844040340103441200780042c000d0100400014100d061a1504140c030b0800702411050a1501d40000e200341326044281060b44000141408181d40e10b5811007103d0a01c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 965290269 1250 965289019 965289037
    0x309071a0c0a11150706020a0306090b030a02010f11010609050609010f062a021002010f0609110d1107050d05030708280905071a0c0c1002150a11030408041502010926 73
    0x1030005080c601b080919401b400820307000d590104101034540c80c0050403925440300300d9a142e4080c0c44d0082c0107601c119484031b45c0008a203040c41044031448003042c295038243e00200c120b280c80d58104212810864100c50040607854800303100b4500c0c00c407028142c1d084d0042c2051900c1406001c0c0304c041c0203454907110402d035014002c00030a24641c44000d0081c4801028000c81509000c0c0c0024083d44501401c4002c4040103002c6281290980d403810091550040c2e1104105003488074501040d0107200e060019044c4e52106503480c40c0c41070005180358801000200c07070100c0f4400b480d10303410030320865110a4071003080000e0070025500b46186002442e0340607481c1c0f64086c0251704030740c1c001c80c0c001d0010903122004a40c5c003804032204010301c1c202d581c0c0c0b01600590006210039400811b81e0442a00000000d1001403d040080e2003240141d004450580320b1000000f001c108003125128440075682d0700f131000b0441c04003250349103050107043c0380d030703c009480c0300264550f4040302c3c0f401100c88000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 965291519 1250 965290269 965290309
    0x9061d07171b0f0c06060307060815010306080102040902120901021303020f01031401080d0f030203061822051501080f060613181a010e07050d0903140309071a0c0a11 73
    0x6064143d02440680c03029400344018003e00c000300d1007600340060a20180c500c03d84580300295942003d01440020501003075040640300e010000c0c58130800e01c0208041d150700100981e80744030f41c284601d11500058800c1006c1ea2042048140d4a61204022000e0300c3c1c0c11160080079088541c012406410b500301c50596031003510000080c0b02400040020024101d41c99000c007244140300154201c0c0000c803507054100384080300e40520f86250071403a503402149000c000300400381c0501c1e0b810510198100440d80390344840c0170302d2840c0703c121040d680101900700092035560114881d442d150b2002030b1030349001f0102428100e0300717100590480390184401803e8110089040c0c2440048030407443d1100f01100000000401d010b804001074a00c606990348400b8904584900a070340180b0841805900300813003110700005c1818414011805840688021304800d424800c00d41c600b54a22607819480701001c000452160784041103544060360462201d00c4c4031000c20011070b200800303c0600344610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 965292769 1250 965291519 965291527
    0x8040f06150f0501020f0601150302040e04030f120507050a03050a0b180415110412020301020d1a09010905130206390c01020c0a0e04030c02090109061d07171b 70
    0x5040000203001240c1100c08606080b03070f9901c2c01a61110f04140081c1010b0b00301200510804050101c0340ca040e503d540703001840c00359100303000302562009a408030000380340d00b00c000b20015484011020707100c0d281c2c03404201d1410952005883c03031142c402888149070f10b602c001034661100e80c1c48180c0892001c0c111400c011055038000b02e01010841d07045892440c8409640d4940a40e842096414108503007c281f4113810030720045c0c0d5903002803004aa042d0340810000311307041814003403405008a00754400480e440d0b0310703040005d131101c1600185116032806041012002260001071031068050703c0581e52403c2440014201140b100f000d001e4030011280c2c00600074190048020303101c114442901e80c0b21283d5001240c8424601040907404548840d040c00b00da0524034506400501ca42040340c503a2006501094003c08243e000f48122030b501c0303804002408400303d006e10b2002100502d182c1e00d15040c40302500400c1c4181c4041d15688822002961098802e05001111000c2001e40394607 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 965294019 1250 965292769 965292791
    0x1103030c01060303080a0c0813210503040203010e011b05210705071b030b0705030a0b0a080f01061208030c03040201140c06010311011107091e14010302100c0503030708040f06 77
    0xb80245100880008010000142401c00c2900c2102400095030303548801a440359031030340c002c1003541d400c280e510420007441100310350210304d401c507028481c980711982c480c42e1500401d1300b1560380001805076641800c0b402281c541d0300c650b801000280a043ca04d840702296800303008451080d04108010102c1d00c414000c0c0e0315008809050210320510032510ba9994009002d01600101c1c80001c08851006010403682409030340a103a00032940b100005031440c8504c0010300d088581d81c4100c4d2140c00654264030f00d40d1081c041c56002e419503040d240c00d003039029035912140d840000c0404403512408000704085a200301c0401203e60410301c003060705c801921240a46072078080c8000c90351400080ac8900b072550040f41030f012280c40130009002c2591405080e03002402d42d0030540002041c183c6180340c000101845820700b0fa0a80580b120150b606600c1030200094500e40020f0900200c1c039444800101e00000f1a0390044040c0341030055900c0710710307169040c0310071804014440d504001c07110607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 965295269 1250 965294019 965294021
    0x4110904050a050a0e0a1109070c0f0f0b070908100e0124050f0f06090d0516061d01090b0a0e0a1802090f0103050613090c03052505030304050a03030c1103030c01 71
    0x1014050300301c002c004031860490441c0e0744038151b8400500011552a60282c00e140c00e1211035801419410219041c141d80d1342c070003820404014003143c0f02120401075805204a01c0d011651103412820b00d0003005003001c440a90301c14101d0f04070100d6170b48441250b501e01800b034000f0074030184401c1901b2101d10000d0300280a4030418014507010b405020329405039464021400e8010035406042e40d0b1401c000c2c0000d00c90b980c034009806540380d102d0300c5092070a041061541200030301d8199144484191061051040b111441804504025110100388140741c0c50750100c4e1441540760a1030480c941070030b0041a0a00c0140d8070107900d040041180c0810382d1030680003450018030803100c1e5100c1da161030005408844d0255200c0b90896259120086210360b2030f8004244140103503c18080c0302d5680d51010303d01121000041009100e950003480c4c00c8080c3c000e0000070744030803000386042600744804260320008602c000b600b007161222140060010b0120081c24542d00501030341c0da00c1e880308002034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 965296519 1250 965295269 965295271
    0x6050f1608010f050103200a03091e020102070e07020f0a1128120203120d0b090c0405090415090c03080c1b030d0c0312020a03140105100e04110904050a05 68
    0x18108040300408100c0035442400514140c6400e2044090b26a0404004400170201e043d100a01041504000c4c01d6100446020300005246d540d808101c6158600c1d140b51200d6079444400c02046a180400b40140c0e0003080301400e95880c1000c0d11500e586201c001c0f8580030002c4c6008811740224200340080c000306071082c04940c00c0c1035481051001c04d4041300c0a00c03d00c180c82440c110940440140001039080071208075403030008044030358245840c03006000c9a84601c0300c205006540da036044c051402c207c1401ca80c2705500c11402c60605d890103011a030040b00c0280024003030344002c038858505070603d40c0120b41081e004100f51103019101c4c980201c580d80907041c102c19511070000c18695000501244010a100c0a009003180c8040d400c2c003500d21600c8010118144404050020056180d51005c0d018a80e520ba4022070265900e01140c022004180c1040717014a0301c01020810440d00044241906441910005a40074008224009602501800a601c1403d103010f21040300300c1c1d5004a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 965297769 1250 965296519 965296531
    0x4050a02010924054e07021906061d0108160f03080706020f0309030d0513020117090f010903030e0f1c030203060d0602120406153006050f 61
    0xc481c105464544202419286600381c0b2241c001c3d205003d00064481d2003e4800c003074181d10070360102e0b450f00d88404020b041d0011028200c0714100110012207003294102141c1203046200201c03d0f003015107000352101c0003d410031300d02580c031050071401c1140030ba00040081c528519440d03802102403840720070f020001e11801c4070622505107004107500000c00c04404840146a058402902d10381c1c0d600c50a4106400a440d40ea90a102a90404803204000d5202e00044c6000c1c60750b6a50091292003155000b9000d0341c107002d620418180140d81100e00404c1d1160351591b40b1015a440d0b10140b8a0320b9846552241e007542032216038402c240d0150014050040c0910503030701c0740385000602c16690019903142c1002445116891030b0078038081d81c000d5030410805420341d0400d040a4542800782e9000205040741480c2c403004100a01c01544102c20060000444080509290220b140e04010010a0303910110600c0b0383c0c0080c06030300191000005540c8000140014501503000820f1a0400c54036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 965299019 1250 965297769 965297777
    0x2060409021c0605061608040f0b071523250c020f0d03080408130902040e0601120603020907030b04022206020f121b0102090312040906050a080d08091504050a0201 72
    0x1006594509805143c0c26541c02411807400c0c081d08034403940040d007071002c0c21b80b2416030400000c190040c0c0518540083c145034941e282d581e03040751401c829041000e42d05031007014540180001c04041c90b40700000c14030740d1111243d50580b2440c00c404e590a20b0f0200708a4003084c000410700c030268021103200351190080f44c1d443d44020701c5c00f040c014441170922006000542c658000307400140340001511011380c045045824aa468140680483c0e100340c111203030b00c0060901300a4a0360b4030215400344184d60342c6051248500e9580880c50090f03000c2c240c4030916844126000d446e880d076906546049070000000984001d90f1056440301c0e080310b0040c60014007032074074041941e0500040404003032201c030325681d2a100040d86040340010108107401c4165400300904001650108880003990002c80840785c0d075035260011010440e0240c0d4042c90003420511410000c071400410640c0d007102031814007034555507402d07030454101141c00340421805a0402e040c0400c5c0280041d48108440c0301b038071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 965300269 1250 965299019 965299057
    0xe161b06051b0c060f100f0602032814030a020904110909180c10090b1314031609180807030c020414060d020f031c020f1b090c03060d0206040902 64
    0x40301580743c4181504400d01d40d0211000c600c40200d14002144d00441080d004004583c58403c041400181030340710b140140c1c00880c0d00a9a0540421142e00403a000d034441030101440c146c01800c4111800410004c01102000240c096801034040f10980300d002001001240162a26803609421807214a80504482c20004071070502d004100c007220102c01c001462740725000820480d40030b03005034900c800c0004154002500f4020100a0821050030740016007681d07007440074140100341ca02c281c2c14800c2d44207141c4d0743d0b01c0c141c0a0700c1c1c09041e19030380d20011400100c0340c030061034440400c4000624080300007500c402450390002e030601c8018822101400100ca071040010707090002500c055520801c003203d030100600e800022151080c81c003405690000b029003001003451110001d15001503007200c0098003140d0320601261100c814081d20523407040b180f00d00816a0321400a04021007014008003050082e554100001c0200d940107181c1d41d42e0301d0301c46810001a400c0840c40c80e910800c254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 965301519 1250 965300269 965300311
    0x1a120f030f0d20030a02030403050904050717060604120b061f08041e081903111303140d0207060c050304050a0303050a080609041e08070506090601081005010e161b0605 74
    0x10305000c03c42c00705480c5040c10360726810003510003540060b008034103020007000214000d0302d540c0074044c8154600d4072216002c041c0042e02d02c140c07410041c08141f203600704000c184018240082118521600003841180c50398440e004140b0f00f00c0078490800700b4864131b0400328401c90b800002c540c0702c2d601c10b100d034042080344140c019072811803102006121070342c184510800815a18000e440b0348600b0314007c600410f0344200d40f13005070f01c0304ca000d9421a412400070b200303000b4003069810a0440060003011031140d0306400a480301a107011348000c11003c00071440900c28204140c2c0c000e400f00610200d00340e44c3c1da24000e0b000d40d1001410b84085030191001604501e44200305138819178025102408403102940e404418201d405001c440900d400e00c0031102003501040070920031480d6000511195040c4000c880c5001540c17902c5010007402d06c40188040b800554030b050304100210306505542c20b0303540c1c042d12130710080c4001240c001c110340c1c640024001550031450080f02c02c00c81320183c4070850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 965302769 1250 965301519 965301551
    0x150801090317040312050406020a030608190f08040b030723191b050715020105092a010302071b03020f03010207020a03080c0a02030708011506031a120f030f0d 70
    0x8030080d021841078002603003424803030782a099000344680740c07442502e905084940700f00e800584013030b544a5404170b990f00c2c03690b8161041e0fa0107090701d0f40003440d0003000d840000e660b15044000042640c0e000184010400000d201a038001e4408040310300c0c0c481c03914240040042d625081c40c02100750311030910340b424018001c04c0302c404050125141400c039503440020303101d4580c200d800020740c03101d54800708081034080c04001c019011034910b625004406100c02400c1d40c80142106456802803404d409003030311841c103c216039080440c0413011800400005034001e001e071890180401211a14a04100b07621400081c01c0c0da2007210002c1d10840c207013003854201d00030058001d400020510050011609010182441d400d009003251040900d035400300307060400c20f5102c900f10740c1d1100c48000c40401d426820401601480c501002000e4000003036a005521020301d21f40211a450310300040d82205000400c0180c0390703d03080b640c0e81c20701180d4040d400c4d0f00c000c0c07422501c5031400d00410140c202d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 965304019 1250 965302769 965302781
    0x5030c1209010c12021207080c0601050a0e01060e1f080402100302030115110c04060e011404090c0b090414090a020a090c0f0f090504090f02041805030d02090d1401150801 75
    0x603903c0d012944072a0742c2c1c4400c059100c0c5000015482003000d00310f4208000c10041002620804141c0d48910101c0285440c005068102e584242d04401040c800e40f90f003c400b03a41194402c3ca00300b840b112100340414501680c401c100700e9002590454140116004800107004503c01d50301418070100c9407400302e04a010a0141841c0d81005114841a041c400c483c401c8030102d80406903028030a60000040403140e031940040701c82e005040040041c01c13080f45180610300c0d0292420300ca42c4000390f444603040f141c0d50051172184400414111580d03110307a80076803c07843d034428450415040c54480b003903884400c0744d4100d21a8541c0c41001c1120b240b207000b800e140c8846500e9803045003c01c044140d6049400c3c00e8a90100503950100081d01d5840d4022920020b008581510020669005100a5a505090246803c00002c12200c005107002048440c42e8064000060305e8689450000c0c29143c1c0d5000040c1815030103c00313244c0320800650241100c2000a00e4112070199140c001030700b41c40c0c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 965305269 1250 965304019 965304037
    0x30f030c02032a0a0b01080601080712080a05220503010b0a0f06081e01060306140f09060405090f0105010e090706091809060b0d060603021507020d110301110705030c12 74
    0x818001d02d070684036558070030740300c07080881901c3c0078200e22030307070030924240c3c10b00ca003603525602c650010040742d141072090700e004d409035101525040e42008520400c0d0001600010011034000031b044025510400c00d6500075080c20b08240501381100d8027078402446039000f510700ca1351802d04c11541504d0200d45032400c40c0d0000d4424110649007001c241d0350103400810509203207004200c4003408141c1d0b2181f15001e85103a0302d00003825810043e075800c1404220610300d00541182d000101d07140e8907c41c089038447c104440c0481c95558440c001414240703800c14004440d07092100120316a4405a2554840c4000c1800c41c0e270b980d030752443c040b13500e018188903403510301601e04a1302415601541059440178090400440d0146100010510000400740c050b00c8040d0750f00001d0085141c10b04280a40c444001e07807403400d14206400086400c1502c8000030480c020401e454205510300f03402150441e0201c5400d161103071040d00f40203850340e0000c142203450b40a020540600c1018050541788850 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 965306519 1250 965305269 965305273
    0xa0c021201090b061e0f060c0d0206011a070305030f0a0e0a0501021c060e011202011e0e011d0a1809050a0c090f061a07030201090203191a06010c031b17030103030f030c02 75
    0x81017a0092103500361000d030180c0d030041d00410000d05807540070000300130441142e03030040a441d89052304c15940c041c506020942150010001040481d0b4000c2c1666044040b80c286101d0b1621600c020030014242d50000030030600032082c03c001030100c1035000d130001544480783c4401c01c00c4120400403c9943c070b4000d100c801400c200061010081d0400e0859040d4410f0400d41c1130300c0c0c0b0311311145c4100421000c0303c00005182c0c940d10186541c0c40212492203c81e035900755240b801035280045c1c070b4005c0f503004c0c8034038020000003030907815a1940c00c5030030703526040b900341c4640c4640c6081450840070240501e20000f030404150104800701e80c494a811514168415402c4180404a200507a0303c2a00280c04640d00d4070304650140c3d4042c00700401c01c024507021150072a80500d424000320122600c40126a03440004120316030f40c0140070000c15941c10300e4a044c90411004204080070180c5001809001f0001c042d0440b0356100c000440c1624080d842d00c1c02d400305484801c800b42c641d1100400016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 965307769 1250 965306519 965306569
    0x5040f0f0e0708191806390203040314032d03180f070b180d02090624070602090a2304020a02030c0313050907090305120a0c021201090b06 61
    0xc2031040c5650754000580ea01300388010541140100d0030340d410324100300c07880240c070807519082200910480b0040350910003001021000040525001000740c0705014001004040c4056407a100348100c801843e8850120040c0c0c2d1741714504156241c12600b41405d02e10904054442240022005104008181000340b841d580e60420804558614128041400d114105510400c4481800b41e0300c080c10009ca20162125003950710b2a6034040c103401d0081c0645038500382c0d0b50158561042940d4003441c192010804010b98031050003a00c02c4100620a4802000c501e031001c2040c16001440800c1003122040b030203035180c85945c4025603405480001b03105440f18124040d00b0541c000c0c10b60101c1c10300580f8200300a90101500310350050151030f08041c50441c041c0003614090309099044000c500c0c0c02141103045a841c0e130f42ea0380e13001041d03004c00c5101203295511123214001020b1120342c050710014640da9141c001034040c100342001140d14401120015559092440d0400c9208074a501d80d1044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 965309019 1250 965307769 965307781
    0x90d0b101d0c0f3a15121712071710050609120102040b1b0d050a0f030b030c06070605040c050f03070621050c0a1d0607060c021c05040f0f0e 62
    0x400e600002070072940d03040451004000200d940b1240641380d0b10190f081441004100c4004c1c1211461054070250040c142d906000c4842d0b002000c9a006504c9411024071034000c2103030f95041e0141800c2d0301c4d14201da0b00204954141e00840122044544200288603600c90711100554180b142c09110340040052110008602d88150460043d50406000610345500c8418071030a84d03105090030507400400d500c3c041c1074280700700302c400600603c5180650904c8102c0100801c0402064001010182c4826010815a0b01408880c4103500028482680c070f82e05441c0c07240c09040200c4050381e02c80d0441e0400641400c1144603046050001005410780300c1c00c0c000103840d95165096840039609a071b41284120810f54810075000310401c4120310746500756504002c00180c0c1c1d4800c602500822980794810340d8450400391051190b003c1008038042d050032108a2a2070700d003034034002811000d002080c034180d4000c0014030075506c0c20040100c2507501c4080341012901648103180e01e1101138000141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 965310269 1250 965309019 965309047
    0x60907051509040e011508070e011409090f060f0601081303020c060c0115080c0a09021e0a0c052a0a08060f221a0f041106090d0b101d0c 60
    0xb1141c0e80081c03001a10b11811110f440c01c5403441109a022424480d42c280038980d1300700002c0c801480001030b04c016a6060002c00317994844140080303400b480c038aa0110340c0d41d0304280f2110089581401c1126100e01c0d0a040c02031030240c4c15640705021411200c04a00d10031202c0c0e100c20403494068008003a05c50302c400a008a903840394140d00ca0319565a800300c0079413141d2500e800028207052005107449100a020404042c0d46c0f58403208020b4410001413444805800d90342107000030034089141c560b0101c3c14280c0f440196058010214000c2005d1581858040882ea29030091a0300d00c01d44150021006c2c031015450318020400554400c10000300f160501941044c4d00403c0c40c48000d121000d020340407080e262281b4421200e80120888070500c0013600401254880d645912021490520303488200c0ca80000d600402e014400000d03c0803010744a11800d080050b80c808200c6609280032001c0020303040d00c40c09880e20390004120003411001401801ca401a409001400d00c3d00481c1c041c845 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 965311519 1250 965310269 965310277
    0xd030906110705040518070e0708190209030105040b040c080a030507060b040605060403151103071b0305130e01081902010906030b030a061d120a050405010305061f02070303020609070515 82
    0x2001c0d5200c2d851010585803541d010301c1780981001d6200c3c8040c241d902004c1c0c0e04000254010300512150300781007002c501e500185007600300c41415609010044281c00500c041d03c81c00503019010340c02c03c003d100c2000090304009106a006e80344101003640c41d22030b01c41c0c460145210240c0001c3e0144030342008201103074031850011100034400603005540f00d001c0360540d0025407090f103403440030004d02c100724003944c06011700102c0d200d0201841c3d0700d018040030b804000c0b0003d00545541c02a00b41b6001c06010b00101c0e1398851074840c100080659030040c02505130700901900b000c45c018000780c02100b59820b02e56000c09a8141c4804c040c80b801c011046004000ea4101c0780e80c50310a2881c1c84010030f040d40700f05285409110643c940008000c01c8bc41d140c0005003202d001394910410401802c140d00c0416a000d0358000d19001c109900c5180c0042c081e20300c0322001d03400710003409080d007040c66000940700088910a0302035840656407101e1450f11000c19200307450300a010300314142c0450161307070020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 965312769 1250 965311519 965311547
    0x2a0f0d050c070c180c081003030f0e060f0d141005120705091801150506030a020c030c01021605101104090921030b1c050d03050603030c06040f02010e0d030906 70
    0x2401c0200544503940080d149510071361080c0c041280703c0c07811007054011100015468103080070282003d07a0040581001d506c4040c0400403041e45010206e44145507402004e10018001601c0340190114810568031400110358400d1a0003040410280c1c02c04040303114648401003030070075600e4032051021000100c000d201c5180100c00d00800c1c0e40e5500a203060041d04032061003400307010311fa000c503402c42da000302c4d00008030320302d400c01000a03a6807903085a902c03001c82d0402503105d90300012024510b018290f0600d100307500200b1122154a450710a002c07003e03004508039682c026034956844101d42c8481441e41c1d0026081201303004001d0190050030206118141c2610349101c003220b001c044187c410035940c002510361907040d030b03180f030040c1007505000003101c00f204142165544c2e00d039445040350001002d0544410000300300da030302403081c1d541606030b540540e40c20346407a01c1c08028046512400302d0114030904601042270402e0980c1c102e200354161500c1455134141001503601c1b40301c035940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 965314019 1250 965312769 965312791
    0x703061e020406030902090a0506030c28230114090105130914090d0e01020303040f17030403030c030f1a0d0c180e0c01020102130b160b2a0f0d05 64
    0x8109034182441c4010001000165400144442c1a204101848102601d001c2185082c03800340101540c0204407407660000448200300d0340a20160500c0c1a000c0d0f411441015400046001031441e207900710b9040b84810481d00800d0b91606003005517004200310102c51400300040c0104e0810394047c10044c041081c103d4104031030b2650f0b808101d0291000005502110001c1c0c0b028404501070400210000454a0400d00c40503800040003e560740030040003c0d082d0701103003078a0f00c1444000e1050072211203c1282103a40c0c0d190038200035000c2c1801c0b1201034002072411244030403620f00c5120340034552900d1a8039202144005042081c0e800c1d41a80980301d412802c140042c0c0540c03400070314440d0b45540440490003504104170b6506040030804d8250559004020601803100d850b8201820744d1120442203403940034081651100359181c1d10010704000801c0280300d0098504072049403284000100b0b1080d80c0e0486280f40d40c0f6001d02011191070750020f01904c0700b402c40e1038010544c41009004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 965315269 1250 965314019 965314061
    0xa150609050903040306091a011503113105030a081b07050a090b01121506080c0909061c020d23011e020c2a12030304030905151b0d031508070306 64
    0x15800188407002c1c5c1c00a000c07042ea0ac1d05101007103815029000c1e00c01c880d14065070a0294550080740c4049003000f0700c00c200c0800401c124007100c5400b4000340545805000c035051b1043e1032070115410ba00c2031221101c440b050040407030032000d0005e01c50040d07486c0584a809910310301242640984020000030303050181e010080c4034600390300d11034101707401c800701d00c00d080251800d040a8a5090041e11071000c500c41001610b001d91940c81c08980c00c0042943d000510f480340c80886055013030812002507014007952601410b00003025104070310346400003164610481c1e80c18049089030303000320204816202d0300050003100b61595015040a01c102000d960040280c8e180355085402941c182030410700d11040c1c1801203040007212042450b040394021440e609040e200903051017a14400c1500c2540340c000343c40c901c0068481650414119004441c03806440040c10980f10720780c0110040c0064a03002da80c0d02100c4151078560100c40380d880150854505641720715014000c008404403604007004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 965316519 1250 965315269 965315303
    0xf0204030519150f20180402040b0708030405070b0705010f060e040b1503120f040614070f170c030c0c040b061303080304050109051e07090b011d120a15060905090304030609 76
    0x800f180717030144a40700580c1d80e0034a40c00c0c0c443d0070000500128011407041c001403184034021022a0700746a000700307810307840b55038074980b5600d44041c50704241e880c0ca10205030708003001015005040140074151060184940b2442101081d4130100c401600c041c0710b90300800c0d14034401802a00502c0c40c05010368801c11003a0050b184150310808074001d500200040c1000942d601941e01d181e00c0a181407224034010042c0c41d100c121044a960150074031480c03c501c1626000110200d030702e2500040b0075a6140d2490454803030700d0b1040c48511a00650900f400b00000d40380c08070445064800103c0c2500d40141141c46044880d08014811110745d90303079118070030109030b04003d0716440001e11000c04080a000009284c01c0a0032035011034040ea0a0103580c280d241c0e00f000744102083c456111100300000b200c1d00140c060010041c0c000c42074002c410510007400b8040361000341c40101d542c01070103003954552260080750750440761507050350020301007440040e407240c0000c8030301c902a074401d0341141d0501c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 965317769 1250 965316519 965316551
    0x2040e0705150403060b01170c0a0207030c1518150305060607060203040b100b180907030b040c170c040308220302040c0e19060815060d0f0204030519150f 68
    0x248482c6004030300c00f0404004202e0740d80201d4850364000c1c42c00d20540343c0328600b00c00382410064a4084011f030080340c10306102d032080024400654104124420a0741d407841c0c010452141c20035490009584021a01c015801d41420002200d9802c110010310380d0754003c0441c0144000782840703174044c03010403450001c00e040340007450095000e0113840d00c990a007221026940090340c0c1c0302d100000004d20864107412085441c0c250b10ba80240c030f070003c0319503684004900601620341c60561052a14000d51500c550240c0c00c9058001c040315015025110748103d54618007031440000d000120402000a40001850042c242071460800d810783c03403a04c07640040c0540300703149907440001e1400e41c0900d43e01d18250401ea507424100c0800076503000d040c120020070b60791006101014001805a0454041c2ca48404640d0304075141c01c6d04001d03004000e910b8030302a42c80380c4000da034241726840d200031903280d41155544003113038000e000502c103119070074500300900341048080d21103560700d03c013154004140c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 965319019 1250 965317769 965317789
    0xa0e15030429090703060c110604140d111009031b050309100f0c0206031b0313050c03030f03070c0c210606060f1b050c030d02010903031b080402040e0705 68
    0x100342501c4031070a90003080c0100141d00030104074100b207000800c0c42000000800ca840959421100c04919040111006d940c1043e52841d2060a44982d0041105210020184203641c00c04002070b030341d1100016004491071402c00718800302c60b40003510f00c0c054542c56030340110000f03803180c1021000c203000e0780020f1808190202c0152869000029650458603103000c2c60341d51a0114180340b43c240c02d603036400804242c80403600a0003510000040381c507100954011000340d00c48004017650700d00e000c1c0c1d00d194050192144c221400e1048030682c0b0401d04e07012040e03a66400041900c1415070380c642e07204480003401d221058466010507400400c29130203421141c41c0c0700c50001c1a40000480c10b2401c01c00f15905d5a02640400ca540520001115032104a40001484007084241400024204541007144030454607074140714a04089040d02c1c1c040d040244124002d45040028603110b039252020701c40e031151290002149000000c00516240e40b0008d20005614120b40445031104081001d800c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 965320269 1250 965319019 965319023
    0x90617071412010f090207080306040c1101180c050102070e150f0d1b050a050a060302130f15030509120304061e0c0908010501050307080c10021f06030303051b0a0e150304 75
    0xb25006000c04002c1c1d00f221001007103003031811860030034152210402400040c10251181d81c0f104800e001081c03194030003626000407a0000c120310f1a4034080321310071000c1c1d208100c80b140001600000c156002045141c2218140c00e04964150740d160703051003101d640b8581203640198400c1608040c0d460303c0c0f5043c10560311035150400c4d40451041c0111030081c0c03d5004034400c5000900034801c0b52a1032241788100d41e110708001d62205206249001002e0750380c0c006810501c20003a00040350000c8012400d4807000701c0d202000980c8640b02a00c0e103540c000c01060003012410008200098000d600c05042c0403c620344004484010b805090b042d00c0007580483e00003103002038140315101c0c00784125030041500310004c00e40145000c1381c403901e0b00900352106102c0c8102d04800022070380248503040030f00302c1c3c14440d181d4030040384d5260f0004191500090340041e01e0400041c074101a51740d507442c48004c0b030000700780c24403d000000311210811000c03400d80141c1c5084d44c90104031030440145000324 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 965321519 1250 965320269 965320297
    0xf121905070905032a011202070b0f060916090e13120e0a120221030403060e060a0b090906180118060e0d0906050301050906040b0d0b160906170714 65
    0x2d0700e040109441e100e4040d1074240000c1c6101441e20400105803440c00c0a00021300380036484440c2d5824102c028001c484000e01502080c030f0030000f80b48542d09000e40b00d42411980e201c4282c44510303130090603030b05000c08400418003e003814000e01034042c0405178450983d420700c2c1c18820302d5554202c0c00070b80456440b004550030b1880600c20349880003d0030041c211180341e03041403543d0741c1c0000d00c000c0c50012140846449030301c1c000c0d48243c2d040c4121006560090014030a07244407007800341d80c8000898070f84a0303942c81d1200a45103407808481090084c5c204c00b0041c0f0803503da0b0b4011103c9203e460f040070007599660203000540e40188525584041e0148000140d03d007986500c01d814403045141800411000c503405000b0a50400f007640d040d24002c1e20641c40d81d139140b8001c500280082681a0340c45250030340442c081100c0301811610a544118001119002005040ea840b00ea280203140228508a10020740c0e2205c0241c059406507840c0360035811580b2500c1082d049502645c5190030304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 965322769 1250 965321519 965321537
    0xb030a090203162603032d04030e0a09020a050901080a020c0106030c08071e03081c0f1a01080108100e1204030503030f010509281512060608030f12190507 68
    0x203010683c10401c000c1041d10712a15100d00c4c02ca441c5030712848010100d1402246030311542121541c0c11104c4081d2080700c0280749158282420f015280004404c02288526100e010102e60b4034006d0090350040502a25510b040ca01060010368461000800f03020031a58244050303640485d003400785a000f1070040580041c01ca041200701707410803896400400b01c40d100c01220407802d002c04e0144008aa400480c3e841d1500e64801607194813011001c2411041d034100140c40b0a030f0503170340e40034240c400400c40212821110510040d21802024428000315421130484003104400580010001032440d100391240080104c0054013640c019070001d588580c030100821611086a0229501510013151000c0d06032a00319404412800510780369019102000c00c0e082c107944040d0400c10000c2c00c1c0303120701805c1c180c071340811181014000d8003d03950a414040002180380c00441200c0c030524844001616198100b100c814001202419841d8078220000154200c501d507489060f00803404d6a40e81105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 965324019 1250 965322769 965322779
    0x20010305060603150d03030207060213051e031e07050603040b1602060603030a050a20010b0a0e0114040b0105040b0f03070f11061920091014040b030a09020316 70
    0x21908010180c5000701802c105104959401c1561040100000c41c5c00482e0002d144c0790450280c020308400801d500d002040407102c0311090104502507a80c141d030f030b504484070041000104e4800380c0e0381e41601a000717003251082c0300c942050b81080200304c02e000c490708103a403030340864195802100d040c0c03030440040c0140004419060030400710500c2c1880140b03d542000800039480f44680285e45040c00400030700b4016613030190090074400c2c001601d4042c442032514000301c0c060805000051711460f60a20081110045041c03168169078840c800350300c941840348140401030254030b403039a0502109100000d41c0102140060000d000380f021004d88a00300000042c020f586199125400e101c8003145500c0c2010b40018860341c00020290081e0b004401c29021038001c0641040b212000e001d80074a2603000111071000b8001c100040c0c070740860880070628210340c958071149000075540820401044130040c04d0010750b0300b0039041f000000c1c5400107030380000d243c484480810342c440d0400c0c200c104a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 965325269 1250 965324019 965324021
    0x90a090f050a170c28050604230f0a0206160b071205060d0503033c0f1006200c0901030501050406240608090a050307050f1902010e1309200103 63
    0x1499100250f1580c1040e8a411602d9141d50703e210b002d4a188a203040320544544081c07010341c0c543d60b0040155403441c103045c104824100804a600b4070410000d0506041c1102c0010b000380c0340007120005005501516820070000e03074005412010201000c21500d000704180d910350714080c8d202c0b52501d19507a83d44441100c00c0c1c074001040300d403007465018106808510080210b80d8070a52100000c0702071009101c2d40c030303030080909440d0031042c146404142510b03c200349017a400750444c9460b40042d81c1d600c04a50901700180d000d0b1400180c0041103a00c14550031004032440a090f1800380c40901c101c2e480030030340f0407600740d205640e141c0d100d41c02d0006100c003521601310041c00d0350400300c04400301c841c0a90b1030b14080e44a00c0d020800702c04001101e1502c2444031102180cae01805aa54500700d50030850b68a208062a07014603004103109440d071904040d0105500c150306844450307100c0741c1070041290344000030540308051516982401300107014007180354001c0d01805544105005000c0c0014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 965326519 1250 965325269 965325293
    0x9101b061b12060311010e0301060e0106032301290c030a0c140d0e0d0201021009031713170f16030201050106020d09051807121503140615090a090f050a 67
    0x14015240c45414808034181c124a6131005c0400c0c20690701e030782c482c080442e00400c119884038001c21800c800204d0340c15490b030020001c1c01d0380e83e890051104660350071500d0001d020f12907556115440c60400c50040030101c2c80c1e20703d8000b0035500900b040b401c20552425170b40680b40da0400a4882440385041001c20181c94007d20300c3c41d40200000742507800080c081c0910450554401e01c1c448026108585c400c002030308049601900034002202c8a00d0050640404040350031740c0781419034006641c0700c4800119441c0c064220b521160841210340c040316207a8007031802c045440d281009480403203448240c01c86141442a800040d1541c500100241404c46140c000410031000d08020011a6119250040e1a80e01c0040c030790380c1d0f034540c0881599180540c84804813603a040082503100402d8452010041f00d00a208500c54209050001c0d070f10fa520864400c40540d4404a0007109404e0000c440b503400340880000180d041456261940044450303502200e50340c3c0003c0f00041040150002c0e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 965327769 1250 965326519 965326547
    0x110115050a09020a0e1c0f14010501080307050a110a080d0c030e0d08221d040510180f02010e0a14120102361518030309101b061b 57
    0x3c60070162078000003030196041c4501d031845001508078084401528003030034603603a1703840324800180f00b4640c0b070141c810304201c2c4c0850070254601400029104404421504c0c50f80d4440040c01404440380d8491442e806d0b040f00d0b00707030002014400425040e1007007003000f03841149507c60021001003460000e00500368400c18034010300c88403070000d0004210744251000100110400c201d200707580c10b21079980d045a940301e0700d0072120040b951010820f80181d0180075a00480c20342e0020080120203170140c1d203080700a9030501c03214a104501151002409070334861051501041d240c0984000501503082c03900140c14109180210b03040b249051005019210401c800039814100c05a0505001e240382024006000d042030040000705200780032400c40040004110f04820402c804c90100d0301e07004050501840720b803002e42660740f0b01e0000140e405810300101600c40391244205d00b00c0b00c45174a0069a0b03408a100040c400c000340b06030080e032146085028000109190914000700354209d41606 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 965329019 1250 965327769 965327771
    0x1509160303031a151b0111041215180206091315060e09040203120c01020d020d0608010f11040504020901030f1b020706111b01120608071a0c0309040507110115050a09 73
    0x41c01282d130107690165840c0d081a2a03800301c040181044182c05400a0303403410004500015021401054400e08465007034007035112009040300310001c0d01d04540351141c0c0d04602e5000b2903141e01c010b01c1c01c840280410360024003110126a48148240140d074180d07401c419107621016010b0010035840541c5c5120604210307005401401c10340c0210b0b48410005903000c0d0440d02c0050802c000d10000d40446075100d04c560000c540e55080c004a05000740542d00405d8455400e040c03440d0644c04070341c000d01c00142014000c0301d181c180742904000081d07006902c600d06164a460405d102513034140306182c009025501d0050b00c0701c2043c50024140348180c2c004406100034500d021f600307200e00050400303224940003481265911401d0060b0707400d8100b001c0b48002d540c140000490240d40200c2c01104441030300115141c2d9a5218034440f19030300a18413180d0b05a403050042e48007516054128a4000209091000a040302c04900c2829504085560032a40701400c40030000e90501000750740043c42113082c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 965330269 1250 965329019 965329039
    0x30501060e061b060c1815030403030b0a030f030c0c090509102705030d050f1015050c0f0f01060b0f0702040b06040f0609080d0804031b020a0b0c100b060c1509160303031a 75
    0x19007c80074007020780041d04040c0c0e02c400188440d1035281021010350f4106034030404070226803a005041c7c2105000c2103550024070200060380b02504c1c06280c0c0034803440d00280180221240002c001044204071500c0c0c0b04405028085040c580c0700100035100380500e015544d14400b01e400071041c3e0308090070312000200081c042042d002503124030030302501e40c22900a40040e0140070204c800e80120715901b030040c05003150380f40c8605800a10391510f14060070092201e207540b00050f000c903000b50002c20780720b004100305160040c50b2940c00840c0041006200600f41500e80b082d0310b5114401e5000740700403d0300c0c0c003400c0c840d03600c0800ca030b140c006000e89821107107440c00780d90091216020180120503240101c1c524011941c605240c94003510b0140710542e25000c1c2804941e50759800b66131051030403171030240c0d049100d0030510102c1e81d00c2500c403802816804125110400800342c010003030b0f041070003442803062444668224000042d03001ea5008600900c200104640c2c1008000c1302e00e210b07901d614 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 965331519 1250 965330269 965330299
    0x40f14042706050c0d050901021b06060127080f0307110922030c05010203070c15150506070302030c070b0405040b0a1401050c0c0405130c06030501060e061b060c18 72
    0x40c00001e94298008000704060f1a1402d20b480345010310620610918207100411025103415030244c81d9200b840141c801e00d42d807000044644030b04091b500e180c0091041202d1862901c100c604c2c088889000f1382100b0b0200b680c0310f0003030b030801446080c0310080d508001030410501c00303410050075904004070380baa03940d414420b04103680d2240c100b1510f000500d080d582941450302403484051440d4201c0025913513868400c400500115403e04102e4000002d030a03000c3c3d101606228040c50743c240c0340d00200c5014244004c00c8540d802c50a01141180710400c10111303c0340c4140445401007034401c1d411610f940c04c050402c000c0e500c4900c0528001d0700d032200100621408803442c15810082801d01c01c1d41c8081d03000b810340c00d142c00040450b0300603041000b0301000c40e00300034000080314000e1000e0591030742c0b282c0044045c2c0d002031103803100140070804403029a1400c1401404110f0788544040307404081c096905003094012140d0940042010850f1035407108a441c6404010804440704030313900b580c01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 965332769 1250 965331519 965331581
    0x91807020a030f09060c020f040b0d05010e010e030f0406210204090b010f0302123d0305160e1b04031208061905030709020c1e030a1209050a03030c05040f1404 70
    0x555000e44558048c1c020202541c9403a405860303002c0026102c0600c030402c43c10000d01030004c4184182d45507203800c640f125682000300584880a01100d2010328081c40c0683c00c880026641c0d08000550410080144215080d84001e000400300100301080d1142c081001601200698401c2c0060600400c5a2907a00152100c5946d00061740083d120446500344000c02400f1000d290150a00c1e6448407031031083d0602048200c1140d03c60011950f101500c120300701005442403040780d94030840500070810200e01003001400e1340303800924050030203640703856210510180c0207290020520f4641403001a00784049034002104107020540000c510780360204c1d6440e60940329050703d0650114000c80312400c2840785101a110b8401d402d0742140003036034100d8881d0300504400c400b0420494945c82002e0311802a04042070308100940a810348540b0154080e2946010f040100042000f0100c0d02c42d0306001e0b450058810212440c03484402c000522003203030040c3d002069010174a42420700b45020b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 965334019 1250 965332769 965332787
    0x62b0620030c07170c030a0503011a04080a0b0c070210030902030d0206160305100f180506090105010c1e121121031f180b040c09051302091807020a030f0906 69
    0xb00c04d26540c07000c4c1c4454402a02402032001840d01c601000440c51030059000c009141a80c00070110601c0003203045000710780d14403031889562441e8100540340d50101d8080c0d1012948142034185151402c4001d03800640800200e400e003002003980e650140043d810100000003507952140000e00b00c506181c8907090510581804000c20541c4520010f005000600801c10080c01c00051030348981e03458128510104000c4241c0d00721240c580030000b940c0389070900b4107904907081078440c0403102c02c46481d0404403155911550b00240c80c0d0354000e0f40015440e80c10760b602d04005a4464034600c4248908504048540740a60002c4804103140342a42002c030040382e402451296400600d0380340001000032006090780402c4000c00c44082d59840703d4001c0d008901c1502d0112401c0003046401c250640c0c000e178030760103050380102c400c0540401c201c286600400c68100000d101504803242c00701039003034280086903110010b0304240d0340b400405401080b6800103507000e0415059103401d002008100480c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 965335269 1250 965334019 965334023
    0x70905040c0504050d0605010e0c0a081302060c0714040e010504051b1503010b190201140f0c040801060b0705010b241803030307020c09070512062b0620030c07 70
    0x10341d6500c1c4540050048049030000c20003c2e109a1704084c0a00b880c4005000c248200710b488014140081e0100c01c0d941c08917a2080303203c1d1200c000c542c646506017a21140e26060807a081082001420703000c0c081002802c004100d02152921145103c105010988161350075078580c0d80e05010912001800101c0d00070b1980884141800c2c1140008000403122080c0d03071035910200d400040003240ca070805138010140500b020580d041c1e81194107030220300300c034210a5110003620140700810011040d0010b0070350441c07903889032a82490388614002c1c0c2158850350101c01c0100780000d05004020081c0242580080e080340d60141d40d00c1c048011030313a9030164081d0140c00031000241c20ba10340560303403448814142c1c040e0403643c030b0386050b50005c0e64600c11451080e10480a00340061011885001190f00e0a061003a8800141e101c01051004214020540034440103c2c03500104003d140800f0000316035004190210382c20858441d2061402081c40074a03080000400400201107010401c4034050740d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 965336519 1250 965335269 965335271
    0xf05061e0d0b06040f03020f0907021c0e0301020a090509010905040f080a0516050c04061a09060c0f2406040c08150a0e01061d060a0c0b0910050c0705100507090504 72
    0x242240d11807400034006000d00c070f54400404603000c29205501030100041d030b403007a1a8280783c050420208a1140c40484031040160b005030010009801031000083c1982c1d51400c1c0001e1000c0240d000900303a81007110380c480015002c04080000c8d1510030070340e6004240c0d14100300058203154075188254401002e002e40300200014a90340500c0c0b10b101210150b80c8107680c060703c0d82500d032802c1502c8041141e0124425820510701042d41c5012070b0203001000340d10005c9502e404001c20500800c0d80010082c071100d0300541d04550004003060115601c80c0c00c8941c81e07050641c008400c20710000f1400b03400d42d4003441c071f480380e9003114076000030b6a04e411415410300c4403c04075540001034002c8c00990041441c0d205c1c004000a549038118021030a0748100c036610040d030100f02014860f241c00341e40454400501a00da01002203041031010a802c01c49103025940750240c40d640501c00d854058500c103d1040c00000e1070070a224003803100503101c4084103130a105906007200000e0800c506409554459 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 965337769 1250 965336519 965336527
    0x301080d0e04020705150718090204060e0103270c033206090303060108190f05180105090d050c03040b0c0a0204050a15140105160b0109051303050a030b04020d150f05061e 75
    0xd1401288c080c07a4001e40c00203002030b51031b00c0e05880c40280d04180305220200c1c1ea04401d80c101d6601a0261016200a80c0900400341c4141414200f80305000c45098400c0e504074a004408211000100c4220000003040300824590502204401079815500c0c2c1c1d5081e000801448810400801169017203070091a102c5156140d0240004e82c804102144a07011031030404142003036282d40c0c014a00c29114460703410307000e4450b194240d007a540101d0313044600742c21800300548061302440140460518620440341000e8481039206180d901144d000511307603200200b2141185003602505a002941400510005800107280310b0103c45034040c1c920364011050205505900c190295039030046058000341c200ba00504141d41d402100780541c405090402c00014200882d0b00b03140030b281e44c3c0c16510607240c04100107081b0010f10404118507032058082254084003103050150141801040e2000303595280380807520740140e80103070700090041d81300380107101e600c2049030b44003140c13410700c91000d50791 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 965339019 1250 965337769 965337781
    0x3020a17070206060a09060302010e0d0503071b080607110619230906070203071e0f12030212011502190f0209012301020c0604060f0c02060301080d0e0402070515 71
    0x8110144064400324416031010852159800070720305002e05800d0710354504081d29220f9403000e4507a6400041d004c14181c8201d003030f003800c1801004000e0340c000c60a59060055540d030701c00f04401c42c0400642d0402c5011010f220307080040c001e042e044019400d2482d0061048402039444280040c45c0601c5040c0c0051441d440310039030b4210714804160306691403d500c1c10b24010107114003043c2d840380c02e54441c0702c001442040c00003040780c4186411020002e0b0700046403000c00c8038000c09200031980c0450066113240080e400300000510803103da02c016031214007403030030020481b5050b441000e0041c02803c0000000b5004150140491014a0001841225401d20341c1c1e44001a00c4000e401c54617000c000100f071040e1107a9030200b10a41104803035107815a0f00120703595842002c1155100508000030414540162090f5000c01200c2c00c003a440c4140c1070f0009020740c1c100341d1000c0300c1500240088250f071755104504810513a41194110b042481c07981740c16641c0d021322980b001003051a6004514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 965340269 1250 965339019 965339027
    0x114090f060a091715011404061e080c0a0602070314010e070b03070e0906130c0e030d020c131a0918250e0906040303020a180b0a030b0906090403030f020d020c01050114010c0309050103020a 83
    0x2074032b5444601025102003010440364114076215503015802215062103003450440040821109290300600759103085032a0341041040102c0c0c04580c0f50768034120001d5000051113000010030761506d56589030300e46120041c0c049585d01e101240300e100300000300074003592070040410301d8040c03094002484c140042000e43c0d08820001d2410b605204209039042c41560006081000394815075609209552014000c4c0a40321988090450400c181041c243c003030401c040c1950340300044c0301c030140e5400851a015810242c04440800b0b90b58644040b50b0801010300c14400c00a0100342400c02c0c0d80c8c900700d0015500e50700060401000c1607000609080880e1250b2001030300c40050010590300e40c0c2d0344142812655002c00c05800c0801d08020601000f4608100c419100d080c0c041d0085e20140e49a036000c500038100740000034080c550078400ea040d144080d2000d007400e00712180c0000740c69410034061012003440e40c26158100080a90b40c4000680c2c00412401101c0007800c0140e1036100c03555042d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 965341519 1250 965340269 965340281
    0x109030e120607032f0304051e0a030c17160c05030304121506031502040e0f040503180103110705010b0909190605070509121c0e0114090f060a091715011404 69
    0x711602c0e04080c21010b45e00c0b00c1e5000318000c500c180c0c21100b20070040c4660001010003000802e00c01e4000e0030140380468000e81c987c60fa2903209820781e0303141d00c0c110b00107098035410180904103040e03110340362142041610b88500015040c22002181022b18040c144880030103800c20040c402c0802c80da02c51100300d9140c11070300146a00170304490f03a084208101d40000d403c41d219105070050301c4404030b1101d48003002c1850050ba000320141d8580031520a138810b18125130700c2d016040540c1c818080c4460030389003004d42205440b42e000403d150800d003040052200010340040310a400c210721f0740f14404842040070f00f170705a2010020401360f4a129007030354035000780110150404007410300101c0c44074010a2520090000640c00c140c44030382524200c80600da03600c070b1140400c0d00540780c40051080300b40600400c050041c041400c0c0c50800340814883d41000c04030b140800c124410038002000c0382c0e40441c1000140b0301c010f042d030383c4440418445404041c890760b1641500e0038202c00c030300d80741ca420017 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 965342769 1250 965341519 965341571
    0xf02040b0d0b04050106150801060f1110020c06061801051201020403021801230a0b282111040e06010e0301050124080903040b25050109030e12060703 66
    0x40c40703200c880703040246102c202120101c646502c0c1c000c0210303c1c3c44001034903852095913030381c8100d51607082ca04251942c046504925092101d50f105100c0c00c1d0404010111a101c3c0304e11015860340000e00c543c92410310084c2000e881019103948044076107075010322013811520b0440d0603d501442c5400802c0c020701c21508041e400c1005406188403860780356000c20b0494a0302182c00a0510030fa612001c0da070071742030713503404e91101c06403804020f5110b0510117440303564020b00082c0c0340c1c01155450501c604c8400d4500d007000c60744141c062503200c00141c46052950304103007014000b04402411075081480345000b02e520220310705010032070a0344161400f10f080720340540204400d503120030342507060000e00c1081448079a6500da88425261140da416801800010015410682410030002c1d8581040700c000034410540701c030302120300a0712050303044440c1c00354000240c0112503080003054102070100e65030090007602d040d031800100004a00764030200600d0000340b42c107030841e41400d10b00b07400202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 965344019 1250 965342769 965342779
    0x60f071a0f01032001120e0c060712170112060f111602040c020d091202030f030318060a110901032403060608060f040f121e0203091003050105030a0f02040b 69
    0x411a6854101101905a9019542007444980c4180c46544031311611122140010008031007030440a51030780000b94006407510581e260820320002150880e00402025100310700c050180b00c6029800050403001e416440141404644c1411460f80035440e100780000d08246d5107401c4080c0d00038250f03101c100344200380d05a281c2c3d07603000c0e1001c12030b21124507001a4801c0d845c0031500b440240c00003c91019501c030640307452111303500c0c2a4110b0713000d2110a90a80e01801030403002200004240011072290a40c0d41151008190400074145050b000410040144e4078107a500f0f54450840000d440404000b4a000711b000700003011481501741d2440c40c0100c0000d0003150200400445400c60350a44401c2402c8984d03d50b0b4921500c118031405440c0030b04104044a02c000124010f0211a030050b60b143c10480307003000d1310b142400307400a2100840030060304040742281c00742c83c0c1951540d40200f65460140225410300c8002910740d0900c450041c40104c10725a032600f1900c440c1c014280c80480100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 965345269 1250 965344019 965344021
    0x405040603051b0a0f0b13080102030705070c05030604171813060306140f01031415070815010c081b070902030c040317041203030903020c0907121109060f071a 70
    0x20b032207a5a446180d4050424040e40e84608089080202c2500c08440328400c2d1002d1a0f85032113043c91982d44901c02c042e014401d0004041440d60007400210701034411962440d40c1c1c0c50280c1420482c1d01c0880e00003920a42140081c80040b07140b0804001051118a401581c0da80c0183c0180744161021064a174203c20329031250081c0c60459030008084a000c4d04050115020b5004049000c10089441000c5011a0030060010601007540d4500760645078086840d400342ca10442d501c8120304a070100d001600c03030410070550840100d0603030b81e00202030805044007025541ca9072000c0c059020485105802d511a01412410400800008008a081c1103549003080c103100c003c29800350000781c4101d02c2c03403515140300450f028222011201101c88403641c1c605181d074101c0107030501e034200b0b400b18403070004081e185a4910707000d18000c0c051a01c95504440c10284260103540d44204c004500e45030a10810703d0640724001151140e81e8281103446e5100c0062410000c10f00c034002e03c00040541d460 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 965346519 1250 965345269 965345273
    0x916050f090d2414040206040b0c070905040c0f082d0a06020c0322080c010c030c020603091b01050a09120c0f0803090310060b090d020f040e01050402090a0509060c030c0405040603 79
    0x107102444610340e00300140004c40341a000403a52007000d8030000e420507070410040080030f8040c2c01034207502d50b080d4103603a0ba090762240040c0645000395001d807404440e851080064a1209441740300611240c00588000030710341c031960740b411901c05c4010a41c218030a43c020000e840a11620b04c525500c08402c648404116640b1540c1c0d40100c0030303408000b0510a40f410700e03081d805602d04200c07400000207200645c400700045440a000803400c0303040c041808001c50042e62018050340c46030300528001c050b080401c013501c80f070100c600041e071030610100f00700d503004103503004004109440200a071000d8104580c41c000030214003980c0840b100c02c0b240b442c0800d100704084018007618000f01c0848108410300070700e004c115803a42c85904138941040040f1501424004196400d260000700301182e002c405070f020400381e9036403d054a00c1650340360104000c40c0303040c0c5622900304900441c108124035280c01c503141c0e15000035003200718291010000a8010038100100e50140c20042c00504c4120b80c0c074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 965347769 1250 965346519 965346563
    0xf0f06040209100e0a2111012a05010c1107170a1a0117030a0e0f0109080102030a0f050f071b0602090301090b06040f0506060306010c0606030206180916050f090d 71
    0x13140f007038420a003103000014200d168032650102d002644103aa41c18440941d00c1140105640c03441506202c110700c04a06040b0302d1000003042d40200102c000c2c0d03800c10314036001c0d085505c07a080c1d02c82440b04a019603241c81c0e1001480380c054279003d00c1410b8444587c1b0b46460702c1d0070103050f801070640e40341268025082070f8a5406504880c1c9010038240c2c2460b6040c070b82512800b8040d0708030005820941d58903506d01e005440804075101c181002e11810340c44034442c509a0b03001701c81c0745505503160b18080b058485540700d5568003641d113240c1082d00e230070603000051032420b014465a04540eaa01c052a05204a235130459403001c00080013000759130610700c0d203071040d20030403a1807901c01d074a0302c461480301400d0b5000d52445240d000f0402c0d46541d644000540b01414007c40c02e0340c03d6a9204000710058a952005021201074600340c016102c01da203003000b80680000300802c400c11034044248050903001001d48510940000400351250800d0340031410080f50701c0c0006e059446920340e90a8401c0310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 965349019 1250 965347769 965347787
    0x10b090903120721050c091807020c040209030c060307090b0301060f2606060c0106090f0603060c050a2f0331030507182d0c080f0f0604020910 63
    0x10a6402d102d0550f01d0103c01e981c08078043c0c2d010200344564054910760445560b00c00e07a0301051400c138080c1442500e90116540b803501401c4614841205802c2c0710b411038040012868206084500398a80612078010070f4452401c07510301d038020800840410030203801660060701401000c2601c64403507a59420041014018080c0c0d100840d190003000e410f41040c1d49100c004481d4000208142920350f501403100581c0040d043d042e041d540c418000c91000e46500881d406910510b001040140c110f0610b041100e100707103081c0c4103000e010803a000c1c0454000d8180d06480c4416101c4200703110f168095141f46104a8076170200c0d9010000b8000c0e00150820f01860800c00682d100c840380c0d004041002030070744007a01010b4081d5120b0041000340020071842450000024100070035002170304000c01c00d206003c0007401008240c42c100340319003041d42d4032900c0074108980c5085c100754142018000080c0b40003a0980100e8600c602c00a44180c44640403903103000e4014101440000300680c0007413000103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 965350269 1250 965349019 965349037
    0x50408031204120504140d080c0a1a06030d0f21091b090e030706020d061205030301230919090b13020301050604050105010f052803020301090e0a0507050d020102010b090903 76
    0x8078481400f03107800d00c100240da040d03401c42c600360100c800c641010020328941031001152072000402960031040c40030300900b5245c45c401c800305c402164460120031019400181300034001da002200800403a42c0c00f559101d61200d0f5800e16003005800e000010403040c0502ca550038a1a007042058010010342d581440c0350703107403030b20384040030b9070380b41c03111842136451090000b00154002d00200010580e55401004100a040c100181032641c8100c2070000d40201e0a06036030541000c030041204080f0122080500340a84403201c1d4182941070000301d01c2c403070241004c1041d01169190203609426903100c12061500991380901303620b4070285c9651030700d82c1140c04a0295003000e010a5490038117010301c90507644161508640340b8115a4100c0311504050b0382241c84003032554542d051008441174100c1d070020156005031f070340d41c1032903441e03410780b0141c4002c21580d520001025001c102d000c44c3c02e00a075601215601048002400100e001d07111016840341d12544034408e2040c0b80c0700c00001022120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 965351519 1250 965350269 965350283
    0x60305060d020a09150302030d0906170f04032f060603070e060d020f0d0c180501080d020a0b07050f0c160803070c090203190c0201050f1b040e07050408031204 70
    0xd61404103000301803034000790003504490b400f80305002041c69a0001d0094034406200584800d580c0e4000034540724801c501000854504401444031030303400003030710952424540c00d500c00d03414002c086e28209c0500410144c1041459415100d02c07158001c0e04182501880000003005080b40d50b2094446c542650318070b00c284505000003401d000c00142d10340c8941030051445640e40c06580030712202c98210048140c0c0003890301c42c2d000c001215440100c02802c0e4440304401d80000f4000482d04036030f0181c0111407180c0c00044194003250340081c0e1902140d074001c10520440e100c1000c180c94030b00550b00102c04801011884c2e4003d00310020b81a129149420109006255101c401d2502da2084440141c204214108144604104ca80080d60405d1680343d41d19201c01c440305543d400c03a0b1550f01c5c84070060751104188218003424101098101c01150805c8080440c60600450300e48228070072100d10708441800504494080c400f65002030010b0703400d40e552154260780d01c9982800480307080f0342803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 965352769 1250 965351519 965351521
    0x201030b0d0204021206010f0f090e180f10060f05061801030204080703140d2a0f120509090a06080a06050619030f031b02010e1909060b130e0f0f150d0c060305 70
    0x29620a801271404440707591036817104a0304100d110350741640300030652503a00d0b03041c4d5516680501d003004035075403c01186026110880202c003040c0240c50312030340a0442060300d904144000e036640307821070b04110035520305040b4241d003100060740640200d40c00b90b0031a0050840001c24000100c0c2ca440c0c60781429000c0d5448698034902c191a144074680840b0034050450000b240f00810484994070101d0080354898903416040c7c1c1d652a82c0e0506141c12000503030007140c68075150a01404240e04508403000500c811418401c03801d03619a10400d0140110b0348482c003180243d1035541240003852600007500c41c085e41c890508441495828008500142c0746500d20040c01d480c68907903204140c1e05948041d5030301c14000801c11040080030100c0c203020941e40000440510a01c83c11000742083c1070f0050b1550410b02c0d0b03142e86101a90302c01c44003d106101040880302d440d4564035407049420742400740300d4031111004220b0b01414042d080c0c100e812210400c052101a903190803c440030791b81c00b4011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965354019 1250 965352769 965352797
    0x3051504030c020918010c0509010f090b0306010302160f11011205010302030c09040602091207140409080d020a0203070813030b161d011803060f24030201030b0d020402120601 77
    0x4840000c9901400042070511984010b24000580a8000c00ca049080842c001c5c003100f02d608440068040b080400c03000a0a8811960440c0c20101858408d040c031809091070100340c0ba01c184002031040c0c2c10150300243c0b01c101c1d8100c0d052540d0704580c11081c440341c5d0390803914251080d010150711490129000c40071910a158440c0111816264040c0150051100540038840107102c080e00c1114020740900248080792a08140b2841010042c4010000645004050201550240402030250742442d40510100d006641160560b006003800180c0c0d40412445c01c82c210f000d0008010b12828002a400c0d0680e24036040e1001605d0140450b4007443c1c40c0c02280c40e0b804600303003802c1c030003040092a10b1940000c00035a0440010f0040c103041c4641c1d14441c142005043c0c0304d030001c032140b80d0394810307044d00703100c03644108170161b144102d031180500200214000d41414911000307041540740e5803c2c41c001d86500540403201c55002e0410754880c104210112019801110418002418001c80c044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 965355269 1250 965354019 965354053
    0x1b0c0a060f09060621170424090630020c0604260909070c0201110304031a0606072d0b0c0c0f01020a09030f140313060807050a0801060e0d020a09060305 67
    0x4100f00b180303485c902e10740c6010782c0c1300e500c001c030154440c00d00c0386005e00c40091040c01c110450382c900f21014a00d002c0580c80514003400300400c0e600500d0030061003981c440c540041407512225412040564415004040c2556001038030441e000c905480c05160700b0b000411840d000780700103901d01581004411540c242e00090302d40908049107034080c0300040440c44490192444000c0b460040c540400c0c0c002c0701400d05072840d0b2050740102c42415180000c60349500c80c2c0240f941d00b166046a81ca440c04000b501c2e807d44592010380b040407441e25141d40fa40b00d07102c1000804510541c0b00101301c40e070345410040b40c2c040303070012401494a4010028141100311040c4215a40d20ba101d881d03004249003592180c05000416110840d4546415200c00c04094020000781c00700740b1520900a82150410724002c1003a400600114180001030002420340c076040a1490306541103440c00821000c0f6220000300b0448400038045c2d000003c01c280802d04403181d4000030242c902980459240d185600f40c2c4003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 965356519 1250 965355269 965355299
    0x509070806062206050a1d0f0603090106050913050d0306051507020a0306050f04050f030309060a0e01180302100c0509031c020f07090506181b0c0a060f090606 70
    0x120004400c400040c0c541c0c80e0150140c1648815104010100154080c6140800c0c00c2d54200401194001c134040e080d8a45c400003c503440c60f1544e91442c00c4074602c0300030030503401000d9102885040003000091401c5000d45c01a4024a07000301a5821030400d541c007020406d0000f4029507250081c400c101d10058040c1c0561021200f01814111581c0d0315424049615000410200c1c0c0c003500c4a000000422860300030503025030283d440c40c003507508151605510b0400c0c21081c21801d0b820a004100f10b0720700100780603501035420341d40030a10b05400c1e842d00e03004000c503420080c4043d900d035240e030b070505074001407400d4034441182080021a900103001c2d00c5600950907001d46c580d014013404880e4107855800115071820b0b50045444028640750140d0030041e9a4021000d41e513982d90420a00d45461004400c2010b084a0315009604100040d407074880c0640c140030481a00000302550040410010410300540080b0200000e110490f140805002072020550712941018404206500fa880d425 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 965357769 1250 965356519 965356531
    0x31406010206060112020903060406150503070312120615020f0c040612120c1703040303140f130804050a03150b030705060712030f0504051c0e0f01120e0706180509 72
    0x10406503a403c00111040209014541002e640074001c0f91140d807030403c4024055886100081544490402d441100135490341c80588a50702ca40020804500701c001c0d160010300d81841c01e142814003641c0b41c1400360403154403005c40d04042803c4030200b141d0100d01d614181500a01703130703a021820310040100f0b4428034021262150003c035020380c000760760701b81543e1000c1011300740910340e0704040e00d80c44440d1100c0c0328440b8280c01c1c00000c1208060f810310a080004030f4609094a29042000420181c1c0b4002440c1d1002040704041c41400d10203240c0956008010061107600515100e142003200f590511840c0c503052810314282d0282e80c900454400d00703a4101812a80c10040f543e211a01c83e16110803015090568440807010ba00303456009003440f843c02817008041d00c1000390440d49141d10056421000c0100401a07504141e90760100c401c4160024613200f0004807000700318000804508000040520800500286694108036000b181000c41d1100625181c2e070741041c030506810899203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 965359019 1250 965357769 965357773
    0x506030309061308030a1709011a0409020409080d090302070b2b0207150209090601090f090e0309030f1c03020f1c090209010603023103060905190b0402010314060102 73
    0x51001d4184600601405141d5501c8510425611402142540c0c0284440400981c065005464814802c107107580c2142400000700710561680624403082e043e501502d600c0b454442030500300303541d40c40c1c0281c802d047c2c11180c2c8541c1c0d4050800a000246a040c4003100135000c0c82d000014125901402d64041d1401780c441001c401e46a0415003211006400e00d0f1120305a0900251020450507003060070100440c1c240142e0310510b107800c2000900c0014000c0d41000540e49090010402d42200e002c1103c030990f10105000e51004100c03401d60048603001c0c1d17007600c500c020707041e600c00000800c1c4c40c0304080c042a0be01c104107030940480680c4581580862804030030805064072480150002508116107800017543c201968000b1b00700c2003003079114000103a008155480d4250708800180c85040203c20703150388107202600381c0c8a48a000d4400582015951400502807150034071a4030400c080c000c030500c40c8a2000c0c41c0a00c1c13882c405039000d034000f91400c0e02c02e145454590010a00440050300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965360269 1250 965359019 965359027
    0xc08061806060708090a080d05030103060f02090a0e07030906092603220f0210032004050315040609020310061e0e160504090e030301090f060e07140f0705100b0405060303 75
    0x311404c180d4132100c030036500700c3e10010300064a40780a100d90710300e03107030156509a500d51460030100241d90703e8070742590165104004104031581d41e540030f0402c49440b41ca510455550300d4005400808126001912160900030500100000a9400f0000740c1882c0891803032001200c0344054240800c4034107414407030a10642914032400d42d829519060311801c1e400b02c01c030050743d02254000c070102030740c4400701e45c43e82135900c2c0d106070b040301100c28041552401e6041510f01400266a8070608088403035a0103003001040c1070008581109550503005000c54200060103031281000b404a4461600755014180400345d10184001d224803c584c2510086030154a919031200b200384a2050040b050240400000800b440140548075020700184051034582d854030307039002e00f81c0d4010001c020b00145022010300c450b854800007540c11002d80e140400b0b64150201c1c00851a10800b103840e844110042049000c11800261426040740349040c14482010003400f40070651fa42a51080d03070503007040c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965361519 1250 965360269 965360273
    0x901060b0f0c011d01021305010f1403060d0f0f0314030114090901090606170606030304080d05031f0e06041d0c0415050a062c03100c02030d0c080618060607 69
    0x24050031030905420000180240e004e2440e903424000034000350241d94011a903403030000035503500c2e0001000282800e8283c4036040100074901d600030080c4044c2990003001051094940030765003403c290b40310004074208517450034a260b049503c1001280090008000e22011415440c2528101d07800110b07440d03080e0303928038100508450010f0404420399620604400407690501a6000070200f2000701c51141904003503a03420321500600342c078000c0d8030410080244a8000555003074086191801e69100c0d224030340181c01550302c2500d070201102000a022401c030440d62042c03400340f00126405c0054001d0f01c001000c56600d1910f01605d1504020141600703420f16030409401001d1482425404039182c41c000f680705862900a64001500d14044407159484100e81c070078540c0849c9110b0703106a40d00000a941d5081c62808000151380303422444200500800c15142201041c2501344180e221245005000d0002220558401d00e8405030303500390007201c075122074040c800280c51149090115 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965362769 1250 965361519 965361547
    0x20c0307030531050f030c030606010f090f15110d0e040b0f060f070203060c1602010c080d0f1505012a020d0807050a03120522110618090901060b 64
    0x56005503040941c2c41100421043c10521039103d91400070783e581c3d045505080c01c1c40707140c00a484009019501c0a54030409584d40000c002da030201007440c02d40b0074144c0e09102101c03044e200d94004050104110408203a11641180c0510310158a541740300e4074807010910aa039401c00f0380954000308890007104540c81c02c054001400460010b404012941d004d900460382a5101000d035480008012565904514040c403200b904070746004402d5081c0310808040b17101d42c0b01202c00090610900f01800401c0100c80c0085d2080e80d40e240700d0401003401d036041c005c006045a00e04132110000101e5001c50b90358007480c000440110160006504070600c1300d030039945001c003240180c0c2c2c442e9400319582c001031020001080755621031006003442100503e0045d01e0f590303241c107159900714100810030006907652807a01d00f01c1420200440405455810b0490b0484560b2010a4004c4400524080c0b0a8100741040404072000d80703404809550b1421254200c0700d407802501c030740000801041511601e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965364019 1250 965362769 965362777
    0x6160b060123030405070603051b090112020a0e2e0503060a050306161101092120030a020721150609020d051501021c2a03021f020c03070305 62
    0x1810a01e011403814111001c0c0c1802d05907203428440c800204100030090306006140c000c0180b801e0034401401c00100c6186011001299403d0514002c0385c0c0c400d16a10450300d241c5c1000e0f00308000c541d2800d00c0d1400901e8081c8490440d030003554400482020394460940726140b2550100340c148881034088000c5450341d10140000d54002d494401c04a80c0303a806100c032901070340b110128902004002600600600c400360b13454281c60345418540400306010240d41c0d0229030541e03a0ac3d0f03284994240341074031004600761900364014040040b80c44000400070040a52151070740840f10207640c3c0d09044212a80c50b00c442029200f5038030501e20006504c10500b0f4039299800d180801c1543e03c440d1007030201d0304445d03c1940380c03644400903c00c4901003203042c407070001c00030b1000d480310701c0c0c40844424105040c4000d0304104803e811030468043c484050300113500d664860301c0c1c1a09501820f0017036031118208040c003005a0071000c8603000310f01c0742c03007111a41e03803c4030081c43c14815107031410740703150304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965365269 1250 965364019 965364031
    0xb03010e0a020f19050901062109030207050105030408130e062d0907120e01091403120402010e060904060e0a0c020a0b0406110910030603030f0f122703050c010b06160b 74
    0xd0380c900081703500d0766600a50344c040c1103555280300054605c100720030a08108a07000d03e2159240591100220350701049000c01c0d204203080c45030340c07070f10b691510307400d148942c00d2026000b1000343d8001c62800c6039181c00e14000e0404460060040306001e00b5050310103582c9071005503c05022860701082d0805502551380142d141c10a00b403081240003580c010b80701071072400280359546070700c030100308130034842c102025088000056080c001c0f08014a80e1002c40500040c1c1444503404d9000c647d0760b0784204440500b00094410310000d82c5d65803030030305a8002560707000d0109090100b40280e961000694140b85600100070500c00d03200c82d01c40000901c150800c2c40d0514008104d8240a511110000d0088000d1560000703603240ca18100181540f995014600800222201201605500c0b80c42d0713030030850001d03a00003025444490030001c1e00c80010082c03001c0703680c48001c0754141034004000d0480292544008e00c501406042000803c1c81170351407440d1602881206800840e04540e29554402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965366519 1250 965365269 965365309
    0x5060106030f0b2b02030a030f0909061d0a060902130f050d080406050c070312170702011109011202070b19060f180c0903080c030c0c0303030c040b13180b03010e0a020f 74
    0x44c0094010a0034903c03256011b40124804170340989015038890071000060003070400c01c00c0300d5030500d05178406401c4401401c100b02c0c04e006001c20001c0300690300c4a001802210021542c840c07403064511030540710340c45848039400020350001218240b0500b100502e9902800007440d040c2084030940c7c01d60440c071031154a40c07191940100001702c0c3c0d05000c0b80116000c0c4c64007102510460124005120300510400469050110341002c0102e940203543c04a5001d003009000968504010ba0090050300000b402d00900d00c0d081c00381281e020902c849105004e90b4080c0200703905e03002e0f5182301012a1054020b2a0b00c581d6a40d81521841d0f400810007030071920f44600c149580e0f40314440c40d40c1000301c5d15501600000780b244054001040b42c412980016030156041d40b6081d008500c50340180e105091401c0400200703012035441e0080740340c0c083c01800e14003110603401e400900c0020807401291600940c80e00c00780d0640d84074005100c0c6801c55004148100302e005980512520464070701e0b040780b440f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965367769 1250 965366519 965366599
    0xb033f0f1c110403060626120c010e0105070c0c0602011404060923240c0301120510060f050109082b14030f040b01060809120a1b05060106030f0b 64
    0xd4003180c8003c100642c0541404109907040c0510045a10640d03803000c08940300c180641840c098020488602106180b1002a01e80d01c5841007140542800802c07209154a070400f00001c46411403683c02560340140900d0388115150801371f400c941100300c40060001426001800044c46c0e81c2000042c00d10414940000040140000f243c62420541c83c4075030742c004101e040c00c001c1500070428529601d140e804100fa044c14410800380c0d22043c0140004c65500c0328141052000c10442c0405820307015801300600d503500d02092039000341d54000d00340010104071001809a100065050030090011100c0800e64200412083c1c4c45042030320840c103001400c07014a5a4240d4103029511540c000400c1800915040c5416945010705070071110038000c4500c240003400000148000c1041c500c0301c019a5100c2907220180c2d007941e2061403421030b0707200c0701c0e06450402401048840c126a802d803000e12503c2d0a040d0700c0b10a0300c5e00f0300d10f03540d040281c03681d00791400c2400b082c0200c1c2da9041c1d520b4440e20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965369019 1250 965367769 965367791
    0x10b040605182d0f0402070f0210090e0708060907030614040f0b2106090d08151c050f0106151b380606030c0d0b033f0f1c 54
    0x41803030a0600310183e01d031031502c022040c18900d8460295150071a002c40c0340498a1750381403002c41c45a14041d009424076040e40e01020300451000002d00050500d060040c905000000d0500078100e038458050f032240030102c0c4086001e402528280c80324010010a42c44c41203091100901c10006446011030b201e010107202a1120340c0d690b00302540903100013060103040498145422000741403903400358071206d81d104444d44c0c0f046102d81c0040e14501c00440c44040303800052001c0c0381310701e10507000c1d1a5a26110040000000d145181a0340b580003d000b00c590b1841301e50005150301140102103065410018000141d2285a2115a108100c00c0044411060710340c04658a03000c0e10400c4080c408001c1e29012188500d020307401071084410a2030352404c54074040490181c1d4840070249901c0e21075840c4150303024854031448080b10702981d80340c6040700c00003a11071041ca6184a160703d80040e80325000425000440b41007132418000b070f0340f800c2401355080640380c0a07502d03035002d01c669030301101d54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965370269 1250 965369019 965369059
    0xc08090411040f06091e0506071a01120302010c111c1205040503040611010b130c02011e02030114090c071704090f0605040b0d050a0803090a0206040305010e06010b04060518 76
    0x2000c3d01425101680090a000020308050f010340c00000c003465403111191404070181000f01c042d100150380858407184c1c0307803910222114602c6071101907089450000300d4113480c141c20781080079009900a1220685c1d044040e07a001e02c8068411001d0340003071a00c02900c2280d000d0360305a0b6040c1d0b1a24995108011440200321102924100c074240c00010b410000654085101402d10703a51a000b00541142540010341141050f464003450b1074650b645015024000e5000400715403540001c13114502191042070001c2d4000d028802d60200034442c10502c031709150300d54921403070145896600e00302d40b40c1c9415440c4143d00c40c011401c6c000c03c11010480e581d55015140e480d502c05080413468a04020420080e00d6502420f00d000c1d0800380506c0b03000c80c400180003c0c81d039402054282d503e440d80707030340e507801c02080d000040e4021400040000820405500c2054503504c22415901c490f62101170800c114800d80c4244000500c0030302c8450040310240e8404080c4c1440180310000d15500e0a0500c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965371519 1250 965370269 965370277
    0x30405150d0e07060f0c17030a050a0609090807140120040608070807050a03051515131d070806030a150506090c0a02070618050a17010c0504060c08090411 68
    0x240400e000300e65207100e005640034a54038219200c001e0825181410001803c42d10100102401c0140c1c0d01122810310000b246007905450019403650355910301000542c000c3c047c1030302c80e02592840c20740d00150640303c40c400c825030740741d2081c0d4091916440d51141d214120b800580d050740c1d95a28800301119884494511446c1407041021684803850880040c20460f0000c0850b0148000700c001c00180c141c3c03160868135604000d0600040d5078550300d20091040300c030040c603e50408071180e850850491250064440f0040000244150f03a440e901500460b20040c0c64481203081c524000c12881c50144032210741c81035020703040b1051800192036918000c240c40c46c420740c01c189d40303200380000c40c1040c4a02c5035004140c2141d0700c1ca45500503400965901451141004004051902201d043c800b0b070707070351001403a008040002d683d132180403050400c0f190f502513120315840c142c444004507014405072402c607855a144c3e142c44900946400449600090b802a403096949241c00182da032031002030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965372769 1250 965371519 965371549
    0x4080607020f0c040501050a0303030c021e070806130f02060d020c0618010e070605040620030d023705030702190507080c04062102060d0609021e1603050903030405 72
    0x1400b00e442007103140ca003816003588009001e903060030014841d41d00c4c5c4082c0c10b81100d0381440c0000348280300c40c008a0920309807000110a40c50111900708004000042c07810a5070704490130750b0b0382510351039201c5600040c100310007071811403500c48800141c60047e002d40041c101034403025141c0800b85000320709204040b078040c64082d215000c072007811a001d102e41003c0124510040444500b860b03001f4056000e0f502c600000c005030b29425241c081c0e1121500a1800031503011640c0b100d0407903484501130f402c01c900b0202c0d4450446200c1c00840324000805129504084031044039070140b210846c0d4540c002403103c820340c441c0c0c03c548520403844030030200034240a00050030f0712508007040241046041d8490030302c11410188c0610035011542595400c80866441c040728541651020440500071801c462851508d0310000080b0180303640c0041c1000d50309078400c3d80110803d422001050300a00c0d40351100201c0801903400060300943c0144440c210050480e07040c00c1e5142c0001d04560b80e0f4180d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965374019 1250 965372769 965372773
    0x20d05190b0a0b0102060a0c14040f1d070e0114121003050f010b031023010b09090709122015070b090a240906050a230903070303110408060702 63
    0x22140a005010046a401400e444420f101d05258840000d54691001e020000d0f22a919070700d000d4620700620314807800608403800b050b185c558411043c00d42800380c0c410511607000310424009440d107042c3c08036101d0f07002c940ba0000b100001200450b62841c40c065540e602d41000c0000312003c00b00ca0046500c180c0b1854040e0802901b5440c03c2c40c00c0c00120107111016a050850102241d0f90104455490380c02031000011464030700051890f100c40c42c03044044404245a0020403100141d4005000c40b62080c2c805070001c0e125450704850041c0580304c5d07440495402e00c10400058104012550402c2611195201521401000544401401c0b5003854605c20000b10b180401140900d4a0791103010800941601040b88e101d8506440d000100c040e0440190811040311500c4c0364841c0d0318141c0c0000c020459458500441d500030301c140c000030300710080c100710a5220004104000c40c072509400019608112284e9003d03009070198000c2d00c909820103020208081508100840c89000a40c0c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965375269 1250 965374019 965374063
    0x40b0d0209182d0f061003020f0a09090302151b03010905270109030306360e010528111e0403120203091c02090612100908040825030f020d05 62
    0x3d0141c0c40d0420302041d55045411800c20014407460f140009400c894041d10b418800010800000e0640705071900300019051034a00782c0400c0c07550000b403c0d056030200d511405081c0c1c0f10002003078040b02c644040004001402c1005114400c0b0302d400281d04007020f40203213010300e4102c5455442e901100342401c890350b1340d204050400d0540c50301030540100002c20034074400042c812440500000100d403244a07100c507113421110105456480902a207011000800c03160404080140c01050405906903840f0012118400e504c3c2c42c074421120000f00f8040703414900340381d040c90740700c129444042d100100d14091200002042c0881e89210b6094a25405541d440015a0412400701d1101c517014400040128400c001a00c0c2d080145400070303401c403100c0d404000c01c030b00b040386458003440c1c40c0590903040400b01030030440c00034042c006880810f020b079042400c0c58a038407910280c0410303500c081103d840504102040403421810050703800a000c0c8a56246162a00c41c600307031020102c4180c0c40d031445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965376519 1250 965375269 965375353
    0x1502070f03030e24090c09090c0103090f080708070303060b030708041e02090a1b0f09030f170714012f0a02160b0405030705060c0c041a03100b040b0d020918 69
    0x4040a9042e603000c0316003c3d414200146070075925270540d03681d141816501c820790360510501c95618a50254801d12603070b03551186141c910b50135040804c084020909002002c030f140540c130000e030780c803a50581d501d8414035a1540c8a15a8201030f100c5402118429900e60f8005030b200c00311010300c240d00792035011500703203884c842c2203580d18800a03003582040b951050403c485075100e54003004994000c0c040c20401441c9080804074a035840c0b1900d02280c0c00040d51104000d07056002c4e08802e01484003c02c0306140b1744c440c0641038500300c200481e0020130507002d45407103a03050010303080b082d01520443d01034405030300d0800d05c000429000120f11040209080200d4a0b0801164001e4482615001e003010705000707007143c1e1895002079482c0b0980c0c44054220400e80e0000402045c00001800c460765049440d41ca03e00411601118900603428040346005504291108881d00c80c0d018102850f1039443c9404080d02e4005821000264040c50000c5944001ea0034419808844140802d490200310341c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965377769 1250 965376519 965376523
    0xa1d12030703031d03120f09013e0906090d2d050d020706051204210509040516050313141605100207052404050603131502070f03030e2409 61
    0x4215130015a80104040181800c1c2d54800740d07085000b040860119803503010300b86001d050160700c400c0000b4101117802c403c3d4001c000403040482c055200012142032aa044c4e8246403281008050308541c0402c40311682d402c000000701217540c0504840c0040c007109101141c2d001a4030010050b52102071441e05c3c09200c0180080d03490040d060005022040c41c010b006441401500d184600c8449294001000d218410341c0c203081e030b41403e1440f0143e51070722010203400741c1c0010349824011407a081c0000c41001d456849080c4206240e1240c504607540d04c030000030343c0c200f1030760700711303014051180c844541002c2046500240c032840c4001019040c20a07090110852211684404550041000b00003030b403901d0300c80c40007c080401c01140008006060a0304921442d03000940002002081100c205c41d00900030301464812035400c410702ca44800800d084e8001c0342006450000c0320341c8507500003030182d4486000d43c501081540d4440d06404462500d2a0901940d00e0403801d0348002c125000c402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965379019 1250 965377769 965377811
    0x1212160b0c1305010f0507020a0f150903050a17120103050d080c0910320a0e0a0f06050904090f1407090603031709160303050d110a1d1203070303 64
    0x1c1025981c100701001101504403101da10409040c0306030b034500395032494801c108440506070080c1c00958081da031040d01c0008440b05204100740b82542001c030000340b40c031407004e010880390854001c0940d034a90743c0728425007800302c1000c141e444408204001c0394800d6411028025801134001d010610304180d006058800c2c0140924040300d0100301e441c010f940d036041e840400000030303d000c1041d03180c03030070900c0700c20b4810180200400ba600d030031140c40107007004000c01510700745a0320060340005d0002800510074050045e1503c0100e41a014428148038001810042d800200041f416003410341300c0b0300303400c000c00d4010784401c0c00308105e18440000400c6030100400003a00d04108844c610348004040780300300c1c151107001001d20b00105040402c1002520305400302d0318074108a00e9503915000d07061354001c13400d4107601c604110540200d9540c1d101901c502100355210543c01c40c10700d0011200030f5055801d21035100c0c1c8044500c44845030204041c1c0f0500d4403036100081d0000c000c1000c030000502c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965380269 1250 965379019 965379031
    0x60c15060509040605040201260105030c01140f03040201050d112805071509050f0f0607021504060b1503011e0503010507050a0c050708030307030609050907080c1212160b 75
    0x82003480400031901c40d0b152455009800580000304c0b61203600c0101c2d4000e40920903940c007485514440c52048400f0107800f07040b501f0460884000c20100801916010000d0315a01c3c814034040c04007140241031000155401403051500300e05d040706030100e001c02c070359262179010b402c00b9021a0895140b000901ca030751081c0b510b48007240b90b40540b00002080ca10070000d00801c40718190284110070709058114220711580704040c1c420200b40364400030b82e1088110108607552040b031021a03036940c0007042041c40030313140c40d005246c16a0b582d01e50601030402c050405801101d032854511901e040000074501134595074079451072140c0d131002010744440803a001181f080c3d1404003800140f5030041c08035120410f19003064040c09040f8280b43e404d100103540200b080c5d0000200308007903d035050f440300f0140c945a03041000b02d40c49000200c1d80c1c0b24030f6030049024a501030b499074205450410000c403042002e03041102c19400032542c05403441e411101107525660b25100010040000021081341c2c014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965381519 1250 965380269 965380271
    0xf0309190b060409150606110616140c1c0f02010c0201111e13091d0c01090b0c010236010c0305031603060b270d020102032a07060c15 59
    0x8600c0780c03940305030000050030701442566030304105820881807440b12074812991402c200182c541d07461000d011050b040e10706c0000303401200c0000b490010038240510000042e681c3d41d5030803609801c0b03056604e030300c010340c0304400344141000381c11011091503400601100f03e68990005807030070a40642501e400f1072801003564100440144c0e403616003410341e00c40d000d01641d00e80c80d20319410800042803142c50815001c0c0c4108150200e40d03800da50b0490400f02050303940c401c04070400c82c5101904e512002c0c0c03080380000c042030410410b01c000d410162508034140800140780610a0301c03508003140d9000403204803c0548454104600341c0503a02d801d46200a0800059041c06950003c182d4400140340c1c01c10102842507200049200390300031780c044d02c0d02005481d980d411308480c4044081d50a10b615407688078000000c41c107030a024500e21125607040e0001c6040550004419500842c00302d81502141007504607a051400100300f0b600040002e61500e00c3e460a0900b0442e081c6400748400201075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965382769 1250 965381519 965381563
    0x26010e1c090806150402270901150806040c0e03010911030708120d0c020c0901090e0c040c1403040204090803070c03020609011107060f140a02090f0904020913080408030f0309 77
    0x19040030415a5000c42203203402d0142d8501030380040e0003401101980c407c90000303509200c0d1029480180004100c1007126110300e142e0340e41004180110015022800290998010a43c2424160800741d01c80c1845d04241040e0180e80b8082421240001401d849000c8a00081c903018281804110040c003a00303000b030a015070000d0014010340c415414844030095680c954001c50134070071302084d824040020140022940c0d52803c400260100c00c0f01c100c0c550141206401c21131030607128540703e4002c1e90311100c0c101c072003000d100036103900000d109a80040d203030040000000d105000440c4110160744600304419482e090081c40d18a00810100c030f907070324044005980398039050075208425442403010450042e050745100c0500fa100903400c1804400c0824440303804100c1c1c004d4400948156612510030008008208041e4015940030f0341291180c07000c100da017504515001d05160040b091946015170b90a20246950712240040d0442480801032240d090808d02803540d0101c4008803441c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965384019 1250 965382769 965382779
    0x9131107031710031b0914150901031e02030106180507081f0b0c030903010507030c23030a0213030f050c0f06091e1c080408151026010e1c09 62
    0x3d4114540000780c01c03a003408441440c504603a86a01002e8084801e043c4441c20700804d603001078010130f492541546040c9104107901e03080001c0b02c00d04a075040310b149426130103000f480d201c40c0c051400081c0d0b010b540b50600468841c00c8031641c00d4160030400c4e0001500d00c0c001ca1f00030407040d00030300704885100e05003072032892070310305000f8000c1528000c24142d41d90340e2003c02900d20314480c5125040c1c01d94204410001c07116050751242826607240d440d51449107600076810b00d114108040c603800a000140f001c41c801046075406000840c050b1581c40896a480c3e4a94208940085004445d56840880c0d0428142480c00030465012000c0d00c1050400080400141c8035681d00d14a131102044030b5840340b9102d9461a02181a801510388080514220b0b414a141c00c5c6d400b60183c0e200300d200300000302c911702064440151190305101c0031085242d051007251500e00c040ca01c194880008c018062040e0020207204407072240121000900160002c0c444031002506101c401000f406002481049 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965385269 1250 965384019 965384041
    0x110d020d0f09120c0e01061b0f06060e0a020d06090204261231030c1a0405060c0d0f18210605070f022a010302091311070317 55
    0x14000807814140c8812101031000c0360144541e0b40800107020ba0003450b8001e11010205102c20344a41c0c03540441c25130b0700d803007003906c0303e08940c1302e07d4034103441518086002c18240701582a446100d000081040b50351044545103840080c0c850718400b50b80015158411681d03031080c0c0000b020544001c0d4149440c000521708507911409290310210398013408480c00c0c59081c0f0032025031694122400792550605d41d03089440fa0102401c0661460429100c540c5645051560130f0450b03500010b04054607090090303125010980c9000a50710345014403010500b580e0b90806820401c007403000404541c0d0a1800042449010b56911010700403c42c40102801410707506040030b44101c140b80c1040a00313044a10100385600b0800909580c0c5400309029180e544058500980f00d4030340e00b100c1c61007007005495091712051080d80e0001d2802c0c05c5088030254040c1e00a46005071004100083c4040e45000034400c0c4c4000710003003501c0c10340003d00c10b0101500800c0c500502c80045203c2110b03484c001050070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965386519 1250 965385269 965385283
    0x50f0a06061e081e13031b0b1b0c0601060e090a060b03013c031a0112030f02031306030f1a06070b091e0703020906010309050c0411070819110d02 64
    0x20100311a4900180040d900b10014184481d400c44c078000b82c0d89800000c45120000141c003c030001001000200a40a1126454802070350040c0e010240340e01d07104041c2500d03002c004480d80c0b030700c40d050000c003c503e9003d2050900900190b124034810006030005c0251503d001070090a04620388141480802d1040003681d040d03845403406c250081132818031401e07002402d046480c1040892340c41034083c010040704420200d0340300c2c080c100d80c1107200d4198200145000d002d442c0c0001c0c803190300000800e00c0f900221042e60799034015a860130001c0c0c50502c203d440303250082408241c8601d45110580080d21a034000d02c42010403600403803900400260440c4501310340030300250900740c00b00f8030a110600070720a496000300c48694121340200041358850350f6500c4241e114141c184005003503035010340629106990301c4030141c41c001c111a0100170003004d00c2008181c40080922016000460b0070300200402101045061801000c1e101c00403d9404180006a495042020b684510300e0b000a200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965387769 1250 965386519 965386577
    0x6061f021209040e03070c090b010f0e04020d0b19060206060102010908041208040b0c0f060a0b09060103090c0807080c0918060f0714041403010509011a0d1401050f0a0606 75
    0x301e90b6401600c4001400b4101e03425005882d0b000004141c010001c2440c012003c80d03915000074001c0010348801525030788101d40c00340e40858003880b101c2c1400c1c60154003c19024919403030018036050001c01043c0c08580d03003544118411f001040902c1455010041940c0c0700c2c800b44000e010358081d564450415000364821410144003d0445004010042c4280c0340075102c3d0380795064513180d982c403880d80c1da50100185a030300e034060040800c45110041c0a14101d429018200d55029240c01e001140100021030050380c02200384540494072220900c1020010b059070360051400d0703101d0004000341450b014140750806c1c4003c4c410105014004200c00d5400003000da40440030b582c2c1c0c642d081c0c4240380001c6080c5500c500014011800b620303004030540f41d141c010340080016540d010718440c00c0740c4400e030f107ca150003d00c1286903480d01c0c0440030a048103204031003554041e03132080842825100191601c4868055200c00c20a185000e84903102c02091140750030f006410030602c084102c4c040344002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965389019 1250 965387769 965387803
    0x106050a0b1b1203040503040f09060f030803070c140a02031c0207180905030430021c0311060720061e0a0b100e010e0a1809050a0b040506061f02 64
    0x9a0b0360900402e00003d0a03d9062200050381e034a0945441c1d0703107a131320900030044180110000410512054410303002500d07491410804160304540703405003544c100408500421000411004c0002d20510344035041541e144010504101c4610415042400c0c201701c60403040111444000003d0b40001c1c0c04084446e2800c00044110b0343c05e074490301415100e40042c0192000290000340d04251000c6182c440005042224010020703071940c0114018060019500810030b4115284a40340051040752441c031034144901906d82c100c0c151410000119400c501040c6248500c0f40050459203151490101d1000940100e2801720300355010b600035410603a03540903180000480d644507507072001c0c1081c000100314500c101103040b4020701009001e4030f0f0700e002075084d82d66210b80c0e04200c01c8031000d5400e99100d035013295062200c0f0754002c0800e688265600d102e42c1c04c007400030031440c2980c035024600500141c001850f1110078048202e03003a0701c10740790801c91b003030340c0310056540801c88110217240001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965390269 1250 965389019 965389057
    0x1020a0f080a09030f1a07020a03091a130906030b010b031303031a061903240308181017060a0806070806120d09090b01080402010804031809060801020c0106050a0b 72
    0x9800c807a41030a44e040144030701c95461030354041c82a0400c20145101500c00c03100c10942d04d0400880e214122608002c020401d100018410700062295042d5481200e442413810018140d803044503403003585e0701240b0701c3c541d19102030040c00741e500f036801d0141006008051071414950b5240b01080d00003d000b5040664032011007441c003100c0400540c98039001484241c85240981d1120040c18004040c807001c41d03c1d10030300c3d40e00080950354101c1c00d1000101d034640c400c2c3c550f407120801a8043c0c0c2041c828a03c4036801004682e813003171841da070b48440c10f41c0c8841801400607810020301c0405024140716040b1108100492840060980d611510615003412691524404141200c403a00c1c021035a902880000f40c52107a40b028805040b103041d2301c1c061103054000d00064502800946020380000e141d0400140841c0c020702c4481300310341d002c030380c13010b080c5607100c10389411031b015900007054907500083c050074244001d004540290408641c010074452808040450b036102c0c0b54011070441a01d08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965391519 1250 965390269 965390287
    0x240f060504050105181b0a0e01110d140903070801110a0909150303050705010e030331120804030e0d080d0f060b0306040903020a05190506010803120a1a0307090e01060501020a0f08 79
    0x905100505006c2c1a030303c7e5008000080c04c01500501d00c030b800106540c5030f070100c10b0800078528401d007216482d0101c0006881445a00310360040c107850f03425210f00e05000541510900c142001c203180c0c242e00e1900d035440154000c12500300b41c0c0c000326502d0708003020791240001508071641140c0d41401c25903070310034880c6803090260501c1010000300d400040104140e00f0320080301040e01c822080d188946002040291200084219901a0405200002d2641158090302c005600300b0300a003046a402c0c3c105400151590000d0701084036200c0300442c01d108c0e48002e81c0140d03100b2400702c00c03007404040c0c02c0100d45001400010442c911641e210120351342407600030712a10701220b82180c282c1d04601e035110201c000c403c0e170820040315184101400010b02c0d43e004400d4030020aa044081401900d65540355006085a000480a03652084101c250240e5003000340f07a00902100d08049400b24140f2007150864409a11141c1950468204000055880c8000c140c850380c0c4500a03079240c05c949 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965392769 1250 965391519 965391541
    0x70c0603051302090f0714120115020703050322080a05061b07050102030405011a0603150105070c090e01050613061d0901090512270f0904240f06050405010518 70
    0x302d500a03401800c0103042c0114403400740c3c0030a00c1140d2a4444405900c010351b01040e044c480c140c05090008294001030210030b10420b03140003909003610488400c1901e0361145401c0d0751120a5020b800380400000b238248404014003d00201180b202400011800b0744801e80c031164024500083e003c006c01034440d0a20911042c0e6858070b4104008546a103060314180d07000380600910440c02200450445c00c852910f442160b103e000b15400045040c02414010340d85500000d03c125070344001c60001041c2103a842c40f0344080849844004a0642882414802c03008040350045542d0750401c1c5040c850601da0101010307009100d4156820b1076650551691300401c0b5110004150740540603100c0907a00c82700020300b561000e00004001c0c0035812400c00111901d4044010350001c80721081280c1926003000c40b03e038003074000e06601744122416020410364100412210400c00e5842010b0302e83e020491003240003805081d0b41c100840d5041c980000c002c5496109819250920b07030700021b08820030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965394019 1250 965392769 965392801
    0xb03040b09031c0e01061707030623040f12020115050114040f030515010b091503310c08010621083703050103120e010215010b120c070c060305 63
    0x3e0f0038503461851a0340920760000c0d0070900458a0b540d03081040104030180c011005022650070200180a01c500e1079440340090a0a410300c1303840440070000800e442000b4081581c0308500c9000301e1a0511060310305450340007040c02890045a03d0031008061454616010906480003424040004803014031500c0c40b62069070010201c150f624003001040040000701000409400001000b05070780310924011140504031042d03501c9690205c2070030b1087c04100c000c1d0380041c00401e001a500303409485c40410f0740308004a410706141e48081c1c540a00ca000151a4064601c0400a01c6620f00d40300398038003181188071a4860540306a40e4010801505904480c1801294072401c0d2640795440400009031000443c090002d15412802001062103841264180e9511400201c0302c1180080d0031200348004030403036419442480300591070a004003400343d0003802603100141d81c41459000b2240402d0380a400003100c003000748068400103000c509850305032101d0b46000511035403a2800c01c1d01c1c260f4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965395269 1250 965394019 965394037
    0x60a0b130207080901020f0a08030109021b0601030311101a10200304090f0507121d01110703030c0903030504270507030f060614030f0406060312030209190b03040b0903 74
    0x710008190742003060705005818802026000e4522141c91000d0554030b81c880120000d01151040006010b07172545503003c1c0900c1d9440012081c640000920000e20b400703002c2c0c0081e0302050551513020301c3c1510030410f01c0303541d8691206c01d02c07149940c0e02d180e210402c04000103501c01c16059502e000e540e0300c0380c0007001c40b00250068104c000307401078802c80c0e12a0320900a102c021402c1501002140711580515400390200d55200140100247d03040340040010344418503801c456418401105074090242c2c4076920411040955280c403e031038082c04460050030040c00340038904c4030800c00b1a07004010398040319080000c03020613501c9802c01d400f1a8030554030203000540340109208180354198000246803840940c100619500c515064880702e40a00b0034100718101000050b0000140d5064603410510840011460741d8981e139a00400020740d180d0140025408120a20700d46401100010160714400b0344034401c5080103540151032200800142042c800c817030208902d40703010421254401c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965396519 1250 965395269 965395271
    0x121e0336050706080f0714030703150b0c371209120308100e010f03080f070b010e1905070e04050622060812040503070e040302010b18070201050a0e060a0b13 69
    0x141c44103005480304d1019100303480500060b00c0002d0000e80a044da20000d11880305040d415640c5450f1308034040c100303156007021030b100c4000340001c020540c103018000010341d940241095a52050803079000d800e001d60450f610f00898100c10341c0300e0a904003d04c08032034000c5005405000c80700303c25109000140c7c400c0f130074140c03140751110515501000c42400b030006041721f040e03800e076208082c00303149500f03020366844030107282010400620104024548071440344155402d00440391a12101311400741d000081d0441c1581c10051941c0c0665048201c86018060800440c01e00010041071094054107083c001c03552040401da04d40d65030748034140d80a0b228005000d00f020380c00100e401920031441031a20302d102e211182201c040c440b02c1038405440e4040c0080201c11300c3e040350020380d501d01801c00e80965684c0d038841d084035110010386030800c0510340300d040c80380c5c200068000d003150b10003400301d03070500d00d0400d254441c3c141c0416401e07004842402c0c0440c000510780009002c0d8609152a02c0c103007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965397769 1250 965396519 965396533
    0x161103040906030312060e07110a0506010e090708030c1203090c0a090c020d0206060d24150509060d03080414011d060105030106120c03031407121e033605 68
    0x206000b9044401500e10983d14851140c48402a2405480c902d000b030900c400301020002e105070f841003440109580c2104112814034040e07071a0070341006020b070440300c60184140d0400c800e40500b000354000408142c0001c615001c04288050f444a41403030618921a00c00800720740c04103010056440300c020024080407889a86010f03040042141c0016000035020306058101e00780d00204000744030b07172000b400d0003000d4603c0d5070350141d6031541c079014840c0301404075840c85028051032107440300d00d05880000c1c84407107050a0401050005c010600c43c0308642c1910210006a441028280c00a030b00c80807401702c81a0222019014146901c40840c20025404c2c1081c0540300000301c990484d201980200003454560701744074083d0009000241c014041700c402040001e12909d01e1004030207802c0c60441c2405c42c2e41c0d03120100c8a0000381c403940021903d02c08200c0160340403210540d40e982c0c9003001c000007074144a20303400701800311451560006450858082159440040c140125801703020303946c0d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965399019 1250 965397769 965397779
    0x1009080105070804140a030e0f010c0506070e190506090409031211030114060c120d140108060a0501060306211a13030e03010b0612060a0806090714030106030b16110304 74
    0x3c1c003d000c0b1425140da0704000740d142070516010800c560510b805070345c4e17461880c1d09141030100d884464210325040102d0a000341d404a1802d0041a020303110f84d59075031101700c03603004c1000700203030050240b00d142c0c030b007102007c000340c1d95100c00703c50818800f42c0c2c0120761003c19040940d007007a80d5400180d02d00d07050004405070180f04500035816151920082c81202e0120028814a030003100702c580c91540c8400607041003410031030302500e4410500700010030b07070141100355041c1058080e800f100b49c5a201030203115101803980107050141000b031a04200c2c46103429083c00c803041c03225042c0540f0b0746010b1011018000007582800755101c0c601102111800d01c414801c4001d54008010703000100d9031540715035185018080c6560f0018007d19407400d01800c01e0904000c000003074041e0754005241c0c540007a22201c1403029503c68031a030f5002d1b140c41c40ca4801c012442031090850b05200341d140107820701c00a5104d028440c0c000c0340345c0000b0084441484815075100c911300e41c050010384408240024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965400269 1250 965399019 965399027
    0x30e010c02160812040303200d1e030b0609040f06090903020f0f03070803060411190e0109120c03032a06060311040504350309070611030f0306100908010507 69
    0x14002c4010b600c200b10350b641d00c00c04162a10600103008400d07420401c000c0002c240300c1c181d5000c1880381c0c8954145094101114540f0340304090910310003240950b090414001c540185402880b103583c102030002c40922000103d2511601d0440303840303295601c0a41e400c06210b039200c140900800401000704100600340a9643d090850410103e4480c0600e041c980700c0307001c000d6441d1298410700c107d095031a0441008003030240061403420800d4240404c0d2011441c0c1000350b001c0140a4842c0012010100001400301d01c868000700011905041e000d000901903824035001c80c0d81610f4410290f00e5801100c1c0c030011031342d400041090f20390f1200d490074050309602c00000c880c89200500004540e00080c00b0545101300e9000d048105844642001d0320303071100d6041035410141210600010345210500d540b9042522030280d03c0c0c1c0140c0084c42502c1d080044040c40e42c811100460905180d240c100e095488014552400b80d4858640051018000c020b900e01404550000380560325003020010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965401519 1250 965400269 965400283
    0x1090e07120c030605010b0c0d050a0e0316090605010908250b0c070f15020322180609050601080c190e0d110906010906090317090909031e0a0915030e010c02 69
    0x5204d4510300b000001c0e0b031096000c00c883c0280307000809840383d600a0302c0c3c20b0302d141d00070301040000e1043d981c05c00d13411035406205011072a01c0440b0000901410300d21302c04100c0e0103d41100f41800207500041c00343c08000a01c14030000c40481010400c86031559100704c1c0c070f41c506d51080280000c0803503004c1202a0204004040c0c9020300450301640760f4a00c0c07501482c010f09034040d000341c2c00030040898144102c0f19891134840606420b50400d5a8845015000a0801e41c0c02000f03290703920000e06c408001c0d4003030990010001d2038130b9100b905080489222620500540c3c90701c060681262100180c090060740500c2031f402418200e400c100d50030309507111010303468594800c90f410700000d10b2960090035001c00799061a030b100b081d11421551040750100c8688111544a0340520203440c19548806105129540280203103459101d41683c461540c0078020035030720420f1003417003116181503004050f002212101c19031030512000071281600104040305064265500744042007121580004909c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965402769 1250 965401519 965401523
    0x8030403020f010c0309020a23060c0102070506060a051503190903050316020a0b270102040303020f06100506070809060c07090c11071809080d0203070305100506030f01090e07120c03 80
    0x13445503519282d030850032503002070390095010315226801e20901d82c00b400c201221040c40340b581c00c02d082010b4000354694200300e1a9080c80e0390001804000c004050014582082050b1000d00d18142040d0000d14030b08200c8030301d0a024000840011080c00070030600444110a14804012200c11800c00400541c0b0842d9507403100310000500d80c510b648001142c905484e0040f00f442200e4803009a40000f030300c070254460440c6408142e8561344003a007840144011882a0000e0a01c1411051050b05195000709a10034049610404002c00d03143c00c0c08880c4481da010103980d81c0e5142c0900059128060300341055601d1240800c04a18001e00d503002c102c08440c0703074403948a0803507146000c40c0c0d00c410b00c0c0120f00c00134190b05a0340c0001c4c0495080200843e20415004d800c3c4a4240d951500300e0304120b44410000303488405101480c13260343d9071000074002c00e64040b4914a0403180340890124184141664256203910386c42401c2c01c140141c0c0050302c072401906030f03108042d00b0503900b007003c1ca00003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965404019 1250 965402769 965402771
    0x615250f17090a0e06010f080603070308040b030f07081b1621080c0c07090b03191a011a07110126060f0d12230408030d0f050c16020d08030403020f01 66
    0x1010854100044d216071107104142d480c2a00d010720742a080703591801c00381c003103600b41c440d0031404400036000e20040c1016040406a181c3c69142c07400d011804900e028000390309200b0a0410b204842140b00c0b280f1100082581e1481d40d60610f1484d000399403a00c40344041d000081010407440c0c854080c03c80742c85446200e607151a201c0d16000d070030700000e10a0b51510301c00759000c041c0400c40361000c1d4222a00100e40101074a8465008500d0102542024842100c100e140b0b55071070700d040c000c081200350151650b807101e02050062041e28514501c80e26038090b000e10281898400e1302d038494044d02d42d221800316206440020120900a81028191410f5200b003101c440d8422440c1011940001400c1d0400c00b20071515100e098107460b40d0f0545034004074000178030b581032008400c37070308028030003010700f20000e60307841d03150341c03e01011511201c0c8644a2103080c0810700c5130500e200030540d40c1c4d4450340d4000404100c4c1d503200040c60818031900080c0110310100410082c1500883d070f52402c1c1c050000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965405269 1250 965404019 965404039
    0x60e10020c15090d17040507170607030e03070b04081803031b1203250212030f0403020c01080907090b030a0c030f140c0d0b19060e0615250f1709 64
    0x444a41301c0c24031503191320002d0107024018103040321100f1000d8015003d042030354012911385203030110340e40074030f21140000c1d0710280504c00b042d5454845d07040c20300c818001641c1000210359410402c0500900b001d8131800300400c2254544407103d0064507140402800c503556856600c00d00358040000f014451b8032401182d0105401642c4c00086a214201800c1c07a03250010b0700900c00c6100329000c1c03d0807421481890714032a00124180d008600800341400040d04600d020301c1d000303241401501a4070b0401280e03d0501819050000d0070000b6500c620501150200380c107030120f0f01d41064814040c0009441ca0400028046d80203800c0d14198014244021540c100b01e04607952042840189030301314030b9403401d031004a4032544010360004941500ca1070f0341d41ca80c0201c0c0083d60340356040003c1d40098141404820720b00340314104c40401415811900b80300320071000b542030110344c0308001c00100f49030700014100007804580c4441c440d445041000d801c60307000e0442c1c0450300006200f0340540d445c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965406519 1250 965405269 965405281
    0x15041b05060c030909040804030c140a120b2a03040605070908070f0b070204020f0c0f011a031513080c0a020a0b030c07021e150d0c03050c0403060e10020c15 69
    0x740c2107440d0303000240011803801106905000090400800035112050705000120000782c0c18680d61000b4081c4c48648200c200030042007021207074641e070004402c3c40300380c401c410001d4106101070390708c9200803c0c0d441c9095583c1441075020f1062500c1007900d008004200f00810a040e0f106c0c80c050081c0c0d581d002c0301141c42d82c0c100341d69031609004101001c40b2266041050403e03180080c80720b1807020b0800b504005012710042801d40000201c5102c1da0000c40c140c0c18600b0092060540f00003441c01081c2444a0f40030200340c0b42e140426042000c0c41c100b800050900707100e0340d507500c0701940c405c01d0030340e0324440d840025440340c10902040748103070b140c2c020020f1130b821360070180c070301070101c803d210b13850402e60341c0c20445401904601100501d1f124400420306548895003100c114281c1854242d8a030880c0c0140d40884851302d410b107041c0f51070202807140f43e0901d9419982500e0340280c0000c0d10341c50f41400203284c18032500c020449503000140ca10219000072600030084800e111180b0440d803181 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965407769 1250 965406519 965406529
    0xf0f03071b08120c031b010e0c0a15030207060b10090f0b0703050313030909050106030f0e06010803160804050a060c201e040906050a06030210030b01020a0b070215041b05 75
    0x207442101a5a0b00c050440038001c03000900134810b894091040343d18044050b106006000740b4920324018503550349064006105003030000100402d030482c1c05601c19030400018030741c0a610400117500701a80440c8407410040958004042e035040181720322864004008018200d4505004038401c40c0700200001807040508400d85500300ea06440c0e00303045a8034020002c181d040032090540070000c10548c00901c9002d140b140c0d03800392080e640d0202d6210480e03410042078030002e030f510b2001a0322403801002402c00200a89155210310107000388402c0150400c031245006035000f040c3d1001003030100081c00b54000c079104000c540300c2c0c501001c10805581c0001c100030000702c000d030b03000040c803120450024056500210522801040000c44c0300c155124402181c0085130800e15181d070350241442907280042003038884000c00d15007440700100e1840000c0d1658202a4000d140040074004100c0c018001e1008048414030110041c8c0285014109030301c81c01c440d43c00c20800c0c4850818003040600f80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965409019 1250 965407769 965407823
    0x20c092503050c180d020a0e090c06090d060c0909020a0c02010e01081b2d07050c19060c0602041508040c0911030f09010b03030f0903121c0b030f0f0307 67
    0xf000d009051220000c1c0b0440302e0903803502001d83c0f0104842c4c0f0000145d0700c0d0051000600400400c0b401c40b40b03803581a803868494a40c038800d110302c074140401040c90b600d00b170540104030741c461404200c1e404a8102940c03030300b820b40c0089407514000311b240c1041c550b0015424101c1ca000f40d1b102c51641c42c070b01d80155404034041c0ca00325100d0b0001c3c003180c050703100b0100c001c0c0001d102210414040880241d030107003a00391202103246020000103603001c00c0c42420810342d0300f821001c031009000c00003103042000d400e217100e106150901508580d03803000c2c080039a0544004004c801000310000c400c0610043c11003500b1181190280355140000c11001110310a50755030500c101000762071901e03120003001100d00010410130711507403a0300a000c601c1d2021310160405041c986a003980310340c0c82104040c103000480c20750840c0340c0c1c070620200e210888119040c4140301e0a28800003442c0e607000b0042401c241006404090304d100e8a020041c0c4902c0010003809a9405002c1140e0800100c900007901010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965410269 1250 965409019 965409031
    0x1206040504110111031c05010f0e1006080c04030c060e011d011b0f051c030608011a13060b041e09020f190306082e06150f020c09250305 60
    0xc229941c0b035072154018204203407181068400c680c140024000f40801d1400401340300031000b6140c2004008081d00c80710b01c2806842900e08412186c81c101d80b000c0065202c0d071249104105140740407500081c40c2e40308076405503801045e001750b0140c4a0b1700180260500b4400c05000499440049003842c194801030101284141d4840c48496501018200d04007c007203425100c01034000f01d0300001902c108100000c0401c4c950540701c208000314800381c00c4810f03540c4600c6140e41410720b6030b6080034640c1c81100300c098040ba100100301c0d040482c40350082c20550842d69000500140c08030ba5100c01c400700c00c8643d64626001d01400361101694070580c02001c40018210f042800071001d0011500c581801c1c05203e841c0000309103035220b03003162400358038001c041042048240302e42100b2010300201129030031502418000c40745000c0c204c04062406841d8142045648004503046070310031f2040240c103900003800c40c5050305142d4064409805d01510315100101c2100715803104500078001c0703d100745 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965411519 1250 965410269 965410283
    0xf12050306030f010b1f0302120a05011d01030507030b2a09030c030c0a0605071e0308070305060102061324090c090c090315050a09230105090c03060114041806021206040504 76
    0x15243c000100d4883d503c4280e083c07d054083c000d007070354402d5007002988104c004030310100301949403441c4c82c000d100c0f82000c0c0d0b0034040e102d0401413002c12000602c000031603601040920240d592580154420913042d080303e02c070741c95107411000f84090250051b00002d102107050f2040f04180e002016503903000001c02540201c050407003000700600a030085e080090140811042210381c0c030518181c1e01c40100421004100101c00307200c0247c0d894810698450030030700090120b400c0c45101c02200440021000b40107040f03141c0e0030180c0300218550720301003601c60714051000c42168075100a05203024003031207020600d041d661002041c1b1480080085981040d21590b802403e04d1108000d800000c01440e1510345640405000904040c05440c00328401c0001041d00300c1342c991b040382550f40285c094076065000080b04545540c1c00312300c8074116040003000c18071040c9003402150180401c441c01c15510b1000a4200080c86440c0d0010f14654100c070117a0081a5212401c0100710ba00036100600341d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965412769 1250 965411519 965411539
    0x71818200402210c04050307090507170106050730080f15010507060b011403040b1602030c0309091008032701030c091503112a0a050a0f0f12050306030f010b 69
    0x60050480c0144c0c02444801d003103440d054884011a10340000d5501c070785162a034450401c00d035280c2c80208003064454130106401c6035450218003c00350701650b00c0107000c82c0c04907108500304a482c070041040c00300417a124455448001c00010780301650031100c0c0400d00c903c540c0060003e9040102e00d00102c03805031540c6007007041a442e41c50052800d9080107050001900c1d55443c94031220028601c243d01c180c80c81e401e03c1c98011240221807101458a20655000703015410170044044140c5039401000c1c0c901c001503030360f241d4030792400b034006034031280c5240800100c0c1291403c2c80e0640c50311055056541d05c0d0424001401101225460261380002456401c014003065184058800e415011850042008200300c0d15a840039030000610203210548aa8581c1001552040807088400f481000d4401104291a000e46406800d0801010702d20b41e0b142c603c1c1042181c07260b0b0800d041e000407107018522029079000d881940306407000c0f8440d00c20a08150f091000502507120080b80103070041300a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965414019 1250 965412769 965412817
    0x140a090e0903040902030a020a201e03090a060206101a0405041d1605040c02030313020d0201020a060515090906070c06020901030f0e010b04061205071818200402 71
    0x899406081d10125010402c80091181c0850000d14018503100300b0041e5142c15202002d8100545448000428044105a115184070100c1c070300f01e851000c0b40501007901905850340f03003035125050400390f0000c805000402d86550018505101d000e030080d1000b0310580300c3d0214504c0150118004011031400c11041c003c3c0d007003a800c98841c1d00d903012644d012031084018002d0501410b01e41d0011005d543c140108118541030040c01a844a00e001652650038111072903441544140ca000e4044da41000d90b09046920800900030241d030018010030a60600791004c8141041d42d80d180c0d4441c9284001280007070710b000c04c080f4010201a1281e0350003034038a40d241d401a400682846061555800ca84104210340380542c60140210000020300c01062100300400c5541c1034100444114100681c80e000078000100002503a10142501500a4000700780310054842a05000111030005030f140041241030410a1011509144524107686c2050144412401000030340000b41c4c6c01c0f4610000c0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965415269 1250 965414019 965414039
    0x315040305070c1d04210c02100e03060c070507050f01020a26040906030c1401120f09020a03151119180909120e0301020403030f030f14090d140a09 65
    0x9040c442d0001c4400300741c0d900e204041c0304141c40021200c2400500c10003041011000e41c0c0d01c02007130b0307120304030f40c5140401c071b0000c2010f14403920082c019000f01e010007503c5401400c090091400080880b000351074225441394880c2c00100040f9490321030300201042d68904880d1407400402e043c2e008003002102503c846003420101403203981e00012012681114071103040040001d031818903401304030b940c91441d2040c1e256046a004d036020141549805806030303805503500ba0451100030011980f441c000d4558001072083e650001e602c1080b1002c0007080143d03503018080e141e6034136401006103101020354400c0074803609555101044581600000d8140195a441d000304090103454000b20349030803582080700c00340340040e50f032641010002e1900a5012280c500315200030b900039400d044c51650041c0c44441c0c02c004c010700303164840b80c2c00c082d19401ca038441184034607c0d104150f41800c000704040d8683d8131249d220000540b24a5035040003d000d0000c4486802007a6074202c29141b034614035076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965416519 1250 965415269 965415277
    0x150f17060114011d09130506130f0201050c070902161202070e06060c0c060d1b05041d0a092f091e19090606052107090c050418060303030b0315040305 66
    0x1010084c4075402c0310036203441040d540300f484054610507280b601418040d26201c0d004166101035101c42d200c0500140540c902c46808640c203081c02c9031240c010351007a504203400754204080580c40032840c10b02c0c1510b10711010070711034041c00c15940d405540d00c404a03120301c083e0154281941d1020046440d60424030010511032203440c007500c41001d413000000e01c039503020008000c0201c0e1141c402c000110307551a6002903042403420b02c0780c0b415103081c507040b0000f5110030314100c003140048001601c40b5a140c0045520a0f84032401c3c504245040c0382290308461070003000040d91425100841c10740c100b41490074082c0510b004500c944402ea02c0000002c248010304400300028011514507422203a4002d401285114100c0801c106050005000c1c03e01c00d19010108946c41c81750310001c94040101d58003040c0d525200000c0303000444040c05642c14429507200c0c14410104000a1800000076030001040c1e034071940c1c092081514030401c042d582c40b41d5040c0d2008541d54440800c000a0241c030042c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965417769 1250 965416519 965416547
    0xb030604023105220f0618140a0506130f08070f02090f040203100908030f0916090203011a131401091802070605060a0f05060d150f1706011401 63
    0x41090310003402c008403400c001d1511100020785460910030501024061084a03542c00c030341040482070161190031015884007005040103584403110715a01e504500100009500000c01c0302d2111030f900d805a5403454a007030103841c4c4e805040f002c9041c0025144000c00501e8102c00d11071044155074a0b0182c3c15400702204a542c0107442c0440e10045e160385910b10b01c60010030740d8004140c54030340149410304c1c2d1a003001080321450200382d08005480c83e400c2da5003001400495000301d68441582ca8a82841034000501da59401c18000a0001c403540086050300e2010103901a1011003100f02c0410703000303181e03030700d0840c556024040c040c005d440b0300e1444940c0c1c1c0516060b15880c0d61006106541c40240c80c0c00d88800d0b40003e02035050082c46c0c000d90b03070001016100e6803c0300786004200c0c001c00319140500c81c82490006088444540d00e6006402040e43d054840e0305038958a072014900b10300c0c140b02e110800204006481b0003140081105030488400b0560329040071829001140c0150749200d41d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965419019 1250 965417769 965417809
    0x90306010e0624130303110606010c08071b0509150a12020a031704090603112e050a020a0b0708190507050a0e0d0f030504060e27180109031709010b03060402 69
    0x1d103031380b840d40300c0e6000740194003030b80342c0c2c003550419043d0603810464010074082c140004004240d0001d054201101c68460b008098048500401c1007049000241035120550110002d400e110031114001d182ca040104d0840304413218035601c0811418085030024007940c0b120640a0400114000040c444115120382c0315251800c0d0300c0d0601d44046408a401c140c0c1c00b94100e00b206041410a0b40c0c0c4c6460301c0301e410b000a16202c03071050724442030703904c1d040001707007008008550076070194000c20100b2101540300c00b00f40c0d120f00e040e0350004c1000d03004564841000c0e248510040080080303200d00c134019100d42d41c5031807070103a540c0c1040c0d41c3d4081c0f0940d01900240c1079000403002c00e4066000359042c92003580c44680e65860704c040140141c20903401d0314400e02c002d03414a001c00306002680501c0c034101e0301c105141c59444030310800b1400c0308881104025405e04800d04c0c20154851980c51842c65641c009018544074034202500302e4503441c0405070143e101d20b0108016203006899800b0b0541c40d43d40f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965420269 1250 965419019 965419027
    0x18040209130b012402030c0c01120f05091501050d050606040933060506180d020d12050d05150d030c022704050706080408040603090812010b090306010e0624 69
    0x620b03642c101201364081ea030703240440300000416001c83c00320303210302080b01c1c03000351708155505004940703403903800e402c640c144074620029140054423904004d1030904080c80810aa1400c5207100e41ca50034400120034655110400100c0c1514001e41608100c54124000303003504d554001c1484010242c003401620210300000d492801c08001160503a8a080303041014202d40541100040035542242c004a1040b0814421301a00c010781d1200d0401d146800c0743c40d00420310160020442c026212940034194200701181c01c140207400c00001e21410900344002c000f65611050307100d090503900120300760f0001000300c060000c43d10991020850900091a02c00c003040182170b410b5020f0f01140c0c031082c0903000c80e010041400000e000c403134000d15040c100f2007003034502130f40e4405143c46180511010f06981d0b040301e40034041c5020646101c3d0003642d450502c6540c4891450380c09401c0041c64511070311606002080e07008080341d000b0700070f1001800c01c02c522400440c441e82103140000c1400c040a40c180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965421519 1250 965420269 965420273
    0xd0f092f03030d0902100f05071b150302070b0906191503060e0d020d0e100e031c0f020c030d050f160503030406022a031c02090301060e060127140f09010308181804020913 75
    0x1842000300bd21181c0c4005a8035601c5140ca1390100d100107100b88180d800400c00c100a000ba01c10b99824081c1c002c0500154406184503001d942d0300041c0c0010b0b001e2403600700c9440c000c03c400142d4280118454084801840e0040c00c1144d030222400203040d0000069040e09602c0c0d40620000f0078502402810348000720041465000341c3e0201c83d1840b0f00094444000203102601070004c000414801d03030280851440105001e4030904c0740031410b000810001070322000040e140303c00398041541c00405e8a0f5030b42460b0414101039000b080510103a40c4020050808294640c03444900d4400800091400d1071038071403400104500300811140d14035001c0007a00100e580a10819000d890a80100f404504208000610449842120b0099403107869101c84c01d00d850030712001c0455406507420745e12625030342c001c0780480c90211910381d00302c45068004000c200c128000f40442220710713000311a8402607401002441e100d503440340801296600c02090150402d49a01540050140200c0b40d81c0c40c2c8035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965422769 1250 965421519 965421539
    0xa02090c07201809030304030806010507240506040b130f0609060b03040308070801120803070504330903030c08160b0a020d0f092f03030d0902100f05071b 68
    0xa401411481e0314204141070440ca0b003d000440302c03620840080440340740003420075035a0710000d0406000c1c0402000000c10580c420350440c0c40131075211411400c0b0511a1045140e4030500b10148242c0e241001c00140c00c5080c14800d00c4c2c5052401820300c5000d880c680c840700001c1c210b240c4045481a2103104c00b25032421980035410082840c410441d40d00c1c6007504009020450240250f82000400b40040003803035000c07048a140c1c55040108560f80e07854140041c2c0d807602c08c90784107000a000403071341c8900e144030708104901440001821b0072001d0303031b41700001c031030341e0001d4040100410b040d103201c036001c100e805010b040480200105200c1341c1107540c480d144196000c841e40080641c0005034222800345034000c0c038103000442203062049081a03034a4010b5440b401440c0b11242c140c0c40115860040780860800034a2009410b0344c0c1c0d40c1040008400c060110080700380d0281481060000400e441458107400e61002662064140707200c550784e038000980d0b0141c00b10b90000110b8000700b091842 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965424019 1250 965422769 965422793
    0xf0f030b031e011503050601150302192001060f0b13090608060114030a210332010819080a090504020d09140a02300d050a021005090a02090c07 63
    0x3003600e01c82c010481100d000c3e095818000864900e8a0b18501c100006400042c01a06540720f80041080c3d6982512084000740580444103003510300040d2004030064001002440d803140c10700c1c0070308604002c43c1c6924241c4445102e40007a20060801c00c102c55a00e01c006840e043c00e084122004031952401d04100751f6940b0741020889400580041226202c1c5015100011000f035010385100020303a101c3c4080750004440d00070368208002041c8108034071a60041c008503180c00b09603280341c00003150703e51403a90402031010f240b0349010004583c01200140c404904241602006102c00c2555101c021070341140c451a014040d920303102298550b5140041d0400001c400360001d2250300c681000d541107104100011746640013402006c0140c0c4400d0000094000c0f1604032107880050761b00392039414111010701c001c0e00c0c0a0002d20b069900d5000300100004101d503400c440d0241ca640412000700d89089d10981c5207a40000f4184005003041380505506c44d0440e0359407410441c240d200d818100d14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965425269 1250 965424019 965424043
    0x20c010c020f0106080c090c0d0608030a0e0102190f08040314010f0c051c1508030415080f010e01060c140d11011107020a030f0c030f050705040c0f0f0f030b03 70
    0x51124440c0030215410403101c01d0141c0030000034400c10340b40c0143c560316a82124581405070388041d0009420001d0301048606404041c00100042e83d500d46609460360000304040700003e540c1030103a10300c0c4d031000801100c1d05045981c108510030240e90344812240e690748c41203c502c102400000701041d900400708031902e24040002c148078160b804980111800900500300f8042d0a00031036654844102464000c140b80f0000050a503a2403d03007540c10fa1010344c0208458032000402041c40d04800202c1d0329090b8030b50703c88107181c1d160b0503090424001c3c01d020b103102001d2a03c00400c4954801d02c116550103018683c440e586004403400141406038401d000c1021824401280141800c24494504104140001e00d41404281d03400100c2849480c4130180c2400000f03194941031000d0003c400000316030100940c0c2d4038428070715140c0e458507210701c070381072045280c5858072582d207000e220f143c21552260382e1040d10140801000b80e80d080383e143d205204041d44c806804240e0344003044424070001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965426519 1250 965425269 965425271
    0xe06070f0309060314060108150a0b09090a02030c191701080a140105150f040f022205030a0201050d091704081b03030438030c0301030204182003030d020c01 69
    0x152031030402a0140342c080d88008101807030a83c110b407140d20803148682d0040024642051151104298203000c40515002c0e03e80c01003031410005144610b600050034484001d945502403540d44240c42c40032030104030b444040c801020442021201c5400006102d039034500d0078030458507403c0250003000040242c0100b80c040d07001032440824446c12400d142d0700c2201d030000a01041c076161a001110070061101c184c029200904805440d5495030081701440d40301d00001c540341e03031649a90b80d40c00c0360b00310040c104120a2000c082054240070a14201094046e15203d21707012000c00c0d9200240410701d002d480b460708a01c0398a91201180c030091000300680c0f4000c01d81145602c0c41d00f0a580c0c4586440c0344a070b482003004001c03418101c56035014101c5d0201c803c040c1d541203715004c1e5030301c0e0722009484d44a10000304000354464400013841c1601d00a41301041a10801103030000c0030b40c404c02f400340040300300303070707807200042d50344101c0001c071804060150380c203141182e1505020ba030018441d6044030303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965427769 1250 965426519 965426543
    0x8070503100906032306040201090b0d09051203060a0608040b061512070806040c0305040512030702070e011d010b070321020405040908040306051e07180b1201061418090402010e0607 80
    0x1d407001c0383c01c3d04c001c0c22405c06020301c2d041a6002800105961007501410791010940f40f1041c1c003680c1c8000c882c3d07900041541d040d00800c084c42c104640c0304560b403510500c2c6080000c50f0087c840c0100038803882c5c0c007d600100b582c4030071080000f0074281004030818420b0811420040c069a0345000780982450f031640d003d2400d18008003c1030300c04d02d91548042500d45010440031400006003515819890006640e594031213040032424540300d0382020300c02d01103c400000d0f00100400e11102082164092510f040e600d988140d941071103560409800030f41a54450320380303503482092001c20007004030401442c1503076a0020409486003084250b61071040881e04106000043c020a035111110304007a07101c081e110a243d520460700941450b040040307404c19102c0c0c801265000b50041d002003035901e0313260f60184941d110015000d00401000030061000714407140c040b0415036401225200b010b1880d0449036044c0200d8441c01403060341041810b0340c0c0b00c031190300e0704002488000c0c0030300d00551340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965429019 1250 965427769 965427803
    0xc110618100f081f031721011a04060e151303030801080f0d0210090204060b0301030506160e03030a0e1504030503040311030d0c060b030c09102102010807050310090603 74
    0x3e03600008029607201d5540400003124400c4550b10341041d207601c20340b11811100c1c658090f07145409902540425540720f440c482000302d2035940664101c444403107413001c90000c2c82070b540c0850b004911911010910070b528189072807906003000342081880300b05842c10320382e15111120116219520a5000c10b0841005120b515002d1041c0d58200c2c10040c01440480c0036444025541c0140c0503041c0d03190b541d6000b280d811590389410110003440c420b88841e4803561603042c8070fa160b03502030b60380c004070342d0340d000d0043c845a0140002d00c000440050140d420004511400c0e00d50400d4046c04640c031137a0388030b00c006400c0c4040c01800240d80a60011512242145041141c0e50708448480b4400e50044a9514019034480002c01e0301c0c40d8400c10104e14038a41c800880c0c50b001e48550f0180c3d00c0309084041000c0c0c030810345544011100300400240c0e8260304203200d0f141d83c0350b038590041e000444440004015a00071401542c200380300b810001c190603541c0c3c0c1160125400390f0421140c85580c0044000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965430269 1250 965429019 965429027
    0x901120f0903020f0321091c030e0606010305010f06050f040b0408030715060e13061404110a0b030c0403120c0f0303020a3b0102010e0714100c110618100f 68
    0x181104c0460015031514480f200855040c03004000c521440740480f10014030001002d1040e0103020034190103208100c2480e03003001d006044005503c920314400c000000e480e543c1300340074060403107c0c0390142124180c144542203070241e11528103965806004c000020f000030030070000300001c0070014040d64a88000346842d403d503007420030201c41c0190800d28103210400e816046160000b45086501003107850340c2c074040700584101060501e0b0000003108120502c5090500c260b540e41c0120b48826a00d074440310318542d507010503191000908000d0106100045581150b80401c5116040900004080d5507a4400c1801c0166044001a80100d4500403160f00581c00016140c500c8003503e400a40c20010b0341081300340d280c4503c4407040a1040e040351a4000e50100080d03510340e1040d5280d1a440e025032450f250700640c8624001c0c0d0824550000280c4590b110303110555105607014042080315007006856008003292080d000526a240082d46e6244010a1114803181d1260b09800e110700402034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965431519 1250 965430269 965430283
    0x20d0b0a091a1f06020d031812120501060507050622080403050d140c211606051b070c06081902070b0709150f141e1c09020f01050901120f090302 64
    0x2483d80f075400c240038045950007042d1a05000355034074000070080c1200005000c0c48000d110702610700c2c0e0400d0050308140e07902c1240c0d6089030717800b81400d110503642c03200101c82600c02da18002d4a681c10041c04135040a034041445030426281560f5114502541e0b1034502869102c0d80c401ca8959000d540d0351080150801f5504404055042c0d401e4104111102d2083e00c480d080403501c1c00352460f078405191040b01c03030000c0e03401107000b2a8900d2030400103442c0050003480141d414001000d80a844004000c40e214100c51065070f01c40c203400c0074649050019514510043c08103540004602d144a034484080c0c809040e02d540141c0000b5081e0415003c00b0b05030710100d4029504510b03244d4140c2800e180c21500e80041c00040d40307403035064552901051800d500650018404400100e070b80003141450360009002c912002c1d80f8075031300040800300700400715402d4450003500403d52440004c0a5030040001e40750148060400d01d40a5042c44680012903201c88915940141e5407030401c0d052540c100541d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965432769 1250 965431519 965431561
    0x602030c010c091404200c010b1801050f09040309211a040503041509120b1b03090c060304051e010c020d0306030b01140d140a140a020d0b0a091a 64
    0x5080d20700c0c240030502004c0100d401c1c0440c003640d16144194040003840003101560710501d2801c5446042511100b4003801b40143d20324402c04801c42c5003481da0913860300c41c6040ba0700c020300311060f03c10035005012020304010800e4060140b10600000d504600d0000311002450060a001c0d18021034a0305c4201c00c51240b4100311510810020400000e000004490685504650503242200c12120842d0441c042c5c0d040501200510440380c030800c2105852203026603803007004201d280c0b599000001e0140421110444207520000303881105081100003983c025000e001a11404003000305240c0c545c5d022000e60038040c2e0341d58600700403450b80c10300c403045004204c0e02d818022140b80da210198503203010301410494502d451040a0540d42d1401c8c4400c0c5150300c400458808a050b0003000d0700c400e0080e1043c0c17040e58034140b0031079001c1800700d00c0300e01e51a4000d003440000d40281d2107501203504004c1c03581d02e2165aa464440201e88501c0d04120140180403800c00305140c415041c9440545004034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965434019 1250 965432769 965432777
    0x5120a02130209150c01020703020d020a030509012114040c0801141b0c0a14060709050303030720030c07080d23130906090b010201060b210408040f0602030c010c 71
    0x14500107940e1190310400e1031010300c00140e2a4034030400059030b10402291a80da40c02800900e968800c0c006402414590b03000c0c0c1c082d40d030400307206042661039940d00c400050000d0f0080203580500e41c0680080011240441340c21071151400c8443c0204440100814118061b41c0d00100710400c05840100b801404181000780840101c50514004220025002059000d620722007078070042002c81c00d0b00c1c1050840030441c1c00c000307550300303003040d11505001030f407a2140589000208524002c1031180304076031010b0000c51469403000000c5a000c03454402c80f15500202d070207502041c0004001034148002d201014044040c07a215141c3d1800c148403105209011074501e02c2001c21313807201811a410134526005607a541052200303111b0850030344c1c000380d814500d04140403034000301c90b521002c400c43c42a0004c0100a0321440200344501404110180c40306070200f00f00000b0070b0308001c86403c40d01c41c0416904003501c4641d5404403039501c0d008840140c0c8049004002c50501340141c207001740c802c2c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965435269 1250 965434019 965434033
    0x10501090b1e120408220506040b0a03060801020f0a12110a0507150903030b0306100f090b12070b25020f0405090a30140702120a0b010f0512 62
    0x1660140680c00e1480e8654080b03004809801c1540c5040701e0030340110000c0404145000c1c50540010341201c100c641c51440401c0300c01006c00050442a0103032400206000e0034103180c8201c8007000e9000340003090400d501c0340707000203020100b400038005a03850003041984504402a0040080d5044400540405e06001110004030004000c41d454400d452030410781d03440b66401d140c02c1c1d81c683c910030b480303031549002c0c0704000785941a03014444460040302640d410380c0320740a4034480c00031355000344003560107110320030001400c9940c44156400d40103071040c01000c2d16803407218140b0b07016500c421008440020407209600c05a08031a07446814214605030702026034010501c0c40b041d00d41c00f14029540d40313022584104041108101c02035001715055a865442510b1001703022489001c0049500c800076418556405928003400d04046903003030714101b81554080085142000084011600400002d04080f84400c0c103418080c0c801141c0000b02c0d00d203842d0070b01003041001c0820711070f10f800400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965436519 1250 965435269 965435279
    0x1101110418051e0a050709080a0203100e0a05060a0f0b10050301060f030612051506010c050a020d08070b13030210020307270b120907080c0102070b030a020409060b090901050109 78
    0xc030908044800c4210700107015620003030340284814043d02040072181c006402c2043d0500d581d00194031aa8203541c600415990300c1107080d642d214240d40095050f00150743e003185408842d400000c100f190401100e40d1150b050310b5086c14550155204078145480b4140a181ca01040c01601d501000c1540c002c131000042d0b01000f07140e0302041c060503003040124548505010b2080c2c00620150485040c1c80701940d0980c50420b94451050494900304069100010310940c002d4034030001164112000d08410700140e800c024160540038000c03a02c4950922259010494604407981f00d0b42c1307a4010503050800b9401e02900e400b10410300705a1030703070040040101441c0e0042e0050b625040d0234441c801c500d5151882501190100c0d004082041c4010802480d00801c45041d03034056555041a507148546900002da120342d10910302ea400759110803401c0010031300c510000d40e40200d82100c010b00b041d450b11074200a5070400d07809031071b0032480030415110030316105299a0042c0f0b8242401c01c070561403e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965437769 1250 965436519 965436539
    0xc030d0f03050a2d0b0a080a0204090512030f01182304050c0405190f05010305030715150b120f1015050f0403061409010e0307080a1e11011104 63
    0x3206030104040d1100c022446031545900502c981640c40c4c03c200c2d1801455812003140140005065042c8a0610fa032840550400c54948010755040c400900101c000540030701024100a180480c0c0c0c5104401d0b001a030f0001c0c60020318040c2d400760260841c29403419660144240c20348003091105868807008220480468000c0b04a6644e880007102c25592141040c1d41029020005940c0080c101010081c6880c2d9903000d40200311481c1004200300c040c1c102441c0101d48003400000c129600800604021843c9150289081c1d0f03d4032038041002c840b60000c1c5181185140d105510250000c0b980b105181030301c2030101c1e4413103c0d2200d10100d500d000d18034149201524402e00e011000305400358000c1920500841d483d0001000c0c00382da4540d0b584c13401100914003814480c0c40c425414003c90120541802204480b2084030029404c0c10501d44646085031f0103c8029014031603501220030207142d5508140c41248250f0b1034072079006d245804000e0a42d0900c0e000920201c200b04000d000c00200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965439019 1250 965437769 965437787
    0x509160c032a030806010f03140f061f0215150f0f01020a080c070501021e060601260a09030216061710050a08070f06090e24060c0703050c030d 63
    0x10325000030304001051004445089101503540d036441c8080742c0005040c3c002000c64007904082c0d0b10b80030a010703c0c65044040f10589a408525803080d600030560a0241c9040d03140c01844c000c0010340d860f50001e503e04186138401044d04056001610312021409040a415078052001143d00d501e00d03034114001000c0c101d922010078810103044c0416020350340300300201541c00f9401201d0070346c0d801c0ca001603165108110300c86c40d8018801c0d58003080d07415860414000080c0070740700c01004e032034a401c0300641e4610340b0303202e40d20074140c0d09820600c60350301809042c5001c0d042c90b800020b0255403c0c00d0003030900303901040c0b001c03142601480400880382c1c040103032841c5e0800b0320882c0c249a00d49141c1c2201c2c11000f98800356004544c280c0c082108100070030388800301e51503c0381c01c050143c0e4490050723517140110304c54070841c1144100065869141103901d185444540d001460039500310a0004001381c00c106c140440b507511040c2d090042010400a81910080450083c60b98040001004000c1c0207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965440269 1250 965439019 965439023
    0x9030c0409080c0118020f04021c020c010b1003090204050c09030d260702030c15070c080a111f0b0d0f0206070507050a030b040b0f10090b1c08040509160c 68
    0x2584065510500c0a4001520f02200400c0005d100792040400101c0c407825a070102684074422a0307220a05c0c40c580b81c42141c00e0300c080745010041400440c00074100940000328444a44d548035044070700c103552803080c58100c103001a18005804980c80c018002200c000078200c0200f00700c10400c1307007620b50340000c014050100c035240412038500d42417410049a4900d841c0a550741c2494801d05c442c0907000300103025407003c050101c8002c10911000b103c2c19034420340c0c0240206080344028404900118000c0c02d8042c000d0030607030181c187e84810b1a14200c05130503004404006014a011102d01c540220b10742c4c4a030803070b40c1100c3c2400c42d0f1038505140d190108001e10409001a4020401170240152002000000e03d29059281d590901e1041404102c40c11114045c0200000d0468000e06c01498019030300c0d030002c1d84079581445100802040070348040c40c3e1080700101c07480103542c020070070300040c076110b044955211494202400200880509403001084c000c54550010326800f03408502c1444e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965441519 1250 965440269 965440271
    0x150609090c030b0607030c1e0b13020d0b0f010504060e22020a0f090903090510020d081b07080405121f051302120c030607091215230103110609030c04 66
    0xc004800680c020014008a1500584085494404e150b000b0320361300c030294065945255155902d0348041c02301164500300502c4101000c021035101e002140c504c1e02500d20180403030000314607644440c181710300111161440e11038440300501190901c1d00425000b00101c51a01c1c02e1070030903400c0f0b10200403540c00003110440246450406560b507802202000b403008502c5414102e841d0501032001c0c01000c40250007140d6000000500c90501354030070010141e442d130142c2000140c2450841c0e04100190061b00004000070340d8000e6004d4600060038158072448203d5640c614241c00e001e6003001800d41d81059400840c01c040e143c1022070039007021241200790000b019580c51008030103402c00480301a4105022280d0b080c0c0212000a0500a0000440445a00b640e4000084910700d01d00d0250b014056040a0000001040b03a00560000603401d031003c1500700004001584642c42c01d074480114820303800c010000e00c004140310000203c400c0d0b618903c1c002203031011a41c1e0381100e141260141d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965442769 1250 965441519 965441531
    0x70b070c03080304060506011d031506040e011404120e090c090301021312051209150d0912180602190b09011104120308061c0215090d03050d15060909 66
    0xa9031050000107168040885501c1c1d08041c24000d005000490f101800b01e00a803440154662503010b0002c041c030f800400900a0140400ba800603441003d020203410549414500d11004000e005005009410000006c040e1400381030400c0c4400e0361810302801d01c10316003400072283d2591070145d50b020301021045e6940c0c1d1840d07000b090082c0306402c84070204a2281c6008148111840f507101282ca0060b001ca4490310148000340c03500740b06200301d982d40300740003c0c500b42003501c03a5005410882071900c0001803800803911520f4450924800400010b82d00c10310a0201c0420f03030703076007078040e19451009001c10340d26131a440582140c2140050001c0c0a8000041c0c40a034094001c68030b400c0403400060780703403a5290400c2c2040030441c501103001c24000d2001803050700340b80f500780f81e2042410100c806030050311b03024070208801d580c2c86580c089008021102654540f20340d14210700c0d10a503105940d40c035140351f44004032007202c00030407481c48d9820070030040d4075444540041500c05441c800100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965444019 1250 965442769 965442773
    0x60307140a090810061d0709181404080c0f0109030203071709031209040e0327031011040f140a0608100302180604060506030906070309031713150e070b07 68
    0x240e20740d5a100c90703140c0c40340300c12481000d00c02e504540103c0300c240d0321107906c1818a0654001d986011502c1c4000106850010030940041040c4102800c02c0000c0c00107006221000704014032001311402d961801c0e0029880e0441801040040220000c00f8000c00c001c427183e40e4025220321545001030050314003d0081e9a446400004a500840004045413202d82d106d41000e840c40e0015400140b0407403a1024108610038044102d61021080f00042da00003500c1c00c115082114001c404150148192080340600075220f10038819119480c0c2e1080b0b880d01d01c0c0400321203043d000344e000901c2410900c1040519511080c40100a13600d00741440d481c26031b00e40d0ba900003055045c2d84040d51200404400322655890b841055014000641e030a2040035190002c1c001c0a21050700c0c4031010358080c0c00000d0699101c1d80c04004002c2c440d01d0304007021001800100348109003a1124542d4140c1103010900300071501d9841c8010744a8050144100203500c01e556441d8102480f407400c1d404e40000e50302003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965445269 1250 965444019 965444027
    0x80a200a0219080f0723031f02090603190501090c080403080a0e1203311b0f08150708100e15040c08010806060a030c0b09040b030d02010b0f060307140a 67
    0x28103c002c1c11034458032801c442080d81d4420500c968140400105001070307150000040b082e04001003e402801282c0b00300904d152403c00c0e000340c40c1c1041c0d81c01c0c03121896940c0e6140056025444c0e044004207072560816090003213950607444000203520f0300e000100010340001885074415018100301005030394400500014200b10710190880e4003454a000d104050f481c4003550055400b204503001b2070304c807000074141d180341c20807041041311100d000640004820044080290002003085030740c0c2c5650b050104942c80c4076403c60742040d040000c2c0308840d0146400d005500007d60b140c0350225090260501c4031502080c0038110303190b0114000a00c0016580f0218020840007900130031582c0c044010040c003c0d4001e01a85020f80074500110f40540742203680c4005a0750000c41c204241403401800b0189a0700c900e10841c0c000d81c0360040c0320351542e800e201654402c0610b07000401d40018440810401764400d41c6418442d03103041c002d01030ba00d40e20241809850050604291341c0d625014001d0b2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965446519 1250 965445269 965445319
    0x240403032601121113022502060313150f14130804052e02030c0f0606092404060303090504110408060103060b011106090c130903020d050313080403080a200a02 70
    0x2d80c01c603417196402d280c854050f1340181404014103100104a40381140c040b01104040400030398001d800780003082d0703c0c022020050700c08621602003044500d07003008a500507181a82e514103101c40d55250301c507058212045400358032025050380c2004101190761202054040c2e4000c081c0254004410502c4443c004034068904100c0b4030b180003010444180000c0d0342e5403041c1040320307050052409001e02e803040041c0036401084014004c44441c2e41c0c0100783e2200d19100c070182e8580e0407881580c601141c4840c482c1c81d0145000359600c10940e403d00060100707591003800b41540041080200b00003007a4045503032030559a0290340481c0c100c014400490780c01405000e2030b0b03907074000c0805020340800d0010b5280b070944030564000740e041444401313100c21940c513000c0180143c2c10090f00543c900d8400c80041d03074845444003204e01c4282554981c64aa60011341003121242c0700002c11110aa82081d4480d8800c0d00849524080030105550151108503691000b402041c01c00b030b01d0300072079000106030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965447769 1250 965446519 965446553
    0x30f020c07030f0c080706080f1510090614070c12020a0f1502060a051905090f0703050c040b120714150309030307030e0303150f24040303260112 64
    0x121141c5440b402c20a1080015500c12128442010000a030f00c0f14085040c2080700c03180c0e240c580b101d070b07500e00421040303000041421140c6104010b41c1c5c5810b541d04e4101030041c981640d0748252203410550041c0c4003c1450745586e5405509102080c001101c0024000554440718103020501f010340c40800e5181c800f80d0000c29205403401340110b000a0360205c540b0304445560f0807102d85844a541d400201d68069500c0b00306030303030000301c1e402110800760809604001010200c0301e034140e0500d505070900c2e22135001141d0a030480c15044240c2e281902400c41c4510003141c0c850080900705504c5030b600c0c40980314840d0365401d003080300030b0265504c0401d004a148c030780a03660b0307881c9400b00050b512036000b1110000401c0c5081081440170b070000098900c148403507621303001d07881c1c0c0c0d03082080344078080d4815071940a0191803507110444d604026038105d14810b601f60545490641c5400f170b0124050100440750036207040e510103180000002c072141101d9100d8071214840d141400c1640034204480c201c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965449019 1250 965447769 965447773
    0xe010b0f071b0b12010b030c070f02120d1107050a0602030a080c070210080105040c030605100302091318120203180d02031c020d0e0f0306062101090c05101b03030f020c 74
    0x40054620300d5080200340b83c110300d13035a107020313a81c80d0701d4203010600041d14040c9258405000c2d0a00140030070358080006400102089515284c12025a14207038400b40c2c4000081d2400e11160b0030311400b0030000e0050101251240e0303a003418144029540e0094401503401c000c01d46010492401d1654115650300750064061011004030041c0500203a40a200701da014500e07084a80701514402d02c50f01054030001058848207128131001140a50025050980e10900c009003800d003142a0788a40011881e26031003400544100d0709068903842144040c403001c0d90810064509140c00400b99481c400d801110001a5041c4900109103000394801d00d0180c60301840040e0314007a03400140000485010f50354030101c0ca83d010003407040905a210059400d54419400300c3d03e1890300ca2401e450074064186400c9010254500305400d4525600e000c0d209104a164148100c5c00d1554070861508035a08203c0300044401120460359441c9203805010160303104125210f0622540444400b880d00f402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965450269 1250 965449019 965449073
    0x80a03020307231b1b1e1c03020c01180e19150f0603020c0c040c03110a0903111206130303020f0c0102180405010803030f1306110c070e010b0f07 64
    0x400e140c3c540c1c000d1040c10082d41d44000090900c40c1c000841082c0280e58581026450b0300300c0c4244180850f0021284002c91a601c1240f01c1c0c079124008001c4c3c0035140b070428001c0a88040c10040c2c20a1544907810b8108041e1400c4000c4240c0364030a50801c40750f500c4615452540c1d0100c0421104100050380b00030682403d0881e09a5150320440741c5c1500c0085560602c06681c0780001c5e000c0340314075080c0c46801d80141d1820f07940f600d1b280d4480890320040d82008964004042643d54141e48206414000700d0a002000d10500484014020600c08280c0d221071000c0403180c0010b070381d031400418440c0c00390254001042014032039019101d4407e840d01d01d880c2c4445101c64194043d42000382400f0100b5007118001803030b850103008943c104c6640300301561030350702c0c0c542000080100c0240241c60020004086100080d81d51003a00e103951000d03d54541c41d008410304c0c0030708040c3c0c01d40c44907180c5202c250052066070400011100342902c5032021680d80c0b0081e180c40764901000103801108035450754 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965451519 1250 965450269 965450327
    0x91548060c090b04080a060e0708011803030c080c030a020a0e1f1b11010c06110409140a150b07140109080301051009150507330612080a03020307 64
    0x24211075403440041d100d001030b494550005011a00981c814040c00c1c2d03010101300c002290480e0b220900801e1140155802d0944800c1681e003900e1014a06035541d540c002e00903410305a0511448400c21154507085201d07040400129203507000c081c00c07440c00c181d80000d803013800b00e001c0c58150b403491a01505c2e0b52000c00d0078146041981c0340859030341c4003007410100c00141c00f00790b9206182149078800030030f1921b240e40c600111054459050100d5101f50f441c134810b003403a91140301030001004603000114200203d0120320b200340d5805400031400505200721102523007030311003505058a124140c4991145641d080940b40b23044202c10078907142d440c3c9101c001c2405100350096068490503139000d174401c804c2e00c00c12501c500b01407065260380c03008140400343c498440c5d001451904d014800300114021044030074004030111507000011030300e0154001a8404d014061900100061140108100d1140d1900d0f145442000729040802d5800030014940c1d40c050302c3c00340d0f21038000002802c100100c0d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965452769 1250 965451519 965451521
    0xa030f060f1706040218060307030c0305101d0619020f0309010207140f060c160501020307090504060b090105161718090a0b130e030d0c09154806 64
    0xd40500e8800000b10244425206800503925000b0703507001d02046401c2032088403840c45500040c084070343c1400b030f8080000115212455800107035016401030200921800030080450b0050000b5a01c0343d554496a00d5141e000821029030207800e920700152504a10054240207100d1401d055010550200620652510542c040c0607403c1c803c5c1506c403d281c15100006a0307410304410344449643c0194000b824040c0c1e0701c0c015040d080c025102183c40382d801030b541e55099070002c0b1151000680913100070070141c0b0380350180c0c600404100c9084d500e03100781000000d2540c030a0181165022000c44d41c500208070b0b00104800e0705500c0290305c161180310719560704d44000d080c01c0100d4420584840410703060400c0b032088080d800d500901006071005200d013030801508240c2c0140186000a000c0700003100058015039250814071342d245040c16041c050802c1c40d07020350b144030b8020400700d0074824515901c10003c1c02e6003034404681c0350205030f0792091662400700381c0749480708040c4c1122108030100038103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965454019 1250 965452769 965452799
    0x204090e06010b03010b16060b0d0f05071a04060c0f0b13060e0d0905010c111c02010801090e06010b0c071802180312160501111315080103030903080a030f06 69
    0x5200d0545010707036a03070040001c3c01c1c0400c0c040c040c8500800c05c4034800391440c0e014080c01d400d200d0600801c0780c003460300c0012032032400440c050340c0000e1080040c004000c0c042c0301302400340c030280341200348022500038012420302590095038144144003584c0414041203e0003181480e40c0442c140c603461034424210803c141015008540c0300d070500000e00b004a40c081562180d00007070781d07a0007500d0740c60100112100c103054002a03880703400801c0d01000b00d807202c0010880d6a07140d030343c0b44a20040d00d0b2000400101050b809121164034000c00425401008110241182c90884000d521820721305a12814001c043d448410864010092820320220f180c01500444c405030030001d00b000e401034145504da00c0903450070052040c0411651046034110340300304020328010000029030340003404401c065540406140da00c0100d002204000404100040851201240c40c0844071945580e030301a000001901000b0500c16001c0343c038400c82403103540100c81041d41203606101003a500c2903030b04100b0007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965455269 1250 965454019 965454041
    0xd150c120e030d0b010c05010509011d0a0c120c0906090f0c08060901210203030d0b040e1606081504021303030e010f0e090405071d1609181e020409 65
    0x840041000e040000034440d00c40c4095144000e5482c0907004490800140350303d5100c1c5050004203003003074000c10424810144140c5408000040810245910701c0b05c080940048a809603c80d0b800c6d80001803010520b001216111068015a0141e900c3c0903840403000e600022811480c02800151070300d1590031140c40e41d8641002081003807851070b001c649062044940c1c81c0c001e151034004005610b50740c8409080598081e00100740c1900e940e00203411a801980c0c5014590b03103440000e10645058803628050071031010007001003581801200303044041600c41d62007031007526000500c2c801707440100070b41036400c010310840d0b60707429400d80850007221502040e00001c8071418107041c294040e26404032a11003030344805100704149010030003501c20060048445000700700c0001401458403640940310039001081c3d18072468010803800710100702111480400c00d4480c0200910518610103000c203107002040032903511446a0b0b8031a6421003034409600507440050005210b9000d41d011041c4a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965456519 1250 965455269 965455277
    0x15140102010b0613180603030e1011010c0302031f0501080c07110d050a050d0f05220302150d0c0503040b07050703021204060c030206150102031b010915020406030c030c08150d150c 79
    0x10342e900e40201120407c0c000200481c00c0719110100d140380104003c5207144e001d1828100d00040c0c8102a4256100300c410900401c0c3c0101c1031184034046a19010703c1d0f4005549821202c500d4080000d2645c200642090300c21040040d1840902c070214640419004015006900c00407541ca001582c5a621701c0050320103004000e0145107442c400d501401e9414840c0d9203e40c10b10b84400311454804140080713800800701c0001000005880c0c5440045002411041c03040d00d911018190400307640c03ca110120400a04104000000d584120f900340c2140d41c41c0780032602c8942c246800c1c0e25100d001803ca054502000c030380010180c5c0e0100000d21000c2c8203500b40c5120f41c03204010000000c850120351800350304180501000050100b2100c4400d5500c100045000102c540380d4004001ca582d560410b280d800003410300a072134040c062410900d1452400b000030584241c0d00030082c060280190746440d138000e402e900070313030f40e01e540e214503040e0031a017150401041d44411400400200810501003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965457769 1250 965456519 965456549
    0xc150c090604121208091b01020307060c05031b030606030109050a1e0c0e01091503020703181d06220e0304090f0e0c06040303141b030d0501030203060a15140102010b0613 75
    0x29205a0f592806000440010051200721005450060121f1083d56045100c20702070040803a41d94090807030211080c0c4c0744c0c0380c0d81e0b003085103940c5128180e4101c40700c00c00d881002400b9060b01e131001100e0448070340e5200055182c4850502e03c0242030040e1102c0703032410508a02c003800c0000303907001150041c0b0036107030303011001180c0006442405680c0709d9540490417042002c0d1409000e50000c0c0b200d58440e16101c00410307040c100705003107100a5080214178001e1041e91010542164152940000f0101c3d4607041c103041500d14181c064460010f440200b0752a03130025a0340a000b002910041d10303101c9410b0000c0111a04528020108003039840450310070b2036a90ba0706410210200d40c01d407a099034489419030482c004c2405603500c10891076800b03c9070b9000c05403410030300744064502c1e01c0c2401c601080952440c010185070800192401004618002070300b600d56082206041c220f520b41c040c00046e4000e4400180d00400300064515085280054402c4942c10030260715070554140c07134041168 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965459019 1250 965457769 965457803
    0x42904182a0203300c07051b0618010504121b060521060d0b180c01020c10030906021312030906081302010c02030f07170c04020c150c09060412 63
    0x710012005018025800c00c01c40c0b0f40c0102c0e80c180481404000c0200d41034510201c0b880c0100c0c2c8458115401941d003800429500c0401c1020302001c480c1101e921103154441c05000300083c0e540c41003201c080c540ba0720250400075503900031015900204100c803250b9076000183d06164900e40580c210090b9604c0d002c0d4408158680540e080d00d0b10541380103c81640307005180100640c400e40541081d5010795514a076000050007084064428802140e0700102a0203c40303403641340a440400c218155080703811000400d8031203001c078146400c610f2130080384102103420324000070310a01d0a105036640070000c0c045110050303440d415203910311a0391a50495540c950084515110a0300d03010b0340000c101c1110005580700c0c8100340c0e50180010309a03024044000c0b0824540800e42d4001060300b5071401407050316180074005494054400e580c258079010f0341103051a140c035441a03014110000d00f0340420a000907113810398004000c007500c0c3c6542d494031200450070010b80c5920840f000300254144002e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965460269 1250 965459019 965459081
    0x11130609050d1205030901110706020c0c040506152116080c090d14011407080a0605030303090307170409111309092324010e0c04290418 60
    0xa40ba41d0858680e503115940188222529800500025600d648903d07400c056010a2801011761b00d12031500141c0d910540c88441742000071039410706104910380700420005072186052990b20401150906d80e0369202108124080103802d020004400e10108c2001b54881060400e44d05003801510b48035019516500c80e00894803030b012007540c006103091424000141c03038115420740019201c001080e0351072000c1c0c00c644613100813100b960010301950281b0610321241d10600c3c002d07081c181c001e94954a0044483c039903900c1003010050400302c501c022102027914030400d880c0a0300c800c60061114400b6124100814ac125094402c40e44940740000600d050b000d208980b1190340c000350b4070113500c0c24004da4890401c42020089941d026000e0071000e2008149151220351810390788841155040c8110698846002443c1841d6840200028400040c0c110441d4035840b5000503450700d0307040d406003a80704a005a80c03040710709120840764a6440b89680e0032120402e040001c069100c1c409400f1540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 965461519 1250 965460269 965460289
    0x2703060e030c030a14040e070905040b0a12020d1a01060305070305010509160305040501060b0c010204090c021203040b090a0204050a050916060e09100308070c0602010e070f0b0309011113060905 85
    0x1002c543c4100803001381e0900465a100020610b1000b090400d0359581501c1000141101c413100000d40d46c1c2e2051190745868454280003c80c1a10340d00070050621044020507080342034040d01c10101001c480007003009004c0c08a075451006425032500d5603440703101501406055803118003003400c080010a881c1082030a5511515a45020b5074100c0e40c00e001c254001c2c0006003058440c0d548480000c150041050000c0409400000006035124039240292048038241d108800441d0421500440c20040240540c0d03001504010f00140f1501d441505502c3e018007030200940003420b09040140b02c418582c01b091180050500381d400c611080c61159488444600a24000c0f54000766800810b0034440300d810b50044042c0d21002e011920b9443e488120341001c80e08690044d0044428080680e0a0180f41d450000400040c0000c03401e003140d01042c00300382c1c050030a00c48008800500c5915003500554440039a00690036038810b40410303000701c650b407280100c00c0400c1520350000f4290038007000d24 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 965462769 1250 965461519 965461537
    0x807020c0f0120070807030c08010504240906140718080d12060911090114090f010e0d0605041110050c030406110307211d0d020906012703060e03 64
    0x20700ca02100c44001035031030301118915800c1504221a000814902c100410f0000d003111100608100741b45180c4141e203190950040211a41800144070000e40d664115583c0714040c2c1004009180c64054104020680a4005018107040800346200e00080100580c0100601e989041408050400c080041d8003503200d540b4a5501c08030038049110300c5820218800c000800300851226601d91842003556880382c014400d0841c0066030002030b68000c0507407075240c40e02c9402d071401c200305880050841c00501c1007041c10720107507000304202c039a10903403081c5009a1040c403c100302e003064240b04d84541840950b05002d07185003030b51110400d00500940340c912400f403005524044c10710004035500794411f400307803200d80700601164002414003044a003400030044040803060f110a18011300035000e000d1440b00d00300000d1403869841e201c90041200d07240e0191400c00668495078012100c0312038829480701d0b140c0c5241078154a03500d41b07005101c1101e006117002c1c8025050880490b49070320812001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 965464019 1250 965462769 965462779
    0x10020102180906040e0a050708070e100302040903030204031a091002310f060e090a09050a0b2a07050c0307050d0b07140a0507140c01120e0712080a0807020c 69
    0x74020720345480007200b0ba1004018201080c0f110700c21140390300d03041800c80c0454603900000c60510100c00204111030040c01035001a944034100300c40341c8000e032a528040139016680f07039103c0c00280b5019404650003154400000c203007550251140410614040d5402c48550107103850b00703411040300340281e824110302d91545010080802c0e9444807881040555240e803c1407100000900c030560014110003030005848646442e1051001c001090740000c1405449615081012010500004051508030b80c40100120245c070341504c0800400852846440402c090107448002e20b0240c80c0a80a0075204000b00c4e24070419103420191100a14007030ba030b40094030f1400d00c82c00700b2070340002d0603040758540c1008203003010071545108069200a03c40c0020500c0060712100304603245c1461000d0a0210019000408500b030000700400c0d150108bd15100f1303194465036500c40410b0000c50000c00311542c418060310000e181c20740294118120502c0404d06070b40001d04414000b0601c7c070200240101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 965465269 1250 965464019 965464057
    0xc0405060c01060e071205090a120315051c0506130b0f0705070206030103241104061215080a03120e0d0503070c05010603082706090402070f080a0503010510020102 72
    0x51068940111010400642d03e8050001d007041a0b522103e029a40e565140d00503820072440d100d040e00d81c0540076002682c01000b00307501040c42d003c041a000092481e0100d4034910006513203080700c2c0c1c29040030342e0141c00105140540b400320f48080e06468401d030241c910355511f0120701c0c40c4055075a0300162100d111140060b0441001d1000c059024105007040b50401070f450f00403403841d4100340c004582e204502590281c0030440301d40003813010301c84000188803400304142a20441e0140d80b04000900030001d02c141102806030308040038040900402510322655a8000e03a44c9804820050300400d510405204044806001300d83d42e541403c0d00414020501e1002110143c2c4000c01e038004114075144450300081080c000c140095020381e0f9030f652240d01c2074442c1107130100814500444420058007812590301c03660180c81c10345000f2100180c50b00802d042c142d001d811600b100520812001480c907070010303003142c040c1d41a07900c150b400b480900e41c0302c00c09038200c0c4502035203507443c0d881c0c0d04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 965466519 1250 965465269 965465279
    0x7060c02030705061606050f041104090203100c0e13020d0b01090e07051303061407140703020a14030c060a020a0e01030908092823030c01050409020a0215190b01080c04 74
    0x200100007005182c4451401c0c20b0b125242c0800319102a00c8c1080c2d4428060706100600488180e10387c50407804640801981d501940081e5640c0c08400c04880e6171520385144030605405240355804401c400b401c481c00c640514842c0c038000b0351141041501491810a518100d5441042840207072464601000040d45400405445c1c1d600100d110001d200e0000102000103070303d0f4050001101d0759640c841030f603420000c401502c811120740d40c40140c140b0500020000c20f90000f00c034a40780c3e0300804d1261407407102c0310f1264210702c203610f04c40c201c42c4599800d010583d4095401002c101d03903c0c0c0c0e1091880200c42c0c00440a60b64489800360a40c40244070030340303803032819118000815482806140310507e0784400058004c500e58040324640c4010326240c804d00000458807500d010084003d0146000d80c6800607080f40218000c0c144450f82c0401c00340c0826008018a65043c501c82e0700c50007540c0340501125444074945000c6480150420ba503190306035000e0a40c450080c00080032403800c0074185 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 965467625 1106 965466519 965466529
    0xa1205011a07020622080d090501081b030601030605100909050c0406050403080c0316382404020f0c0d02030304050c0d060b030609060907060c02030705 67
    0x3250912040003140307022207002660441d007041d101c01c110924200d40d90140844203104060840c004949044005040303010076901e80e0300c1034841d075280d20044074014400c0e0341d0148010714400813078200162620296901030410f1600250303d03981c50001810100b10300300b40c000401d040c2502071141100d0380c083d06a120300e82500480c031b094580003000f05644114030000d445c0c0300004c034460302d01101c14000c558202c0c00750b1440d400e0788007443c18501d6038112040228018200d05452041102d0081046a9400c4006850b442d105550f080801402003c10104000c541c101002d118a80c560741e034400303008601c0c86803440d5600d8548900c542071402000441310000d641c0140304100014800007502403039245e00b03031078400c0180050f1502d4801b0300340c241000756141c05500b042001048001134110b22400e800b40c1160703601596454282e4040f20030740c102035010b40281c0e900340124102 = true := by decide +kernel

theorem cover : BRFrame.Cov 965287769 965467625 := by
  have h0 := BRFrame.cov_init 965287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 965287769 ≤ n) (h2 : n < 965467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
