-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:15.238356+00:00
-- url     : https://prove2.me/submissions/4dc10153-012f-43c0-900c-14095313d270

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 579856115 ≤ n < 580035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 579857365 1250 579856115 579856141
    0x90909050606280e100611030706020a030609090311120306010e01050d0e0a050a05060a1a0904060b0a081006050607020105031807030803010f05190302060d09021207030c0e07030b09 80
    0x4840380e050030041c0c642080c5258083c1d402c0d40a001e090f1880a1a0301e00711203d804501c3d0b40c2d5018104000000d0240c4414410104c182c402c521350110300541c0d01c10340c00104401411950704000e4200d85084600001c042cbc00c04115000c1821a50540303e04001c040b508200380d000444a290126202c000500c0c01c0d0742c072a50060640c02c0e44030701c0c0042e9105080740300318602882244100c8080c0c0c4180780007010302000300070351344c2c2c0003121403001c0c0040035040b0200d0502d0b0004102050049000c074000c00d003002002d4024040420000e000221070542c1c580e80c1503a1400507207a02106245404070204040c01c000d0708650880d50103844a070b01e55281c00d010f031401002882e0030015a80501600032000400420007036009083e00004036071050308180402c00040d955422011003910500b40070001030321380c101502e000c8020b078500014084820300110340a1001401080c2d0301c1c1c0168400802000315500c0450182c4810b201c81020a580e00c2c40150304440c480d825030f582c000030101c0001c41c40c41280c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 579858615 1250 579857365 579857389
    0x60610140d020a0503061806010e2106071812020904120504080d050405040b0303031003060b03030705010908030915010807090207060f1505010f03020a05030a0e030408070303030c090909050606 85
    0x640810300e0720140c40c0010040780c200488400c0010000024881c1a240c15540400710503032000d9030000d02e061860018125003002c0402e5070190907002c480481c500d1000603c03031280400344059030070380e14003440000c01c000c4103844401510035003104081103011040041c03100c400d03809015168982c44646643c038600380041d02e007004000d02008045481d40040c4411143e0ae100790311442d07125800c21007007205494080300107034020b5006004100001c01c0001e410f03411260005000524641d882d0042400c51049010260240d0300b402e02c20020840d00800039071180d03050700140c030341d61101502c1e11a082402849031142030381c0006818041200355900a120181c414800090068100c8802c2c105a80b1721b5000200e44035180c0c0c504102c1540c100b01c4062240c0d80078a42186006a1704102a110380401303000c070181c05a80c0c00450f4103038101003007140c0191100008584525540e0300d4004c010b0a540d242150006805140c001511138060040c0c400040d40000900404e0b030f2a42c0c14010b0194a032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 579859865 1250 579858615 579858647
    0xa0c0f06180c03020f04140a0903270f080601053f0f010c110a0b090c0a2301030204050607080307090f060903020312030f0c030903040f06030204080d02060610 70
    0x100d5031081c0303440000300848640c51040075141d030354a00d90700401100c88800100d46018074100200000481010f501c040d602c55901580003802c16864281141d4800d201201541c011911306441448002000c50307174070884409002002206407542c5080307885100030710401d0303080190b00c00c4003449145440c0608980b440310014440ea21841007036035000f40300018000703800940107920804007012080c06140088845e504004240da000d15043c03d541d180c01107800b0344400b2181c00400c40c1000c06020900c01068000e1000550549441008400e0313560040b02c2d400c20103d00440c024194003034003d40d811540c0040c010b46c14055652102c10f21030744010855400c1105121020440b038907003255141c043d0505644480b0654214410300d40b4150280c0c1d0208100da0041c130801c5031400c1c00c80c0b6501d80c0300403041056500ca0311441e90f114954004c1e41c0060f281c0c0071906601041059247e0f02620441d028074044a1151510b00c4059880c1c4d20141c54580c0c102c0c840707a4880415a005210292000ea40c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 579861115 1250 579859865 579859871
    0x70606180b1e10200709021c050f060d05031c0b0307060c051507110f1614090c0702010c05070306050609010603140a0203060a03150b0f03030f030609070309061802010809030a0c0f06 80
    0x34000005080811703036041146441e5001c14080c04482c2251500c00a00c3c110000c1000117042c611007001100d43c00816145c0709840c1403109200300201402903981008a0148c4610300c0d0b03a0900d031410140440c0643c040c000d04c9200d00000f00c540c0300d0a030361401d040e040070150140602802445020150081c05c101c2840621120100840403c210030f00200103d98044e001c942c600c0c50640900824950052060102c2002c8200d03a941e00c4c01407086d0070400c1505804d60300c19441c0b005035000643c004024050b4010850000107100180d00030b2403041c007044800d404140e8880030280d04403480f119100320201540d2000544100c83c5030700541d00410020b03d0390f080240e44e41d4810040048040401c0005d0341c13144072041c454103041c3d14208902c8400ca02460030103c4030031180016000090945100700c81c14004125003901a910941401e13402c51030500c17100d44408038038001600008c3c000c90010b0540f000055103640048103032544042e580d03485001d400755544808000720b00708401a10300c955 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 579862365 1250 579861115 579861167
    0x200a050901050d06120b0703060603060302013e030304050114090604060b01020c2106060604060c0b06130c0815030601080d0c0c15080a2004030305070606180b1e10 72
    0x100e40d07013005e440070b2062507038180302d180ca044000d09a40882c0c1c4031205040c103148090005030780100900c4c08002d5102c00b1000410840d14010170350034514040c400b0082e07409005041502c1000c001144510302500084c8070307102c5034403113082003d1011035031000203070002c0c00454005080780c1c20a138060001441210717440d40c0341000250340504c1076401c611900e849040700226001c001e000c141e030321a000b1076581741014605240502450454030000344203110f150000f40d940c0e270302c8100c5a407504005031400c001d80d01e0040e2014100710300950f071100701d1034600c12914503d890b0001e8038a05032007183d0081c04895030107050a90314150368820071100d0400007907000c5040504d030080c024040c20b10f0343d45c0a80d241080311200044402400407103440b42009031f03070400c841d6005401c4800300c0e641441c020359640c005090180c0244140c1e042411000220b0020f012041015045811480d50890b03450001c406400003c185440b580c03003901c0c2e04481810000b924050240300309190604000d92a060780349 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 579863615 1250 579862365 579862379
    0x1a041110090e13030801150c03050a05070c15031d0706050d1d150c04081e010f05090c040b060306030c010302030903070c030c0e09161a070510200a050901050d06 71
    0x9500f11240003096501c8443c5038289940000c400d801005245408044080309440c001c02030f140021001c0d081c440001400412144a80111a6825007182c2d141d0b01c0503850f03e200c0380459001c04007040c0000d051940500c042880c85210b00042d40c0c5050040418034940b04c02910103800c001c46145040790354032090365440800101c070311441c038040c0d0064a0703460300314030360149074910140200444d010f091006000c00900001c3c010850f0300c44c035038043d06032a030001e881da01401c10300703003090a26803d00c018009400000981400b14510844040c000d1002c19414000c0d0b90000300e9845604d07510000465000354001e034003c50b00026810203807860040f0a032200c07a03007461598421a1202c924070010080c2c12002e03d03120b60441304141c0a00160003000c1303d60394180105000d484844078011140794803401e4034000f180c100c41c0d440400e0710441e0240c040c800c0c001701150480405140d941c4080c808001403c401101c2100100b5101d0034103090900c001100c1e0742d00b01e03498000718130f9540c050210b002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 579864865 1250 579863615 579863639
    0xd11031207050c030d021501060813060c200a0c05090a0b0d0506060f011b022e090f090506060301140d02040504110a23040504080f0301060504031a04111009 69
    0x82401a00102051a000c0084c5460202c40d100c1000440d0090007401000d01820103040741113407107520749544a80c48440840001555100c401001d4900d0200d104403403a402a4009040020000c00f0414145151042503110078295400401c900182e107014810b9103081148550030000c038030000140c62515601080b1020200c000c241e500c0c0c0d004204004031481e040350185808813007842c15071030b5081c0e2281510b140e0780020500920404601e00010a0703020101c45002d06c010034400605402208a58068503220b114080c20201c0500d51070007042d524802d004e6503010320405480145107030311300b080c0210310240c0b50f90410340c45203070200b0120145c0d03241c3c01058003540c0140359824200191a0800c46200d41030b91098400c000f0400e01c5582c0801310220100656030151404180c6039503c2c40e0510043c4910700c038149812101000100d100c0354407002030001d4900c1214051241900b5024118866404070b40040c007003024540711200604002d1000398a03078405050054034141c03178910908003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 579866115 1250 579864865 579864877
    0x12032d140d091b09060b07020f0f0114130806011e060507050c0306040b010e180d0507030c050d020d0801080c090a020c1009060e07090905100902190e0a050a0b0d110312 74
    0x15150001418410341c01c0d80e00c605c03401000200400d900d0501c0356404250345a0703140c91094807400070b510307002000d42d00a4285042c5420300c000c4042d035a030105032450104d075059000c5d4a003079215101c00840c1c101c0600d030700c103096140070200c814003440c5010011030b084d60000d6011211401001e07806156074408001050049100d021502e00960500c1c46490201c80700810146a0700c126030090955018045400d44200e0110301e85503a4904950400707a030844616a402400c0f44910341c81d0540346940401d8a4a000e5039580e115102170340d8030820107640b03401c28406c507584290000c0104500c844240d00070f05d03a40e0001c0058648807102c0d500c840084403080b90056600b84d0b00d54404c4c183d44841408aa00a041140c804016511041e21a00d0b9520f8500c2c55000020780d441c2c2540d0203540e80e0200ca501a00356900385454016240c02900740c40d20303400d80e90141414180b0700403404021541c010414140009050703034041c040951280c40d4101ca42d2541c07103416001d20340741c01d1031146d120801001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 579867365 1250 579866115 579866153
    0x40807060519050114100f0f0f03090b0c0d0e0d020d0f0c060509060402040b0109080309060f12071101060f21060605130204081002040b030406020901030612032d140d09 74
    0x940d6913420107200c41c614490f40c4d51010001c100b10a46201c0350004c08c04030b035800ca5464501c0049040c044190020f140e00c09026040350548810000051484001001030000c1c10030142b086848400304a40d5802c04100c00d400940c201c0310441c1c020a201d000550041081c1d846d182e0300d10a00d5403500b80032260299a03913202034002e07000301f10540c10503000b0303050804030070328103490403503d4490110303124002c003000c9510070b2000143d40301805000c00195907001c50f503070600c000103051064010b411030305101c06031000c1d542041d40004006600300d05030401c0b1034a080f05038061a80c0d80700700cc0d044244903042240c40039910f100124160b2511000c1c8400c94541c18801039075242001402032400c1ca5400800d0079541c01000b00380419941c1c00160780d00a588000050b844100800058001e004507410403000c90410001000c217142d804101d40c050032400e000c0114552180d5102c0c1c1045030700d050010f4010440e00e400c5560741420910040c00d51035a01c52000461903059a21000d0b140c03040e002d003c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 579868615 1250 579867365 579867389
    0x303020604031403013008130611070b03040206090415080a021206090307030c150c03020304111e060c010908040f0608100312050304230105100e0408070605190501 72
    0x2c150f00301119082001480030894195850310428500000344000041e40e00c5260910405840e00035610403020558040543e940700c0041c0e240c2100b200d101482080009038209000030355480c4041680d4098802c200c1800340346540c0d680910059a00002003c0e40159503404400008855060020054150342000d098040700034010409071a04c0c032034081001d5005501070207508407001040740c500680c181400d54105405080000d4103540070100c0070001c0d8200b80203848403d03403540c000c52055104144102d580301e421010f00981c009480790902c0d4500c0d00165091091400e01c015016500c0030500100702104155a020255040303544440c51841100001340402500549402d5001c030b01000e840100d1071a42d01e403007000e5086291074809000000020800b40065000d08410718560700700007240d80d25410003030a000301422030b2080400f14032a00003268801000d070b4043c0c0100d0b0002035030b90410780540c031403800074030018004540c0150b400e0030b890200140750282c1c2c5d0090550032240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 579869865 1250 579868615 579868621
    0x1905090117272e2403141612030806190302130209030f0717151b0712020303060319030503180123010504060b0f042102090103030206 59
    0x140c124002110080c00c50701c03145003005030400b01d072440e54110b141c0642c0054542c1d80c0754555242000e8004601c00d0070316200304018920010b40711160754854025903801c001600e0081d000041e1004800c1104c944d1402d481320030404514180c5100e07104100c035105580010305096416801021144c0c0916034100078000402c05158200c404258020002d5880c41303000050fa000e003800940c0b05020080c407a114000c0d42120a9080d54140e40c12424060100c031013440880d8030150f40c07080303240302d5414905825a443d00000c0c1000c100d02000c0b090701c114115132512040000c3e035010080c3c01d6010303660f00c0184001004911110f5050401d100303030350081c40d030740d04000b030901d0304011103c207240d014051848440350000ba0310008495000b0780c2e618425800020317140683c0d0141c0107031244c0400750031551103600c00130010b4041142c100c0d0401c0740e08110507036880080413018002d403440615041000d01c030801c4030601510019080351612001c1d107030800307081d500069048000783c20540040e03012400b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 579871115 1250 579869865 579869867
    0x10e06071a0105030105100306050a0609050118150f1208120403051b06071409010c08032d0105030309060d110d02030a0f0b0907140403081902060c0405030601090b0619050901 77
    0x1060b000d0203040d8028805450f1102c0702a01d0704085100082100340c0d0b450001d50503418641c407200103010040c00034031036075940e158016846940905240304c2103241c035078010650400c0c55040412601c010050300da015281c501455980c8500c010140c9140000b00301002d03610310704c4006544594070076101d09803602800c5070700c10690100024840c1c055404901485501da80101d091140d807a101800c00340d075011070100488401c000c003600200001004402d0001c03604000b100141e403030f0115420340c0d84c2d03100c26050719240c4040a1050b9074141e08200700309512814240d00904031070024035800f08d0851910303a200070841c3d000340c400c3e0310f4241c0d010040c000201400e0040c0148024100801e11007405402d00140312914041d2005051014069403a05450000807d031401076030001052074a859100199080f02138011808e0030040c0103031000a190101514155401d80d100540200805e030b080c1100c80c0c008082c20b445403640400d040c401c1010a06d1051000c801c4100c16940c0e0548410301080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 579872365 1250 579871115 579871163
    0xa200f1002130b0708091e030d0912020d1b030609020f04090209180a143003010b0a09150c020405070908060f071701030b0f160509010e010e0607 64
    0x410503095004005400038400c19110660036214800c050030390f41e1080b450600031034424440d0301c0e6000101813511014100e01e240c00400108401e80a4803400303000543d084030400c2c2103004090711208030f107480b4400b50619030340180c0c416206e042002e045c100c80400010000c0d10b5580300f201c0181d21241144114100095460303407410054509000e51050baa0015080d42c01c020506008000081c4130100e440104120320340485821580240c0d07810605102292228084040004e5184c00303191048c03081d90101001c8003100543c0d0800e24216403c2032401c00b4654441081c1c0070400050f10008a14808010030342c0017080620388038501115094030520094600061140c0c040c040d10500030000dd0902241c0c0325408a181d90b910182699168020350301041c078102d00c561401c132540004003c0010380100640101c1e182c21101c4280e964440000c050002c2c07660204000603014401c10141d54000d000d18595040141801c1110703405480124026404c41841034801c51100a86245407082500e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 579873615 1250 579872365 579872383
    0xc0305160510031b0f020c10050d06300302011d010c030b120307170706050f01081203070c02010e0f090a06060305090f120f090907050909130201090b0a200f 69
    0x1c201800341c08403d01c03031030044042402c0341307000b84110300c50203038541d0f8400d0045018034000141074048150301e292005045400514000c0c0d0f10314504440807401e4000f44820101504440c5040103e10301e012002d001c0118070380400301c06641d20303611000c032042c518001100581611800002e850116030300000c0949413003481ca14014a2030310b000340d11a000110841d0b00150704025221030316112482e01c50040e03c81c282e40071740402d2800e418442c0100025031054125600c50341100d0841c0107820808010344015504040881d410003204801940194240001d101c4000c04100c103d00c8040042001008111001c5203166a200300902c0810341600c503041e0042c4109000741481400d01c5074040e0394002c041001c402814020500310310f0850000c045507681400036007428220708080d0300144c6680c0080100c28890042c5000060b0110003c1001c000ca40e81c05039544e982040c90241e40240ea80c0c0240c228808001e0481c0c0c05004000305228490b10343c1c000e1000800c4282108450281490307290 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 579874865 1250 579873615 579873617
    0x60b19110307080a08070219210e0411071217040f03050702040504060b1e06030c13081506090c031905071b0f02010e221505030f01050f01140a0e040c0305160510 71
    0x8c3c5210300c0030408105170800342e0900d20400c2e05d40c076601c10301c00703842c9149400806503009090000003a10030341c1e860046c0041c64891903100094209a001c156110301c031880c0c1a281c804070741750008000c9041c1c00040201d140c040c0c2413051030b101c2da5030007003030075290300b2201900c03215181c42c2c1c102581c3c280500280d151070648011050b12542000c001340041c48050031185400c44045142e08000700d050b6041402032040d03004a815030b466141c100080c049080714280d2041c1000d50020742811f8165044901c105048018070080d102c0e8030355900014403001d4040c20070819050120341c400710103070058a60030741c011040000f00480343d1000510522300784040074060301a9800000c800011403200040d40458805d011800e64241c400484100e0071503802103a2600c00c2c0c4400b5410340700107502690145004180c1c144980e03803121802c40340c251014000541100314008100280707440740c03010b40d070403c0c450100881d916541c0c0e1a52403a0002a00052603088405201041180340c03408040803a03440c0d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 579876115 1250 579874865 579874903
    0xa180807061209110d0623040f12090f030b040506091f0905030d060b0c0c04061401080a0615050c0f0123060307180609060b19110307080a080702 64
    0xd00070700500080c050a52114002d031540d0b07902007086034000d41d40e00c80b8440034044080031021410140007034035642c410755600d140090074107060301e01d80134801d074850740c1c0012018545101c9a500d0001c030500d0701803032000b009103415010071421703400d0304040c0046010702d8882c111030a250803d1410403001400f540d910b03030301060f641e20b064100e00701c108405e0b80c1c03025000510410030f0305185080d07120b907800c141407180c609900854018401800342c58a80c3e500e8040340d14411800050008840c458020210150a4496050310561080d14845d13485210700e000070a20355501e80003000c0b110350b011391480100d0000b04511a0520003000307440a00b4101c1d07002803145440c000d41e124000c0e0400c00f5a10300f1007607100b00261058030100580c1004007480d00844841c110100345c0600180b400b0f02035100410b090520010750a24040103030f8511100070100c000050204a0007620005400c0c3c182c0400da003c14800c0344081003850020303002d00c030350381e442d006640d107070240c0e009040000344014030010380c3d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 579877365 1250 579876115 579876119
    0x216120308091b120c0402030c0403050c090f150406030c0303090302011805090c0c0a0b0405012c03090103090309091a18040f02060318240f13031d060a180807 70
    0x103c40c000c002c0d0000826200650094400303800c1c0d07400c0c5034101000503007040c000000d1000601502d0018000c484c0070f1002d0300d02d00092042000903c800c242d0704642401c0c1c0038404140000c484000f10019058001c20000e4032a5681e40c400d80020620380c825000711f940c00c0c5040042d540c201c0346180e010300c3d017103150b07194407400c00700007a28004c0040c0101d040200007184802101d101081030918040e00104548441d182c1840c2240c081c115240000c1c0b54845c0000740201404000c40720f5000600341e50000c0e41c01d29990000440c024840803a0540410035005400200b041c41c61044044480340c04450040d2000c5400900502081c150b07100c0c0d82c920103203000c01012600a81004001c2e0380d045400c070b40d0b65182c8600b07080504032089400340fa14040d8240900305080d92443c0c80c2081c1c0c40d2207600d444a40c0d126420201c0000045a110180302c4c540b0040750006441748012560b51400c1d52000b0715919a100b01007180c580082e803020010407591003541c1111034501c80300400421020b0007e0107a64 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 579878615 1250 579877365 579877393
    0xa0e15090d0809190804031b06120c020c100c0b04030f080c070209040b06130218100801031e08070c0b0310090605011d04060902071a090106030b16021612030809 71
    0x20042142200c50444ca484004080250360340c122401540c10944812800303d400544405900181c0726801c04500710303200c500c5800480b405480300207112500039100280324507081c0030881d06010212000c00540d10020f400144511304428084c0d40660781e40c80e00e40f4003401c4054000080502080b03040ca909216040042c5d444200707441d406980010901c20f5511048003003080c2c0c01a0642110006001199640482010088060f85100200c54903144011680b00c143c4401500380030181c043c0c2d07021080b148000f0301041580d43d02c036108036903c5260000c00c0e00c1d4482c01d0300300354100703c0c601c0c1000028003961101100b92030000c1d000307102c42085003919000018160f1721600d103215500e907015215041c06035a030740c0e0104004100c00340701559a0310003441c000c0503400076074140d40310340c8a5800100e400c170801445490b01392584890300001640710154103144640c8400b5508c0114400e80090506000400030b0200007401d460042d00d48a016600d0007038603489005104440c3c030390081c22103003981 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 579879865 1250 579878615 579878623
    0x6010206100314010e12090306010e16270f03020910180b030a0209040822080712050a0614010f090e10020f0c032a010905150a0e15090d0809 62
    0x50307502040c03d008404000c82000e0140201c0241c051945c01a801010000307020f84005009403a02241a2030090380c03944140d050104080c0c0c0c41004c0b00d101da21808440358014090155900600001d4001220507902d5403055001540c200400782c1c156408204114240b4040890300010080c0d1078100d103c0c2000603135681401c8400021921540380c1c0035900ca103071010300ca0844581d4000c3c0c2020180d00d0241880c0c04036520004100b81c86800c80c6409516881e4100c08542c00d442003030002c0c0910707602d401500701c51a801c403a015269405422000d1000940341d200305008210703280d19015a942c034100814001542a41c042000741e800d14260620f035043c0800c0c20424403031b00c0c03000180c4640c00c20503181c030b050080350f50030000ba10000824600301d055140040300309804e0721021141c12007414281c1c074240c03101500002d1245d0b0003055159507404030318581c0b6610079003d80300060100d880c4200c0a1a040d0500040c402070040c400605c41400424170a5016000582c10403c038181801c104a42d82e17 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 579881115 1250 579879865 579879869
    0x209100e120105090303090d0c0519170d09020112060e011203030608120705070906060c0b06060f070317090607050304081e04090b01090e130b041403030c040e0601020610 75
    0x20051603541040d003594030803020154014560000b004540b40c000c620b41c1d540d901c01c0d02c0109140c03181c0c10085400720300c5000185042640314024218028488940c42d45a80184000b100c0c00c03282603027100316a4107041c1c040c00c1c3c0000d07400c5020413041c51900014220801d18504045c220741001000c1c040440001c0480341121004090000c0414807070404030b008101c030740c10000041c0184244d80d020405544080d1003558014020360700d030640d0701c0c0100d0b42101d03198032411001c1401100100e01040041c03004950103040900442d1420702c3c00202c960351548050002c9000c9803880700e0500c00340c00856401d0780d2002880004150354185158054824000100014044c00b000a10000071303c4202d40c035280625000211540c40d01e0700d030980c00e00907000030180c1030b0004140000006001703c16209031402410f00e0100780200d0f10480c0c80e0810100c4c0010815a000394419074044034405041004606c00c0c0602010a40c0b21341c06e00035404030120300685040e046510850a0000c2c0c0c060740641001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 579882365 1250 579881115 579881117
    0x1801080a02010c0623011a040f0b0d0e070b1b0111040302060703022d0d0201151406040e01031b06030615050c0a0f0804090b06031b221401030f020910 66
    0xf2610a0510701032010704a4004110907065400b04000d20000700040c0d90f5043c2c0ba0410f00082c11040034000611060189101d040000040040104400c1504000401d410404c1d0791004c1402c070740c500b6035140740806c0ca5000740c012602c001865407006002c2c204490890b030401d4002d2140890850100c03000b406a80400ba1261000062030002c150081009082c100181c401c03074488445203c2c3c41e07a01510040440003214050444141c3c0d0300f51042c4900d44078075890002099029041400c001c44aa180d20701042d00400204800f0a00e000c200b2107403030095100350400c03034607d49644d448541c1c2c3e42040d40707c01c041c035080003000e10000c80d640241100f440903074605607441d001001900d40c500400d1000180c45004995811000d00c110344004100f5907403010018040c1c5c000d1001802540d1104403003801014500050000601100c10000c203d0040c0c0190b010500d020b0031607200015548950100740001105a0455801c2d60503004020840444200c11401c015820000c00c18a0356881c04001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 579883615 1250 579882365 579882377
    0x60503030d0b010909050c040303080f1b34020a0b0703050f030a09120c210509040203150a0611061006050912071503050f15060f0f070816021801080a0201 68
    0x1c2c025910400030500100b2620605002904040c81c1c40e030075991040c00154005061b0200042d1465215030389103009109201001c60714400055400790b480c0c11000c0f5000581104d8205c05003054502042040754840c560003881030b08403a40304004030344010f0380c090030461b00203100000c0400d41002c191503030f0201e1125000e0380d9507613808141c8018a01c00304010200b038020b00c0741501e00d65101e13045a100c5880340f00c1d500303403000d03015040400010304801c4100020394104000d45075401c0c150040c58000210b400d00404030740041c0001840d0000303503009900028515507046840342010800d0b96000092084075041003421701d8070081003403140400e400e0261580d50014800c040c401c000345d400409059500130404001410700401915007503500ba00411100c0010550122100203120003c100042000c2c0c038110014206c241c80307412100760001c80f68000c0c06030001040100e0010420540380100b04089000940304010f1022001948000009985801032011740c40004203407218580900f040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 579884865 1250 579883615 579883631
    0x120203040204090803090c121218060903060f0709060807050412380108010212060126131b080d1b080c15070c02010912030e0a0e1504060503030d 64
    0x2c2030160406400090810400000300043d0400128503c5410102160464000b0500030a071560300c20000c4a031302000b10003046035010704c0003003607554642900060030391800d200e444000203092030011148801200000c0c3c00b0801da6507808420f0f0b001400c610f0030004154140340740c0007465400307180100351083d00001c074180c1c24000d5042038150920401d00c01c0091110b1102042031581c103500d6245921b16000d1400800e1403c4107009441640d200030f0082c03102640c503040112507203004171700c58a01010301c00441400c0d440100816902c1408840c1c001d0354002502c1c03800c20088440c1e810b8840e02480c0501c2c05109844000c0343c11f034400100c07443c1110940310f449200c16698822008000e000c0c07400016071501c40400032401044514002959008560b105a401c3d00e8844160500a00061121500b03028060f440743c007980c007042c007915102c40c10140607408108045216040b46415188040800c030318040302c1e204a005500096405000c3c66140002280d500e0013040c0481c086a80c4400344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 579886115 1250 579884865 579884869
    0x90213020c1f1b09060207141c140304030b0f07110709020d14100608090a0305070b2502010911330c1b0406060e090f071814130501061202030402 64
    0x410888a1580d000c460085002c10f009020311015210300405801149070008034031500d0301c1d07603d50004000c0c050064154400103001c449155455085520a205038105010828200301a01c003840c8076403c00104c500b8111802000d031400207007900c0c04c021054040c00c1d540c2102141d88000c40d07003003000250f0be4142d01d4260b64080c2c0105045008040021010007909098600640b41260055112201282c44030800113803103004019020700860000c201f41c4000403a107443c646c2c6d010b5565020b051031909803d2b0407661000c500c012840050f07449100c5201032284105205200401c12141c08000b4142c0746191003041c8001e40c0c510140286511006545a2000c4221031843e14054151101480004007070b2003843d40c0018058001c5103042c1020036a94059240a581682c00400400a1380e9404c2054000a1070080039001003110a050128035075580743e5003400545410700c2c4c0d010502d5503d0060200910441048030b0744103080000410200303801c403610030700c0d11a90702005a500ea45e9400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 579887365 1250 579886115 579886121
    0x18061205012102010f0201290a0905130f0512040303030e070509070e12190c210f0f170f0a1412070c0305130e09010b01030b0a12060b0d06090213020c1f 67
    0x4c401d000100040c10000030308c4005c030740c5068000c100f21342500724161155591001c503081111004455080740000d5408104840c9002125034421002c44600550080d903001450308603234002c9005c03d8513800c07400304020043c007034000a8402511244143d240000000346010240180075000c1c1d034a0344010750a0340c03803e108000040032040f80c219114400d41c50f1140702d4000074450316400000f4043d12030310030300c0240d0800b481070b074020100031030b00304840e22070b80301030181400105d45c0f012244011aa6905000c1c025007801c4200c0e240d03082d00d0708d0b09124054880741e203291402500190070030184025071001e0700d416400140524119008100c18a002d9a0521442c4150002d021502c0400505041040702e00c0e40b0458452000780108070001c5c00540640b40300c0504654000344a14040c0700d42364410503140d07000d601030340011880340700b0318000c514110030428041d50140d07100d082c003a00f907050250b007043c400c0304590011494810058546a112150000000b0108448018601e030900c0560 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 579888615 1250 579887365 579887381
    0x19170109050a081b0a080702091e0a060515030103080313080d020f0d060602030702030d030f020913020702100914061809240a08150718061205012102010f0201 70
    0x541100d1030691207080c124842d401100f2a481c2c02050b00840615404011502c800046d90140400c0d081401980c02c0100d2103000600260410301c0040224404581c0d07501e10354094424a40001a070380c0c1130030180400140e00444505282204200420005980a00f101d40c00b000040f00d0004050843c03906c3c9545128164074001d5003400428030040840b0200300404880764080c40400c10b8550350101071ba101c0c011040c000e980b641000003040e00c46030107a000180e0104124000600d0200345000080003158000c582c0c00140f5030100b044001c60070309000c50105410f1505103001160303d808050030f070b5102e8000d03029000310008951000d00306051942844030101c02000ca031032034641182040000b00c0f07103030101e0303146400300a17450f038450402c1d00c1071a0644100101500762000429000b43c07040314040c000e40200b00b40c41007103810b020b0501c41d820000d080c85950301d4141654103501401518810780044000d00a00204521580300c0d10f01c3c00c2c140329a0a0070648081100002c0580c0104124 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 579889865 1250 579888615 579888623
    0x180a02060a05030a060f080615030f03070f110102190818040609020c1e0a0f080f0c100515010903240f0f0e280f082719170109 56
    0x101d050862036800c5805507210302d4000008201c2d065803605815481d9600c1c2c4500b110507000302000c10414903807048114000b003000740c1121040c0c004130f06514510341c003038201660540e24a0324540100081104c11400400e000d10040c03450740341082c00c2c2202d060321014000c050309800905000700e110b9505003080e00d201f005000704070555441001d00003030b51103c03403122841d0003215038000f020f48142c556480c44101c1c100c010441852560381d0791000b401c11400075204048240f1521111076810402801c2202044020341200314210003004143c0b4405071121880700d00e4503070100e03e00c2e40d0100398031007120382120350201440010521075405d028019210091036081031900c40c6200c8807600000c00803910f81004000841d8060300247e124a804504820000410398484460102d41d21100030042e0041d95078140301e51050341c070681c450b44a14028042e01030f204102528103410380c078892640e504181c0304400b004422072900059007150740600141801e1031002c842421009505c110030756548 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 579891115 1250 579889865 579889867
    0xd06050607030e0909120f0901030207050d03060e0f071d12010c02160501170f1801020304030201091406071e02011107050606040501050a15140c0a0c0503010f02040509180a0206 78
    0x5a824001e10f84860810641c4c0249640300110f1264000016403420300f103680b52201d800c1084503050000c03a42d2103965541e0415401340302c86070200350b0070b1003107000700c421a031400102e06190005030740404000038080c000f1840c00c10100703c10701d03800069606144041b41c22210301000a580010802c00c60407000d03052644c41c1c21484140c0325000580012800100ca0005040c2c42d9684011030340d46507a24000f0405961241c0030501b4011805a1107400010300d0055914017041a034090f4220b030401c4400380c006139120807c0006008110307858a03410b01c00480a4a02803130b007031174090300710240740c51801c1145800940581c00350303100794001603100000c00380c000e580e8081c9040481c0e0f60407040e20114840c500c2d280c000202440c02070141c0c807c48141c0440c0340c42c2091994001d44181d004200386000c03030041048400c00c4c07210203019075a450380c413502405408508102c1030508444101f05a5103009204010501c0f07517654140005501414480e000f0245040d1411880c1c1841c510080081d00000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 579892365 1250 579891115 579891127
    0x3070311120907050a0f0b16021905040c051204021005090a03060b040b0303040f03060f090c0902120a0506030705120a0b0c04031103071503021305150a12050906010b0d060506 77
    0x1041c40c140ca0182c0092030440d5242034480b0100500140c0a1068800d903500c184002c01003440d681000c2e04d9a68200d039034508540007580c010a40303c0c0840300c1c8420722100418070030300052815115940d05680c6628100781066910781004a013400d0240002c1d00c9060100c0c003010301b61b8810001c48044101c06000c40b4442d030b54a10b48200038100003007500e44201d040c1203203000d1a040000540c0c04441000c041c24440618545440b0020114015112807544e15036040e0340c081010400000000d0001c40d0005a0798034440034018000107000d060700885a0402c003c1c030010b60390000e45030054030000c4031302114410680b410203203411510305e0000c0107484004100480c03400071501400c1101e01403072801c0c01402d00d2004040e128120350050942811900c1d00e405e001e5413199010b0701d5001401860b1001607a10381c4001645800c00902c084014080000c07401e44455111180300022184101e003884503041203201c2d0754803a00140500d0201c00004280401e58140c150401002088098480c86d5180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 579893615 1250 579892365 579892387
    0xc1713051603032607050310051804030210060503100b03010f0603140f061e0a090c08070f0902040e071103160b071103190e2b05071a090603070311 65
    0x203515031105402203801d0004413546030501010001c119060303640880c0762941c0309002500d10380c01c06018900d404010410204032922094204e035407502408030b4007201c516040c41c000b46003010030184281d2040c107160042000d5280001c54a5000e0030f40c80001c1038140c09400400d0061000001801155052020002c04d0080300c4000d42c1c502c104ca0015101d1042c50fa80d11a983c50310107540e11b0078000c0e55803a40036912406150a580c104403140c0380894076903001e40300d000da0aa0030380c22a40f0543c0044200704611620800c0040050103d9032040d400e2600c0c0404007686118010254800d12040322a0000c0c0300006004440d214600d803820100c80151070305200c24107403400c0711180045543d08041804010001065903816494580240c0041c1000380c801c5606c00d112084407a04001c1d0588090b041180403209142c0c002184583c0d41c01412440c02d06034602181303039001421240380b0505010f0500c140004444c01101e09a54081c0d503500c40080480042c07031000400651014081400b038424 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 579894865 1250 579893615 579893653
    0xf060309100501230907020601060305070c0203030d050115020f03040308071109011401020c120c0d210309060b0105130b0c1006030f050c101209050c061b100c171305 73
    0x1220050400054071340042e0140100c080080d0342c2800580d110100400619210350000d99018103035251056800a0310740c0400d01d10341101e40c0d440d44407512100107102c0007a40000190102040d40f0007443c0700e484c044901a00d030310980c00050400e040c00a0094203005000e0b00d07a60b40d440001d084e80340e00d903070748080c4124404038102410380103001d22a42c10540d45820458562910901e00c050701d20400d4100802138403840e81ca008407400380c211041400311120411000f0030360400303a2000301e0303040301d5450309604403440400894140482407210000700b00950001c1e00907618000e0010f66154a10552245013602010a0b001c2a5003403020100400c000c14664025092240e03040350a044440b00c2000f50a0b00c00005060005086e0304002d00c90551036007010b50600e001380c09071848811174601055095000c240c00742440101c840a11202c03d00402020310700390725511003040310000b5010010081180044415420240480400c038842064103420218070f034848112500741000c01e080000d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579896115 1250 579894865 579894899
    0xe0a0b100c0615140d11100e0f0d0308060118030b0c0a0809010501050907050f0c060112020a0602010c021903032417010513020d230304090f0207020f060309100501 72
    0x10500782075000300255040f21105095135121907404e0f040142e140c00348200081e205205039141980090403a103d5140c1c0d0000000030180ca41e01d110140000c03000303200301503010400e00e0b4010340b8442d0141003c01d912042c150b400020910702440016541107c80c2a06403d40e00050074411256081c0440d131568100140595100b948034000c1130740e280401142210002d1080542100724840000d04d0188144010701c2c601030a000035504100e010901d4501d4640709802144080d48a45070240543c07418000c0b030b500030840c505c020b101c08582140000d403140d2240c14600342094050801208242c002d4000d408261355007086104050605070541e08200301502c00c6003401c0c0f078040380b280400b03007041c02828403800c0c0009040c072402406030300340180c0d20710103e010f84d200d00102c0300000c03600c0d40140c034490010310b01400958441d400c02c545401100c0a02e5200b152080c8104501070058072012001c4000c403e0855195480340c1e1350620841c1422030146040c08543d181000100f900c0c100200c01c084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 579897365 1250 579896115 579896123
    0x60e03031504090b06010e2b02040e160e040819031d031602120f06090d0e0109150f03020c0d02100f050408120403020102040302040507020303061e06040e0a0b100c 72
    0x2a10941c03800340300889094800140c0308240103000912254081e4050144410010304521991685401c8003500683c102c000d00e40042c161904203805e600e06800b80c40d04287d6118041c05d54076040c1081412484be5038403914011041181c0000c00b484410010780304108102c0e540030070081e0101e00003c00070f00c4020b014070a1007003402e00c2540d54880010503625078858000486020081c1a020861060b0070440b5003000b51064440c0d000e00f00005119050054501800514a286c400c0c1409010040074030131341410041d00190400550b0700d40c010300d011440d642e00700f00700c42900014040b0041e22810716010000e1148440c01805c26500044c03801052808440802c50511004810000d803041510050058801032289080c200845140e02d5006032181c0001482d040c4c0d2940480c7c00c0d0b800071a0700c0e00141e00301104000304c3c0d081c0f08442c200701c00300404100790252600000602140203a0041b03020a9609400217142d00c13076564443c40b030102c4010115074410162007002000041e1281c0116 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 579898615 1250 579897365 579897391
    0x40c02011506050c100b040e0a0c14090c030a02032707030302060c0306031c050705010c0503010e100303051b0c13021b030702010e040b0d020901090b011103070c060f020703060e0303 80
    0x41c95407042081d181600804c40140940003440d80c40070300070309004441c841c0d010b035032a90040c8034480d080014004c120312403103460303041500e8022a52480b0500c2c900d503e00034011a0f0411040018050480381d010502503030040c0c403600d07440004d003001c4d08001500c01000b10076041c3c0284020000a0140441c0d21030390803512030303588004d000490381c04151000c03234260b4403040103030301840c00d080c2181c00235851a242040c20040d036602d031a42074641081a017408194008010700c0341903600d140740b40d0f0140d0400e01c454101451607030011301c1480340382d40c41151551825100703000300340140154960024014010041c520b0740741141c000075404000074020319140600052000b0b0001700071741c0d0390070703405031a085000c542120620000d0085440404d5000410200020040c0e40e110645800780400c0080000c03803200003000035051190100400314a94018030412001408101030030098480c14030306518041c1440c1c03020f0b890302c1800e400c003e142c1c0f030510b00581072003100000950301c54607548240c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579899865 1250 579898615 579898619
    0x181515260105040c232803020316050c0a02190807090c1107081009030e0904030c03091a0306300604021801231504171618090302010209040c020115 65
    0x2510200350144001c0d404034101150b40591798603080140168460251902d401e02c0d01c071000d0480c0c0301c00c03c840c540700420303400320074406040d685043d0a503008200e8108075203800c603500241580c810700ca1100903c50203034044080a01002444110010003118003200c02003034480a003a4040e0603802046800245d45800e40f20050000181001c116980c200c0600908849041c1e20b1010b002e017500290244001d20b4182002500c2e11210188224000d0f0f0b03454920100b10715000b001400564000d94401c82d136200b041e0b85060324001140d4000e0011201b0841c0c4200c400c8103003040e0001001c43c0c11a064059801e03184081001c5030861081e4070803501000e540c80800b02028a5110070b00074400304044105100842e071070012523500040380d000300300040c001d41c4407904090039800f83e084018044168000d88003c040704018841c56100c01c2946800407034140103150b0140145c05440212440d1504c0207581031600070342c11103c1e51880540305002d00207103180e0182c040c021200201403001007031080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579901115 1250 579899865 579899867
    0x30207090b0d020d030e30010606020d05040902090a050904230114060108100e0c070b090102040524040b040902120906042f06030a06181515260105040c 67
    0x70005100d43d008003061030510442d1411a012001c030114583c0190a80003001b0301d5422108109510701040000443d180e0030b803110703050030345400340d100806650240b010000385a400c00c05650940b94040320050b19940362400260f1407440b00c0d400280c000515005200511002150301c4212004c030000004403446051102ea08890301104048410b0030300c038021889562050304055040b0842020200c2d61684a40031240004015101c0c1d0f0070001c8005030a40812078586a2944c1c481041402107061500e03210105d035417100001c81100c0012081526038140e080b02d20305850280202d0041c064813181c84540302c0000f5406140203640b05c8066000049455074005410351017268070120324500011514480000b61000075561a01c0360300d0343c4144007641e00c40002842c8101c0d0a031001095161420140d40301060185807025520350900501c980c0d103241c2d0809004c211550300f860198640e10100c402c0329132218200f0301b01d01c0c000000c00004620340b03c10b500103041c2e64040300d08000500e844e981c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579902365 1250 579901115 579901129
    0x90b04171b0607140a0203010e100b010e030a12050408030301150905030d0909020d020f1306030c020d021506060d020703090602070f080a0809180901050720100f0b060403030207090b 80
    0x41d426911403400c103c8280050b0805944140804190040b900503101903400a070a580803494070b6015a480341d0320823052600b1900504400c6007080c00d150300c04040b614003087d120001018050420303400110070480076449035003143c004180d002d0070349032a942c459650307145003243c106004c0000f4503c420045141d160102d490311608030143c5640d40001d241040800182d0880024015031a5007403000c40c0701c0803003050080070306102d26000c1003001820310700c3c050202e440d03501c0d020045600c019400d09038140c0014141c0700c000084040310803141d5854001581c0c0380b00b41080301a00e9400404d000b4101034004910b01d050b174480f40c00f0303150880d0312810614001d01040c4200c01060741305013022004600c5500080c01000e001405c2c950416455038413540e0801802c1c0c0e01c1081580d035800401840d02e90080030309010201c0080091181d10003090f006551b4008e14107000d00d80c503036600d100c51610350603501220001002401c1d0903122541ca05010751550418030442d01400e00340120b299040c0340800c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579903615 1250 579902365 579902413
    0x19080316031e0534030c031806030b0901090605030a030503060f21010506030609071a04030c1715070905100c0b070207180c0c080708040302090a05180a031b03090b0417 74
    0x640003a03401d5085445c01c890796400c0b00000d805026030160b0340c80d8031800240400024050544010500d01c16a0092020281c4164005100d0504c1c08109101c45d80e0003040085205406241c81500c03529000000b4003407030b80c1c40d1206075119846d03040dd07040005d01c40405060b40360141c0c0003080070703036289402c6c9a207410080300c02e21040d4010301414004c4420400e403019200ca04950103d0034151207503905103c2c0341c1c0030780022140d041008666103004030708210100c0c00c02e8502c603901c0c40324104044064409011401414132480c5e03480031050450f80709204184100703070820464516801c0110010751100c0150040003d10705000c110840b6601c510b01031561180311690320401e00d401300391610b0708550402c000c1120042c9007080000301594818101e68020404880c0000f62402c1445224454040f002203120860f0016601c120129400035064820381d0030030318000174518101c3c5021200f0115940228030083c5020402266011403550038280605100040381c0c119040c0400f0620405240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579904865 1250 579903615 579903697
    0x909060103052a0a1d0a060b030f06061606020306040c18030b094602030a060509012910050c03030601140c030c010b19080316031e05 59
    0x85401804400b042c0345881c00c2191100060600e03c050301c00080c0c9040c00703584c0034130b41d0a200021042000c0c0940c503a0590040700301e240070000c00b032504850540038000108407103000150180000c4007915072004880e00241d600055004600d05031506800030340013503861902079498511400c0d8004d010351141010b071100505123041c100d15550314884000d000a00b002d0381405404200222590814040f00361151145000100350948000182111078100d03c0c0011a84035000d030000540c801046520072990401c1002c41e041d40c811a202e4050100c400324180c010201104a140303664403c0c801054540080310074182d20004490211070502036061028403c0d0800c0021890b40d602400202d0104030b405040281001103614030729055801c10fa40103015a51617840c0341c005072501d0550314410920310740901c64194140000d40350b0740d000e9461403001c0040c9a200302e03010305000b17400d04514a500d03655001c03900100600001d0150700b00c1098507040951900380562090128450b02000d4190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579906115 1250 579904865 579904873
    0x10f0f060c02270c0304060c0302040b0706150b0c01061d040515060f060426010c17060f03030a091d061c020117070c05101506120b040911090906010305 67
    0xc1902000300440d0880c4008182c42d0820014001c485803d5601c5440354203e03400c42c0761240340a0902109a4900102001c02c1502c100000c0c003ca6400310180c0741d040380c00c0840000e40b00c855294482c0520015008642084004126103901080540000b800e50318050b8005a42003502c141d12407181805a60060064000548104400c0046004198015001441910b92510840c0420600d60150b00300b9170400d4800740524840003640e000010a034540c0f10003c00c40400610402040381d01d10a492241c40b0200d00080b5a2640e201d1210310111200201178940c2c034805098003400308002c2d403056040041400288400103810941d1642c8282d0b00038040312008c01080c11100c502600741013040381480000c954015003d041000c1d464861507041c1c9800e404031a45003403003864080541d200c40c060a05007140001c664900c0300b4900220350b260301302460080180c00401000d03000c8442d03010f03041450312036404240300040781c980031030780d030b00740c96095003600d50084170394a5034002d010240030387e48 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579907365 1250 579906115 579906137
    0x11060c030619090c050301050306070903050717010f020a030b03060709030804050127090c0e040203010b1204020d050a030507030905180601051602120a02010306170a020103020a0c02030114010f0f06 87
    0x1090030441110714000c03480e1180680d00c62002004130b0707180d4040300f4006a400700050019007404c0060302d8111a250401c004890b28650f91159541120300072494500c030000c0014003010400d401c00b0100041c1c440d019521003080c860010000c2682c00c020750720a200d090045a1200d001d00003020035640c0201b00d191030142420019a102209406000c015102c036240d240c3d03410f2000e5204001034401c1c600c01082401c40c0c100018800400c000c03816105501c1000100700300c4645004884c0520b800d00d45c0d029896560f4000603803d05040100502980606003020041680c00f2004201d140d100e0b4681c1d10003075032180103101c0703001c07180c104800300100040e011484175805000600f440b41000c861850700000e59501003103120341c22282e007030040e90080c40c0e85011581c040c080c1102070403c0398580c81a801c1d80003442c2c5c1c2e80e101807032406030502d0740c0040c17551106c07446840c021107019000780c001e10503100300340d00b080c4045801340b24254029a0148003c102d00c10000b0030001107964545d0b642501070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579908615 1250 579907365 579907369
    0xb060c0319051c0c02060702150f0c0c1c1202090f19081207060e010c020601030f032c0111010501141c0f080304060f060b1b0f0303010b090111060c0306 67
    0x4040d404450040c09014004440e1485015202900366582c031034000c604101c24841c080d2034180091701f40000e54001074031a4a60340050701c1c1103a40b003401106251485c0d283e555100490b1302c0b07800b54040b00e602442d1111008040056031b0707250b0340f80c400c0c4d550800002071500d403003080380140c1c0c2c40300d540040c09041c680c81d0b614000700002c2c404c01d00740c001c15138510764542d0301c207242081c442d40c2c090b040c0c100402c881090001ca48110030050500f0307002030101c80b141f81030080d101c0b01c0c14000100307801c007070030a50b0052610030300416440400060954070303a003008040601c032a640b100901c5001030702c02c0c508882c60001c103024450480b40701d2000711201c50986003c01c044100304440d40c50200008040d03032000b02d951508040800b0f401404016502c0c00c0906154094901501d0401480381c204001000041035510403070384826022405900c10181c60300095040c01c2c504280105144404800810155000002400504402d03291600d030305040c0c3c0082901c1e08003c03106e000e0302036007e0000403028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579909865 1250 579908615 579908647
    0x102070b070b09120409060e0c0c07061409030601090603120306030c09110c0105130308010b03040c060c060e01060f08100b1f09120c05100309020d11040603051c02010b060c03 77
    0x807a8000341510602d48004c0102000c43e002580809800b580740c0c1d078108001e4003017801e403a402c108151140c1e0319000340600e082d955840c41c1d105802c01c010002c0201d01c03003080210141c417540b00f0010203451165a44609940c003800003800240d1300301d905a40a44915802481400b00b1030358042c641c80006450060170400400706191000404001040080c00c40750b428800c0300d00c5040745682141480c0945d0400812080c0b0580080d40100020400d01000c180d11445e0742c01200d150f4900081321060f0b900e4520058030600500340c1c1958240309010070160288040c050a030303041503041b81c0800303a0700b80e140c40c10fa540c1140442e80000003400c9002c240c400e180c1828000c41c005090603030302282e5540c2908001040118240d419010b050800e020a140144110440c600d00b0700d0103020403a6283c0000300701d084040b2005003102c0c0810320441040d02e41d5080f400c01960842c064504420070003122200300c0b690407070b0080040d40380c8003402e4940e140602c2a5200700346002c00950810380001486180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579911115 1250 579909865 579909871
    0x11e0e01090b03090303090d0906020705100512041410090f0213020417010608120901020615030f0a050109020406060f020316030e0904140c04050c0d090606080115060e0102070b070b 80
    0x41150036500828600000b000440c02a42c04030000d41c1e8910301903404a05108040703061800f049040030f01008625400a00c04059520458840280324203050082d100c610840f926002c0740361185003000b0600c00042420450031070030000b59200d1031170341203440c0c00700ca41449008100c0d4041e0307410400507080c80c100003140301e0702207000149855180e404a0324500350b01c40304010b850391039000074058802d0610106a0300003441c5a554200384580300041c1d00e4420003000240c031000303007040c1c00401b0b0340d007002814191502e40c41641c2000d06c1c1814018040e03e8890816800341c1e0400c000003e4540c41110481c00c0c0511b2a030203942041d45e0100d07010042d010a040036010042d00c22080d07480d950fa41000c441c0154452070b51641d0241205034400d05241c2c0403c11244590300d44002c010710340402d2011901504414034002400e1025444d091000b0a1076030081c4001c0d61800b0000c0d200a4500c0c5041e609031a15525441410002c1d400126510b98085c0140d06c0038800c1481001c000446060903d60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579912365 1250 579911115 579911117
    0x15051c0f060b180411061801030510051509150a0f080a0f06181a06040911040b0d09020307081902040e0c150a0e0111030a14070b090a030e011e0e01 65
    0x4a40b114000001e8225494030000c1400f180c601090001300400c0c4039100e00c040c1c1054071241e040c016010440382c0b015480002150506440e8400200c4c81200043c0740e1010700001800030140100034140701d805500002c181d64020387e26a810400807a803c0d40564088004565645c0800c0d900201c04407004000a04491900c0b62a40f00b0440c0c4441180100401703801080420b090f282100e42c02a000d4a0280410007100c0e12006001403c948988040390180e0308c0c03070107000c90340d402c0e01d0b642100d6910599109000030030011801d10303c0150142c101461942c000c8080341d140d80d444190b8203440c0c0743c01c4242d11003418001840c403401410300d6040210071800180c290b9086c0c404280c041039200d1035090070b448550000068844600390001c018900c608020318040d00140c1141c000d04d6500d00c01d0000144c284000032010003904003828045801080e07201d0f007030515904000005580d9040c0d40c250840115a8080c032242c442d505c100ca2091121a03030040d51641e1000001056480d400d541c1c03600c0f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579913615 1250 579912365 579912371
    0x10e0703051c11010516031a0117060d050708010b010320041404110a0305040c06030c091a0c0a05030904050703050c071401062d05032d16060315051c0f06 68
    0xf000202c001e00c1030a01c01c641000ca040850300c92080700800710fa40c0082040d8212060318083e2910303036030000e207455404401d90003112558440c080040d11283c40208003c00d144201d03400425900f1041d00003040d00c01081e02e00f84000c4030000301800342c0400500310b090b02e81109120800440c030000754a00e100c14006040001c840c0119102140e55a200250120100380c907441480100301480e4019402400607240403c0741d580c011900824942c00c034882e848507181d0300011300c1130003004007080340c0001e85c10800325040c0c2035103407414580b60b41140684031700ca24a0400010380d26070190150b18451500c0404980c54000369a0700d640990248600d00e0500c2d643c1c5100106026807003094400003100c0b0031580707026245c071710b43c80042e031944180c104902a41051400741c00003440e8521080020740b00c211a0b02e1442110642540f0b4130b1601c0c0004a1807565080f80003820030f070190310005a0305c0e0101c100d004001e454030305024501004201d101d2070980140034000c042031000c046900d45610400000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579914865 1250 579913615 579913637
    0x4060f05030a02090a0311010e06040503120f160b0412020c0901030204150306330e160e090f0f1302060405060a030f1b081605040509070c1a0603010e0703051c 70
    0x10030000c101541085400a803000c0080071f003583c21080c070004214044803070514290902d0f0200340c5403003009016030003880002c580a02594005000d643e4800702c0c1034420b0344860100d0415208200040e10165190000909401207031880482e130b11660142c09001a80d9907440c5500744402442c0000d070291908500610110000e2a140250f00b40001043c403002d0f860540801c0c0540d1354106403d904161100c040b40421480444024031039011401200210b01504401401c1c0c070f076459581c0c0c4059100d0421030421500d2044480d00301e0061221003460200c507139942e0100c0f8030b04030000c0d601035807045052104200510b404001401c188c0c1c014a00490074445110b202c5080c0e4144d0380c548408200d0410443c0d601a034450b109a500817860040b61120301400350014120b48581d01072640a40b4101c000104581d01481d00380c880c1a81c0312040e0075120182e502e04042c81c2a0648540d40701e542490184942c0c40d01c00600074059907000000740025800c4002001074224048940d501170001100398 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579916115 1250 579914865 579914869
    0x30e1207060e01120b130b1504030f06060e0402030a080c0102040503190b09150a0209010c081201030b09070e0a0e21120601030504050607080414100b130204060f05030a0209 76
    0x200c400102203a49850910804850001d002268000c0410364407604d80304442145da07840400d456042c0b281c007074000030702000394804600342e0001c1320600d4245500c002800010411585000203080d4000e04041040e2502c5403400f2940e480161400b0358542e110095000200e02c14000422040b034115000500c2e003552240860f0030300540058050800490b4900e880c180890040300c20782c4200c00c038001d0085410001d551034600c06000d4501d076105640400c50300c980742d02400528400031303000200d842d00c510400d95007604098003400115800c18000010506080c0c0005445040d5081c25410354655910a074245004003101300c500304003407046003880d403034408546034002e0004070554002c5943d0041c04401541c61403028215070304152401003000301140000c2031154004502d840d014640e0740b200d04000c0080490004c50741c209000301415942190100d900c146202c400035aa420440d5081d0808003040f80510701c544408030301181d10b05c010300c502c500000c683c00000031000608240705000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579917365 1250 579916115 579916123
    0xb0a0c1101111b010203060604060c0507120f060c080c070209100f0f0f0b090604030809010c02061b100e03030708090f0109080904151404090312180b070801080a030e12 74
    0x40c4101c0040c40002c500200115400c3d41102001122000754918102100420780600c290721608007081062400c6104010003030104000034801030708868100055411305030f4800d024424101c903040d02d800d9500b50b00070301500c001ca02c42d40f491140f450401405401780305103800010700e58410305d01c0c00030000c203d038207000d5030b09070190058500040324030741001004051030f0f082e90802d07200c5400500c0b000b005584e401e0100d406503030b807101100391038800c4400107a80c1c2500e8410300035031150340071441044541484400c1e000e002032404c2191418803000510a040b9040344503421404d030410000511414007801c209604500c420080321401035075125528210303403209008843c030712000500d2600c2440c260181c0f000400da40541085410b10300000701003142c0e141da0720303913000d00e4540818a00b41401810402240c50340b5000521079000a4080c01c0210051040120360f501410804100e0b03480c490310140e4142c0300303000c3c000d1188110395141510711884103010103074882c08110030b41c4411b03e4180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579918615 1250 579917365 579917381
    0x5030315030307060c0809190507052e030f0606030204052b06090c03020907080609070f1107030f050d140403081804020c0706080a090b13110a0b03040c0509040b0a0c1101 75
    0x3586e41d20311402c00c070089501708001d5540400f0840d200140318008110b000c180c4108480003268280c0180b4000c40c0c10a16144025240c80f654481000c042080f054044c0c01c10310010461304001c0280c0c3c2e8403503074141c08170b00450080e250001101c1d06401480d510441c1100950600c46407036101c5001c042d43c605082e25013030744040f500c0040c021020800c6080c200c0c81e1641003001400c02c81864074181c0003240900b00f00410072000c2003240c4904120b1140200906181e034a0780b42d040d40c003040d4890410807079401b2211030460f0517102d0049079500c5c2a20692208180404094402d89082c0c070f152141c01058000410700e2064400c0b03c1031032407599941d40b000340011b00400c1e0160020031300e0501c01805c4440010410b80015080c030b0706243c0010006505181c0c003807450b500190700440ca034108942a15041040d09400000080303004ca20002c0e0300300a0340c41644140c4198482d291100140701c90b092080d60000d1841100340041816007145400900800b01c0728604200c4044610325401c4c2912021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579919865 1250 579918615 579918617
    0x21030507080d140c0901020a1b1701090510021c0c02070f09050f09061909050c09070206181c0503180d030f0b09060d240609060503100905030315030307060c 69
    0x355400720f512070f004110542c0d02610f04080642003200d540d002035100d0400d03080040603100c0704001d91026138441c05400c0060521080c0d1002d01c000c42d020303464024081e444003510144180344030000b9244d40741c004c07104845008510054400c2c13010251002602c484541c140950117450000b003203c43d240040c580051011175404501ca042902d070304211440c0181c1342a490341c009504006100740003810610700081102e50014a442050604600b07000072010002d03400314901d400c2c440d0300d9900061980c000c611290400705107040d4014a180c1e108a01c0d0b081d0701d040003c0070045030340a40200081c540c4044000050b6040440380d9400794106030700c07080c0310808240c1d02c11048800c8110b0380704034080f6030b2003503c40c1d030028102100004e2a01c0d0921000500c01401d095200241c59207501030b00300240c40353f080034003001c0c0e200c000c0d42001d4001406418024454041c40240f2083d9600500441c180c001c40036502c0c60700e5521407103954a0000c440b554251108001c80000505c00748100341d041507a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579921115 1250 579919865 579919871
    0x1020a08180d062a05030c07080c0613030f0c0309150e0a0e010f17150702030c010f1a090f06120304030506090604030809070e0f06042a090b0421030507080d 69
    0xc0721005440c1ca51a05a42e070102008524130300c2c0041e0848104c80d040200380a0b02c60311510b55140501492144e0342c0c0e09500d60180c80240042d110740f01045040c1c1750301c80d48440c504114020400c0b00d144100800240020310200310410070342d01c8590300500c0340099454040e481c011281c01150061405030b0003e84040b03603003801000812001c00a04015081a50440c40c0c40c1d545a01c000b5902e0b68940c83e80402d0000d40404114002d000300115181c1c040c0c018000d001030300307034140c07104000c0107807a0070084001d40c28000200c031890300085003813045802c0120341c69252138020030701031185009d400d803421a100030800400411401c01115200d212070f03000414881c40c05e854000e0000c00c0c050264105035104180511250504000250380449203403d10041c9a44040014005c0e0180c100002403805884a10314040c00e8504040620000315031201c0030f074a50f90300d01d04600d0740f0541c82003102d080781c003c0f1070040504401546aa400e40a03250281c05c1c030802d900c8241d0603034426920075035502d503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579922365 1250 579921115 579921131
    0x70609021230070210090302190501021c1b230f1c0207090209040f09110108100f032303041205100605010f0806030f07090b0a090b01020a08180d06 65
    0xd0542c0781040c000300c40b501004010a80b11512440303500880e03000a2143c12400c0801180600c00c43c00c440c001c41c4c00070103082031400700d100721910400d52405a1801401081040180e940d20125601040001555034002e030008007000c00304031b5903100ca4120794a205c075549a10101d03c200c600da0281100d10390103000c0358038818510925041401e140b002d00004015111000e80740c012880c4400c5544525002d80d6595407000040d00901d040c03070b0100c0c8814070300f0040700e081c081101c100005000303003a2161141500d5207140e143e0340f03401030300c501030849444600070302c0040e8503010030741b21401010568020541700c0b203580600315007041e0007034911041d1241c62082440010040d4000c151401c000420100f030814000030240411800c22409114840020554649040140b50205140301095802598490020707501400c600c00c15548910002d2502144c40c1c9482d2040b50301a40050b0024000030380c1c583d0700c2100e1900801d04da600c00040e034007000c42d031580301d02007014100341c031551000a0440d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579923615 1250 579922365 579922393
    0xf1c050d030c20071e0902180f0a050915041508060603120c0706140903010603031d0406082e060f050909030a0828230c030403140706090212 62
    0x409481c048088403020f6110709080031001140e0142500d15041019109285040030b83c80741d041240d102c00011440015024a0265140c0c1085540d035000c513125601d05061401300900d400c124016268061500d5000c2062982105c0c009021960702520108070050240b010b2200101a6030094407190000410001c16145c06c2c002c80d5040310f03c07160490b0038000b501d81c2d642e0b070760700e0140640018000c00d40d54004075140014151420360100500038400070b82c0341c1c43e00410f1000c018900e902480c2c1c12045010146c40c0c240204020b0704c005200414032440d20001d8103040b280440c01e101c544003c0c08446104501143c01194090b0043e000c140c4091481e0809200b0444030041903c18039400a02034000410750298a030f40d0484500c4030109001c1100c080161004004580307103000303030340c40e042d400881040d180401022401d0301070400a429503401681d0801c1c6d04c0116002000200001c80001a003040e05010740312030350040c907000542268507404039000c00c6142c0404583c9030700404061000d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579924865 1250 579923615 579923627
    0x3180615080f030a08070e0a050904110406090209060306060d0209030703080a0f030932031305030c060c0d18030f150b01090501090501141909060e0f0f1c050d030c 72
    0x42c400b44025490f1410100f03004084080c040d00080c200407802810060030303600c0c9031141c000303401e0041c02025242060b10703000f056102844020760080d4200359002650000520031380d040d031000504040d2540c3e551000f04403483c5e0000c05107422113a0b0030300894489803001c0241c00302031071241d0070031a5240b5150b2405030035542000900d80425092103280340c0014941482050016590014407044800d0042c4c0011440004025441584804103000010140466141c400c4640c00e500380c0c0e41130351402c002d0012a03c0307261001c41c030a600522000200318419500e1041c0340e10b049425003002030712952103403101881084180e81181c043d03020780030a04e481c2e00c5020b0110300e090801c0180301e45040300180160582e40706450600c42032560010f1480010400c1319104500c140c0e0800201c0d00103480030b4102001801540c0004020b207a8000d0345007018860030b201c01800401c921000480901002000c8142d41e0000b90803c014085001c0065010042080411100c0d05c010034090304440004200d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579926115 1250 579924865 579924883
    0x16060b21031c110d05090a200f10020601170a060c03020d0b120c040b0a0f0f181119170103141603020d0303090c0e010e1e06010905010318061508 64
    0x243c0c90091902d0a458009088400106a254000c10079640e1001024248100b0020181c034540d01a1100d8580c07058504110109030070450380030f40711850450500030524160038524000d6801030005102040c07024204280e220802d8080341c03000042540c87c2c00580748013080d00300100b5004250f509500d074450146184040c4160303100000c048040a03105d544000b20403410380503a6407a44e80c68a95211040c18001a000c034080680c1d465540e01c002e0664641e4912900101c618040395000401005004005100491030902070801510304420800d01103014030300010b100d00c00c0030a20002640101d0907000394045c1a0384c0c01c00b0100d00c00824103080b24050240e5600041050038801a50f4803a40c9802e5681c061400040c80003141c03074030043c01d0303140f078114107280d8028070b0000841c10710910800b841121807100348901c05900041c80c403030020703065030801d0102b10107100030b1100f035100344d100009400038200400c09015482e10b4500440c1c4910341b42558801102a050080040404c20101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579927365 1250 579926115 579926167
    0x3250807081c030b0108060f0a090e0a060c0809120f0d1d07080c010504180624020d0c0807030f020712140708070b04140a0b2d16060b2103 61
    0x22552104d140020200f00c4000c100754070440003140e0010850710740450780c90141050a00c00c2201200c11404243d5035513000c1011229503050654403080d2921450303040740030f852101c000306040e20102c0c4e240c10568010444420252a042c800180090f03010300842074469264194403c02c2e0111052003801e04403140c20000e0740d0707441003c02604691740035007118100c1d900e51000a510182d8401050040d14080c1e008001381e88020000c03500d42c402c20210424110855000c5030300b1441380c40c8060714a14803010018142d82400e00c04c41000c6409a803144031620740702c2c13040d11407075030311a0344100f00b00d8501b413800c0e10004040680c040172030710204200b50190031140300030136070ba5240ca01203010034480d80c000c031a01000381e0b45100321152240a070340d078090030300c0001d01a19156840e8980c040c90040136040e1000c1d9480240000452012100f02da00a4450506c810140b01c04d5440d007202074030007050712076005603000c3c0c000d40c1e152040c1082c04e243c60602e00007440c0e9410b035001c40d003c0000d04000c2c03500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579928615 1250 579927365 579927371
    0x2040f09230d0e06041d250806060c010b04060b0c1209151602030304090902130b0616030c050d0207030b010608130312090b040b07110102070203250807081c03 70
    0x1c400740c60000305040010264508460301160182c0442c1d51400b890380620900b1442000d01081c1051440040c1d1250030105070343c13010203440c07019208180d64084a002c000c00c01560100b042d5082c900001c1c900e8030b04480010940c40400c0002c1000c4030710b02c0e88200d000712004142000001000d0111070b41c0840e1a4142e0b81c1030901010014540920601210301c00d03440c006154071024524004154000d130b0000d043c1ca4a5a50703480300907001d046031450481c40740310b0070141c0d050040c6480c4501c1704034143c00f811345401c01148410b01e1000c1c0321100e0056043c80f4288400200040040090031005111076001c0c10340a0310b50315101028000607044103041c002c1030800c015011005403100d50b0050b8051820b1403402410310072800c0104000341d409094165940c08100070f100c030313107410240199402e54561304d0058400c04802d080f07020340320000b50f2640020f201181d800502d0074619074003a10160079001155a290842d40c82c10b41180c0c0300c044c11b43c020704020348041d15050101d1010200606040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579929865 1250 579928615 579928673
    0xa030e070e061507210c050708030307090816051302040306020d1505011b03031a19032001090504020d020f0304060903030507050c031c020c070305161706010b03070c02040f09 77
    0x107104102410f41e2164082c080f0028170f14010f51260145c148101d0300101624080c64440001907100da00449000780401e040350000100070000007005400340200c541e01041c0c446c189001c0006e500e803200d081c581c40540a12012011901ca84000d0100c00c40c0c24100042400015400e41040c4100c2c1d8009030621061205401e04c410b0702c034032030340c038480d5151800080402c010089025061885119a0f800811304061003414000313205400c020f0b240190f000d41c10400d81804004812512403000c41d0005030000010451420980c01804032000140d05c09820502020a040215001103505a072100e48448501c0e0600d40c2500c211500100c040c0b500b80e04c0c194a41103808d50340e2103401c49404020704840d070052503201081d4166450007540006458450740e4030304041ea50b8200e5240b00859050700c0b540300160b1901008d00c065501c1c2342102c0a130245038607200c04000b141d00002c03e00b5047c050f209403000011303550703031140300714a890301240010100310504240c5899403528801032004100c002203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579931115 1250 579929865 579929873
    0x902040602060103151d0307050601080105101a070219151d060702030f0618060f1b070f0803131217010504180b040c1e03020112020a030e070e061507 66
    0x340b81d0540b03400c07440003010103100340403010041110101d00f4443c9150810004028140480202099402282100d401e66207a00740e2364201d074000d072103582c0138080303461042000c514404c0405a42c1000d091601c0e080c82003980106001c1044c1c05603641003005512000d10007d0020078101c407003068685803d20180342c003101780c6036030505000880c1c1e1041d000461544210b40e8200001761000b4241000c4e2159401c1c000240041805007205090352402043e0014030b060030301c00003c1e03200346205d0511204200351780c001e000150f4040709040c0c80708114070415078041144c001c0114001c0014804071004c1040608100e00b800300c0d401c010004000c0c0446520515081c41202ca5040d100c086800103010201d82001e0300fd0302e23051040040035502c201040100b8400310400000c21a140240701010b00d40031720907400a800100e0100a0214104004003144a40310b58050115030445040015a108050b00031301c0c80e1500c254000d0300c91145088c10080b03c2d0411295105520091000003400c2c5011966 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579932365 1250 579931115 579931123
    0x1306060c020f06070c03031812050606010c051002041404050a02030f040210030f0905030a200a0813180902010e0a0b09060c1204080705010905180601030f0b1512010902040602 77
    0xa0082e00c1428200d1030b00c1655a541001c46203603680c042d800400c034654034035020b0480542d0300b95100d40390341b0801c1c0006400400d07614811025a2101c007401003960348200544418420041c19691842403020325004201c0c84d00c000c01c0500114081c00d01c2c0030304100c0400c4141c07400144002401750040c41403004155000324a0782d0429812180e080340c281c02c50004a00904c4260350b04240681840144404c1c0700011008107503220141e6107c0b50015100380c8040d40b804059041008682d00140400c1c5c040f42501d0042c190b9120a200100205a954114400005850f142007c205c60303552800d40111360304014103030946101039500300d00085c40d10440c02c40300d00074050361f1070098900042c0c1040050040c00303064041440e0084032034550392907825469980606019403404100d0802000c81d441c0f030041044002e00c40d0b54003003d90309944000c011005840202c408040c0341c0c3e1580c6031051140d484000f4020861010840c0719250081d407591000180010f034411842a44100800e1020640c045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579933615 1250 579932365 579932387
    0xc05070b030916121202010b04060e0105090f0f0403030b01021507030f1512020103151706090601080a0c1203170106020f060c04083403120305091b28060806130606 72
    0x3101c165403811782c3c00042e409041584416907010b4606100410501c0c00c201c001c505a41003684c08103038a94404801c650381041c140c072001c40311041c080000d800240700750440489000188144c9010304002e2016003140d0030141d490f0804261a0303440b8040005840c480d609030940079408003640c0c10f14005000e00700301005540603040507114030f001811100340500320801012511428001403440140d5241c840c030040d280c1c0151030150a00000e408200050305440c02c036086041000b003240b805403a110a02d40642e0200c05000080d60700e9200b03030301c8580441c0d0091513140c01800600c40040d0002c1d041c1503000303050006c010000d010500038000e0008a01416403104807000e4000303040503111031400c0c82190802411913002050100400c800c10f0b500d80c1d020782e503549061040d521b2303034480d0584074034040008a03041c10201841c405c052501411200510001e5292650000442d0000c02505030b980c2c0c10120101c0c1400c02449034a0809611156000c031040d902000864103008000345090041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579934865 1250 579933615 579933623
    0x100302010f11010b0d050c090903030c030a0906091401020315011121190309061d0604060b040e0609010606020c10020714010314040b0109061203080a0203070c05070b03091612 77
    0x95442c005880409503c604070380600188801002d480a15280d60703a48041d010003401004807202103004214004282d03402910250070b00350955443c0000c0a0041004041c00c0e580c541c2c4413460140803800244014280304000d900250380c07850607010004051040d44150390401c40c5111860b00380c44004a005003049035610428901403410000c116018020b244501c00340e9082d14003103200494041e480060300c9449004140000c100800502d00035060014100a460700035400040000d0300a070700031210160000c100080b5080040021803422100b154580c80b680e551b800c043c003000341c041140e408112412103422401c494100c80094a8274020f1048200c820000c10740b41e18182c1c00794202c0030286642011008041c41d29090840c4060380c01e100ba0030a55140080209140038030034040c5016a802d61910a015181c03486501d00950000f0020303010000200380880000b042485400010a24001301684904008180038103056107807202e040032280300c01080000c1a202002152100c2e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579936115 1250 579934865 579934877
    0x10f150507150e0303010b0c0c0405090d030b1309150609090201050406080714030423011a0d0c05030102030c1209070509131502040609170a0804050909070b040605030906100302010f 80
    0x325281070b003e40029003042c082c0340008030020a942c00c0c3e0001a000100c1034000f03d485029100c4203002c100ca2080e1400045a04610040702c1e034140240c101070000710f805004e080d134600b2860b01c23200885110103c12110780103140c8000c21111068019103001e07195411040040c0a17080e070000e03000388258814030040c4100000003030328440c01441d00104181c00391031003582c0c920701460300b4007036070302c4900c6100007411802100d030401d25014461012032003402880411011624401c202c4190390380340040f503490300520000b0403161028001746000e1000c054400341c40301c80c00d0080a00070b00004140004a03031002200f00030301e030748050307090390010840012003040c00881c3c03d1081640001c0301c2c045407094000103000031115484000402214460b03201c285084e0400501076840b843e8000c400780a82809000c18004d518000b035945410000050859a419954545400403504241e0141020950110030404058420301c9003580c00102c40210940c42e900390790002e090810380b55250030800c51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579937365 1250 579936115 579936143
    0x5190e09150708060414010501051b100c1107140a0501050304020402090406081e0615040b0a1703030a0e0d02070e0601110f030c120a0801230405040308010f150507 72
    0x28140105801032004458400c0e2078541904098083e40c0d007503a40354022480c220348003616070451100c0a06a41c01659403602d13250300c490b040c9604401d80040e140040c00341414a4802984034814054090000d8850f01d80b00400280300500706aa65484581e181000402940266403504c030410256002401d055859443da400403030004c0c042d10401a070068944500440c050500103041000354207068640c42c1c5007c1004d000507120b40d029192030190100e01d084500051405821040700034001400d050741841c1d8404504c0c648071480804410740d50000018019192100e01400586ca220200102400124500d0007552003aa91041c10a40403070708011464980c410150b0056040e940c4c801c46d48240032a40f40340380c490f4070640c00c1110300c2c031402800898811010041d41c0351085143c8a0050980c40e1600100310080010200c1404600800350482c2e00e5541d4400c0d14040c5000e41c0e44c194a541c10111401c216400382d4105103c044824208541035030b031300030301b01c030440c6a1004c2e800354541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579938615 1250 579937365 579937381
    0x5010c0c050c0d031209201005120402030a020a090606090b0906030601032a0306080c0f031e0106090e0604020301110c0a080f070638010c060e0c131505190e 69
    0x400345241100c203003401c0c0940301c6c00340403a420740c0201444016408404801c4c01c90100008509198684408a041031000201c00c00d0000c084a91007030014040d10407000c43e40e03000400110680c3c00fd00001543c2d49801d2041941c48031804c000f0700140120545041d51880020394140402030002d410140c45400c003250056041540e55500611058140300c9040c0428001d0042c0c1818005c8645030720491035441158a040d04806c1011200640a00540c0130040c20fa500c500044034140344c1c44ad0340300d607000101d83c095842050443c003845400761500382043d10400d400e455044115400400090004c00f038252004181903404540c40a0840e50b1200c641c0c01546450280c0032000d00800d00e0410809a82c0842d0603a03007100b400c5081140340480d404131a00541424035001850002e01141d40344400204c0c0c5038020b4464039144012903002c903144100107a00f03411442800c1c0301d41500c40114000130144889040301a0800f181c0c0b03400150103040c180710840c10b4a100d5900001d8000003c039400c0c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579939865 1250 579938615 579938627
    0x702120d05060d1407030303050a02070c030308090f030d0b03100515040c02070e1f0f210201021518070e011a070201090e070804120804020d06150803120405010c0c050c0d03 76
    0xb060303008840c0441903041c4e80d40c0c40d1329044944000c0c0d01007401c0c00001160041b5510881d52881d50090a0302c2c207550940d01c0403038200744018980c8102e8828512035135042c00040020302280c1980400103d040b036180e20034141050161410340c20914200002c0c09410504168650802c030000d03500015000501c1008914041956100d424048014001e000341207080030303c00f60042400860820340c5540d50080c00307241a2051180c581410900c500495482d8414000354254038014030440f14000c80064154000d24000c2c2d80682603804041004078030514103101d500c004100068500030f180d8982000100d841c0c07803100c042e00c1440c3c0001450402c580c0501d055002030f0610340c0404505242c8604017521514083d00d0a4034143c2c54807020380c003840d00c10541c481c40f0b0765020740200c3c0c9c03a055913a540005070114146113503144422400205415804001400115082004080b001c0c206820618210b070080643d600030001e4203071880c00880c50000c0c00d0301c1034910076070b40403800c0091414200c0303031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579941115 1250 579939865 579939889
    0x1205090d060605040506060f041e081504060513020d02090603010e0f06010f0f03031d210109060e0606060a0c061b031a091003140703050607090e0702120d0506 70
    0x44000c5031004401802140d90110b815a5800e03078081090b911141c041001c940200190b010f041c00d0100f109100d01c28040034088101c003030742d246210307296842d068214108200000101d042c00e41c007038200420301010b401555002a4100e0b4021701070030240e004030380001d06601010b401448100007282164509520031092071850030241c980b00000a001141c580a0030b00c1020f42641016001040100040c00c52100f2650700d5102d5030b14900c64584c600c00480d81401040394812400d152440ca45034a041d00c502004030000c00000380c003140c5140c00c1c000c42d60305a009844a83c091800c100151f2910011649141458141802c140b8070520b424005030400c0020702600030030f000c4040c4041074058020040304240131080c024284c3c1c459040c8030003c001213444040304a4003003802c002191101c82031003144c2207035809035011076032039841c2c0c9490b10500361801d40005405500800c0700750040089913800070500d1000d00510000c8061454007801003403400c451403940c44002c43c500c0e513078130b100c0d03e48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579942365 1250 579941115 579941119
    0x1050315060f06030711070f060816090302060a0203070b0f0402030a0f1e080301090e01050c0d0905010207050d20060f0a0c0c17030703140c040905040201090e0c040f05040b010c120509 81
    0xa030b40c0c45c00720340c020880c02c1e58800c08070b024071801130f002c41d007181102c5000081d502c0d0707a40c80d050a03549054100e242026680c80306c0060161403c130100240e280e0000a040c1c0310025001550f1302c100c1c52a046500380300040c04c031102d11141000340300059902040b8040003039004441c0a6900c806405c3c590002001000790700c02e04e05240d4803440402032003201460403a9420101081500c00350003007142070b544201e4a559001d9020080706c1c0031441e00340d02141d48170380510001400d00e0b04999a091800e429281042d010036244c120040c0b0041c00c1d031000c12207582411014002c0360130300750b01c40c00c3c6001d0090014100d80b901c0e01c0c08101d003540300c1d001400501c0d4104060328a090b11102601b0a9030740140c522074002424100f03c0c0e1980d10100d0000340c040e010360340d0002d240c240341c46411070081c00064012030411a0303030203000a500885a107814000d000b007007411039895191003200c400ca030006078030141c05182001c0c0e0441c06a0782120181e1101c03500408112041014183e0032580e522031142419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579943615 1250 579942365 579942367
    0x31c091121070602010f1a0f01050309150907050a05010f02031c0f020d0e0c040c02060f09070b0a020102040f09050c1e0c0d080a050f01080a11010903080703050a080f01050315060f06 80
    0x18103d80d054000114201d03a0100030400c96000241c0c8108400041c265290405210340708000c1e954451401158810340503070a4602130440d03000209c0c102501902c00301807950199070f062010703141c00071148004107400d00380200d42c01c90000b80692a030050b035490f5580a944c0c9038000c510030340143c00000002100d06421961968054a030500410a07621840c1c0746101c0c1024454403414640304421007200c0d660002d00c140e07a100b108080000c90003c1c5651004e0107060000511002c007013010704081101358002580741c90400441020760b015a83c405100c1c03d05000c144406855410210341c3c00d1b031190650040c1c4d45c200301080d2145442659100e03c6181b01d2124042403441e8844c00c0306000b600301500911140c2c844e03100010b2060400e0043ca240b07078001c0750503240080c1c0c84164101e01c603403043c101140160358030386510385140c2001d1015800b160740018207100c1d499100c10a00d51150484120704860350500b000700e0703500c0d0035400c0f90112036881d40001c1601955040310303c21822000a15031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579944865 1250 579943615 579943619
    0x3090d0c030c0b010b0a1706031906060e090604030f0201020a0e010302210a0f2019140a09030b071107090e011404080405011e050a14070f05031c09112107 68
    0x2030200e540300c1c1c812000018507c0a9602c1c00d03904200300b10b4003a850040062042c6003100440d11140341403007004036a03490b51041c0006980390050060341c40f4442d00c6016103030b50b1410b402e0107010511302002c84001c6910401c0950744064110810421204084c42d0060f1075540b011032581c9a00420220702c030710300300c10758204600c0c0d890700d030021340c552400900b040c4061712070810030f5071000b00d02d1003032490103010034040d0b444010f00102c0742c5500d61406141c00403001c0044030484500358041e102d00790024003101018000c0c84000d5150a410000e24503000c03502070000003400d0780380c441601411540a4880c0c1c048010f2240075000000c20200a010780a580c9c2001d15162505610500c01c407404140d5107015a0b000a03030f4a00010015800c6464062801c800b0a000b20f4080c40a5500185a14000d21022001c107041800400e11144600015a44c600d009424141c01d220a02e2000001c0f13814600d40500048101301c0340100102d0a5030b100748080c1e101c442e407040c0d600c012003076041035109003c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579946115 1250 579944865 579944879
    0x606021b0916122406050304050c040506060403060c020c0117040215030901020d1b021507140702062206031b0c1101090305100f0b040204030203030910050f0a08040209070503090d0c030c0b01 84
    0x2c610341c144030340e405880750217a90b82010340349404202c5010348190000b440c050340a09081d00503c1d4803950042c0054503040c0ca03507580604552940c49500d00584c1320036a0006556009021400300f2040580006101c0c070341940012011b0390041c8044452040100200340307690070035015a43d441d518460705010701080c00f50084600c40084510000510441c0c44000d0300040120714180500e406913101c6000882c0b004044150364010101283c115100b08007254150008010b0100c04801c2c00c107484848a29205008007968042c50300262000e01c844a00d801d0150401c0905002c598440c0d6003c01c0c0b61303130840040e5150b03d4103a101614501401c416814088a0359100400c81207032020100710464042080c4012030146d400002c0d0140c0c02084001001c1c60709401e8440300c04914a03200c6d10b0642c60120602a60f0003850400022480d00d0060000b14034181c00601e501581c07520304030f4154a802c5881580e41c0c0b01508895042c45208450502410720418282d0865908810319004c01c2d6980c0103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579947365 1250 579946115 579946151
    0x60911192a12110a06020a02100906050a0b01050f160f0f050a140a020a1404320a2c030405040203010b12070c080f1605010f0606021b091612 62
    0xa000c5404442c0c0303072100780c2c986000c2c001c941c4650035031800070401d650440c0c3e103041c001d5100901c003c041d03102c0c002d8803c180d00d5503806000d00f01842042c01050500b440d1401301c054031049e141803414050b00f400700c104440b6254040d5000c00301d0741a850101107149041101c0c03402103902007d003e59003003074040c03014080c00140340b450f50b5102e802a24400124890007603260050340b00000e6100c6040c9008000d030541075588030414440080002400e09100401d56449068980c40380c44003c050303d0800b544100b000003201d5000c2d400c5c8606110b400801010540352504c0080d0f4070160883c049140c200c130800401c00d580c0a024040d1085541e56181e801c03001031a00440800d40603800240c001440e0a44180010030702254000115410071b89a6003c65856030010b144550311504040410800301c3c0f02401f500060f00120f4900140f02c82c10800001d00f08202e204801080b01c3d2000c0c400003a41c2c07541c101d030a80c0828050144002d40c103e2040445030b51003040c41010199003025241604601150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579948615 1250 579947365 579947447
    0x30624031212010603140c0309010f0504051e010b090a1d0303130c080a02180c090d060c14040b0d0b040209030303090601061b1a0a0b031203070306091119 68
    0x6082034460380c4e14003080b402e564021181c0d003804030344036002c1048001107401868111000e10004a2280c84841d0b4480455000302c80a03a5140d11604542000c6001d01621845910850380284074500d01d402c0401c0c41c280d0080c1c20b40c108140e80355010000c09654055018003503100c00107480c1e403402c00039084041800141d10030b80c0c03070211743c0a000803030000008140a5850b07000d810010903810440941d002c5840007880d12121450401540c1110381e1840f45a05460380b04440008a206041c0340c010100c40e80c8007901c0b601040d0410050007000d80c00401e841c040341e41c3e0800400c002d80c00d000881d001c0d0046682d40b0b070f007500c4088203005031a400416401d05070350003a50b8507401f408140008056110842c880586484200710450b1100d000c5401860782c480d1003600c000c50030a0203113021038500841000c004010070404400d1180e000e6150140342c00801150000b4440000c105400032250b04c84c190060204210b4615000b500034051544542004070400640d164880c907806000342540708c1c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579949865 1250 579948615 579948637
    0x70b042108130b1b0a0503090114040302070308090a0e0103080d0c02010506011b0c1d0108010b0d080d09111309020117090712170f0c0f010b0306240312 67
    0x569030034154148200e41551040b4140203120040b00410b4942c0d80c03c54602501d24401c00821964400602c00c001c0d00806080c917081ea15581d8a03d40007810314219940d17484034135000350301201400302091340001d848081c1ca4200803007541e245607901c000b81c1c04085541c010580303074440030000010b0002e07510180000c0c40446405126858105c20220b01303c4804485190200d005005030303000c0151600743c9a400d452280038080a0503480f00f403000c15890f428401c0742148840344005110f203400078011814001d006840c42c200618403655003e1036801030540c249009980c51959500784103a41c10b2113683e0b41c602806004992210881c1d0341c01070030285c4016800300b2000c1c290074844003131a01d0800d2259601c00040c040792070503c42c0001d003030b4030461030070340b26092031088200d040c207101c00090401d031202e07030301c290798640103505a0b03414205150f40804c0d259140040100c050b440100f03120f6031024408012514010b0f1607400f03000e0a0308600b988640503c00c96076011345030311003900208207880c12 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579951115 1250 579949865 579949913
    0x605010210060b1c090501021201081203070c03031802220b060403020303040614120708101d0a0b0a09060b032502030403020616050a050a1b050303160503070b04 71
    0x420803254007650500c3c800c8400700700c400c200c0354595080e00350440d140d9508180020032105440e44400342680c2180500c0c140949503000100400b400412008600c0b0401c1c0c01c03458203501d0300c01000380c003184c410344020b010f03d0385540851143e405070340d400c4220740d6401407810681612020410300e403031040c280a14101458500840410316288090700d049aa000f00158941381c1090811140c04408038140c03050b206090102c0a4900d10720680603202380f0700d960321000149000d0005149225035688004204001e0b0010200741025590303035150700c07440303218001c1030621051011500005180e4008034034940b4080703001c100b010181c402503003e0405078100c00d0070000741004010f20f850014100c0009a40308000070401402c042001d490846210f20120701e918000c0d8942c40d04000050b80c00b200d50b030308070000e2241000b16154010f0303a40d0700100010000c0d181040c0119550b0f12642c003082200340130001e15402004010422115042d600480c9a00f0078105450704400802010b1034581c0c19400e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579952365 1250 579951115 579951133
    0x6250203070f0609030e1e0a050d1a180304060e0405090c0303030411040902130507120b10050f040b0f040f0602010203060a060804020307050913020307050904021005030702011e06050102 82
    0x440001070312015a0812954001142c00c1e80d90b0f07800070015103404070305001c1c0b07000c0040059507030445020f200c19600b80ca030910085141d4200811410140c00c41841910380344690030219030503044103200031130f2103400700c41591a070b11002e002c606041d58102985100010f40410b0039036002e06007445d030701016281404183c41d03c40615458206021042e0f070168028030010300882c0303180340c01c000041800f600025100401e0b40205405410310031809840320380380c1050200f1030307074007050004d150620300504100003204400000e410381e0003940c071802000710203d00e94244004000c2250f004041405465035074005404109600c0d812500c25680019001c80c400034205006001b02c0e44071305001800e004005050410950f0554800761059030075108a450101d0300c2c2d140c2d891ea00303014203ea002c2d84003842c0080c0c41018942411074110340e008981d03040500c40187c5400c0c0c25800640114108a5200e43e11800c080b030040420200410326882c041805441020460b880b00c002e403102a0700b074803c03030f031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579953615 1250 579952365 579952367
    0xa0308010b07020d06021809010b07050d050f040b07030e0915030714120d0f021207050c060a0e0405070305060f06090f0103020a112e02120c09010905060f0d0b01110607051b0625 78
    0x102038444064000d0308a0080c10302413610030b40081040c0350704683f04604098441c1c00300289904100000c5003c00e16075250742c100e516059550319400700d5600c1030b80d044070000e030300403a80b44c403882d00c505518103540510f070841542d0703a01228a4003800c44401c50f403000c12501d400170406a083c41c1d5520160040f040d881098500749000c039981c00d03400400030041e042d0164140211a8004500b4074204010080710010680e40ca024150090301c00ba94003060600340041008411449131045e00e04c60f030300030400e1600e6503d074070400c117411890034280182c0b00c5250450960b8240e41400841883e401080961029040070316002182103c4c100c890484494080110000301c2c0b086901400c8410710401c00030300a40310210042c0b05414062400e905011b0b03a42010800c20341101c103401d07070115404a0040714051081c03040000d03c00c400d10307051101c0c40300d904404d03495020180c0350134200a00010031010301d05000d1140c2d03407004900b008a03026840c041c02c0c4081400d000c802400e90245808010030700742 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579954865 1250 579953615 579953617
    0x606100f020a1e0203030a020d031811060a05040b0c0106090b01050a0e0f01090f08010618110706051012060902040b1e0108090f0303010b0406110a0308010b07020d06021809010b 78
    0x4103040d50014450150181c5500c14440c812500599100041036088001620188060031a00c1180d0300203003200401920090142e52910791408610b8001d0103044000c06d031911000b040c40301d819074400d641c804000c0b03000c49551003580c104d400008400180d5120140d41540107508988002034204002001c1d0401100e50b031188400900018841440d125014030f001e054140300001c05041c4481915502c09905440079000c0e030007100141d64891081100ca032603115008043d10009000b0810a640c1025185440c0180316011b440c250b07440e00001c000a04040c500c502900f5803d4203600441001e00d0301c80050420740c0c004034041d031300303040300101139046c819601050091a91101c03414220780d4401192403240013000c12030b580c494245041800002400251302074148802d10a55032800d0102c041d1844107025016119a40710b0814080030136444010141541c41e154101913440515000040301048400b401800312840029214541508c804800d103415400380c070250407603aa90381e41c003503035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579956115 1250 579954865 579954887
    0x3050c0d0b19170c0301020a1e0c050114061305060a1701090b040507050a060504050a18090c060818120d0b01180f03150509071502010b060705060610 66
    0x600380a8802a0025a00045111040a48003165810071141d01516565a80e44102c000c418015201c0c1140a01800152240c41c070035002035140c0070400c01f009021030800324510545040003510003000070b1044040e440b0b926000740087c8150208601c6000c4610802d4a1662040c3c081580740300600c0814000d99100340002030092844919000e80708441c40f070320030130b100700a5507961240c0380000d41e6201114002e80c080c02c01003070300c030f030400e424402903a26a411080a200c1d0a0104120544d28940304c04c040d0390042e500c2c0480c0743c81d4074000c90050078550300700030070811601d0740114030954800c441c0740c4154006e000303000708000e00c00d500b40d44428a03410118a0342d1410803201310f9008058003c0515500107140c042010a0111000020001a03400c4000303403000c151810004e209072661042001c52001c80308100707070300380400315550b1107001e40f14050301c1b400540b2041e2140d9000707602500101070301401c0a0b50b1110245003031615807404a0303440e0312903d09500344c00d5141e8031131181d85203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579957365 1250 579956115 579956131
    0x10b0a0e0709031b0e0108160317090d050601140a0806070c03120525050708030c070f1a070f2a0602090a170f03071a150d080a0201110a170a06120c060801060305 71
    0x10078078110785840704c1800562100d51050784003042f194409131183c00c0a014154000c8004d07080d44e505215203503403084000c0504510940684d541440400404500260441841c1c103104101c04242c0c9000d50700308820703808000e41d0a142204000c401015001341e041c60880908500c070f00050058420f9a250207200000f500300b420900000d03000c225100000c0688600802020b0840300b120381e594030300104040e030031440c0c1680040034080055007040d1224000c8400781000416a440003255100440b03e640d6480e0080090010a9040c8a06c03941203070410003020b4581c0c407a840d02c500419600a208600441e018450020784800f03105001c42510b024950007842e500c0e14542d03c403502050a20003529920f890790013940312004036038403032401210b694400c0550303030703103460034080042d0071500d00c903c403100707060010801c20100503800020100b1011800f54003900c03d0310b500941038002c11640d0441e110030108819a2018004502088012605a541d83c0e2100740e80b0b8080450650701c05a440d02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579958615 1250 579957365 579957403
    0x1020a050406050702030309040501031b0f0e040209060d060e0a05100b0105030622141f06020607200a05060f0a0204050d08090f19050f03010b0a0e0709031b0e0108 72
    0x1004441c8110028241c145c00281280d0504140c0e80004003110020f91080392280146520500341c5a908180807000300b0040401d11905498880d0591030500c000384020b110355079500000d041942c0d400001002540c200c5000c0040140313406c41c0300c3d52802c2100040c0c0301803003001da0b00c0d00711a0a502030072410321810f954160443c1c80d0301c018400d20404060310118400300c00140e4940110b0305103d0440c11008200020000c0d0405101d00440d20503411100303003ca084d0b0100600c4600e400017042c0d50440a1803400c452000c0180204d800c0f0302402c0c4038010f8490098030112800d0010018095000302070440300c00c045521500904000c0b40710724071440790880c041200c281301046030320026207030115018204002050b00c05000036001c1407007100081d01140801810300203400e001a8844032484c00703a000f02302814003940081c01220b4a4030904405c241c185001030021407040340c200d4015903004100b9074035801014624035a0103c01d009844d88100715500006130044006610800300c14611106 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579959865 1250 579958615 579958619
    0x10e0304050f420c0a060c02030309061801020c07150305070914210d0f020c031b09040f080c0d0f052107021c2123060102160905090d0201020a0504 65
    0x71404030554081c80c0990740140d20403803a003800000f006201059090016103d64111407500d08121400710031400219802842041003809002864036000095040a6030351910110031aa000e88074007014600d65010700c803c0001c82a00600802c100d1152549051040b65251320080320010410301c600340b2034200c40000c944403410169003040304d1030520001a4641201e2141f090f141040c4404114002005c080202c0a101c1e03060101001150049000e05071810317200c0c46c1d41c54014039000001d0b114008035408a001c10440c2c82820f14100c0d4801080f40d2160f14105290342c4440c103000c04030380410804006400301c10301c9802216080da00311112001d020a2401c201969580014142d40962044090b10514602d880403424804116942d0383c803019403c240c01c1e0080c80021440c1d1408441c00c003c0003400c58500c40c0d08140c05c822800c50b410391642d454030b0041b40307070680611000c0070414018070041890703081d64128030300c0f80002108842410240840c01c80c01c0344101900800000c01c00c1c002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579961115 1250 579959865 579959929
    0x60301090807030f021c080915090d0509040b0a060503010e010f0b070303022226030a17090a0f120201050f041e0804030c1e0603020c060a051305010e0304050f 70
    0xa0b20044000c02d2040b40d806c0d615031039900408404000e03203440032034030041c20400e04035420403105d0a0035030010210030a80c1004030b00c043ea60107c80841006000c4007080004498940703621440800c08010407400c0a16030b544805055036100307010314145420f843c000401d00d6003042002000301c1e914010140d14002e81520224000d4214100c9941d04406c01c0802620011150000380094000515100c0f20000340050800d4460500440c49101c0e0300207206401007a41c200040c09c8900d40b900120708001d0780c8440a407410101c040c0301c000c103401ca10070341610500011084807080d009040d0005c21803130320340d01c90700d00e0055021540107002c810300f00e0103141140c3e00700440280305407003000c15608058596171900a01c41c216008810124600e6140045596007100c060000300141c0c1401c501c2c009903000c1154641d030b00100885021919000803032204501d1080e0400c0340da0708280204040d0001e65000c1e920b0b94801c0c46500d100e1980e0000e03002c4c1034a407070701c54585031100d0b4003061100c05c0d0308048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579962365 1250 579961115 579961127
    0x5150f0a0f0e06150a09060f091e0e0a060b06131a0d0e0d230304060c200606010f1b060e0c031b09070c030f030b0a05120604020906030109080703 64
    0x50503495251074100422640c0410042c090040ea03124010f8a04d6501c030505101d031500701d40c0d100b84250380c20820108a03600349045103409942c800d0f0b07000f08421120440c3c408118040028100b9030074508480d03004500c0c0c0109540e59070714403504003407010011140802040f0300410481202c0d8000859040198402700000c145404a070041c00324100303400b110b007c200b00c482c500c000030342c035811034007a20807026404008600000130507131038811303054001d07082007a240c04003d100070406603030f903486038410600a050540d01d00b080d42510303138840803401c45001d031201d4042e1038041c0890341d08148114200c0c040c03603521285206071020b40f0109549929148043d0003030740d1058449000f0460707800c0d00c5440501048031441c80d02c0a82e0021400d9a0062180d071900080c049800c104102801d0030000303500c140909500301c014540400d110036588005500003801d940640c0d40429559101d0050036070220340e0700c1c8102e0084032400040c5c0d42d4078060500f62462200001d207205030401c990300000303000b03070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579963615 1250 579962365 579962381
    0x607020a1502040b1611030d0e04050f01080a0b2a1206040621080409020301120b010503061003030c050f031c060b1602061e070c0311190b09060c10060305150f0a 71
    0x140198041b00d8451022070305044d514425a8001481c421444d00740703040500a40b508a5002c460042103585003100958403200d0322600200540c00713480106540c00b030000224403007010710746411406000803c582030f010341d002d008600400c8003400001046442d0921603482242c1807401203524550116602000d40d4080c1002164101c2d4188000b00c0c0780d0000784003441c00303002c41819000f902c0d905410035125503101640f00a1103584200100700d828013581d480401184d615003040c0b42440c03141c2c94002c8c1001e4101d200c2090b1444042511828150b1600403880382010410341081140d071078855807002d600c0341016481031414031100450042c1003140051480505c000342d0f201a00544041c090032540c000c02081d1242d8070048018414003820b0440d1800e090002c4441c801100b0180b04140c406031507500c0703071901e5600086840503c1742c13100b508492305200b0394400d4484038888446200010140b03400150b40034072518050840750b802844006000c0c0907000b44510700c0f99030b003000d05000350042c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579964865 1250 579963615 579963623
    0x160207050d061103010f0302031207170a05071506060905030c0603150307120807020f0d0f020f060706090b071803050721020916081303052a0607020a1502040b16 71
    0x1800c1180d41109030f000514064013103840075510642c950300405140007d80d0170b107a09140310401c80000007543c12035200743c07a101d10407503442d03c03094402c40541c2c03140510000980024800091078035080190f5100c4000d45000352962119140c0324420700d079480c402d050041c0e42044003080402c1c45818031841d481c4101c00018215034109403904100c08940c0c0304480c6c00c076001007002c42c2000031450104a5941c41c18070903200703c2c003201c6654a40500541c103000c40680140380a401540458030740b001140c006030340194050201403118507090302860002c076980e0000582c81c1d100c0100c51200c8118410403030ba042170040c0003807824150750704100c0070150f00c00c1746203004064840c001030304e4000407144900101c0c1404c610310005120050403c40c8010b060f101c028984540070340009401c84159411032900e00041c040c02c80d42449006203940240007140602d00c1000104030080c0d41c001110000d0b280708903960004036501502c42d40c10386c09280140300100f00d050200c825460001d42d520740c1d00b2805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579966115 1250 579964865 579964871
    0x501060302030d03050f01060c030509010804060f090b01090c051617040f0801020a0801050102030a12020706090516081516050901232206050a0507050304090501090b09160207050d06 80
    0x103268000707450010030184210100c0d40359400c00c40c650a88115003801000e090a05144900d2107680060462190240f90b9052001c2e8901003024000e90340e100c081c0c2008601400c10211240f4140425204024071070b0b500c42c0c40c10721481908881c0306109640900e0036a078020400f1102d03d43c0c1d18603821f070300440c0d0140c11590922000421428400104005100c05800181e440c69200c50080074280140c002c1c5040d540200109003061703070700c280f03007000c0b004201c18010303102d808518200b0040c00741d04401800d14866034005034190503007582d1302c5084a01c41021241c000f030300105802d41202084940002905001c1200752040e400b5400400e0074460514100030b0010340c1c03410580302030010300c0e120421f02d48041080d0179000b0a00d400901c110303000c003c110142500d800001401031059110800030408049640d00c2005410400d40c2c010f403808031424842c070740e124100c4600a00144030b5080c0f040714640d000c40c650300d555014116961183d54041c1664a00785003d2011840e04d9840c21903409507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579967365 1250 579966115 579966119
    0x40e0c07020316061b020102030d020f091503070801240507140f0c0a0b1c0b031006081f0b010903031407050f060405070803040b03070c020f130905100b060d09050106 73
    0x5003d00040c000c41c1d80500140703080c1c609140d03008040310181041d00300c01501103000400540c1c1c0020980c0c44094010f1030150307881e0f50407101a0001e014004c07a454000b42c2e11001c131107081440c400910301c07070340c119540c0c103655aa0360a06510b000d034a9a805a588001541c8228000d612a400070003403039024462408100c200d440c600c40c41c02c4111290342c074031034008008a800070b2400180c04801407000c03806041c189081044000030300c62410302540b4107503544a44040141d14184000859921240c0341000016911001076482e102d006840301000d214607494030a04844512a11400e180c0607900c2c00101411035038190358010303d9641c00d101900051089100140c81000b4042881d65440c0c050115801c00349050751804401e40c0000c00c21360024007050125107001002e41c0d40c029210b1406018440c0f15001280c214004082c410740c101c0b402c0c299941d81c0c1600754201c1600680b103002110358068a00b48403100300c98103095100c0d8451400c0040c6041c0404a40120703550702d005500003c2c0881d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579968615 1250 579967365 579967369
    0x1a09160609051e1807030507020c030c040e0a0b070806040609020f0d05190e031b0105130f06090803070c1b120213020c060106080a0609050105090414010b03030c010212090111040e0c0702 82
    0x310a01042e0302c49800c1c511308010f9200d03410700466803c152140003c0014050980c0000c0e110079200d403409002d242d40341100078802404200380240c40e03812290301c40c031714201041e00400c1503030304540b401e02071400c084000498038403174821985001c1d14222424100b0507007a10100c09000c0c050105452a00740d01c0fa1502408010312800e08d00803802001156281c08030311048041042040d102580350b4134040402c600100c1d180360b04110a584114003940c00682403509900500110001418000d001700c100940c46401280009400340102600e07054882c0b030f9011030b05d06100d40c2c06104030904500c104080103084c880c0304118291030391030025041c801c9a030034251404e40c0907032000340064500000d2051802040c803032800a4540c0e000c01340007540c14400410209031020308000e14505031440125207042d0203600c00e00f41c50f40c0003001e07a030f5100150241503000c0d4011020582015a001c0e02241a61710144200c1d95000100c034000c034101403034514800f102c1c400081009039100c00c2002024016 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579969865 1250 579968615 579968629
    0x11010603081801031a1c080f040e010608090607020c13182f03121b061501022503060c14030a0f0b06071109060a031a09160609051e 58
    0x103407034101891600b2405103030006080c1c46001c40d00c0c2c51130100710190341d606a02d5039031010032000c000c582c90101d0000c461400b0100d45c46001c82c840c01600022a0120302109125603e0b412201c00340d03182031098883d05043d6803262003d892520169202c003014004504141d8250710020f40c1c5030500040340e59207094425182c240c0828111800703503042c00d0b00c5056090110301030008000c80b0342c0340b1708540c81e9880480e82d81d003288107009805260200d02d10001d24840300c003010110265109480b000d0030002194143c40403031094041c0540a03901c11100b030840030399808060302c200a141807000078556183c420040050410318010071148000103000c1002030002035018070b40000d8009446c0654200281c21a0b0031820407500c500000c00441010808011920203c0071080301d20101c2501e8110015020700e0340b50348001c4c04480000b5906044031805030549100e80ca01c0800ea071007250050b405519800d00501609006c21403000061003541030901031100d100140d0070b00c05400d002c030b050008240c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579971115 1250 579969865 579969877
    0x1113050901020306030f030f03060f0a03150e0c0d031e021c0e10030506010807030b12010e100b030f0d0c060b120a060e06010f090f0b040912020c010503040c061101060308 75
    0x25582d00001400f0b074604081050f0510ba4201306e01450600c07281c441d0320601440050300c2d151050304441180c0c9429034404801c2c10081d03038803c01c110402d00c4102d000354064403005141541f28050908256558100f1241d50f05202e40c4c1076884c1c10b000b4561a40c10a0f000c41a4106441144503d296041204404114204c4036a5880d142e000c10302c80c1d01010406004044090001014144030610119981001401703030082c3c154100402c0300303541140406c0300d2001c42401d0454541c28012010f1200401240700303118011100c900307000e4a41c850f414955915031512040c1801c0c0c0c040f41c0c00d000e40b1391159038207214581c41040003250600903030000814000b4800407003030185d00007c0c0c0d44400c00c8018411012002000005052690b1614070070741e00c071070000e2180c18074007911170602440d11100c1d0303800406a06d5008200300603900150404601102e162188003002d48100d1038405100d6000704180c038800caa1001880b55210700300034044a0f034030541029107140d503403140300c0440081d081d1409012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579972365 1250 579971115 579971131
    0xa09050717060105060f0a0e03280b0903070c05060c01020405211c021e1603060501050901061d040c0e0a0303031a0a080705010f18080c012604111305 66
    0xc007010344424414100a01a844144615001c011104003c2050740544040e0959401e0120f156981da801107410001c2a20550600b840c2d1101954000300c1407123089030403207000d40e102e84220381d0341d00c4400340d6a00c40c1890141c442c6800307400400003450214018600401c402c4005400d09540c3c1010a84c1160907803051214010702d900042c2e0f0100040004940b411040700c419405100d00c4c0802a4442c02c641c600c50441a100c004000f140c41c0d010000042100360040f94065803a031b590911718000c0c0008e004191003040b003000001401d922400d086c01201a0380d072810002e81c0400c0341000001c104805480b01803040340f030040c03280b17543c584000c800214040e0301c001c6034070904400311903241c685c1400c2d004d00c1868041c100340190700717000802005540080c00e080503500e680c0b030810303503600f10f0340305c000245d240b4000c43c0807656100100d00f11660400030707210f0164403c01960440c200d41008000d070121041102c0004001c10030030280d0407644880031b8480d21031400c1030200300c030a40c1c000f120005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579973615 1250 579972365 579972389
    0xc0d09080306090a140f07180b0d11030f07030213080613020301051e1306020c030412050601090506060d05060609030f06010f0f1d07022409070515090103050a090507 73
    0x2201a060010011381d01001d10f07041001a00c440d0b880440d0154000b42955aa042e9194005101d0b00d001b034110076880074155420b807500c2d540d680300721880780d44484264403005007814101c00074000070303d0035a80500344904c1c00c1c0b50582c0c1c4000d000c0707009401c92440480c1d660201080090b07801c4c1c00348081809848000000c0c0c0d10100280141801e46130b0241c08a5200701ea0b42591111030801c4021803a0009034211510340c010711076040581c0607014200d01440240000039001869240d4420b03140043ea00c900159401c0343e0365010382078111002200d100340c00c400f04101c03d204d014605e0340001c1d400030001b0000b5060090010104e840c1200111228110754407a02c011710440301c1d0150000000d00b4074000b801341c280e041c42070348040e14a903c0b1003180c800c601d050100b01001d00a110960070030401d11500c0c04103e072190104c0c1340280040d40c9500c40350149110200d0700d41424410751264940e4008024548903e4000442c02000020000d82d40c40790f450741d010001a0381440721400400c0c00305040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579974865 1250 579973615 579973621
    0x70204020403060b090108030306030d08060d0c06080405010c0503060d02060d1b18080d0203090909010b0612010320030318040603021801031e0b040f2105041802160204050c0d090803 80
    0x4040e17100010380010201e64000e000f001100d980000e4081c5612000d460007240d603849060100708800410400204004910940490400d40c05200303e44954000c400038020044c2d01703d002d464074401a00d0098101200310303400401b508021004003034580c20411b0004d010528451000d444c07444031020b400c001050704008402e054107210303250001e000c040d0060030100c950140e02a50324070031003000501a80307194001410103a0300390f00000b024072001e44641d5450803150f4800c4a075003400d0000300e41280601401440b01004091680c090900260046190160420507503c00340003010b5801da000380c035032030080300507140d40700c7c80a0044440d14002381154150305d0100740340c8102c00000700c034a410301d036414808560b400144941080c3c02034258007000c651802c060a05400e401c503460300c040a58040d601000b54480b0007841120302407401c1d07948180c0305554910917481a03915030303143e299039040d8078070261610f5880542c0200001040e1481c0001c1ca420f4042911030241c07091b11500c00210070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579976115 1250 579974865 579974869
    0x3080306060d0c0e18190902060c0307121205070905041d0a05070312020318091003080a090f060e0904080a0525030f17070e01020c060d091e12050f070204020403060b 73
    0x1584040645400343c0c05c1d05850100c500301c0c003031003404000d05007583d22200340c4801d54681d0000c650f440d00c0342a00f6241c0d10001030034418100c3d50207181400c00555420703102810ba018034490703036008800075a10301a030545080c2c20080030300102000c01007081d188107505c403414801001840c082030301c5100500721071461403c0c0020070b54540780d01001590010010061205588103500643d8801220407282c0303074a40c0e0030f00c07080070607460b00001c202000000c0c440d188246c204080d00d040303540304400c255205c1d445034011510308524004c01e07500165601e0100f030005e04070304d0280500600510b0000d0a044083c0350240501c91428000d048800c41040d400c421301d40e0145041e00824510b0805c01c400e1282c548889007200001000c5030704119405c0701742d00c010fa2081c00007045030007008080340e490710b0910403c00010708406504407000070141c0058a107456208402035522031304a1b5030101e0104540105540c070750b003c85003695808004006c18401696141f010780701a5000c1c0e02c0000700c0d0440113003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579977365 1250 579976115 579976129
    0xe1509010509030f0d1802150c0c03012702040b090112151812270e13020609090919060c03050916060c020a050d050d17070903080306060d0c0e 63
    0x2241e00b540d80c00403c05a03048401c08400c131079400d07007402400901030428195031668040c007048001d502004400441502c5041c0e5409416a040e90310151003081c130b20b04003003500303d900d20740064880280a41c920700d00301030b44141d017058542c00603001055a08030400004c215040980044004075856007401d010f00c101c0b14520f6030f003c0d584131410425400b181b82082460b585c03e4500601840b46048105501881401c80c0714008984c106280c05030700c5103407840c2000800c68050746c0510f0854400040c1c04810200e280d030780040d00a08a68a408842070601030000b03030007004501a8460603e02e41c0070080c01d04488803050380184000610146c080500406039000500621035940c048084828062600d900c0074088625130304094502113868404a600c0e01030030341c00198400c0f8904452014040003080e51104000c403a6107800d480d03100884845400e030015981c10b00062403480c800c0c03001400d41d40095401200c002e20341070a2030044110300055801741e00b49000040c202006003452428010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579978615 1250 579977365 579977371
    0x506030117060a09030503240307180c05121f0b0f3a051b07050c01090609152d09050f06280309211706031c030e15090105 54
    0x1d011340071007514000d046000203880030700c01e00c018910081000300c081d80f66241650024081d6605582d458045015104000103401e0003142002006025688070f0400c48100300c00411748000c49440702e1007041410b189600001d40c10061048000c170f43c6010f9400500b4604107000d40c003913520041495103200d140c0c2d031307400f4055041761020310703034820401c0280e06888155181c1d4000519559403c8002da40a65070089214810500158850a0203404541043c035000281c83d8403080b59a240c104503080544c1340314404d0104044802503d1551040c011020f00300380c402000304100d2011400091145500656017001c504c0c4e1807020082c6003072540a04011030812141c1c5424940340c002520000664501c0220307084042c4040da0b42e05038041c1c2e000040e215084100500504840402da2000004800000f0041900103e58010105c055100c0300c0c03003080064007500741c2820310400009403c5104c860603050503100c08403c1d0b24440f0402002e01004154004600241000d07442c0c1400c4850103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579979865 1250 579978615 579978631
    0x21b04020f042301170f0402150c06040c1512020c0c1c11010201110a1b141b031b0904170307121b0206060105280914010c0c06050f04050603011706 65
    0x542442c41041c0c1700c3d0450f0b0358031902c040ca8144103a61a88005180751080e96030380343c4490740100c0c114920100000f9000c0c8154401c5200000c4a40c0301d6042ca40030300710000d013402c00140c80c0b9500288221240e009881c002ca6001c045420000408000684110500e100040507908030b11401c024048907850541c0031342c000780020480305c0300720603601342c00744246039811051110b041e1b110006030914110b5028200d41007141000202440d04055446140203410302c40325104051032501c90745404a447d42e852808509000b10b02001402404890b2030000c00c10b4451901d20905003000307041c1c01004500c01e2900380c0d501d1030100c015141003c129441141a000c18071525624a6007440d0000348081d0040c10909190b40c031400c0d0a03d561b410305000e03011000d2401440081466996085030040054035901901d05c0000c3d00c80c0b000445070800d000d00d010f05074158401040000a016000400d40000d1030300c81c80745880d4480b808103440307905c02e0f406501c4005516100704004003040c4815608901c0c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579981115 1250 579979865 579979877
    0x50a174506160c0b0309070e070f0801060807110a0308010617010e010302041d0106030f020f0102150703150e01081b03030703051c02070b1003021f021b04020f042301 73
    0x1000000c01c0190260300d030441501e4415a0076078050001c00c5003040020a03140b4500340d034926044204507120096403265092a502e00408903100700d014001000114403641da5180b4030744e281038411503550001902510501070299406e0400143c02d000954449000380c07a501199403400320002e00c1c00c3c085986031004030b4413040044c40358940400901e0304403501120041818071001c0680f01c015800189230600a44c641a4000704210904a003444403c1c005c0312048900701e0040016600c42030380c40e009500c0300b00000005002c80d0301030340c401c4e811054003103035a1001d16199825804e1006003a0400300c915030001060f0516405420b41003165000141d001d5414803009507009002406440d017804c01da4440701940c8542c4540781d5059a4903150001441181410b0208030174031b00c1c0390a800b05a0182004500380d100340e52441d60740d1207141c2440d03401448401c2100b1540720041803968409507001da02044002048400b201c007030409880c0078900e8004d144004100701d001d40c00c840c0c0d850750500c91 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579982365 1250 579981115 579981247
    0x90e0a060e130812070e0603010806060f0f061204050708160503010609020403030206010605030a090828020d0c24060e070f020610061b060501060c02040b0904050a17 73
    0x81c3e00240c9801c01d18002e1801d00d03580b60204180c0708401d10307001c0300c1d402000c08000051841c0002841500a41058900301002d142840074811a07000c5180b803203030090010450205115403015032980e0080c0101e06880309c1d5602c560000b420040303102124a143e0600c1c000034410b0b450288a12130003082c604070304615151441c3c0d4043d4131030005100780c40501401000044546140d5044088020f9001d0700d0140e845903c900c5920741d08801c5c2d924445004050b080181c0410300000c1c521850026136199030007480441da803504e090040c040c48000b044d0002c09180313208690baa009500c05450b001071500785914041100820442c140c400441c01c6501441c00e11002140382d0000800703845241c500740d646601e000e032607641d02c0c0b148514000d0050745080c000241055000180c521250710845090001001210400401000945010300381790400c100b00c40004905140701d0718000d090a0441d030815900e0703002c0004c6201000100210801c0f41d078a58402c048074a0030589000c4614601c480d2450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579983615 1250 579982365 579982373
    0x1521040f03052203060204090c090e06060f19030509150c03060d0501021e03011a0c0316140708100f0527070509150405060a1d0601090e0a060e13 64
    0x11000340015060100018a040301d00c120440c90720f942412503104041c0d4a0713600d00c2c00100940c498801e10740403926100001c1c2c3d40d5031050488400f2119003800100036a00c0e0842000840c0d442150102c60f620005c005000c80c0120402401002c070980b51800546850000c42071070403c824160040229074038001040b0358a10050290381d0007031820345080840042c11300c0e141e0700900c50440d10240c0040c46100c208050980b1000450503500380c2d030301011000310400e0003141d06018021054440360803c2c0240840461202e82d81401240580b100c148616a840903090400b5000c0d0051801d64100303a8ad03440395000d01c3c1c014500b840070420010801898108100c40c00c200026084a40c4841070702200c007211001002000c0203410006c2800717440d800c103080041c0c121b007075010085010b6402c040000703440d80b504030360000807130f280414107004a0000324214100e4a0f40281074a050021040001ca484000400364606c5500e0002e00002c07201c0c100307554010050341c014200300070f0300303494202c400001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579984865 1250 579983615 579983633
    0x709060b0a050d18020424090903050906070c030b01090c1806020c1504081005180703020d06090c1205030705150106050d090c080d12051e060d03020a02152104 70
    0xda010301d03c2c001941c0c207518020490340003d02c3d03800783d802410900c9413203240c0101080901d9903070361803441380a001d5a9802d440c054440811010380828000c1c4070340e18880c01c0840c0100192032142800302c40362502c079512410508420707040518002d60f200895400c00f0b80003640122038044001e0404207852030420029501c1800820030b60244100d101c103d80721041d0901541d0261140303809071044c8007c00344840c00100011114800d510805080c0361298000104181054980180c280d000f080c40703075200c2801030480904210b0306403070003d1000441c13007188283c031401d0300c1c810350187d665408a42806450305910b03085200091841d6401007281d01c2d040360454910301101c0c10041210011400c100703603404903c3e8007040c00d03400364640d005041a40b100202c4502544884100450307181e20001000c1c0c0324144043e03101d072440c05008103c041c41c0ca400f410386000d01c01d104a8031108110703800b00c0e16030411031b80e50301070409000c80c5c010b600395080304c0c0000301609072207a200442e18103511101c5103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579986115 1250 579984865 579984877
    0xc0603060f14150a0c03080a0e0613050f0601060c0b1b0d09050a020d14060106230c010f140a060b161b0b07030f0e0402070c060f0e09090709060b0a05 66
    0x2d40000d6555002c556200c241a140b908822042007070344a1040304005070114a5155040b40010101c0001070700c64413040c0706506403d01d00800605441d079518101014680c001c003402d032000e10540480f244454010080a4042c00c140d81d0707035181150349881c0c58060040c010300880c180510315400e284101920f00103640ca10a40c0780408250321146040450801c0c4c0b607590081d41241c51101150300340a040d9480c460b42c0d00c0ca00382161031507030342d446007101d1000d2440072000c160064103400380c4291a50501901c000500d0f02c000040f00c40c1c0094444040b1101c40300c980246003517880401a0750380d03c81c0f2a02004114410715a4980300c0030803408800c14484010040c08050440c222001101d80d111828018000d2113048c2e40e130b1010581009400a142c40000d10009914989007440d40d0070103000b0b80e400141e00507040c440e12818a00c0c00c0d03070741c640c460309460100b06081d020505295540310380540507a440e140504040c1341000152800d8a0319034001c0b107401c80b42080f40c980721030381c01812200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579987365 1250 579986115 579986129
    0x40915050a09050714030c0a060f050d022701140a1416020604030305220311150c01180b09011e020708041814330f0a0e040c0603060f 59
    0x1030290380c0c0c141c1c5240200751004000d001d602c21a00f0120301003401925000c0d505004504403101140c180c000c004480d5064056080080c180e0440e0760351550141015100b500c03030003080941400201d040c00c0036211800050081c241755000c0d4001f20550b0411007006036440365080300d80c0790074000c18001c0c0c001c40051650300c0c1c4032130000503009030654004841c2c06119500901c1c0941d50343e034038100140309030804840d000c1c1c102c00b10640d229500c408608900100d0307074403071060b5070a26040c000308040c15000300c049852698007088000070900b028841d0101610940000c000d006510b41040070900030700a04441f000c0c1c0c5081125003032083d61044505d1503003001800543d50784424508103596010b168060144020503070780303082c15100c40c0e801c402062081544481c40540c0d40e0012008608188005083c01004807042c01d1035100c20a03070502019000607041c503103c0c2034000301140304030351198800110208200705000030042c020744031700011300d800d282c20b002a5042ca14051000042480792117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579988615 1250 579987365 579987371
    0x60106051204080c0f0318060403021804030c0203010e1608280303020712091d190906110a030606020d1107060819091101090803032a04181505040915 66
    0x5030410003e1001c60301603d03404000e60340e0000030048200d0380c1c0d800c008500c0180c051000745254043c01c0c100103550032a078000b4a05001e499144500d000b1681c0c1c090820307000c0001c00e100500242e10300740a0940c08241a80040484441342c403e00442e8501d00e07013280c0c140d500040c0e10513000baa5208012400050141002e800d58215460181e0080c455214010180844081d8019019400083c20380864045490f030340320316a42d01040040b00c040c00c0341d0525514180d480408034042441d4410420035114a41c0010240800660410150090740c064400252144028080c640d81442038a050740c0140c106107030340d01c0a001d412a103030030700c50054808201c5000001119003543e170050051682c07580f0400c201400c568103040442c0c044001209012a000300e00000e010400041220304c2070f1020014000310726421405001c0d00301400801117403409081c040420724140b503501546100407090070000303140070840d048443d074000e5940054840e5250400d000003090325100b43c0b18100417915000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579989865 1250 579988615 579988621
    0x903070b0c07170d0e060703080406020318010204030605180604030804020103200319110703090e15120c0414010605071101031b05070506011403030706230f040210020601060512 78
    0xc503150090340c1e4440d0504485408400c803c1d5400424400704401d003e6803285480e8211409101040c45451002800540c00400003001f088056014540002d4605c160803c001450010542a130704035800c01d44180742e0b01c80a0155200740a50b9001800d030148001d0140c510700303510f01a0011a00400103810325031516000720f1050740c054000100c0800a02d103403074a0341001d14884107441c1c004000001901e1600ea0801403240c4800286c031400d641c1595555401c1d8100700c8482040540507100401c028444068200d15641b1500110032481040d4001c2004030582c1c000c02c000d843c1c40b5000794048402250043c810541d104080f0b41c0116000251403006514403001200180107225511500011820500040551000080c86c0c1180504104e90040c1d80318840703061600f00004003258194010080c440016070b81d6006000c6240d0005560009080c6a400c0b04407071040031540840705944081c100000c43c50300c2c7c518424141510f10081c0789540c10b00c407010704244108461207624812034400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579991115 1250 579989865 579989887
    0x60e011505031f03032006090c06130308042c01180e1f060608060a050d02010807050f120414120904150308040f06090602030a08070c14060709060f03020903070b 71
    0x560f02140440c000754008903a00d050043c07031780c5000c4004095601c04c80022200692000864a00034070000c405455003e0ba20001c00c02594000701d405900d409006900101047c2d800e40030300002c048403c080d07040f000c0c0c524880103008032940705c01c00700140e100b8010310480501d0230f04240743c3c042100340043e9108006075024a4250901ca00300c1081302c410115440c50241900281c0482d449504da030b12240e220002000000402c50052035002502c40d02d102c1c0156100e5240c50740c10030510309060345048201a9005420780c032200040c4054180d8805100400500603141603951300d410300981011800b40c8075014180c4504840c691286484040d40801c001144040700300855024881075034440d07403040304004d00c02c11380c81280040742e400000095803a00120450f11100e1082d82e4002041d91074071810703182201003d109aa40340103001d0204445001040380901a010300d845488a0900c0c00c0f030010b082e03082180010003050f0041c00004001c0d1000540171066541419005031105100c2e91 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579992365 1250 579991115 579991141
    0x1116050f04140103080c010f050115030c1b030e1203071a0603010b09190506011719020f1611041e1a100306060e0109080d03090201030605120709060e01150503 70
    0x50b41c51034819038200000b04200300c48000b0440c1100b110006c2c041005614a820100d400c244108900b205105502c040c07154840e030f0080c40501140d007000c00005120000034600e818101804030085202440200f0306464202174001160f030070b11004515103200d503030710520340e002d000b50140203090302500451010380e02034014244500d0054912450b070720702041c2000b050080c07029a020030318500808161f8652080340c4d600c5c40400360b49a0040f85888107400c29018151402c180c1240ca03030309108044140c074200005001d905a20140400e405445040500c0e010720440b150078071071343c42c0c2104203141c03c0c0c091046a441414040c000284148148401e0b0b0f8030040d00e43e001517010343c00d0102a030007550154031000544556a540b80420b001c0c10006480c0100f00740154802940040c4081c1581c91003034110060081c4185000308401d9a200c020847c2c10340311641d08007080e0010002404401ca003072081c00c0040048866000a41d4907011090b80c1c2039a41121107000c202c0004000b40740c002040d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579993615 1250 579992365 579992381
    0xc040c02190b010512010b1005031b072001020c0a031b030b040503120a050c09040c09050303030c0d11120c0d1404060b031e0d110708060a0209011116050f04 69
    0x3860282024081e840c107000c500c2c900b40100c5203e85a050360316051502d05108011003a58041d050103500e8100050650741608014160300310b200004040311901d12500c0702411000d44030700c02003103c03440f081c00001c031683c903d44203172411075203c2e84401d00c0580d0b61500b807500720390700200610341962662800441d01e0010f500050244000f2070207000030400008014429a05d14240808198842041200a4800a5841406207141400b9442107454254810681c51401d8100000039070364400100c0d086800c100c414180000d408903135003407141218002d8034600342100703080c03d1401164040b1501c2450004c1d00180c104100400d110440c0c00603a407007500465100c1d44103101500d05842c00c0b034050644406068041c0c02144110000700007800b404005124400c005000d100c500224111110051004281c141d4450302000003420101845070328000d050754117016a1703404881002500c030f260b1219040c105607000394000c1d501e8480300c0260905a840c01c03039442200ba19140002000f8003405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579994865 1250 579993615 579993643
    0x105011809060f0513060605180d1b091424060d09060f18150509121303050706020706141b01020a02010501061412010b071b14090c04080c040c02 64
    0x4001c0100f038220008150204851080343c04801c030840f103059000541c0d00038070072100401c0c001c0c070010b0010b94150322583c0c0c01078400792441c1c0015095841e03440c00e0f0401c440c0026207100c159032062102100781c0c00340007045103840081400314108917000c0020041c08100c0c0e11202024100114807564803030088420001998200b845003072003d05007040104001c90029200903d4018008185007400741d89030516074000540003210b0210400d80d9000e0b0030b0080c0411414010403604105021100300500344201c81c0110f2210701609500d000b6261001d160850000d660180c1802c015891344000c04a0041f47c42400441d16124240300c51101c2c2140743d4900c0555500100d16220426030552140d030498201c0d55070305160032600608030300d1600c280150b0071082243c480050100540721402414141c0c441e03000c244914a4071340b001c01059140c2e4216900c0111100c0524500d0300d03100650076042452051210711302031603c0307403140c1d175650025100c0e400b6548407900040454000c1c40309002100e52 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579996115 1250 579994865 579994871
    0x140f0102040302090c030907080d03050f0604051306051906030503131202060301120f060204030803060108060f0102190c0b0313062306010c060f060609080f0601030803061219030e040c03140105011809 88
    0xad03c690141c00b4100c01c0701c1c10840e584c060400a601407829001d981d0107402c03003880d64441c0c0c50044e12030b040a004001c0030010959850709032030fa04400c02d80b1032840114000c4000c0c580312201384603d00811805ca5011110b490500f41240015a454004980c11540911081034540d01c05207400580c81440c090041c2640d803011500200748088000118880e074401d076195142555017a08110300700e5428106140160301c484441a52000081c88034034199004001a84106684d01040c54140c0c0c01102c00d00c108089840d100c2e41041028019000e460342003e9580483c034112401c0301240580c0200290b04220303004d1005014816954030001c1150046a030601245454490180c142d500714400c03c6c040d4416861451000c02d00454494140c96008950919580369101001141100c0e82e0310201c10307002e03103602d2a80d008910b44202c8080d0b480381d1945031603a40c1c0641040101e0303543c114281e00345401d01e0050394810038019000350640b00b090034081603050282c078524003030011940040e02c0e002c1c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579997365 1250 579996115 579996133
    0x141b0c0111120105041404080316021c02070303180b070215121005015019080906040308010303110f01060b04051018050d020103090f140f0102040302090c03090708 72
    0x421544128144e50080c1c2e400d00041d81d00c04149000d4180803a03028021040c00d00102d80300900c0071114561003905881100d00300c0f0161440207210100b90008100542d2100740d0401c105504040340c90030040d400091545624a0420002100c1c89224002403007100050661100c502201c0c05850724060742000c2c1b0101c034a44502281045051400b41c1400b00385440010004a00b5101d080c1060308103100c8488009001360800100480d10104d03251121100700070001c1d0185540c801900013480c003601d1495100030710b45c001420520b009041d056803500030030304000119030009481070460b075152070a0f02c52500b40d01c0d282d03030410000003254406542420030005081c1c05200150099900132100e154140710420703003c1d902080c12581f0081850040303241042503142260700302d541d483c010705006c42d600c1d4880d50b52a0246c440f59104490742100c00050190390007080001e91481000d1000852600e03041d900080d5046600070240c11400c0700010000c1c0c00400248104002000210f0444000310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579998615 1250 579997365 579997387
    0x61003021314042f06090f03030712120c090b0304260a08150f010219020a03060507030203090111091503090313060f1b111002120c0102040801141b0c0111 68
    0x310304590258a803551a0110030612000f0134002c2c3c01030400401c0329140c56041d20601c000a4000003081d076050000348054004180d0501d00101c0d40d202c1a51fa40c0c200c4486040c20785c0888150001e90000c10410072403e0150310700762000c90307411036040a2855030000300ca03644002075800551040d01951400b08103645000c1c0c02c8001c0c0d5003e00100c1d5142144080d00c1c0c1c0c103028100446034060760040e070103640c88450508800069032117403800603004c400920303180d854100c180c4806417100400070f40d0010030080d111038203110780740492000ea400146412000341c00248040c042c5500340c841e569000000c1041c4000400c200d41020342e822500751017142d510b07140900380890034140b860100d07070007c0e54000c035044202070350020f1a07441203103104269486418840703110791010a160641c81648081c840d03982004000e0300b41311000500150303455080000945c01c1d94001003040900064000078807500f800c541d4111400300403c0c440c0a03407602c4000308207901500d07030022030004980000658003081c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579999865 1250 579998615 579998633
    0x50319110a02060a0b03070510030902040218090603011e150512061009021306030f020702090c03061e0607060c05130b0405090603062809080d021305010206100302131404 75
    0x12590701d03000d03654141c3e01c055441c0141d80414410780c2d49600864410301103494103026040788800e45203000111040541c0c00726040340d00000d01c80c00d0100d8441c0290806262640d441076110000b500244070700c4d075036040d15804803100d481e6141c0784d4580700c00c0491b000700300f0310344070100400000f00082c00e404480c03c00caa446040c191444c0b4114a003100011800054074002c03104250849220b4544041c42c0c818210000e0428031200040603808018010141c1c1d203180d400b81c00340f039088030800d41c2c81c2000001c000861425649150241d008020480703d15600e6100360b0380b0090b002100802d50b042c0404045900c0e10820705c1070702c020350040e000400d503418032a000e441510025240c416040c3c071001c0805503a40c0e03040f50041c019264841140003d110006802c0000c261100000303e0110b04907540c420300d81d0800c84000d00b00644c0410b0813201841d061124034000d00083c00a0015414183c00b0000002510300003c1c1c02017910044002c001503455102a100603401401040c281c1031500e001805 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580001115 1250 579999865 579999877
    0x170a0602030411030f0703150207111e01030e15011a0418020307030f090f1412070602220503070e0717090a0c151706031c08043005031911 61
    0xe0310a0f5036101c507620a00181c06c1d0b041c0c035040610018074038104521030000e513104c84001c94100d01040c034070b15400c0c0c0b1350001900c041c0301c03903144d144441d0966000041c2100d1920111540c0ba0b4400c04002a80e2a100103103181034841c031110401c0c0880c68100c01c01450305c20381d403140c01c00004008000002d0b0381c056010b1406009907940510451026030306030400e80c0c203c0c17400601291403c50040e400030b0002528500d920b80300c0c0c001e80780402148104000d00d0703049100c5c1900e03c3c9400007501031044150030041d042d07141402030b500840740e080c900800e030755140c0ca00803c0030744051000410141341c090070032042e0f00b00341c5481c0d241852919039641f503280d600990701100c002d001080d0103c0c0c1a2080d00502003000103a90390b1200580085440d0000100054205a054065070311404051403141d119a08030031090f03140da00990610340782101c02d042c0c1c112080080701181e400301c2d0705010401c01c0d0305508060545003aa8580d11659075050305200708502c00044945000c85103048a5003960250903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580002365 1250 580001115 580001119
    0x6090a030f080411010c020a05040203070302040f0b0412150e0d120f140a020904060b030114030601140906040921120e0610030803100e10030c051207170a0602030411 73
    0x40c9000822050302e00050940b8000e0661000941c000025441107a002e18003074001003010782815030390340202e0120380c01500c3c0d0000280c0c00080034096038007001e500c0401000d00811652406181031001800d03c00c2010000300034001c0750300c090400a049070042007020049409441c40c1005040024003102c0214601c010801e040c14000c00184c0d6a0b4801c00d504103550b50200d0700c2c29920004160020342c001c001c804d03441603a820000c50462041e001440c060102490166980a8100101440e21105034041c3c0b100c2d0110a500d100342d5102c0c01d0a03982c00060688020a42484070318006a0003d4100c500ba078208010036400409541d004036540032410204104001d50303240c14800b646c035084100c4020b0311038450307854200000384000006540c0909562401015161a410074030210f003001d0340d100190307502c020018010300c214055480001c3c0340440d55201c1d41ea0940071100d4503101c1c10300c40e01042104d48580d021000030140080814076911400c119600d280614000700b402c1c0e4112030141c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580003615 1250 580002365 580002377
    0xd0807060c03290d0209092103010602010617250306020a02011d010b06070828020d020705010507030816020123040c06050403051c120e1b240c0f06090a03 68
    0x82e110f190500c2d007405050340161520050010b2502405400e0324003130b06d1001d00c3e1107041e51744c40720742500403901c441180c11a6802a0349500d0301074020b00f5903a09800c0302400000e003200402070518005112201580015004041c0c040c15180803034080ca081d50015200c0d84c000103800011503030640c400307244403070b0090031443c110300001066400ca80e910119650861030400c40800031400c400c0140c981a800700c131082c4250716008812074402c6115804400159001c10b1982d0800c03601484008080c00e400c0c64114100002a18000e03c010303070240c02d603040788150303c04800d0010f20030340140d2211544583d0b03201c00340341c2000380c0c0b07584208111002d440c030940079200420030501c0381d0304640450b50040c00900c640029a03082e603250301c00c40c0c01580148411002c1e08030ba101c1190080d12500540e400c00781070091020881c00d1240f40d18640320358444c88443c00101840081201c294034201c0c0d00c1d500703590700c500c001e10303001c2c2c03804c2000c6c054100c5900c00c56040248030140010345111841c40b030355500d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580004865 1250 580003615 580003661
    0x20405010e07120f0912020d080f0705071203060825080d02031b0f0703060f05060306010b0d0b03070b0f250302030306040b060d06030809010f0212090d0807060c03 72
    0x3000040006940b010000b80600c1220b07682c03010542c2000710a2402c4e0400000c1054035959246080c441c1c3c0e2070403102613048a800f10b20203540000070a0f6101405844488481c036082000030441d10580400920102c40c0d1000c1c1d6410724483e40c070900c054007080701118484040c40803001501c01143c0d141013021002c802d4080307010040802c0848200c01c65130019800e0002654078a00c40b0340440711307281c200c2d00ca50740c1c41c2c0550344001c01888004601482000425209512281c0d0982d41d009151354001d82c8018010090241154121107007034010310300016102c4505c0000905103039041e446075403001404920035500f5503c207401400d101100000e80004000104c40150682d03402aa0180c00b60b0000d1000a4135400c1030740090002c880000c00992600d80c0b54555401100c901e50415983c0d039502088074038895810803940c01080d02280000c20402c10540c0c1e9541d502d11508003618005d002c5404500204042c14081e00c0e0415442003050090701000e00d00140100000402c1c1075460484602ca = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580006115 1250 580004865 580004879
    0xe0c0f01140711030a1a0703060e060a0501080702030408030708090a27090201050d09060c020d02070f1502010b030a0308040507050906030d1416030e1801211b09050402040501 77
    0x507402044500144040c01c100154480c01080407104115a405010b4002c100e80002e40e03180d01640f9003103600c0a000c14504203c1c0c4003d00710741c8160013183c1c10305034080901ca603541e0381d100c04000700c85003460031011507030742c04d0000c03810f5000320340c4000f20070b2101050b0401005408409404948400d4490040041d0384180303100b68511540060204c0c04001c00300481000440c3d0001c0020a00604001d49056110541442164400c00b0241d814565410042c0b03011507040c08840c48001c998801051420309080c404d003c1d800041c850304403800b028407440d00703131a07000390442c40c030040f001000d460100341d607402d000d405a8012641116603000b40103001c1020702c1c05014090154074082c0062078004028035069600903200982c00c071460100b40400d802c1000304000d102d0704244203980383e8140258030020310540c4040b480c101010758041c8001403008100d24681940801c0b4940e22850b1412882e0034040001817080a02d100c550701d01e0400802c00c0c003982d07005140980c1c401d450411640e030740c40300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580007365 1250 580006115 580006127
    0xc040f2403050d0306051011010b0919062c09010b0901180c020318010c0f2a05030c03210706020406030518070609090903090503030307081b030714070f060e0c0f01 72
    0x1a066001d4070307511512440f0791181e5400d450390310740303040000ba076000c500e00050b0210008039118158100412014002c0e81014090b07040100400b40050000c0854a204c809c8500e0012882100d1001c0f3b180000e0b14101003504404078031900a0b0203c2c90558641da81510141300040002e088141403000d40c0340d02510020498014903030b49242d1032500115000110303504000e4580a03220b00c00b1070b840c010003003660019010744d9040b2a94100300e503842c4034800b251701503e40b9030240d4800e070480802e20308551030110f03810380041c240c030200100d0445500411744481c0a50903001d4002031000c80c000c240550140d0100340a034228004800b8180c0d0035044140d507403540d074040c42e000202d08180c1041080107681040c003041d0310906140218035110030102c2d1650304210365180024840d07505206041d00d01c040100d100e040c090000c43d280d8039081e000600442c9509400d42c160700d2000441c0d4082c000b02ea10041d03005644003c0c01d0141c02140850319a032050100525441401344911828440d0b01800b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580008615 1250 580007365 580007369
    0x6090b070206070c06020d0e100e071d0606070222150e060a1404020c0f150105091005010c0f020405090d02122706251707050c040f2403050d0306 64
    0x80e445401c40d81d003079a15000039400206100c3c0447d5241d5041c031030341e064103002d00040340c0d541d140c0000c2e041204c0280c0701d2070000c003070340b00850808500c04a11480b540768140c05038400e800f60740c15951400a8404200071079201c1d90910411042842030f019005074030340042d8911110354081c61090740c0c54400d04100036a05aa0383c40d03114141d041c1c20007280014450840d05904000c0006041c002109007281c180308014000064a40100c2030714208076280c841117501408090390300048a02e482e55203034451241c1c5005e103034140600301d01c1c030100b0841508403440701594058802d1120f070421084090340c58002072120b0002d07026a40c0c84440d07180480d02583e1900b50030303200340e1003208142d010000071904004100b070b0f04174030b0400c501c0b5020782c0d50200800d100340010b51a44103040550070b000e017000701503800018003540e0802446020560004405100d143e04460001c1d042c3d14020000004040c019544089840c0d540c2c81040358911002045040f039010b0001da444c00901c481c0c0480442c0d606d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580009865 1250 580008615 580008617
    0x82208120a050c0a050307110115080a0c06030903020a080c1e0d020c0103020c070302010c080d020a0f02010b0109120308060a170c0108160c2310050103030e010305060a21020d06090b07020607 84
    0x500001f41040e00c00e15000c0006900c21000041e64080b0310420354082d040d50308000c3c0203500030002242040f1a110400008050501d82001543d8250f0740c02504c40c00804400381c80e0850220b840d40c01003c00f4003c1c0c0d2078238506081c0307400c07181d1a0000364584803940d00c1c268034054000c4000509265019000729010b280411000c0c0140c00d01b10313401503030710707c03200031059460f00403e0164000810981c40101800c01190b2a6042440c03182d00d0b000342911004030300c581c1006240102002110318130304111315030aa040c140010709943d120089054480580d00020b00e10500100a01c040040840c8894004d1801e0b41d42c99100e82e28544003180281c07110001d03100145403c0315000120b0304c4511046030300384000790400d0300824410720301403800007050781d1200e049941c0c0004004140e0001e40c101e946000a0070144410310b4800001030160342144923110742c5030308074040c110400c40d94104800042e503000786800c50401c1541480c00007484032400448025a511011a00083c00012031500c2407100e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580011115 1250 580009865 580009867
    0x201030b030d080c1612020102220e1501020a17030a1104120201030b06070b09150f100b0d0905060910060e15061b0a05060a0c050a082208120a050c0a05 67
    0x10448132100c0e41d4800c040c109914417240e00308400080c0601040c5032422100d03400942c46804468803491046079650703510300c0c20300c03a20604201d200c01c01040c030756200000701c6d0442d6003060490010303420501d205400a082c082c2000354803501500b02400b0758011181020308102c518200c800d00001031060340165007211480f00c40000056108e80c000d88a01c3c03401800c0c0900b00411581c0e4943c4c40241910750300001d420010000b14000040e1404541c014100c1c10160454240380009503010003660181c8820020002243c10380b0b002c550f0805030001d41c0c00300866150340340640b02103071509a44034965203040d00b00180050003410700344502d8054403004211182c1040c000040200e6036010030321000741c1409100320150203010070b21070382020500031809002c8910b00017108404503000500010203001050222980300340d40b1880c030503403008000b46645a00c0c1c6800362455441a00b05000400c03a08002a542000b007407600392150007444003010601032600c40400d108618014840d0310800110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580012365 1250 580011115 580011121
    0x50d0507051005040627050c04090201050910090b18032b0c0609080714060c040f0509090f120a0f05190503040c05030601090209012a020603042d0201030b030d08 71
    0x207142e001c9070700240b0034030b40001c4508140011010200c3d4049540c40701b40464061042440800e011a00442c88126020888011207070b00180050180002c0310740507412a891110481d030050444101506104103d01d4490f0281d050440e405109081014024084e1a50740060916400000c07500382c21040b4912030003641e1400700300c40c04200e0340829546103845484203408500300200034413040d40914070154140b00d0510615107040d00140000420020800041086104610f90b01c804d8075022128a03450f0703210b07054003622b03281c0300e60310351145801400b0b948800005c00c07100520840300c40d81c645071603150144805541c580105402c41c1c0a0324051245002403510840003586c0c41407007030304442c0810741c40ba0040792a14009030800304002c0d5000480b9441c0b90381003134401940d241d08840084007400ca4040f0000600743c244402401000080003181c1008607680c1c090700148040c1c60300541805401e4400d110702d02e131001040c0c1c04680380244407c034178100840c18402246103502e40c0c80080d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580013615 1250 580012365 580012393
    0x41a04030c1a040f240c0b060f03010e16030b0108030403030f0e3f010b130b1c0803010e0f0610120605040203010f0504050106080906070c060612050a050d050705 71
    0x94084050300c1c0a60420000880c6080d140644440508480c8004044140039485400022010107034200f086c02050a21140003a11500069a01c184244c9030080d00c5000d00d00846c2c003410442802c40c3d074500400d8840d6a41c0c400c000c4000301140c0c0910b80300300386070341c0c2c4103100c64a038441d501010340051682e8146030000c900401d21082403501c041d0035191295505030389160b002c1e9139110200307210441160403d0261446d900701c0e000b05107158000b004243d820000045006040e5103041580c01e40301c0340004600d84d82c0441b0a400d04080c404c4075818015640340007915503000b4041c15014030004804111079080c580412803180c030f005408010a030800c94030540e00d0303405072a00c1803030b02911200d000c20b540d11940007441c000c00250070034403c42da04003000c00044d200140c02c0b600030055a1001c10026060024038290080c5a1742001003021015080c958080d12164020100a216000310342e010000e002810804060145040d00c010303184140d400ca0b00d5108946000d000c40e030103001c2d40b40b124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580014865 1250 580013615 580013639
    0x140c07031412070e0f041109090a1107060b1c020108060f19080f120304080301090504050a02060705100c09050a030b152106060f011d0112020f041a04030c 68
    0x4805a0300402c1c100380d000c101a5185603400c60f403c100040307000c0381c11030082c2010203841c9408002200c0a11584045040c9440070340200d01c40c5c9440b858000000c108909002c0d4480b03503e00341291a81582d03003c042c1002d0010f0510000240c1c003d40b22107400e080686d40e401203000c41151705942d5031040791156010400250084d0005950117440020f40a05191409a49030b00070814030340500368030404001c0003800c0550303a08013109007000c20020400000c140600320b90541f2240c560004141c0c444d820b0492602201903402908858009100e0007400707800194181e51449a280505c450b184c0c024044075100c68074803446400a410080a00006003184074441c0d00984c491004000403074800700003400c1854400c803e58100b420000c2d1b0890b60401401555400b20b41030f035400c1c02420541c000280401c0003044210400c04a203503e280ca03a030b206a400710b0b00c0e4420641d0540d2030318016002c5030001d60152182c2c6c860b0b160340c103008445001c141004e42d0100c9401640740225145004924440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580016115 1250 580014865 580014887
    0x50304050c030709060503100504050c060f0c1006031103010c120b060d05071e05040f03080c1f1a040603020904030842030f0c0622031401140c0703 65
    0x200d0140e503000841c540c82c00c0096100410051002003055441c081c185030402000c00c0346809070a00780340801010400c00142c00718021003c1d5602aa03500c60b2441c0c4414a008160907401c40740076044466800f00d80c150040c0301580d0048401003141d0001c4810036088500c04908d01000c50594010711200343c034294800780716050701a000324500b14085625408565040f6404cc000c503142c0c01c941400c8440c000c98008030320807907040503840c203410113007480c80c1144240b000410f11400080c503120900c9080c04403841d07400b01d520f100c603200184090800040c0460401c41c80c45295041305400b810716090046008903a0041c0581001e521240c6044501100c0104801130440034040c0584c13846031305254200c044000c241d40f00040d44801241c4614407000b47d40c50600c2640441d000161a040c042a103108400c011203030301c0e68501290503215680c00341e0a15130f4004d1000581c00105201030800700300e00001d100c1c4020000440500302d00b590081090303c00f02c0b5198002c1c0150307000030703009100740c0007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580017365 1250 580016115 580016123
    0xd061e140607050304030b011d0f010e070512100501021c1d06160501050a0b0d05192d0501361e05100506030c060a050d150314070e06060a050304 64
    0x200e0081d041d181c252131540654422103e40840100400c4400c4840d20203410044004029400c3c5003000c804000c038002041c001e030a001905500442c2c41c40d80514204c414100158010003501d00e89010070300c070000518424140540a007440044188030403100801c503201d4a40c54200c0b200c2c100e0b0351b030691500c035118101500284200303c21051030119010000c00c00d4810400401c5900d8180c1c6080e0550b07c0d0380b03c103580071303414002035000018400b1500d407000c0844c20718001e001000300d003481484c0725402034a03000e550302e00941c01101d00c941440c41d801250300480090000d080e2111002440d1014501d00c11140d040b280b000d9a034495400c440328400c2ca015100c1e86641c2c0601d4654441c401d00e0022044603d0703482100c3c0c02c41490f051380151030344414210701034118100c840010803903500c15014002e04100c400103e1152008166008141114a000d00207009079144d103040740300c00c105040150818441d40d10009000302e070b0b8104184c450300c0c0242034141801d145140a0b140b079003010344126 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580018615 1250 580017365 580017367
    0x1030e0709050c0c01090c060314070813051005070c1712060114041a03090d02060903031617040620040b1c091a06100c0f0b10031203020d061e1406 65
    0x81c10b074240101445a80102d0395121f40d1031401101404554000f2107400d07042211800308440180c100034103507400400c0f030080303200d0000c051a00c9410007103116a5202001e240038140300c0440d07071000b40a4401c40c0f16003909903105100805900c1e80740520303141750f080317440e0200002c1d8103544150103890069040e40110741c100b644070346080050f2240003050405941d004810480c1107641080119007141280c0050400f1b41424030702581c4a00c401000c204822904000f4071180382c1c401c00c040c412000022038001450b081620301800906540d80200039040d41e490750404444002da0100c4044a03240300403540341c691010071042c00062810740c01c66540da9103403140300c04281c140c1034040a0b0260300c0500100c9241080402080b05c0380c00d5602c0003000380307140c5c004e40082c0c0002ca4580c4010382054801d201d0741e0320762104000702c00c00c9400050860a003800e0203166183c260700a005071901244040c0034042e1a803400004149202c2e601d09440c0844200420042041504182c10070101034041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580019865 1250 580018615 580018627
    0x90604081309020a0210111920070e06210a0b0411091e090c131a120604020a050d03080a050c130b0301090b0924030c040f0e06010501030e0709050c 65
    0x48000c907000b44c0700b8000076800c181000744803e103591044056038042030040d24140140e05a140040206841c1d04100307004560800c4c001c00c09218401070b8a15030014104c401054403421600000d850596805000c3d44050030b147d40300980c4200c0c0c0b000314201c104c0040c40741641c29210b40708940f9001d41b00744e0703154100c4004810162100e1070b68611420030700c880008142085110000800c0c001001109541c2050440345000d030786140074400700906000d030220b03813070404020815102e0362101145a001c0c16040740302103c0400840c90341e1003980212403d2904d51340e80c40501c5a02c2c42c911000400042920740062602c0b074481e8072440d004142d8969241c181101c2d109194494005a00801c1d050080031004010708a40303070050303c0c2d59003010344e00a41e06003400300d184a1030003102000c41046010340e401e04c2a1300c0c2c60400c415001241d000b0800d00c1050039030091100104509040040140110310000c19107501030301648a117541950000c0c0040d6103442e200780c0042c41d015240100f02c0c0070030020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580021115 1250 580019865 580019879
    0x819030503061815090c040803090d0204061511070503011103070f030e0f07030b0a0e190302100609020a030e0109080307140706110307020609010b06040e2502240906040813 76
    0x805200740307220160013540d406a0b0042088800d4002c144c210415810041405075400110594030741d41001d481c0c2d5043d04003d0700c00940500010303001241c0c1004555a01603003a5400049003100d03215a0056034480c645a00030b25090300c1e00d00c039070326012103002c0000c55801b901c10320b8441c07410301c02850002030b150070f0101210f0424112a02000d1254400e00302841807101502c4e05030b80140085404014001c00d030011180c8503504408940007180010301c50380b007458001c1c01440304c0400803400c1006001e031684211802500501201000280b0b44180c0c60304c030302d20502c07030000c1507500250160300f03507594850121042c0c8801401000300c000240180000160540659000e040c00086d07e56202e26040100900d040c4004200940b141e040541d6405241c8410b1304480072385001451030301450380e4600f0707402c1484403194511440f4002c40c0c0e20f08a9420750100d1300c40081040702080810084a20b014a0400801510415200c1d00114080307800580200c009000d1440009005e01090b07640b220 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580022365 1250 580021115 580021159
    0x6050711031c091215110c120d1103070c06020c100f0204062d140c0f0706020606011409100c0c06031401050105070b181024081903050306 61
    0x12030442032040c0610940c0b079a000030740c80340a0540f90465040a41903601d41a803e410b0000c81c2c908000d6071401d80c1ea5000c0b1001e021100d081d01c46000700e030001c80d00c3da440c0304402d511003100c030000b03035180c090303409900320400046a0080c2450340e1203c0c42a09951034500095005403035501c81c91042410949400c5540d000f50401d6504444005886514113400a41400002104000455030307403140e48841d00392444081d11103100b60b20b00000c500c00110080240c0c2c0c4249004a80c0b180b00d8040d040c401140001090b2098424581c02d40e0400d480b240c00548090031ba50300302c101c0d108030070b10070480142007100b00d480910460385030150001c0029161114140102d070450b0000035151b00c009090064640156801000c080c03815a181030180e8a8080d0019800342c000c85629600028280180c1400c201c0d203a078442c10740400b0403403010480300684056940d015910300003170f006100000c0705403011a044da040009102041001e40326035800f01c0f45a40700500b40e80e4072014088948152030020a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580023615 1250 580022365 580022383
    0x50a11030d0f020913060e070503150a12050d0201110d0504050102041d070809060f060108070e0a060e040b060c0d050a050d020d0b1e030721051b1c0206040605071103 73
    0x80c0c4010f0765940480c3c14017901c4000c403100d111610382040300c02c1001415002c110b81c1d01c4541480d049403640c0310b03203001e550345401c3d0140d0380b83d1102c1c120740c001c250030040f11003000c4207074840e8040724086040303100160b090341d091b2400b07005040c030103000d203008650050b0004d60b1710074494000180341c1901c413524012101d190030110705860400034100015160003c0e05240c00c4030400c1d004080e42c4c500b406400241c040010180c60401842c40045003007070740141031154500c0801022001030503102c1a0080541d40c02003002c61159007000440641402e040c000ca034419207040700a02110107503030b8810703100c0390b02c1b450101040002c200490320600c00310340b014045086151101141b914280001c212440c21a00640c101e882c810310013a0580c1e6800141e00c8003140c00000420968140842627542007800d6901c0150160007404894586500240030394501078004072009502184d14804900f000100100020b400c520100014081180150302406032180303e03500040c0030307008290201e400e0171a92 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580024865 1250 580023615 580023641
    0x7030906080906040b060f0f0925090810050612100902151207121d0604020109060c08120a0204030614182d07030b0702101b050a11030d 60
    0x809000d1000d158001c401c1c541003803000c802003403036003445e07240c1c1440c1000140925125111031502d02d0030903200c2e901894001200100120600c0c5401000044084c4051283d100c00c0c03042803410702100c1c0d002e28100700a403900c0c00c004010921003604004010a0080d1109034041300e02000c048429100300221204c00c024a0004542e400701841401185004c03041003102204090242e48030b83d40400d200e056001100e03240107250300100810300030003004072140e120240c4e1080d4007443c081703d800280f000d0140f03100303036a0100f60705ea480e0402c030703078240486600a00c1342a040024030407800209034030743c0d0488100c4c1001441c20f40d50f940c403a8110345090226200d024071101c2049081048030f00c0035500501e031900036049080038113800910035008025a55514541c40c0b03aa446143d0081000b0805136a00407501800e07030503c070b400a03540d5100260481a19410185408904a6000445c4003022081d4440b1424480142c0301a2094002142911214881400955041030190081000107112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580026115 1250 580024865 580024877
    0x111070f030515070e1009050d080316030c090e0403120e1015050d06091110090e10030309210c0b071b08150c09030a060f0b0d1203020703050408030703 67
    0x614905a4280040c16400703d8603031000700b040014039074001541030201001101c88103038451505c2c5061f0b501d00c0c0c054000c6500448044d190104010344078000310300800c1c05d41b0490002c959400c90803000d559075a0580000595070b09070030050031050003d0180c1252080c2400081080c0d101d2118007121007401d000c480c81e6014400301e90384280144038503481c1c14240210b515070039051030040303030029a43c440c0081006688030b10920030700500204482d0500001443c0301100d00000310014030181c1c00b8090030703590180600110700c00349815441d54044039451340f26402980c0c030788450400c03600141c03681d10160f101286001070009042c69807003c0680b00c010800c80d00e440c12030400c040d08009032403040b02eaa041c949400c3c0603041000036080400003c10b03888100503516240202d006010b00c0d02c086426114042e6482d04100d490340145415040e40441005810b15010401251000850000e0002c80c1680c6450112500c203400070302e10603000c1e00f00341d4a404c2d80e64443c1455940301c000c040e000510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580027365 1250 580026115 580026119
    0xf1227060f0809061612150305070f0510030e1903110d0216150c0516031401051506130f14040c081b0a0e030316050105010b07030804020f0111070f 65
    0x70700304411035800700982c03a00d0003491400d040711540e150006400441c0340c01140c0350742c3c10b201e03114040110174241c0c042001d100c292256504407501078080c2c081110540200c0c4008039801e5501610601119070040101c242101014419030042618144c0301c5c1450203000c0030f01074007081070f15214903c24880c3d5900d06503100c11100060a091a0a140d0702c1150402d680c203007903400d0440074000564011402c4407468018a0303c003070b0360000d00e00200510030b0148070072402c82003104080c0b001c00c80b406024014000c10b014004582242c004550071501c0c0c0d040c041030207072a410325601074501610400e1300c1050384c68580c0d08881d01391845900481104031030700200a07150400c0d0041c9100581c41d428440206d0420b0802c4d0b110001020200500d622008501c0d070047d103105180548450b0703805015669100012502450718049910040c6c038190b003400c0001071528481e208a501042d019a07502c007064840d5800c01240c41303403551002d410403075001c070204100c55050043c1c00003088100d07107841c103c80c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580028615 1250 580027365 580027367
    0x103020405090f0105100c0c030b1305060a060806010906053010051803091c020a21050f0c0f040906060305030f070308102402010f02040b0d050a02070f122706 70
    0xf8040e60511b40c1000260013260740000e808130010029640e000c0407080c0144e0722001198000100b40d81d0240051165200340074a10b811640018240c603056019a1050381e240d10214003a41e00c01d10605401540406012100c0100f000c4c03014400122882c2004605941124591030401e007004070707810240e581c6e4140001030721401c0c1c03420070840780c1c0000740d410542030307500107112750521900c003c086071103442120007159602480d40018010104207000c0d240d0700303180d0310100c2400e060300480d503501c294240510300c4413000803140c071503040081441542490030002e01c009881c501408503602d54a46c4008400914180041d00003420080300b140d4175400941001001d00402414860201d145100b00b0b009a181209441c0c1c0f42c02e20851804601030744900301240180051010900d038503202140104054200400900c1c01e04c0100303105200e40d4680c48800f104a11444000415141e0302d003489100113010243c4d44050614642010b108040c44c400f0084036480078903454405041039000140016 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580029865 1250 580028615 580028629
    0x18010c0e0a0512060f312a0909030210090813090c09210b01030803090d0e0a171002040b0d050a0902010c0201120e1203071b031704020103020405090f0105 68
    0x1040b0407252401c110f0140000d0986407000600019a40038a4000044100202c855892088108550807000c1000c120f4450a11003150010443d2045c54001184111000703ca031200100708042c0c503007401c480d250100d44030007420003400490660055440e4800c1411451003a02f042c18010074846680b0348580106103400625034000300a410b1404521900071540000010180d5810801c04041010703a070220f0146610340f200002c0000703019400110400121902031805914a2000c40c1c2e80e445200c0c0c01610051121030a141d0414541c10040001890300851449410130880c280c0e407520b00c54207030100599015030088210703d000003456841d10b0b4400c1c42900d40c082140707101003102c0052540000c5c5440411580030341003113081c0f100c1c00b00585e0680e2180391811141022507002030280c3c41c0c4d4100c203403c00c0343c2000c04a103d21030482b03200048026440c18007581a23030f03070240f050125407640100c008060800d90400d81c1c20b20000c0380036150601000c1c0144c8042009484030b43c505010010b031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580031115 1250 580029865 580029869
    0x1103061f050d09020109030615080c120a0b060a0305031815040506120901020c01060602010e0c01081b0c0102040513091205090a030204090f020303070b0406060e01060c080318010c0e0a 81
    0x29046040320034015540e8828261003154280c103030003060120300350004032040942c41d040070b0b0101c0e1412180b1401d03102090758010403110541d083d61010f06000003000700f090a903e00c0051141c0054041d0000940741c000002d610610040505001a451740c41c0e240c07a5070000d500b003d8440190381d1041d1040e142070180d40307000c610b411100a1810b805c0001254050041001091001041d100852150807003901a910b500720144000c2000c03582e00e240083c060582a020501e55000d0906401c11755440780c10628440d03003d14664243d400b5a210868030142c1c09021644155542440081019602e4a010f54123104403800e02107040306190910b80344508104c006d00e130130b00074104003000a903150810800c04490301102c00207200da14a06150842d00c0404000a51600002546004018010000c0c1c2d000300c2c00340f0020407501d915100050032030700c000e01401010400c0101c00c0c500042020000799400441c030b040090360034910741d0699080d40d08103000880482c03003058840006003071248680d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580032365 1250 580031115 580031149
    0x607080108070b090105031305010f1410050f0d05010605151b06090706050c0a080a0c0b0a0b0607060c110f1b030a080a0804051e1614090622110306 65
    0x20100b464030f0716032881e6200d4602c025041c00320201c001400009800c00e040c0440b80c1000007440b03542c614030441c1000340300c021341040d40c2074030310070202e07203e60340c0154588251100a402c0c0c2c0c134144c001710100100c580f0800c0c000c039015074880d4404200e80d101e50b80595440c8520790f000548a50840420500803500c458607041680c5c0480304100f0000e0300050300c182100c0603800c00d250346003c0c10051506080c01e580003c0d0402c80009180c00b6903d0740207507900c5102d400f60400c04410f0700d40d2000e81003940e00c5000b40d181d0020083c070201000c1011948002e40f0450a405c002100c2103c88840c40c2c03d04c0c1040c0381540450f0400c40010a800c900100e2802c03078014110003038000244079642c3e040c0940550446502007000703150001e07007049401c11001640f109400c145501c000260b0b04c0320b03540c1d502028070303403045014002800261104030034000740c200c540c01014400c15541e01402e00140c03000e4040240d283d008400001114241681b01d0700207648008081140c0da4541081030100640094000310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580033615 1250 580032365 580032373
    0x303082e14040e0f0f010b060406020c040b06210f1b042612070201090b04140d02061c05010305120a170c090a06020a060c030b030a06022a0607080108 66
    0x14410300c690305884080e140580c0741c01003a5912080400d00801003035016055030b101d0405080d101d050001000508200c5250013800f072903220707905101d003031301480c4100e5015911104280310586002c1d04030805041c0d010b4165400d100900c3d1010002142a65001100c01050001e019040b0006280349500000c91401c0e071900c05a02c440d07941561040e07100b0400c00c2194246001c2e142e8841d034804000303155240d400ca40d10790800b21854085a84401d404901296107032070001401004003003645c003107807401c141c04110b0444183c00c3c0010030912001c00c0741c0c000d1040109418404a682d43c003411031102c041c000030150b040d0300e0a1807400c80402c0004c0c040c2d81044c04110802a80508070b410f103c04e0300004082d00c1d4488410a40050045407015507000740110b0740400d519a002903601c89550244000b407045141190040e0219100600d078076805421961001c00451030540041940c921035015484002c04100040c94019940807110403658100700e050000c0303507900c03030111409000500094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580034865 1250 580033615 580033681
    0x614010e0405070e0909030405120319142a01020301091e021206010f03110d0c020615031b0604090504051f0203071704020d0f050f1905060f04080f04030308 69
    0x4d8544007400f441a032050b44907000007149080140103407070040030007901d00c88800324645100c94998000b00301c1a0384516010440309803092082e650940c3d509000700c01280b9004161302d594068070701d40c203a0081c83d0700c90305411a20b4010f09200440c020074940c5800591480d0190f55455010b0208609106d41401441001c044a4440c8400b542040003401c041b44408203000d400c6e0042c20112a91022405c00415070020004a0b074200362803041040d425558559a25000d01c04011003020009400da44400400110208904100341c2c1d9840010b0600b070800d59a0072544d02600da048070111419007150400c0495008203200c0080240c0b0108800d50035407401540042002461142440d02503c282c00440c0c15034840300e0b20001129000f207000528105070707041c581d9450308050f101140d02d00c10f580c02e241d220b0394034110a030b0141d64007001525058440c4085011800c4000d0000d8500c85010001280240303500790052008501c603442d42907d61400c03528140b80601c240040f24034550711101e603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580035971 1106 580034865 580034867
    0x315030708190b160207061101060e010b04050a0605030f0a05070e030321090d02060412020f0a0302010e01050109020c0309040c03020f0417190825060614010e040507 73
    0xb002110b030f2600007400c035001d8820132000b40140c02c04102408024401e52030294101808800401d160ba15800c501d18965000c0e030041c0741c00c3d50000350030000d60808200c0000200340d01d0501c2410f600e002100b04d2030300e8400403d0715076003e40d50b000040100d8091507550701d08820140c22203469000d251860b81604888071003040f00741500c2400203405082c00070748010345c008242d000e8021a00c2d00c0c3d07580903414113107001300c070254090a142500134450400c5019040d0f0b010b0b03800410a400c1e510b0f044c03421100180c02c42031401b401003081d260083c5001044624a2205a500160500d2840d504070024080c41c90740c241142c85c0090005a45420800c101501d42c1d5460305880e40c0c01446403450341060411080100f5031076050041c2c40c20480f4003544100656070011040c4c003515800c0d5110011185582c01c040c1003d10780003244070715960301001ca60160042174500b04414145400 = true := by decide +kernel

theorem cover : BRFrame.Cov 579856115 580035971 := by
  have h0 := BRFrame.cov_init 579856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 579856115 ≤ n) (h2 : n < 580035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
