-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1598
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:46:59.527428+00:00
-- url     : https://prove2.me/submissions/5e31e69b-c848-4207-8cad-1f63f788bc6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287230215 ≤ n < 287410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287231465 1250 287230215 287230217
    0x9070504050a11030f06010908120301060906050306010e0f040f1d06010b03041a040c1802130519060c0501020d05010b0c01050702030306060a08042f040e0708030f0a0302041805090c01 81
    0x11000401c3c0802c0b00c0802c82e68820343d8424052225603640b00180c1d81c45c150740e01b01c44094801d400f81108280d107100019070603560789848030350043d69211800c0722140f0044032410300040c01101205100e0034040c11540d90301400400104460003540311001c12180450041110400b00c41c507801c070303440824041c00740501140c0e902d081c40e61401d9190b1800e0007910441800058401e0342c006410301c08c42200720009807603580d03814400300c481d00c0c0b031440103501f1070b4008101110410344009600e00c0d01da000411450000c0d4103000b0300702c2c94020141c80c04142c00c402600c40755020061264604010300c1114040c1403140b00041d160316000000c51300710383d030040800e0155032080091000c10340c0e401e030a031400300000f0b15000800e80d0315898000c100d4400d014a49211030034400c0701e00a080c115150622110340e0641341045040300342c40300565940d480344140505a001041780a0200e5692401011118110304000d85016500d030b802185c840c64058480d66826035030000e00c84480c0060201c17860440003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287232715 1250 287231465 287231471
    0x1703070c030809010e030d05040b10060906050c19030c050d0c0308060d0302190501020a14030609010303270b030103021e0f010503060d080d0c1b05071208040e09070504050a 76
    0x454000a444900a11000703014440882c1c006000303070400b504624100158542a680c0350b040c800140c1020f0482543d0403140e0000070301c00159030700c143d10354403400c40e811036850b52509880c1c44000c0d20950700103841c1c078003103000b201c140c003820705c0681c0c0500344090f10030f5a8000149580e81041400c00218485007410418066110300c04a0780c4606841d400c402d082742d8a50a40800d8502039141c010140111800d607900b403a0b00105104040d400751100c98465280c01c580140300c107030104141d1008682c01c91b44a92114018004244074452440307404060300d00f03865a5060411440003199941d90105a1105002005104500305102d4400c2000c40b14030506a00c00d580000054440003905000c03810804c0200020b58070f60b0300c1d080c05500c0c09801c141c20640d24100100114007502e007411200011400803041c2001140240d0004104030f82c002c2c01800501d03082070080420030749403e60a03a0700c8030b010300c0f0100e2909003e04a00740941101d0000303007001c1c0d00e000103004c190b036001007200c2c03480d43c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287233965 1250 287232715 287232721
    0x30e060c07080a03022a06090a0f0b060d0f050714040506030d03050a020d0915060602030a050d0504050307080c0d141602040f0204030506100314010b0f060a02281703 73
    0x32806095690565100450039180e8503003080c01c4000740200b14409544c1943c0b03c4103045c07182d5036540c00c421990030303c0c0d06a4070b65a5441c84e0440c1d81d4400709800a00c1560b0400d509804600c0e24226150012401058440710300311580f1a0903421030882c60a90312a0050903040142c80a100610030034200d0540d4103004514002000a1b1204050b0243c402850f4540c80003440310603050341203d101c800090002c10412810f41402e071884002222103049a0b03207000000b1540e00d0000041d505138844030303520a441c20403130902e001d01030040030300101c4091200388111000241041c1c060030304002c030307a00100b500d80f071540401840d084104042c180008800c01541000319100c0c010244104e0301568042142c5a540f00f201c00248910b40c00030707000e4080c41050080710903d80d00213004403405825218020154002c0d003500b25407003003c550303500c0f0503645410110780c240030700070f40035a00310b80c015654002d41500c034441c00c407121540c514446094031a80d050400503000209011060340200140c1146 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287235215 1250 287233965 287233981
    0x10603020904060f0e060a060302090105190b0a09120303020921062a0703020606011412011a120709052103030612100603080d0f0b03061504020706110307030e06 71
    0x308082e1000c0e0001c0c0d00c484182d0b002c0b040035041010b1130700c800f03812501c1d50302e40f0f141c0580013005070307000803403007043c84500006491030040c0141c00706820840104c3d04a0346812907c0d10141e00c0701c01841d080c0641c140000845841c003240104049000e510050f94808941042103d20184c00740c0c0000003104400c100010640300041240d440152401d000c0c070403031003600768a01703403084403c50142000d000103589000c0581c08120180104c2e0281c82d400040c02c08018001d140d401403101e0341540030400b170010402c2250560814229142000302c2925201800d450224240022a611404140144010886800c0c8583c2005109419410306425445000b454540740d10000c0c0c005486040400049458054148140e038404444840304212590340c03480c18022035007094065440046c0340c4106000590000d000b030403d0188000c0203020a540c0b0560310300f0b008a0502d28040c2c000d582845030100082d0140b00d0102c41060160020b5180d280c610740040944a80006140050f0802c000f40210340d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287236465 1250 287235215 287235229
    0x1404020a0c110f090a0603061d0a03030209040b0405090106061e08270a0b01080d1b060903201b06090a030f02030a21090b04050d0209190219080901060302 68
    0x1c2988042c241004841c5100054900c40f08045015031042000c01072000c3c0040d19449201143d204881c03c4c08038131142158803c90410000e902d201e11b40144410a0005e840780d030040c01403890007807000803d07240b400040f4040b11012a4500d20981d543c840502070141c021183c048007900010300383d0410040500c006042d002d01518940a40991508030300c1103081425035010081e490701c01b03c40c5646550301b0090b2010100b8400d000ba540900707500001801c2c40380303200d40c24001e00d42d180f0354420389896440c80001c2c8000c2c84258100315495092000000c480501502c04601c4040281040d4212020764409201940200e40c40303484104016280307a2038403501a400c59401c4406a020182d29001103410710b0070040f40140b0444440400e40701c80309202c01000c1c2e072405150f840840b030588450445d40588a180111a444046840750100618004580f50342c0420b0100514a141102001c030f40300b039800c4041c2020a141405910540f90b9601103130980d171140010b0001e11001e8916004a850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287237715 1250 287236465 287236487
    0x70b03060105090d05010e060c0a0f171501020a06230c030103050a1e0b0f0106020c0a030b01090c020304050604060302120a050c0307030209041d0705030f16060e030a060203010f1404020a 82
    0x11303083c00101007091103402c0d8002642000c14905407900c52405000b40e0440e58170880c2541c011840a202c0c003a00c1d21701c502c80313005c02e0364502c900121140e102c4000340d2101c8260450420b0461140c49030f0308000444038014030302440404815070041419200700d41907075040003451201850401e000400100b4800603600520507004201041c280c0c1c107400d4038201e115800c001c0075140f084d121050004031512480d2041c100c44182d82503500c060941010402d20300101c1c071024044040060040c406800240c0c020304d910440e600440b1300e00ba03a524040341494000341d00c4000441c3e8007064444103908141c00250b4884e07050b0500300218917001000307801e0f901019010f5010554040340c1c58230b25071202d901400fa4000f40c0c156403030b0b4a030703070004800c0e68920107806018020b0040c008546c1c001440000d00e400345001c48400072001c9828a40308542e14014551490360620422036450301041041c4002c501030700104041440d00e03800c000810008040812405006038810030503110303404e0340201c10b02c1c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287238965 1250 287237715 287237719
    0x2030913020307020304032001080f040209060f0a0503100e120a0c03030c030902061201150903020d080a1404080d0e062502130c020604140109081603030f0207080903070b0306010509 80
    0xe02d079150844200e00d980902c0e0070042c0f0303240d10f00ca03401400c0580c0316100301c0c45034001da85810303190780d94903917400003c101a1002504003080303001040c181e140a80b2a03c800c04005410203241c0d640d0b410010b494280040d6410031515994500010382c07100a10101880580200005142084122000f4600404410f003d0201940c4514140c201c038070980180d185550010280c030f464200c181041d44140c1d000384100c0f440d4900401800080700d01905048040301d80040007896101015200c142c0180d104034074060070131450209085612001c900030b0800707000d0301c1c0010f00e00c44260000140000c1401c2c006035100c1c40e402c1c0120b007d0441031402c91828034074040d02c803102d20302c07251001c16200800c01d0340107039507030b0300b092007034250650300003509403145000303942e0780c1068010f42012600300c5161820151a1031010070640c213070b00b0880300b0105500c5205e80740020301d86507802c4511040341c200700821240c8a00015000c01c1c940b17030800044000e002004400d603d113040c4072002030103a20412940b1340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287240215 1250 287238965 287238967
    0x6050f060d11011e080a0c110705042a0207080f061005040e0f100906060504050106051b10060e04120f050301170a0c0e06090705401502010c0203091302 67
    0x26040e40b0a0804c4c2d1810308070040e0403510070b41d100380058003140302119a401090702e44280c10312114801d6200d48111074404d0080e0659609050510019009509803054030000c01e885030f9808000702650220208199405440300c241410045800c0c00103020592840e9440b610521095100c5c0d03402c81c02c03c903502280c000070034003025003403241405900810300d00745002d11040c000c01d9101c160010500507100300010441141c40b030040204485081c0541c06c0051410f200a1441608410706041c0c200806804c541c48036580044110a8030000c1d000b0f41c00c0d401c850001c0c04204042035101c6441000d19040c5504911a04100204035020504c210b40b1183c00c8000e0600b20108240092000c032908803c12048403922282380071520617099801500500c9080b0005008c244503005480f8181002c1101007261882c2002da00d1600c05512201d880840703020b00901560805460108010000c40c00d80381d0b40c130f41031002c010f821250300844510942d081001080250760782e0110103248100060001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287241465 1250 287240215 287240243
    0xd0203030f07021e0d113403050304080d0806121b010306030602040b03041101090e0a0906020904020a030b0301180503070f0503040b070f0204150506191b0f06050f060d 74
    0x200c0c6072201c8000711407400780d0703084500c1c64100e40108000c4405c0c80f040d15050401c4050300c000750b55030030840c1c0002110034103031140100b0f060014849507001c03a4280302e040803020b403251107450a50f403140d03002035210751062018021682d00245101d80c000c10442d52140841c484d803803403a40724600f104010a01c03180c4911158116800b9a1200d80071b5a0084003c40d140c90321100c04a18561095501380c0f44119514101c0c000c540c440c4002d9415218a00c4140e911511401c10000c094a81c85400b261060b800303002405c0982c54610191154281c280c2e004039a070080c0c0780074582140c00f2000b81c0a1100c8501880e0b1001c40e43c008204c4002c1580b00c0b10468500707049091050441c0219004036041900010b100c1c406d11070000d14560885008071010003485a1408030710a10709194032601e504494148152001c040400d44c0c100115082d90501d815881192004000b650040d4141100e4801030820070b10144201440362030361002582d4010403603414464009410030780706001c010a4004140b0030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287242715 1250 287241465 287241467
    0x9141303031e0c030b0f030f030a08060d0b151206090a02010c0614090609060a06150e0103202503050f030a110703080405190201050412080f03040c05010207080d0203030f07 76
    0x4441000102c070504200400002d40c00074050310350000b03000d00c6400c1c10780302414a0b28020074540d03840c521080c015490817090380400c1d41c82c030000501e0303d83c1c040d01403d410f001007840360010901c581c2000162140d024160030412020404030314142c032295010204201103004001000342000303409092071094a0301a00c0c0101c080c1c03e100790b500301c1c008000d0b024449407000026409000b00100815500140d40d00d1740100b0899801d0b01c214625451181c0d8030700040c0b8003469080315041c50600d40450781e6809500000c1565000c10001d007130703555000448917041c4090900e0000c0031807030f1841d02d60601d8981e44000707001d40564205070100c07000c000081004040f003684540744c1d00a00c2c0720415100c00311418060883c0c40100c800751214058000d000c2d46021620070a4515981e050b102c8a042a08241a24401c0030180f20101e9164808105500d460301c0d4240c0918801c520070080100d501e41800002400e00c504c991080c0000c0c5d002031308821026802000f620b610071a8054952415512408 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287243965 1250 287242715 287242751
    0xc100c0f2309040b03031207020d110a0206030405150c030105040f1b0311130b091c15021b0715090503070e2202100305060a050102070e0c09010903050f0105010914130303 75
    0x113900c40c0d0620000030107141144204450750710900729a001e4a4204841120607510f8151001200c41e4680044c80520014a8610702a40c1c00038021400c480c010701e1321511503180000140d8984140aa021004010501c0c01c3c0c0581d0022801e14842440581084d58100c0340b0800014011414540c90701058100600c160045d1a40034584d20110b510079a5692840c8009900000d0418010108081110503444007000742c00702d4145c0c0a1400d030090810050080008e401844185d55440c03c0d80500380c8a0080401c198000760240c40c50400d440e07004042d0260040d4004d51041d40a5000300d80c0400114409544041e40f01620107000345000c4000c1e220b41d41000300c01200250f2000c1c12417a0380701210b506600045c0b10308801da584d0840140c03101c0044e82e54044520400310500b0740c00d000681030714494001781090300e0041c100840c400f44c0740da84072410026180c06444140c1c2d52140108441d10440c0206191100310081c0741096041c8001d01d00107100a02001406040c0c80d0850123901c201590 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287245215 1250 287243965 287243981
    0x1021c09060b091018090b06010c0c170709050109050903180a030b191127031501060804210512130819030f020309060115050c100c0f230904 62
    0x10240c004034134003089241000f8460b8018a050690441010107410440d8420807a42e40d810410004541da1010b00442c2e407540e441c5811108092501800600844004100c4501c940840f02500007a81003010704d104441c0164044c407009404c0c1401d00c0b940070300c04000c88640300b00e038000240c0c43e508000c02203481c0c400036600080c81c8440c2c550800c2001030940580648030300b280541440070300c112010348186805100c1c662010301d1003c0f079000d000407200380c940161007100030341074515144031401000b41d003e0f801d038010001b154500003000204251076030b180d07801d2201c8032010701003202040c1c0b006000b40208007104480760150400b2886030412510340c10801035110b00305654810420361000100541c80058101081c1008900c2503003070440d00a8030302ca4101e4034020b024580c600007503080e00b038550703420400900c5420084900e200038117000c2114108008600801d1949100f00014081c0180b00300c4c0c007042140c5110003954195a2070080c454280a084101307860300100b00c00a40281049 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287246465 1250 287245215 287245219
    0x6040b010330050c010f050c090d1a01170d020109080d020a0216081f09111504080a0507030210050c06040803060a0f0801061a0c030418091a041401021c09060b 70
    0x76185100076998880010081c2c13815140c001e1000c2c201c9103030b010050312001c4d5110a0014000e0008140e07a04008582500b4680210b46200820000e04141d04640000381c02441c500222000b561060b160b08016003c0e800486200810a0091a44401d402d500842145a5130150001040110709100b0081e4034503061068050030072082d5141600e969480c1c1c5c1c04802c540494810328040c2540c2401c1c86820805c40d00107900403080701c0b51104011401c0c01c4901d01507a254070912020030440820031030010503e2280c002003040605600401c0f103084031003944141001010402c06e803401d000420380f0f80e080395000303242070303102e03140d00000584908440d00700112031800350400141204054010b03504640a000e101c42c00340307c00c9040001184201000b403000d55100700420000740c1e0444d82c2001c605402e000700000d40c0411a0b035110010408250341850801c00a02031000f0b110401d1501c1117903500f0030703008510b0051000080325110542c101c0860082e543c403010401886101c2d007190b0481400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287247715 1250 287246465 287246543
    0x90402090d0b09070608161b0302012c070909050c040c09180609051807030f02010215010909060b0f0d0f08070c06081f06080c1b030f040509060306040b0103 69
    0x200f41c5034107035604598030401002a002c68041003401a000c12807104400607030b5110162501d00b540c51751004520904214115036071120300d40041c1a10240e00b400c80100794819242a5250888061401800782c02096019180c003400400251001a06800c030340020703600803e02454252040c1c0352980c050340101031184002d00c1e4010000760b254411015035160f648100036030740303401c11085820404145140f80a80c00380c403081c0080390310901e44034005481441111211460440900e00d411004e13407014070000d8440000380d0400c44103015001c1001c2d82a20540055000e5000141c640000c0420241a407002c98100710103000084045600240d045140211241e540780c030000c081c03100c12618400550306a044007140b90710f042c02d909c42100e44d00e68079010203449446010900394441e6010b403c05034001d500040d10b9000500141c80b16800b04881d550b1210710f48011310070032403001440036110360400402c02000441c194aa141074a40011207240613107000140b8072000c115144400e174401e10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287248965 1250 287247715 287247721
    0xa020a08030a03061401050306090a0f020720030a0b190b0d0b040516050102030706050601030b3106030f0f020d15050709081501060305060a0513060302041d03090402090d0b 76
    0x3001004005000c841e03503040100c155a0507030a01040b49102019000a400700040303580d85c5003158410b9001080c425001400300990550141203901c808411500074001110180c07001d001c4440c1158121760035000392036024680d0f0360f50b40c01600c008050200c40b46540c0116540410694400e01400c0000b922002002d40241007012a2117400c4500312910310440c00349582c9030300700c0d4034100b00315132060b0029401c0490560301c050291200410080c105543d40c0c3c0218541d940b610b40b03503151411880042d0210350824580b64030420b400b40002c03806141001c0082001480d820040c00364240c0009600000720818800514100020300c40546131070000c0780300280d0701510780c3c052801b451158035211480c60751000410340307404481003842641c1c44600d00402c0040e003e0b410840d0311400013080300c041c168130340b000910040c0c004402c48002a0343e40d0814011420188030b51250303000c401400f000801040d00c2c0d0f0076528803400000c50b02032500801c8a5a840c1c403010494401980c0c0080c0c0c249483c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287250215 1250 287248965 287248979
    0x905100c0f080c160b0322020904060516140405060315060d02030106021c05070314041206060e060d0807120e040504080304060510060906050708040f17010e0714120a020a 75
    0xb030010200c10009000e00d0344605160340d40f02000300c040385c2544c0120350550b03503580720b20a441007960510601e002d81108103880141e48000000d88a0b505c02c100012b00d608061514400304003a0100306000d00c0902c1140150660540382900d00b00d49048502ca90b5941c0c8056400c41007142c10741045030450000300301f110030300f0540e80244d41a2000d990855400c0440034544400b044006581d200201e2410058400401c2c410181401c550310382007042e1b85050382c0e504401f2440c00ca44002a00d40310750303880d0107000522003921860381200040710428802c0c6126181d04c601c500c51600010214207000b4000c000ca40d0040b034291042c40c1009104024a251074188100340340e000701c43c100c50451131b01c2c1c0001c0c6038058010301035041e6091340c1e03151780d0f0184c03c003072042d16180e100d14400d07101d180041c00b000843e040518846000707440240040500ea012a6142d9400c0d6011000290020b405c4038400f88032a02060075189079101044511490803030b112130414cc1011015040a50007005034500444c0e02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287251465 1250 287250215 287250217
    0x50106090e0706080708150d020406170106050910080d05030a0605031b01300b0303090d030f120618020f0c0105040803180307050c06250b010e0f070905100c0f08 71
    0x1203034544c5941149940e070b582d080312880411140a03105190104c0020a41e00341100d0b020031103440500000369064580320791741001c203c4054804401d0b03464150611250030900b41c265041500201040220740c101004241c950b010104a0002c1103030110006035880401d42007240249000f03800d0344c0e680c00203500c044101d106540105e0703012404008501c0b540300656954481c03a0911254034103003103c44000c0c6a0058020f051015a142c881400007501541c0e9010940e0030f107610a8503500d0714460b4840d1301a1024400c04ea0b03692003a4a040f00c108043d414041d1902e0390b40041520060b42ca640460200045007e8215007a1056180604000801162000a6004031000c49420b9551a0f0011500f907403846031400082607508440140552810685c020780805400e020b180c3ca011501d41542d21800b854151069031081102d0004100000c030014007079400c82c040310040f12043c50f040c80060302a401d00e114442c01101d2420454070a1841107008280e0079a1150840c0340b038641c103003400380741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287252715 1250 287251465 287251469
    0x906030501060503151014031e0f07021b0a0305030c0601090b03010b0105220e07020601060f0c0b04260c0307140304050108041104110f0a030501090507050d09050106090e07 76
    0x229150400200d5058021404d0f00d1192060102c0c071444c08200c4030500c0800b42044406d181031051001d683c181c0f0703402060155200750b05400d42d03100031040b0440803400500700681100009c800382e40511041ba54041500c0110301203251041044500780004181d903481a58006045404049070710614036501081850494000c0f010a21131901001d08041c00ca0751601d00c403038080703003040215040714010070031640c2c03c1001450743c3c031041554031015140303403800407940e140050304540300510009408c28801d00010135245491080a1a01c3d600d068101d9000340014000c019955004100c20810080030009100305440c09074a640403e070303500f030741c0c0d030481507084442c2112241826003090001080d5421110305a40d0200360303407229240c00d0101c00c2c10350300c055049a1a1142c0030b120045807001090410b40040320182d88a0042e00e00a00704c40040c2c00c58101d0505000a1060f82d59001b002c2d255418260800080d1509e241c0c80e00701d005040540c80710400390b08100d0f0500310785001040c1802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287253965 1250 287252715 287252717
    0x3020f070e0106050714010905070f1802120103020d050a060608010c0e040509070e1f0b030402040e0f03030c0a2303070206180303010621051f050103050405100506030a0b070906 78
    0x310140d12900c801840d03810900401e00042c2082c03100c0400304a2000300f0000501e03ca00002801100d03644403182090351a4108880592040c01d0800c0b600f000700f019085055002ca80450428407a103030182c12002c0e041c40041e12420301006240c043c04814003088803041c1d840708040220980c1c1e2805ca078041c150b412070074800720301c0c41da030380210742c0c00c0c00e0080e02d102d00e1042001c0e011581c1001015440030300003414101080340c0d0b500700130803a0855041c10034040e0110394852512860544100401d07a6004182c010058002031071080e241381c800410b8030b800107100070a041d120b03021194100c0c1d400342d140d4012188003080c510308100341170303201c0c0045000781036560a81c1d00c01d40e01c541c40030704806c1450342d4100c040c2d401000100001440b4100380034400c8041c0403007220318010700340240262601a1442110321005800105040206407a0300009200070b0030140910320709522404c1d103516404081450300ca03210707400600259014808030308000d030311501161050030a01c4c2e0081c0800018050380d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287255215 1250 287253965 287253973
    0x10501080f0105040507171c0302031503010207050604061802030102030a020903060c040609120c170105091b030a020d0c080a110901380f0f190c020901120f060903020f 74
    0x14101d006010b0319105030b4014004014103403401c501120751403008900c001c00360103200c0c007003c030304001c0e00c4c84100c01384803a907005a203038104007002950302c01c00e0040c4c0600c80d80c4100b00042c0010008170b0081d40c0b080e0070080015840305800c000304900c4100601c000c0d45540300008102c60070340c0c00d0f4060500302e841541101e4080e87c2da1118030b900c41c4a60700904003c00c165840402464000754011403070184203510b2010400da48064078003000c400940f41d039229945502c1001854401000b1120100b803080000c0755914400d074010a480d4074101d000a0b010344c0d08180e611003804000d04079200201120340440e0341810342400d0105440050b0000184070b440d03014000600c50094920303415403035041c94030b01c035214241494a820b4010103d4034405005009016030f0f2158290031015000c00c901001d0b002c0c0e5203500c4009082034074a0081040c100b8071400401d513801688482c440641900c04280e07590842480c01d08000403a10403008000306054149841e2070100b42c0d000c0307001500100103404071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287256465 1250 287255215 287255233
    0x7050303040b0d0f0203062d090106202d01090b1e01080601030305040b0a090e0c280503190612030e040b010f0e0d0c0308030907030c0e10030807020303091201050108 73
    0xc246d00c0309070f401c01c0e0300441d081e5200d0300d0b00358098010201c2001020081304815403200210304071000907406440441c4100c1c9540360600b042203012444030314000c2c0549024080c0c2c0d403465485820805203aa92082901d034481e04404003540310020480c1c0000080708185407010264001c0c039031070346400401600d00000080e10510000c0c40605807613040d12001e0800d070401e204206280c0006140c00301308101020300188880811000700e00800d0b601101d02d9a94107490703c10b030b06c0860304039140394000750703603224a0f040740303034403500f0b50741c01800082d44108a054068214000f410726604025045401b0300000000c00d5000b004141a182080c1c500780044544100107650103c100f00b03a0700049507000b00003814500d041400340030000e00c19000e09051540382d4880030f195800481e800d444540c0700080502c06c0c05001d90707075a0014421030719000388925100e206401d00d1100b0380700c010444d41001c1088000c550301481074410f9850b0107800400490603c042d014040c002c01e02c12540d45001d86205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287257715 1250 287256465 287256491
    0xf010516111203041e18181202010605040b061206010f1101020a0903020111011506030e070e04050f011d0703063903050601020c06070209060102031903090201020622030e0307050303040b0d 83
    0x10300d40440c0c0841c8001842240c1141042c0003030712200c078100c138001f42070040c4100010184080d50203202100e6000280c81130810080c8011682c072072100038810355060000004005180c002103074003400a10b040244000d000ba410381d0800000c1030700003200e5001140341c6014035404018001144d000366200040128841c142c1c40c221041402c51a2101354410014000365020350060f000c0c10848208640b4055914101049011003e070f0702240c0980007070b20300d0102c0e19801d018880d01d014034003940c4c0740c1500c445c0d007460360764501612001b070181e07131a4581e0900503400d1a4010100d204104840001e9183c1c00240300108000c1d4019100841e02e0b01000c43c80c25440082d05610b4400b0142000d0726005c460703020012411030041c400340c110311080140d00c0d180501c1d003410300322031262a240410000490710000e8200107004208070321081034080c5056039158408080a0500e41605000e80e11701c015001090402d4260b170000f075014440014009200170010000b40224450f150041102202c2c50607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287258965 1250 287257715 287257769
    0x10e03220b040605160c0f060507060605040506060417031b06070207140604050105090402041e03200d03080709030b1905011e0608070e0d110f0f01051611120304 71
    0x212400240140314907154240c5c080044e1404502561161200596880c405a09a200e036041000010401704a2000b000510301620000c7c0004950a01a5141450229003540a248221807400c0d6080701c0440d0144018421915540341d600d8440a00400d03c070201540d824042d070386000144110340340002c408000c034200c45c181200c0200f105161a281c1001107986070801305c4000e600075402c0000188040d95444400c0ca0101061403e0641c0c501c5c42c1040c4120a8801070741420415061b265000c0035980d03c09241d458aa15003010541501c0d0f1000c11100828185c000400d0300c1080403e100302225414540200d502190782e09015076030721100e280400030755043c1c1200006da0000410f0007854050402d0721707404080e03841d080b19003e485000240b10120b4a901c181c40e50000d81d0240410ba0401c00007010700b601e0103840407860a0319200009050b0b229104c948450320786410200010400c404000e195624001017800042200d1340c42813540340d6005200c0c801446240340550100b00400b06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287260215 1250 287258965 287258969
    0x1b0d0309030801050111010f0213031b0503060402123406030e030a0c150203073b1302040306091b0e0c040e220308090c010306030203060402040e010e03220b04 70
    0x25580d050b80d44d02c0d1200568840319501240c1201d9500d9401341c155031501d0384054154a0907200c0001d90091460030400030700359800e0185c1c4080500002d05208949001076080c2d00564190b400406201201e101c035403d00320000580c00c0000c104842401c4443d21203c0030002c00f011758141e5030031566031340380306a08603909040082c201e5003090051b803440074041d004c481d03902400780c0200320b508002c01c1403200881c0e100705d80c000003245440c0140c1c114131b00184440e500f40c1174160562041218015113910884c04000d02c07551141d14410f040758011082c54054400075a8868030512070651301d4a0010700b001c0000810780184e4108010008400104036141c501459591041528007410f0000c240861100104080301960050300c10920400b46e01c080000b9290003651880c03105e0070800545814036000d03006280c101418003106201607500403d40c0f5400560480340052040726202880b4050043c1d0200b96846020200e08501074031f215087d94054103441440d401c01d001e0b194100d2422078040c4d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287261465 1250 287260215 287260217
    0x30403032418240308040e0708070806040e0129040b030a0f0b040302010b0a170607030c0203091c06150305060c07080405010815060c0f010605042d0e01021b0d030903 73
    0x20308624040000940c0c4040342184840f14850012095080c0404580310f96510071680309100003020800e8942e062402a00714030030340390404041c101188000c04184000d4032007840380766903030003c500d0210300b5404002e041c1000c00450101c0d03520412141204891340c1036140c040c80c107150886196113400302e48100e00c0f5500060f0341c4803840103a11148012940104110199940d4031030315001c07951281840340045c00d01e628280d0046c032810796268201500900140141030600f80170708082600803040d500e07800c006481529041d051070440d80c0342c10380c1040d0040c0000d40350000c0c080c074403040c620aa00070380b40200111030403071300c0d542c040f5a01482881005091105c003400113210540c810784071241c0102c1181c599040010700d800c001605540070100d00401c07a401100d10950540c000c0c001d50001f04400c4804210381b54000098041100c00c07484030048151410811025050441d80f1840b50244a500215200e80c0340181a48201d580e840f40d0340d11520848800c03c81242c4a4015029420380c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287262715 1250 287261465 287261489
    0xd0e010c1b140109080a030e0a0209012c0a090b09070e04021c02031b0a0b19080718090207020f220203060609060d06030b01080a0803060d15020304030324 68
    0x54034805101840c41201c0c1254081d10369606034400301024015410403030300540060ba6103140d031610103800c40300d0b1412a24001c0d049510100c01607511002058112070203030441810500400700d1110101654045000544c00c0f0141481180091a4440052a4811034400c01c0c55211941c12070b6540d101440b680a41d5031100e0002030040c01c1600080c1c11780c6481c40f6000020290560009003082c071415261303a400040700711100514600070443e4401080b10a04035407030031481c84130000d00d44811207180428050098081000c8511500b5244220403a01c1500b000e02504c4052443c042e6114500c117034443c40f41c03410b40d030a0750b25007680f1114945a1110724003501540c0e404961000c0d40000704800d0740584140011600c588858000707190300e2580c200700050690640c5400503180780107030481072195009004480015814130f08483d0040c900715043d0500740f000b0700c0e0030b06440101d004056034050012050204058141d003081001c606055894a0b0a00384042e02152900c01740c0300b08204001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287263965 1250 287262715 287262737
    0x90d0b180316150608011802030d031e18020d03032f180103150f080706050c06130534060e0d08031e01030311010b0105130e090703170d0e010c 63
    0x80300a00301031601140c03100101d40c43d940ca00840c6c0c211a4448010040a1504540712007186014000001d44803180d00301044865810348030140c2c00d4039500102a049541c50707075030610107031280e800c243c072845c1e0007000f400c401c42d0503142c020050010b6220240f0049424005814000c16201c1600381c4282d40a50142c04d1160300d5106c118030420b01100b10f81815134546000d0040418503d000020b02100e1046601051400b100300ced150013100d80c800010404140218015560301003042900840e100310842100030f070038107003e0300f40341000c0714100f02500c0000004a40302c0c0f2520a6141e003801d0144040346840d6a0032054842100e010b074000c3d03000c098184180005104c0c1d50242d03070441c842c520350192624507404c03c40702d08a000c0e00305801041c109400c0c040800c00c240250501d1440a2a19908220400141082100213409000b4541c408400081c1080c902006000019600705000d9400d030300941034580c0342c5900550308210110b003056442c003a281310500a414410300c1e1541c0d8030882c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287265215 1250 287263965 287263973
    0x51f260a030f1206080d030e0c060f040b07080408030a080a0b03071a0c0a060e060f010b13030803070c020301064110090815190911060f090d0b180316 66
    0x2d03a0560100f00d684180103c4d10000c2045002c0c1146802d0b10002000c0c40c0300350079185026001e11503e13110b00f0003041840110340b05a015107086800d0200440e0b1590307450300c0c1c001e041d8001c83d001030002d0720002c503120b07000721f91106400b4080c240464080156500400c20326440310300c1030183c3c0c10341c207002c2180c5000500c103090050451480c4081903c40241281d6125816600c101034041415408142805141c5818026160040802c2080b0340d10b45240e5174941d0b20040041d02c8040c040c14008800554040d00404204801c40ea00400801c10301c1c0e10741d9070880d9070504440c0040160406a45900c030984000100c0140206c440e40050400c007840c0c00810085002440e4074404024884400040c203450410510400039482c0c50380c036103545412601128900510500344815034200704041011401502004030421815641c1070b0b030700c44455010704042d11580076140d0b0400320700080e10041c00b5800880601440035a40e0320312a0254008280e5943d01035046040f03010801241c9800000f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287266465 1250 287265215 287265227
    0x30109060503030c061f031703161e050a0903061404060b060901020606150702130509010506040b010e09071b03020615010e030d050c071703070215041206051f260a030f 74
    0x1031030512846e0030925265078500c44030700030358202031840c10404424000303c1c80304103680b1094a02c1900d00a840071820307624105141d10340c0d0000d00306100300019001056841403d100001e1a08000b0038003c2501080080d84602c10444003a94000d2808202d2003280c94074404803492080140d00415064a4910801000b13050f10005100080001c104010050712100481210500d50782400a0545410468182510700003400280701c1d81c581081c01c00346d680c1100044c8481502a6021341180d070301d208040d60712140c5151120300c1000c2c502e2440080650002d89144640c6002049a001032003007001592080b4110040c02d505070000d01c02201c3d031034400d5010b0303c0300354484000c075410316a851440c0301c1c1210a5441c2c40c1c82d250400100b050a509002007072440b148462680546072510381203220940000001d230082503c0d4941000c02c03070b15101c5804241c891041d003022082119520080d103030004026803030034500c0c1c600880030000c540304041891008503400d0f41301c1c42c135048144601140c003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287267715 1250 287266465 287266501
    0x12020f0a0306090b070206010b0708030408090310021602030c0d0c05090405161403150103110d020d02040c05040609080304060801030b04021906112a061e0f030109060503030c06 78
    0x101941800c00004240180a41e1180f50b020f0180c400103410039400007414032005801c400d000640030405400080c01704030840f035020350080f801544820003c0d0019041c41e01c52504142140d0012840030311106c1c02c10710710709005200f141124501185c18090100f903c40040010380307110b0f9a00ca08000d64103041030940d500911800a40d03080c00d14000ccc000c0380810703c5401118155040d8490744400342001c102040d4580d0421103854200d40c074540c0c0700004a40c800c1c015900031182c0315441c000319114540087c0a0380e50040003840504803a5000501a402522070440000c4800000150007007010044034141c0e0300035642c0303069584c2192104003142c0742c0a00308a030446407202c0840d001a4415203404040c100b41d03920502c0c0403d100595510309041d6a080504100807000d0324114a0003850203984e040d02d0a03204140c850507201410700c1d0fa08981700e02c41803801000035000e100d00c4010401941a00c10b00e0404000340d0f038848084c1a034038054902d1040082d0700c0320b03002c61f4134042d680c0c8441d12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287268965 1250 287267715 287267719
    0x2010c0813030810031b05040b011d04181703151e150904020a090509060a0f0e060d080d061a07080702040f110a0201090c081f0203040c090c0203090111010612020f 72
    0x1c003069032652802020b881210399000302d1b56480310700b40b10510b4540140344240c902403034441c0d5298a80102040e0b0340d0103100c106485030340c1d1501040ba0150090481269442d0008907151030f1420044c1030410301e500444041c0c0302c0005800200d001c0c0e2038503401107400c80304040c60300358103c040c110900c00042c8940c10200c2c5052014840d0880503502c0e40010b1040c4200d95403200300c806d2502003800100d44002d80f8062085448850520010444510384401c645042407002804c2d21508041104184070f100d0181c9100c00000b01d929152230150004402c550002c4500d49940e2485280340139035002e0000002c1244008020000c0075140541205655000d0042c000507040303a01c0340e402410380d10031501c01c00582d4403a400c04040c4011090345c84000c09804000c2c1076040c107050410f034090302c8100d0a1404e105e1b408404202409041c01810011303080d119002c125954601078080c0d92900140f0400340012030b00e500000d00d10406009900490351050030b00322901200740d0810174421304043c1c0707080d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287270215 1250 287268965 287268991
    0x120706120b0a031410060605210a09020d0b15060307050a0309061d0d090806070906110106081e1b010e12030706140610140712020c03071502010c08130308 68
    0x4000b048141c0031100039136822600606000c0030151043c015902190b1004080c8502131110f03c0344036440800202c8040c12100342c1c243c1c1c90390382803201e0006100100020307400103140e81404c420481d00c1c201c201d0148000c60482a2500c42c81c10400042d8070044541d980020400d01041d410b5502035040300d110148100c0300461000e618144060420703440108460780e6902c0005130a100030b4000e01040050014200070b0000c41c40c103000050100d601c140328000401070782d1811800d00e88002e43c0600040c01181c0241e40d80020410120844114410603c07000c1c0e0003140070341201030b03036560300300f031000f09040c0c5602100c0038429041003494801c0354000a0f95010070002d24000038141e104440d4450302e01d2032440317141c0c11b01d1024844919a103000304070078800c034100c0001020142c0c10039107540c2035005240707020011408404a091622060b48903030144680d06000c644120401400c0e4904039440d8000c209082e5120b004a40c07030181a43c012800d440c0c904014000b00f032007121920f0740040891112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287271465 1250 287270215 287270219
    0x15050907051e0a0f021203010b2809060f02030a083c0103050c0d0308040f0222050406052811040b0301150f030207021e0f1806120706120b0a 62
    0x401c0681003402c040041c01c640040c4580b2255000400c0341d05030f00e524402010410810860ba8502d4407040c0034608000e031001c529444400f505800c0e006d0100b01c4414461045112501c015080362454000c3c000070480050200d50818800419a5040915a558000340792100f5421030305800e22944400000c807400e419404140602254000d101003001c500484a9855403c1103070420300301c015414070a40d000b41c114008070781e0000f14107810580201318025520b8251000074a040e603040e280c003001080c080300300d01c01100542d125600c00e0380140800d09c0340b503954042040002d00c081d85c800d031400817081102800c5488941c45404941c500d420085d1034036072904440e0705075070426031190615032040a41070786c0f904d510041e2060b503042d0368202981400c1050303000070f4500e450548c1d00d14008040c440d500b00030341c0d11401c100700c10003000781c20842020000c0380d074080541700880b01c03140600000c00700c42c101d0141c0016040111041659021028a06e0068010140a40340d0001ea4000d901400c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287272715 1250 287271465 287271487
    0x6042a051303050c030705030105160f0216031a0a05070c0308090a1b15030b0a060509030c0406060306210b0c0711100906030b0301061a0c0a06020c01060602101505090705 75
    0x9000302560140c2c0081c410b044c0b81004061426200f81c02a42c081d90611003404400340c1419405c1e00c4041c003d04014101c81c8058200300c1c5044401a102000841030b0400001444109076640c04032210b90940410507503552000503098070f005503004800141c11481500120323104071502504400010240d44495101d902c0f080c8500162605000c5001e141e54010801c480700003603080c000c0c2d061030800340000000f0f900000d4807840b1900c29081800b8000a003041310b0794050105903030341800284204030441d100c0030028003c1140340107074051000c0480d007064000c48807000101c0031540c841c03e84a081d60301d220040c0e0903034010b10b1007240d40300c44941a2a0341e82e65581d0a0100d00101e41d9940300000d407408000805860041ca0064000d92400c0d00034001d8504d0803035885c2c1d010b4030054901c3d50782c1c1c9110b07106030b2401074505406002d0307070b02c04a4018880034042d08100c0482b40e2a070308481500c48a440040221030048a10481c44140c09504000b00d045c00c01d101c651082035400c00e982848000d40d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287273965 1250 287272715 287272747
    0x6100e030f0309030d090f0324060b0915031605070c030501020f0d050a1416050d0f02120610050403061112070c03030c09121407080d08090606042a05 66
    0xe2140c1a000480d2410640c01c00700a0f0440e1020742d0328081c0804d038070701f00342c02d141c40506000180080340d44498903181c810481a801d400881a180108101907071001c0c080c01603000701103918805c59030084251040d41c41b000580380507503001007400030700b0607001400307817400d5124520494140c0407040000000c66428809045107003e07000c20b0a5580c29110084030440c1c0000348458000c2d8503040407d4202c20607070380b5041e8004031003082800701cac4a2070482071715140207244005103850304007410501c240c01c4940262041d10404068104d154403601d08002022640030f04117070000f10144800c0003c5082c0e034001c000300d450981c0c0258548151800c0100f40304100310b5100001c5010700b0601000c2562501c41c00d107011a2916102d030f0081d0924164142450000701e000d824401002d0902289100502c0b194004180d44011200008d101c001d015010a10407183c0310314500030400040d8080c02c050082ca450940604211542040d007a999404a600081c0078542003100a0243c1072041e04803030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287275215 1250 287273965 287273983
    0x6092303070305030d1b23040812070203010c03020a05030a02070812010603050f0c19030b03011b0807080106020a15050a06050901080307150c1b031704081b0c010806100e03 76
    0x1805075541d0440d080b102d1055401c04206c49060b044c0c1354218840d01c59004510302c00d090b20904840720281a6540122000e0007a508901e80500943c006041c00b410001d005256081c0700350001c5c0411390902006400b280a041100c0020450800004101840c9580146080792048900c2814001454040b1904050136005100800da4030001c3c030040c1420841a81d521040f1251558503189414120100118020400307406041d101c0e428428141e8080d045400d020741901c24056621400340002842030200f0b03500c00d804a0680000807800b2840030400b590442e41000c016030002c468009080002c2c900107210a5880303a640801040d00c0e50742c14030450090901c00011501d91400c2c0c102034104513141d2501205580c0707000b220055039500240c1c0c1011604076050300400146841c1401d0740c0d01105070300302c10b1030407042c041004104582c100107044040901d0300d101d259a00d944003400c0d6940f0032501500d022400a00c001945460100d42c440c6000d0a40c0c50182c0040c094000881e18240c104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287276465 1250 287275215 287275223
    0x80c0403080a03060302041409101104080604061d0c0907050304050c03060412090e040218040201020a05190606050f0a0b0a1110020a0216030b04021005070506100509010f060923030703 81
    0x52904009507c0c0900418a00780003410340341600d42000740c0341302d03660110401001001d50711075401022020018050b14018103840c416151f083c501460b10100401c40c0700c003000d03d08a0703001104403140200180003640741034003810f090303066119100140e41030b8000810459042c41180842009034406002c01405640310340c1c2400103212003a8070103407000c02e40790003160380400500108030150b514402c80f03800390a80e108030100192110300040341000c41c51403000d0001d12030120005600710030950078444103402072004000b45a03c1c2d07000c00c12801a40d903040c0d580040d8007001400110700c2d9200510580c052401c0984003844400d070700c5405c2c1420fa00004240903804168212104c1d01400400b240e03400780c5071803081c0542182d40355041c250001d48064025240141e0820043d40200c0071280c1841c0c102d000c4451b140f420b20400454001c141c0551030141c1104400024140d0b124014003046d10b9a984900050f141409131041c609060001c040f920030001c21040c00543d201801044050342c00b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287277715 1250 287276465 287276471
    0x1050d06150906110d080402061308120d050106030603020f0f010315030303060f080a21020703080f0913110706050405210a0f1e0f0e090c040602060c031501080c0403080a03 76
    0x3d440e401401c0301000c00400c04442d0007600c0b40407040c5900444156219a0448955444240c14065851203d072182c04c0021148100a20740700320000e130702c01804000380381290a10843e0f80f00c4031b045041d1440c3d813100070740042c01e41d40b801506103811018034680da01d040c50009030088261002014801c200c0d803042e0042030381c0d61000e0010950a003c04000b5021301c0e4010400012103588045080d402d4507008072007900c080c00329550042c824002c0c000115000622982c4550490310785076015440807407480c0c40b40d1144000c5540341381260040708407080c104e695030b50816642d92180c2002d03140c020000c45040c06900034402d658503200d04e82201c031180034030a080c0c035003066400203014243c00042da07c0a1100800f9800d09c584001441444200000c0c517101d0155840d034042510701a810155559100e82c4005c200002054a1006003044902990880706a503d8843d0420075502c001e5807280030300710500030880c403194003038070070039800c0355403010301134600b84e542d8490f501d09401c0307405030300c0000303403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287278965 1250 287277715 287277719
    0xf0105011206060801060501091a0d090c08010516120e15041a0f0c040b0f070f030201020306010f030b150a0c05010501030f032616050403061404170708030601050d061509 75
    0x600c0b80f28040c0a00b60490007006040c0c20130002030b141c40280d01c10000014940e034901c026500e0b0070019500b03000000e01043c031091610703140016000032a0b02174160305601e00800102c003642d20040490b01c1d0400c0d6103d0020301500800090003500002c0f420100a1081d0206000301a1110050511890007079514442c8186d89641c04c00c200440a008600c403000c050301032100c24120308049034215031880340300590700d001c1d40242c0b481c42d000f41c0c0000751500052141d0001450380640040d4481c1200b40d90781ca0304100020310507000c030380240305266000f6403401404c41c00c5c46d0f41c000c001e185250160504202c8002c1954940e429900300360400c88a2609061201c010141c00400600e6001b442c151038091a001328001c02e0000c0740000c0100e101c6915000345d5241c054024000c0f500038580000e8103016600d0f4040664140c07900583c1d00700c6d0403a0041e071400c0307c1e88508400741c695440c1d02800c0030349075071503030401120b00d500552400c3d0741090f40c44200003a101044130103800504010f80303070920668 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287280215 1250 287278965 287278973
    0x15060c0c060409050a15150f0309120201060627050607170705031914070609170703030501080c0111061b0d060e0405011406010e061b03040b04170c210f01050112 71
    0x180700d40203500071b400c241003040c401d500500f0400101825145800e80e009075500030200e0151080c50303006000d00010a0307110a11a5040d004142a200d0755181c1c1410203011440380c44602150014450482542c070340b00b0f010360304c0c04c0c13401070440740c2c0034100a203598855800301c1070705580402c00494242d0300001c1c00b6000c021081d085040c05540303030b0400c00c07140c14504004070541d00c140000248141e580e83c040e1010007206035802d100b41c20401c00450b803500008d10b80a001890203004d2441c1511070312210203400c0d8031400007046424040800392155454680c00354a145071308000c460351040d000d014040f26010180306050040c5194826000e060038079083c4242104c0800c110303510000890401c2241a90b080701d0641803c02c0190b4100390b44600c50212554654a0105c80c0d10040c0800500090b94041800180054540ca140101c03c0c900030f0300d111340e54a070541614a50003c000d00010099041801c04c12812031008400f940c0044500501c2d243c00c44500744c0000c2c10400d007429030304041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 287281465 1250 287280215 287280221
    0x810020309100c1d0405070507141005090d03150305070e07020703021003020304020f010c08191202040807061101090302100c02100c050315091506030606130b0301091415060c0c060409050a 83
    0x192010785e41040607041103140109a4400c84401402d04c540200015954840030010070015801143c4100514200b18100b0780d11014804081800a810500e40003d085055103080046a50280c001d00109180a80216504200501b003000b58010900000050384690b84e104003c401a50b40041c1d41c1d03d8244108200c28048000c5e09040200000701c040000342c80c04119100704800b00c99002e244030020b0030071603015034503010b035510841c00802c1c00291420b00060010a60304039803160091080407945c0642215100d4201a0061340412407004041c0c41d150300030000301d09a84107590f00560014a220140c610710006940040c1c0000700300100006510380c6d4240c0ea000440d0303001c01e1420108104014201504051442480c000011682c0c9640d500304440381003d68031140328580350b48481c3c0620030f400074418500d035982481a00d41600c4d0f219a003183c0710f401e001d4010782c2017a100d90305001c4a07030882448640f0350b21929000120542da1480500010300710500041a03d281c03865000342a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 287282715 1250 287281465 287281517
    0xd150e0a0c080f0403120b040209060f031021120e1e040c23030618010b0903010f0b010f111f0207060c030903090b0d060e0901091103070810020309100c 67
    0x1510003480f041c07000095020062004403c600309000ca10707484d40c840090024401c035181160700007000140e40310b04010900155202da40214800c02d03803140e403048450030404180103c2d210f14418000000f0024440710f640346030601661030315110711301081000c50950301c01c1145628070344503510181d0040e45064002c40a45954510789241c0f104550000218004400607490045010109c0000d00c151a0703880c10142e40c1038158046011541e49103c0e04029900c9101480d02035401c1c0002c6850340d400313600a07aa90250181d5a0b0b580320005550200c07829001031200c40d40758003030b401c45001846210b41181c41081d00c4801c00503969241403030f01c60304a41c950350a260901d41400481004250030182040440b1581c40420390780d0b85201d6a100020b06040d00030203003401044003800440f400543c049001c02d44100c6514135030220b5181007641d54200c03445121480d07800b400d80032550b5045074002c1d43d0010000400c4944415804c040e10080c0e80300810120006803045800c15100050320110380c3c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 287283965 1250 287282715 287282731
    0x40609060c0908030409020c0c06040e090c0105040f030f0f0203030307030b090117030f0d0f0606120b0406080318010504050a06170c0c070b1b070e090d11030d150e0a0c08 75
    0x3140d14544541d013500c0380074511034901000d80c00304440c001e0810510043c008500003d04d4503503260b89600450050079416510401180711f40c1d400040154000c80c12202502c0c00c00b02c2d40d071001855a035548100b110103050403180e841c1b1102079003005803402c00c0554040c810b16100072541588480c24070407030340d805900c801c4540e0805c412001e035540010084900e0303032120406083e03030340142c400c003a00139120b2206038055440c5410302c0001d002d54850410401103005030030034021459024100301c144da45500034902c4a80040200e004030034494420f090902d14107040003428199904002140703d02540d2041011407200c0c5860540070380b0302102d140d07114068071030380c0341407241032401e042e903510709030250b0714546400080720001c10018242040c0c2641150301164901e81c0c40341000c140180060310845028400c0f00403081e2041e003d40c01c0c07640180d402400550501c422880c240c03001e0120703503481c02d041e100340c4080030400510020b0050f00c6100c011340c012450101c0340b00c00400c0c012004200708 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 287285215 1250 287283965 287283977
    0x220e0c010e030613030315080a111e030709051905090303070809060f07080a14070f11010903050f07020f03101a0901031109090c06180312090d0b09010f05040609060c 73
    0x3840d80c8a04d00101c0c01290540740c0010040040d03041060750314426000208140f003030094107020001901c0c030070403243c80d041d00c58000045017103a044010700460f628265068000e201c0034094503205a0249070f000d082d40c7c41e205d180c41c0c81d804008040f2101682d5581f21900000200190705822100d601e4004241c00020245440c04507810210184040c0008041100c80004905000510741009040c510031140da00d400d4100301030042c1401e00000080008955640700714220031106229810f13000d41c140e15198544404600034004a900c8004100d9000d200068548d030203460030480700d0249514400000381055008180032014550802c15920413040d0800500004942c4402110352321010f550454107520b403141010304101188604e50f410207804a0307503800710301030749500402d04001a81500c0382e4000c1400c100f14a880b901080c02e030450040c42036640050b0007044a0303075210740040300000341e501e8074010044c01c1d00d900303440c2079810030744400d500c0c0180411445015000d260394107040b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 287286465 1250 287285215 287285221
    0x60503040804030807060b060c1e0d09060c020301021608030a0e01060f0902030402010207030519021206070801061808150115090e15030a08030c0c0601080c0a05220e0c010e0306 78
    0x441c068891404010314403c2c002c41d94400300b0089030070400b90010000c5c1280d88840b101070304545d035440c01c0015491002c410b204602072000012900340d215064a964511a4600b81041a21111401341003281c240d9801c11480c0c9440d00050340c4200b01c0d0344110141d41e900d007401e012076800e8a00b0700c1c6100605074900ba50802c80ca404001501085881600703000d43c0b43d544030b00060b4184500c9030700151682c014140070503007600d646c1d90041921071003140c40c2401200314810903561007008031040c1c00801d50500046c841c0ea400303240d580d50150640c0003280103158455003018100443d2100c11041150503600510510310041d43e0718501900515081e040c00e45009141141c03450007900e0340418020811010f080340d1424021050089d401c10402d40d030701e00341049800c000364442805030300b40e0701400d000481c819001048032884000d006055807a214100003c100d00c04100002400c2c0ba8800707110a42d066003214080c01c010314924001501385120b603080094195880c11500511070b8000d2410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 287287715 1250 287286465 287286473
    0xc0f03041404090201170c0a1214070513081207200a05040b03120f090109170a02090a0209090a09050c042309070e1f0e0c07030e0a050d060605090106050304 69
    0x405070090204860200d907a40d294001031780d0a0348440101d4007a8014501000380f5204c804004008640480d55071441601040303a080d011103040c5001c0952000a400c041603200e4031a2010b0085001030100e981001a940c01160745001501c4a81c5011014041003c1d418400e0b0100da100c3d0240c101031604031040032181c00aa01000035015051244d0764401045003151400c00c070b002080b840054100340c0c0ca031040d1a43c00850b810021289001420000001c030320161500c1c40564403908220080845103007685c2000006070b07000b00091052a428040183d0315622403000c54060040b01d0f0000404801c0c50400b241402224400c103401107044c81101c0e042030244a40d080d4040d400309048070311b151171308158642025119880002001c540d0800d0101d0050400c100005c0c0c0040d0070a004011652041e400340702032011105403d0101d02480b032800401d000b4100005600002015a1295500c03180001c4540540c4c0c1e0090300c106503140c4d0240721500f44507407550b024191a0400c503085217004e5031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 287288965 1250 287287715 287287739
    0x31202070501090e060909030f0a0302040e06030109030c03030903020a0221160b16020609180a050a06030f0803100510020109060b040204210f0c03061a0922050a02150c0f0304 77
    0x10440c0500706c003100041610200344243c1f010b40b081c0300c5020b41e5603c11640020065042030089074000003205e000b03e88a0b02d014031030102d103940d068840030150070558405900402c1d80400c00c3e404d40c020207140400503980c050b265080e1001d0405940340041c1e004241624121700c0500103009a0044041401894066030550300101100c1c0d0203001d146ca100d01c045091401041c0314990000a4554a465105401a1400d1160a8040b410022960349422603410342d40790707210240140b101080d0340e1000c02c4000300110b600c224402e840c0440c852b510380200d00100110388c1d0440050355104400e10030000107000340d43c21404100c400354101800e14441b0041684403130701105002484500e02010420300326415120f07580c002030362401c59550390500c0d130b002c0c1481c2d418030302c1881c030200030200a07071034175500d441d001c2c44581d15070400794222165512241a01544140d545200d511b020b100141c0d20b0984406540401e0724049488250703000b222440c1c00c000351161003258006220600294030039035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 287290215 1250 287288965 287288971
    0x114040302070522020d0c110a0804060c110a060203030a0606020a12030903170403050703090504021215030a050a060603060c0804080a08181605010f0315050405041b031202070501090e 81
    0x3101c003d0690100d10b0f9958a01340804c55046900d400469280320160b281c1d1f101c40c14003c9252629102803880842d241d03103d4840c00c1006009503000e0009000b0b041c0309502c0510000d1043c40d2082000900a0004031486800d50002005071300002c200014100e16000e01340042034640002c0040b12182d03074540c0071410341ca180c20300c1015035841c545002d1511900c88800c0340040c038800440b0508247c10014015030108401f50049015010000380030306062003212070081040094075802c1d16482554520000d407400c04541c18403074211510046002408500390707403440343c0d800140707403440c504d010000d4034140b485d43d03028069000101700c00700b41c0c5030b022103051010350b140c0341d0540c1e170f2031482084000081000c04000f03071003a440000c2c0e8003000c00002d1402c2d03072026280c500d40580f00690450580d0301ea018455483c0c020700e00704001720b09158220f140c1061084e01c140e402e40c03002c80c610300801851940f05896a0f000020000e114940610110002e00020703e800d00150381010f80100e1850005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 287291465 1250 287290215 287290219
    0x1021020303030f04030203161101090608091f0f14160503010305060c070c0b04060807020c0402040f030b04080405060c0706030501081222091b0201060902121605040b03010603090501140403020705 86
    0x300300240405d8030034812903644c0741d4200e0481d4001c040c182490a4600c0c06a8602804a51204404aa40c9004021240c41807810340c0c002d01040d001d9032000f81b803205d55860608841e40c1c44901080d4102ca0b54014000500307224218000b852030f111000c8a11120211803107418030600f0030051020030300101d9019400103e0003401981d800c210714080042900503401850b02e1000424042080380c0d1140b48507009140c1a800c4032000400c110400040344554450210301c1381c02d00e40c0800014518200195028ac000c0440d18240340d5910046603203680030084006c00340c0c01120091100c2601845841c1c050800b107070041c03a01500200f42c07140789104010080050031960700a62503100d02c240c3c2c1c1e0300050001a003040c401d03192020ba4100d400d00b265003400b000b55003042000300e078004052090300e81182c981281d040842d1102c000901040080300d46a80401c00100004034140901c04001e41c020a41981c0003d47d80070341b8103101d401c44003000194101c103065036091002107540015001d06944003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 287292715 1250 287291465 287291491
    0x2a020f090903040b1b010507090608070f05122509181e15140118030308060d0602070c1a03090c100309050105040f0c1d1501030b0405102102030303 65
    0x148200d1540755000c0c40e40000e84a41000441034240317460441c0710328403d004407000f8007241d00d8862081d1100d442500940000031515400907488030300c0b6140d00a610806400d1041c034001450350441140304084032030941d02900c042545130b1884072003100d28030142c0a4980300361845d00f001c465140e01482c04621085484d241c0040d540b6015811403503503c2c00c1000761040003c411003900356141200144100103044000807000340031540078403030300301042090700c0c00c00e0851415694166a00340d00a400c041c0c100c010441c11500090380c0780f00800c0e03400d0050280200c0c6038500564039050b0100820405800d00003030061080714840003801140d541c408440c40405001020300440040c00c615001034140c0d03091078140424886c0e90a481000300e0302510880301301d03548a050340848400d261202c4c00702e120001000846004201d040c940460205240103d4042d019070006005d544041c3c51520000351101e804000c12100320841100390081912054540b4a481d00000c3c0c0780e01009154982c1d02c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 287293965 1250 287292715 287292721
    0x50d0206090f07090f06080a0303140114090a0c020a0206030c070b0a1803080a0230090607080103031b02040203010b0d06090b0d0209040813030515090106030f02010e0a03060c2a020f09 81
    0x1030141c0041b80645040700444505080c01e042c010003030b0203403a21030140c0c0390510340007245140c800380202d490144042c0900c141522401c1051000780000300d070020842c040c0e90428801640c0b81300065005072031070000a80c681400d420806001c0c40007419048443e031a01146110b850a01c1c000c3d040100e8144c104105913540f00c0c05894060721030304022005010815140c910712044981d4018001256590b0795052680c3e00c0c00d8940d602c04090b50b000002c03030904401000041d1069801001e00c0d03c1c01101850310a100d0340c0428143d80084c0c1103445001c80228011503050581d208241c002c0c03044072000d010001f03400300030681c400c0d04181e001c2d020740410400101440080700440707034a081d10120642c0e442c1d50342d062094491506010140381c5d07180e010003056400303505010f00c2c41542d802201401104070158010744000c016122260740201c003014000000c10b0032445076803c190855251005030002d000f5505001807003c4101c0000402014007503000740e155801c48547c00c1070b003a41c0d0b13923103151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 287295215 1250 287293965 287293991
    0x61d0105031f09060e010e030414030705090c0a090b07080301081902010f050901111204030318030b06041a0a0603060f1a03060904080706050a09032d12090f050d0206090f0709 77
    0x600303900c084801d582407e0000c60081000001042151043c001e0309400c28130700c00c00c040d10b0b5412846076640c403078036140204034000c0f040e100602d05000a800c00150040d5a850f6850158100f40400c3d04c09000100c01008848011b10860082121181400e80007803caa4000303000300206010708810010301090b00b1070603034098035088181c04100000c0300c01c0303450200a030700d01903030040c00124000741c028031f804a40a00d40e03411504c01d07070703a0015442420f56504020b0000915800b010040c64885012100b51a6158400310304041d102954012910a040c8289440800c149034031912203a050751070303e0440b1090100c2074940083c1d0458407400d031500c40d800e01c12901d000c0c4c00f00141446103031070309002201040d9400190b40710300c2134a0383c1d203091102c00a41d41c04001601854a907128030410b00d1340341d1368480c0044a101e00e40c0746400003048072441d110388410a0b43e181c1c0480701940b04a00c00307403c0b00e40411280364824103503030051117200c03541005282c64009503c2040ca189071582e030350a101d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 287296465 1250 287295215 287295221
    0x12060408090127080f0607020705090a020f0c1b06090a031416090c08060d020603040228060c05010b040204050d1203090b0a0507090b03102601061d0105031f0906 71
    0x1200f051000c40c01a000340b40190605a0714922030350115201d800c05519014101240c1702c2d1050401d0340140c81e80500d42024000360381c0f40100890b070455801c01500c1908504840a004442450380c000c1240014813140e201e0020708805500d803058900340495807007940ca280c0b030082500d07442441000c0300c0c84482c81440c6800020034a003142801004800304a04015900100d4406c3d8196a900e059031510420702404061a01c070103074012004000050150506c040824246840c815003869400c20040c201c00d4030340e01c3d41d0046800200326550310001c0c03240901400d043c5841c01c07139085140c10f16207000a8001034051308020030315504a0007240038075001358002c00400390045501c288030301e49580e0810003820101c84001c08112906000b24501085000380c82c0708009030406003c02c981865000d585c03607a202c8010b61141c14030724001d110684000e02801c0000d0003442007401a41110055509002605030030042c000c3e40a100d0030b1f80008510114505003204000c40002c02c49803506000c0c001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 287297715 1250 287296465 287296487
    0x18060d060302060a1d010e090126030a0e01030b0909030412240605010f02060403091a040f090b0909150103120e030d050a020114010e0a0c09030f0804050a05120604080901 75
    0x1000b03d0110f8540d070500c1e0000d03080d11840d45540c02c548440c4009a00541d0f0640f086e148041c0c0040352500103100203c6c1d241807922100c1d0241301d08802c40c06000e141d20345140d020703128031030024003800c991508030b5030140030744c1120074421240040e00c0d01e4041031082d5240039030320400d90f19002c0a10128240000c00c800c03124080d1800320f18441c205060200700014000c648140d0780061441190900c1c034600c0801c103640100c0e4195652555946007034000d04c880c002e40c00011120540810000400380002c000c880000c0410300400702e4a10f90703500410140901c01403058500d500030042821000c0607500c81541940e0380702c4210003210038850412550400a4500c0e56050722030f07034040d090102d070004082e14a1040316402880015400941c0459104080c460040102d440801068011a403500041160005454001c082c0e41d581e844000038404500415034250b80005428081d509141c2c0403903025041c01e951001288820b1010303e03a850741b00030005010942c01080c0c00e5503ea102e40140c504d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 287298965 1250 287297715 287297719
    0x19060315150e010c080d020909010e06011706010e030102040f060311040303020c100e04020a0c060e030717030c071505040317011203032409020d05130302071701061203030911040218060d060302 85
    0x148844051644030000d48c895000c561062083c11f0000580c403924000c0c045c4600c10607515036070300c0c140b40c42011140120103040303a41400781c0142d107004191803d04c0034000034401c012404458030303d800c201800303c0c0c0d00f00c41d403c880c5050400061010940004958880d904140d800201382c04003414121380b020022102540d1041c0001403500e1310a030302c0091102d882c0c0c02030408201da0b0314880b407000c1e50b80c0b0500c0740007054480f181c407000386903140c49006182c0c03144240b61503d141090640d00d080c02544140c0d2070b9031202d651380c0c06100c01e0650103940310001e413400c041c03840c1c0c00d9410b24200c11000351050784024201516038a0242c1c240344400fa6808400e200302d04008402c40d00e5543d00f4001e0f401c20008040c0c401d05e8040000c201842501c010354061340c145d009410703040d082c001d00ea6454010135101e0101d40d0b4031540c001840c04544040301000c03e009640005080c1510310344208a810042c109038491801403000b4800192040f402c0135003000d0850314599144000040c41014201d1a44069 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 287300215 1250 287298965 287298967
    0x1050a360605040c0c061413081c090b07020c03030a0e0f030106090c0c020f0411030118091e0b0a0b06090f0406030506070c120305070e060306030c19060315150e010c08 74
    0x30364515003192800c11206d2180c00c0a00c00c00c55240102c50034140112400d400c00c0b124141d820021a12220040c40030059061407481041800e05041c003e0721000c86044410611000800000650500440e4400102100550720305082854000c0441c0030300c031143d911840941c4409a110340e825409035000b045071010522403002e00c420007800b04041c54005078050104140450280c0c90284618000c01c0c080c0206c1504503428082c400402a408008044003242c1d84d6407401c01003003a030314555070800c0e80044211020790952500007000d0b50007502c1404103e0504007192000d42d0b80c1025514101704c162100814502008001000380240d1342c00545240a80024809a00d6000c0722840d20756020f042e28801d20098084201c08541003240d101001034045801c501462401c80f0045404c04402000c99040880e2030b40042c0843d881011218010300b402d50080050f80c1d014041d02181000240200b1000b51034001b00544040d00b11001800300603c05030400c00d00d038003e003031044426400c40a00c0e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 287301465 1250 287300215 287300231
    0x506060c0111041401030608030409050402060c010608010204050f0103180803070306170c030d020f0c0d0f120305061c02031e070b0f041d1323031201050a36060504 72
    0xc82c803942d01500807416400e40f101d40c0d24183d94024000d600403121520010f628080c9410760701401004060400c0307034440006c10030220100c0c170034010f5001501c515400103907928506410895840c0e0040b0742c0c1418581000c010014555505074555421900114a9940c0f55580c2000720700418003500124200b03160501142c0f1408000621100b044c1c0c01a4111a00d14211a20580e0351781e0b0010210301c9582d214110310032a07804c1001044892901ca004840c012144590711412103c043c9501c90b1300290780d48003000300f103280030798a00c180c00d80300c400c1000d0900060f07004280c580740d600c0e003c0b80700b5044002124589040030460b4400030031001440c0c0d9120080ea441d0210568424440e141d01d030b4180c0c84042640c01030b41980e482c0105801c0601020300ea1807603460842c400c0d0900c20381c0e803081450002001c00320b50b050004141d02c0b40b528124070b41a41c102402c0007020b80282d0070020380c052003000c0000c010000415040c0c43c412400b183c0504400750324035100041e0204e41c100c03d4000b8200f2520b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 287302715 1250 287301465 287301491
    0x10c020f0f010603081801031103010603051e06061e16050a1b05060301090c020a0606120b0903070b24130f0e010b06041514031e0705030403050703030506060c01 71
    0x6910040040c082070340e182940d018405426142c09000c081d040e00320410104202020300204401c9001040c1008507801c40c41214182803600240c0c440b03800b0036229010420320449000000b011011034855030303174540c10301070082080f0380100e0600710f41c40710f14186844407400a8500b9a40240607540e010540d05031185407480e100d0031480c100320303034141c00c0c1c0400d8880d080181140d075082c1c820203042c20381544c2c80c1c0280c0a021b400c89c001d02c40107601503e0704d050302050705030160b00c011300204200c0300341500603403504105000009004034070395002407002c04006241060303441d03048003c83c20300a04405c6542c5810703220a00000c161076115200c2e058a1000c01e006070094203591466040c1005612103880500e420b0381d50000601e544444100001d104070100326100c03250751601c2e0305d006200c0404003481e0f80c0350350f441682c2500c11104d120560f80c400800b901d00e4560300040518001d4214202a13070090010f0044280003010326841d80002000c5842d14416a8401c01c1140001c0c800860341c07041c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 287303965 1250 287302715 287302723
    0xd03110c010204170f03030114011407120203040f080304150336060c030b0906131503050a0c051c0b060105071209050108010f05130506010203070807031809141303020c03010c02 78
    0xc1d00c180b0600540900c1045c8100200c01c2d01e04907138041d00005082107400c0e00440703021221074100c030400101070110802103a03000c9842480c01304a50001c40d61a4240f901c200c9406400741d10140d0240d20030001030203204e04a00012040c2010f41c20085001220034400b50014071058490036000529400b00e181c46007090701035081c045001d200f04104a605580c003c0342940c0301c40d55402e8206848101043d85410205010549900d01e040b001594515048910221812650003a6055804540b5481c00e01107454001c4001b420126844504441001c5140034217890041001d04201c0d924400a0b59990040d411142d9075517208104003101c0041d00c10141183c0b00e50300806000a5031040003160700c041d0081c2a0056540081401c0c4100c0840300440f406054001c0c10386046000c107105840019009501500c1010b110751549a13000500441c100c00c00c00080e484211001d0600d10b0541c0301a01035844507810031900200d0458060a501741a07181801c40c0d030041e9055880d00101c1280aa4046 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 287305215 1250 287303965 287303999
    0x3090f040e1c03050105060306100f050903160302100318080c1002040b0c0d02012c07121212020a210b06181305060102030a0f2d02010507020f0d03110c010204 70
    0x7440130011039803210280801400200d40071342d0081454009003a40c40e00a9841108082e002d280c00c3d880d040c081e43c0464100900082c0c1024080d500c072105100714648603056210765846440c0800030080c01080f00c00c031181e0340c5100580301c007900141c0ea00f4900070501c0210341c124103001d001e55031180d0b02c54001146501406c071040940c021204000180c84c0f040c003070f15254000c0c6047c41e0211800c0f01c40360101c040c440c204410458415190002101500f50403282480c500941c8070b400c40e0f0b201d005000d4881d001280740c014481d84100310302d9a1035034116070081440400b00000101c0c21000c6425080200880140709500c102e02044200703040050340034a030800c0c1e40680e00004c00100141c4d0b4501910815619180580c00612035094842c1c4603030031001c00d00d278803468010390200904a82110041c042d80201d1002141d226808081d036809024454001c2a5480201980304ca05180d1503141c510940141007016151520300058651900076954101d1111008641d02c5507246228800c016880d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 287306465 1250 287305215 287305217
    0x30f090301140702032a07060807090909021518030105010305011d031c020906120903190c030f0809030d060e010e0105090c0909060402070803090c090606070503090f040e1c 76
    0x481203a14821103a2010b4501585854004504028482c800c1c11445080e180c1420b00520389803818002e940020001c141c0200b070581c613854141d0070803a000500003a52a003203801072a0802d14101d0040c0c03902108003a440082d4012a41c8440c1c40078142d43e5101100c8048641c550b0802c00044248181035018002401705603254203480300380c01c07130036070303228055a0394185901c2800249220410159001080b0f500401001c091030004e001402e10015102a00d41d031095502c0030449582019803807050b010071100e24207218960340c48668005201c569802024020003c0352070101da6841c2c001c0041c0c0ba080f032172183c3c05000305510f820181004207402d1041e040f400c8424400003030030b402c00c0b03014940607c140020080ca024509000d101600394060a040d030095800c0004501090002000d90700409484000c0c003445280741080003036001000d40b60310710440341048100e000440000440f280098150f40c220440384080000900502021520104e103008010340680e11141c0880105488102e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 287307715 1250 287306465 287306471
    0x90516060905030c0402250c0e010905060f040b0a080d02030d0b120a0f0f020a03080a02100c0e12160308040f120b070318170405010806100c020120030f090301 70
    0x140d030404840207a4544112a015040a100122a802c0640013040e000c020301803031107204120306011117820307100c0300030981d20400748160078418462104202c03070040401820501042c10284001544814400340003071080d03a48070518421910b80c450700400804074075007521104a55440c1c003948075481502e05403200c0d03161020243c1c0d50320f000020495542032850040520381295901e00d007480180c40015980c1c3c9803000c0c0401d005940c2c00c4103620255106290441e01c9884020011b480e000b29510300000c80d90905d1661103046501040b4804075500072038956403c142a00340d05410a400803155200c045001d000200c10b2000c0b12006004542c1035200b14000203595109031080040720440c000d00d100c0700d01c0c02041d40a4821780241499400002c92880328581e44e9440d46803006048162502d90071002c81d00300b1466070400d01180d4812420364000300d1222031480020034100c80c1c50310003418000c2000000405418080002e49101c0c2803100700c070340d1041074201800c119013140c11200e101c0d40c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 287308965 1250 287307715 287307719
    0xf090803012c09031e220311032a0a0b0315010801060c05030304030e03101a0a0f050a1703070c08010518031c051806010909060b10050711010e0301090516 68
    0x320b038050749119600c4a00030b1414420030b035200340b4044117a940300b0385800109104413800f040c0450000503070700c83e5248071150704600c0d501c1e0001c84240310344501c0c2d1090300300504034151902000c0002401c0780c9a0b02c1200b501c84040c8001a800041d42d80160b107081c4000f108200400c04000d00900040e20240c80b403030890707a41c0f0801203415080d000001440d90b0001d001103000a40982c40c0003c20f4071000301a1424024140c00900c101c40c8203201000748405604500000c60600d0030003400a401c01d1341891880c1418580401ea0103c072034841d0100301c02d49481c44540d040c1050054804c0b05a00c000144001a510780c1101d01800c000d0b070340c204021f58040c5440e2100036001044840640d04a145040e02003100207903580206001800c00900070840100c003803418800340583c038041e2501e61000110310b6883d007006030031291100c03191409030340d54464180c00360b03401c4410795001607880086d01d04620380c0d500040310101c01c8203114a8056084c03a040604000b13001c1507108000c800700c100311810f55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 287310215 1250 287308965 287309039
    0xb09090f01080a032f0a1203020705030f070206042303120306101d12010e070f05011704060209040603030509010f050406092d08030403060614130f09080301 69
    0x520300303201d03001c80ca41c0b1100309000044c0c00350034a01d18800c83d090f40721014404440110303141d0492218442c1498000c0c0e1b00342030401842021144100c038251508604003c4660781d42070780c9105101e6581101100401c500c4219951a82194050000780014101108003001200c8480004140d00362081c02038409010f91180043d0135203100c3c8000606034820f020740000142c84082e00711100003000c11000d4003621103922144402225013a5200002505000aa00003070404032980c000d58017001c0d050704c08102c140ea009a643c3c1c10802d40100040841d21a0300c0c00100030712a203919960402c0c02c10300300205050304240540b071304607020780b0740400150054108032054072460017031001184c1c003d2030a11070001607a03a0010f01c0819000418818075a056058003c0c16441c2d21214041d4000039041c0f0800c00d09005600050070002161010100d0341030008003000c0c0715121660249a03aa0345060440384035800150b0055004916290f503941c49100800348401c224806024086182495100d40c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 287311465 1250 287310215 287310241
    0x1104080d0e1305190e070806060303340c0b0a02060f01030b0109020706020f0706060f0602010207080d02090105162306010302032e0c050306010305070219030e01030e070b0909 77
    0x1500a040c0342c2c0400c00210a0b5004140240c003110350b2034046842d80300789070024403e54019042640c0184110352034184094a0254024001c90081d0003d02c9010140b94841c00306800020394104010b880341d26007018401942070200003d050456410743c0001d5603468507000b00743c95480d56082c0c0d03240340c1e00c03000c901700052802c0c84010304d0111032000412807464641d014107030030343c891a40945402c2c0100d50415003500b010809803401030361000100b00908041e801d0f9801048030340025810b054041d110752040d07002e030201001c1541c0e000149003200da882042102c0315a0751201e500c0170605801c1c1808201101205484245014100301104c40c4600024600e0f0403254010b004084030361031f813443c0121540c020440340000d80c4c02c1001c42c4025290500034030036107043d60740d55181c50707181590006054501c040c09030307025904085104000896590100c5a25903058248030070030140900c0120300900300c03007652a52900400e080800c0310b00b0380c10010f015000040710842ca1710344400102c4150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 287312715 1250 287311465 287311487
    0xc1203160305071b0b09070909050102090f090903030115141b0d03020903070311040b1201050603060f04050c010c02030715091401050a090909020f10021e01110d051005041104080d 79
    0x1d40d05113000180c00200101078842d84005117034180c540130703541e0f0344150054412020b0101d9051b5000f280043e040e0070701c2c419003c21010115880c240d80c0c18000c03041501d034031040c000c801c103185e006401001d0f070300e00416050308034052003046555525480201c1003001070702a070082400340104151301e01e4003840382c000d035812640300401a020751445e40c2c0c0c90300c6507924040388581c0c0298588105100d030380d4a0a4009109603c01e00020840380b030f205d8105410810000c0408480c100040f040c407020560006005000000a09220701241d5543c00040d2800303650350b0195000590700c020940242c3e0340400302c0d104440b1017440c03000d030016009005588034012484400300040e03144030100f100803100d42040450a0010707003c414120b5a0602103442c0d404014040009070b0b001c0d901c031001d8032507654194155025164000c0001200d0400091158881d245101d0442c54507132001c116041d40315105540140f90017081004a400c0000d012a00e94119200d2200c950240445404900d4007505580003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 287313965 1250 287312715 287312747
    0x606060a050d0b0a1502060403020705240a0c0602130e0c07050c0613080a0c1d0705030105010c020f09091f0501060c02040c030e12030a060501170c0c120316030507 72
    0x204142c0568029002400c054128139808000788100080c09107100c03510007143d0010398003800d101d25003403d000e85011140c0c0d00082c00b40101500150b0510101000703910340e0107400466039070300d000d0582c00b180c05c2403121201070882c038400600c01c240c181c21803002004484409460b54030b07540e60480c00c6071280c00381c410042d0072034010280489803460110300522a0032000d001100586446004440c034088043c1e00031078090108250074000c00c00d0041d20701c50403100803a00d45d0101e181c544001080c6010600ca800e05114001640c5411540c0b107084c8000140405040c045141c07509001243c0d54050b402c03e0b00c1e40c5145114900e08200b41c0320302940c0e0580e425511409010403007542404020660000d6100c1059503074070500e12400002d2041e11102d6541c1340041e41c80f030411250404c1254825404130341032001140c00300ca04001d017210000c0d03204202c80380c3c42e0348400d240c2c0005420921848810001c602002040107001495548440c130940302d1076030204500d6541a0003500d50300b84030380c0652 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 287315215 1250 287313965 287313967
    0xf0a0e030304050601090c0c050706031505030c0f04020f0f0f03010303030b09240607081801020f010209010e24040603021936090915150b030c070804051f020606060a05 74
    0xf0042850035004090005841e107060007903c8e2841d224076043c0170b5140c006000003521000d00446900c07c024805001d48004c81c09000704807004400038102041d4007030b245002e10313004142c018a0707901041c20b48217540518001c03a41e03954a807401407030096209010441c0400d150800070000741c2007400400d84100c021043e9070009440c80540e0100010480d090b80d03921801c00c00605001984c01005000820a0500545602c84c03029002904044e01030502851503803062081050702d0381e21981140c1d1241c003c4d0340c000c1e294040c0c075682e4003100000804a121100c0c00040010750701d0742c140d0060001540b06210760b111115041c1f41122280c4240e040c0c0850740e0f03182c000c079032202c400d03030410140e1070a04400e6200300700fa5110004015201141d10689000d203131204101d0261040d070203200c140d840f1000b0392449190400e6180c000034000a0202036885502180100401070070b40c044074040c01001b0050070040c0b40c05a40c100a071003d1006510042c0110404540582040390580c0d042583e04e490749 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 287316465 1250 287315215 287315219
    0x31501151d0d030e030607021c03050615130e10060c02010e0a031b030605090304150c0311120c010b01020105161209020d060227010f0c030302120f0a0e030304050601 73
    0x200c1e5075009944424100600c01001803115030b4408420500702c074420344034031100075102002c150601c0ca004041c5019900301202c610160011140041e10300380181c140015613071104001f2414400c0307a0002d00b81d50700d200281d81c284200079405008200c6480c1810681c650b40d550900307480e401114800d601c0441c28440200f0015070140f810011100000340940310f00d075a807525101c44540d03401200c071031f80000101d020701c1840300c140243e070361040603040114a001c0c580700e040c416110414512004000407001100105846030200c0f0000c41c4a0b01c00b1a00200000c00354400c05600050752400598602500b401003035006003d2984998456a544064503110b118140d42080400c012076240541c0c82c40d0183c010b958020801d54000e00409006840b0440c2000320300c80c508401012034400c4c1566420204140e9004c5030410500f1710070b103070107103001000d8074050703010303010300c000c54851416908c0800c01400e50000559100718882e96090201ca424906241d440b48001c1c0e401501c41c3d0001401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 287317715 1250 287316465 287316467
    0xa020a081506190305010501120204030f0b0603120c010c1209020a0905060607020405011e0e0c0d020f1c0e0d030b0a0e07020708100f0c0e090a050c041a030603150115 73
    0x11004110320040c1c203480c5014620918039030303420700e0f000d0380c4808070342c1e5940140825640b0420310710100c0b41c0c4050462400d070440d100d40c4005860000010302c444940000203206444c00e1281840e42051001402d03268407050254070b0180084445440019568848124903915240140c0b004190007800e410421420041c034280036240007084160001010060000103881c1c9104560080c0041103401c49080c2c0d00209000b85000d103940b1100d0344460010130300c02000c0700d201c11107103120700140300140e0358841c07506086c40d107000382012138a00303141c0303051100c0040d070240e000426010381e4070064034005000b11a01b501190450540507800c0407079941c0500210001c09078050304000980110f0700510354400b00f00349042d405206060320903468160011454085005510001019083c551202e10584001c141c1c06e1500406910606d80c841000c0388070300c0c00e0041110f016165407070341281041000044502158415140c083c00f030301c10300011a8100f030710130840034184d80950560b06a82c00b00868 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 287318965 1250 287317715 287317741
    0x1008010e070c0302011b03060311060c03030a0b0f10120509010c050912010e0a03051803060f04020618061308061003020a03030f05160c1511030405150d06080102120a020a08 76
    0x2c012004d6668504d04c0700307401c0340e48181254442000341d801060319030440c6088020050b00050460162000b40b104401c92500881a81d40c441103048001403820b40e9a40000c0c00b4462021086401a4103801800300181d8032a040410747c0905100074005c607292140400e0803204480303483c80016074140301418851409184800705030490000200300741034001100350600045000442c0801c90024480001914544001000c0c200880c050852440c0c890b80d424031000000f400203103d003070000341e400020048201809903800014040c26140e203a840c10b0002e00703400d18010303141c0c1071007001300080070907203514051301c19640e020f080806214515902601d2a02c00d10940d1400e1020602220042c05a040c0c10010900e000c0c801c9007100070310b450003402a10800301ca2500c1003050b0100d060001d488000100d0381100c109480301382a503c45c0382e0b201e201500520760414101030030309400184038901500603141802140c0c3c1c0701001ca48036904400200c0c450b40c0c44100104600600003400e0641d0782c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 287320215 1250 287318965 287318987
    0x302120a030912020616020708030a1b050d180f051c170f071a071e091d0106020105010b0307020706080a0608010c080a0c0302040819080702100e1008010e07 69
    0x420040b030442e003030307569101e0001e01d0b003e01d2600581c401e03003c000c00c4002d64618451110140c0c006846c1030344c101208140c69216080019040c050b0381010003161900030101448690340000694000b01c0c001c0ca0010400e20402003405c00d000811540405c0442e1800804001c50b00000d1102d60745001000a94070341c144c1514054907a80c0300030f20031458078110540100a80314440c220a40e9a04003458501c58078112011420004a00c0100b000042034000d100c401880e2904145040d01d0761030100e0845240001d5005811502400241d41804501ca1100e60341611a41d0300240090fa883d2000a0380500044540d800146c1c0464410003640740101034903600192103001c041030b1107446000c0182924a035101040016828004014010318140f092082e5403c0ea441d00703601d014544a25655100300381d442c0e51071540c101c04480b50801600c6800c0b5100154040c0c190041c81400100c064000b1412565440c000c0086a102c08a22442559120305031140d40c487c11740070381c64180086034484010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 287321465 1250 287320215 287320217
    0xa08040f0f02120c1302120a0b04020d060308030f0108030702060304080c071a1803010e100b03010b0405100305011a01051602010210050a020903070812040302190b030a02071b030302120a 82
    0x102001070240e1207040d0086903e420410042c5001d10100c001d11102d0a41400758060040c8140910040100d40020054005802c0c0702d010071002501400600240718145114440340d02d004c1c000020004002d001d10310440000102d803009a90360382e0050384070b100c1e016000350302160400000340000c01c2d50b80078048000d200002c8a204e40e443d1035860030080151190003440f001d003c0703221100c20705030070034020301d00b00c0680090088020791046140c0d00c201d845585144a9200c00c4034003c91385095016850509000b84140b00c5802c21140074480020a80020f5500b035080c000359a0249420b020070815807581a581c5915200b1500e125000c0c07504c900e03c0480c11801448c100060460103802070b070f40070791001d403070040e03407224188209407504100707901015140e041400710b0706080f44800142c80440e601030300d03490b0300c82680c0300101e075102000360072100b039880000c0301384811200355a000d081c01c0c0d4030aa0004807108007004151b0443d250380e20004006a111032085a030081154001c0d06c0c0903042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 287322715 1250 287321465 287321483
    0x120613080319091a06040b060301060c0516030c06021c08010b0a050c0d030510080f03120702211305010c151e0e0f06010506040f060509060c0d0e090604020a08040f 72
    0x10042c800103880c000e450a07520001100c144d443d00866101d02142c114400300e07001c0010711011404240305000511a00040c0640480c444041c070100740450300242c2480b00400905a0f00c034500707000e0910413806040300600c00c0290341031141c3c120b900c150702c407200f15846032492a1b10340421008640c1c013106210b4204042403142c0060464100051000241c8540f4003040c0780c60100700a80e82280c0950040400382e119440311050b412001c4115140428000040c1e44140d580d40c034207030714202a42d600381c0c0c4071403105201740740a402400b01820850310513511a0210340da8032030045500701c0c05000c0160240c604d41c0c9040c8504160f42d485840d10461440c003035801d80c1c982d036a500c800c0300d01040e1400c1d0309420064426403005414410b0300d025000403220b80d42070500b00b10f0040c00d015000d0054600740700d0002244551f80e520842071ba401c81100d2822100c032580840001084000080388440c06002c403140800c403249401d00a4402c0350700c41c0d540d008a20b580341c0d00d8075060030100003004e540701c003c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 287323965 1250 287322715 287322751
    0x7080c092110091202030f1207090b0415090e06031009060609140105030606010c03020d0804020307170c010f020c0d0206070c050619020607050a080106080a0e1b1206130803 76
    0x1440051180241c0440004010342c0c1400c103111020204e82030001190402c000a00039008501e01b0384440718090b540c00c20a41d5200c0030151404a0b030380d00105969200850001204541d40d200740101c44042d03074580720756680e42d01c9140b0003810b09544003541030b0004200310284450540c40401218010300000c641580e4521b403940c100c5880720003980e01c0603607440c0148240d00b0108a61034101c80d003860b001c04410081e4400a4440c1002a404400c10213540c000c42c0640d501000358402400c03401c2e840c900751803010310540380d9500341080d070680840d013404140c2808600110300c11001040c06403a0022243d12a8204002507100c00411034407091800303400b0079143c4844020f004400e9000c000f41d100f4911501d4040d18050000700280b08100b4100722038003020f0b5102d03901d141122002d062504494841d00086000b410404081e119944150a42d801c051018100c0131780f00c415050361115805461000f41c4ca445500c125441c0c484055039265003000902000003c0d40d11045491012000503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 287325215 1250 287323965 287324029
    0x507022809090605060904030e10050c120403061401050a211202070e0a09051c05190e0a05120705060a021006060e04180302150c040512100507080c09 66
    0x5035180c20420549556040240c100f040d6881080d0308880101d4044449161a58005100c1400900d40601607200310541500e407500480c2565031500c0d50300f054424201d800e540700d585a4000d8402501c00174140340e10489a05c101400c2d00e41602e00281c01804214200100403491140b01030000a043d00845040c60115100f074500f400c08035200c2d8090007400e862715084c82da0040d805001080c0c00c9280c440c0d03d10000743c002802816602c801c10000b580c040c1038038000c4d5014041c40001c0191480b51041e540300d010750107081d401c401c840071990400310680354028400b101c440e1402481c00da0344410801d0009203090005400c0940c01807040360b008266001c8590b05803901079226601040910050b000755203024020418041134070340004546180a89000b9034841c1ca0f04040c5410442000114069480c0401201c02410340607126901c40200f5109251303403249200000b115062070b10020440441c86044168000c1d5602d500c481d040002c0c00003040b034506414003074541c2a90380c001000b6244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 287326465 1250 287325215 287325289
    0xd030315170714220b13020304140106060e010503010e091e010c03061a12060a051507062711180f0402010f08010f030b1905010b1c0507050702 63
    0x24541c9500609030b80c41c41c01258440e4900c6000005204003622072420107502c2075828a05900c80740000041081c41e040b00c040743c0c509106403a2110181e000200304810300042c220f104c60400710540003005150365449080b0b408060f00410389000501c20001002012140c605e9940c00195030800c0c1c1310141007052000826501d0504201c1040c0d4640d00c50401c0107170148203540c01061080c0f414042d0040c58641094944038406180d2440f03040301000c10707000c0d141c43c40caa4003e04405022851a07603110300030702c000ca8124030001ca46442c18011205081310b1808400050300d202d0304940c3d40c02c220307103a9613072001040e1004c60030b800c0441421a032000180e13210105000352001c0842824034245400010310f042c113844880710a100010004101091031011070b0b9049030f4000d82c00c440c580d110500c2908200d0519500180040e0a1200114240310440000c1c0306054482c0d50390401400e501d0190350549204440300d1012500030b0000c440907003440c82191104921443d850181041440020464 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 287327715 1250 287326465 287326499
    0x80114010e1e0c161211030307050f18042d060b030c030c0c01140612010608060a0207080904020705071719020105030c07021909060803090604030f0c0306060b071502090d030315 78
    0x121032110410b198015004101082c10b50380806c055803035490007005c05881c0b44110740071203040203000285802e2840601d04981c084600c020000d0124030000008450a031035507004540d00160b4410080f40d40f10301500c01d007800c443e0f26400c50703406d42e5281c980704000d64100501401409000300701d4a0000e00003072240805000c204401f51255060400a10004c12034001030041c840c3c0c50910144080e400c0000c105a01019480c4094ae4400c100c0c50039030140d02411007180d40040c0081403000405c0303030209205050340c0405104080340541010040c4d0f07a003089680001404c45804800000b65220f1002180d1080019403000d240c09240d40c08262070200c210071244400e016081d0a200001c02030107100d000b44504002542800d942c0c00001e8030521a80c44024200510040043c0800004186000040d0741000c001c0054a03500c2e1a10031a0342d001600c2114404c40f103000a011507850b500c255026070002410396200f060450341c2c02d600919070483c0b40700a042e00c0050024900481e0850424 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 287328965 1250 287327715 287327723
    0x421020a0504020a1803121704020f040e07081f2306041a1807030c020d200a150609061205030d1509020a030b03060a0b06030a020a0315080114010e1e0c16 68
    0x11f02411500c400034030214039058000203000000d030500000d6030314036410b4414510101c0c1c0000f440f0449410b401c1c980480c90303001c00e216020746040f02102e102e5101181400840c3c4100030721503c082d040500150f04041e090030300c11019410017298190816600200c5894101e1020b4100501410b00040040100e031074505200c03540b0204101c0d0450f40b40c0244503821046000902d80c0c031800240152078406503015019021464140d5440410400c00c0819201c0350064030070341ca01d244801803000508010f000d41c1c0426410098001030458102c0344440d002a040005141132081060510300079080070003203030010005c2d940e03001ca034024107440140a5070f24251400911010762005250508a0082001c2826841e055841d0802d07111041142d42c800868680142c2d282c1d0020000d90040c400b1400b4805603080e4101c0106e0000d105510804482d80c90214803a490380e0395441c00d03900000c0032035031907880032100541c100013030b10100301c2107420900c400401810001d0a0444d1104048007041c180d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 287330215 1250 287328965 287328983
    0x3021f0311040503030d0b0607141c170f060406080607050a03050c190c0f050601030f0201110c1c0c0e1f080604030e0d02010e030f01020421020a0504020a1803 70
    0x262054040c41030041d048403150441d81024642400203071240100b40203907122548075803510034550750358400c0740c0509a00000761496103070024040c55541c003140c0d003801c40d030341c040d089a054110f028040d40c042074008644080b460b540c504150704c0707100c90003a1001390841e468034004115a071080c4942403044103107558280d01d66080180040035554054444095400d041181c8210016006c003680700e181c0c041c0c217041c40722042c2c07454000792003500c082000e0500c0c020b51001200700000503142d8006035000746d840001030044000065112907803952400e07846130541c11040f032612640b0a00850b0700c5d014065024502d03a6030103030071716910812500295a04120007448604840610459010b42030990082c00c1c1858550340c05840d100780c0100240c03194020116240441e885000d4000ea5900040e003596039224a10121501079005806602003004208502e0013004860b0807240c036196400405a002e194640001e0000a40c06800150200041030035110640c894460014009510511a403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 287331465 1250 287330215 287330269
    0x3150f06030d0c0c0303030203040f0b01081c02010b030618012306010f050c070504050c0918090c0d02090a0c020705150a09090b2107170a0b06010203070c03030e01090302 75
    0x542008040702c041400c1c080c0746821000840e5103001031000380d0b5450304005959840f541045004201c20f1480206400d104000120310b0b80d10104e00550801c0203031480e1440007010341016400d85261310000b81d0140d20040024450240c0b01441c1c0d0403e11071400001551429803c0c204846007448a80c810200c40c44c009200c06543d10840c0c0c02e8a214662030100d08104001002030f031141210f1050318882c1c1e41300c1c00441d00d00c008a008940503140c00900c000390509034801c0984401d4000c9460113554050550302c007846045c04d00e171031000c1c5540180740c000c0700e90310407400100506414680000310b01c18100007040c142c40304d524401c2c0a81d00989865120a001c04006060303200c41d42020400d2410164100a0f40d112405411050f210f00042c802400703005142ea5482c2c00c0d02580000c900f2512006101c003102804251400c541e8040c0040c50660f03954000103a96a1042040c000c14086c0d00070400c03c04030303104a06513100c11030145400ca1400b560303070b00003a8280c0301d9566203241c03580e801400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 287332715 1250 287331465 287331469
    0x10c021315080c09011a0a05120405060402040605040c09061805030d050c1002041a1b1608010f020a02121809070f080601020d120f020717040512061005010c0203150f06 74
    0x440001c150484130202c0e0340d81040d1030740d0203040b5a1a244007180700042107000032540a141600c0030200d444035115404c2c40d103808c010307a803198103a400364040c03440d003440800d0b1410326000e0f041c5480c1142d150000b101e0700d03081c0100c0700a100040b0008182000c40f102081c0c0340d0302804641500300c400d50360551036080c0c10700c1c071a0a058a0b0740814031410300c10802080311750b003001d039002008050a0348241e11140440d0101ca1298610b04501c22035000e00c40306200303951046108030080d9a22800204444014491480c08070b10641d1040000b50713200d0041c03400c40c80c110340010f005d0404144280c22520300f85101055410009403010b1001c100300003054140650300c06080c1c0d60141c000d02c01002114400d0b413001c0d260709020504089800c0e12500280c848404640450760041e5000c1241c180d1401003555a140f0340c1c21038003c9606c24108100c3c2603403480c1b00007403a203015540601403440342d030785030000540340c201d035252041344c0502600b44441c600512071082c403407188068031181d500078a01401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 287333965 1250 287332715 287332723
    0x11b0c080c060103050a2f0d330c0815091012050c0108060301140a0509070e090102040512060c0301211e020109080307210e060412050d0908030702010c02131508 71
    0xc1049002031340c501c007a0300034030800814071002c001f0540f40103007044101d0814400c040da1100001c50b2a100d000b11003c55801d00c0440702800b458101c0d03040209200b010000c60f00718400f61000120812003084520f01441c0004140350000c071807100f401305190340d456010413190003110082d180c9405c05441c0d9200c0e540c0000d00b243d40410110001c000055140f26280c10050001d0403a40c1a1655040061903410b0200300341006000100300703030f08141c6031410040d4042c0d4002d0140a005001c151041d0300d5880001618038000c40318100c51901f580e08183c11801150323200c1136054445240745074404042408115000c004003075481da41c00000380207000240a02da040d13400080b0907802002110041a5042061201107102c0b40004201c0030b00307801c00300c85081081ca2480c0c0d22441c0090001400c0c2e598002080d90988904103860181c2c910288c00d0742e50f51107602c21180746401c20001100150301c03618800945500c01800d40710994001f0040c602160b843c03100c2c02d80c03001113580d0280b140d00b00401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 287335215 1250 287333965 287333993
    0x15030f0709120525080303180c0414061504050102070311030307060603060f0c050307020a0b1b1903060f0f0302040902041103090a0c0b0f0a0c030c1a0f0702011b0c080c060103050a 79
    0x41d486010f07610b416104c65492000400d404020000e030844211940c0003444500109c4400038801e01c407180701c100c1450600c1b0001c2d10720902c1880c0f18402023185006c0c2c03106907030407130300c05802034a0510710315152001d0801c40144620380c54001000340c3c0c030003c0c03030394840c99010350301819000541c01008031201007220180204002402803c1c801c0290702070740007401c01c105a42c03003401000140c5030000e03401603c0c910258510130003407011035404000c0780d00303101d0446c40c66940d5505110486d5540d43d0700c0c46200c1c80e0300031203102c440281014030242c106a0081245144090000100903201c0c1d645c1013050703003043e03e4000701c581080585800380940309201d100038100414143d4589080403076424142e209540041040c84900c40c0c158042c14083c0900c00e40540d0440c00b19100314652800c00101c01a08403802c0400d0401c10022a2030315205110f0311004103400c0d0303100c890048650b13009030f40d213030589082141c41d41810040081201014040c550080d8400c100034030b003100d29071908000c00c1101d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 287336465 1250 287335215 287335273
    0x4090f09050c150408150f010e041101030c020f01050115110c0a0312140f041a0705151f080705040b01050c0d030b0409060e06090c15030f07091205 65
    0x1145140d40424008201600c12600460781c1103503c80c1010814090780c01940c0c480c2c0a240200032142d03010046c0243c429124000500b80b18503180e03203501444107410300940740540184080910409654040c2c1e1242c100c44410340100c0c0d001c40080b0720303070724217566090704001241c84403080140180ba80000346601c0c0c11014502601240c041413020840d01030052001411525a0649104459000308049001d56035123000d030b070b41e0319510810480103a0b4040e2240b80c001506c0c01600781d0301c09884030140c0c0e40903a88480604411517100078002816070700500f001040c8017085c9035038007a034030101c226003008003400300c003500c0214035001c10030045910032500309041c4030080155095581c8003241c2d00343c07047c1441c1000214900c02002003401013805010003081186003a11502e00e0b1304c0005002031040080c0d5044034851150401403004000301c1e491100103505060010680400d45d00c000315600210ba0301d08414020f03601c5c01119843c0079001c1d4291041e41068074241540d5254a502002e4403480f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287337715 1250 287336465 287336471
    0x412020f070e0415090b040602041401090b09010e040e030d0e010606020a0201020307170909090312180304170a0c030c0f05061315030e24060306060d02010f02010207080d0204090f 79
    0x1500540b4040040020070042c5480d01244943c50003c807980e00458105410400180303e070319192400320700030350003809182c458015100c0d01120540c4a4105401510710f4141c82d40e080070320200c0152241c0d20140412075101e92103040c003503168203080000c5d100030703000f40750042010b5042c03d0000d0300712502a005801107411018801c000350760004125181641e0140100c2c2d1000d1120180801c0b0380a09658554442d518009006406000202400800e240440030100903120300100302940d483c9510713040c0064005000400c01c01d14103140e0341041060400588580c1d100c543e452a5403d00150002c41e4285100700041c00000000b0020038040e1109607419450022044020013150744a4480d402480c440d40d50801807540c030a4020300e6114500c0c2c803c4400d850b501b01c079400c00795003000c441c1c061008180c40000310140b50000b1014081c1801910500710b4000c11b400454040c0d180d0400c08c41503640070081000042d00c82002408031000ca40b10068540d0f04001103a001d40d00c0c001d0b500e0709500c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 287338965 1250 287337715 287337719
    0x513140a090506011e0f090204050108151c1401020336100b0609030f010c02190807021c0c03061407081504020a110303010e040611041d040f0b0412020f07 68
    0x40010200d042d00d10004a51030000507003038412081c14495080621b00061a01c030003d1980c0070b40d00584252407007629210100d41d070b10404c21080c00d2164410992007010b0000301d40c014141007046015480c01905c00302e00c40b4803400c058a080e0b070f005882c2e01803000d401d0703001800c144840c11002000300901d910401030744c2d045060b100e5540e1800014802e030096031148540d00503911201103500c0214003400380c03541001d032140094024543c2c0d025a0700940501818602031340c00254003480d01562042c415801c01d103e80c0c00784000c0e001d83e0094140001d4000f28400080707120400080010b5100b6000030a41b59227108042460000180c29082401401c00511911300e00d03490412440c41000e03030700141c549098000031203202e00e6200e20b481582c0000000401c9051809050b2486980580014060705081510703c0c0d4851046100c0c544580d0407525491214840c010a110341180c0a0380e404840b0460320b46800304a000c00b9501110360f2054841c070710881d00c1d01400700c80300000015024096040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 287340215 1250 287338965 287338973
    0x3020a0f030224180f1f030b032a031e0307031b030f030b130e06150f010c0f0201030b040e0c040b06030106021b030a0b07050d1a0a0512070513140a09 66
    0x400b8003035064030b071322031048225006070310ba4064980580c5001840502c0000007440481121503420054100117810b048400c00c01e410000740c0c0c015002e022034102c0d00010b000e00c03818004501c0428000f5454041c00c0e000c503c0313501620f00e10700c1c0881c01d010050b564861552402034425541200c007111629815440c2d40042500408543e018100c14140416035010800014010000c0e00d8041d0001501d0503003011030700c840004900388102808400c1080c50901ca0040180060240d84902e0010b80090720400c00030310fa045010304060701c10b060100d00400d0140c00581a07400c883d041020607442001041135628190003940702038081500c40c2c81c91941812002901c9403440740d4500e24081c52040400c3c4a514108080e0141641013111170740d4904081900400b5503100050900b1002e007800b900110002c0c41c1c43d170001c1c10100007400c01c0c030181e00d09003d001c1d60300d80e0103203d105240500c9000082a03120281a02c1c03a6400d100720008014019040d0790022030005003096920a00e8102000005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 287341465 1250 287340215 287340217
    0x261501060509060c010f051003020102061005030307170d0218041817070f12020d080903030c0a0309020d060c02060601110a1502090310060b1b010c141303020a0f030224 74
    0x2c1410b54695580780c0004070240d0251420700d80010314a0703d82810004c0d40c281d152214425a4401da0039170382c0726214080c45107103603140d03401800d600d5001042243c000030750900da841547e800526006007011002d25500e0200c0c2c21101420180592440d00c0346200e1170580708000200c01c0c041c00303907120702d1103646134611b000c00c0c06442080350050000d0b070301c802d1040c3c3c0c4819080c00ca9001480200e0503140798802902c42d01c5541002e07022941450104488a50200030344e41b01c1e14441514078140100043c04401404610009a820082584000f00030401501a203a031140c2d554000340010706054000406000c640d56408100703400603640c62002811041544808480b44100581c0342d0240d040040d042054100d01e6144507031610400060620601c006409010003a0b80710149801c01e204c100350076908520081d20014400341d02a00a83c44c0e000c014201c0e00c028107905504079a05ca03804683c01046680000c45410200e050030021880d0001c0000c18030030140022424490701400e4402503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 287342715 1250 287341465 287341477
    0x12051b0303070f031505040905160503030c0d0e152205040c0e0603100e0a0e1006290d020c031e071a06041b05180103151e2615010605 59
    0x4c141d2100d800301400c40c54844a140901002007081040745440c0c40c0050343c3d0758144000440c0c040c518000002d5502e004000c0d01d481d00c50840c040d04d01039485240848150402c401070304e60011081284640602d2114050400301c210b900b00340c880c3c40140010504200322951083c0d02c214200340c4490702c1143d01c840351701c010b46410380b003007500c035220380d1916211807429410035002400d170704d020010410115000308403502402025107200d445090b1040d420303140d69002e001e201030729041900d03800b113042c084513652900f41f20340000d06159085050106991100c0c802075001d6202261320444500c10310307004440040200041858000c1a55408444081c0c42115002014040c400250f0644450704151031090710381d0961480000d0305080945039030001402c41172a040014080c000c0340d40079100c0e00b5100418103080c603c6071031a14030343d21081024200096452440074400185c075046540350358446817520480300b82c1700741e44958860b20b0400800364220210750801c004000c8079400200300c0341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 287343965 1250 287342715 287342717
    0xc04050109170a050a0f030905060906030402061c0c0306080f030408070506032e0e28020c01021b0c01110105010513090203190602032212050a0c12051b0303070f 71
    0x20186120300b0705035042900c1200c000d000c9000f09103144040100c407066400040f4460b44680f1712094803142032100900800d50303180d40114040000c80c0162038032001034907010f610f800d044980703483c0d542c00d0103040d942c94031103040100b900c880c801c2c4000c00040c0306c0321412020342c4004609007442d249040b941c030840c9100d4540155800004568484100c0d81540040144203201e4090722400c401281a18030b8103100f681d1442e0410008550344880844005129480302e1110510203410748106800030750008112404a41d82008050000ca50b40311a160b85564000c0c017a1081414103000034010141c0c400fa2002a64903080c018040b40e42c0344001c29410070400e010024076a24148042803400c11092302d481244c505201003441001074503001544200e941811900c002e490240ca5003e42009111004140c0d220107010301520510920141c0340307044c240d152040715040342da1584000081c800c003400c800500002110f220403082100720a403002080c2008515620744400000d040300014441d940c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 287345215 1250 287343965 287343989
    0xc0302070b0103020d03140a090f120201021f0204032001020606030334060f09110102010b010806270903030a06060f0c02090709051207090b06070807110310020a0c0b0c04050109 78
    0xc5c061621039806030b84d0b812024141c0e103680d8081917001600e40000c80c03103498400007036103c01184280c181011240c20f0380d41a00100900e06680c441400412562030100091130b40c280310000120704901a1058001200580711107100a1180024103080c0c000748194000d600802c600a10110f80d1003015501c2c00d001a44e0090b40305481c88000a00c802d4070a001d4031550610684103d08a6940c0c48074035000d02c103c6510700c0c0c03611108010b81c20794440521050200d5000b10003d9090709000220b00d020710b00540001200c071405d640e00700b0720314106a88182c0260701c040100b001c21a840c0c810f150240c200b03800d1036601400491001481a40d4a00c4000c1c000c00a203c00300b050a8060340040024040042ca03d00d1403200200c111540c4151900c600c4d11058180328160407e0708184c021994201c0d080014079182000303d4541c1d04c064001211030b030345c00d0302c15a2303a0174186145900c040c080440070f954403881c03106581c3c00c00101c006000b8110100e502010082008241c2c0c000080c08220303091103081e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 287346465 1250 287345215 287345239
    0xb0f0c03101211130c0e091005040506040b060a090e010f0e010b0d06170a0320030901050703090503010903030203090115060516030201060506071b15090b03090c0409060b03010c0302070b010302 85
    0x288201401120101c1d04130b20a500300c0e038541c40c0c0c0b035040465482c403507540c1d40350107100300c008200d83c4160030b503030040ca0032403109000d00c000c4c00c1c42d070003417580850060300c0411407901450101d61941c0c002d128800c001942044180709803040c00b40c4960060070020304025516042c9a003411424906104942081900064040340c1d03203102c3e00b0650007440745e40c84071701007000c070302d00e1079a203d40031480e08500280d402c803000c0004460882015183c8c1d4000d800a40c20310b1450001518180d1011009405010315050006800d41d02402052440d900c60f650141e16401c14060b61401d4986107105088100100801800029070250030f45110102d004000751840c4001d0030f0607401460a42c22942d001000040d100c4148035498500c07010a0042c10800c0c01000c0d901c2d89107508684600e4015000240801010070155400c90050b40e008038408082c1d52081074000005030407107a12100c1100e9281e00c175403602146240030311808091b0b5000341801d600c1c07c1426601e00c0c607194014000284104010805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 287347715 1250 287346465 287346473
    0x803010e040f050105010303020f0f0105010f030b1314010c1e0c030e0a08060f061008070e0607031101020a02070503010612020a090f0902090a0b03160e0a05061207030b0f0c031012 79
    0x740002e690403030005c01095840f804c00a40f07424a003036a190341c0744202c01c00910000380c1441014121030720300a580c908942581d6564400503c040e0000d12504130700f8601001013034200c2441b0b0940409040006240c0c0e0440901030700313404001c0a405411010000b00a44894104580f0b080f9540e0611f4450000c0c508400040c80c940d83c01e4211280c180b05540400210016040d01e883c003449040750304000854484400b200e0310101100e8901c0010366941d10001c2c14107000c1c1c054904c4a00c83e0400070103809200c020142284c00059600700140d010100c100910300302881403d002d06004404990003010316004921400181d20860807969a500010800c40042d58000440716600409401c1142404511880500a401c468501c64010511101089482150311030201c030040c46081d4079564400f000316004000042081740c000d20900016444000280720180c040c40c800e13003504074103082046414154080c010000314904004100784810396038804402c000b11800c02589551040d200e1070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 287348965 1250 287347715 287347733
    0xa170303063102090418022b1a0a15060e1302070206040b251112070e010f0f0f0506040314010b090a06061106070509040e0a0b090303010e10030803010e04 68
    0x4a040d65150007150103000d1800c0b42c0e0010058510121400d0140301c1c080e06d0300310602c44100380000d5000c800d02ca00304500041700340e1242e414601e080c1764008891400c6d201e8408800146c50802300072200310081154210607803147c000c6a03d02800d481c0714890814102034110000b402c0c0952044091059001c2403000e07940445d113080d035014040540b0755907200e40489407a006003803010b040c080f41d08144a20482c201903031481e12600550780c50348150008040c40781c000001c02147c0e00b54000c40001044170b114010501c0c0c001c3c40a02e0744d00c840c8a01e0003409200103041e60b00f211008102003001004543c0c1c4c0c1900b03450950b5004075881c4070910110f048240108a81250b00303802980e920100a41c1d0030036540302d88202c0f80580c64800d11840b0b00140342d0f8a4079422603204010410500800c00c20b03042c180e0001401802070400c48810844503241c2080755030044540104540c00080144100c41168110940064112941c00700c940e04540d1002400d010500503640c0d040a514001028400426 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 287350215 1250 287348965 287349019
    0x201180c0b1c0c0e012003160807051524061b1903020a03030c05071502030603010f090b09161805060f0d1109010f08030301030f0602070b0f060a17030306 68
    0xb001048044140c12010b0030340420b4419560210b140c420520740303010a5590340b4410409050081c43c87c080c83e00c03040303c0d1311440c1c04c0c2c41900c0c040d4040c0000341c0010b038200000704205d103601c644400d051402c580141e0003442444105008100c3d080041c040c90744540081e5500d01200d81c0c404464039107420a9603140c100c41380190405d00240119180615801003050810180240d80a0156074040304007a01e451160040c000c201800c1400c0720000a01d050703002c5d5400070700c02400031070b000070201000300a0703441024013610009601024851035040800c00440c42c03006803480d2441d800d00c1e06030001a040402090800541c1c0c8030000158146e803410001b0b49000d90081130400000c1590900440d1a01d0754443d4078000c2015100210b282d40d8544290011949800020b506c1c5a0940c3d80e445150362a1102c202c42c059001d1005800041002c09268451024581d2602c41c5260120070400b850304682d00c461a4000c0c00a0800194040401203982c05442981d1101406c00c0315419287c1442682e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 287351465 1250 287350215 287350267
    0x10504180b10180b0c06180f030a17010807050108040b0406180b09070e0603190c0e0414060f0412081008010f0b0f060a090510030b0a14010201180c0b 66
    0x149403002e802c41d030001002c006920b1055070752545a030704d4000014040c410540c0001c031030713403100c000280d5000c42e40006104403120301090340e00341c092094000d841d58000c0c02083d40803070b10b02c0e0f0b1524003c959101609004202505c010030002d480c000001e4070050014001421015000000a0074000d041c0c0000c1c001c4e0210b00c05058101c045c0782000070170140c0030b45400c60a80100000000c560322008078003402114002c01908958400c140d9021491403283c1c4100c400c0070014900181041d007200310039204500072000f03028250020b8041d241049030090207045100340503014440410040b030f0400100c0c400301d041c2807004c0e0f140d010950103042d01c5540400060340c20000d80003c8042c0c90303000091150001c1d103141030321800d010b042007500d00600280e03500044a1040412403482c2905074001502d403142030010707500c1c102501050f411407540e004051224254031004070310307580c2449500801030321000c01c1c4e0340c02043d07540c8895403424a440307000107092000c1011203566480c8040520b500070070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 287352715 1250 287351465 287351479
    0x10e041a0106170708010308090105070501060509070c0b0705032211130b0a0b04030521040f080a030e04140420040207062003040506071805191a09010504180b 70
    0x1589400810101c03c0300740b40090080d04001080d000c2d40a91400c6050720391040489003480003031801181c1035081940d09503400e41d01d40070005120703120150b01c1e50080209030f560320000501c0d4141201b02d000090202c02c01c1110070403c020492030401200003041c213940041c1207001c029400d258000c0b0340400001980542014400030f807161440c0d10100803170100b5600c8803400341c2d4420001206003c0c80c400038005400981c607030554202200114258100707044021800c0c56100c0030a03146800040d0807103c143c0d40410013034010f0580007001e0700c2c00c20f40200ca0034454552a401ca1b04000480508024221520035030070318602c81e2080c9041d10b1003140600110740300c02c81c1d07003450009080c100310250006007040480c0c0751451200e108a03031055800000400003529100c1c001c503441c5569133018840707020700d800301041c00c1c1d07245110b804c1e442c136420040078031a40c02c01d004120022901145146042e500700b00842c02e9036009401e880403039041184400c5194072a004440103088001c99959000708 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 287353965 1250 287352715 287352719
    0x615070219030204050604020909150a1701090b0f01150809071d16020607050a0c150203041101090801020c210f130e0a0c0c02060a090b04080106091112010e041a01 72
    0x190290041e02141e00843d41070003107844000910040b03100790300030180c005100a000410442d1001c6607801c0d1403038040d10208007981d8841041c1c0d0001d0a0042e48803e99455030b074220b050017001034106410605d140360304200c0d0b503d01442405a14000300c04c0c0814402c51100003021044e00b4000b0400074090412121040c8064080a111891044a0310300800d9206500710001a20011302544950710540301ca03031922545820030788203d030710414100d55211109135200c4c01c03c1014009917000d644110001503651141800140c109100d5421044080c2c0c414003090003030480000b18205440009030100c02091400800050b0070702c61072100e803003a0003000034960200c4020404843c111420000d20001540b200c5400c9016580c00c00c030b030800000c002034409805890680d00030100080581840e51081d5a1483c8087c1c454000d07a000e0b41e484d135580cad4000c10440e0300300d01440c0140b03200c0c090228541200e811a96800c548180665a04034894900140400c1403202900790140f000c40005040b41da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 287355215 1250 287353965 287353999
    0x5010c0c08010629070804051509030a03030203060f09100902090406032112050f010311180f1512030409090503130f0f080303040201090501030b0a0906150207080303090606150702 79
    0x11454113914244101c0104103080200d0a802a240303900e41c0251010b14040c42c00003041a07100110900b25400b1800f000654130307aa0b01044401d0b801c910230340f000741e01c3e841c0c80d104216527502090700e143d000d04604001c1003424902030b8503100070f031914081d0050311042c1c9c01c0040380051105030801040c4040301c10b5230402d4050380f100202c2102c03105549000460082c40c400c035007914000d958081c0e010589400520015078424031002c90701501600c5101d00301c50102c2c806825031800d907090401000224280031902c0c1100300041004081500c504003c07502410400380d03680311b944200142c0c41d036512034a04c2005000c0c01240d0f100c0c4410440c10031002d031504200c0f090141d142c401c455a0484145c2c001888131000300940c0d106640503125801980d24250041d0003812500450a502241410010400c510701d8070689000d4480040395900c1c1c030306900006850401b603508491520351041c0b0030081800c00014941b83d00c0902a00c0071306592180380340b6075415000380e4100a521201c0118004461 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 287356465 1250 287355215 287355239
    0xa0306020304060b0109140f0d020607060e0f0309010c020f010c05070608071e0813020103061205031e04050a270e06040201030f0c020d0c0c03050f060a05100e0105010c0c080106 78
    0x580d000b5501008103004e400700540d1621030300c0c840c0d40c07503e00300b030300408169142803009141c80b80d1000d0040d0386c8009196001600d290710262040ba031450f520768109099030b0b0308025080c207040421000710314005c40c2c000041c00c1d441342070344c009224040c6d1300c0034581240d1103140c3c00385480d58007800b140c2556840d50000b4148403000c9640b1400039021403650014000d003180200101d00d06a00c42641d00d0301c4125030f0322413a440980d001d9050603113400c4009120a006c01d07080445038007031000365884581d1040b00d00041b200d094290b9400300c82c140002e07c01c2d03940b514103a00459904042108580c074000c10b00c1d00c060800b103254410500d1501c0d446282040000c07a02d103105600c00d80e403c01c44400b0700701a02003105c3c0c40350256001030b40444c0044011600440b500403185005000303009603640c0d6030351840c1c50f08050407003042d001e0b00f00005105031540d80b4050950807907600702100324082e0074101340031004041403050504005144410006003c0c40403043e2028bc80c031324009102c6d503a111190f81c206 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 287357715 1250 287356465 287356471
    0x1360809090c0c06060102070302010906030b150f070c0e040b07051b0d0915090311121603060c08090102180d0809090403050901110c0303040324050109051012050c06030709050a03060203 82
    0x501d00500c400945d140d031010451600f500e03816107500c500039040c51002c4000341812019160403600c0b00c20b0910b000021000648511701c4504c480070f655044910301481c103241203500000312100d03070b001808009542a007085a02005078549584c4403c04a4680c0040c49082c0b2035050b06030088c8200d20701842c0c6e0204006099608003500301c203032000010801c642d000c00920002d003428245440342c3d0f19902e042403400da00f02d61b011040302d0400c20340642d030014889481c1c1c4101e680c240da4880012049401507819680141c20000860030500395440e07546c80c02d00030729447c51041c0c01a10104007044400000e585003000b015000b00d0a5144c28640684a54400491940400c460029075000d0b0207000660100c03030400900a1414145181d0341d40e42e44003050852900f407400b00b4540c080001140d40300700c41c02070181080105041c2841c0d94880c402c2551a040180700c0700d00b44159401080d40020120b0246005496a0703580380c0d50100c040340e210341c50b44c1140380d004070004000010300400750003640c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 287358965 1250 287357715 287357737
    0x120c03030708070206040309090b01050f120f1008100b0114030906040201080a06030c03080906220501031407050a120e0a030e1f02100f1107060c0201360809090c 71
    0x801a01c6040c0c090780d884104480c01800102d0b0001c007440342282755080002100018109103080401d050500d48083d00002ca100d0201401c034410064845ca4501000760407050b243d21001e0841d0510410300d80b202c40c1c40921110b45c4dd00c1c0c0f41310002c00e034410034894161710820302a041c0c59040c8000400e40342c10091314142c4c005480200442c4007465071b4454501240da100d40040103072451943e803010103401c450f0107194812000d000d00e0340d404403601442d81c0c0c450036441c102e0070300e642084009800c843c0b07141c400c2500c00c0c0c0381d1010401400d400ca0111401c84040d81013078008a106070303640c18040c01c4010750401c1a401002c40800c00c1580041210b018598115408605101180d400100320701020b245c02d801171b0304c49000301c5501d0516500450801e502c0050114121000d4200714800343d010311070489001d90b54403540c0300386a5082c8510001919810501c00e81071007810000c80f03401c094030b0016200c40c2190b900004c2000700100c1102d205100c064180d2201c2d02e80b5210110301c0c0e4004c000d50781c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287360215 1250 287358965 287358977
    0x2040b0909010e1306050c09090405060103050d1e1803020a2603030f040f0309030501050c030403030f140a0b0a08010906060f0e090312070c0c080706090501090b090f03120c030307 79
    0xf01c2e59501800c080d038441d0040288071015520603480d05805054041c00604589504105101d90780e1111103506109501500c01070885501d140f5100d45400c01c0040800104001d14860035400b200829004064421902d003002e0102000c001c40d5495656a41c802036010f0b11543c1d00040e9224240740100c0900d1500941407440c100e50200c2986920045400c0d00040310341c0703000100050b0318000e500d01014000d00e011003400c2e0301d0742c0e45c484c01c42d40c0039a0700c400501c00100800c0100355150040a49511a44100b0310200050740040e00e000000030703004500c22502e032003210304592174402c0380c180141902c200a00c10a091400c080c00109030300e001d000b102024100c804103003821510003080c000c1c001c2200540c80d180802e03040d1485410060030010400c4104203603d00822105d8030301c0c2011704084805022014500741001e407100b0250340c00a8144451000100023100b8104156840c54406584203902100360000103400c04c85c82c2100c01d5045400800d290380928400406140314044544400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287361465 1250 287360215 287360219
    0x203122806050a090203040c150309110105090330040e0105010e0907050306013506210604020415051c0209100b030a0908040b0d0203100617011502030d02040b090901 73
    0x40103a0707285004068002803141410071034011550b00441d8420f000c0d0034000401d5450303030101c01c051610842a040029190755048003800340f030f42c602ca101c01d002400d00714038120b0414042900e82041c0c4000d01e9452280000348107494201c0b410b07000c203400920000903035482d00c8090540e140070080c0241c49c0000c1509485003960f040002180b4040c0a030f43d1289415a40e800004440e44501c440c100c0400560155030310580c81d009000c807210a0303154641c940b10f145052010b12000030301040c105009007858003c02003002d4408150180c110381c05450220391040007001e5503d40304004c1c1e100c4c5400c6001c6400399405a0300010300f24840f94400c03a002032454031203002c0c6098840e40e07409100705105041000c0344800b07166901010549100f6801f15041c180da6100240881e0001c000c034541140e0000304001c003003101c070b0381f803d0003420703850500b020f1aa400d134904c03080a0304140038280071805140b802203400790003001503401c007600040e002d540d55600d40440070b040340c0041103118051074040d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287362715 1250 287361465 287361541
    0xc0c080120130306060e07030f1a0d08041a0a0201050f06090a0c090b03180609210705010e0616020d030b1c080928140a090b01020312 59
    0x80e030200700e079008041c81d101107041d40840d8003a404403071015841c0ca07001e40008009420350150400511780d0300a5840d01d4a0583d40c0501030b180710024903c4000c2c03401d4002000b102c110441840d0f1000305441d2022038070003914200300d05100300d070003040d82041c443d5100d00b0f10840703510040c10310050a90080c012a00e5541408605420903141607501c071079031500103040c41d400d41c0e0050400181074501381105596840c0c0d50002a4010f40310040250b484c1d800313801000408100040c0c01000328001854082c6400302002d420b400944420420b1150000d15803083c000250004220090b803402138402c00c0c1050003281c80c0c210640070300c0c8005400368944296009000784240318100d400a002c07401ca00000e09000340303011410b0350301200c014034140804200c54441c0320411440101c0203004045c4201c1034151043c2c0071060307a108011039400104450625214a43d01c442210070410011440c0c500000050b0300b140649a0b009203140d00d00307820404420314408140c21000b840303036100c000175003108107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287363965 1250 287362715 287362721
    0x1030c05130912050a0c06061719020d0b0c0408060903030a2a030e0f03130920090609010909180605071704080d020f0703120b0402040819080c0307030c0c0801 70
    0x9000741c00c01c0d04a6012400044c02032004241140a901d01041d00c65483d981e034508580a070381042c00c00480c600107500205070f0420000c00111f0062600b10040c540b0340d800030301800100d180041c11071040303030007180f500c2819a00365009000e5000c02d54104c0d142c200c6800341e507600100ca26510b40d5050680d0000b45250107001051084040c01000621480005c0c0550107804018440f1209100704144c482c0f00202c1400a404501c4545040c526a10720303200e4483e0665140d19010100d078034100001069041e000c108481c0c1c100c83c140d480702d80710072056005032031800303199004110150030404180281c1e401000c40210403440399004015a0f129020300312954000140308800680440c0c001c103020131480b9015042140100c4005447e02c000081d91915a4210b200101c0c0850121400014410082d0040048461040d101107013054600f035404c50780c40310701258800507540340203c1031080c030030314900322152072440e802101c1d52100e1030b20700202103104014094910071550800400d1100041c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287365215 1250 287363965 287363981
    0x403290c0a051204050c0d0c09110f07062d090629010e030f030a02030307021b0d0212210a020601050d0302070302090c09030706080906070c03122301030c0513 70
    0x50b030303424107090f18001040014100a40103446038803941d0b5440d44c06603983c00c2c44a0666201c1c103140f901c1c061824200500f941d03070b80780c89910f0a10082c4440c002110000099070b1300244c01c1040401c83c11907490486ca5540310300380c003001d4025090b11507e056070070f250300014000740c0b0400c001c200154111542c0542044600e001d2070307417000c10b45a005040d61048591441201c001400e48072030070ba500c00c0703480c0740d40c0c0410324010142e0070110801407141e0701405070440844540c0200031400c0d00000000f070715a0104003009104a48001c00405100d60400400100d50302108500024030701c8840c0b4003900c0e40100a0100043c4a08800031800741402d154008ac2c0503416001403411038210b50030445003150080000c8501c010134007c80180d543d04010200003050b50303458042050414941d000d04003000184080e00740807512405100082d802030b48003001c00c1c000038001400c107034030800034280c04040d1690074a817641c0340e500100502120f048000c0072030380c00300c0c1d5250171380c88003001000548583d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287366465 1250 287365215 287365217
    0x904080405040f0b1804120206040305070b0a1805010f0f020f09100c0503030c03040b06030d12050621062e0603051506030a0b0102070801060e0a0209060403290c0a 72
    0x900041115042c990030449002860b290f003c9a015001c40214901007010742203400318200c0d03072051000f40541601c02e40c410010300d10292900b481d00c0d89014080e07200301e01c2c00a1950402c44001a4190490750002000f4400004205a100d0160404501034100400101e0314503180c04e00c071010361844ca1080b9540e6001c2d0f195154203200e800000c0018040609500505014040848400044081c00118403030b00348042c100703442c2d05107818501c805403c0180418026849100c40b0424603405c042c022041e0307a0504408682c607956500460030101c050101000254106640d20f9100310000c511144100040780d00b86202001004602d0b4a5020991204500c218040414003450384a41c0095501c915180d001030030150689001c60296401240c0071015a81c1d1840d1140b4103690502c40c4400400312200244541414521030840d140c001518008110758005102007040d00e0340c42c180d030011900a002080c500b40350254005541708090500100700002c140003544018206050320007003441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287367715 1250 287366465 287366467
    0xc0903290c0702040b0a0605130501140714010e0a05030309060a0615030207080f0705160902030903041e15020d03050108010c090e0402040902031c0206060406032a0801060b0c0c090408 81
    0x1030100c50540c82c0e02150701a40c00c243c032901400000d4507908410001443c42c2d17502c1e03a0380c401c800142008040300c40d42040307041114000584101e10600c80c00e84000580140c01030b85800054001039004000780050b40425005800b0208180300010015500c0380b1802c00a59503d07903940e16003501214003900032080c44130740c40b14156240522990203400c03407604c151246403909083d6080748c141a0818041118198003800c01c00110027400d400280091620781015400e46c1010206a520f80c080d6000d1200003460603040d86001c0410803000400425080c9610300341d20004034002903c03034160707005110102c1c0c2400000a040070051190300e44004240d641e014220341019801c440d40300303000c0c000341c1c3d0064440c060140542e506009411840140d540081107500c0d620740e0207814a0301c010260352166281c00c070100040345500c1d6030400f9150381c1030b030311051004004030f450685644a4000018662900c040031446800c620000c00b00220f20b0300880350707044126002c020f505030b8204c80080008070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287368965 1250 287367715 287367721
    0x20711090709060c110604320604050d060f020f0301050a0e0601050d0b0105090a0f0528030f0812150f04020a120506030304030213050703110c1507120c090329 70
    0x110990143c031110381702e12056152009100c0c0040e41a40080d00008003914070fa541003d540001a554284d08c480d88109421604041d50700042c0e25000314400d10740109800034040c0200b00081c1c0c00100b000c421418115201c0507483d120178000e4000b40070b024050303030b0300d00c42c04213088a10b1400144541070581d0307003d280114000d140700250a04070b02140c140002071209a205554608010003e01154107468581502c0c0070b0270404191440b10021078407080d03144460410b0221012024240c7e0f03003144c8004205012846e0420a500c070700c06042c1044842201449241c0b1801400d1040084040b5140b0010b9002031003000205cac850503a01d2030101d00c0d10b0b0700340c41e88241c1a0b0001ba60001300102664241079903500412080c0c0b0480c1e240c00c0c0f94650391020084a10f07094800c044c25014081c1005040240c84c200c0e050303039800d40c004200341e0b8840050004010340c1c440c07a44900d940c030054009204e031000500001c3d1400ca03150000301c0c0c0c10140341c000c00384279000c9004801c0c44e1000458900c04162 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287370215 1250 287368965 287368967
    0x120304060b01050c1b011e231c090503120108060f07050a0509120c2808030a0c2006160b06030303130f02040f05130501061a0304030305151302071109070906 69
    0x1a0717000c2141400700d50361881810303240d00c1d03021540150310358803004d10748003021201e0b8810284420310340550324418880407034042c0028509a082540201000a141c0010f040c0f862650160041076190044100000305d201800461a14003411b8103e5415880b5200e060090303946021342c0c0c0507031001840a0243c009076240404055121503004016541029607500110344042050030740c80b1800b24400c2c0035104010650180e0f070f0000e00e4a4401303141040d40e10103000300040b140c044040c281c10901500c602030300c16800d8612961400c010001c40d66801c102d80807002d41e0310055815260490300384005105424080b088922804540e16812103001080d501c0428107503070b628013a078100d55190b0308403480020354454140074140340200b98050350b2240c41c1450a41e180c5410909100300d030b44044441405546041d640c01c150305050120301c40d40c4000303010085100d040f88003513021559055006da11200e960082c85010301034214800c00040c20750070320411000503103070900000c0204000308026 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287371465 1250 287370215 287370253
    0x1060c0b040c08100608061005010c0b1929010e03060105060a03090501150e09010e060106050304020409020414060f040207020901090b03210904060e0907031b08120304060b01050c 79
    0x40d200c1e40c0e1403064035480300da40625041341c04a51042d4203690798414080701c4810403920303500c1074107030780d40c905540d080c10002448070f802e03000003c00300c9000030046865844170940c043c07046000ca00302003003030307104d10821614520b03a0040442d1b0b9908031036086070b10b103500c529900c40780c100c00980205034503441d04050203030340d502900c400010940d403980c030381c00011000e014200c9201c0804443c0340080b420201881e02d2a98080c0c003080311a0315003410b60078640f1002c94542d044030b0180c146541c5a070740754004140a4140280e000354040c3c540300c1d12a01c00c2e50340041103030051505071008207550b06000103103c00ca20501101960102c01ca00040160640e541c110082c510000b03401e69440207002d14100902070140301f080140310401190a08c0d950900c0d108010007040354050041c0941030490034a03461303e0082c003028000e0611405011070019142d00d0f0003004001e0042100c0740d2424245105900b038205482c00c540c0141098070f0201c9035031242080e80c1003410610013030200200c0c030805042c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287372715 1250 287371465 287371471
    0x7170304021e0a05060d06060201050106020f060406051e09010c0305090a0803150a0b07060b09131208060118062a02010828020f03090f060c0702011d040204030c0f0e01060c0b 77
    0x8005401c140200300341d11088050901c0104071b840118040c3e0030000082d00303464058001030115448004014080301001441641243d000000026551034040250780d4400c030703210b8034003141c07d50001442002d0f68158418901c0900780e0341c0c10003413a02e0b191400d0380c0310f00280c0c002801c812014404110018402c060026408400410100d901130380e503452241d01360040c2e0000c0d40c7c007032b0342d500005490742068104d15510540c60b181003089030041d41d54024a9410a19112080059010020721503034003402e80916000181140d040707401ea0b4a40c0002c00c1d842c00d001c80c0b00740c0500c001c40d1030032a6000d072203034070342e2141c0d030503182e046550342c0303404100306403a241418075041d0b82c640407548840500720344024188910700c0c04120390749151041400b8604015a031086015500c51001c00004000300e00581c0c49260342480c10b04031280c40790a5052102c0c40104071070f0b0380a03200090000800c82a0b0312814112584880510840c685d41c00c010408800240f086030301240c0c02845001c0010381100003607038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287373965 1250 287372715 287372719
    0xc11030717030c10090812060f031903090e07091a04030b01150e090601080a091109010b040f0905070f03110c010c0513142b1707170304021e 62
    0x6445a407644424000080c460203905542c100141c43c00c0805803d0007010711041c6458001d000d820b4032555015214810307a91001c0d0a4807182c00030a0080c2c2c0c5a41958201110040403500e680001c0003800c04c0c0d0070362240085000c22200b1b0300008200024400291040080d925290151440c0034449070f404032111080d1450308604120100008030114a2076028117105000400c8004c1e10b56409024080d8035000c092082042c0001c00c520741e80c0c0400f0702d039480300810300040f070200f4140c544245003004100400c6c0d482040d00b40045406881e54018000316061020b14500d0f071982c549154080b01c0c0180c6501000075001900080c1c1e060084d0088506080c0505800e03140c06c4a6154850841c0c21030804200001c1000400f00105000014018080c0280785030784644050701d140010000304101180003060090548412110090400034121468120b0100c0e01c40441c502001020396001354821200c48040c1e10b0840d005640041c241ca11030341c0e001d080c1d10781003030021401e07007004501036040325 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287375215 1250 287373965 287373973
    0x804030507050a1a0702011a040b0a0f0306051f030b0c0708040b03070c03020709020406050318150414070e06060d1e06030503040312171603020403020405070e030d0f0c1103 76
    0x7000180100304200c0700500072202c0c1d551002c0e04020941c03030104054007a80442e8140040f41c02c0d80382120102c644d0341c0d04210b400061404807180030414500706544560700c4041c140000009010650304114841d00d0a1304400203001443d072011405052a0b00002e0464040000007948082c94a4020f1181c01d008105190910b641c130030400c1f0a50f8001c941110014000c0c031508400c0640400c00721000e008480420b50515003450401411408020301180300c00010001044035801d003405190b50403032000e15103034850b01d000c3c14183d41c0800f025400c18120320942800103001f000040c210380c052507008100c14504a10030310850080d15450040a11348043d04401c02c400700b4413482103c00851050010355103440c07079414406402c0c8030541c052030501c4401e00d50000702c1c0c0d20540c1d07020780c886005c0364114891620000114001c0c002d60300020b410a10781414000f88907000300da03000040b8003c9040710000c0d1002d07801101c1e0a140403c0840208103c0c09800000400b09101c481c4e140e1400b404507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287376465 1250 287375215 287375227
    0x1a011214011803030b0f090108030909190207050a0c0b040b0706050907170c011218080f0408030a08090d0c050d201504030f0503090a0201080a090242030708040305 72
    0x8802c0c6a00086080f80840e5880b241c200f114149902a84480b080072030b088031181d858005440d880307110341603d07503218184030700004030380403041141d5103960140803c0842d1100803518003503070f4a540d103071415560700380c4010000440c540800202d0341500c014200c154107100e40707a5240000b03010701a05c000c49600035001c000c5501c00c40c4c01461103c48010740000d1030941e00c01c800243c28440701c103500000a030f04012818045000302603080c50381c02d5001c20384640e02d10018004103a107000300c0c0c11580083c080007a0360900168880c0010380030f1140c423020fa0f40d40005c2e0352030666118502c040002c01ca45c00c203450701c0d00d00c207001d8013107407003044065142c0c1c5426401001115080112003900b1601c00c0d1080b40031301007410f9015401d10340628850621a2071400c01c1a031841e6100c50103000241042080381c00101c44260581100340361781d80c0039003c503a9286828007400302c80d0603115009070f114001c001950001a0058100210101c10300552600d513888420b411106440020820b50502c142040341c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287377715 1250 287376465 287376491
    0x161e110a03120c020303130b06030a2f0315060f040605031903020d090f090f140403020715030c170a0209030f0a021e100e031011071a01121401 63
    0x21a5004030720039a100307203620b0038110078002102c1141469208651041c41004115a522505165130030742002d00141c07643da8500c002851311003c11b100038000c000d004180e4001a00026444803210042d000c0002d00c032941e201410b585103202012a521019203d002c101641808260103141701000340c4045111500c507804207113051003040c0c40741e07260061502081c0500d94140280c80401d141c0e860014030007071070f00700d809000c8441405604d81039543d800c55494080e40a50260b020140019291081840c050078080c0d1a0002c510462080000707804001c00c0a600c01d00c60790344c00c020b6944500c041d10b05403c07000c8018000041045102c598200550441a41d04001c7c4049036000c00c1d00134507030411948140918481400c1c0c800103150070303082c007002140da81c0c0110544a0011441c0c08190714980710002880c0c50440001c8810140c5006a40401c254004c00140b0b8124051502d10f07c0580ea11207800032102024401d2140c01c4e40000140381c000384561080b042d41e0309602002040811042e25 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287378965 1250 287377715 287377723
    0x1c080a1a060a0504090605180103110307030204140f0a05010f090b0a0e0408180303040506220b030709030c17070614130902040e0702011505010c0206070b150306161e11 74
    0x100030040f4402090800132030101d0702030480681410340f1149185e20400e035485034900c0042c0001401d04c1c011105040c5680c5040003580c1c003d6400900c1071007401042441006c00742010b44402a0b42c5540070300040403205103004450407501951010f5603040d1800502c1d05c020800e10180c02d07440301c01103900043c00040b250b107082c001c034010900d1381d82d1850794080f12259211070010460080c1c1041c0070801650b07549106a40c03103030032940c43c3e07405d5050391040e84449000c0c0c19049030345030b60404818840340b96440054001a6032040344164074168031418032510407103a591b01e0700c04603446070f1414008544940500c00b09810045012403d00e4500d112150120b40700d60403402c50315501007410040303110b5451170941c00000600080103032150342c100a22000195018403418061036592910454640c03a0844a0064002640c0f60141c2004401850107240ba181c1041c82407103980d0124800300078115030002d003981d00c1d071600411442d0340d22146201d0800c0404050511020410075032076080188 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287380215 1250 287378965 287378977
    0x8162001020a020303090d0801050307050909010e100f0f0605060703030e03040806070507030806090f0f060d05030c0f0f24070903120804020102011802130b030102220302031c080a1a06 81
    0x3c0c01464491815070300103860142d4240e52041040340e008010030003500c0114030b50043e22001d803030801c955a00d480c40030f405401d03007001801c11480b5040950382c50a16940c803900b550796130000f09114900d0350aa500b403c1c0c6600f8054507038018010130181d00040d000c1e50100f5600701007001500d0920303030b940142608240040b60341c00d001ca02c001403100101584003c43c45ea000c1002c840160450600d41c201c600ca00100038440a40138407000042480d540d81d100d5804000c2e6400422a59242900511207807289410072007500c4a2140b17403402600c030080803901d0403880c0c1d450700610101404000305541040740150126003841503140b03000c40450607032410444560300716107503680c0030b003040c1c4002800c40e81030b0309050011a00342a40a40165266400440d082d41d225802140c088100320010f40284030700850125070030902640c1c3c0c030441e51042d2204040724000c909442e60103241d04d20b271203441280079441c00001040d9100080103011350764061780c8a802c0c5c0180c01e5038940c840401164543d0f00c14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287381465 1250 287380215 287380217
    0x140a02151f360b030304141905060a1b0f08031906050303161a090601090e0a120309030c0803010b040906150203091c15021908162001020a 61
    0x1810031841504000c00400c40281040d1a507040c0d003000103240346480c9440c0030040060502508515007001102ea0041050010001c0c01e0300d07500c90380d9401c43c0200d15011400c06010741501405640007801c0c00100b00100d49010b482c880c40c041e4030920446440c0c00744041d000c10b5000760b103221004595075091000300342e41305040741907890034690210240840b21203802d44003141170140501407030b2004010f4800380500b07050080c020400354a00740e010501081180c0181e56204810400040000103415040743c0d2404010418980710307698030b60f103400003030f40094480c003600840c0b6031455100746d105c086135a00a1502c180e498000f6035551f103203039100f03a014124a0724042002d003c5914544140c10080200e00240914070049000280d01c90180b2250b1a210342d200b815200e942c0c0c03503500c00304642580d00100c1f02400e05001c030f103200000e410855411410303204441600e9a068000c007140c2e40600c1640e607003101c040d541c2900442d00f07070082041a100802c003407100f444803003809001902e24a549 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287382715 1250 287381465 287381491
    0x60b0702031608070b07080904050901090215120c0702120d0e041107051b19030b161d04020d09060203090c010f320403330903140a0215 60
    0x110380105480d001c003400004180078980b0004200c50741c4000350000c2150605d440c603039160581030070a030000c1d005058000da0001e06010400080c12019442800400d200b145e0514080e464140b9040c402d000c2d01e1070030703450100c03002c001c20341031380e8184003038000c42d88010a080452400b51503440e043c8103042e50320002090f5000b1084000f840c00b40211005604101d95141c148900307038442550343d042040c401d0b01c070301081041e000055180c00c8180c943d03181d8010004036074107940e407902a010220440c0c16000d441081d90080c42424419400346410810320019800540090001c2200075403141c1951602c0c181d65030082d800240b07050015601c55403150029041c3e14035a40c00140c02e001d4101070410401610040054034901c00c2806046500c04000c40c0b501c0f0380040c4044590548660381000e0007079001d010000141010352402070321100c4c141c0ca8035404c81984800c0350026264540070080114225070403d130a501c0c1d000740540120100340c8100d13030019841514072412035405503080341c3e208034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287383965 1250 287382715 287382727
    0x21b011e110a020c0d02030c0612040506180a1122060f0914010303030b0a0e0c090120071802040b0715050c18131b030e011407020a1410060b 62
    0x2481d104045805600c0001e1070b14010035204001e44400f00602c0e4144200d03032041511080d902c04004005510001070305590f95003c4104001e03080c0d4204550403942489503800190002e10f103641c030342501d40919001000c2d515003aa58003072048984105154015503469848920300b4100101c440d002c2e01064070024500303040000010000042d50015481c681c18200c104203608200300219044a406141c0050641d00c0000040c60301300250b4414100c2d49800c10602245032407620050011380c000b62078500c5015902c0f8504520705410044c08803194014100c04c00501150034031000c0700c011607000045c5060f4130b480d80301c0b0041e00032003016220b6000e11094022060101d01c42c032034020039140c40807800d20500800c414404070b1074401e03c0c5d00554800710007544001c5035401031100240f18800c007110910f03003080000c0040a104d07040d10100e600308040300d0194a013180600b801a04c140d8041e0000883c1c913181e500304074000f030008440340c0c4104901010210180e110704800741400b140400c0c2c0d120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287385215 1250 287383965 287384021
    0x1501090207140105060f0915031f051506040b0c030405130e0607050405060304030e01030e1b010e0109140d021309030201020307140307020601050910030c030f0b07140904021b01 78
    0xc2d40078a03482e9032980c58502440100d6681c0e003244c0100010817140e42516a843c200c0c000900c5000d240706540520502d0381e809032028034440070a8510346c03034003410070269450b27400b00c0d0742c0c0100700c444150304000c04010510041c0300c01d00041041c0605039045910741661396001c265120a550f00a09000b66210300d2402c9840090190540118032854000d08003400d00700000c50306d01c000360008041c0b00340340103102110f074002e4002041400c0c11318103940520a10588131000c880303010014030b00244200003082200c2d030007409000143c0e0941e4040c00101901d8400b1700c49044140d041c240e0780300d42141e5050750b90015600407028842e01c06c4d40056140d0030190b802624000461101e200106028000c012210b5400210309045440403540e4074180c0e154003000f0700405074030380c101502000d00c114011091000710b02082c010203204010310642c50f940c108007140c6070f00320302c80848074000c7e04104d558100d1410f50050448080c288000301945020080c405003101c0f0441c200e6151030700d81e1f8400344114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287386465 1250 287385215 287385233
    0xa051e010516090b09010e040e010c1b0c1a0906070507080622150204120c0311060c1509071508160203130504090c03020402210603210c1501090207 65
    0x20001e03650142c0c240b00692006042035005005049007124041800d00a580c0b040070f0300d0b00301e00c070b0141c03081002051214030280072300b150311100000b01c0e0305204081625010302c1c0c005911070707130013a011074080b500300240690750403940c07201079285c440305000b2240d00d55030311001001190300c00e20007881d000346840000e0341405401400c19406014a060080392003501e4901044c0d501c3d03210750710540e0503407408c441034028040e503041060101e417590541d500b00010400882d0589000d2040780070310b01d1454042044503c618581d500c02c45c0c1145104048061480d00c0140e00141054180e07004151241503002c80358921584c40320014090b9420300c00c0c0780444074070812440d000c600c00342d45404102e59041a503078003c2d10a840c01690741d40c03145002e00900100840155500400130355a841c3c05800881e0721444400c1c01c10fa100c4c041c1300c0812032500d40061044c1c40e8802d54420020b0041c500d990790382c0c0d15080030100350100c0c0201e510116080e51404e41d400d01900c03260000503103c5070682000c2d411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287387715 1250 287386465 287386471
    0x2190611070302010c0809012102090f0a0506091c05032106011103090d020d0803041115090d0605040809040c020d0306080601121e1203051603020702011706030a051e0105 75
    0x3290890201880540d9002002c2a07441e07400480807030307440041c480125501c0d408440c0302c0f0341880c14540700c0221540203800906045000f115080703001e001e424208000e8105620139103610002c10001d54006040c001c50415100c1c0c51160811034428031502c5060031680305103075045240c0c2c13150040c0c20814080009442c1c0002007803070a8540c1c44201e8400d50391381d10444e600c01e0b10659843c1015421507440107000d9a14952001e50181c49007000e10701258154100c038059072041603560040103241e40c1101c01d0701c3c014000117085503000c0c1c2560311410004c10001e0400d6600107002c0144400c640c5031030291a6182540e94020308000701100e50043c1190381c0f079003107184144c018000410018081c50108144190440b618040c143c00400c0444100030585a00800c0308405000d40b11318150540c3c04203201e0030f00c0c00184210f081d038450f0101d0407403040020080c041005030208400c4000668500c0d944150b02404440d15802c0e5911110301d003070801030a02285144841e060740404000b0301400350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287388965 1250 287387715 287387747
    0xa050103030305070f020d110f100e0607021218010309141b0a051f030212070801210b040b0a060b071103010c020a0203030f0a0516060c0e0108151507021906 69
    0x405e00111500a4031840c08a0030384042214400070302440c545c0034007030704001920b000c08541600303e0300030b40d000107001203102c9039440d40640c0b40040e2a0034000b164005e065070b0310a840034a40204540001403001342e101d0000c0c101940c0e4070355940000c40000d05640c100003100000c0c1a5688101c0800000001e049045402061564030030489500c3e006a9100340f0720084156001d43e42408204400038022961340c1140071132000144021242c02c9030301a0305131030162205039051900b028200001e03524018009028407905030024000c9001281c1c0c1582162103030340e0102d83e096544155011f00d4104947c1503c1c10200e82c44802e0740c2c6d150034400c220518071940047d1024030720300d80001e500d9000d509100c0c000c0f520700040710403c4502c2201268a02590044584010003031420a00300424254910102051610060040070740c050070350a48140c04079022241c281c40380304240041c00501d40c40b1680c00c44030601c44103005955840492910309045071400c0c0036640b420600424600407621002c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287390215 1250 287388965 287388977
    0x1050f0921160f0507060e0a030b061302041d0108061006030c090e090d0914090613090c06050307080901050c0405010c0201020c0d0303051b030108030a0806030a0203120d0e070f050405041502030a05010303030507 93
    0x591a4480e600c204080340c0e00040d4207001503070bc800200710565510084000564030006000c51840350302c8100360084c074601c200c050704680c0c9560403139540b110107844505400d0b4400341c04000303e0b032180d000320035000e07280d14000aa00d5910200034070b04440c00c0c0c85c242c01c0c9400401c25080041e6214103040000c1c5541107900007540e0300b0340003007402620041e00c0d00b0b0103107081540d220b90181041e00511400e0b90b2049040c401581e81ea40c005086030002c1d5103c0001800800128015840500956014644840031240b600b4502401981c0c80c0244410890540c001d0b803820081981e5044038503c0c049000e40c8000c00e4902d030074441c00d01403032170710a01c04800c500c0a1006104600f400070680ba01202c284c20040d03116121070300002e00e001c40c510030007549440782002d903d0f41c440c4190058100581c8000e01440502c0703242d050340d521280f45025014424490000c1000285440e81000307030464040e90307064640030401903100f0141e90084a90000c85520360004000300740c0d0500c10940c0c045407601d081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287391465 1250 287390215 287390237
    0x10b03010b041a210609240615030601090801060e160804080d09080405030f0d0305070e010e15090306131101090e040f0c120609020301050f0921160f050706 69
    0x2450840c428a0f030390380120f0703210b100b0b941110608446a0515514902241d000785070006001e40d891001041c202e0054240c0c40518600711401c1445500601008241d1a00c044018449403071a0304000d0005041050700080050441c4007032140402070301c000c1d031400c1c4641c5840c04c008411009981a9041003100320403c02c004901c03c0000d5802c415070170300010852202030f041000f07460007250001a8580101d60201650910005101000005c1510203001a070389445082d5179450100078601d0219000c410181e11038500a548000e51807001b1801c0d0341000300c0400031030b10f0190f0890300c888010008100305001e20071400950442d8210900c1c04544a13810010000d28081d40a0700081101209450b0340d01006544039544028000c0d004d05019411450b0400b0b0000d0203a00f07074180d00030f501c3d2801003240301c0303a41002c0910807030303036a0000c204d1000d03543c00ca0030380290302e000c07551240300d011f1000e511801406819100c0c083d000340d5660001081600740942880d40650051090004152030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287392715 1250 287391465 287391491
    0x50c1009050f031513050703060608010203040309050a080c0121090803190606050a0e0d05030a030f0501140d0209070311030f01180504020a0512010f11120106020a0c050405130b0108010b03010b04 86
    0x103070301c000d44241e0500044e00e1843c06d64079100d41d9800052400e0f080450100e120881540035510032400380c1d031b40561190703440082c0444000d25010b92800d542201c0c20788007041d401102903082030007038000c044107513030000c1d049103044a60000301210801c1c0c000080c0410000f0460070303c40f29078151311040050341c4c58800302038000d2240e821100140b10380c049090050303aa49a408003142901b01c0103490343c032405140000d004003800c0001000d042e241c1800840c86001c220b16680f00e030304014041e40c0d51280181c003000010f0000800c40020180c840b600c202d0605501d001450043c5283c5001d80d54a50500300045406280d42c020080c8080c0791008100151303480113003080807503100307175896029800107201c0c80b0b00bd4007400302c01000490900c15201c10100601000f40b4829481c810751501c0d590300d5140032a100c0d49141d9002d011460003c0c024011840c041e40703c50f4229000405208054a01d0b42d110580b404003640041c1c13681c0d54558810f00704d41400e01401c402c05204440401004040d459 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287393965 1250 287392715 287392753
    0x7020307051b1807020a0c0e010807081c050309070f06120605010e10050c03040504091128051e040c0215060a0303080114040902280605071a04050c1009050f03 70
    0x1400ca10b034002c0f01c0d8003240c400d03030080c040904515040b51444090070f40f2101650003110084c030418241e0b03c2030610029441201244250708101c01651194410400c03103003c075601e80024103030304002d005c1d0f548002920000c010300c1e14010403103030300c407414540034280203c2c003100d50a62015041c41400c0070504c0b010303a2107405000c1d0110090805580710615907085514502494110b5900f103460000400140000303203203051201d500131203942c0119107143e68480b42c070f040e04410756450188402c0d82800a4940544428011041524411007180d103180004060381d9940403944056000f9540c02d8041300030608500c1c1d07009106a400300c440ca880d694000701005014410f003081844c0003c0c6003007060352190040c111a607001480544080744480c00318220082011022071038540b02c401c000780880c054401c3e00c0c2080d0f04492000b2907000821044580b000c03005104403030380e0051203c04003ca640d500340d11030487d2060b43d80c8900740e0303080105111449850824080c840ea218a101010030301c1502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287395215 1250 287393965 287393989
    0x2160e07080f04060e15010302100f12090303380109150804050c0a030813060305101e0302060d090b0a02192303070503060112090203060a0209010c020907020307051b 73
    0x102d06480569640e04010740240002e980e040118040c1000311007204a0144000e8143da00840f41a42d006000c01c20640b8001d24000c20900461101e141402040f0107076030141901034064280030400b140c501c00154028070400e40060000c1d0072040e41e41081590751800008200307030a0802244a9041880300384020a08044a0f410407032580c0029081240c01c1c48030f418082c2020300f0230305e01d0f29203a161111a83d00102070100e9255100f0a000800503c80c0c01040d0140e94540c4140b14140c0c2032089500200031084240382e1001011407001005072902001010030302828200000d04981c989010800000041e01040c4d2441c0103100c0003210303c0e54002c0101990542e410b00e103507154009542c180c2c80c100181d014031b02d607620200030061000d401c0801180304035000d0b82c0b00e98202c801c003200740c011106081c4000c1d4141e030004000a0701c001c6668003e0218400504100300c2c1e10780300d5030000300441c0d01220340c0001a040403038440200038080080c0c918804109800080451b100004104501022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287396465 1250 287395215 287395231
    0xc02070e1311040e0c19060c171309021c0603020a141c21170c0c070810060f0e010803030402040507110105070e1f020c061e070302160e0708 62
    0x20440d060100b05844964072040d05015000348210842070090359200c142c000c0c64a4010500c048450b00c403807640c440c1c1c0303800791030841c1ca030031420209a85458822002081140ca4065400c0040c3c450344001001040000c165049015942c2e4828402c08405102d20f04003510300b0b242401c41c140016601c032481442621241c0313000c00841081c010003d40c081c61004108450000522070180500000c03c0d03010154080c0304400304400c602c42181150594020f5400c402c2c14868070003c10000c0140d02c006041001d141c0080f00c0309641c682178004e040500c5414080c0180740c0c2c9080410100340121405802445c012340d80132182e40c94082415144d100c001c00082c03003140c0d00c100040742d2a0281400c6d0003040d41d5440200190b1405000107000c100840001c981704039030942e101100120030541d00180014158041e001009040c03040c00701d140c005101e400c0080d03500008250382290000042d04000d8001d81c0101014107004c1405032849580d81c0200b1300d10000366080203840d542240c8499044481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287397715 1250 287396465 287396491
    0x16051c020f0412030c3c0203010b06270f1c020d0c030f031202160311030c010507020304060e0102030a08010b0307030905030a0f02370302010f0612060c02070e 70
    0x41e40508030491003950403910783d54204400141c00e040e8030004400000c0c2c800c0386200341c450800680a0104020f114441c01d0203068103190182800140c0c3d14038018920140003c1824400c107400a0700d80d070400daa000d034203032014807030901b09c4405101d2502142c0740241c441c9030603046000301142d11042035580d180d040403070000000e011900c4540da41008076801c070000081b129181d25180080b40c0301c00d5010f400103500700d05080200d03250b520846040d81c909a00c0148260425501902c03141e88c1c11b000613180d0302045c0214855420203000d854458507039a40511b80d1390303007400b8002d031130300000d0303203013030b41150b200380200000150040e9103035064500e082590744d242ea4a0007806c4000c0d1034400001415070002042c8005190b030000d8244003440136030b0f02a25500201503420380c900048401142181e8000100c40038059030000d40310240b014064400422400000f603400e6007660400c0c1d018614000c40103411009008191040f2440d500030b520103095954135020351507902500241c040c1d00c3c0820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287398965 1250 287397715 287397727
    0x30c0b040302100c030e0d0e0f040b01050f0706060f06081b0c03160b190e100c120203010e041e030905010513080f03041d090307030309020f03011416051c02 69
    0x4000c03c02032481c010000c01c1032205110101006000d02000c0100b00e035a84aa0702d00b500007107001d020341c42546180913156564135648541000041c00c01d008036941031040030080300d0512044100108040c0b802684007103421458005415070005255000204021001c0d040c0038040800d040306090403004028441d032102c1814802a08501c15043c0c8044505e41c0811104104107488440f54840c00c4240c0c08960160800c0803e40203480b40080300c10f540342c00084142d010703040e080e0310a0142d0415881c1c2900703850304922880040360300a8006800f000600002c1000300b1490214200204c401916075014000040c0d401520700c901e1406503a040c0072000c80d40c2111503003051000002808100100e0703c030400003680003600c80d4001d004440c01c18181b01c4020b0043d1011032036403070050b4090401180390102c0b80d24210001c1483d0b140481e4400191003035031403241c1d002d000b0076000403120f810013111810580d0070340d04a09148480002404800c0c0021003803845400198540017030050710150741c500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287400215 1250 287398965 287398967
    0x1080a060b07060603110d030e09070c14060603010b061911210d06120c0b0d020423030f011514120d02060405010b04020418150e07050c19030c0b0403 66
    0x48141e81001c150280301007001c2042c84520340282c81140c2c05a0344620010708507009000c0710309040c04014010400c03900112840d82806811254800414a0641c02141c0d140c3d6032101c54000c101c140403081c1d4001c000340015440c0a11134110359000449086107403000c41d521440030100080d4058051200600101c00a89414000d9156007042e051018241c5441060000301c650050150300e80c25503c0c0803c04140d6141e41a84105425000406a0030b201d207020140c00ea15845440520305240d028000000c10301e4106501040c200408464060b02481031000c4c14940300c03a036000d9a42683c10150005084640d00c2104810354128007040301609800c140810b2001642c41c100c0714040c411803841c146101c0c2d004c81c9803801248107800900c000307604001000260b00440c0101d0414080e8a0101c5c03410304a151300c016941c9441070640710003640e1383d5000300f00c0c24804480b9503000c1900040e0804644005211a005202c1412500c03804c00e01e03035842c02007030706082c100d0040c44940250041000c1c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287401465 1250 287400215 287400221
    0xe090709030501050a1d03070b0c0c07030606090c0f140406030b0607080706090b010e070e09130b012603130504050c0c0f030702010305090609060c090d0b01030605010e01121101080a 80
    0x81c64000000b0301c12400e141007803000804080018651b0300e19240704101100d1300101c04c0300c408a4101c408000a0740351800003102c10391204514100c00d204e200c074000002101401103100501100f00c0001b48406240805071020400940c540c04024603140c207404004101c6003614140ca0440c0340019038aa140c001281d5907201e0f8090181c1a4031001c02c220041012070b4010070b00341842010203500e0341c2d13a14160600c10480507604540801c008026591140c1030180383d40b0f03846003541107030000300160354643d00980842030f0000c51a40034401084d4010000391920340c400310f4800d1005500d8016046500d0341501304074025076105649403001710340c042c40d065080d43c00742200d50f401d0f90001c003c6401c0b05990b0368071501d800c9011a04050000304130001c00300c0c6141c860340c1e40c0c01c007425030b656911000e10f4665014a540c00e600031034072002000821420a0018061481035038001908d50400c1045488490140c1c40040c84504501d822000207039a04484442c0480a00741580180c0b20308203040d0103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287402715 1250 287401465 287401469
    0x10050c0708030406020c070b030c0a1b060c080709050a050a09150b031819021c2f120a05030d0f09020d0b060405070201060b04060c231e0a02010e090709 67
    0x80007501106010601034558024008106031008481c0b01641e04c901e00b030018042121000494482441800703021802512001d04182d0b94440e0101d25240d90360f035910883c2c1c006500000090165003c21075002e0f00031020302c0c088c0400b1100e8582181c5020b0000780810300754001d4043c0f240e16245e14103c106540030000d00074100300c14005460307180c44040c2070090408641d440e48a4854054180c04140c0681010190039401520072180c10f40913100c40b06548901c2c0608592400b0b54a4000e500701403226500000622014481c24502c142d5808200c41c0c09020504c09007181c0060b041d81e0000313000001114405180d0780c0c4041084a049084a13004011105010350000950800e01c0e007044000e40440b03225180c1110108055161214200d08a51050080b680c03043c4d8208010b006e1240260f81a50a480c4640d202540407136101d0303008111407210301034512141d03100c00751f028850700d90300001d80342489080c0000d18501c001e540000b0288483e0039001d0b4090346400f4007254031984a030f01c032900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287403965 1250 287402715 287402723
    0x151407080a12110702090105120a020a15110d080105011805040f06030204140601090b09040f090b04150b01051e0d0606081009050408030c221e140310050c07 69
    0xc1c88615000c000b07400e0080310302400480c9868002403088503801d0506940403940c000d0300e00441c503800c0a00f44440c1c40c20003084501075101340300c8007100582e0745981041c05450035030401140d45ca01c1120140020792034841040c0d85402c14040300d41c0c2140c0c88003c8a044810034640103200e20904076031b00d0071040c050b07000190010b00b0302d000c903c0c00079043d03005042260310075034003040350b8004c500880c400103a007034036500e000030baa0700d00070840c030100f4001030001340c44003d01c00280440c01b07403101011118070180488078003004104010038888414038840e41d080700e41000380100c0c0c0d40080000c129125000348501300380c07003006d017403a1810201016103554603800041001910740f00c030742c090f00c4400d0231138a1454201c01c2e0030000c00c03401454010180166441580141036843d150340d50b07010b54000001d4208150840ca4000b951184001046c0c801885041c83d25041d0314813a03e45d0b50500d00554003d00c2d2020300c414074020040e200028600329010042d030b80004c81c1c0d182c0040c9100ca82c0b103614000341c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287405215 1250 287403965 287403967
    0xf0105122a0a09060f050a080708151c02120a050a08030a021c1a061c0e011e09060b1005090d030201111c24030f0c0b030c030f06010915140708 63
    0x8007a1a030030020043c00e840b000c0d201d0300760416507244102c40034456180300710300050700e44020428840c010b144054200d030b20408101c00b03400100300415010000c90050700644002c5404800a504040800310924441d86028000c030b4102500c070f4540c2c4103101d4a0090883d10004001424500b032541030300c0c00070345464100e105950448001c00007814480354016409880015038041c54a065000c0740c1c00d19003000c1e8940020009258240c0003003111010b210320554a0340d030400420b01c40e40703048a40c88049040005a0051107042000c11207030004041401403030314080000000e034000e01520070b010b20480b0781d10002885841c080340544100940c1d520030140106444510000c5100d050000d005000c008010260001881d86000b81185c400308580d60060441400810f40e032064209a5500524001c040c0139920000b0107621342c0100c2d81d0074450740c40441840100c80c1168801c41e00b0502c01d01e002186541000241e0b01d200c81390805101c10300007064a481c1e4595030395016070300143d420400b82 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287406465 1250 287405215 287405227
    0x71e02060f0a02030108190507080d18080d0806061305030f0c040e070f0b13050a0b040512010b090a24080d0f0201061206090201022a0f0105122a 64
    0x80d54500003a11890454116400001c80003811071007503a048450300c00c001d0140740d9181c0740c01d0003c410801e00540c0c0f2030088a41c040303680c44041100b10240400c0344c1e642c440c0d40f28640b00304071040001e50800a107070f40055001c9040c1c2d55000148030340041c01190b1069540315400001d0100100d1540250380500924041c640340c02804103034650820300a482c24440d030741d0074420b103c1e291042e50040302501c8015140c00d2002602d02e03000b615000c0314040b0241145038484e80000d0352910380b40e001300f00041c0005001d000a0401c543d20b0525000100000d0001c0441500010b484480c020442604c135a03440c070344a502c80423140b0803080b188041e84008280e0796102c12002e505d03000c1c8596054046609101e4404e07030b81d0710500c1802c088034984480101c894001e552103001070311290b10140e045200d40c40e10001c035110a02e0030f0212040342421141d103c400e6040c203019030141c1c04000320781404010700c010075241c41485019507000c100e0b1250354800301011500d40c00c549402c00340100c484080070402d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287407715 1250 287406465 287406467
    0xf060d140c0a2006011203020a050316020f0613090209030a021507030207061b031412100303020c01020307080318031603030507080c041212111204260d08071e 70
    0x20300028403540d484050494000c081442d03020403d4040842e103038040b00040020700d404000c42015a8800c2c41580c07038000e000d4403a85c0c6140c1240c1c0b0000d140007401c064100c1146440342ca0407403001c80c1904d0050420040350310480200324036204070b00d82d0b03a400003904c480d6581d0a010b440725155008040b406050000400d08a050700455000c0300984580b040201e405030061041d103011541e40c0c0342060540703a5554003219801c141c407407615090308040c444421941c043c41001d502c14200c2902c940c0c80c151450800918019143c084e590554008000c0c07036012075800303011650b01c00d400c6a0110304804088151034550300c01c1840b4040c48a00c0f03440f0003410541d00d600030f01d0140c50f05680e48006500d800442140e98481c6105004808140202010000e0300c07125003c0b846c41c03100d08000d00da0004514031703541000043c42e02750800800c0080e05000d04681d600c4801d08400c50503040120400e842c2070b50503034995501d0070460610546a0008000520507040301540054162032039000d2414444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287408965 1250 287407715 287407717
    0x71205070216090203060406050402040528030b01171e03070212030c01050f0103120e100c110a0801060f0f0f0e09071809051b06180a0302030a120206070c020f060d140c 74
    0x41b058031580c1401d00024a62516009a5040d41d00081c408666100c20151919500825a080d1000c08140b5500040440c0b103045250f4000c243da01140340c144a00100c0b0a41061140c11004070511032030310360103418030000000d03110b41a9065481d11810550780960070310350f006000050307004e9030904003048a40d0302c00d030385440d040f0391080b403145c11941c900c0d5500307030b03522040750300d9040c8c00150f4180c82c45180c1303110b0800001e2442c0241e440e9032018885901103000f408054000184503074480c6400c000d22140381ca0304800419400d00c5026401c0e00300384d080c46494084d445810f80126070900410000c0009004540081c07001100344a0040503414503031011300211082640c0034050511400000e40c000c1d070010b511060300424152a11070f030850700c8640001c640420300e822a0314100c006c40107840800208410358010621810314400a1400901e0914010050001c1240c10310603070f070068a50307000c96026004202d40a1b51681c10304a5001c1c002e08155504c00c141030138000520140b108020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287410071 1106 287408965 287408971
    0x15080a03020312060607173a02030712021908011224061208091c1703220c0f140f040513050319080f071205070216090203 54
    0xc7c0358241615410154014103140000d400758510500602c0020000e032205601d0580380345c0010f00b08005a185000d00c41c2154001c0082585140554060030b00340d901040d046446d00c0c0800040c40620340800542000f041110380045082200003001d058400d400911a14079001450380c0e44140404090103409a960740b0a40840d90400012090f400a4014032241c0e440748405800c10074510040c5100c0e140a10411041b600003901d55001040d0b02c00c2401105a220380d40c0c80c42980c880f8a07696048048041a2220101040842015030701541c0d00e104602031029214016094201c091a01d640c2e80040080b01414051074550400c6034042c0060740303503404243c241d0f55103500c1c64121489500361001d010180481c1268058421a401039030041d1084260500ca58040e00e0b10460305101071344d65403240d002440d0035000f00512112104c0c601075504425035206540301c005d400c16 = true := by decide +kernel

theorem cover : BRFrame.Cov 287230215 287410071 := by
  have h0 := BRFrame.cov_init 287230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287230215 ≤ n) (h2 : n < 287410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
