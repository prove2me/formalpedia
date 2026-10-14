-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:01:17.878974+00:00
-- url     : https://prove2.me/submissions/a9db1e97-282b-46f6-9328-4563141d752a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457194244 ≤ n < 457374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457195494 1250 457194244 457194263
    0xe060901170a020d0602041508010e06060c0a0b010303020f0d0813080a03020723010b0301051504180b0709060f3905010e060a0b1905150c0618010b0303090303030a09 73
    0x80044e12030401c440340061040c180981c81700c0c148148050354005154284081017484801000003981c250705040d0064bc048d580c103070740c49088800181c1007148101380038000e400043d000004165000807400820322580082da114140001c40480e917109041e681d40f601c05c021024440003050b540801002000d0141c2001850b080e100d40e81d02c501d90550701c0b0300000b250407a050070349124000380101059180700310003c2100740fa190842619400c0540c804a00031a5610354141c140c450b14010021001d4021901c0b44062403e0800180040c6107401200f000804031529024014040c000b0706600b00744104003551001141d00740b64900c400320307040381688500c01c1a00701012410a00c2500309a0f01c00601801141c6000340303120302610b510060306401009c000c01a21080701c0000d00402c15500200c030106201d00c035026403074069004000011060307010340c905116440c038480c24182c0b400b00901000b4800c060b01c03002051788a0203070204e001e815406c1040020030a88031a449440014424170543e17 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457196744 1250 457195494 457195513
    0x70c150b09150901151d01090506160210090305100c0509131a010509060a11150108060f0702010c230c010501030804060909060605040303030b03010e010c180e06090117 74
    0x1801c00c80240c0d40119104669240440d89040841c403c50140020711078601308000b00f400010096084e50852202d0120300a0000340c89a100302180001040010002030302d40c0400c10345034000c050b0000b000c13480b40c1c01800140034002e006880070000c5035000b0307025000501c91950044050243d100384e440170040c0030482c81416944060042e0b0300d6000791003000691a6031102d440c202c44080d1207030b103414441e085c4000510307580c2d5402210702e5183c0720f16001030b8803065180783c0740ca8103e03a2510306200e009854004900603000181043c403940024120405039220381505a00f22440011600c0000720a2014004c0d0412239100c1450203a8112166a260400c2c0d500c02c6400c6820a030801c41d010304000504004d529401804600a05012981000010718002000e407a500c1580320044c245615074801640d0f9680c298000d06074880510024007101c452028020b261006507451800310300040c44000c01c420904106151040f5009012000903909010002207411000d24401106214000341d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457197994 1250 457196744 457196749
    0xe150f060d06051309140105010b09010c050106050d0602073018080102030405030a020706030204050d0f141b011d090718030507180e031c1d03040815010e070c150b 72
    0x1110132200710b4002031242010b00d800190541c140c889102103a04000062180c09003650031030b0000902401c240040c12450f1800b2409000154012540702080e40702c2001446100d4000300360030f03442540804585c2d165403600ea060101d02c0c00100e05ca503c8080d0180f40014003034030508100e85a002e01600074203a65888843c26030740204e90031a415003000c9185036041d90100b0180c40030b001c0e03c0c1010b5007400e041c02d01144400009550203040303100004066401e0104002c0b00c000301c1103000041d10000a01017500c0004c0102d4414401e00160750540306448410f12450844690000141405840d4070703816803c50b0030404403030f20f180c50040709400000c0040c10420044009010740c01e5403603a018156000001140c1100700c842c13025400030000f560a007400a40c1d0040011082800001c100440d0094100011941d008002c954440020003288030701340000c0c400700210300e1814545482e82c80d441d0040c41e600e800c2d58404003048100f5603110004a0140983c801011055400244d22111000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457199244 1250 457197994 457198009
    0x60e030f0c0307050c060705060f130515071214150102011d0a022d190b0f03150d0c060f020a120f0807030605060711030102040815010e150f060d0605 66
    0x41c0240564000104078041010034465a40d800c8000c0311401e0a00c00e05880d403584031b00009000d885151414000660826801308642c0070841c1c2110440e240c1805d080202410303c43c0696518001c1030320241420980f51b00c9001d8200c20601031500c8188507140c1c0b20022102160500c1030a066548035820150b0100300207140c544001280d000401c000390310b90040c801140c01039100c11078550266200305500d4040032594280740d1505444140070389510818035220781c0c080750840b120804c00021b02c0302050402e04065400303102c6000c0400d4808001034100200a01071210003407104a02483c1000340e640034161680154178180140c81040d1381039603407501d80d41042560b80d800b1a9a1044101c0c2050740424013030790255060404200316414400000c0450044c1d40008211900082d52203c16407429016100108070040441e002480950002c64641500b40280c200700c1c1071450000300d007401d404c0c140b42c8070a08090011595240d210060040991104a0030300b50309848440000e440d450307029 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457200494 1250 457199244 457199257
    0x30b0f090408030a0501080316120e0a0b090102010605030109021810030c090c0f02060f011403031207020a052b0806060909011806120c06230a090f09051003060e030f 73
    0x2111550b0340744c00c2404204840301078000401a610600940b402d121280824101c0c69800c02100301c4190b01e0301400722881c2c0800c80207660071442c405000214203610001801c0040c000340c000b030000701d480308181403c8805003540a03500c10907080c4000140c03843c04c6411900406044090141942c481d124815414002d6003c02d580c5c1d9660300c0082c658030b501207046c0e2078030062480a41101d080c070a803044000d900c18010410a01c003011902e8140742d0b1704008850111000c1c0745441803915000700d01944841c1e60003402e80d03882c01401e03042c1500c0054002c0d1009440f02c0d000b184603080311440422101001c3c010002600000208420032440e0303502000d00d40200120703034964800ca00320540d010b050320260340c031290034081c62195104c0010000b401e148150351151070000211440d948103002242420325075140840c03030001d85500d0a580c804100302c01d45018864440a00340d071000a50111401140e500d03081c28448203040c0001138444d0841e401c88918407003200c1c20003002071440c45480e440744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457201744 1250 457200494 457200503
    0x60906030a051009110d140405100c050c37030909090204020f0c250807150e0a030c0306060b0f0d0c02030f040e0f0a270512030103030807080108010209030a0201030b0f0904 76
    0x4031b280003c0c40a0b6000d07034145104040140901c5041c0360340e0f580e60303900301441b02c1c0c0002c035190b20030303600040d20035401c3d521030810b0f44080382d480342c0801c044ea145154510a00d58900780c414403484140784210150044e8451b8503980e80c2e111207140800030b400803c003840089034044e808128a501100c2031a01410161941d400070300300c4039906000703114544000b450301d000c0c042451803041240d200003083c440101e410030703081c0407100c07079a40344102ca0b20b40c001250b0f1584208044130100074460040f4000e01520b224000400c100d5482e5080c510907801492600640688100240049144503401c49400c490701d0b030040306e007009815000750609421076085100342c1408541042240d020700c40549030490400b000c20801d4501c0c400340c000305594486a40c00412035002880c40402074204011481d180e01c10180035120750310780c60010b1000d00142d56000000b40b1500c008180038406100310f035148040140103010b2050b02e50b005401400c24130650710342c81038031683c0001207501c0d200c000030700c03c7d4800d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457202994 1250 457201744 457201747
    0xe0a09050a0b010806030c06070323040308030a1116080a02070e0106051e1303022701120605060411030a0903090905091e030405010e040f090210020c0f060906030a05100911 76
    0x100c2c0001404120300500051003580021901e070380315120041150000350f0035203041200c9011640d40c0c545854000c03801c0c0004800005000410701500300099405070f070083c00203005007110191250550f010703106800000000d001c14403400528290000c04280d104c9005503070b051a52802a0352200ba0300342d01540114a0004407640701007510740b1080c0d9240000414142015829000405040e03098003000340503800d10168a4080070902d140c0e81860300511303907019465a1511512003500c5170030f40048a40604007804201c59150500a502c002075212944138150780d1810201000303488801b500350b05029040c1000b0403100d0140c0550f80c03281e400000103041d8440014945408418004404001c5030414081070255a03400008420740003070889001c518812456503940c0200894372009520800c46200020055000b00d041d6405c000c0403141e07001c0f080030007024040584517449038140d229a0400002d4030000c09a442207401c800c2d0070107400d41c0700d078403041c3c101d0403240c0c000c5540650410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457204244 1250 457202994 457203011
    0xd0f060c09060504140d1a070513120b06040f0e07030c080724050d1107061e0c021c110d02010515060c0a022b0807020a0605070b01060e0a09050a 64
    0x41011070000200399038a0a5440d15182251100407010440c20640c03150109240e414103205e20302481c540f0203004024a40d01078249094090041d601247d50b00c3c0140800c48000121031a9090301c49240701c0c1c000900c1e0300150b80d00c1c0304000c001c00c466500501001d540d4102c951401c1e000b040080d01551180403141c2942e410071030000d260005075400350000c1006054102c50210201c202c004c5c1540d09800c3c11521044c0d40c031405c1c80500050100840303131500c04554103043c0031142c2c00c035200c000f4450780000084d45507081c4400c15244038001ea00c000d039020003200100d0141c00d05620301c140103c2d10b00345807041d5600708030908020710802c00c0001030313440b0380070b10ac3c014160302d0710b034808520102da05502e011410301005483e0803644070007900c2500f080c413140000c64407211541840044001e0082c00701100c070302c1c007804960050042607020308001c2c2d10215159000784100d1b501c45401c00401c480a85c601101240d50043c00c94065401104214001035650414041d05020b0a030301e50000c540880c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457205494 1250 457204244 457204247
    0x30d09172106040e120904021b010213090e0c0d06020f0301061701080a0209180f06070c031701030f022e1706010f1d010e030a0308041e080a030203060d0f060c 70
    0x903070140429126078030301103901c2c145480c0020004c442d1620039200c240c880d00b000000400902032a036139036080c0d0004500e6100d0130b090660007481001c11002682c41c40d203032646280d44c12980381c0789818200d03600600582c0f201389042c080d080c5c82940310b46405480e110000c55039200350740083c0c0c0004046180007a9100c0d011100d01c1009001d019044010303d00554650001454240c02a00145c690f5040002c0b41565050500007101a5035980080b5203c50401000003042c00366100000d80004a101c01c00c82a0700d2040c0031014109c035004001001294602c1c1c080207420360028003610408046d07a4031094a80981504400400d1800c0d228103000c0c04901c01400500c0c00000e1540e07041100c0c40392810310454205050940c01c4868441006044041d980142c62030079080c00c910b6031611501380d0210805511540e41881140300344403d0801a01e5041c200140c0c44440700300404585082c031005455171301c01c0d03010b1980004010041681078015449815801076114020707100d0540704c014030404203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457206744 1250 457205494 457205557
    0xc0203030f01150906050319060608180712030f0203270f0418060f0908040b0417070b090f010c08120411030f0c040504030c14060109060f030203030d0917 68
    0x60183c0c603060318041c098500010000d91480c003c200c207202010010440082540000b14840c041e80e000c06c000fa01e4035030303502403c4880110f414809101401001080c0c42c10085403140403201c3c1501d2400400c00715580a441c02807004000780b0441c8030070300501e070305002d01002d0908002031a1003003811720030054080c17101d880c54185000b070150b8123140903005100140c028515240741c11000c0020710041000030000641640070002d002001d02203008074600810b900107104079180701f071500740a40c2c0d020a1541e104d0340300740f046271001d44080c05845194188544451415001458000310100c042d035143d02442d000862199040f80701c103010031081100301b001c0761032440c000f02c00038880c1684010455555226080700c183c011515000407800300f40c010482a002294000b89036800708100c50300e4242d803241c0901c69403061134107103040000d81e840d42650a200381d039005000b852a008001c030f01e02020b0402c05070200c511462001d001c0d02603500e0440503100001d0b59100e5a450b090103840f10b900700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457207994 1250 457206744 457206749
    0xb0304032d020c060f03040303052511060603010b03070608041a04150c020304270b04021c050f0c040b0c070f0609030506011d2707060c0209092e020d0c0203030f01 72
    0x260400300841c000d0b000c41c200586c1ea1042e4145008182541d4640b10710003000d104514200808403510302e00c0c203195030460012060000c0311310071200907035558001c1500742c402940c100f1340c143c3c00500090005a1065820315440350066a030280321102e0310a03604038554080380c1c02c0d60002da08039034030310310055140115080760105100440c281400c0c0301c1d080c1c0032030460200c0b44411031001036801d41c4d41c0700e2580003520746001c0100115200c0032030030307003411808980090058242d460580003c2010700d40d0000c0901800c007c21816040c1030401050b586603900c0707a00682114403c103503000030842c0c0d03540104e40c098040c2c0d039120381d50949545001407500300180c000c0941d059022510040004030855002c0e488008810090905540095030049100c5444213101c11401003020201d01c3d180c01202d0b010f949442038542103025940e40b800e00b0707200d042884070307103d091b80f181c030079480c40b100d0041115a26000c0900018640900c1408110855110107405009a0804010860083c1003900701c10300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457209244 1250 457207994 457207999
    0x712090518071e09090204060504030b0106020a0807140f070b04211104240824060a0302221a0102010509030f0703080703090b0415050c0c070b0304032d020c 69
    0x1080d0400c0070000e0310760480c560440340e0702c00d120000c2002281c440c2140c10010841c5840466a4a0700c8e107500401c0c0ba4041d0009035060400c0d0000020568400141640d02c036400c54412030415020b030303440900f54004221000076030300c102c0080826060007440f040e4020114180460742c0d481c80c1000c00c0401081120754071a8502c0807048890219007580d114030a00c40044400140056181c40315808006075142150811032030004040ba1146000550400602c501784820b01c11081121001e0b94000089030099040001d1620070001070901000380000c150304e03000032694030401079032000d044449440898010034909440da40642d6028400d02d6041130103640914508092040c200601e0300c9a04001030800c00768000195510340310f5485041d45640c1304840f84002c1c101418100001007003144072800c2d0a20b8180482c4540c6460021219044855405030650514180100f001900020700030b409000e00c00402c0600c11000428801e119240355880e500303201c1d081c10340286004800031102e0b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457210494 1250 457209244 457209289
    0x10c080f16090b0d02040b0309010b04050604020711100908010f1d0601050a14130f0905161203051602090421090b0306090a060f0b180901061b0807120905 68
    0x81079a80601103070b0a55440c25125582c0c0c02c1241a0080244078690080041c50008801d0140307d41064200b030004140c202da0034886916858108001c074800c00c44001c0810240c895002000d007041080c0442515170350070031010803a89c0703040b15800e49003105801c06540380c4c1c510314a8064000c0c3c0c03118030070300302080d4001c00300c5606200c0882c00a82150088203480c1c1c218440000041d5148030082610034038985081c001c0c41210074001d03000e0400701c0310440341d0b400b81c03401c9550340c1c1c2c00d08284107080b00e50783e1400003807840c1c50f5101a1240d44c4000c200e40814111003a0980150721015502800740d8130402d040e8001842005118a41c1030602c80b81204000a0110400111507110140c03604804100d413103101a03241c0c035202d030300201a0b070742c00000d088070500c1c000100d02d19480043c0442e0041d0900d0308040f100040e00704114140c1c24050400032546429000300c00450742c002c00001103104800702482c0480c191509503005004a03507050008145c2c80080c043d50905c0d10551111031403004244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457211744 1250 457210494 457210531
    0x5150910081213050a030c03030e030f030406030f090812010e0f06011e200106050102120705060126010501090209270f090307061a040c110c01140903010c080f 70
    0x11070300d821640c0190307030003450049416030f20203880e9480b0030000d00c4001d11410800f60b51740741494000b11180b00640c0402d18007001000c145c1004511280c401c1c2c05c20010358030701401d012080d030040c0b080e041e8654049035100743c03000000356400c1c000c00e481c01181c100e00c00298034001880314003180c02441c015110000d030b4180219070740c008020624921240b0146c2e11903805c0701c2c0f0101d40b0038002c00120f0001810400b01c09210300c2042d1b001109481d801e90950f44042d4200e40703051034600c600b0000a100d50300030001008413501d4039103069000140100b8101c8164203020034103003034070803e0b0001c600d607a41c00640d003030045c0303042c076201811101c0c400141200c1240f00c8600d55442d040050241c0102d01d5844001001c2000070b20071240c02e0755014200b008000004101d810b060b00341041d21038052498001d2540b1a0340c06403e250306d038090340400401110154030011070300c01c1ca56126038030380e21800b808051681d03135080c000d5501c60340c80b99481c150146842428110001d001401c80e400401c0e1840d1030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457212994 1250 457211744 457211759
    0x605040b030a021602030105150f3003090d0302030309010b091e07110a1b120533010e100f05130902120d020a0b0f161107080105150910 60
    0x1560340c499440b010060f00d4241601100d010400d00c1a0000c0d8107500c0c3c4000c000500c0000041a100307100151545150110203074144480030300c6100401184090498900c041400700e008440c2c1c50340c0400d019241480109000301e03d10000c3c6050440c0940c001104211711540c00740725100ca043c00440e440086400c0c0386081c1207540d00440501c0d444814070780c00190301103016203500150624404100c5c2c0380f031101400c000740442a0500030300c10800d2000c03030000c0c104c265901f480c003109422002402e0181a1004180600c0024069400e04621085140e0000c0b444d1aa03509000f4001c20303500001e036203042c0b50f8603e038551958008825403403030301e04103201a44400c4202c81950340150800104250140009a0004411240000d152143c011a01c0c4020f0703000c5802d2a01f20300c519040000750700d8030000070400c504121a1103010100c0c045120855512a88030041081d000b41e0030f8402807900c8105440c00e50b6000c03501040110507040a40d40c444c10710240c415407002e807007a00e81c41c00c80d040000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457214244 1250 457212994 457212997
    0x61c03091406131202010c1704030302061308030f1f140f01031b0e0103090506040606030516120210030905060f060a050901080303011205030d060305010f051e0103150e06041b0605040b 81
    0x1d46030030482c4a04d18004590003803080c80780311500002c0609091160040303a01c07040c1e2040c00100d006024060205401d00441040c103181030b54800402c50071a500d030402007001d070350002c04000c07409600b1195007950300d10000d01c5502078004040380c06c030410340440602021440f05070181f81018500a00b03484010401608480c69641c6490030f00400810a00120b02502d1100406400c60180c4018401000740c5a0b00c200b08403442101a01d1400c0d20780204141035841e036200e5000b03a200000d04400c0145001c00490200d076440c0d0400141c0ca10700e98460603c0e14a00b2550b26500705007003000d003c0036107002d1001c800241030480300307401658100040a61640410311030310f0100003000b02e5404c1005801c0c000e903a00200c00341740070084641d4a051840c003924002203c2c10b4600d107003030042207048494100490a07080d0a20184644d6403a51f0f1714000c81c3e040640246c0e003026a06c0d4100600e102003800324501803402100c00c1c240c0c101340703820402c03c0045554068000e2140810007000075840500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457215494 1250 457214244 457214249
    0x203130b030603060f06030313080307060b09010b03040602030a2a0806190e040f021801031505370e060a14010e0c0f0904060308120108010b18061c0309140613 70
    0x88220305c0f5a220740020928600902c103a0b103042e80102400030074501e80c0007010b402c2050040a05210078500c0708144056580280101081c031030003040040d02040c0f568000359001400e810001800c5581d246c240007040741000704031107140c05120305031030b01607611a00054000e0f60803250f50040d8160103586036101c0d1440c0c031480b11050203030b00c0002c007848140800c12a000d41c000c1c1c003402e0b200b1106510403440e400c00f400200c035601c0340b040500155500074441e40e4032417911300c00c110340101c0c0d140b0200c02910103100580c400944240014000101c0503004124001954400a240e2402c0c14030140060b6001003000d820711030310400042021040d40444182c1011400f0505d80c0d42c1e4402d0b0440c0950340c4124500742c0d410508000f000800c01c4050001000301c80d51000c1001c1e02079032070f141441e00769070816800c01c1d0300251440d044421260840e460742d030000c0d0010184c0c0441410090202c2c2441840102500030071140c0f401084a0030301140170040c0c1a01c11180c1c585403e030203410103592082d550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457216744 1250 457215494 457215511
    0x1f090905070f1d03060f0907060212030121061503140c0928050c0901030b010201060305100b03070f0902070c06030b06040b07080c0609030c1005040812091203070203130b03060306 79
    0x40c6845600c60b0f401240b0000441e01505072880b40c0b0b015114442c3c0b420055a0400c10391140c074074005085480032075080f40e00e10700220344500c4c41c0d207019254200b08031502c2b0411107123405801100e0014200c0d00c01c0d800580d0101401c90301143c61424101c880f94800406949960801d03861060196110f02e0940e80c031207a000011226155039600410303400d1104400e99a101e403400341441064143c2e02d010b4a00c02809a07000e1106440d9040124203943c824400141b10303521218110901d013846801081c2c890b1303400b60864010310358841e200344080881e58440d1080350750000c2ca40d82840f0030500e160001d8a054182031000c4a40701c40801c1c1c86106038464461920800f04800041181c0c5d4800c49a40c14007103412a1114100803c050f902d07030780507440c1040365100710b010504c000f11b21401610320440d040f4112606200207020140c0f07480704000d0013201d00b4010074554017103603009a00a5409800c1980c0210b46a02c1140f043c0d510308507042c1c010305046132040c02080304540d00090001e9020468 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457217994 1250 457216744 457216757
    0xc02160b0a2015060a05040c080106030b0f030a06060501080c0703020604030c1a0907053c4027030311160501110307021b010903021f090905070f 64
    0x150300d5100103802c0c05102203140b0340500780c0c56088448146a0040c020308080b03a1182141d607071281000116940c802940000c030758030800402440f4000c1d441028240b4002c1c100030740d40342c0c0c0000000d0501d5044482103501c540c0d2240240059644400910f034403040301030800c1d10348466030310040d65a120041c4020200002c08008908118401c00f2001e04030707070352250415460030400710641e283c0f0480d0044e580540c03078010814801c082440f160b40707800c00d2040c0c0058040c164a035102081000380701802c0350000c0000c41b0300c4040c080e191003099070420f01582401308040c542059070504080d9250b001c0802d904040c03a0071000c2d801c000300e40b07079010000603440340c1c2e180103403400380d004d84804500d0400000c8003040c00908c22425025400b01c03684100003c0010800302c86040c441c0d03005c20b50307404005030b1001311411301c0c40c1001440241d0824050600c6201d5603a43c0c1e0008500032104d40e0021001e00c0c002c0340340c07200680c2084489010b440708003801e0206141400c00280031071038095422040119 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457219244 1250 457217994 457218017
    0xc030f170304030206091005150f0a030b180c010f050a050304060902090a090519080a081009020a050403051506011e0306080307050106030203060c0a02070b0a210c02160b0a 76
    0x40c0300c201038031031034880c00152285414200651100001c888203034040c05038114041b044651841903c0c4100e00c100d031070700200d0306803609101394140355681c0b45400580040020000c42c41808215100b0b0a42c070f22121700d852881c1a40d00d0900e244609054140705500c9011410160000c080d600183c0503858125229070f600c1c01d2440280c40320b00c5c0041e41103075550701032002000c1180c002c0d4105074000c2c011203029107640c2002c240028031408002c0e2442030240700c1280414400c541207500030407680007103608562144008022039000780c1d1404045200003c00308100907041c0030002444800c00c510451514001c400a000c030791600c0760408554a60744182c12042c1d006c2d41c401c80c0500300d6402201d0301c0d40981e1030514001e003c1800140d01c83d03c1601d0008010222205c00c507422408198060840340d4503042a0741d200750490a014010310003050480d28400300c01c2c50b0303921106000d500380400d01c540c0c01c44001c0d040000d00c040c1075a12180500080c4200f8820340e003102c000b1041482c0c035150a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457220494 1250 457219244 457219253
    0x3020705040209060d060806010611030c06060607030908060f0403030e031c110d050a0f0e030717163002030c0a0809030118060b1c02010804022202041e120c030f 71
    0x4194403800c07032030074036100d404207038007c0014465050b130f00d50392503010340c5001340010b40f55a4094020b41c00071a40c031980c0040c545041c110702503c0c0080c464104404400e4490104a081440841350015500ca20701b040000f0f156040c05125440c44030007016620704034400a808071500340d40c944c2c8405007616030000e1405181a942280c03070314076405c903080045060000c601d802038581080141062820700840600502001c4201e511041d0b118001d0701c605150141000d00c99046484444a600708040c801800b1070b80040311580d411140001542441c81000142514104500029011944240b0800c149d46200285021840c4c2c2c10440c0103464568580029000d009520661450041d400500408004540c0c1200000359021280c0440e089002c6500d113094442510019000030340c224049405420191f4441c00c5e0a11802090000300c01d40b500250181d0f1303c258064410660a503500003941015509980054906034003406071070075541d250b40c1c10646180c00040c0070003c88a03010030812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457221744 1250 457220494 457220497
    0x20d0c0212010c030b030c040203190b040914060a151a030919080a082d040501090b10140a0b04151e0309030206060405091902120709061505070302070504020906 71
    0x80c00e00c20081c4503c0000d404024060201240c502e4020300c03c40100840e10f14182c0203a0727100c2c1900703181c040c24102401d8102c00140080114150300a0303a25045100407134034204920800c41141c034014080b81c01c0810400b0225000d4801d422040c80694100303128070b10303842c544010844041d440460b00c0b034039003040b0a030410300021103940005081202200400107098050400348151351221011aa14072150b10300c82e14a01407140d100415a96107800d07200580c026164205026900005034100300f030b961078816100503113400700e09070101041000075250507001490b04420503904868001d10f030015141950080f070240d0500f440c0a088900140741c402c00d111032500c03008030304288010180c50005001001540c6080d001030081d074001501c0d905090040500440c0410000c161203540607210040942d89000204d0344040d030301110a40c201e0080100c4400341540080004080d86000303030103603003503040d990b440d020702205200701c0c004a034012403128100d072030607540540d6030681d40002031440d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457222994 1250 457221744 457221769
    0xc020a09060608090d030e0a0f060f0507181d0f130b04061505061e0306060909090c01111615050c0a0327051e0a0807030f021e01020d0c02 61
    0x5003807a060002418642c0031901c10302610f424400d8a40060411108405580f0315101c5500036621942c100c1d00050607284c0013608143c010792001500041e40c21140d8103455080c5c641c900080d1665032142c0702400011400d100611803207840c0321012003900021300c00320400500320140c940240f400a001c9240310100441602d034000720000036442c00c0d281c032400500c4040159040c1c0d040741072010032107080c0350084458407545400441c0c0301c004a0703100001035520081086401ca5000c0c040841603859000210b0b004824003c040c0111001540c00100b40c4840f0b5003640096901129101c031101640105c0c0c80142e0342000080140c0d082103803400d0750503101d00580841d25100d00b05281d020b055002c0c03007200b0000310700244c400c402c0d030440072032001484441c02441e900007d0300001c200390700b1090140c0c204015016141d502102c0d52100118185009944252418040c0d0b240a40461030504c4121a40c540302d0320b00340d0f035078100c90b900003541c98907008040811f02107544450400d5503168000c4103079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457224244 1250 457222994 457223009
    0x9050a0f06140708071425060509040903020c030706050c060f010f03150b0907080402090c04081518030a020f0c090c0d09030e0a2903070203091005040b040308070b091c0c020a 77
    0x4010107030415065846803501000c40b682c5400000031a1f60b00940c1040000702c508581c0d420b0304080308001000300410703803074000303c055200c1c01029080b01d0704c060090000401007074440395258110b0050003410f1200081000741da00c0c1090005100c040508504482984d0b0000d1500301320040c0000964002d10b800c0780041e03844290541044081984100b40030f1083d482500e0800607521030015100450180d0b000e11030103a0804550300b00c1c001521944990f1041c4c0d00d03219054062a150881421a80030444450060b00000c040c40b81c4960208060b810512040c0d41c8610f151408070301400d85405484044848540c071068071909251107880e44030844103009112a1515544884a16201095a040d6001b195804100010114810090f00e2240c1c402d9000b40d80342050030000c03c540500240401c81c288401800041208500b940140001d148650046a034983c1c15003800c880210b8004d003890700e5940300c1c2012004050250a00f078000c128039050000c0781c0c00a620014210600710781100f00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457225494 1250 457224244 457224263
    0x1e061809020f0403110a14040228081e0402010c03080403020109061a040b0303161119090f1b020c01030b061e09120a031d1f09050a0f0614070807 64
    0x1c12444051000f0030403a44210500092100c01c4024000b0f52015489001410a40740c00620080d0401d0f80003040840b0303c0c3c0c41a54003400c9006030482c3c840c809200c1030000510054100000040b002c911484a02054221801185000d90000f4800754110b20028200301d001c00208040500075005005200d40c0b0203028099564185d1450700080c4501c91329501c40e030300b060901001401d01000b1503140100000d0594400715543d115440140c1e880c1010640000580700d8045441c40307400d2050001c1c3c01d46a40201d19007204d0751504059079103040307422184000c00c0752801c20468000808000c142c0d000c0c03c0c0807919404200006840d80100303082031407022002500b04100c210f020005001001c01200d0903070307001030301e85a22a940c1e141e040e80280070038809016801003030701003481050b22000060150f21040c2080910a5280c00100c0351440851215442030025142450504000d06540640c9040440c0342800050131500f070000c0c6040468000204501440f040741d0484481c17940116900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457226744 1250 457225494 457225507
    0x311130b06030a14010519030f020f13090b070f02030d050a02190806150304080d0506030c0d0318081f0510080d020a14160b0a0c0506130b011e06180902 67
    0x910284c0035030000e04584050340400403406280c0a01304814003000c541d40c0c201441d00b0b550b52021074007408801664480000d403010202c540c1c400c044810410000d000100e486001854520701c4200301078003c0081c0b007422159040c1040d40002a00c0e201c840205004c11a03494091042d0300a21070f45980a1019001440500c641c0e6048203415006d00026075160040303c01c0c030001000d0500040e1030080c90740804005981004620750001e6800c0440201621a0f141c4144002202310042000442c04521a0109240341800480c510781c02003400d08041d01d890112005002c3c170a5840c100344804440e07a4401007605001c02442c00302c09000b1140c22502618082d0303401035503c145c020b104644880d000c00005a0109c0c000c2000d0214511000581500c2c90510200c4e041e143c0025002c0801c100e074142c20344011402c10407085001d0341017440c80c124240c2c01802c10480c5818160004203c0c9030602c482000010200758030081184c3c1b441c5040354045d4610340c40c6030039594003540030b19030750350011846 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457227994 1250 457226744 457226761
    0x712180f08031b06070f08040302030d02030a0509060703050606030a090c030804031406090316020f010c0f030e0f06030402150a050c03041e0617010611010b04110304020301050f010311130b0603 85
    0xd140f1400480b00c2c0c41d00c01c01003115080d9544000705c40e0070002074005c1701d24031640d50003280c406400174442c0c01642d0501c20146041c400301e0700125007412805d0788450038050b074131400740883c0b608070100c0e15061140d46419404200e0f588006404c1719446562000c0980c2800241e0400c6006154080c02c0c296481d5924103000400151030210700129004000204103030010000c03c603100040e402061144880068082000718129080d00e181440300311000900024031800900350364502c00e0310740e0703000c400d41c040521440e031070702c000058000c5004100b40400342c1c0e510b1809050f410f08003040d040e40d503140d8440481d43c03802621074102080c8800300300491b0280305c9903154101820403140b4084030a0f41d503407080b44c0084d65803c880c201c250120006218643c460f15120707920203000000810030300343c00808103045844c0c1a0f1803403001c20000c01072008500d0280583e50300701d9800f01da0041a0750646e1030703034458500301a00316071141c2882003940e070100d401c5401c096030764640180080c1d103d1910340354 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457229244 1250 457227994 457227997
    0x3070f140313261c1404060c11131404050106121502030408070507090e06060402040e060f0402090a080a06050c0307140703090306060e0a24120c09020304260712180f0803 75
    0x215000800c1d0038120016803840608180c801f21007181d600c4061905c8241c5540011500040d4116000401c069102507404030b076014901d094094002102180d20302130600c0c0f421a180c5420044001d090311615074041585000e11441c4030394944070050740e07a100e910740001c1900c2281c0000700316009442d80002c59001076405500000d81e114103552a41c0d0305d50003000128800d500990405041c840007145640c10284c0811030280005000145494507420004e4100505a84642684d52081c0c1c90313003003042464000e20360007450030794510b811070900c5180a00310110290041ea40d069010822106151003149480000c540100081040c0ba071210f50984070b450301282c01c0d851050420000031000b00d074904c50407a408240001201445080601c0c05030f520292072400d44001c544d2440101e203041c000c0c802036024074840c0940080f080240040c0c2d0510f104040803426400000740901e5011440c03806048009a10a140c205410b0707900c0c0d540301c4d8080d1203a40010510960000011949240000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457230494 1250 457229244 457229293
    0x120408030115081303180801020c0c040f0911151c050403030b010e031f09080307031514100509220b0406141305071103070f14031326 59
    0x100300e0201010001000d0340c1104003680d403c88441c03c1303940282c0200381700c0c2c210496020b00030450901101e51790589142640c101d906201e02c142c200809600e06460b1901ca1004c0001400405105050b81c40c1c603100449403440c49010300859600c40c2400c90b40c6060030894040c0e8114003d46c0841c00f4051200c00c005040480302140800d00d8520b03407090b20340c000c0e825076818550041c02407080c0210691503080d00b16816000001158a50f214400001d00e120091031050001e5074000a0036001c03981d00d87c801504c181e000a001c01c0d203003240449030340c80c0d201e0460754800c91400c2c0349994240507408142d240c200034150b500500c894521511100c0f001e038101481c26001140c0c04d010300f136100c0d41c80032502d4150340b1015601003040300c0391071203082c401d4018650014181c1054100c52888404103829688850300031180c040c244900102048144500610b41c01501c1c80190708054202c50040134000706406100516030050410540d4a99858002c444c034078500415550320f5543c4031081048d01c0d400a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457231744 1250 457230494 457230509
    0x60b01140711150706020301080a0c0e01150305040f0204090506010e0a060e01090c030204152f0a031d1e031b01120b0d02090c031005010201061d0c1204080301 70
    0x4104600c4800301282580c00940d00a01070010381d908003401c11518a04808060710041000d000b9080420b0041c800b46000b00200009084890220b01c0c01590521450b08070342000620305005110382100c80300007420005c90340c2400501074071942400c0390303801c0c00c020b00298000e00b4250404c041210204825040341c40703840d0101e035641c0b1555031020507506103005062940c0c031140c0040101500a030818003452110382401031070b01d41c807a01240124210580303660007089a44206224018a03648941980d40241d00441109054502e0781c9803101050341d000340c10001941b8111843c400b0a4040b40f480e404010076003c00213584681380c800700c4902c0c200040c824054880e0302da02c5040c003605c0700c0d59140416511203034075038004501c9000501d04540820740190b6141b0b0702c0c0c00107840310160725004035400303010503490f864610b234540c40c0c244030350700078604690400344104644801d6004101c0d40c01081000148c3d00e60340c413482890f01d0b020315858143c1481029081c041444000170003941030b0f5001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457232994 1250 457231744 457231757
    0x180f090c03060b0c0a0624121401091e15180311031201051302091e0415180e031e13150e0f18070503060102010b010c021302160807060b01 61
    0x440f10040340d503000312001301c1c4941d0050f80c180f0340017610071341c00107826802c4454040240104a0400c03994141c141d00301d9540519200c112009021340707090200c01490220000340b1420794955100082035004038407075405906070800950400910141802d4010401c0308104060440010108034024090703d040c0c012170f84082001180b8031011048034507001c6515075a105070703483d00701481114005000c039602c0540d800d0110003640d5030b408200340c858500603441c50b000910170104010403a64541801c106084007084100114500d2100b20600704101d0403000543c18270b1026210f040d4400c540c280e80c9486242484410b61843d9080581001a0b00c15524012584c4480e10840c85816200302100070400300c0f41c0c000c01a00c0d282040105240001c0c00303170304481e0314502501020f40000d03258440802c8000c000c03c0940d50742403246100c413400900e40580910800d40106161042c0c81240d011001e40000d00000d21440c10824282555444004555506102d04000008088403248240010b65 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457234244 1250 457232994 457232999
    0x9050a111207150f0207032913050607080a1d06100b0309060412030b061b010c031e09050114071e1103091e0409140105010602031207180f090c0306 65
    0x50000d03201c02519100c0e20702903c1d00c43e403490240d03404031075801e460b8218440c804000c400510311b8451241500c583c03a041414006047ca040684101e00601e40500301c5800c0e0600070205030006142d0703402101d241400e101a40301d940c0e190303020b04840f02040201031401c0716040c00002000a10521803107850a1560b10f850300c440f0912501e100036a90041c289c0d2101001c0b40c007080c002e0310301c4428917505040c0000d8032880e9a002c92004d030080840700d040d290001e804407003105c07401c0c001e00890507440d00c2c0411a007060f03007110301c0c8603003034500300c0d54520369440840d0402c100d425404101d481c1890840c0320342c0f40c900460010a0644203100303244100000400950a403401071041d156203d030000091400d003644002030241c42c1043d0610300300703182d21102e80707107100c0e413503a10070800018042c0d02c0d20010300c030301d03044d8590950300182d005030300310b41c0200f015240c01c94142c100c0c150080418a06200d02241c010524043c049054000c0803540c0c20405000500300d09541c1300c48446c500c240c81c14040142d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457235494 1250 457234244 457234279
    0x203010507030504030f1b1406060f04020406020706080901060314030c19110607060b060d02070615051f0207090c030f0c0206040b19060305030408031e2106010309050a11 75
    0x2e001344e40c010301281516851245007805086210a40c1080ca441805130000e11340368014609514980c0c03403075540155050110720308040c0e80310000404203807001d510f040c3c0b0b4042c0c000d690715131a00c1003004100c204004071f00869020f400c000300954102d00040d60840303c400010f034a070740c000740c4041910300c1450422100d92081c8040c0144158001c89180c803423443c090284a102d6100035002c4640d036943e4051100c00c1d81c0d40b0400303410405440c00b0010380b00c030810703c0d04808a80007107540d40c241a4100108101980e2500d41040c3d01c0d0700c1e075101c00010b400c0c900905914010a0350081d00f001c40c1041191501c2da03901d80d00c00241080521030034004403042040990301d90130180d80c082c240910020014028184586903c00c0810702070000098081d580c4d01d480c0c1c215002600301101e640c0002034442070003200c00c04158100032900070510316000d81c0c0c0c24103161500b80000e034030403040c600000003035850307019500040940360440141e61a217101c40c5000b24402450000c080d2040c0f58000710100a40c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457236744 1250 457235494 457235501
    0xf0c060e09100e010b0a11060106020601170f060c070f08161703060117061504030503030103030e01020715120207140606040e0102070c05040914070e010503101e09080d060b0403020301050703 84
    0x40c3e2109108400a07424034152006641c08202d0841c244a400c0f10881c0d40940c04000160080c141d40d40a4011541031506c00c00d012840000150380c00c0d80a444159102e00c40441e02581004d1684501e07030b40c130001c91802a00680c00300d0f10103000180046a12501300f04040c01c00e9401c988102040c40802d00384c0c001c00d0410703000c140c403098002800d161502a00101c1141c3e01030300960001c00307005401400c9a2454443d174080c0d082118141c00100c010030801d034005d4400700310340a0074005490114141100030100000d014000070070042c2d20001e4030310381802e40d412240309a42040f1094604441d1600b210380c1d510041d00c2140c05580340100d62404208180700f52a0181c1e801003181d000189010b0800c00509903040781980d41901e0500154103c8408001e0354009000d072400c030b010707590b240008050410b03050f021038150050a0420740428121804244c6154141e0000c0004604056040010b102d001d1090010407803454100c011821030210b0015104582c4228001e00c1035a0ba2840b003101034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457237994 1250 457236744 457236749
    0x2010b12060a050a0617010e0709050c1204060f02072001050913090c09090b01060e01020309061c0915021e0c0a020111120a030501030302060604090507060c0f0c060e0910 75
    0x1a07000303440800c0031240e80d5048141c0141da403c01c00300b07445440d009400860107501c00407034500c0e03659410001e88494103111a00c0104a003110400803450051b08021a42c820b1200d0984007401c840c00040030046207070f008156403c002001103494580c0d625284c2c003824803640318400c8410b848190001258410303001c07284403090146c031601c4134540201880c2d01405840104480441070b9032030104002c0054890100030b10700031f031a925a95450020050700b0350340403406050441d00204162a001c0e1603060440c1d40404110344560008205019a640140300b180001402680b05101006000034182c0151400104c00381c840d043e840003009040b1460300c25014414020741021081001560103090b04046000b603620a48150f00c50070203101507250b101c5040c040109035a80014014940d0400c20581e100394251400c120b00c4105e625507642e070322890f00c00d403000c00c20000203200c104060300701e810f2811a844040c403002070b52202d002902c40032007059120f008a0551000030548078070800391104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457239244 1250 457237994 457238029
    0x50f010b0406050c0f120318030c030a080411120f070501030902130b131514090f0615040305060c121b190e06070302010b120a110904020307080d0c0302010b 69
    0x14040c580300c03007501c0640019010280d9801025482d1003c1042030029211220344880c00b55038915002031585030511000c40e10b23503101e07402482170a040502c0001101c51460f8036061003205641e031440c042d658825641c90094005070b4a6201107001400000c80c441008401d03810303a04460b4941c03004408482014101a43c40010a5030501c50390f011684014a90000903001c903040e00120502072003031314000f00040042181c00401041080c180e18080c00c00c07918121002162420145448241d030000a003050f44034800e080519801111402c0031100155801000d84041d46000e03810401990440900d10126030003607030004040580107140d00c06140a00401503003054003040416403500350a42c21981400000644000660380304009001d24520039800442c002070445c060180001014140d04441d81c090580140081c40c0c595140000f9241a00c002c40b05541c0e13400004c0c80c052440e440250140541a11103200303c1d844001210803d0082d0000e1010006400c00c0c400f450310150300055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457240494 1250 457239244 457239247
    0x40b0c0d09140a03230604030c0312020301050117070e13050901060602121207020106050a034b211107241b05031324050a0f020307061104030204050f010b 68
    0x8000b034081074003e4181d0b0450701e00203002d807408000403840c1030f46c180c809401041c0c0c2008528201a4840c02076000c60409a10a60665240c000080d001108140469011960b44070001d010742d441884207901c900e01c002c2801c00c4804100c00007800030f0106460500d41c5508240d800700c0c56600004920031480251054145041400c0309461480100684880d08654840000288503584c080c9008090f6010381c1c0c010200d95840e42107c01c99100c485851070020b000c6030302141c004415400d9900202030301000106003c07916140460090900f03035100c0710b14001e81540b24203403581c080ea580c1840507980c01120704040d181c0d02107490841a1429044403103500d650314a41c258455013503905800d00400414034013131401d40c1c0c2c15046800418180c65075091504007001502e0b040355403c4403688545820003d285100c0c54018042e2051621400c2070000010303140741c80341c0c800c20440e2003260b0000740802150b10f0340c00d03001150341d00030b100a0388514189000308190000091007141240c1070f070403002c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457241744 1250 457240494 457240499
    0x20a090911040e0c0c0c0d140118080405060703181e060809060123041e0b0402040e0a0c05040b07120f020105131211011506140a08130602040b0c0d09140a 68
    0x500702544410180c45c4180502034024405446081018441c0b03489042e140d608610880e0109007141c80076035140d4602140d040300da8000c0360448080300c058030750a6824a64414103401c0940b09031061648406416120f50000941d0891240034500308090f0124000c2c043c603130360002120700c2c44050b5183d81150300b02000403c040302d414201c80c05980e44d4481d680c40d0040031040001d0032911040e0384049000d41c88681c40c80c00168520030350589090880d4114102030500100502c0ea040060107030741c07103903550301140b03c0080c00360302900c000703121b15000260f940d5641e01d444540075a022018601049140c1c501486140c01801207034400c0c80540d900e844240e4145d1036040d420201d40852005106500c0c41034556403a081c0a0844160342842d84a40501c0c58008010b02440041c1c543c5c0d648624207000c0e203108994405030054124885c1401004a01100e0034010002c0c40342c1c0c1d028646280001464087d00c11020603513081480c625183d80c1000c41e5150700d40200090360892141e40041c250ba4203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457242994 1250 457241744 457241761
    0x1208030a090309030818010305010512060408130f0f050102060c03090c01080a1104030303050f070306242c1809250317220501050d020d0906020a090911040e 69
    0x6454041d00c3c1c00c1c6001c5540e80ca555096a1150381c41c40e881d48000314140107196010b0103000d0040105403403108a544c1c842c03030074a49801c400f50004060900019160010004110b44034001d07140310301c003007083d09650f410302242e182d42e544a901d0250040900190844041c6400c1d00e10640d0352001030a0000b55105c0119081880104401074080d500e8800c120081c03007603005840603600c02d460016050034001d00c00008440001d281404244c24104140840d855100b1200e0052015010040c0e8107109480309035581014100070302c00d07803d8a402243c00f01e100104030320b036202c50b0950b12951000c40c40c240d010f05162080b9440c11b502da1001500038018500381c0007200303802c1e06202049100f02c2e22a0359988882c4400100c15000c1040490044203100c01511004070410415001240c00d514090018119010302c46211210356400705404000e96050380000c10111361091007155101074900c07020344040100d0240d0004103180150100544018104075400e603010318441001940d80c0099 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457244244 1250 457242994 457243001
    0x90302010804060632040e190507080d1d010320070f0212010e100536011104060e01050c0c0d02030f010504080d0513030c0210050c03040f0f1208030a 66
    0x2140c403655a250009112941e050b90059031136001c81000841e03c030084804d40c0c201c500079101c948901e207040a51500307020001030308c4035030016455801c82c08403e5401d20a0030615250720554070b6006245070600c1e9180d0005142985101000d107440c40701000c0d0004404440c48002c84236445031000c040298101840710143c04240d01c5603109446000c11303079010501c040c0601100380b005a440b00c0c0480c145e40ea081c06010a0f44503404001c200c2894a034000e11026103040c0d42022610100320792000d5108108500700190a2513036000703014010540000304280e034000d210786030000302c412090b0020b540c0b007002141e07844400080107040d140303000c408106903503400101c1264144510211455100c2080c0104c61085024401d5683c95482514000c0309490004011641e020032107541000000d0300200d04440440d0143e603107411005000340181c40c1d9100f88810100706102c0850002980380031070345010140c44032071415080007a41c1750114581d02c3c82c0d06100034145902480054401c800550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457245494 1250 457244244 457244251
    0x9030703061e06080f060c03040503040e06010e04020a080702060108031e16020a090b1809060708040c0f03050303011802090904080d0209090103060b04050105100f0e0f06040602070609090c0903020108 88
    0x1c402e045115228480350044070701c1d65000503103980121000390309214007801b0056001039441c20282c618a42030f50344580764816406400c410b03443d44400708005034450807840184503009482103681302a03080d8042c1041008852900040c403074000007081444011050301c9105201040d403980c02080b0700000d000f690081c106c0c014000c1031450311500580c0d140941e1030000c1070040d4001070300b10704820900070181e910b41c02ca40a10303081c4906201d6101c8001940540c49a5586400580b5444918210f025000e80364001c0880300a10880801407140200c02541203606003c1d22040481ea048040000d0340a080e0000b40d10004082c0024040f8980c10020540c005040703900520703041814001078940c220a030015a40c1030303540c1e03140703c905003010b108242c05001c00311544144118400c100502c2a114010300c40e00304210301c070300014285c480d031101071132070700f80240801e072200e032900f00083d5144480c0c0316050029110850000d00003080c0e11504400c00e4441d51078030b12107411500155a01035014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457246744 1250 457245494 457245521
    0xe0f10051f1b0b07050c01180b04020d03110102040617060d030e01051b1f0c110c060d02040f0603090b01061103040512030c01060305010c020d0801050f040b011211031b0903070306 79
    0x100401c0001883c2c40202d9114181c1d54954545031090107900e10300711707814a50102c1c0d8048503049400c0104010000e41648940c1c1201c0742d1a401c1000e2508481d105100d03a2034025960010034085007007600020104100d64980c3d402032002c0d80e8090400161102c0c2a0000d008209040484406544184000c0400110081142d40c0341c030b400c3c01403103140030f100201f40444035460100c82402003c0c58050019040b41e00e00d0036451100000301c0d41c5403984560303200d05201d05000244030411101c0c68064400900380d00e000c0d0302846544401c081e000d440300385404c9580041800000c00c800d80100110506003d1440086050605180070b104116501080b454064801840070002d8204c09006181c0610f100300300214505a60040181c504400d0b540301e582407180540050105071100c11100b490380c08222001700d1a0180c040041c1c0780c403640c00c8008a1001d0a001810100d90f032020001d500500014007090351601c4e040700206c0140c014801e0b090341c0341d00004810030102d003036600071200d8900350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457247994 1250 457246744 457246787
    0x33a02090d0c060206100801090b06100c020d06060303140c03070807080702030a05070303120225020f030303040c05091302180411030307150e01110a05030702070e0f10051f 76
    0x115200da2841d00d4a070f070f000000682c0018104080c10411822140090154800900003850240e903084c980c4400200154051f04070301134104942442900c400380c000780c02070410030086d032103410248050185400154040340280b03400a00a04540c4110790b01c0110510265040098658a141035030f40303d048140c40c900418828900543c0c0c0601c04220000e2003440207101d0305240d803030003402031030560364051802441400f0024600303c035044085040b2401000081090341540700146007040f1526086405110103c100b00400146207500001c0d900b040341e002070f26684007402c002c0c1c48658860000e400060104540c0c1d0340c40301d141c120f15003040c0304851001c002e061500100345943c0006a00342c030904560301901c4d159080d1842a40080c028040092025003090f034000c4601c0e200303901c01101040800800204564828440314000e000214001c03c41c03170a08114100c45080b064844d500c58a0040034009514030301040c3d0071440408070b54102010300d10f00d0720103948400c1c10f02071141220a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457249244 1250 457247994 457248019
    0x2040209060c0f01050705040503120c0709050708090f370501051e011401020304050d03050d09030e1e220902030f0303040c06091206020a02031b033a0209 68
    0x1d4a502030400440c1d80001080e404405482031402d660016010b0340074400100720601a80d00c0c00304e00e05c2500c0f0f040c0001e455403000140055440d00c941544451541ea1600051101690340541d4043c000c2040404941080c641c4042d100e8543c00302c48010380c0e1425841184803e000348480d036442c2401c071a203014042008040e212507003940c030221240c44441b81c1c3c3c40c91004075128030041050240458224071000070f21031500103507aa00c0b507402014881c5a01000603010944101d0846007040f45851382400084124500505070910400e5128859000d856080307038941e201040546100b200148803400b81c0103803031140d00340148400c45035140203454040c4180543c400b0042204a060050f004556034581414050042591604448208001803c3c100544000b61190140603a00020010fa4408400030141e2441c400e220740c14400403600104d554880780003101410302244040c146400c2c07120642c50044903040e0701001c0b421980002c112001c5a00c1641e03000c6e11214034080c0c0528030703c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457250494 1250 457249244 457249249
    0xf0f11010608010203100e011202120a12080103060f0b09010501030c0201060b1222120e0a0509091b010509180a1d0a060b010f02150603120a0e0918031602040209 71
    0x55450b0040358103690000f06000045a035181c1075401819030301c042003259410181400f850400e2a0b0303003e0b12401c014406401042d8041c814000b0690344002022611a142c81d0085e1030360f10240310a9807944e18106a0b1198030445008840c2c01c0c41006005240d40c4e800e10740150010310310740389000d0440d0b580d400302217011031280005208440d80102c1640452800440170b05540303c0d0000808540d8010302c02030030001d08448a0590880c0e4913052460b9564a60400f0032501d510a0f888164010542000e00c954010301041e2440c5907032852804243c40c0c0340384030054455104240d0b000c1d0b0460080103031000d80e0003107000d807030b608104518004100c824000144200700b4905039142140b58009000703800800815200d00c101010082c241401c2d40018040081c0d04c07401c0083c42c2110710f480f81000600595410301072802c0d041c3e0041d03010780d141c01c40c0e460001c1200840640c0c2d5030041c0b50202c08106541000e8102070311102581700158517020061012100c41003885904a822075000d10210340180d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457251744 1250 457250494 457250501
    0x218041a1f0b0405190e04330f0f050903040302010311190f0e03060f06040207170a11010e030f0f0c011b0305040209060405060609100c0219170106060f0f1101 70
    0x24100e0030025a100c5040104100080300041021002081070750350130000401b4849145a00c560441050348140d600f0a501030b150103280c03080c0c00c011038010314410071401c07125800102c15107031041040003d9000043c45204503041922510700e0381d8001d2004100642c4660001904e00c00c40c11840c2c1d0034081042c4d014070702001082d0001d0041080f02d803101c0340036644240c4200382c00808400510b0a401c1c0a02c0c58848040058220b44c001d81c1c002610100f440100e03481d01e0b03203001c244829682c0d2840d54100050840c0c5285160700155400c2168545440c40004180c401b1040000e50462a084001f80c10b4041380d44007031a40c40e215503c500c00a905040c50255a03604503006880c04901e030700d000d03c10403591480040c40144600c0c502001e000300c1e07849003403d4880d421015500140c3c804900787c02552580040f01000b50b01852142c0081461030b880d16807042207d04015907030601f8000502d05a00303840040c0104400100b8000c0b0441d0703401d1240d04400c00810f04c6003404202052405021803e5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457252994 1250 457251744 457251749
    0xa050d110901021b100c05160b0c01060506070510150803191403100b0306010e040504060b1005030c0904050c09040f0b0a08010911060310210218041a1f 67
    0xa0300020400464658060240c00c3c07401d10098656028014580b000600d450307013001a101c00c00c6000c1460f07500300541000050500724104c10781894941d40c030400808030b070340010043c250365400c4c050001005d04248080c1c2e0912988000680141a552507050000701041608460702c81260315001807070140600050a140300074040321603000b650b08501030b001d184440c91000210b01c04000b04500c440d62080d400f800d5480029100b036503601c41c0001265030001e01100d5940c05840c200902003001a01d6000c1c0c42c00c401d09580c2401c01404558059920740022204003060328010460b690031858590b102980c00303078403520301c54240725190002c1002c8440c0d0400c40d4000c02d546548130583d80c0780c4010820000d00030136000344490441c0380d07100c0d90240300b8011854083d01001c4041900c112080a0b1080900000030701c0c210314550407410b0103000341c2c14006c2a401400c0000048003680c44010842e842990003440040e2000d084c0c86401000e000006c00050840d018003100c0400c61120f030050100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457254244 1250 457252994 457253021
    0x90604090206040e070e31023609040b1602010f02030702010218060a120e010f0e06160915050c16060c02010818071815090f0e0d0e060a050d 62
    0x903902d02402c3c0070308640d0b00110501e205411020084140a2405411007003c0e101003c0c05c8099501e0754008001900490744486103500c114827024448081580000d03140034590300452051806d001d062041c2c05600380c9020b00841d20300000202d131402665440400700f4001e200000c0c001049403442c00803a0816210900141d40020f003d50001c22200401500040222042c624011000001521092403200320b640ca0075240c0c44000300310dc0c029030000c401c96008503020303c80305502030385507501d4140440d01c017600b100740c07065a4002c0c03d114015400c00d4611000d2611160000e50106071200d420084200320075105040b21341c0c1c094000114000010009030711905580401d03440050040d02000300819201d501a4044002504001600e2000c076104124000d10180c12006020702800b40b6055101c02c1a0f41d44000107540650380e807060840c80303503540e010840c0c2c018840d980c03516603440062003400681c2c0c9401c6031541d46032100003480c0140c01c5044c02e6140520241003102515031a00041d071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457255494 1250 457254244 457254269
    0x160503031e06030f0c21160f08031303062d0606030617030405040b011403070503070e01030e0d080a0f1d010507091d061512040c05030c060909060409020604 69
    0x701440e20111082d810031011405824003402e140251550307802d1014405114030702c540002c0581d19003100800c5001c03031400c004d031060603442200201000c895131207070b56807080340502d0000d100c0c04044296002c880305911400c500138915101d250140601c095880540d0f0418030341310320401c1c0603030b014642d95240740c0400303d02a841c001c801350840d0941d078000f48401c41c140300000328000c0044200c0d816a02c0071a00015480014401204d40700c040803042800103d000060244154104000e58800c024658400c003002040400440a94a1355007a03100e0952001c01d0114110b402802c425600ca85c001307000040c015007481d40c10703056483d4410700e24803044452044a08034142800b886a22001d2070404d454680e10305000780000503c23449000d030500e1000808522180d543c816905003245021000d181c0b923140302c0c07074a1562840e0640c0c1c01c0710300049010000400781004112840d000380010203071424040d9900a01c0110740d0020000359000740d0307603100500143d4174940540003400d80a00e060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457256744 1250 457255494 457255531
    0x90405070e010506131a120403020303090705011e0e0f1509040c0c08120c1209010516020123130b0c0d05150a0320100f1805060f16050303 61
    0x996191810307000f01c2e0140004200c8641c0c1c81101c03865080c1100d011940b1010525141502c6907498003a800044003447d80190510080c0756001003e58010030065083e0b511041c0c0c1c500056903045600e02c05800781c041400220b480d25030240c1c01d081002d01002c0d000351441c40c00300c1d0000b120200446200d13181f030000030480c2403c0b400d2a101d040b11120b020704120720741108035181c9418900600542c0a2085807200000b0001c071100815503400c280e81000c0120542011081c45019180803962810700c2000d4403800c481d41c2e441400b030068080e50089100e100c8078a810308015000000401d2640d24003200800c11000076420008039224541032042e039a12910500d1814041d00d0020301804c1c000000d84402d41030580d0f804060f0001c80341d101c00441c0c10800082001328a2210420f211503105112041d407040c11130b00601e40d640241001c1d928061341038050b2000d8502d00d903203401019040301007800440c00ba9501d6000074000c08807084c040381141001569440d10f1035208075105802c950a550b0807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457257994 1250 457256744 457256759
    0x40605042a140f0d0209070c02090c0405010201140601201c020c0a060513052205101e0e0f25020102040609090504030c110f0a090b010f020708070b1809040507 70
    0x300c99002d20100c0c2d0b04071040814000040c101070072480040c1c411040b007070101d90b4250181500d48100c9502034085c6c001071074480c026845540162140e207003d54203100000c002c10a0080e40c051007814161a019203009207459810380003a0040440d044600c60360348c5130580511960582402440594000c100b100d0100c07040c40313880c0314298065018000103211882d0388281000e4910706940c2d007603420714220024100d4204512104a816598070f40c94001807041015583c1a42030944182c042d00100000f9140c01c019008503640c0724902c0e8030700c2c032040030928101c000a01180c110a03c1d48111040008500000403001d500040000141c2c2d40010200a00c942111280c1c008004440c010090b0385440d44001c1c10444800d0802031107454400d4110001d5901c03861011a81c11019014070162502c0b041d124000b065004130140c0422405914030011610004d400016141680050f0041c107160143c80c0302d0a82101702c01b0300f1046407000700b0140603100c003407130140b00b035004d10001c2c1f2003289050313035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457259244 1250 457257994 457258019
    0x5091b010507080f0a0c0807030903020102330402180a1a0d05030d11190302120f01031e060b040e030d0c03050c071704050301180611040608040605042a 67
    0x2946818403400344007410104a841090b14045500055010303541d9048280c11030f100440d500e030003408071101003200c1717040c0b40c0e1020f00c01056034400c1e000c540c44603040200120b455440020b5071480181c4980103014915600d441481c0c0141c405026008444000085010107481c11100a140180e4580700b0198030506810b01c407803c032000381d858191502c800d4a600d40c1301d116911003021026180c10604000803007038011a100104039420004c0480241c02e0001c0207580140191400c100408000c200303646180414141240d40c081da0701c0c500c55088001048070740d4445641034480c2541e910001415480d5070013006000ca4100002d5a41d6603484155a02168041a8071600701440e000c2000307107000681003100c43c0c07a904410a013001221035103840146200740e401194040d420900d003102100300c8850380301c00c2e86100d100c0c18800300d40d01ca01407034200d00031071041800242448012801281c510381c459500b0a000b1107801203403800c4a1036105030802101006000040d050710100041d846160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457260494 1250 457259244 457259293
    0x7110d081801170601180e010f060914012106090f0203060306070c03020705060c010207120206160f0c140a02030105010303050c0709060e042405010308090a050402092d03010509 78
    0x81240114407000e403154a4108004e02c11030521049091030701e4007142c8800460024440003080300d44a6845d00f450005480013403242038080340609001080c800101020b2900c6014181e40e209410704420295500c0303040300c07050984c0c078503984102c00705040d01a4001c82c007000108100150b0390b400d001e41454036098009001e8030030450080307980c400095000c54100d04841048a10b15141e0400031002c500a2141c4180200303410060f1400e66466138000c2036141c49410100c2c01c0d0030640101e00010b0b29a0392301071145100003058665400f000400c81311200300821301a0040351f00d040015408a070840d032003a04140d010070030205006244001c20064480078100f60135082c450903107030400d101c2c20504050b00003441803110b074002610a02d4030007140d40714004111400c2c009560342e405c0840d00c50303008450841c00f6195034903020502c0e0420b03000f19a19214040c0c2800741c4814030f602d1409d0000040c01d641c101c002c04220b84030045036024040d1902460711b10700641071011003401c1d078001005800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457261744 1250 457260494 457260497
    0x1d0105160b1b2701141e0706090f0c080307050307060b010e1503061806130902120a0c170706050a030c0e06120a0525030207110d081801 60
    0x811030308030303a400140d40306601a580200d200d0107503100c100c208042800070b00412034400c500401c105181e003c0c03182d085410341003814143ca01a40480f00116542140100074880401d0204030400801542050500c011004604110305000c42913417860107484159900340e07000890403003608244403030781040703c0c000c040c1076009614028090b0745103900d81c001c841005d0000d030340e2052070844690023210140c0d1a485c0040620040140c07500c46005650001d40e0003900402c0c440c29071480c417400d0342c42c10a01522001b0030780100c3c6444422400050019190200d1300300308510103120740040c08002000c2040c0c03081790300d80c002e103040a903c03001740c00c181040c22141d90b01041d0100301c426000f0040302c8580015142c0030a001c02e440c48180d403002e030031103601600101e00150b0219030807511b1003c0f034080c0b41511001e10190f2a042c16405003000f01c40c840044c511480440400703028080d900800c01035100d0025000c100c200d0000088003d900d41c0d400381e9800c3c1001601400312000c41e00b082d00411000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457262994 1250 457261744 457261747
    0x2010b0a0f1206111b030307020c0d031e0309080417010b040207080a1805130f0e060c0901030e070503030a021c0504060503130201020a062c0a080304030305071206061d0105 76
    0x40c4440c1c01c003140000b64024042070307601d1040c0c50f00601074030b04903000095603d0403200b00b50600a60290b981d03004940d440010300a020138014a07213807201c29090029015640c441a803442c100341e42c2851175061041c403052658591260b00000d01d62030250004005002a40b00f040d00c030005a14250750054171141d00c22031040040800160f00001954910310b110320b02184040d0083c0080032400e90642c2010f40c2c0507400703800741618940703960015010381ca000103041c0003404030804456952541559001c0a096090007141d40552013540320660304080c4e501140d50075a9510086811a4004090200141c0017030084075038440114041c0e6038814032625040e0300e0545051002046400b018103000300c03c124090821007960300c02c1103405a104c2d000a400c100f0390308100c15084402c032608445280c01100700415100404004c9800654180c200701994a50303030703569604500401c0f0040008040c002007203040c042001c150b11524000d4132058039116150380c1e001d6201c00f8200c0d0186c242d9030402c0b10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457264244 1250 457262994 457262999
    0x11106010b0f0c07080109080a030f0c0e0f03010b09040b090f0706050403060b06190e030d0314060405040501060807080307050c0d031d0433120c2c010602010b0a0f 72
    0x40c260860700303a4503101d209251a480e0343c80089050180650000203e51b08011036003041c801810020041038059407400c00c0071224008280081d00d5200e81d034000418861407450781d5904003d1407411642c40000c00005030441d648001a00c1c0c00000d0310180c5000200100300410510100300c3c1040e070151b80e400a03d252490700c000207000c0d2040e400000c00560700c074215080552661001ea90085541c00000c042050201000501003185001024031070302c55111411001c50280c03041d160101c440c1c03101503000b60b0303a035024000640030240044a2940d81d550f8001564082031140d04c01034140340010750740e948030900300b20746094103002603030b88200311440c103000000e50060703a160004959400420400485800058014001c4460022140c00c0d0007180030400d0350050651424115040460207000d40c07242045007061006d81070042c104071583d0014005942c905003102c00c4051003401824103036607000180c080c40fa400384c3c0608050b030745801c2503804a107000e54100c40a080c648180000c2c591 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457265494 1250 457264244 457264259
    0x7090914090d0824060403060c0c0c21060b2e08092b11011d010e07050a0e09030405150304020f1801090b0f04060f030b1b03010501030507050904090b0601110601 71
    0x1413011403e5106202e00c414030ba420398860400750b6000715081042004640984100a808000141d000722854800b042011540110b5501204500401c24082c52010034060342c5490041039003041c1c140d1700030403024001884040419054681c8901d96003c0700c0ca407030000070040d103152409416210140c0159594520440840001c0303650050040d21050023a1a140805d440114012098165550900c5a0500380b02c481d0000750412000d0340c4000c100e00c032410200c42e52100024040d02d54803100c2060104540d6406135001030b000b45008003520702d0655941c00049500c05c4004811241c07000200c1000b040d8905403c241c04202020303181282d6a40504040c888402414041c2c1401203a81e05000c1c0c250342c1b12254140c80140c4094804c1007150b858188070917403000c1728402218020f04200015a0003802801210034801f507403a0342d24110307400e20340190003419008105074100507050158100c40d6950340154048107000340b10a030302d41e06021000428500381c00c0300743e1070139a006600400014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457266744 1250 457265494 457265521
    0x91005032a09010314070801061a0703050c071e0603020a170a090203160920090409020105090418030801060c05030405121e0706090609140907090914090d08 69
    0x14152503035046441410541d200035005403a28a5040b40303100c1e001004101381d100f1600e008014580480340105e55030018242a24024001d0310071030b02503800364000c0b150048015081036031080c201542000c0e44090a00d281800a03801002070a400c81d038001c400700301c8880100003134612803905614005040d1805003111500c2d10f8032a582c504030100040f661030056200403152a8010143d855020f5610f1985192464900907000b4072440c18401c00c4420803100d00004102240c000d0f101d0401d074140d02040000c0115040684c1405002c00c100d011a0741e49100d10311240a032400382502d81442402d0080c560001600848240481401c0c00d0700814000410fa504490b003c81c0c1d8a40c0002c1501091400c246028488042c600075072260119a013102003824025100e0301d030b540941940c0d031a0b208035222141c1d0302c1008001c1d01c081c80c1b03019003802c000b20466803000f950704200b03544070f90b01e103042d03c202e0f0149111402643d4517103042c011407501c14403410040500c0380c585103c0070b0030001046802c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457267994 1250 457266744 457266763
    0x90d172110050d1a0411040c030e010510030b01092417100b010903080708090415060f0c0206030f06030a080d0b3f0109120e0f0103050c0a05130b0f040509100503 71
    0x40d1601c200041d00701b00702c50f520204800c20151081c00800200e60b00540a0400024003000c15400d00e400205040c01600d1044200e0b50030004802031640380000c414000c143c000440c01090800542c405d6503049800b22510040017400c0c1500303502d12011319054140050041c140d60682d04083c20f00320ba6a91046915055030303080441d0715a64401407405000500c2018141074001c0e00301403e80c8148410100400102d400545605040000012040b01c0c1701c9400240250720201c1480403032480c03880544010340c402c5001e4100e5001601a80fa40003443d041118042e100755103811101303074541026294039882013140314000c400c20071200131a544130400602022101d140c0c006150485074030075042040103d401140c0c89001c01c0305200300502902802100e02d008000c481030780b001d81d51203845298032498034071449500b00a0449800c42e2243d1183d151070003c1032078000003040b10700141c002400d02110135007415644c1c51500090100b00100181346d072080418554040004c0c0d140401c0170111b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457269244 1250 457267994 457268033
    0xe010518010c0e0f10111e070806061305070318080a090e0910111605160e0601020606040c170f01080d14040501030504030311160501050c090d172110050d 68
    0x3000748403e208a448280244100c4d01e14481c940981c7c00f00300c0340e0120000c40d40c03000400e031030000d926006180e50301c42080d42e1a50308688200b408500c1600d86610443e0003000e1442c001c0380801d4054546d602c00c0074504c0b0195101c0000040340d54085400c52040001810680b00c09000d500d0080c1f49592500d404001c44518240c135400746c020b5901000c0c00720390094000081c140040d49087c10305a540d6242400d846880700b120900204400b0001d40103070f0310400c2c0c16801402c2aa44034414800606080b441000034044542900d41101c0e0080d0300a034441e98102d050303130310103600d880380d4070f460302c1010b107032100900230164458015083c0e940c04035025100f00b03007408986a125450110010a0480c5010b00c2c140004124400074402e0120703000e00c2140908001d1000362200c100d021082d2040402030755101d81e041c110342d030000300c0c041064064110f504180741e040a01840700d00c1001c044100480040303d462804001c0f0b00c440080c0002c0142070180c034801c524800a136602104141311000303802 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457270494 1250 457269244 457269259
    0x3130212010b030d030e34060908060a050124030f0c0809190f0b070e0402041e0b0405030d12090803040506180102190302090f030f030a230a120e010518010c0e0f 71
    0x8444d40058000000300c92480c2071151f0301d00390f07201d44c010200c1c01140607510f0a03005400210301010014000c070350507a01a1642c2d000c004110340d040b0428051740c150703001d085c075032103003010031101d2918402c402d040c113569141c000303062034641d206604204050084216a209a42c0404040307003012281c80e40142d40060411071585502c1d40030ba80c3c00404014040d80b2500008003c50406d910015840202c40204039000f01c05807214064943c60050303025a131703050b900240c029800c60f40b0130003d035480030141041c0080c034514a40c90b03800c2140e00c21142a605688101d05002c04590307104005c2140b12a607000071414018100d0305403801d1540d00410504154007c28800c2480d980c6c1a00e04c5110302d0014201c1e8481d0b031541000c5500c1f85c000110001c003144501c0f64103c010750f020300300c00c00511580c41c0c846261841440b400d5611840c00a160309000da9038010710601101d007446800c0c01000d000b07078240300d0038103c0e1105c1c50940300f101014204012034503103600760700e449040c00003425800450398007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457271744 1250 457270494 457270543
    0x6130f06090b01060c1104061a070c1701020a0207090c020303041211070608011811030a150b0a0c061a0f010f02030d060b030601090501020a150203130212010b030d030e 74
    0xd501030003101c0c802410340c500c0309000103402c54001c05000e451500c0340d580110007074000d0040108444da24070a01c90b42d600c8450900c0d18121100004180c0c051094071412440b039101c81100070780c0044503011038040da50000704400c415404000c04401000007000a201150100c0c400945a000c003510042c1200300d51500d101c0d650b40240c0d203000c1b44a14190407036408a558590081c1819070078072401d00700140ca041c0082040c0003e0055111000b11b1425543c80c43e141c1000c600000d10784e80e0007e2514070719801000c680d075600c1400070301e1810410b41d9180404801c50905004444403011507600f10a90202c010f0314589580c0d4414074050401d0a10034501c0c1144d030402c1e400c520881095000213031600c5408104691101e0145020740300c00c0e641c105156442c1da006a99601c1e1000c806010303101c0b50300c600c0b0380500b015002140e02072401071840350040c0300c65010800800c0003100010060b51940f800382c0444c20700300041d008020f0320307180c14040741c1d80e4050555102c2d400c82c0744600f080c09820f02d26 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457272994 1250 457271744 457271753
    0x240708040e07080a050603071d06010e0d0803090714030a030c03021207051e03030702060a0b0a2c0a0b0f0607020637050a1d03390306130f 61
    0x2524020500c20250030928541054010f01140048a04118492400011524904000800384181c0d40401d04c11419241e66030b00310b0300908002040d140c1003224001a01c442c43c1c076105902004140704201b440d44909101c08024101016034000b558006607041d40d010090340c0000e851801c160701400c240e803070b004240c2800c0307003800e80c101c40e00c80340c024000808204025002031a100c00004102d0010715100342ea01080303403644415502040103038400790105000026a900c030300100b20000b408811090f0b46e460540784a5001120038050203850980104134803140e10207c1c070740c4007080500810030580d4500000c1c000b1001121110300a04d40401c943e02103403a08400c69044c140100c807900f0300000c50145001801c07100c0018044030b4030150f1241d0100c41e000d002910820a03c0c7c0d11550b005e005800d03515440380104000142c0d0503c5401d04d0103034101a00014201d5058211900d49415080c0c141f136842040c009621046c002c7d8040030070090078445040b0f130301714030540c85803410b0503030700c05801d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457274244 1250 457272994 457272997
    0x114190e06010311043b010e070e0d0b0106110c1c110604031101201203070309060c021b09060307120f0501060b0306040f0903020604080d0e03040b09010806240708 72
    0xc041d00c440340b00150101c1c01d0106d4a01c0800c0d0018030004c0b14000e07500c1070028200040c3ca1110101440c1e840c02c00611080700701400040e8024803915060710303514007840c001401c0d207036400b00580707201a20a005001456004500c0303803000d0b01e410018005190608041040803001c010342400018030a070425007082600403004003180c000811468545850341080d2b5480708501c0700b428003203070886690440750150000c0003c0c1c3d181074040640403c44070450501440e5200510520405546003481030010703040f88248008907809600504e20405050040b8001144c1030803005e00c6881c69104001541c4c0e030005800c42610295200406410180d16100300500c14070103004200c0d50a0020102e000841c040155100e9481124140000701c0a10080404c407141c2980c00340050f00010001000314a601b00248040c01c60410000341001e07000c95550304580090b08a01680440007820700b003250380c80f80342d05410000880d038410030004070480048000241c04490001c440340031490805004803c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457275494 1250 457274244 457274261
    0x1305060f040f020a020c1e09130203060901050402090105061e1308070b0304172d0910120c0906020604060902060706050408030a0e1b0f040e070303080114190e060103 73
    0x1401031049110340b41625020350070a00e150341c014801c116a0b10340728603040400c02c82070a0640644500e243ca02030a1240710000102040e010b14107980240c00162000c1112920402c1d4035000080c9905281c41007000b801c1069021600c1800305010300c04180841d01c001e00030700c140f50380f1f129a84134803141c1c5010485c1255800031005005000700000d002405500442c4241e21800c13610316904144220085980228814004882131180e207041c544400b14901100082000c8105418103d1150003c1d030810384901e4103070005120b000c01d600d20074000740074a45050a40b400c102c4181400d100c0025582d5600400181c84191128080d1095464100c1100e1402e608990180320900e09800c1c0044241d10a075072200c10185814011040482c0100700100304041d01032541c3d40700c404550401012340c0582c444079904c2a80e444100c68108402c026420046200e07171900c003019071400c0e114074442e0394204426800f51201e00c20b0404c00240741d4580c3e2007954001d5400e0b2816488603c012030003061903c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457276744 1250 457275494 457275499
    0xa0e03070314060106080a02070f030315080d020106060219030e0112020d1104180506030606060c0c040204170f1501092a02011506050f090609150d09020109141305060f 74
    0x341441c2c26120000c1511030581d652030301c1c2c0981e6a01e1f071802910072482280c10141200500d400e160300024400d030010800c52016000f0008400d403108003160a00000114003c0580c0d518031041151030f8051100c41242508520004019140e980780035040320441e5404c14100306020205070030f41c08040e8160703004880b80350000c0009004420008d089540580111040b840d0000581d00422406021705841001c01402400c20b40d01c904051101c140c100c0003400f0310178010409074041a8440c1c0c4003400043c040007003045000341c1d0501c141c908141c160b52511300e507504000101c04080341e04081a03070460b1220b03940050f0700c03010005651414148240d491405400b6000781c0303050180d054000e4041f18104602c031440e881d039602d80a9a5911454a000c12a418284a50401458004064800c1d040003410f460101c841130140c0003003582c040004032003040d650f280e105055581c00195a0013501400409492002c4807000185032524440c04c1404034075107810001d005505c0b507003400e040b0700002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457277994 1250 457276744 457276763
    0x30c05071b0608062d0409140604020f06040b0f160b070f0305010603060602070302210706050309070506030106050711120f030316092103020a08160c08030307050a0e030703 76
    0x2012072082a4160501c105800201c02c480031800380d10f8269502605216074596040c03410011030305490002c070034820801c1d409651503c0f000e000c5852102250445078410380900b0f05864607104001f00c0c1c1d008a0615405400c00f4042031143d0fa00ca8001c45000d20100e0101c0d80e10b507600e000403148425580c40303000b403103482050f0a00c03c10315001000100c24041715201401a40c0e20f80008074102c41c3e041c410b00300103034801c000401c0541010a00d603071403170030704810103800709012003034103480d10f000369009100040e03000003003080100c4140071900c05800212080f030310b11b5160010081c00c60089440107841c090307000700c1580c0c0760358075110103901c069071a0081d100c06c0c0c0c00381c401c11503e07904111008106003024010240e003191160703588100750360810742100013005158816141c2141405002c805500c02c00242c0ca01050360000900002c403150801d00c0320580c40d078605103444c00740c20b5001e2010b5038028014040e0094102c81a1642c044052030244010398100c00000d10300603490348081d0000701d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457279244 1250 457277994 457278023
    0x8030d0e0d020102130e042d230a14120a091e14040f0e06090d020114130b040305040f1202010e1008060d1113060812030412050c030d0606030f0b01030902030607030c0507 75
    0x5c2e0f6800042415020700c086041c127020b03401400b0072a0300000310801058001c1d01c40e8000040d12144002505a0010212414140b0805a42600c0c0d8000c000c0640030502036401000308805050b94001c030402401104c0c00840d2038160036602d284c1840950921903500c0d110000c21807902540310340000c000000888501e42000e901040e1145070a9151400550812007046c90f40440807c0d614040d20607003d4501e40118a611400b40d031001c040c000318100310040200050000301c032409080034041d101c0841405608500c005402c519050a44030300903107048004141762a0440926540600d00382c1c1c0c1c400c1d40821514209024000c800d58465014080c40d1010201d03406960081050300c00c45003c4541c20280440c0401071404100c41c000c1c0361000811006444030f115101420020744010200ca00f000e4620030418180c0b2525001680000e5031101c022038001050300902d400c0d0a000e007401c110700703402034011075100c842c000c148805041c0c680c0305461085c0d00c590210f035031035038020090b140120f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457280494 1250 457279244 457279313
    0x4060207150509100909140f070e18040b01091a1318150501030501050711031602010e13050a06050105040506070816080408010603031d0108040f0c08030d0e0d020102130e04 76
    0xc05e107002c0c00300704510b46600b03941c0c0c3c0ca4420001303500035040000042055501c000d0b048510700341035825690001e05008407072070502006150300d4020b5214074203500b06503045c84101c0084400071240700b14a60248080d40701d060311281c81168101da0100408078604c0b0410144030306891b031051005103c4007480e982070540d682c08ea40a503040e24032481c007d10894480c044121050b030b40344000070803550400c02211a46c1d84965114006051042c1400c140701829080000d0925031501c036070418680c0c48404100400000b03103d20300c09050242442414541080045492030040090080100e50005240d2884c604104030720000507a0145c0000d40c0e072a150118203002c0c02d11440210f021800b025000c1542045400c0016100881030b07403031000b030b9074070742d114130743d10196140060300c004000080c0481d81e120180001e040e40b2013003401c003042c40c0d00380c03d250360b24100c1002101c03000c6901c14424020122045610003003113807026000f40c800d0b0380755030900300c040000c417414512058444003240600103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 457281744 1250 457280494 457280507
    0x102040312111b03120d0915050c070b0423100b0f010e1011030a0302040617090a03050a030b040606031b2d140a02210406020715050910 60
    0x26803080c0010391036a0104001581c10342e0050320004226004041d508842d030040b880c01d500e0b601801821180b0614414100403810344c08440b00c640001d0721005100b061008024002c80c4503e642d410400551400410300c182d03038002c0780401082c40180e072002c2814000c0703502601d0301e05901654035011400c144c00c0000d503140e120190310b144080c10084e02c108079142190006071020410f0b1502d00c000d448580411450050350031908091020703045a1682c60750041000c3d00c2d040704035440050f640c50500c040035000c040da0031441c10b5107648013010094201008200100301035407605209032184c00d416001d401910a0071705080d0060314200001a11542c95004690781402d800c1d000341100b0000c450407101c03094890320754907420305a48402a810001004a251a4403944c5084240b1441503c606e40c1e0070340c0001944001603100d4007000580003e08020008030940600c40c03145414501100a9102c1035144200180f210443c03210381880d0780178208580400710300a081c40d0b000c03e107a142c050010f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 457282994 1250 457281744 457281749
    0x90b010f15080f010302151e2203020f040506210105010f050108090a020112090212060901051f05010810180c140a05040506030c07020307030528030f0804060617010204 74
    0x70050503400c8544072806055200c0c02481801d920b00c0c000d83c03c0d0b400f40000007000003240321041900304000300f41c0d200000c181e000e240b50452003081d0790f2944040420010315030342080320a0300d01144001c00041e0390b07403840d0455912040d240403502c3c3c1d840400244940006800d0700c803e0100c20b4580c0c84001d68107512881c141e50840e0380d0311a0803034a44c0011242e840040f6640303003540d071044c0c0c91080950f0080011400c0c07030700000c801281c0d0400d075030f022501d2034502c012030741a554401e4060219040c428060140c2c405811440f110b2000e0f161110700924107014410981070108400110309420310031110030f0041c01071180f516400c400740d401004014020403401200203032b075a00d00da00104540314211050840540c2d070361400e160402c001c205840c5e0000d00140140f003010000580103032802e00c41c120045001d2005024404000b00c0340e1003004a150f0079001440f0a0a414440005c0d000741d42d96000366194a0621342c95611031520340001e00c0540c03c200c0042452804140404a054004205 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 457284244 1250 457282994 457283009
    0x902030406180803130c0f14040b012a0204092f0919020c03040801150f050a0b04210206130305071d1305190c0608060a0609060f0201090b010f 63
    0xc480d8002c0204401480d0381400078080541080131600800700c411050348418014030103004015680c40001c02c0302120380d801000c400c0d8800000c0c410910f130a1003003400d5064203080c0291220b5000502d401c007001c018180b00708101c0d070002d01130b040d500c0e82d40c4503102d85a44042e0610132840c43d80a410803411400c660200a2070950045603828200048005e01401b0849207400c803603031840380c003000a5040400090078503c014000001e0f185400d004c0c0b0040e401c1c800b8480d45803a803d00203c94000e41080e0020750180c640b80300100003604946046400302c40040d80c96220743e102120b1801916000c00d14041d41c0310901144507205560f10402d042d045a10a808580b00140d0b249958015429000c0a900c04080341d01c001034001c9a0500448103098814810786100c200881140d40556407881d0050780d0300e0000580a100c881d8003e003510750466001c0300c0400d40d01c0d1a00e54000d1200c861030240e0410021642c0312184a58000d40110b03681a42c031181243c025030b180c01c4221102d244521074900e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 457285494 1250 457284244 457284251
    0x2d010c0507180912090e150d0b04030f110c13020a1809050603150907090506030304030606030804090c030b0901060513081203061c050a020f181303030c030b01080f0a14010902030406 80
    0x24404ca000d0720018017160305200d800843da41d680e2124407441288150384a4205000c4106600045c62a0740c401d840360740f10b91102c2c00340c2c0648402c028a02d54411b00347e411583c0c01100c06621302d640342d000c1510004503d041c0503958481c80c05d03003140c1d40b00300c5c0a05004203170000c09010400200b1900514401c080c16403c031902d5905c1c0034111b82603550181c82c00c903580c0e0070100b01400048a580c0045502c0b03880034003280e10703180c0d4a5840e24110390359503109881407480400c0500400d000c03405220204c0015150078400e495041e00010202c00c0188588001d00030002403006e811506010b014005000d03100035201e03104d503000c0d61444035900072a442c1c1c1c4558032110303003903500f104850b2580302c400307401100418010455509000c02c2c0d851240c0b005030700c802603081819401147c6401c3d10712580d4003e200350b8101a2a05d0050142e6586030259020306090440c2000e181c0d0340401d05503800300b41c2032a010300075154030070705000410b40303031b003104407401c0114001181c240a590001c5000d24440c60041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 457286744 1250 457285494 457285523
    0x10c0e011b0b06040b06070c0302030618030a08060307050d080301090609050103120305071403150f0907020c04021b03030403021b0f0109090902040b03070807052d010c05071809 78
    0x441e04002080500303103001615a01c0c000115010326202d070340c05000030307000144218402e8006242a048860308464040e0008000d0085060500c03d2a422070000341c0c035141d81c5d06030074000395102e014000c01641005489c100040032550100030303041c02000d021740001c5107942c650400c1c4010b54404d0049441c024103000c00008c8003c018425941201d40041100940b00c00c440411000351001904c06800c0110008415605040503030003103015405420702030b0341c000580b03000e00030210391120030b0318420030000d410041c94a4000c1125224104101c0d2700580c2d81c00c8203200361305a464001070207601741c0300202c20030040580000d900780e80c050110a51260741183c02c02000700d82840d4001041c00a40c1c180340812071030125412107408280300500100762400b03c940868a05030059101e1400759010340320812960400c3c00b250454075001c0060385040c044002c00608012064044060401c07021450400138041d044c0190400741c000b06444405680c802d003504030142c00c41c908241ca840c07520440c40e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 457287994 1250 457286744 457286747
    0x13141e03180604061b0f1e0629040903020f03070317010f03020105070303050a0f0905030d11030103110f01051b010f0e011e051e04050d08010f0b03010b0304060609020a02010c0e01 79
    0x1039404445040c0d4039a00f20080807504d11400c2e22125404451701c0b01c03e40343d03140004269400d00840c4401d40fa11002158245007494420380c0d0b020784400c0071003041540401041255070072703031143c044416200440c090304140740480c031303111045189102d07500012030602e0805512007610b040340740c400f0a030401a0b90302c4200381ca54010207840002d002c107004002960000c0e01940190354402c00e080c2002680c6105403120700e00759a1034000c2207806800c0025602c401030001c2c4900c00c241060181d07042c3c155815543da4101e00d40224a96904c101d800c40c4c100e009582c071400c1210602050388107070a01c0800ca08030418040c2031000040c225050409030164004101441402e50f603c0c0345018a0b49a6824084032000501d4040d080303141803504040e180010401c03e0000a000340e1150008000000030310700010301503c01a04403507040c1100301c0080016041e000166415111141f1841396203495525000d40101420b50000e81e005001050070401250191f015122545158460403000d5080800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 457289244 1250 457287994 457287997
    0x303020106081516260108161a0315060d0c0801090e030307110f010c05071407050105040b0a030204090c1115070c0f0204090507030c080106080613141e031806 70
    0x2640f03040500c5190000b485003074450120a0740031514100300080310100c019010040d9103020380c400c0441000e1004101610341045201160b00c825070201d00c80600b00f080c00c820200b2070900c551010140440819114005181c0b03451403540001c1000c2e076030b5480203031000042e1101d80ca107800450070041c00003a5182ca80e009600341f484148001d149140e44028065580d8076692201082030300c03452855102c00b00c800d100320300e10012241c40d60f5840c0e01183c03034100d940140c4034021500d00c0e0418101002582d0308401910280c640316000750707031a0803c19004400a02466001090260a00c0345132080c0a4000c007500002c1d40b43c0b107096880428200e002c2c0c400c82d980c265006000200d03501b04440205030050304030420741344010404600011a0745481c0e00d420320a03002910002c45000040141047c02d22440005200e0b41c00500454506010380280e210400308028080c4a5045800034060401b4003c0d55009200e0221000d2802006440640d40c1d402c40100c400003a002c1f0860303a0390078900f400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 457290494 1250 457289244 457289263
    0x110603040b0f011a040e180601140f0418080f0c030706060501030e0105100521010606051315050702040207020418060e071403060412170a09200f06090d140601030302010608 76
    0x400704e403904e45019050400d10324014101030019074a0810b0b1700c4155024402540282082c3c0308840c1c05a14030000c00030034044000c074140c41185490304980000b1010620041c1064000e18030a07110740d900e44c2c45201d00c0c0704000162015000001d060700410165030300040070764100780e0b4100002c420048036075088550a8950300c4841c0181d410800c420300e00114018401401082c02007455070814000c242500c181f600b0010105c0e00200d400c002840103e042100101100c801d83d01c082c5441c000081c22510444030041e00460f00090a481035489a402c0710b1100f141032500f540203444141004001411a210080a1409508270004405003082030079001d034a0020b01420720341c1c0301c2d603440328918045495030800b8444550300755101c1070341c6100c103680304941108010a10909034500040104448040d5441d038992801d485e400c1c0f5140c1030185605404182d03440d41d43e0f40701d0300c1d0005a20255990000b006a0090540c0c0150701e070011604074102ca210750000d201c1d85031518a4070b9102c4c07a206 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457291744 1250 457290494 457290539
    0xf140a0213050907020c030615030d08040b06040522030f030f14060405070e03070303020307030305070815011211210109051b090d02060a0314010e01150804110603040b0f01 76
    0x41c401800240b40400030250011110f004648064810002082c140031f8200c50340c0502040b1290050001e08040c48000318404107490320032068074050f5229410750001a00d000e004e06d946400203695440e00001c105003203103402c031000c140c4088600d002001d000401c04d0000c006418280918291004d40c000c0c0c014010100030f800d01c9943d2110140402810002c4c900f00800040306255070aa880c00c1c004c0c41c000d540254090340e034841150401405031030f400703021034003000030820400080e24294025410051001d04c3d04d00510310013034819074040e00e42d2021150036a00b00003241ca4070311007000b03880031180c80000c101020343da0784c400400080b200c045034041701e1002c0c400b003409007648000d801040403070300041c030340810108240c01051044c1c2003c54203034003099480e2040000c105410b0006401080e10700500b44240d0304090040440000151702041030050510106080264002c500829200042c104035100d19040c2002c07440da032800c1e01d42000d5180c16000214008000500c00142100f04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 457292994 1250 457291744 457291777
    0x4150f05010503062403070212130e0702070305060a06030501110403030e1314011d0a0b0321041203020a02010f0201060f271e0c21020a120f140a02 65
    0x500c001900c441c0d2004003201c2d0700010300000b5002005160856584100d40424000e0300e82c58803140c06403820540849205018006000d1000744400d4240c858040e00c40500c44e2401513202c2e003000343d1400c02d0340d40000704240940ea04005110a0740e90007041201d01807802480040161107580f080740c4101c0c04050000303401005440710303d00300498140e0f990440d900000595150740225103c0450302a0442c141209001c0d581c0c5400300d050b91091500014a1b040400c50201207400290341c03000b9070104161804a550300a840c0f200c0304a095134010301d145000e01e40040c48900d0000d41364240400103c2c007140780300c60a6645244141b003080140d608402c0c0c80358403a070030108a0f003900c18541d10b0202d0100038680c1d0409541c01c1900450100d10401750360b41901d6404010140d080e81e2071202418200700e00a880b00000c1e24901e540d489401c41103000042c0c0d500030040e41215209034543e401c00c640c80c104608202c41d00d40700e600c4a40040724160000d100740c0c44010407641644200207113040c0b0b81c003a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 457294244 1250 457292994 457292999
    0xe04050304050f011403070309020f040227041d0d080f10091805100e0d02010b091501110d050d0b0a0501050a0806190e01053a03020a020a031104150f 66
    0x10309440f200e0038a101410518035030b503d1095410381541c0200c40344000242c60304a19411170500c03e000c1d818030241140e003075080c690f50510549110f04500303d440d510450030402203c2940380c540c01040381d86402100030302000c485240d256a030349201014080050b080400145d05d840703104241307902402d010b44074500914503180e50341000e0031642140c600000c03031075031035280041d008120b591190455101c0204400c241030701e105007000902d1000c0d1080d039040141241e0659070314070980340e00c07415141c0461740303080342c03080125003401304442c0340807440c03081041c807001e85e1303403c10064460300050040134003160001c0002c3c400154018820300b8003041051150209079405081441c4e817001000e0001d10024541c00a40c6640e0146a40150100140400188101c5c10600809503246881c08400f0100208c100090a210b000d100320801c18180c00401e5082090310a2154060558000b070074060100e449050a012281b2034203981c3d441649005c0c1c0b0200280c003004402c504035007140c0b04110a092 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 457295494 1250 457294244 457294249
    0x4060206070c0213051f06030203090a0209130c06021506010f0c0f060e060115090803031b0a02030408122703030f0c0709060806040c06080c0403020f0d0221070e0405030405 76
    0x400b40700201d1344002071145020305122584181c07403040030509081082c282e04d00340fa0031051000d940000e02050300400c1000115840000c110b40301650645810071030b43d80c0c600c401c1d0079018101900416145500d540001c0081e03001800a10701000e9036040c40c016110f6000640c0c5c040140003001d800305503040184404a420400c0c20340c40b4a00a000225190781040400d60406100b604a86103200c950140b9014281c7d1100c0100080c00310b103001140f46040000f0410307500ba501c6074011203a01400203104540714400d10584004250340001c0716201d40f49801d8a0703140d5084846194424520b185060500c0482446415080d44014018524010b000500040b1a074401a2008001c1c030900c200050014050311424000b01410405000b550409140c0401005850340c004410000c50400348100354170f49200311000c42e82d04540020683c40c981000c0b41000d04804406503003c4200100c0c0e080ca40703842d22007010b40307540c070409561503152100000c400b80a0b081e10068000c1e44280001d21450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 457296744 1250 457295494 457295507
    0xb030402011b051603050609070801060e061212040923040b1609180c110d12090c0b163f0908120c0705040b09040b0606090604091b050406020607 64
    0x280a0000c0e40c00640d500408150310304404d900884187e80250700b00040c4c0a814132a00d0041d10b84c141c0240314803450f210818401c2800601854401c045210303076022100b00c100300c180b400e0511143c011b0340710b95031194010f0007001d01c0b07040708407060103103001e442940b00c0c070f41880fa04c11765108a41191035107c080045600b200040040740a00c1668040480c801d412000140c1d58100340e16408140000c40c000000c0c2159003100d80c4a18070703441002c144614940010415850850860b4001001020340c101010b14a1440d0f11050400e10300084030706c1d048804000c2c5003005402040044540d02c064850480103401c400c401e515000342e140d106e15468060302d1a00e1541041e58a4001001601c98140601309078100d07000004543c00094600701070f07402070029100030802140c0820020055601103501c42d40c00070070040000740f80a0000700c2a556810550704c1601d0003401050322144c466401c07900624510782e00701400900c2c64a903ca076903110310b045130700b5901581d01030030590b00c881c841136444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 457297994 1250 457296744 457296797
    0x40b01110303281e0c0c0b0103030c0510020f0706060e19051b0a02070e0c09060d0e0a0519020102010b0d0f020d080903010228020f0c060703050906040b040f0b03040201 74
    0x80c4150202100414000c1d0241e500130042c40d4020042d140c41507101803049424840d90703181030014030080003000c1500b200a0300d0450b40c00d0b041072381c500d00d11031504505004000000300d010b00e102083c7d0030788000c1144080c00c00c0c240300d420f040012130344603240d480c410030f42155410341000002441a050031080d80100e40c01c14041c60000003500b901d11a4846190032245c4000010391041c0342c10888003101109098000039900141450420540d020400511442d1851154036031952181d4040380d03000c000c0400c90f50f400c0f20607111005105c0f0300c000080143c024040e4019800e11443e1071070b51030a20340c21040e6540c825403101e090001030703090007102000000240c405c0002400307a80150784bc00c1c001040c0203809400462224851103000c240e00c0e00384010100f00710350140c01d01c14041ea400244411402200300c62013500c0c0c0350a0710b0300710780b40e2144121094004d2004140011a4141c2032701030b10079030354903032501d06030240c940d502128180421100a03001480140714001c8042c20f4074040d141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 457299244 1250 457297994 457298041
    0x303180f030706140a09030e01030e19030302031b13050d0203100e010b0a080a030c0209060d080c01051005060f04060f0306050414040b060f030c06030a0204030c090902040b01110303 80
    0x4200412005140c1076801107401503502d41c0d00c0e4140b5081d1041c0c0e194071550b0041181c0802c0001c00c603651002420a8103045142c0d041c156036121181e510f00c400c0086040ca254440003a04d012201460000c010350401d5507454210307030410710f600c04000c03201c81c01d980d0b07480d41c0f0200040903140713000100311000364044401d0b6058016400f203030814000c43d00401d8680c80c0c0d8a4008100d082c07800c3c040c0060340040b0340c04403040740c0043d19400000303030340640c8d12502d00b03030121504005a140d402c009a0354008000004054141c00106100c3d07854064104511910401d2511400c10740d5400a0000074402c42c1c4900080c00c00410040c03003091f00511a10203881894900025641c1c0c81d000031070119040040000180303610f04c1e00700800c02204021460b408403042d654040e80d49149400300307a03103a0058800900c1018044000b400d9804031703506990003140c100612904155441d04030000a11480700c050f40500d0800030955a40e500442e02c0d0014200518021441c640c3c921500d0341a001d009100d201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 457300494 1250 457299244 457299253
    0xa110a140310200d060e0c03070804121b11041b1e020a1406063a08120403110606060403170702130609060e0a0e070605031801052e08030318 62
    0x80c1e40c41000084d00d15a00149000100d890501d4010502180700a007191745d111010010000b85c160322080e1950031680c40041507040e4940c3c0070081d035414016103460051031202105090500038004880f0489800c148c5042000045d2a0940300c02550b003854040701041354140c12170b80d999000d0348404d48184245c0b041d81d55140b1243d6a20549a8480700c54403000d80c0300400303110301c61522001c03038906602401d0b480b0600c003c55000f0950020540100c0300100400203c01c802030089050885400000306030700d40041d89040e24010b80004c07941c025800041c4542e00c001156410400e04a80a6076000700645103500a55800351400f07901ca14001c90f0040741180340c5008149a43c002c0d80c2c05000d808101017107083c10000f1004003840001c000720b01907800c2080b04c0100040c0400c0769020f440716807074015034982d030f5608000c0ea26002c003031519050750318000070080100b803606102103900644000301d00d10308943c1402c0e00c050003a940241c1c0580d4000f0400300ba0410003080016001451040030b66 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 457301744 1250 457300494 457300541
    0x60105030901140112030f0201050712090c0506210703090807290702030306011101090f0605060109030c08030d0c0f090608060a08061003021c05060a0b120a110a140310 74
    0x1e0b00a10281c0c13020b80680c174610401c804042e0051145504104a80700821903450a020010120300344140c1411003290b9440c010000d0041d1580c04402500001d054190f480d40d08106100ca8205070710707220069404860007007240e0511034041c00d2080303500304982d40c0c00d112203031700ca10316440d45e16112031503080641404000a10700d0812080c0c07180d00745401440d00d80c54080f0001d05803600b84034041015915007003040740000c110400c0c3d0115150804000185076942c1c00050742c0c22000c5410290441c80045400203030307403a00200404160103140d4040c004501c10007400d81d030f003e44090b100700200e16020002d10060780304031601d42d4071040c028201d601ca0703941c888a06041c51001c2e1064401c0740000b100910940c2407140c0d801c10344849a51082892580b075888558403000e01400d105025921017401d0740d629990b082454204185000984807150f130b0700e1a21103081001920141e024070800d280c0050000018091100d0201c0060045c012800c540d410481c01422070101c400072002c250802d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 457302994 1250 457301744 457301771
    0xb13031a0f1008060c030606070c08010204050a06080606030a050601030b04090302060f0108030a140d060504020d0218040b0a05060d020c0a05100f05010b0a1d04110d140c03060105030901 82
    0x28034503000000a4029420308100c00c80c12180c040003030000c040c02c08645010030580f50000b030400d42c0859201c20b484d0f00c0b5103a8600144051240078000b40691900540100e8020810b50041084a800b1142c0d40103070340d910700303027a510990102e03040c51340300030240000740310802c0641002d984408140740001e09034859400040403125a26000c0c0e00680c00315081148685070040440e000d0a01040218284080b0f101c0042001c1607402d40159280d0000c034806017080a030742c0005024100080c800e42d250006014140300a40041c1c440342c0d661400351000004c541028400e0440c200c40192080800600384000d005166001c0140b1140c8103500300003040700d4407014007500b84054842e4002d80001854008000182d5280d510351004081c5003e0040004c00501000c442c40c1c410241000070300c8424080040454a03000b129681d003190600b800e070450940141d005003c9804d81c500e0400c001c640c0c1c04616000c0c01401c9071846031851080012036103e40c01074014580c00340320b00e400401c55003103034080c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 457304244 1250 457302994 457303013
    0x1501050319060902090312070210270b0c0d0c021518040c0302030402090c04050d0b0402120d020102030105030d02011a09100305010f0b040b0108132d08130510090b1303 74
    0x3008060f80d9010a000f00c4510302404808042c0020f4403225007807544a8000800348401400070400344100b10840042c0e030110308012507040030914040001040c1d58584101c000d50100a0341d821030300031210746c018003d000c1d070b01202d0515005004045030700450f401040f0103a0103c0a031801c2e0b40d441c8007000c4600d946a01034000c0c0301815990240c0c4070704050ac103000006201900352070000c0028031060003a138452585000046412020840e034548460000c90243d0000f4100c5640030b029280c620640c543d015001075048034016021203d8400a0320b4040b422500107009400054203c1884042d0f14030b000080607400550780711300711500355500c1c0c0d1007070700710f030700b1809442d207c1505c40084c00f4642c607007403041141c0381400b8200300c011443d01081c1820b8502c030000004003c030f45510050402d40c006002c3c02c1c601c03026410201c1d11002568200000c0e20b4100449002e00c000300d507040868507041c6030301c9004185074107886070454141800b0b403140341500480700c90120640c0c00400000456070504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 457305494 1250 457304244 457304249
    0xa0c0e030a05160b0418110c031306120603080301050607030201020405060d061d010321030204091805010f02090a06050a0212030c070203010605030c0d030c050c0a1e0806150105031906 81
    0x10040090f81680707a052001403e40d80d0054070251420300c810854003100ea200c00c40e03030300f510980004164141d084500814015816a4103040c403002c1800744441e80300707410708404da44290b200d4800050040070300302c060342e8550000805030b5605200420407420040040e0216a10a00002d4201503d4001081c80b503041080490072481c0c035403030100402107141c41c021990400d2401164025811616044e03000c070031071441e151900003e20b801c1c580d950b02c00c1c2d0555000c2c0c00280d40500201120003856220304403883c0003603c99501e407001e4024212214800c40e946aa80980040d520a14103101524160060b200b2034042d40103a01c0c00551700c503000c40c0103500c6240303040004e07910754000340141401c640031a000325020b40d008001c0034100b903641c4949545484e80c507103080e1050b80d01b1442e10310304013030125a1031034106808038004542d01e07080d0080c01d44194424450490700310b503500080d951b01c020079601c0400b5180c6509400e1040e5100d03200855210786d0200c041006e0501c411081011201103a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 457306744 1250 457305494 457305503
    0xa1803061b08070f050306100315060f080f100314010204030606091b0306030c09110903010c08071e09051e0306071d03070e0c0a0c0f050313060807080a0c0e030a 71
    0x40c0c4070100300d03500411640c0d0024540e1610b440e01140b050f10140c1188800b811591065010404181440740300307411550b0104c001042d104000c84d07490711301400e420030060603480461440d50009241004819140744210050f499402b40b4501d1522130041d08603201c22a15250b54003003101002040c59806118001e042009000982d003801c52050360b4600c5299072940c0400d804d0050410115600d42c14407002c0e220b01c2e400001c2c2c48000b0403c0c0080d644625a9403542550030142d01c0060f40c0d8000b0503a0388110401d03181c05445d8010300c3d203c412481000408032021400046041c03006040600326204095014056040d16402c5000064640f034800c4400000142103608145d0781d10f01c0d8041e9000300c41c4c41c1600100581030a240d5013102c02e60004244020081c004644111098800c0c501d40c0d40558010062101c00c0601b42842e80c0c40750301c01005410f03040b03441c40002400034402c0c44900c0c82640107035074001080c1c50b20200322028080307200415041002d443d40401d1300390f50521405610074441c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 457307994 1250 457306744 457306781
    0xc100506120f0a0b09010e071401030e01090f020a050603071e030617072619020609090c041d04020603060d14030c03040f090509030d090515090318150a180306 70
    0x2c40c5480c0f44c440781c00404409950f41041c43c00303060b15000240000c10f5502c844203040c540e00070400100c1c01005001c040c00120360818150a007444040700e1008102e80c0248caa041450381c4540900444d0310013910140c0028001c0e41c101e207854040c8550b0b0805001e4a0f260200b08155100440e1281c14031000b8601c0b0250010242003200081450028050710015900b00000740c0c032241c02184c031004245030340c0903103241c030740100021940e406086030f4008000410301210390400b1243c1825681142c05206500024401b2080010199000c014071940d40207006034950340e0364200b448252104111b048a03c152500044a5040c40a201420500b03224a00560311030b4600744440c02101444d6100550302d41c5080148078060070301208603141e070500b0800220b504407c514040f46400e40e15800c518111358400180820030070040020501e070001031404203680f1415a00f0829800d45441d8107011524042001c0c100f501d014a6180b40c01c0c04c00c0000c0c0000c1681e60ba119a070584066140d42900e0340345 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 457309244 1250 457307994 457308013
    0x1080606010e01020d09120c15050d0c0c0b060118050411090a0f050102030f0a090509070c03020f060f150a0801050a0902090c07121d03010c09050a0b0c100506120f 72
    0x2c1c018000241440300344020a076003a441c503809040b0036468003501d44500302640403c018403020805101c02000443c2d201c0951240800004100d600310f408030032800b030304002031141c10343d03c078000800019400042c85e9a0580f6007800554a5200c8002001074014040000052503aa940b150919805507004691782d40c0c80008100a0f00d041950400a440c244010040c00301d41d0380041a00da124021200d8169640042101650b084015a1201381e101503010100211183e010703e1216070b1074031035000c4400c1200c0410340720380c60340e004481090b144200c00340012944c240d054140c0c034010801604000e4841c1d00e0314045800d5130801c44080d155103458101003000c504007400c4940c4e000e040010240d060500c00e60341c0d10f5106c01c040c09c51804005100e40042020140901d540f12004030040c003c102030521180c01900d2404107100c0d0300d01c107a414201c002403800c2443d040781c8034442c004c00030b0009078101411250081c03401030142504240300c0004003c0d030080030000400f1f121103100041c1a20380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 457310494 1250 457309244 457309247
    0xe0106061412010b07081902031201060f0f030c05070827030d0509040c090803070606090b0607030e04090503040b04140301290904050f010f0509010f020702150904020f030108060601 80
    0x40a980e00150001e01c10400c0011601100e01070505440c82200c446a0b21112070030b04170710501070290f46c4082c4c1c0404140181070180c00000401003900c450b03803071030701503aa03444094580c624400e15513000b18401e02d0042c3d620764032a0344007001c111032604003103060640c562036800e150b40142c04400c020780c0540c40202c000c6d40b0104100c48407420700300c00405124a6051004105d0701170048440d0241d0340b2030845541c0a8040c0ca1000054134160003100d03210446410080e02401092141c4050145400081da0190401c0c4007101d503800c4d0103844180b0501e008409100c000c0007100d070140c03030350b00090002241c1890148014001080c0d4801100f80701844074082500310784038411040020412108800a03010b240007041054003011a500b140c1aa180c3c14100e080c00381c26008441030b03510349041c1d2002c50f0441c0c0c1c00a4061034443c40200b10100840640e8000ca100702e400c0a54043d00f11603a607a8401446402020303000e5020300054140f80b480c0d034415016410a81103442c054024008101d683d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 457311744 1250 457310494 457310507
    0x7120e030c0f060415120e01110708070f02060703020a0b1f170c22050601030207021c060b03030a0c0611030601140d0b030709050f0f0f01170102091c0b071103030a1e0e010606 77
    0x519000082000e000154002c440c0f4ac03040d02e50040c4600740209080007030264070450b41c41425009484681e1710b08903440c0c025203a10b280d000440d0485064800b0820440390f070300003100c80d0512805280701d1031307051000800d5642084041900113108020700c0310030940b6181e02040c90410b01c0b00701c2104c9140440e5407042503c8000700494100342c8103001d0b00340585c0e41d03200c840e043d03100350789840d10025540e0300f0000007074504524940c0d0103100000b110050140d0150100704d0a40c0642c10405c00b607024107170414030502c41511201d00145000034148541840c00d40102195904088006003001860020030f0410190307511030301c19503a4403030410000d180001a135680c07084803d0b452030b18528020948110360030301802042c1c1c0300b80c955894812007039002d41c11501b2103080186280780d000c004008811800049603000c50740f03402003d000c0391985001d150540030030304241c00a141190703240c100b44001450207002c14000000083c2c090724080015100316640b502e080d000210780b060912802070603c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 457312994 1250 457311744 457311761
    0x50c09090c0a030204020a1b0c080d0302070506271203040b090c13020f0f0706270510091505180f150109050a1d0307120e030c0f06041512 61
    0x16801c412001c0100340e9840040c0016650b0440d001a20b0302e8020308215216010742610502d400321a103048800e0000745001c51003100c8645085035205028198201d05038003440c68014290b5109102181124085c1d04401f05164990280340c00860741000209140c5804904200c1441ca4001305100a2200d02c6c140c050344900288018551605a10003081405401081e1070141e964042040164610200225680017081c442415141c0426041490080050341410b507040854040d070400b0750030505200e00703c0b16802c107000d81451074000b054000503102e03d88040342c0200d0164103045040340288603050250203001d0f5000d07103102d42070f21403910b0503010300506111980991003460f402401c208a99054940400c0c0c0420103860700c00f14030001d8400780440240c1e00021100500003c44008043c00c002c90040e2203c1c18070758031500040ea102c0341c02500c040d4140d044400c86c9092400c3c140c031140c803481d2000d0b0056292907500c031066204040c91904010000e0208100c101c442c14850060307000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 457314244 1250 457312994 457313011
    0x3070f110307050a140907180305100b010c0308010b1303080c030307030501060915030b03100212040302070504050c04030b060d02040c0e030705190608070212070c1d060306010b25050c09 82
    0x4114244a48020140340c017043c0c045c4215140030000c6c1000d4810703059807400000f01c05036441c14a8492800546561182000c4007900d8500440302c03940b0b40c421000c4848461701602d602c80f4076420200110b90545c0040c00f416000c4461500010000750900c00a040134107038840a03507201e04103008000c0944da03040e48004200300200009128200f00300c0f111106130100d500300041d001010302e001c6401c02039941044100c0610106444034151035808585108901c02e41c262000c1e5a215010441100c0b002d68408400742803e12050001481024001c3d40001008100c50f01d100c1075940041c0580701d1100d15078002505680000265040800081c80a028115540c00b031a0303140d01d2007c1ca401c0d441d849503600704019080890102402400090554240c20003529910040d505050002c42040c3c4544007040e81440d64091702c81c1491810207000e948010702410250b4a0f0185900b00e640240c01903c4003511203006910907408190700030082c0510440140a543c00303040b04001c0e80f8030b070090001e03a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 457315494 1250 457314244 457314259
    0x90509040c1701090510021806070606060818070303030f02120109061401030905060426031e0c13060e15031014030f0c150712031e0225020303070f11030705 69
    0x400114045a40106c4141c085030068480001c1828080c00040091003e9008600011102d0501c041f5400c4101654003d88491030140c482c6045004c2c0c10003602403156250704028010f00c0004d00c02d8103c2c0c2d00a104424001d402e01d105d906028010f1a000c0e0b1218591607030b140010001c0680c0601c3c11001301071f003401c0401620792980c0701d05449072001030006207807154070511501c0c041d645000706441c603c2110300c01610b81c5095254150341d00030342811740114440c43c2d00001c020503842c00031070fa14055880010070829141c40000d840106401902c10323441550000300307000d088007050241d40314920740e83c1c22080140c82c000380d040c1251592207199000340c10159044030341d40d070001071032a043c06040d65098084011a0f4030302d030441c019002c0040070a042036150509896040c1c2090f01042c0c851050307c1241e160001e46c50013207100701e20b804020368451b9018080084c0b12000c3d20702c1c8160003d02601c5c50300c0c40c01d540701c0100400d90b98045034000c44140320b050b01400d0030000b1202401040e00c103032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 457316744 1250 457315494 457315511
    0x30b040e01111b120f09010921120e120307110607081603030b04050108060601080a0e2112041b050a03210216081f05100312090509040c1701 62
    0x56140e20035443c0645030024150704599141e401000305001204422008a48819034400e00c0890b80e40300304d440c2070000f41d0004020500c1c03081031107014201c01600040184443c0d01c0d0750782445c206801c07001d0340c1c1030004556a00c0c1943e110f041d0526840d024134000b8541d0f0b210a40750a4099103224080303240120018050703c00000c2044048650352140015503980211852808a000d0311020f4039064125042c18000181c00b54005141030098909885080c07850745e420041c202202d180030f00a01f02d40e4801170b0b60b1070b0491128070f07100e8000300c1c8860b0620301e42840a009031190420980b8100e52003280c00c1095400f48144188003c050a401c41d0a4400a8910788854000c0340e40c0e03081400d0b0050500d00c941030118001c00001d01c80041e8404c42e01003582d034555026466040281c525602506559801c4142482078820305104840444501880600390f848a40d0301c43d40030880030083c050340302804241591500e011b28403a0b4440c075810182d06040840c5116010814490b080740f40e030500014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 457317994 1250 457316744 457316771
    0x80f0402010e0d06060f0b0403120810060e18100627061d180603160f03170c060903090a12050c09060f06040e0a050106081303050d020910030b040e01 66
    0x200d00182c40211a00e64855402d03042000040c00b1a5020740800c4030b500300c2c0040c04501d000301800c102c0b0b025500c2050391000403d03058484010840342d8408200c12100d06109640c0112049000c080000d072180e000000040c04054002c4420b0711854891800010300700110f640c44445409014580c000c2d1641c61000c50a062081350303954014182407145151040201080028048200c4840103241490400d00b41e002e205c1da030b034030944050b4082e02070351101c3c0b9440c515a2501c48100d83d040b00d000312509103962110026031000114085990304100440440084104100e03405006810b015550b00d1921b601048100060760784000320429000007410085a004106051004001e41b1100020383e01da5001401511034005540d60049020902154854001002500c00c1e15a4802084240d885c0c03401522160821078480c840c1a00c116060030009104901402502d505c0c05400340c204951440051500c5050410a40c0000e0750380c4064200362a01c0e00402107004890402000050b907210013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 457319244 1250 457317994 457318007
    0x5011d04110f130c03050705120a0903050708070303230108030a11120d0605090609251b0f02041103071d060d020a09090e0c130c0e060a02010903080f040201 69
    0x2000e4007058a00c016080d0a480d241c40d41c55225000901c0140142480c1e40c041d401040c81295003c0003e1500c40000c203047d0044080310403185c0c84058105660b07030f403004000050140100110f082002c24042d103000180a8000b62107094400e032030214003003004920b5880d0000c00548102c03035070711022004100d0008084112154810b0300d107081040c8100740c504483c900100501e81e580c0444000411485549469110006841044403040980e0b10b51004010320391605641090a4058514030880184036209400203040100e040041c0c41e000c07402da1107900744421706001e4822121094104045240c00d02c12403443c1040e89280e5170442c10705510090200c013018103580903078090601c158200380e42c2c601c15a900841c1e0b407841595103118400d0001c0c035200b900c0c231514681e1800d01d4010800428045018090818007500201c02ca00e0354400b144003402c1ca144882c010700440c1140040d45850300402015180300700c0d000403c14008a180060200900900a90034200c200d414040184e030311a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 457320494 1250 457319244 457319251
    0x50601080402010e150f040602061302030d0c0303060906120302010e01090c051c05070b040f140312030c07050d0203191d0d0314070c05010e060a080a021b19050105011d 74
    0x600f0000d24601d41c030109074149042d100300361750088082252071058107094010000d84040c3d5083d0ba640e40c65a40440ca6600000c250081d80f640088d401d00300f00c24410380ca42c804060007854045442946c603044101120619080b030001c0c41924103019042c550240941034004c01804000c00400308503880304000c107407650007014807070212040c009030400c09203400e59a0254010060320441d030307a101c0c0c0544159015100315006409041ca00081d00c0038024649103409034050040c203000c5030900c00e0884194070040104060ba1000c1c070280000c60000c007c041030380c01c07180d0019907481000c442c8484000c2243d0f0381100c01c0051002107813804590507d40680350300400e407500040032180b1305c0c0c29150303142c00c4628a500808007003a00014071105c1002613040320400e80f98100f4030704002c0103000c441e21511200c2808599a80701041c44050780758000c00d681c050b0244030404045000000c43c0c04c081012014403580c4244903031403024840c083c440c0341d0062001c0780e450500000003400072004140002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 457321744 1250 457320494 457320497
    0x100b1602150c030408010608120414010c020d0f0f020901050411070f0c120b041505060108151c0c0f0503010b030607030f090c060305040507050907090923090a110405060108040201 79
    0xd000c107520010003001640c2080c8100003e8030384541d15080b001e40217115500c43e407203286c81549001e10510b480101210b051b00c0e020b0f04040d2102c0050001501c07054004001203800c803440e5001e03140810102507250714414403542c801003070030480c1e004009a284045e04140d11071890900c01000d240304880403580c80b15400000c52040381040d06040709a042907a00c025407101151301540208105100c40501c00c0d80701d03c3c80c4401c1d000e045050003003180c0d4201e60240c0401e481002107181e01c0c05072050083c1d120f20040c1100b400c4102441081084a4002d0f01103600350001031050099030100101c120182c54190000c0040743c00c00400a0744d5410098504000c1c1582c5080c800e4041c0082d4005601040d008041040b0041d40da00d0002c0040800b10f90039100340c012000045418030340724007882d000d54556a034820b0078034100400f01005110200c40350886400005600d40c0400c0f12802662003112200041d0402000f542004101c0303a180c0c402683c4114688410007000341e0f0801c0314242c000750207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 457322994 1250 457321744 457321759
    0xf0f0105070f08370e09070804051c020a03093503090901060c050c15031602010204260d02030306011d22060914010f1406040909030206100b1602 64
    0x660421580c94410001011000001580940c14840304048203034941e0744d08040e0b02d0168803001d8411264007108500d02070340920030b0030104002038481c44800360440c1c003a02c00d4407050320b9520000c0c1d03000302404411302c000d6080b44914209041d044000c1a0082c0444000d200c0c0c0c402c41c600c1d0f40c04d841120b074405035904044e12480204020070400035107080542c00f41403c946561211400362007040c106100f00c526104a00112100d410a40c54188885204090190a6898440803843c03401000c0301440e04540d800e00c00003c00d06003500112500748607030440380302d1145819070303540c1c00c0c601c182e221f6000f9580200700303020032664403108041d078601400c64942e5910400d40c0010300000441500300c8801212900f800783e06051941c0801c0403504400300810003008410b02000702c2c0f01092003003000f1001010410803481f02030f104800540440181f0036031401c1c1d00c40c00000d088a010344ca003500141d201100300310102e0a071500341c01c0035040c41424282005200310102410a02038980280650f04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 457324244 1250 457322994 457323023
    0xe030f030705131811120f07030e06041109010605190f1704031809090b0a02070f0c0b0309070b07051009060216150b0d080711012105060f0f010507 65
    0xc584143d4850540c2101c0d0244501c0d40d0b0a090401002c1e04416042e400d0f1a01805107940624a0216038603850064202d0303915640720b40c1d050510781c10040240091507101d003d00e0203406d17014040e0707a11942c42140c030b414030747c00043c080c0917500d20143c20040c00e00000700300000c2000c082200b840c1c1200e0301d92800329170003c0083e0084981c00c0c001d510700007400c041e110510041542000500d0662040300d980c07880096030302c08540059410820010b0030896401001c0381d4141c2d940d4000b03001e198060a00d8894800840e500c41c0c0a032a0b19a100d503900c000c0100c24001d10300014400680105612160305042031803d4607501d440c0d070103580032044680da8604810040147c80c4d0103a915452614010a00c0c04409003411094800021f000c05e402d103250002c401e60b43c0c504210451646904642c03d1400c00019903941082c00d00c1c0d25206038140700c44003125400e03c50900c080081c04589501e07010515017440710510240750802d814261080440810342640e40c0d901100742c488158000848420448 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 457325494 1250 457324244 457324247
    0x50430260c0102031b03060f0d051204120308090d201e0d12060f0e04030c0203060a0b011808030a0e0a03080a0801031515090f0f0c030c120e030f0307 66
    0xd0350010090050022410030201101075014520850a08407400222006081c4200240c4412914642e11042c4144a4002340c201401c01803580c0d07101d1030444004440b460003050041c2c020b0341c082c210718a1a54010800c1640c072144086d00461308400520551000302c0d400781080e4080c0412803440044002d0500c07005200f0810544094008008003032a5005514111323181d401c0006640702081d41101c1d10754091030240318000440d24401e0b500c0380060f040c1841410000b401404c281c0400001c000c40c5009030364140a10740c004e445040000403017901c01c44c0003422884181c81184210300031448104444a404011200d0100561800c1d40200c6a104c1c0087d441064540010744000c00c045030b0301200c40d070495001c6043c2c0e40241c07081d440c4032881031310940030303585a0380380741c429004801e00c2003103a500d07260401c854602000402041c00803141d103103a411100006031400c0080c2d20f440007510b00c140c01c003d940e2065080e041c0240b1105244101c003d0b560301c40d92005500305180080020081c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 457326744 1250 457325494 457325543
    0x403140303161224090c021f0c020a08130e0106051603111207080409110403051c092301030c030b06030417040302090405010c082d071e050430 63
    0x184c18005a412441e0240500c05110000380d0044813040c51818070302070f19450001070500041e0032405007078007120075031407a0300b000360240400b0a025885258440c030001141070340900314441041703681c201c1492400d11500b88031407061344401c081c00002c100c10401c804240400d16051509401c204c20a20030724500c0a1408081019400c0e81800218180081003001d100900071681c24450500800050800010180c4240e1100a18550010b860030f41c0d10000c640040380c18040508000f003150380e540c5060450341b081b6501e00b20002148000d90103a41d0b17010321400d241c10000e80b400300048046140400c5152101600243c04031048a80740c45c5c124001d00c0c01c03030340915405420000603080a240c824046c00365030502e000421007a80000748484501e51824240507160f00d4640c20320300310106007460711403000d0062000c0201c1c590030401c00402e4424088240019995860340d51403078103503881c20b401c1c4140c0021503041101c1c82c1c2005e2143c0d0212014400c15041a11000154902110346142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 457327994 1250 457326744 457326761
    0x3030c0f021e030f04270e0636010f24050d06021905040e07020604020105030114030a0212340315090f0f020f0907081609030b04050304031403031612 66
    0x82c1c590010f030104204a082c000f010070300c500600a00d06c1003004a2254040d07411203d402540f6901500c000b425111941407540f0060002d40c10921882e0b40018001d0100c0e803202004505581d16500003805a080d1449a80c028841101c650000507840030341e240c441400c24410b15204500400450040c0245541110b200240c20a40720041c6001d08201400070b800912032010f039540d41400186091380040341c42407040b0ba0503900e1600e16803d100d0b560064a66070740241d9010302c100c66940006032207112424480c000039500902070710381103400b00c062002021211610240200403158040001490f045094036841100745055040d40740084008003480040a0521129002d9441c1440209154251464002d48950f40c1c055140401c8c03203160001501c40a0001d414040042c510000300520a4102a480e10380760810310350765143c045d080703501070b80c0945184d0070002d01082000401d86c4401d2006494401460842c035010440c0000d038580c10040c0421f110382500341c400480d4540e80146071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 457329244 1250 457327994 457328017
    0x20d230903010204151701080102160b040302160b0c0f030702031203041704031a01080a1208100b0f091f0806010c080903100f05070512013b0403030c0f021e03 70
    0x341740390511802050401500c00c0d86503d009486d001107148001030089618142e0748050034100100c0d51b03a01c80e802c0d0140140250114090000608001c030f2004d0b40000003800500b04464440c0e0315600f240e402c0c9440000c26141944c020040040107807408100351042d111001c003181c0e2070b580ca900302a246904001800005a500003601000300f082e10105080c81c0080a07000070580c0e030f00c400c0e00c19901c20016134068040d101403028000e00134400c5943ca540811110043c41c02e0503514252040250003000c03e540c0060b6001c954103101c0e0815148003801c52949143c44440401c0030745002e800308902030304a0341000407005e00703072040c40760940885911040c0a0201c496a00045117140018855040c201c0300b4207042c140490044c0303101e6002c2d07906c00040b0a038183e591340d2070490002c070140364403450070080d100f40752011425840400d61070688441121000d010368585450028122805c031003a19040c0f104c8590342d0a6903660002c0c022000e5a18078544da070340111050802403850140c04102c21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 457330494 1250 457329244 457329269
    0x50405191a270307151404020f03011d0102071103030304030f030e030715201908042a08071a0f0a090512010b01120b0607150b030a12020d230903010204 67
    0x341c0c0b00c0b01c000000c160f068090792010b801000912040c0007a5200415079032007050011010501600d0040091803910310020000101d050a02002d0000c440c00c0016034181a540401c0c4041407280c243da044944000c02c401951079840e003950060a900390480c0c540e001c01d940c6500c0526050001c20858595a0f0850071504c01e4650640c1c001c005400700440040c002c07415440000d0054507080c00b0303103113540e41c103180d00c102c14480034000310340241c402041034464561401d45001200a040b15080396811801400f1500c00e041c034000e80d1030f00ea044d52044042801e01d080c1c5041c107200079401d5038030260195000503078845540800300c6540342c05802c900d5000d15010b83d14098000c0c1540801c0018800b070300c034017141c5d5540c1c0344207030121a686c940f5240c1246041000f007000840415114008c030200c81d030005107180706480404e1a0461101c02100c10080c0921074081c0e030f507010010003000301c0301440c1030384182d001c1303030043c01c0c070441843e094101144011888500b155000e40694028040c204410f8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 457331744 1250 457330494 457330561
    0x303070c06150e180a02010e1201020f07050a051507020606010e030f070623040510200106030804090e01020702011707030603080c0604030315030503090f150d050405191a 75
    0x818906800e444c00503035010a2058000032080105001c01070f290140c407101d1114440005102c184401e0075483d01295600300012100c4200030f4014004282c000e800521010301586061b1345481861b45410006460320780030800d103103a00142c074a40c000d00a00e0300c0801500d40001080c50b10040209044142c018035101041c21076100c9070702014a5113042240710b00c10102c01005403640304902481e40c00800d004050403445000c3c402c400540f1140310790b0800000d0b940d00310341c0e0860b0744540048442110010b810040c03000a40154030003064404000c6140c8805a070000c0c1a240b01d0801c481c1255562000040100d80654801c00041d6041160540c2d50548166a02c0c0c9405084030708901107403900d4000d6140008440e40542925804030085161190041c01c1012075451145985d9001c0307248107040c00c2c8041c40f14094890781d02c075108042018201480d200b402c20080811203010682090844400718031103041000d1011031145100049844144012240d002000d0003484405000d5400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 457332994 1250 457331744 457331759
    0x6141806091e100f2309030a06050601020106090b0d0b1915050a0e010602120706020d090308040b010e100504110403021c0b1608040602160c17060a0e0303070c0615 72
    0x14200c24011284440341114010f0107443c200d0a00f15400c0000721000c1017920140500121005040860002d882c10039100200088c603240300120105c1e41142c441c0c0c280485960240500406070003d41000d0104880c4100070803884400c40d807020701020008400300c0c920040070b0016440001520f50144070103804545406504413003442417601510b460400001c0d240074000f41d1905a0386141c0c06000248018414000c4e560404081556015420003200c1d505c50201d20451130071a00ca501e03428020318003800c14920340305050b031000c46030205038030810101d03114079000c2d482076403012500010018000603038200350f0301964200070740108000c0e4850b41d558020804060820f031083c1440e880640d2862140040901144000408540c0d240301050010b52690040c140020f04030024101500c0c01d51548400c00c21641c0c841304091414282c41c110300c00f4240401039000140403030038000e8124500345640d880c40010a90010401950584001c2044680003804100012604180d071140c45009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 457334244 1250 457332994 457333039
    0x3020105072613062d0e0715020f030a17091f18020402040b19020f1207060207120519020106080a03030b150f0a120527010f051003020a0614180609 65
    0x2e05c0d00702940f42a83e58051410315000e100400100d940c00740401a28007001660000c09006440c415405806110401c8040c1040540b10151055aa0a40d2440d00c480b40c00c080c1c100142601003190060b07030b40c0304400203019580042c048111500025084428150244400240311009600c240000b500040d4650f921001c0c051284944d4011880705007200000d0340d44003401d85100103550440c84000259a80b250003505003540141c0307000d440c20961382d8900c000c1c19a4a4110f0020640114407036129001000103200010030030b000812007d03084c038450659802d0a100c0c02400c05859402c040341c1034441d48404078034100d0400449882e4520002c1c10386030758002d42c0c808000030752000d001c8002d030f205a004180c0a601c0182c81420080d4808612900c1c004185081250564071075050001070655407086505c00c4000c0d0f1020004282984100004001030b42d101d001003000b42121b01e800b064811003220070300d03907808030011254403125000c034445000e041ca120342c7c0004106420809000c0001d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 457335494 1250 457334244 457334291
    0x270309031501140108060f0907090e010611030417190303050402130504122a05070f0e0603100b03010f06060305060306010911090603040f0c03030c0302010507261306 73
    0x400361100090150141401c101092150b200316041d44115002103500500704550440d85c0540584030746556034000c9901f506c4190f4001d000503c43e01d1f81002103101c41c2c5400d034050512031401c0d01e47c0721085004c433030f5070380114066034034410340c10304c141c3c0c043d8501004801001d401c907441c600c2000200341005801860704803001d9008020700400461054450301c2010b210340e90104c1c92944100c1e200d903040701c540ca090204800740c8403a80c407840c0c0b0072020a051000e0014480e0000b45541801c280f851541ca900aa0000700381510b40400c0c44110b54000c505005603409101d070000701c490f41c08000034003508100b483d003550306290510101c0d125a041d080144a0b210580c201c94890742c3c1c948001c400c4410032a80c01c041c11509110304111460004011500320f070080c010140140703900c1d124017138070501a40c000c2700800c059400c0da5007059020b0145651021050070500040364150f21128010f006001720b810843c1c803542d000601e003211a04540d05a913030041d07400c120a510f52138007030180d0000034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 457336744 1250 457335494 457335499
    0x7080a140c040c09141216080f0a050703152408010e0a120518030d02030a0f0906090302060a270512030702060f0307020a0f03080a0516090e270309 65
    0x300704010a5041c54080e070503502d0a00c0d0f4441032400c3c030b04a03013100103400500d091a8441c02c0d03454104a100400c10849880e0b440c0035801b0301f0f4640c5003c14091030302c829032040444580002a039003000c100041440e504032a0001d02031000000c90561100080c11201980617a15425641590529a0044800d019928070380020800b1000c14034810756034a108910080c000c1e10b1a44000b0302c010b10400c0030b440c0040c800d106080c0014401320000342400366514100005a10200c4c540203503d500040c11010307190f9a00707284030340c681003200c010034540250102034041c2e10006081c4888510640c00d560b0000c0d0041c1d20303048100d00c1c140c04c90401e0051882910301c02e6a0070565140e070b0941c040200e404481d0700422161400122038820912074000600b0340c401e5008102e44100070444894082101c14803d55807001d03680340c40f051160455070082c20301605166181c45084580790010541c10968803114030010007543c0390344100105102c010000c10711260000040421100000003402044004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 457337994 1250 457336744 457336753
    0xf0f0b070206040b1b0405030307080a09120c1a12041203060f050303030619050d1b09021c24180b06070807060f0b0409081b030c0a110307080a14 64
    0xd0100c12a60340100f507034003821010061011400004160481c00000b02280c1c146a00303159031000000d0454012020907905040c0005004000715800b5004078042d0120182d6103001244036216414449502d00401440149941f2004529281c100a503030415881021803a55494035107040903401c8401849400070070309110010401741701c51290300c4195000a0025400c0d5940c100400080c1c43e02001c07808400c4e8800b49010400fa19100302044215001e07005058009104510031081606c0f50762000c8036580c41070016100c080d101c90760383c00d0202c015050100d44074802c40100141080c84040c0d55602480039107000440f48a201c442c000080d046d45001c00c401040001071041c40e01c02c640d0010407280d402c200160005d242a4012200c1e65580440099800c2516000c2000c48841035425201e000300032420000c001c00b58812501c480d41144055070401d8a05080349960310712281000f0400c041c03504091a054a080000313000410314582121108407540c28401c030001a00d01d20550180607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 457339244 1250 457337994 457338001
    0x9020d03021f0c230c010501060c210c0602130e090a11030703020901170127120c0b0a020a0e0603040803090634050c01060810180f11030a0f0f0b 64
    0x44600c10941e00060729200d001d501c000541000c00340950f41da01c1c4441080042c0180c0307001744024402c15000e0703c1c0a440b24880303005541030070703606901c001c10b610f600e01c4040000000601e503c00810012280d211030b02607140d01d43c231141c441d11941550024218801035004102d810000005c030b14114900a100103251150400103250311001a070001035000603070140100200c686604000c46052410341c0001440c88502d0641035003441000e120083c8403d091560405000050030300204410841c240840c08502c9070f40c44001c44000108450502e0f41c2c04178403240c0242c0160200f0070300329001401e00742d5914052030002900e420a032282ca425120307580001d00c80c412901c8a820043c9000031005464241d0394850f5800400845e043c1c2d001c0041c00c0c800324140c0c0300c0074020344010b00089009030400300d01c3d080142d011545a4078180011003040303030b2510007040007100e1501e01950050346000c0204000e82c0402d207004050000200465100c0d2404400d0110502589400b03030304ca001c541c1074588 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 457340494 1250 457339244 457339303
    0x50d0b04050c2209050118060803090a09020d090b250203030903160204091e031b020112050c1b0309010813200f100305060f0a18050a09020d0302 64
    0x114100c0d40c81ca82c107902001000120034106210145005080342d0000000f5200d03500901a201c0c20b902a14401d0b660902c002800d032624000c6902070704130400118105000c40001465081c05c900c07508911a50015100155681c0358001c225242d800210340c2940d0304101e400d0b400e580341c040314002541c070008111075401c0f51000c42141e00a03d443d00003541021340521400d0b00c41810f183c4203e0303101da17582e40000d0004035020502044190714041c01c01b000c00e100d081c09081c0c00c54403207114100da1100c041903c0141c0e08418000e000c101c1c16200011640c0e1405410720700340c4920b030129101c8041c40d000140c900500080100090340003a42c03450402c2d100c0c1c004420311540c25080090182082c45c01c05840b01240c0701d00103001280003042013110051000124034040c808603c4034002130744a0003000001d00341240c50301c27840e4000345c070b98030a89441e242c080604402d001e0118010541c40b040171441088494010300482034000380003c20121140ca4042d54480d0405001c51516401014034207144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 457341744 1250 457340494 457340501
    0x6020f12180d0818070312020d12061206091e050706140306060417011d0a0c080a050a0b0a0e12040509060d0203060c0a020a050706030903081b1204020607020907050d0b04 75
    0x70141d548406007284c03104540358800280354460410940701e0108000b0210340019a5440400e1594001d0052505456401000884481284035403213040005c01c1201d8080c2e241c0c444815504500c002413504594070f0601001926000d1002880050f070070000144000800c81c0011511242c80389010091030070858406404119043e0340e0011044c4002c00820002d000d0441c107441080000090a081c400e903003142100320a0400203a96014030300c0d0004001c00188580068101d240041040442a0b91507070780d64080f09070001c10003913500d008540182c08036003000381c0c009480c070b05540850f60180313105c0d1420f410a100d01071190101d580407508509004283c0c1700900d8018000c4e195583d5000442d050a902200c0300c9004c500c00c554860380403c100307100c000302404041d903001c40c1c0c01c82c25060041100c0c902a1050316540c10130080409070641176402c03034080040645413034919079200d0001890038001c44001039000740540c0304218480380d0120060841248003041045464000010311048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 457342994 1250 457341744 457341763
    0x90213050114011e0f110307021801090b040618020702030a0c060338010806060904050c04060327021c0506100503071a09090c0c07030b1512150406020f1218 69
    0x800c8208843d10b184c284544078106c0599010001c0ba881c05180c0c0d80030503800241050300a011201440060210110600904080101c00c44040c4402e0b401c1030845810300b40300b01004042c090b0700091140864030b0511809580542107440300b0b920a6075000041d01515604036070741d4507504a10301801096100300c10714060384940d0f01943c1e0801d03610000640b10b00401504c010350210081c007507144140c0c1d490240a20030017000d607629031a28500312000c0c041e07070900c5122948184045c09412410700c10199010407040d011103c140e80114a00c40c80e07950040401009089406030070200918403200c05036480440303800b90308030703400282c0ea284294060481d81380d40d07445032107042100d50281d00e404180c0c1508100a112103d16100c24209424540b000942c4201c070310605c00c00801c54280704ca000c040000d07080c02d581c800c00d5034641e11030282c2c07214608405d2000b0503030400003050a00400b541550003e2882d50f01465440304410695098900110344044445811080f201079014004c907002c2035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 457344244 1250 457342994 457342997
    0x6051605030a15120305120a020f031f0302040509011407141c2c01050f060a0608070e030d03060f08010204150503090c15090f0a05030c0103090213050114011e 70
    0x110b4031103003908005000c0422070350b100c00307201c50b030040343c481103040c4a01c1c002da00c207441e0b2940d5156072001d802c4000300e0003480701404610510003203081c0c4140c5011258020541c800840496000c0126001902d5854002941161400003000525001544003000d00c0c041140032541030768440344111184c0910030240c0b0f84a00c01032002000b20200c0c184c01283c1001c041a000c90060307100b01068405081202d403600000700541044d0910907020b00c64540c01c8841640074409a280079000709004161921901e020856030718001644d0500c5607604a50b41e80f001000c3d5003015032600d000a015014a001d03a281c42ca00007075000425001c14400c640031108040740e00104c3c400c1501d0f00741c88d40c3d0401042c0b600c9501801c0c480c5403055440007510452440783c01b0b003140c0c40700c2c0c0810922841181c90720810340202039281c803c1c00a55000914008404002d29003c50036088034804920510456140c0090450501d0f001264a80a42c110b448160500ba80d078141d0809909100c03e89281c6800075110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 457345494 1250 457344244 457344247
    0x90315050c1b011410061b021804020409061103061507020a09200d020d0b010c0b0604020f040302031504020108250513030b0a050103030e040209010e13140c0706051605 74
    0x107942c20007861441c00603007070304000212036007282c58902d0560802c03181c481c640d0903a00c40c01d205003608040243c1c1280300030642d401d5480311540c04120686802c3c08603e805a074200d00050445d6200e0b0800d541c215407042040c002a0035461150107550000e40b4a188682812800d9042c0039503000c00b41c4100a400038450004a80b41c620507900410380484c04e5800d2005d100104c4280e840600018a141ca0286100603a01e104449010007104d03204502c841c10005100610004507400344542a04610210340050360b601c807040c44c400892291740d200940500032243e1540c2c042098140e140c0c4070394000c1e00d9410960381e403089441c071040080c0922402c1c07030003c1d1950070051441000900800a800c00ca40f016032a100c0e04ea8000d500b404480900b0030f5a100c0004ec420103500101c40840a0001d803015030902c182440042c0014440180070343c05146081c2040019417442c2e04040c62003884600d1903142400c0640e07015910383e1080209580c000d04213004035845880d0164220000d801c10750300c2c113 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 457346744 1250 457345494 457345507
    0x60c0f0d0e0a261c2c060109060f0e04060c0e21191a04020d151a090c0906030a020d0507020d0e030a0c05010e12010c181a2203050303010303090315050c 67
    0x40d008090205c2d52042d1140d028115084400e02401c468600121600081075198549001501511242c1c2c10141d518080f0600030008075940040080e0070640c000c602007590b240061007150000d170403820843c2e01c08501550000d41d980d08440102800c50614150f610002c2d00c0783c104400000c1c500d000500c04030103080c03010b0740c9441c400b4907540c2051004202e00007442854036500080100095120b05180d83c550b00981010890254580d070814182c0e40101e103440c0400310764015000c2d104038240960000230006002e010070b5811118088800c0c0c808000508142000940e0780b018402207001007141d821009850b0319000408a50045d0700107629031b20f0030b0030f0000444412200581090700101c14a40c0000458020f01038189420034564030b0701c40c106460303042c502c00702c007880d8000b10040c1402c24000c96851000400c40d18501c01c64802c2030f640c05c000c500001007454880d40047c009000110000c01019400b00501c402c49010350243c40c054031210b20000d08841044d110764005c004204a04c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 457347994 1250 457346744 457346797
    0x603070b0f0403060213061b0506060d08040e0c0a14070b01060c06090203011a01021501080706050918160906021c11010b0301050c07020909060c0f0d0e0a26 69
    0x8240340800444401d0809070f6a07922601a40c12600d030369140440d9a90081c00100c1d07000d58484540344d0900170b85100f0305590b03120302e500c82901a0109016012300086c80050002d4402241d008142280c00e840d441d213000c429111182c2c1001e11500e0008a14000d22002855480f050360150754110800800f0741e448c0c0740041e030b1074901031035040706d14170384400282d0003582d828450700030b440401020466180348a0b0000a0038925000c184000056003d0010f0101020000700c0c0400d5500604085039121801000248080300c40d219181d181210001007080c0d5041d86411600001d045465184026880311020b036100e18208503d0005c44007003001c4543c48038411240703041304513140000010032981c140082825a04119809000d0140000d850821418005002079105441c40054041400c1c00003401c42d03a4441c28040d21028640826107a110ba03016601903a00b5000000c100d4507050102c2c50072600b040e601c6031203c0c903062000030301c4a4201c02060222141d5441c4452031000b07480a0803039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 457349244 1250 457347994 457347997
    0x40323030a0506120a030903050105100b03010306020d090503041e17061906050310020702150901020a110609040912180620010f060f03110409120e0103110d06030605010e0603070b 79
    0x1180e9800710300104e5030000714200f4004440082d0113a80c1c0c044a40d8203500b0000d080d2100585802c00d621070210341000f1550b08042928152070780140301683d01c0ca03401c1c45d01005403e1100c8054042c5c00006000522104030710007003810058070070740ea41c01d40c99480d20003071000407440ca212105d0b500228000380c1c44030541d480030307a5040009440080d2503a2074030042071810038480e5800c415184c0c0080c0c0b100962400792480e01c4680417444101780760000010000b915500d2001005141c03003014004410650b03508010390340c10700406001001300d810b50341012207440c200507200d007010800d1400038100d043c041c0380900068680c0ca4960080310380b4100380c103101c80032840060303c456560301d594003400081507018040c010031302020980f10701415403c0c90460240340e00b00c0b0900c118500440d150001c2c04921102d01e14800710b040190a017845070005a001d000c058100480000e000074044003481015440070056074040d003000c024607030f00d400c01c0c1d400403c3e050300d00d907505500002c01002521b21000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 457350494 1250 457349244 457349251
    0x405190c021f020a030612050a12030b0d060204051206062808070620030a0801170a0b01260606090406111b03040302011d0d0b090109050a0b040323030a05 68
    0x8102d072194110301e1403442084030040e070811402500042d40200c00d80d450701800c4098460f4450040201003d50307500b48e84e4480c0307814024081e0048203811000c0500135400a00c0b2700340003800505003040b40c0d1500b00000d502c640901403151030076240d140c882080014016200703c001910003550f0040000d001c02400d000c2c0403d030100304030b140e0300104610105001d944024403150f1180c205a01c21482081c0064144001c0c0305101d600c01c0c030140706a95441311005045522914298046514210321035050401030302e8007428600180d000011b007a210621030000010340b00d49180300c1407001640c0c0d552182c0c0e042c1c40165001d40101c01040215100d544401500880342401a03d01095000051340d83e00040841c80d071590070100f810020755030001441d0301c3d454507005070183d60080800000d40d1141c82004054040041040003030f5050700250300c010394040d0040300b19090780c11189400450203404030307802c500164040142e02601c1046d4000e0506030400385840500355928040034200814004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 457351744 1250 457350494 457350497
    0xe031b030a050f0109030806060703270b27030703230c15040e0a0b0904030c03020f03040902090a060905090718030b09210906070b0901140f150405190c 67
    0x14424000840c10030080d1003c1c01e544001045490b000e080180c56994001c0200740079980070091140001d512450600700c20f0456040743e081956a03001c000c0614803203820000904500281c41c12000030205c1e08445c02da002d0881c88140c0c40d50210a00d9210452480010962840b03d652406201c42d0121544466010306045805501e04400024044034000b0104280b0300c0c8005818013038500b0b80305609900505262041c4480e01600c0c01082104000a00207401c0080c41c09000d02054420700c0500d26000e075090880f0b40312500d9101030002544102d030164859802610000340c10f0b40910036403c11550010803512090307490040940e50340d42c0700c480c06e030300b8480c8405010000811013402c2c180140c540600a0003181c3c0301c138900b000c404110203021824500280074010320703591507000b215042075000c52210103030785492035124003408050301c0300f41c05c04030304004000c61401110307070580c840c4828200321128142e280d0300b40700403642c0030750340c445880401010900a0070680d4212010b41400d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 457352994 1250 457351744 457351753
    0xe060f09130212070e180f061302041e09110a080c07021008070315030b161209050a0b070f0c02040b010509090906160908030a14071407030b070e031b03 67
    0x1000c80007040f039020400c4240a0180d24040c040c440394403c1100340c0961040d0356080409a8400f1070f24003481e00100309540c1c4206081c00144e031502d41d1020940c0c80b5112040c1507448030788840c42c10710f1039130301c0c1541c81c540c0c5002c07913030000761001890007040340503502c402d003951400d1440305044540240081c410146081304001180060f105c501070707482c889049940701c606d032f814024002025a6040007440c01543c44221040c80400c0800c2c0c0d00d03070380100e283c03280074000c15a900d07410b8906105000d40030400500c0d182c039003414040b002c40d071003c02074420603520a465444800955a5409010070200028114100300c0b00508241d07000400511741410b00303600780152800000c680110455142d4929044042407280c1c10086502603e00745c2c44500381141814200032000340c0da4040c061060302000300a40c10884007407045000c94034031a402001000010801140b4030b031741c0e92118070044030b0b002031140000b07005601c9450424042c22000b8083c182040d10350034100c3c00d4420107174416515005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 457354244 1250 457352994 457353019
    0x31b010f05131806270f0e060117010507050a08061e130f1a060306240a021c050c0a0212190b010503010507030207051009052a0306070e060f09 63
    0x1075220721400606804902911a1440040210a0715810390100342d0300c520500c144005c0d1340b40101951400c0a81850004a03182051610307006021040084111030041600111300a480c003a14076191000c00d400a220365125424101c85ca8403035003492400003840d44c00400c0b0f05141203411000450b208005ca43c1104c60050001403962080b40010340000e5a2846900c0900509024205403004d003a0a0100450144004075855200050000344a540710710380500e03034103240b10141c0c285801601c024549070380c4007100195440e00301c45030003e90403400301c400341001e030f2041086511282440d0058030216400758207001140c0d484070030001082c007503005114003903001202c4054950380195100c0041e545030600340740c01c550000e172518040500401c99100071800004d2030312034400903003100003640d11407800c0990410382c84504a001042c40b003490807021100a5200a014500c21406e551507074803802d03002e45e00100d0301c107101e40c0c1040050080c0102c0180c841c000d0106038038081d00e040032010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 457355494 1250 457354244 457354267
    0x20c0a1505040f0806070f020d0c02060310030b0108030d0b100c060f1407120e03031509040c0b1201030b06010908060732120a0519020d021c06050f031b010f05 70
    0x43d80d07401210321940300c002080340c11940503140440003507013800030b0407524030a0728005103600603401c03010307000e504004040b0360b040040c3d40c80c070401035800c55482c14041d40c4580c51aa200c6d44244030000009041410712501c1e850701407900d2074100442e440e50040590982d40d40d1014107406110481c0090f503034031044002109070100c1520402d21582d449c02c04047c41d07521001103e0300f40045610036401403080100d512900c1d004404403520451304082c080c2e45501d064001c0724195040641540381c0465000f00340c0015899040c1a44d2288405c500e807660342c8c000450350181e00b842881c6503948204040381189000f038203011002041241ca510040e02e200c1c2c220402d1502c0c00b180b2140b050000104004942d481c42d410f581c1103981d9610074466810000100b20a04191000340c12041e5400038600b10003101130390440352051103580a00410494426248005100500c901400b41103441280107007403401207141c4500c1c0e04a075100c0228445600d0044600f44c180c864076100b484070400031403e0342c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 457356744 1250 457355494 457355519
    0x6040f110406020d091203031509090606030b090c010e0402091c140706081e0a0207140c010212091c030212040305010c020d09050612040213060306020d0b01020c0a150504 75
    0x40c0d0004450380e03480c600000245400c3c0203200310300c1004850442800f248032001d074034448090305854040350510140c400100802c0d215400050118506404042004801d030040d00440c4d00134034600020741d03034a6082d0703038480540b903070302c140007402c42148400d451401e58064000c8032005803080700d40541820454640041c400d0054030f0503840040158010201004408003419081c0f5141e1064100305d51003041c81e43d030b224141e85140c040540040c0c916281581038594098125514180041e604090140ca171080511043d0050192824403c61011403000300ca00d180405480311440321000940150aa203011030214118060181980e800d0038550000e4400381d030182000150390134140300082e24041101c001c00013482071401e02040f03140d81301e00c1903540b180600074004082c0e998500c001000c0c012406105580d00c0d1030721402005000b83d0b903010700700d41c100c000c030108280340c10240103994031501d109865502941101083c80b82c0c404805002c0707102c1b10382e800c0c9242015203c22600090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 457357994 1250 457356744 457356761
    0x41803080a06080304171b0a18022b05070e0a091109090709060e030c01090e060409151a040b06030402130f020403120f081504090804030204140118020414040506040f 73
    0x6c41030004d10031440303250074820011490b41c606c240d0280784a1400209601c107145205030380115940c02d513003210f55401c54048800d22031100d03c90345049003c2c100e00c0c00c0ea04c3d40610322072207124038080c00501100d002d000d550100e6480100110103081c0780c441208084d0074661074540da84c580078441a501600c4521445000707100c40d4503491441803d16400514806000c0c0c0c601e40f003903000502e5940d17242d0b044080340040d2843d082e000001640d40c0408030700035000b4110004d00c03460bd02c0740d4010f90340d5001d40c01010700c50700ad44400300c003d0111000b000152801c0000303540d071012082021030300500d820041d40b441a1061302c808110090703811483c1040fa001640142c550f440c207100d4600301d01d9401424111041407506120f03500e81004072102c074030868007080080c0103a42e104407010900c102c25041d02c000391fa00404c00c2c410040d030f6803c216031103907080c4500301c086207041101da45048014020b940c2030b0f07085503142c005038200250070880a0200904110f40003590350300d02c00c40c0c2e070004c1e00401d01c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 457359244 1250 457357994 457358009
    0x60e03070f1406070e10020c0904030f1107030503250804030b010e0901050432070f0f05030f0c090402060708031e09010e0718110c0a0203010b041803080a06080304 72
    0x79000c009041007108000b042c51225020742243c81080380c0d45070802d0100d80c8242003900c3d4403140c010300c0413040c0e00e00000c00f0344542d40714a01c101000300f01540800400c002c079066507110714441944c03c2c505035403a1031900005040d50010700443c0508031100d10000224100401c20503002c044503180c1071010ba000b90020b84518011100610010150854036900458000001c100390b10f02600c880418154009454894102d0b0402140d80100480702c450801c000364020f03107000030383d0f48900b000440828800c00e130382032240344800241840d000c9082e021403d000d0b0007600038104480104203150b10700030002c1341d01040c00d01404002c0b43e0740d070020f03610940c120481003107a2000c2e9800c400403010300034180c070200d81c10900088008640420524100e41001920f0000500000e140c0405044004d081d0401003002043c2039181130000140c0502690094000304009800e540901050303401d0300c1034000c3c49400c22580c000000b4892490540d00500440c000130b07003a9240d10440d81075030b1060f80030b480c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457360494 1250 457359244 457359263
    0x81002031e0a0b0f06040e190609020c0a0b01240513030c030501020c0714030703030c05032104110a030c050111150a0f060902040509010605160f08030405060907051c060e0307 77
    0xd02e007040c0d03900701044e60003100c1e0700e03003040d00d000003040b0798443c02480d008450040c43c4506004c0d01080d007281e0058213400000395160803280c54400e42c3c8620220081e00c40814040000800c101c140030a0001303030a42c411440e004107000308054490f40e00c804004c07107a07050425000404030784408050400f441c801c60002d6940c4554865040c0303000d10356080900e11024914500f40540d50000389942100d42c0360420090030052810310304d00790301881c010803002c3c0060b0000350103145e0a54900750322841c422001011420080d6051002c0250b45000040501410040602ca19070040c2ea41206d201d44013422034070f0324a43d80305510036200080d19145502519001d03072281450081c002d0201400c2da5100071403e1914050000f00c03201010300c6100d06000340068201d4009203043d503410880f94101c0c00e0610780003aa807408000940c0111030588160240d140402c0c1034030300101c1c4060480c0c1c0b00038401040c07580031410001d1511035a800c2190510b80c1c641c40c0040080d802d00c0500582c500a58526 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457361744 1250 457360494 457360511
    0xb0d020c0c0f0a090b041508012c0303060d021f030510140312070201140301060206010e07110601150320040f080d0804170904090615050a081002031e0a 67
    0x107454606080c850511820308034440001603181c50301070704104c642c99a008540780e242030011074020440300441030501c2c3e642d6180800d48503c15008454100c203c20f01d28100c80308810308801c90006558000c2d00181c0040001c10900e03e0100508224240000c0003403441000b41201d070b0000040b000b40c810301103911070040003d400a2116140d00401800c0980d403082c2c1c0030703040069202d01800246c1c0c0c000350004940c25041d6445500c0c003c00d880d8030014070b10b41e0780d61114000b07903640e24248a607440000d016000620014820000c201010b00d81c10010a070903401e00000e600000d142d64040001c050b40c030b007402e451040e9000400008111140c001c03540d1603040c0030041105940303581041000327600c07442c4100b10b400da00c10a0603500070381015041d00f0b42c0d00e01d25101040ca12400800d1a4850b041c10040011f200745c83d0f105c3c0c2c5401c0e8501c0003201c0e00d143e0310420b20025000360312407003205421071804044040600e40003564025508000d87e5a0741c0214000842100020748070502c0710381d56079800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457362994 1250 457361744 457361767
    0x10338040209011202010909020d06180213121104050901111215030a12080702010908070803060108090d0903140f0106060203031609050a170c030303151804050c09040c0b0d02 77
    0x83c0540881086000b828210b900081d000d103106101d4008010303800100071600e07107265401200580004802c41508120183c0e0040107900310304802d4085a400c8000041e0b020000085003803c140e204688210740c3c3e40300700410000305001050b02c8555500c8107110116030305114020b1803176070f0380b08280700e0131401c2140360380d03503082141005240070fa0f001c848504042040d00c040c0c0e04d6644800d24082d5000d90320704508a0143c0780044000b802032001159460400140b000070310310407882a62036000d07a0b0741345000700c1c3c2d031a0043d0000030080b40029406201180c4000b144041c0d03000210b0450b0380c0040700001c06030840f5080d6000000680002c810311145d00d000851f03501d00c0a1503858521001801d207400511944120300c03920f401030054100901950320148001507074140c004050300d880f441c103016810010028403206611600d0422020a01c401307044960500071030300500101a41300c207110500c0705020025105036246948004001a030018240040201c03202d003203009a00c82c01816103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457364244 1250 457362994 457363009
    0x80a03080c03130b0c04031502121005102a0f0b070203090f010e130501060f11010603080406030e07210c1410140903030414030601120b0103380402 65
    0x1a01c1181c4070200305109480f4100e5400083c0c0703d402c8152402a80c440003002002886154801020242441e000002c0720001d540a405499181d01c8680c505a9540b80558046003541c082c0540c44000b442605598601c10a4079140044441295601000380140048012803000c0801c1b980723503512604040c1080400018a60800c115000450400100030002817042e42e103280c850f8100311444848504594a1020801c01c0c0000d0100421540d41c603034100902265009400708041480104a03075103890051003014226034001318801e04040c14520100c0c05030801e0510443c841c4a43c10303012410361190211801f042001c0901e01c2507886c918500170070311501030b5002c1514920f0044401ca0700782c83d41100010940c403c0c0c41e080701482c2c6200c5d0807900314051040400d07010302c004980410700c400607031030022078107408a0840c3e00036a81c0d04428105e040201c0001042801c2c60001000096008044120701c4030210340c0140c24004480e01611484080306202c130064030041c0148800c0d42083d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457365494 1250 457364244 457364251
    0xc060402042702040c12054b0901060f080a0308060d0f0f02010504080706080912030601391a070504051507050a05031318150b0a090b04080a0308 64
    0x184400300c0c01c400c00703001440b401200b6501030700076038607090301842c0248540114010b000346483c0c10002c6040110b00100700e1189100c4d50a0082d02c50b80c3d183c070040c2404090b4410008000084817002100350740703161011040035100d224603640713524010690750384941d00440030701609401001145054100104003100150049002c1c040540c1203c010030345168050701015000000324078800d00600c01210030784519032280301e241c080d030040421829401011107016210940450340070341c2d4052141c2210344030a8920601090161070303558a48601c60b070401324844900c00101c0c510fa1101d0704001d41c00228018100e0311040400d0300040141d4455000e550420200e2030f0072400c060170800402e0310740034a00d4104900d00300200d451420090104103c1761010b034030a040d20307214081030820003500e0125008803103100215110303104082d64580b0074404818519040d801f905407802c020100d65a1009900e00c04014142a01203510120b03103005200500000c8000c010760513984c02c0003040d050000e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457366744 1250 457365494 457365521
    0x70b01080f0d05040b03040305070212010f0209041d330705030103020316060203030c070807081b060702010b0f0103110c160515070230010f27030c031b02060c06040204 74
    0x6220a00030b40c0c1c5c07080300b500da01680c07604007540d0380c2c0024000110008003170350304064150f007441c0c04102d850b1300c590042c000a80d01910103005a62868503184683c10114000e005141d0000402030b110b644804141160101c00005480c0621010443c0b03a90000046900c800445c4000004000310300b4104205040c02040f07103001e8626070300b4464025120710002c2c1200c0084080801c88030240f1607408103d07090340c0c0d44184402d03030f40d6600741801030b502c0205044040725401860000382a250060140400e050401411503e0840540e801074008044280590f40e040105129000c2c0c0c0d03039000c102c40952811405e0080d02c0395442d02c41040016000480d544212140500020005031500c00c8540d605201e43c070750807200303d10703980c0c421030754a4030501911901b0b41c01d00100e050000740c2c0380d12851a00c0320000c5c2085000002903050f11083c21002030040018020107880404207214102542d242030f200300450069000640004029410409012041ea0031990500c4210303d054842d0a124a412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457367994 1250 457366744 457366747
    0x31407030806060a021009050d11070602060a0903120903020c030f1504060b0411030a060806010b0901020c0f0a1503021804060308070f021504091a061914070b01080f0d05 75
    0x15a8020709958002d00100e0055a0120b03030004060b000380884000188003801c1086410b40e603090843c3d450213081d48900100343d00d11000c1c50034030008180740b0140c5046030001c1c0f4980d121510b1150040803090380c00c1d01048045208a407420304140668080d45000c3da000b0842186d02070105400c00046c140c0070400ea82c020310000707409995840d6070680c01900600006914500e10012502070070100d00c40d84203400c400410007010764100c3e07124000f0340e5041801c496a0b683c0b40c81c80945507219500341a809603000d280c441c0344070310f00031804000042c0040d040240603659202e05030340702c05584c00050046500801d4001c0e0040300341c0f65802503014125000d014091560f102c483e007034401c030714014100d425400d10f22b10543d1203420a0400024544100d603a03559030300c0510350700611035a020b010820911050110262825000350750340e951000c940a000c000c01d03030078260b8800c60f8043c000c007411300081c41040081611280302070300074040b51028000044011440e1414000a000c0e40c1c424040b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457369244 1250 457367994 457368007
    0x1141003020f03010608010203190b010302030f0f04140d0f030f20250606080f0604020619090801090605010330030b01030f0e0102040f051c0f1407080a0314 69
    0x40050004898040c2c860450008030480800d0140c9602e4000700e105600000c00c1c081d00c040c1084c00020920740c00402000180800c000440c02d901c030030b07101286008007840c00b0903405040c5400954001d8801c90040e0b01c045480d0b1011400c0296102581c0c1c041500b170341c10595803681502808031080594801004500100c1503c000720140900141c1800304003c540180c416101040c900502040807888118240300e0345000b501501c1180900034030750281c5e0314483c05500c0005031990103a9030080a19045c0345a6035245003110412094820070048000d000040200003881000416402650045490b40c198208480e240c07802c0c0101c0c0c1c0c03010046402502c0941201c1c05841101356092a001c1644e850020040303014100801d01030700054588035030f508000d80158010300849489060b0903410f290f84004000d440c450048840450005031078607400001c10340c4910010443c89401c01001da1444d000980c1e28208654102c5901c80e8031058480c020b1541101d80500044000c147c1e40b4070b00300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457370494 1250 457369244 457369261
    0x1080c0f010c15320a0b0621160f091707090203151f02100b180f1b0f0f070515040b0103030e1005160201020f010f1d0102190f090315020a020114 64
    0x30010028510b0f00e0742c8510407840c075541e507c115441c4445a0030030349062440d04400588001060701c21040140c00020f40c080d080380203010410030340794103840d060006884d200000f40700e07600300d9054040e03030300500401281820681c8050340c000c00a00e543c00e00303148443c0c6c0911500582e017005200c10188d0300000002e2a80c3d0000d040c00e49815501d2010404505100100d4441c0700e101c2081c100c1c02c0314820801c025600d0341810301d8815105840d0840c1e92604400070800360340300b03c1c1080740c0c1c0e00f8010050f211010301c0400007400202d100710100c80e0000f012100c1408550020f40b02220715907150b40041042c5680f0001d141c0c043e200031a41c0700d200d03a5110202400350b20030081d0300c2102841c21240c80c410f580c000d01c01c01c42d1000e8510001d000340149280704e0b5004041103030020f50807402e50144040110700510a503100f00d132090004005000c4071500681d481c404050540040180b10348012000903c2c4a10300041c12421040150702c41c940c07110080c0c01e446031440314a48603a103c00800403800d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457371744 1250 457370494 457370591
    0x444102a05071709030a0c060302090f0a120b09120a020708060105060a0516020a180c180503071a09060f12070c0224160c1d01080c0f010c15 62
    0x3074410020f2240d945100b000400d0802c0c81c0c80300050009414001d00142035505500146415071003115501401800e480070812802d4003401030890400c03c036001c0c407001510342d401c001e400030340c0c1c03000320784c1840f514580414665124120010043c1c0040e08100003911013002803d01610b0f00b107a84c0c0b420070846840050540c000c1c016250384a50703074114503406549501da0010081e0114020b4441d00d49a031001c030401074030390b03802c0020010f01d0100c01d6900c146420a001c0043d943c0c0100548441403170401085140d0050444201c01000d040009800030341da844014081c01c0d014003005900e40d0058000312030000401441142440700d1159010016a10550000c0749860700c801c20400c8a0321616803030f581350041001850034400891003010510000d50103031011228180c2004e03144e41c07200607554094140038401d40b0b00d40e5000d1802c1a040c2e140610050203289818500800503080d52745400c00380074280345512a8048d80ca98085c84054180c00712108035207280c0c0c6140da0444040740e1b1403000e2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457372994 1250 457371744 457371773
    0x30307060b060702040f1505030303040b06040b01091d190e15070504030b100e09030a2c03030a09090518031206010509030d03020444102a0507 63
    0x40e030358500340a002540c400c400d0728040c0f50054000c115605112035403400508001c640c002000340d030504001020325002048030302c03482c2d0003c1121141d0326040180406054403400c200c2c18002d144102092040f250291f04c4c0340b40065401041c41410301c3c205280b50401d0250010202c9420715484081c405400500000d94500c4900c1d1342c0090381d900b080844017801a41c00007040250350300144040e00c00c41400000a940d006042c60800380c548090300d95480c480c44100e680403a00c034100001e00843d40a041e5184a120340001d90b40000382c1000003402d5520582c2041d0118603c6d0409001d0812588205a48850b100c00d65450407011021a160780e4080c1d0800b03842502c545500003a1141d2054083d034030a14400b0341200c005401c0024090040e4000340908103140c03045000a00d006010200c00c1c1c1c095181114488840c9611030408c10460144060b000d480c5100700400140858002d115000342000140b1030755842c5014018103070184c0c0880d0200b802081000d0014a0101e001100711414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457374100 1106 457372994 457373003
    0x7080f0f12031003080c03090d053004140310140727032a0f14120705011d042d0606020d03090203030408010509070510020606030307 59
    0x124001100c403c400c42034101030070030200d0803280003084412820015039240040d41c102080c602400e0030401c44460b0b0100e03404203440f65154030440040e4545c1c400c072444a840000030b0401601940c010071124803440c0288000340d5504020703d420050740500213200340d0300c0ea0744142c4840e14089480101051040c0b1000120a00300c041302540d1504201114010b01d0039034542a40b04490483c1d1110038408071804e804800417105000002004d1188046880c5400c00921044254250200a00a840a0a18a405000208840055402c00c3c6004c2c442c070709002c2c032250642c080f49003062750040d14180031407045e07403102202070410000c010600b2015003900c086100490b60240324001c0143c1240b48900d8040b03209030441900940024200d07420151226840c0782101c40581d02103000f40e00100c810001401c8c103920600541a10f8005410503140c09000703e42c5910078103c00a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 457194244 457374100 := by
  have h0 := BRFrame.cov_init 457194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457194244 ≤ n) (h2 : n < 457374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
