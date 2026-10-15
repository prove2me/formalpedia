-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:02.293293+00:00
-- url     : https://prove2.me/submissions/72bc948a-a791-41ad-b168-65d62d0a5f83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735791366 ≤ n < 735971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735792616 1250 735791366 735791369
    0x1270305060a050402030c360106090503060103121b0b010b0304060605040926090a0e04050d08070f03110403060510150f0c02040b040b0a030f060c05040503100e0106091805060a15091104 82
    0x11400d4243c08e010200c00f60381070003405600c00090341818002010710300012a81d048039000703681e80244c02d402d44000c0341c940140c86201007030008141c07200c10005603144480ca00070701c0000485a1a81451300c0c2840c1035407040d038816407045041c240c5000101354a0000603a01c451003070958880c00318141ca54541c03a015404500e640003440110004a0311440c6070f0044c0304030301c900c040d40c08081d402c5001740c1c2c145905803240030001d55204028072010380a540301960001c80390200334142030b5281d641000755201180c1e41074182024200c00c0042e414200b001c2c04158415007803903d80010081c100415001e1039920183c4a076403290544003560f262580083d85908014001c84020b42e2030781001022544070364402c1710f44c2c51411402551310340c42201901d0503214003e0207450781c8034062011030041c1210b1140035880d03540e203220018880d03184d40304d82e50f4100407000c11404900c0c0e240c1070003402d00d54001e100010300ba0420600d0741d25a400e11201d1070554084c4a03000603030f503a07480080203050155 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735793866 1250 735792616 735792679
    0x709060321030e0109050a0b0a020703210603151e020a0f08040206040b032502010504080306040f0f0203010807060e0a0609120c0e040b0f06010c0c0b0901270305060a050402030c 78
    0x3d0176580824410003280001d59107000c2c00e2500c415458030b004907030407849800005400100c030b0716021111001c80d01c03210204186821404103a040d05ea455006181401e07202840c1c005541d034080e60250128100c05135050b0780034510460800c2c0002c01c01509507841155404104114031000904550358034040d40d020b0000765052644914080e0420402a08103640c0940650b0814048031020351050145500c503540c400d00b42d03400c1d901c0348014080078143c6251000100d80e2070b140880c0d60072072244040c50003040b40c6001001c199140c228041c00c0816400f039440d0040301081c0c41400481d0304120550116260300c01c19003a2140340c2d00380305c218240c4a40000c0000b2004006000c24012119441802000e6a07100c0e120b25440b80d8005591401202c00e00500e0f04640350010881030400c80080d002400b0181407038403400044142c600d125100c088101900316072091000d10034403208100c980d13030101094038200040d003040d40002e941c0f0310400701e01350b00c103540702900c076030b003680c210581e84910401c3d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735795116 1250 735793866 735793871
    0x3170d0e0703081b01050130060911131401030f03121401230d140c09190608060c090f0d020d1511121605070c0305060105030709060321030e01 63
    0x7180c0c43d200d001a0310030302d02030314a0718002610406102061080e02c0c101e41e04041c0740b0750042c0d0a0800ba62400c00208650800180c04600040c0411668001c035074074184600710003805002140200001c10b9444403c3d00c3c03082c1e103482000400844244003050540ba0010034015905a0701d00c0c0440f0716800e400140115917080103411510f041440f517489043e2540b501220b480803070544240b0b000d0404070300344603611442d081d00b002d0120710110444040b6808207000c0c0c0d034045080e01d0100d01800d9003968409801c030500361103030300445c201e03100c1c580c050300c8000041e00d80c0d400c000c02007204502030010014030400e0b55000404203680e0740582c0403c03a81d806813880614030030504201c440030000d004001130903420032411400400d106070840f802100c0301c100d0032429403109140381c40e0005500f07100b4400d0040401001011660610304440218421b200808666041c2010b05080001541c0b00300034060606c0c405000003008409409061103111110b45141c4501d000e046011b0030095441004552 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735796366 1250 735795116 735795119
    0x809010e07120c320f060904051005030f0604051e0d030f140a020706060b031e0c04030614010801200301170a02040e030703031a21100515100903170d0e07 68
    0x20480102c0c104d9040300c40700401c0d0082004001d001c200d441e0a092643d11100400c0700302c2e410320705a803020340c001d034081e81700109040d207a20209184c03140000c6010199071200040008001d8208171114242ca5170850307030344966039004441e03591190340c810140d09250300c071144030408900307030f0340400e1001002c2141c038000c5050110901c070095103c90000c0d50a181807000104488140c4800c80f402002d00d007210f40c1e4800381c0c0d26124022040094010400c0d84402c00c00007020840502550144001c507014034043c0d540f502111508540c01801d01140c074005910b2844601900c1c401581c1c111641c0380001d1440c8036003005014200110040025841441c5c019080010180000a484807501c80c1d2400c0203007200740305510780c04540710401c15030b01c44025005d0040200c450684015000303000000c480042c3c41400782d0006481040f100602101c2c3e100c01024103d15080b880300c6c2c1c80400314282004654210b03110000704141c0104070324007a0000084403540ca5089500c60524945d50310142c54506 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735797616 1250 735796366 735796409
    0x2010b030d0915020c03030d0209040b131e0e0316020d140d030c020f0307060c0507080f0304021003051314070506031e0709150f20010b010809010e07120c 68
    0x2c0c0785a01640411194011500340b95a00004000c4c451101c0100154242241c4030350180c080d5105141241c1c01caa154400b5101d55110381d440c06901150010021032180005007420070882c24010880c00c0c01c03406d08540d041790180c0072007100c000c00d440d40107100d50103a65001081c00b100d440d03840205000b0000710581c9011754041030646808215640521280d40b20200403079071103258214001c15500100302000002d07000d6881010921020b00704581405c0350f40c0c941200ca034100c80100030390001c00104100441c81c02803d0000e032100c0508080215082c10820021464502c140c01810340020046403070351a1410044180144001042290f0740d2074540481d280054040014030752165582c008030390400d01841c1c500c02036441100320b0540f05e0941100071921080c1e01f14070ba0003030000b11f14442d07400e0304c4a0914198104002c0c4004112000e031000010076455009160000d00c0e45800c5807111414030120301602228040700c05460b04411609140d0300c4180340f98040045d582e414207058100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735798866 1250 735797616 735797627
    0xd08070b060a050415151b050c18040803040f0204020f07030504030209010605092b061109030d03020c0c120c37140904210c0213060f1502010b030d 65
    0x192400d41c0c00b00e08196659003440241c0c1c0002800034000800c85906002040c24060030482840c91450100c41028510900c0c0c1840003a40505a07111b80110072865002e050191402240c0c1018120404444c42d1580711015a8000540300038400589409200709640d00d507010b803042080140300075943d03030701c0c189405051907110780f2049025540146c00016850300803010f4034a070880c090190880c0481c103040c001c0c4040c071880e0040903903001203945040410300520900741520482650755603962182e03010907180c56280d00d11401014010089160300103400301d4030420400c0290b40b603240e10003103800c0302030401ca84545c1403604080540302d44088020044450700101c6000306c4422000c22902144050014460080304078906041c1da690019081c0150303515801409255103540c0c0d00e0024000001041c6200c04103800601580758802c01c2d454040d1900c40f104000c0c500130840140f40419800d042d0a1611503000303441142440300c50007038001c0d080b85081c03403401803c0d103040005210f8003410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735800116 1250 735798866 735798871
    0x312060509190f200703031808030906060a0b0f070c0e0406060510080709060f020c0415140402131203050c010c120c050327070305010e010522120e0d08070b 69
    0x941e5030401502003c0759a10b8860251100c020000c032003407007036010f090301180b0fa20880c0220101565007018141005000e420310a020748103a03101543c03400d007c40b1007494100054030306803080740d1072401042195041d100329003039039081203041c50f103682440c146023500b9406030744903030110702c625003c020400a84e41d0007035042d50001c66403011200951141141d040c0d9040f2405404902022800d22000d401000c40300200d000610403a11500001360109084c0c525481c0041803001e43c1400c14094103e43d01c4c0980030318441500c085080c00c078104110810201d86106481e940000c1040701d40c00d26100d042144c002c0c180f442c000741304003030304801d00800c01c50070105544000c6240000803044540b10300c08880c01107180540c0520303805014050b48081d20700c1112040c1140c8242d800001c0040c40a000d00c098142c44040001100c0c40c200c10300076280000700c038000c40ca200d440d1142000144014030b40e241d04021514100c41e05422104c003054180302140f50140000b100072071044100100204140d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735801366 1250 735800116 735800161
    0x150f181605041b0801050d08071b09110f1c020c0f0c01080106080c030a0c20011e050103030815040204050d0b04140610060c0c030605071116120312060509 68
    0xc4407071800e0382c003560061a030f52140c0008859000400c86407070300d0440b0850300c034050480c03140342c0002552028042c00b810034401c0e19148000b281088442e4440c40303100d900e043d2801d40c4910300702c034409520846104044c0c8400003203c6540c182021000d55134191b592003002141202c180d144009043d030f9451000303228050005044000104e030b514480c0c61a9400740001d00301290954a5000c20a40609460603040d41040a0034941d608000d0030016188020050310000003200b04100410101c0c2e1400500541a07107820310380108000f9500690b060b9008047e482000a6000500001070203440340340e22603135210319102071050078072076000051801148940a551050101ea4580680b140c00441e04003108611190341000501d0150305400d166610404030300301c000d512550345404a400c02c1d142c6d1030008461010701c1c03a18007010884619084488000380402c140303040130110941546d0b9500400700000c034401413607001c419800401c06800c000f003250849c0d1034080d8045c0e46642c1201c8216 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735802616 1250 735801366 735801371
    0x100521100e0405070915361d06180319110a08030105030f0703080426031b062412010219020606010210050c040608041b060507020a0503150f18160504 66
    0x100203c1079107504501120b41c046c003540880e2041402c041100d8001c90100f031b003040140610300c2500d40c418410786a106d4620010190648c4698401510307144004103a022401102010501500b400200380e810244000e01264118803d00c07108455003008143c680d4070500c21141c2005c104101c540195040c0e5a042e022580721503a401100750b074850b4648805004268108400e00044d59050400c048a08030400c2e00c0728052111500b41e8510350126041030b08640d040000202c00c00d00c144070b041e41102d8810100c01007070340d10703c5415001c0700c01810202c2c480c0001220341e4603400820340650b840100c5489d150340345a49000e00103500c5034001c03940d050042c080c1c1c1c0e5202e1824100c82c0f15a901680d120184c081c103040c00d1003410744100030081e00540c0d84102d141c000e0110111000d4411029003d507070748854540c54548140022101c040e04454420703007100c507000c00e0801080c0a503030352103504521206459100c6828401c05001280b0548065000300854410003a0311000c9102c1200c1d41602c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735803866 1250 735802616 735802631
    0x1205070306240905100f03050f0706110d03020a0e04021305010824040908130308130506071a040602090a060905120705150a03021611100521100e04050709 68
    0xc810b00c800c111003075224801c400c0100340000030b0994802d40c0d0022144041c03503181c0740c4400d00c8020001c5a6401102e0552003a6039421200405224100080820741000701806829100207511a54900320820805030701048122031580305064182c5444400f80c0115510308803a00c2d20341c00c101c0740340122800b0644600c042090030606003120407040503000034035503040440204010243c030a040c000d40d0500400c0c404142079248680030348000b5171180e42d0107a035640c0910142a06450640d000501c109030034018200421840d4800003420f1600010310000c9640701c0c40d04034028001c41485175080b1406030b20103c0c0305a0044d1051056850031100500180703410840d4542e107401a008103600b28800942118406c0004400341426880382d05000d400c008a003058181c00050340074058030154030303440f000012410131446100c3c582c020342c070f0004d25002c0a072441d04a54911001007001c05448030b00012242e1031040220006061140500301850a160800341e40d100380303501620803224501501d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735805116 1250 735803866 735803891
    0xd080306041d0a170903060c0a09060e0a050402030a0912090905181e012009011806021905030c010203131202060721022a010f05010e0609060105041205070306 70
    0x401050003000400200e031aa0ba00c00802801c01d07046044c4842080c0003a0b0a255818031215110b103907946807160b10ba0501d144010401c00d2a035114000744410304544590702e440303059642d4141d550544000d0b84e41d480d0b04e06044000c0a203008007400407040b203c0d02110055025403420100d540c00340050240d034580c8002151040000c185d404820741c031021003c4001c00d24030f0850403011540e10000588801c40440e0240d41c01c801104c112501407000911403065a04180c8003000a981c20a280b424242442d1010f50b03100c1c2c0340c00101686104041c085130400000300103c90484861030025516810400e0b247c0c14460709c070600c2101c035000c02440141001e840020154800c141c9a0350740500085000b030030190702540d4624000b03000383c0030001800c000010301d04170000d001001214100102c6110100d41c2103c582c1403018075854184001004903880c0400c6841c2c112000300c80301d035440e40b41c913030060300c142c0b1581d4000312000c070140e0104c4084c800c1c0491035800710790044400b031141029014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735806366 1250 735805116 735805151
    0x105010e180a090f0f05010527070b030a02041206050402010e03030f0d020306010c05061303020706020118060209031908070b07110a110415091b03050c0703080402010e0d08030604 79
    0x40848920100c50030002e03202511541000b01818007036408402000020381316030954065070b040c00e4409079100e07400d21641c895804e07042d008510b0022000d00c41e1101111280d03031103d07282e1080d080b400d100400031550720100c0e0343c115030044c050844910580700292600b50f01070071044038142d010484d40551080c450074003000b01e80104076517052040c079051183c00200f000f5003010b4480c80c10400703030112040004108000080c041d9030b80c3c030001d8221b1710551500a1904070349400000c11a4142081981c0c03007002480240c0c205580810702589810010340440c1c5064070300903507000b503051180760900c01d20146500900d4524022400107019560340c0380e0980d400c4150448030b1000340d005449080115002e14145038a00e0f074002d00125038850200c01d00030f10380d86d41c0e42051101503640c03076070a15000414102c90a14070010708090019281402e6012440d0280090140c1400fa641c0d00150440e032141c500c030740703155000414442010017581001c030b4564108070b07665400f440c80d060808081d80e40ca170 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735807616 1250 735806366 735806389
    0x9031b121c0309030306120305070b0a151809080a120605060f030a09151b080609040201090b0d06081e010c0c021c0503071e020915010c0828080105010e 67
    0xd10607400c0510350300c0710840c0104541c9100740c081580e07400000c00d0038a401e11803244500d00a40c1d80d55101d02007030510040d44035001d0a4000c041c1c0c078040c841d09c0d0a21010b00d0420460704156540b0342007519110100014141130900100743d03540008003404e4242d045070001002c10510402044242c0d141c10509c8030b14410901c0c05560240184001070643c030064001901152161041803520b440210008082e1007440220b00c6200c19202c5441c150554802d00550703011204940140340c0e401c264002034045455402500c3c0a0003000030303412010806074119400803e0440e08a4504e001180c58549007105c69482e000310550800050403500740c490145500c0c41078000f4000007085600c81c10800302c1502c135942c125400d0200340003280101e640101c00d907904860305c98505601104070320400c90100f1000341103a045e500070344600c180c240d90003074910040d150702c0340034103030384840e4003040388119000722103040380f1914a000140c00c42c03079110358124101c0b64280ca0703c646100a01080001d001d054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735808866 1250 735807616 735807643
    0x6030f0e060f010e0708101203030e010e030a1701120f1e0b040c090c0929040b0315090c3010090b010c080708090613080d020d08040203060601080c09031b12 69
    0x503050b0a20140e4440d68108031218420700300010387d03441c6c030482c1a08dd10301050a60609820204401008982110806c40b8406071031f010b03609198107100d1400c1c1052403c000217400c22007001126010440c48840110003900b1035401560710310034a2400e48034100084804440304034690b1800660052035019035600402c9030f45450303400600f071450007201000c8401051a00e4a4080039507513200c0407920082002c0c120740c0e001a0740d01d140445600a119406504150003902c01d0300030000078101c008140c4110780c0104200e03040c3c07a40180c4020185e1078001c00740350815600c080c2444016110307042c0300421109a06000d010024241c0010354921000040c09001c65208000b20300000d04c3c4400100030380c0e80e000707105508203203e039200000c50a40a4129032003e82c03000302455000c64040150500f45d2925203801c140b1450280d0100380c88000150280d8140031044002c610070743c4411080d102c10280c040d048a401c040c2190a410504403540c000740d01075855461920301458010802c0720844c0d02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735810116 1250 735808866 735808891
    0x706050a0f05131401200711151206190603020a1d010c0201031113030c060206090304051302031b0307020a031b0c0e1801060f1d0103020a06030f0e060f010e0708 71
    0x215465418404d10340034100d40d5155039410340d810a114410a40016421008030240e450780701ca881c4c40c502940c07098102d28842d040b440541e01d600c030007000c21210b040151903481300158841c00c000c00c0d888040c28450708032141c2010703000328034140d050303001c0c00b91828a03564100d01c0c2d0800100300b0b03002c14031030b00807540000c071608001809540a80c1060003510341080d6090701d0000240d020100040640c0c00c104c940d03a80f20802004030039410441c1c05d030000e110768061403030702d86042c002070307502e2040040000c0300c1500440000c0051000501c0d4448802c4103510340c1e0340c0e134500f441000f03407140e20401c0100c0c040740466105103a5030a0310501d4031041030f48148100041e60900e21045d200d018000d010f1340544c400e00342d076001401700030f0042500401c0c6400c2d61040709420040e0101d05550560190941200751000400259441d411160100c45182c240040ca110007045054041c000d48601070725a44140800e0011102c0c040b0399941c126200041c00017610b4071600011680b0035002d81c5c003040c0041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735811366 1250 735810116 735810151
    0x1020d0212100803161a040308010315060f090e03070203070f2c13020a0f120303050c032e091401030203010b090c090f0a05030a0b07031d060c0a0c05030706050a0f05 73
    0x5c10806103840c22801820400703081c1419a082c0740b1010002c6400301c00080160004004201c90034070301064500b110036040c86200c0c20030440445e40c0c415403040e650540e840c0c01c03142100c1e6200b8000c9031001500501640c00d5a5221002c1c40e1000c4001d100b2205410160200354041451031001c41040c00c0140b08515100c2d1189244480006400c06c1c0c10303684100341540001e035101d400e14a51004000c010b1200b842c40c0041d0801404484c0002d21342c0c05100c3c4200304200c118483c1c0440c204580010003418400c44400708915032110509070084070340745140041c01d60150745100341a41c1200d01c00c50003070260038012010300406401c141c030010318042060000b190103143c031210302072180c000600840c4d5a1961000003a00e8400141c0b03040d03c00c80e0788030090120150340750158607a0f13001500d140a215241c20080e4aa440300e0040940010f6940803038505d40d62482030358141d00b05a000b1045070b45922103400c1a0000f440c0503a000740d421482d110f0841100310103802040e00c1411204000040003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735812616 1250 735811366 735811387
    0x30903020a02090a020405130c09090504050309010f020c0307090b031009080d0506010302070204020d09020f03160b0c0102040317210c0a0509010c0203032d13210501020d0212100803 80
    0x8000342100400d01d80a110111f126158a103050f00343c13280010005c50120b0400030f029064505d40d8201e6402e0394284800c100116500000b100c030600c00070710f041c1344c07401e548620880c181031116a103241d150142c1000021101da0030b070008011b800c012400d55200e46040c080410444200500041c04044180000e00c00407a855101d0760340704506047c0517140010070781c0050100d0b80b0551040c0c0540d59102d09146c02e508013508508500c050a80043c0014110406100e01100440c49200c004183c001401c074180902034050380e004550180c803000d807015034640e200b540c0b030300b140042800b080000c06e200c4800c5144500ca160250160b84d80441ca8000f8a80f412101588649541818805c3c0d901c8510700580301003008154180d9001140e180c042140701e6001951542800982c9600405010140604454074a00f208507007840d00e6044401107007040d9030209500a1501818952003c102d8840702c14135a001410b20145406405070946d859070a0030011050a0080750380660003484a103585 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735813866 1250 735812616 735812629
    0xe06010507110d1a060301090b060d051606080115180303050304020f12011e0e300a05040e0c1617160f050c090108060402010c0602120f0402030706030903020a02 71
    0x1c481c06290780e155000d003140d000c58480030508a044612505122034000c044d0148001c403a040b0b50b0880091010101075200e4031020f44003d4000b91041c0c070b4510744002044000c00c13000075000301c401c940c0c4107101e594a1002d030101c2d900b48528031500440615403003c1600c1001428007071407911800c040e04a0035506c04490356000103100302d801011911031384200c0e50302d05828100480c604000454440d00c2e0090384040b03840d49200094041d814045944280c030000310301403480750342c8103c159504026540d804085810705a80340310260304000341e0400d107154010010001e0b01c440c41c461021940b40ca8204c6005841050005c0306c8201029003030300e0005200102c1e14801c0400b0700e44a0b400d001003041e860000c40e080390300454980d82e002c0d43d00c100b049414804850030b1141101c843e4007540c0340c14025616450000e100904111411180c0810840e403a4151800580412079007101482e00c1068200c41003001e4509074407038800c0e9034001503120700c1f84c01400100340d4154058124151190300b441350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735815116 1250 735813866 735813877
    0x121112030a15180c02010e0106030c0306200d051501080c22090608100f020f0d32040b01050306090c0f04090512041d0103030f050a032c070f0e060105 66
    0x1408520100010003074034a454155241e00c005500007404551420080d00b120540d88042907d13074100242040442c0d82d0f00690411aa0012008280c055541d980000d45c2900700400179428840855070b00307a0843c0e1603001c603100c0d21104031522601c407510320056502080459141d503030342508004045e0000c000012000401603103141c0301c0902a1207413048010b4901a4019030400d61091030b04030900c20340e600540c030b840925070100714504802c015865140340f00b0018070050a5846104c07440c000064608140d101c181705000070072401c090720108080d03140054070140d40c0804540c00215052501203a010302840c41c100c000c004502084081c040030710450400140e003d030303a60034a070300032400610101c2c00004140c01665640e5041400d4890a080d501840580c081c405500600029402c03c80c0300c988481c1c00c1c14891b84509607668101d01801380c010043c0c0b10062040c202c01c41410b40c3c512030001c001210030658906940300c608460607558035205652500e4082ca000c1001355010700c00408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735816366 1250 735815116 735815141
    0x32a160204091e06050109091208100e04140d0e09070e030f01020a0f0206150603060906210718020c0c0909120a0833010e0307080604121112030a 64
    0x340b0302400b6190040540402c0400300e401c1d4036940368100400881d0311401d809029545401c0064060584851041c02034140c40c217801d0107205000b2130704100001c2c00903401418017000d1001c46180c1840e080d40341f403240c2d808022003485070200c0c84901d5030107403013134089000c009411440140e9072510119601159444001e4260064074400c1844000a0008001519298655503480c1070389004c024503001c00245000d03214881d1044622096442404603a00322408440a142544a050010303088a4600308014420f03840311540d007a5899010441d0340171a404c1003a5a0492a10080c0d414183d20852004046030f801c0100c80c80c6c0da40c0380000405401504a104460441c04240105181070303018407076210104690500f0402d002c44041d0f1004440c410301d407601502401e50b039202c1c0000c4044090614180000000740500a4400704040e00003803403a141121002d060504204a103120040483c00004d4202c02d0702c2c85a110700014030050300c004074500d0629550390b0121081c01001001e0085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735817616 1250 735816366 735816371
    0xa0f02040c0909112101060903060b060c03071101080a2304030507020a03050c0a050a081504080903070902030f09150114030703020a080610080714040f060b030408032a160204 77
    0x41907a9019128000c040c444900304a41d031038000d14545e0f200507801140e410840c425190040c407016a0042d40203040b03980c0000c0214118100380001003190080381c81440092001141d1602448005489002d0f581400c0e202d0451603141d00348241c1c1659410b001c0103842c50f058040309559403405100c1180d0240c000d02d00740d42014425400651400310305da0050b80c590b8451107142d0044c2c6001e551010040c0000c03a80e410300e840c5400c4c109600e420407802061004d01202e00002d00344030302e40b01181d511940080030f43d04031545600504000b904261074480c0e41c1034961002034098000050360020210001c20b0604841c0e2804021084d060746005070036806010341e203400401a04d42c8103200d4081d01003003028018a16010301c03504100c00d001c0e404401103a2014208200410400311481d02d00c200640d0040b404001a801d841e003d4000c40c1d00085040100004000c14001541c02960141240c82000038000420202d100070b00004c0700c00010041000308015070003120380c220f0385580184081d001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735818866 1250 735817616 735817619
    0x32060c0a0312090606030c03030801090207020901060c1b0b040e13261e0405040b0108060a0b0d0204150f140903150619080d020d1d01140d0906021b0a0f02040c09 71
    0x5003002c1d6040c5d5442203c074580c902200388105074103c12114050180c500e01141041d00907000642c9150b01803203000240118071495400340f00b40040e00c1a103001a803182c107515a80d41e5800391030340e0350051142c6c5950741d00c03030400f1404102c05030f44400b0051380c021042000c014100300803c0c0e07140d04440807a03801382d6002c100e0709481c06c0d0006a031044c580302c0646401d8031140f0f010140300c159200c1e0000d0314104035980d0f040020300c2e5620812001560035440f01103884641d101007180003441283c120b624602b10010300d108015511800b8103044402035901c0c503040c0c04444800c01860300403440c41c02d40c035420581c203001620b84441e140a511000081c00034080c000080c442c0c403900c56480d00900c4032600220100000c980d010007455914000b14540400521501205960307c0c0c0c0c0740881403070400c400a5400d401420b581c2040d1040a00e2200c81002500d4507854403c5c000d50003100402c0d1549910300811014250206075411007681220b01c8000780e00c0307103902f00300003000e110421809000c0ca5900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735820116 1250 735818866 735818873
    0x30302092706130516120b0d05240106120c030605040e01200408121810020d03050a05010b070f15020f0c070f0812030403030632060c0a031209 63
    0x10600348458007401d04a8942c14040103000303035030300018100d99400f03003003200344242c0d0354420143c1c100c25111490704000104043d040e140242c003485055540c80040d41c42c0d81e8040c0040800c00c64404800c150000028582c00e406070880d400b8244604004904042e80c00307000c034031640c0c0104188103281e103070003c2d1558560000808031006201c4030700d090ba64402c90b4000a01c219640c802c4c1c170444541c03007035050600d000000f50b03030340c00f01c0d2050040d51b800104054401c0d04104445801e05440100480e04031030310418025600d072840c810380c01c0060b080001260701d40403940704144c1681c01c0c081c0d8031407800d40c450300c1d5040803c618105c00c4620608280c0603481080c0030b8405450b95100803e990342d9150f08128034240360030705e550442d6884002d40d980c01c0001210000e0034807080320291100a440e42d40d517050030750080c0b00b070340d00c0504045031502c001d908601c017140d080c540c45408100c02c0c0459a13401000c0c041c090264580385481d43d40007000d10030100e801902c046c1001d0b5910f06011601020303d03034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 735821366 1250 735820116 735820159
    0xb100506040b090114251103030412200d0201050703021c05070302010b0312071e020303280206091213051f020f16030f1109091011040f0303030209 65
    0x20b1086500402c0400c41d4052503130300199400217488209101802c08906d903981c003418100828017050003034500c40c100010000b4915440d0351a0307000070240c0781c0342e5558405001180d0744580341151000c0320030300710302000c032828076500b00341e038034080c081159801542d4019102c0354050351098056110f80034440f264012070324801000000c0d6542c50944508652070040d00b9146a6110309101e41c0148a900030305102c21b000303507494140c0121418544600d503603103401c107076000000080d406010014020709007000c5072030a164900c412802094070b5050140040341c9801c015a2915250341200c5124405c410444c0d02408013122000e0b1f00c0076040d81e4420000d944a46001c00603034003481c2e0441c140309001d405024145000c0d072803502408101c402e01d0603540c5001041d000050a00301281806414003100140c5c1016501001d45200018240b4600c0503a071105015200080319080c44040d8100b001c030f00301560201e50005039610174241c01e6950070b130301940003480c6881d0022148101d030f290315582070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 735822616 1250 735821366 735821369
    0x22209080f1306031b0c1a07110c1518011101020c0102040f05060702090105060a030b03010e1c05250606030609140105100302030303060402090d1e0b1620010b0d21030510030b10050604 81
    0x15110f21a40c0d034400e078050f9080c1100242b41c28400d1001d6240c40542850407800c0f1180600100103440c0440b0303050f801a41d4140c2605010640c562020030306030a255415401013043c2c0306242aa074105a0b41c1e00e042206030310617032000035007246020340102324a041c980c1c080e01d030003207103130070b021401038a80d001090844911444e10030440c0d00c14044c8400307003040580d10304400301035450203074542106100a06c106040340c1c680d000c3c13050f800303000400170321007982d10840207941d002000b803014103181e050580d0800d007241c5084255501e00b20110f5510340c02c1000e145d007140c0d4050040c605590b100710403c0000c0d0071407280d00c2c0d04404403030310003000500305031904000707050118004503048420f03040505c4070400080000344c400c2000d03868003a40540000e08060706881600003030324240c54200303049024008c103480160b04032452160071020071900c81210041480541c0020601e01c00045040702a502c0948001424a080740c00500104110300d40007640f2592403000c00303243c1c0d6079031800b140c8203a005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 735823866 1250 735822616 735822631
    0x20f0904172110050a0308030601050706021603090602010506182a0c010513030909051f0602030912070302010e1c1a07030b010c022209080f1306031b0c1a 68
    0x2000c040d1001d020b01c940e0558101490b80c0c0d50804441c10000892004940e90001070007108000c030009803603a02c40c0048032402544100c0554548018034940c400c1e40140e814110701280c0340c0700303010070b48a1052003101d01c80c000050003040e8900b0240400d8040050150026040ca06403403102d55150013060f14504048002101d150b9171405444221421a030780600038800043c03040c03030000c02095000390450141daa0b420360005607602c072048000c121142c42c40c0f003154022094080003030544e8000c400f402c11f422044d5100316481045d850001d494107414080280850640d5003008091f0500d4003035442000e03d64905001684095218002c0d07000c925545072080359102000c20051036810b014030551a182802e118294007030550000d281916030329414850788401181580f483d02da1a000704121a410207161552040151602c0046902003032324a003400d400141c1c00103089129105105d0104840d600c20780400c01c0c0c0384001c841840c2d01d03240642d055a070310204540f00e0003140740350b14041c0c0070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 735825116 1250 735823866 735823897
    0x418030206040201120c0e15190e18160e062b0c020613060c0216080d08060d110d2f040b030d0207031101051204060e0118020f090417 59
    0x5240c4001841740e600021650609403d12154109058101d000e00003030a03001c60304500744044c0e99890400c42d00507510301c040e0490340090700d01509500192240c0f0100000d0740d01d0000118010b01009036501e09aa02c034840c034940d01c00301020a03100f0420707845a4180103068a02c0e04a104c400844c030321441156041c00c02c7d140f03c074100c0a281240c45650450350131350016285e10300d04164801440160b41c01c02500641d2500f00d80c2441a200b40020b90098180000d2403030165290b180c42c03541e64042c8040384020030104c0003c0b80b01d038034100a2402d1460307030062803084420381080900200034080340c030403506405001c2e8143d100c0c90541c2012012458580115095030300c004080009450000c3d4080d07002e50400401d80600d103501007950f00c1900e0304000c11402c5542c00200403222842409240c1c8554150b0700c0600081000070b81000200c40f401c40000e1045c83c048440f600541c558049000307500074001d81041c101810200615039001740940e1a030b1103407900021241c8070341d6025038080c44400c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 735826366 1250 735825116 735825121
    0xb030903190f230c030c1c02120304060e0c0406091416050d09050703140604050706170f07120213030215040803040303080c07020d0c060f021f09020418030206 70
    0x250140c8a60950056407030300000b5000300741c0d400b410110703510707000079200340d10058581d032800701c0282250078440b190310880342c0e5011001400c5480c1d2140f01503500750440c0543c1d080c5481031000a011503108c68480e981d52540d121a601c0d88000c111188001005000c5c0307100c40d099a54803842030400400c04035a002c103421b11030f240300c1048444010705480100c0802c0307581018443c0d0002c00d4400c143c0f000c443c009066070341e0741011880e0030540c0d0b100034251100c94240b83c00307615000c6181c6004500c10300454803001d44890085e00c2d025103420415094400410005446058031000d00340c010a441c04c000a6629a0f0200d07007050343e101450410000304400380400c21401d24000701414140c1c8402c001d03083c13a080920039900e0744510f1101504016421010822041e0b034101101c1805e80d00400701100d1201e035150034600700001d80300e00408030b0a0303841005400c0b4008211518041031203408a1640300080401e0001000001001d981065a603e20320f940f42c600c600c036840d034040c0a03800611851 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 735827616 1250 735826366 735826387
    0x60b03012d151e14041707150509100e0108060103020a26100e15060901090b0408011e150303030e07030203030d050a0e15040b040249050a02060d060b030903 69
    0x1c411161080400440c100d1284d400c0031030506403416107804041380f12255005503412483c1c00e407a070b084400458443c0032040342c50b540140052180c100d0a450703c80f003011503401c2c25134240c0c20100c0c01502003115440011819031003a40200400c0c0c065007000406003046c03e10805040486201d00807050002c1014400903080262903400184074039240c001251401034505619400b005008500850000c42c060005a00520201d4060f000c3c8041441d20350755900b907003501825107603039684011902c0b244d08040300c1d01b0318018000c0c2c101602e41c40e150901d1460703400701d00906100541d0310702c0f4000c000c00440141d405000030194184a00c81c0401c4c00e0401042d41c004507403061003000c0c041e601c00210320404c400749103003181e8003a4005c0d0b8000e803c2d55550001c0307110851968007004d540f00145054a000101d40da100000485454640c030007402031700b4084000a88034401c001e016a13210328000801441d098000b810741d96203a03200030450310340c1c030209409140c0007601c0007103150b0408103910300300d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 735828866 1250 735827616 735827657
    0x1e0403021614030304230619170c34030302030603010b01090f0312021011070501050705041206050a090b070f0e041b0503060103150f09060b03012d15 66
    0xc0c182c402e50100e03080341c0341000a81c0e00d2085208224400049602d42c00a002a032803840c01404405405181d803040f4010b400f40c1005401701d016000700744c000a0180060340d020507031501c680e61040e881490300c007407030b0510340f9403008240d55101d8803900900d81c8800448030881c1004040d00c29200940c0302e040800400d404d4440048030181006100b035810020700300e10160000c100ca4002000c00b00100442d8002c90620f03800d6000007529600304048019080f044078014507070b260007240200042c0d2240c1351f080703519124503c40c918001c2c81850601c40820b61551182c1d030050a1160006144280ea5440e517003d01400c03039100b4080382c80c0d0b40c940f0f0b018540200780d17650001400c4400700052118a4210100743c3c1900990004000d030100011703405074041d0303028120984030805490040c950310028005040414080d0002c0e80e4244500016501000c42c25241600c000f010341d0b800401d0580a01190400d0000c080c040710030f142c1000141040325182d8200c06803025507102502d03c032501d400f0f02c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 735830116 1250 735828866 735828869
    0x8030d0f050c09010219030c08070c08010b01020a050c1210051f1a070f1112030319060f05010e0a0b03010f0306180309060e180c03040c05010c0b0a02031e04030216 72
    0x5a030340c080002000fa607034045094044580c032445c0c0c045004c42c55080448103010f030f10f00e005190140015410003403061904404080b2018a0000d000384002c02004a03195800340c00010700f50741c003c420b503c0341854035400041000794140c0803140405086c0b059001542e1043d035160a660603003100d214104407040e004d200c0900380c2000030300c03103d2000e50151400c510070641c0c09820340c0c00811880c004c10510031004013200400034641c4846044a41c1ea490300c84d4401d440310b28541c136030401c2d12045508140660b50485c1c82c88440e04520398070704001034500c2d0f000c01d000c041e4070000440b4042419400d100c05140644500031504800504600c5d180c0700700c80c000880413000c000c00741002c0380001c0c0c1c42030882c41580c000d0301d410090a82d0792000f0484000b2007107420907001c4104004c100210301106e01461141e8080c1d0714640c90f1642c0da80064445c45c180780303000b8160501e01e60010316409604c2d0011600f20b41042c806031f68515108030a5003124505540481c0140c2007001c140c00021111040300c0e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 735831366 1250 735830116 735830131
    0x606050f1005040e041a1005031b010503042a03030801050a140f12030f040e100923130b01030501150b030c0403061a0d08030a06060e101808030d0f05 66
    0x20728841110300c0c0604076002e1841402e0070710a40100041c10061001070000c4c074040c5010402e078407810403204440000450380121402841040d2040030030b10240301c0350444060b0107854035859034545446030303825002050703108134001c85240010392250300d02806020045002b07a80eaa00c440d41807004100074241d103944000501000c0d02030104c61650b840d40a00b10028044900110950f550007109045020301c140a0700d0202010a0003c0c001c0c00d5044080e1103031004020200082e51a058071400300e0b00070b10100d00141103805550b5404407819482c158102c0304c40a140c42000e041640c5182c01c40c0800d070070407100c503515258000303041b01e10300802d4009040e40456041c00c0d45400903003000580220b01c4050012903e030260300b01c22001f000c150020224015100400030801c0b814089071581c0141d40804034075150440000c0c13810300c00d4128516503240100400d0941c55048400c6035040f29071245031002d45052140000c1c201810001480c10801c2020040b030641b03004046c1900300c030f40080403030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 735832616 1250 735831366 735831379
    0x6050106080c0a120b040612020a0506030f2d07030e010c0f050913020c030a1e05272e020f0a11061605060108100609181214070606050f 60
    0x202c4901ca0500540d040c0404510703100b0641608548136001038800c0c092460303000f910f000750114021030030200c1a81d04a00035506410103684d5542030010b18802103030400f003010040c00100b0002c0f0345803c010803040c03012104c2007000d80d1048900100c0d20409403516008071355240c0800b90340304020302500c02250481d0804100280d48a0000ba00511036045413030700ca1004001d0180d074010090b41a078020510389800c580e11085101006490185a80309070580b02c21703030f0b125100c1c0c2988684200c0d0300030600341d84420602035171141400340c1058102c01c069031003028500140760201940c0d104004101d42440311924041100b00080c0c1000c014412241440e0061140704001c1494102803540740881030302c0231543c4804960340103031080d040d1513004101d80500000000d906400040c2e07040304418a4004001e500d640c2c081d01070444140c0c0781e41d142000c00540556011076030400d51071101c4081414151003103c2d5825200005512400d01140c0b030b95a00c0318140404c0c00d200c1003a0b001e141d01035821 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 735833866 1250 735832616 735832621
    0x10f06091a03121b0a060c032007060528050601090503010c080c030912030c071505060f01031e06030c030c0801050c0304060c1e051c050606180d02030d0c0605010608 73
    0x200f9110520100000141c0f140000c0320810310724542440940204c041c0c040d911381413018901903010b00784075021500020b0078134412482d991000e4100d4230848641c40c911074909a4035986601c003812000349003940c60404c19403400040710340032070790039001071140b00001760925107074002600075140c5800c854081d0307140200009420783c0010440e40c00649407031300d0325101d945501e1001c0ca4462a41003100b01000c010091158101c00c0300043e0035107511580c00d401248441d6101a41221401c0743d40c01d510641c035681d031181c0c0717500030350042030102a0110042c00b6131105c00160401d8941542c81100e1610f0050410028480c0d0102c48001070f000c240001c1c400c90400f2612245035020280c00a090b00d40e0300c83d000140c0b94014055118140000310816100b040b04800c09000e0760800414140c04a00d0099508110510392185a105c4c140040506042c02c0c4c40d20b0005420107904081c090300000c00301c4d40030340035903004c00ca1180950314513076a06450b0381040c42d0040c241c5606a10400c1400ba54405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 735835116 1250 735833866 735833869
    0x100509030f1602030a020301110a1e08061903060c0f0e0306060123040e07030b040b0307050112110c0f03070203070905090a06020307170109061a090607060b060c010f06091a 76
    0x1111490785a034168011605800e00010f8141709511328000e50540c6492410303070782e40c0c050038080c089050141d114070205981e103006225130440e0802d403402c0040c4950340000d55520301410710003038200a94408084480d107030764030300007168001c1200502280c002c07608031290a80c001203222015400340e010f440c450404800181005207840c80304001c81d41c05a03400007030540e1400603078000f00400101a51907080000000c0d00600246004a000e241028400c2045080014132a021660180e6540000010b0642014011b01d080d041044407000304102c42d200030386080092030399114200700075541ea00c1c52803040601d0541700b0341c03000c1e1415040500304440c071000860708240d02d9030003040240c2c1d81c8c0c0d90900e0850b103003040e200c1008880c0103c00008101116132758451419102842c0e9641010411608104843c2c0214100640d00c8101049880d0001d03031683c01040012034060501410302c00d4201d03166080d18580150341492590301d41c81003200400c94000e00140341c542c90854003d9008010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 735836366 1250 735835116 735835147
    0x1020921280f050f010c090e0609160f020a080711010305090607020304090c0c0b09060f1515090406080d0e10030b0607020d140d020a110a1d0603011104030510050903 73
    0x10054604181d80c0888414440e050168082050402d0006c01011152541c0581412460301580c00511140390014410341800040c0c00d00070200d011010300000912081121080c20b002402d401b1401500102c600007541074015008251185d0003940240901000043c11110000c1c420003942e48240148500703144c000c030442d000e0316070441010070402c21105040c1e0300e10103070340c00051000660004010a062001c01e005015013018084180d49460f243c50980d0419070401c244c943c00041e802444c0a00f21120004100c1010042d09c0454255070300c8044500f04811400c189010840c440106051480c0c03800403580c040c00103007003c00840020f00042817190151a40c000d003d29140200b40c014000e800d04450f202c00394001c202e0f284049120303402911160214802c654102c0c60300d0ba03c010f1460604484c50580705038413140d20304051050480d6240010181100350113560702c2e0300114001d080013001b480034500820042a00c1d0809901140c1190001452841d958109210341d48694080c030703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 735837616 1250 735836366 735836443
    0x30306090c0403020916050f030f190c020c010e0d05011b0216300636051c090509010b1b0c091807050301050a09030f0e09160201020921 60
    0x84011581b07841600e05c003544c4a1040c1251803122403404401c00406007502d1081c640710300b440e000d1030401c191070351648606880f0040800300140e006400f0006041d40300b0409401d5043c00146040905845a02d6541c2180c071544038407a500c00e11025803054150701002521030000b542c40481c801c8510301a11154034080503064012411001d000c0d0741c02541e980855002140e4112400704901300501400c00001e007648640340c0e80d00c04500070290100f40600440516084d0800d01505170200240140e034000c06038a4070100034810f040c2c801040c3c9888943d42c0d1400307003803c1c28010303a5642d05281320b1140e5090000c0032508e15804942004402d0f01c400182c00d4220445115000e506031130220640d0400b801e0b900300c590550710b404200450100c09400c2220880c1c001d40f90840140c200740d40484410441220980c0c10150a5020801d49d001821a2985a0a09200050400d01900005a040182a800c44400b00302019000c0c84910091010700012400c2200c070805055070002007860300d4900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 735838866 1250 735837616 735837631
    0x1221031401270515030d03270209040f031b080d05010b18120f19060c1b03050d0b06030a0e10020405010c02090901141008100903120b01090512030306090c04030209 72
    0x124000300d040c5600c3c1490103011110001c09031b42e80746000000060050103400030710300c0110320400380d60070b03440080d500490384a0340250800d002641c0e60740324000070b1654844124104010a0300da4400300f90440c2030001c50f244180401c50380c4072105103210055400607004840c2e1100200511414148141010152030000f507560300054280c01180c030303051401109000e8094080c0d10441751220048030300300302c580352055a040007840350203501101c40401d407000366985000b82c0c00d00c403004640150054903511342d1284001c660322501101080803904147e8010074610f84607020106440d105228030741d040074804004500b000e152000080c02c040000c88040e001e0310040c00400c040007020f4000d030707950014801410031141058031114001d10803510602150f40603d01c90780c25058485d0280030b1110307801d580c9405c1e60741d44502480000341400d10845052001042001a841d1515000d4144516241c1d000d1502e030324240313041c0f024140000f000c046c00f03a10104000e00059a907030514a412140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 735840116 1250 735838866 735838871
    0xc0f08060a0c05090f0f060417011b080f041b0504020f03091e0a0b0c09120a11040501062114100806010b0903120a27051008010807122103140127 64
    0x140c940104040d0b00c52034212810303500d1027489642030b201e4150040c0410b604607014440b40703100300603002c5608131001c3d54042c020390030060100d800308115504030240e180e448081a41140c0d61400010708a03440551030222030700340442041b2180c6130520541030380071049051101c0716074070682c01948915001c000189000d080c0320114146980c000c0c2603c1b410180607002035091014154215a580188441121000050149480390341050b000d1903048411645540300d01c00484600410805070b500c894038440385d500e0402c2c80c05003401004207401003100244c6952001d05005509040c00c0f0140c120541d103000401c807906298800207100b020701051007500544454450100700c0f4086100027a0102520003400060354654003401603000301d0b9022130754400812440c8005641100d401d102e8100d1036003043d5400c20000c0d4050b040317001c40a22940c0130281888800d0000f21903801e141c0240c10005e44e03661044200c804e041240d59000d000132100c928880250400c8540c421080c02c44600701194 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 735841366 1250 735840116 735840139
    0x2c010303200a0c12200a091107151506050301030b1305210a1d0a03060c0507020a08060703062304090f0b0f0609060d0515040c0f08060a0c05090f 64
    0x120502c2606449544040d00703200d81d9944540c8441444401070041e200281d100c0050100c0100d13210004d5070101000e070100d452030b46000740e02002040740b9802001504410401040003544200b021034140100c0140010100b8400c442500d54484c50342000d410700ca402c1005102154015048540c0105441510601e0046610b001801d1064000c0c1c010000748840143d40c41000600015105d186240c1e544c02d0704540c15507489064041044280c15080320700b9650034001300c2c00c40d4206116070f415074145141752a42e90b41c0800d1803040785500451503a08283c00344811507a05005a00050044444020844603c09003c082c07d03260082024440c3e50b6800c40710082240040c200314410740c0000040866183ca0206c050b1514070880e2034910448000001031140d01e041400f51a0b1190001d00900101a400e126500660780c06401551480c8a115000910000c80030450300504003540207000b007420800b10308015980f02c2c5800c42c2c21b01005101d0450140c44041d500c0c01c110004541d540e0944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 735842616 1250 735841366 735841427
    0xd080f0c0c060408030a2604030c051f0603060630020d060f0203060301060f06021002090310060b0d0f0b0609041e060830120703020c06012c010303 65
    0x5069490880d00060040b03000103003004e010000d84030342c25a030344669203120400051032805450b6183d50a090350351355004900868800c00407451a984035808a8903444904403c1a50a50782c45905569041d25800306200f08039850240d0f400600301804090050b00c60704146030420700d280c240c20b031448107140d8090b03025983c5440f1000070f072607001207040001c04040b1603a00c019600032641e1500075800d2040000381d0035014950442114030303a074040d2092714103030240840039500c040c41065240c07084008031803542503070348608001440d421380b04c2c0703a844107200750aa0568140f240d20428061030580c6012154031240111a0350b40411500042d4404250b010960a0003944000c200c034030385400d102241122001034248214100b16049001801b19a842260f4081c040c940c0e040c4815014031000c08080c0007603e244e9000b205606000d420543c1c0b040c0010315000003680300200240d05102c074018041c1100b1318104d07a01300d4000ca00600384d07045440241c60310440d4200c1003020304010081411a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 735843866 1250 735842616 735842623
    0x10203091e060412140601030201020d030c020a050d051306020102040b090405460515100219052109090114060702060d0c0e010815211c030b0d080f0c 66
    0x10190700400e81a11503442d4512011000740e240c01c04c4640c1c01d2500402011410001225070403a0350517030041c81d42c445012030490140220500c2e0760250700c1202c4c030020000e40d0500030444e504019a1f2100e4403080740e01022205094198052400d59104101c00e010301c83d00310049600b5103405540202e143e8076000039008502d01c59101c9080314194980c4402c0d00c58030034071420360f11004031040c0c2c199088803a40385007048500946017500b5006030902e180c1c400b4204503d03816890706081c010346010401030810307148880181e000031290b6030000e48100d0350884070303918603a00c2d82d0100350322141040103100105585800c18064005500c80c0184003056a9031050102d5000c0c56024040d591510b2644526201610200740800081000c00c10000381d01c2d40f003959030910514900303c50603503403080c09080c4010310020310132801000d20148000740c0810420000302106078044070b50079198840d002c3c0010202e4058071f00355841a180403a10801042e0103005968016102c40740f5147c1c2c0d92800e0a80174603 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 735845116 1250 735843866 735843919
    0x5070515160f0b060a180e0109120306050a060804120305061203040602071d04050604030f171e01090203090c06031f0b0d0f05010b0a110f0f0d020f01020901020309 72
    0x300c940907800c020800aa0038220031180d4891640040c1c1a03d0781c1c001c0000303041c8640918072408426245c1540d092489070010841d12a000c000041c2480e0300c6e4841e0f41301980500864400309441c1c0900300b0060924400b070500030071aa19042c40d00303040a685182e02035901ca0078420805032510b0101c0e110750344503503254024040c10022a83c2d141d940380c0b0040d490302e00c0781c814004001d034803074040814821410449072007a94014060121903030f96a8098030751600c01401c1c0010015008003690a01d950700c10181d000e410710440e01550b9080c2c0003515103500d50160000c0e518a0300520a002c04560005800d015009040300d50584a546081008031415400d030314a2008401c2444c0010f004118000102043d0341e241c1001c0c804014a20f5480e82990402e22443c07284201c00c0010300340c0c541c03059407540c0405900406841110449001152a00f00003011107041500101c009502294040114070301918548000791b05180300480041e44a0080580c82e40c0268110129482140c03081b80389001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 735846366 1250 735845116 735845137
    0xa0507050f03030703090b010b03042406090f0209090915070c17040312110a111e0d06020a0e090f060f0a0f12120c12050903070b03040f031b05070515 66
    0x1d8480c5807001c0005c1c0034101c0034405440303d80d0910004900c801030041100e101d41d400c4201d010404199031119202507005420700a0380554034030020400910500485c0002018403d0140c0c40c0c210000030046450005000d8a440d40e0000001d09111424103209903800b40c1582010303010080141030404904030480d00c41c640d1144c0016000c010000c00340e079a1160700440b542d42020310155406025680d021803800a461180031218042e41c624007101e01c10145010030301415800c00051002c034150107200741003114581d40214018001d02d5101c040342580c403904450040103400c02c2c1c02885d04514028000e02e0013109070400d85112034960540306001071044001200103940d40e152811059442c81008a55010016514aa02900c00c074414040769070012404140203456100c15123156200c004029018003030761034005208610b9070081c41c0300d18000c400c0031038100703141d03d001440790580c002070710040325110b041100428800113050b001c1e43d078191421200010800d038108114000c0b0030981 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 735847616 1250 735846366 735846373
    0xc0403080c0307030e0102060c07080a03060503030c0d0e060f031302030102190801180614092707050f0d05071806051c0203070b04120609020d0507030f1110050a0507050f 75
    0x40c1e8140310000010041180207030381d40b28110044800490301c0300416102e182d00d0b0358040c170100c004103902400070691401c86041c0000c08a0345d80d004a411034201064013102c0f5000060400055500000403001c102c02c1110224508001c1310303a10383d1f05020141c0100141030541d5a01400c5480c00d6040b100c12107070903220010603594411005054100901901c3c2c056195400359100260003070107140280c54684449403550400343d01441040c88004210544502062008030001030000145091420110024146580c01c000510445100044182d4010304041000c0c0020800c0400d0601c10303100d820460301100103007032413004050300c000c0d0000c0d40e00c03000040311022500b210a81c0340b082c8610070360a596001c3e60b10001c42c4078a01a61046d014541548901c902c00030340940e000380d4000b8401800d4140042c02c58641d64a8003085800071244510b105142600f4000141402050600d0403a10203102c01840341008002e400755401200520070045884802c00406005210a514105088 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 735848866 1250 735847616 735847627
    0x303080a061d01030303061e050111070905070201020c060112030e0105030a090b010b030609062b020d060f2f18031038061603051e0d14040c0e0c040308 67
    0x1da0012001e21041300464504000041c0e507523280c2100085003c1032000740580c9910304030040d42c009144076040d41d16406804c401054103462823242030301030080e1f5130005807542c4908140038540300c0b042c0c000055550f12960b04000207948040c0d220441d550a20300340352640c4034aa1034501500d20080000d141c0e2100000114642c42c0c1ca1000d54812407003290b002801d51036050a11082401c40351403004602d0401c082e54150003c5c804010152620117400782041d1003042d1540002ca0b95076081c2c152545071580c504404540c5c0150306440301d226504075040d0491000094645240f00700714803080041000b005110090381d0074003003080c10001c0990180107000309013105c224030810707440300d25082d2640071043c118139a44004642d44081c10282000b440c04a02c9605010034802c202c50403010444100301c2800115002d58420088a4602d0300e06a2100c680300342e00300548050f0101d50b458143d00108000c04240802d4694040f1003114070017840716101c580001e60188110b400107480e0070400140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 735850116 1250 735848866 735848909
    0x31002160f03172a0307051c050106230a0c080d0f0b091509180a1407031514040f02131e0e070b070b130c09090b0603010608070303080a06 61
    0x80b11840c3c0303841c400c6091803690f12099400300740c1c0509641c02001e900203101c00d50440d4800e800842d000056414094100403005d800340390080720383c4a4240c4125142e000411140e0342004420100080b401203882d00f030070141000100314001c0040740340c100045040460103020b282030494658601600307041c003000324074101303040240040e40b03809401100d002000840034070b40115452140003004050340e6581d2a0394a01c07003000003840d000d43e51980140c1100c0e00000e28820507086009000d80043c11940d0310714204250303911000c20390340c14100e040c04c4d4840030001000380030b075500c1640440c0c88040f041d070318004114410011051502d0307d070b01e42443d40c600d000300020083e400407100c4d0b01c00d214041003409110b86030411b5101d82014002d041c001c400000ea1511140ea0707020503100d0500201c1d01440d1500103e11740180d016204095440c05010b0500680903815944800b040d4000d02c0024902400c2640e10101844042c04000b91900410091a4140c0051000300200301c0540a000c1c080d90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 735851366 1250 735850116 735850127
    0x10e06040f0317071806030c14070c09020c0d020d0302090108130f080c010234080d021201060822032705060a0f180b0702040c050c0a05030c0d020606031002160f03 72
    0x5003003140d402c0742040010300c06c1d1203405a0780d0308042075541d190810f0f0201301810b4042e0040e40c400c0354000b08003000401d80031640d2000e40f80d81942d1200508040b561003001904000701030000c8410140100031004491760044c14007900440394100c5244061030320304082c1c401103409a40205254800180b2800481c015005001204d0b0b10001442180942c0e8815840111240100c0b00200446100303040c040387c0d41d00068030040010f5000980303400d24466200d15182000d07000341e400b096502e01486011100481c1003001c00c2d01007258001c24034641c2c0c4020f40318aa0f44014125540710b800d644241e030a210059480c001d081c068903a5441c6c1c400d040c0054610280c4129404c0003078480d09201d807086d80d003190349804441e980d034922850200f082d02840090030251043c48c06128081189181302c4004000404031139000d4409503855484c4028181d00f040c100000c0780c7d04540c82203080c809141e50201b088040c0103426100180d8075107949101c2e003896140c90328046c01c201001700c02d03d01451b4104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 735852616 1250 735851366 735851387
    0x6010c020d0c2408090c010c020a0b0d0609240302190e04080403050d091203140408030315030105181902040605060d20032203031e020c0f010e06040f031707 69
    0xd034a42c62910f481404200c8030385000316101091a40a001901c09035405140015000b50000d00089525a19280080b256901124a64400710341c0d403041044210030070310032130309550140d94809841082c543c0a4041d45034603400041e1085407641c2042909080d0a120080101606d16213225103280604260344140c00510051b505405000b1301006c880e13102c1c0038080c4c00d6445500a4940502864404640c28030582d407500301d07031003070400c80400c81c82c20400c0554854107480403200c84010380c00042c1403c3d50409007862a071892902041035450801140c0a203684850091051503800d060001801401e00e030380c4030765080100081c07101e20960054012021820301c009100002c600b100b41500668403049480c4605004008804a14084d0b0890703c41d803464002c1c03402060130550b540d43c1c1a8152032090350303c40c6003a400581c0b03c0e5181c9003848a501800c20303903402040200c074034810443e207035040204014500d040c00f41c40c400805001c1d503610344140031601404100c07440c0510000e010880003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 735853866 1250 735852616 735852659
    0xd030b030d0f051e120c040f060c05010204170a050715090306150b0f030403110a0201050f07050f0d090f0e0402090f09010e102a09090e07080a0b040c091406010c020d0c 74
    0x107110782d021b002c100c0e412120040c44403603006151001c11038107084101411500e030b5408000006506c60258140c00d030001c05078000e0038201420340ba1051420746541d201c00c044c403101e072540440c907580204024084940060000c105240300d038840f4036048200e5041480142c5011074031703801180000014501c15886038590003d4101503501c0701d0342e980602c032002400110104040090072240c000035092a0b80300d1412920301c0300c912400d903824000b86070b42c0c020015542000070001680e90004c2e2800501003404652001d05198011642d00c001c020710002c0c0c002200c00114140344000d601c56075a1120200035250103a2540d40c00002034823035610a2081941e22600c04030b140c1b180d4481c038007100340d880d440307140000e40307800618000752a8100903c0700304c1c058494005030150040c400c080b066849a182440145802d02d005104001b00c1c1e003201e1000b6140601241c110b1003083c2d60103402c00c0c007d081403036403200984001140303424030140043c000b421107400020801c095110351041c5458 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 735855116 1250 735853866 735853897
    0xe07080108010b0f040908091503060a060503010524040918060b040e0a03200a0b07170112030c111804120f08042904140d030b030d0f051e 61
    0xa8401d00301c0d0070388404480b09a8040d000c80c0401455140651200040f10b100d0b101080c1030003030480000c0c4120383e040c0300070315480c0c10001c1000b030706240001c03250019020a0a2460440d4101408160b50103604986980000b0300402c10001d034483c076000343e5004111403031081c44a000d01c0c000c00c400b1142e1341c4204444c42c070309183c0300b40d40d80d2a1500030b41000782131010051088141c251011508501d8907081031440c45d60301030025400c2d0f40248041207100b0302452031582141002800146803501c4086240200d0034000c0061010007016124100c00a4040ca0040003002550134003036240229600720781c0e07000480040d0400d9000c0d40781c0342d00d0b04c00c41c0580205003000c0d144443c1500c1c51041842c2c56000918901e00040015010b00030302d208102d00a800840b4190300380c410500580d005813006c0e20f2001c00744080d1140c0000400c01400030b41585e1400f84001780f044400300707035200c010895400500038100c1300701c42480c0c0b04034180c1c2d85258641c02c43d481104c029402c00b8205521a02c0c07007058495 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 735856366 1250 735855116 735855119
    0x9030337050711012106030f11030f250b0d0903020606060406090308160b0403091e0302060d1d19050c04050f0601050c15280507020601180906060e070801 68
    0x78001c00a4421940d044600c0c00100d2002c1e00044843c5a07140000344200060703403414101d503940b28499000514400e483c0710890605608000011484a64080303100354400c80c1c00c1141800d010545a6550610700346010700c0000003d0440e01041140c1c01580c08114042021030712000d682c1c01c07100355903000340c0030341c1c0050b25503c0034850640308502a46003c10414042000007500c1200100505208401c101c61145481e0350341c1c800d0a1340030380313050300010f00018043c4082c0d41c2030700590450000c1c91062007029840c1d07901281881c0160040b024001e6540c900c5076000c0b8000c420410104259101901c01640c00402c1448141f01c802c1025120740c41042141400d80c14240301c1c06000c0c1031021074506183d5140f03801100d451340b00074174890523805001c0c1c0240303c031452a01d60714060028030501c4031850312044481c1200c0740702d24004c42560740c14001801030564020036030342c5c1520031420303000c91410100705071342000e050b007004014411441e2102c00074548070705044980c00390005039140388059 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 735857616 1250 735856366 735856477
    0xf03030f060510050903010e030d1d0f0a030503182a040203040c050d02180103210507030e01031109030304030b0108060916060e180a050103060509150606090303 71
    0xa80030750040c1900b10f403c0e01285015140101c0190030868802400411003050a41f0003c0c19a00b0081f0303568a12502e0b0103010414004801d00c0060166140c80140500840b1490b131695030401085c02809106001020418004902420790075405c032000c12115000d01c02e00480101030350582d42c0307000d0007504c2c10000c001d91401c1d008403801260051401c402140c142010000c101d006142c003280e00c601d401c074000ca80041002e942d140214003074860414107460001d40445002c0c001d07488541001000c02c942000250030021012090b4000e00e07002800c20711020f0296014440d59054070f50510001c0f800104010840c404981038807000c20035182e4503290850102d980d01c00100381214149010031044c81414440d0401c0046100014a00042c0c1482c0c2c2540c0000711500740c8800d0141c50310f800c014401c1c020140203180c1c102161a00908807030411410700f000c5420050101031050100040d4008035603800c0090701c0018503084880e5010b41c7c41c2208106203e1321100d041c0540103100c1d00d40481d407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 735858866 1250 735857616 735857621
    0x2107030b090612072402060c0f070b100504021b1606081906050418020103111e0304020d051504140106060801091d060a0606092309150d0f03030f 64
    0x6030000075000e5910340d2503076000c0003409601c0300c1e041d14284c0b0035200005044440784103032000718000704040702515110b442c0002d05069004051607003404041250704d01c40600d60044500807030b002001c00324a510380181c0380f000324040c2d40c04694094000300f242503088a060020000700c01000c01121681841e219802c00e02c281c0038032415021502020024000d4080b000d0940311050300401c0c00101d042e1124000f8040b00c6400b01e0000441c95014000e40031035800d40304552140301042c00050916402006049030180700c0341400c16034920100100e411522a4200c4c01505513008042e46d440d600c440c80c0c1d4805c0080b040b0340a8407030202c01240301c50000e8061144006840c810340e10441305038200f5992001805010688070025000c4c403004601c50b941c2840900d01426003401c0c0406c20904d400f03001048100c00c1d0700300d0b0651381c0404e000140039114400c0920800441910252a20f95a840d03100030744210803080aa0003da11041032000c00c03a8580c01810164440c0c4c400b0003800304110440c104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 735860116 1250 735858866 735858881
    0x4110409170c2a09092803030b041506050a0219141504030c140c0d0302010c030c051903180b040605041a041716061401150804030e1306030503210703 66
    0xb5000070f040c2d1454401d007016040554000c9004007200d0b4000e00748802d0b1003503141d103504207120715203c2d850104205071b0b040c06003007403001c81201c050000e96601807a903494950b02c4d00c660400d02c03030009107038242c0c0ca00920041c05040030700030f0034a40721385050800d1650020050140750281c044c012503c030015603910745090140790142c0c0c80c002c00940a50720500364402c2e5403007644083c03041051260310781c2d40712104550190b100f54004a04845200009400c1c3ca035580502014040180040c0000906400c0c04003041c0019284c0130480031110002c1c3c480c03018019170003408000c1c1075401c00050001036040720380500d2040c40a1307003003007100d0b03007a07000c40340425a0020010b0022184849030060380d02c3c05003004000f201450540b88001e40c0e00c007822113400100300300c801c40c0020010003031000c0507050200d45141c2400d164084c0e1405945c01000c1808418519105036440e000800d400b0b02c103540400060740d4030208480d0744813a4610003050040442242d4101d80b44040e00044034140f00380603415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 735861366 1250 735860116 735860173
    0x6020d080c04050d0215030a0903020c270a0b030d050406080c0f03070804051f0504110402071502070501060905070c110406050f04050c0d060f08010507050a0804110409170c 76
    0x103003894101810800300c4680107509170fa0007908040f6000040003041e0046008030f210340c10000d6180c01e032b8503010741404580240d0602c581492000300304507503801c06c0728442c03520b8071003814010f96403024920001010800c1200e074040c403a40000f00b480da60000001d0003a00c01645400400350b03a1074039625030034420384420381c42c500f401b4030102e8801805810f0094000b0301c01e405403900041110490010303512030900415401c0e807181c0502042c00642d4401143c0130b042540c081d0302d841b01036210854000e120080031115160b0000306603040c808294000340207000c01c1701052095081c003e0000300502c00341041a20000380a004240081ca0039105240403208050100382d6041344050811004000091101c50190010040184480aa0312500c0050050b00324106900e5051800540c04c451000700740005010341005003501d00d81d0407a4400713500a52200c8000502d40101e4041400740181c8100146079068400302d8807034000c003100c042c00c6610280c03401c0790301d500907110070580b2482d01c607034841 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 735862616 1250 735861366 735861391
    0x61112090618010c081305040f0e0a0f0c05030105070e04050a0903020601090c1407080a1403040201081603090c0f05120309090604090c03050f0102071401140a020d060503100606020d08 81
    0x34001c42c1000d042c2500705005041c40249150291162600c41d400f1140308030901c0f007550011310041c80d0500c2105c070f90480c03544041101d021a9908250395201945000d8a001841651101081440509640940344c040c0003800b1074203048502420200715950300c03512860416001400c50449480303030001d5941c05500030400b591801200368010a889204441000521214184a104080f00a20700d40e80701b640c01a40e101c1800100400d01108604070314400c640800c14000942c0e80540c4549c0c0255030322642c583c02d864404e406074014184110000c1108034442e00005001241c6803000c002c95006440104418540040080d181c0c810015000e40c401c2a0350701243c01030520b41e0000801501c108880d5000c242c8a0301c0b124546510750741c065072180e4000070080200604502c1601411384020000e01c541d4180420301c0b41d0351040100005503090303020484441600c0a500301034020300010342030715005d22072005000091700c007501560000d40715141d001e500c034920444442d0b1003482042041d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 735863866 1250 735862616 735862627
    0xf06090a030b131a010f0b03040b01060f051603030902031e03120402010e130f0f0606021015120f05010c020c03120d1b0e09012102010509030111040611120906 70
    0x880c0341001000d40303441048020031a50200144c1481c02c2c4002502d00c0248006141d031402d80d038035811403440d070080d0307003039500038824000040c6503406141c0c15038040b4144520119695501102c188c015080c00b0b4180c10307002c01b00340007410b80561250038024000e4060b00d0340c50351030070344c0d440550102500c0804c65038401c000d030022092080e140b80e60098030500d4185004407040c0b000074454101e291841c100c15036518150a407404603807007400007920907550180300c40742c54650040c1d11a60070000541c160342e15841030081d0b150350203125032302500c4844070300801550b1324103285800c10381015086900c3d42c684040345032000e000040c00003122000a00500d4000114158000a500003402000c0c816494a949003041c0709103800303a1000142c25950981c404504c142005009141030703208903614000300220448805c080500e1411050702801c0c216542c949a40100340149000c3d640040e0746103002c0b9010584a80c0700e600703900204000e00803640b001c102a1980e00d4030f4880d90741c1041d4001c0302000f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 735865116 1250 735863866 735863873
    0x61e1b0c0f020f04020c1e1603020910230312070203060412020a05060106050705011b27030b090c0306183406031d010b0a0509060303190903020f06090a03 68
    0x980791500748043c0c0199059502c000c04101641c2181c140c0001c1a00024050495440081c18030143c0d02c1c61075000384500d008108903501c8041a50102a000d4000c200c00a8036108003180d91340001e144511a8503000803403140440062100b403d009486030052100050302c0d0141c180580e252075800501820950310b03a80e07600c40b540e45e102e178208020b6010719118072000c43c5003440800e0081c406a22040c0d070700c40701340c5049170840b24424440c001b040b4909855400441e40305d00920450b80c0d0a07900c0c00103502200d6207802402e2900d9000900f142c80c0c000802000100105640030081b106030200c1c5c0703868030303006800da210410b42d50b26416142e001301d03410f0030090100e01d102405011651140c5041c401c0d00b0b070b40b511600400d508a41c01080d180c10300c0c903111600e1000c0d84200110001c00070884804004002401c0c0ca8180c81a64812004a000b06540e981c0500c00c139181e0078850240382e0081e000c030711000351450322180b1090b40700c0c52003140100c0007403c100084650600000305003200031406c664 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 735866366 1250 735865116 735865133
    0x150603070f0b0d0b15030f150619050307032409050906160f09081b0307090b06180402040f090b1003020406050306091f120b090f030f07020d061e1b0c 66
    0x11607503444045c030004841071880d02d05c004c500800c600c007d80caa81e407030803404a4104024081d8414040d030b071308001c030892514854200b84290801da00c2e10b42d680303880d81c1100b00c015082d800034460162450501d4004d015102229580c1241c4400900f4095540c401030800d0302c410b003c441e034032024040400f241001d10b100d510082c1c2d844080b410561601512900e6035854500114654041e601c9552840c0701a45001c122880081400003003e00c4861071320030116560b8060a0400000c112641d20f1031060b036522501598050704284407210038580d51045000080d0140c1c4465074002d01c000442d14000c00c1c880e0007200c059a01c6500c0d410300d10b880c1d5505124800c200203086190040c44d108401d61151510788102000742800650445002041c0c01d0040c441c3d5405080601158020300000818520220a07580c10445144c400d984481d200d0020440740351031080020507141c9030101c05000711901808502c803520140d03d00308804e2018810785040e035101035014002080903690328500241a25 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 735867616 1250 735866366 735866381
    0x9080f0d020301150203271804060920030a080306180708150402030402060318010f061e0509010303020703020915041b083711070c05030607020a080403080c0f150603070f0b0d 77
    0xa4240050030408000084038904241e808852b995141c3da412001c1c02240204405541e00b00c240700755400340000d001940d2a94903000040c45c1d40404400a4900d44e198092001c120107000300c2c0300e4803840c014000511032381e000c80b481c0c2c4901e00583c4910005040a200b52841103501600340d51542d1100840341c0c00e802080c5071800880e6403514408000051a8080c0314002d00451301e03c440d4241c940f01c44e4507000382d00b0303800450050520000410100340d0004070301003140c3c0c055440e00700703648840c4c01324410255415642034100b4142044065508006d0b6a0048403401503035400d0007640302c00040304046c11400c1c17141c106c130ba002d01f084002030215402029910a04805002440308480004c2c2c9080341c0041100b0384102c00a8401000581010f010041d844203c0d48080c02150b01e0325500c142240c016800050000b038070205420040e44420417080c40c0010741078040795440d540345c481c1044c44040841b203041c001d001c1c0c03060016484418131001c0c03098a491801d9641440700c1d1042550080046 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 735868866 1250 735867616 735867619
    0x1a0a050f0705030915041a0c030306060f1e070b0a05070804030f020703170403060606090e22021c150c090b030a0207020909060a1a0108060409080f0d02030115020327 73
    0x800203621141e0340e1901000c40500085c1a035510365142c04080100e8080345a156954803400b00322a030200340020040782d40c003010480b411600c404010104c20b18a010719641070903403291035024034030b082c0340120140c00402e1250304283c0103981c6002c03100058660503100321010440340c6d000320300081c1c0510306150741404103104540d03d00340c3c1d17902d91010305904045120940c4500040a10a0081c43d00494000c0e2002d0b051046002d880d190b041c4981c80d0005002d890107003481d504c1ca002c0580120301a03054550000d001354074101081140710000440d125044801e82d59202d4443c811a110740205900780796140c941c4503000d450500103106c140e0000308452105942008a5030050b51040285400781711030000520b140e1801200e00303406c032002d50880d00c00b015100d9151011aa078802d0020360300c18800da81c081041c0d807041c9000d01c020301612084060034a000f0840f12010a05540698100d40550080100780324014405a03200d1055141880c420440d10104200d28002c4090080c4415030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 735870116 1250 735868866 735868873
    0xa0215191d0706020106060c0305070602070f0516060914010503180601150906030b0603010b0a020f01180c29220609030501140610030c0513060206011a0a050f0705 72
    0x46124940c42100c00e01c0d07200d2600100340c0301c501600e00708200244005024540001c110b11801d11901511342d074601100201001000500c840c2002910303015285196803003151006c4046062a240c2e480e0020340152102c008180c0d0000528a44245c0c0d8060448418200070780c08071040c500111465403000f8900c0600403421012105030003c100121802400c000c07144412218031040020034821075640a0800c140c1010306081d0f441c0d03035080031281110602c0701090380d1800e01d0b140c2a403e040502d0042c1c0065440c000303000c4110b0480342c02c44c0702013a11035900401215151542e109144001170003d01a440008101d105600d20580050126100000c10301c5d038019480c06240760f900426070007205c0000c200e40c508100300042401140b030b80f00d25040c0102034a25100300803d03803801d071032503120303041548515032805000d00442c00c41714001740b10060b00900e1500c50801035511803086c8200c01c60101c4098000126011080c1500c0380000c1560307400d8a40080e0b03805d5000c0c250418007007a01e0501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 735871366 1250 735870116 735870151
    0x10050f090f0306041101121104051315060908010e07030f141603030215160e01030b041104030803040c05030607170613091410020a12022109030405040506060a0215 72
    0x1a0100b003ea031046114020071a090100c039400101901003000240b4501410b000c0111203c000150a5a0030741d003042d0f408040904403814858041c3c04100940c40e140c040030100407810a502031200004e031004c510007841a50707501c1d6651559400701d440f0207070141c14140c60003400203040015080c102100c610490b40705a140b81c040f0380168129034000c4002d0b0b449010120a0f00300c0300010f5584c4110340e02085d658040c0d14003405460150300502d02c904041c0d4480200c00d1543d155031122600014100a69842d913480340392100c1568002e03103050b10810454075002901e80303000994a4800d8085d0307621003101078009601141040d01c068051640400b001002c8400207801e4450b407503000f03000b9420444c803468010744c04d60921107009210040300c5c0c01006001001900208408d050038650f138401170351080a0540045a10b48150a0010280306a000d0180b111000000b030700680d081110200401e440b41020410b4504c00d145e0300c500541c00004004040c050b00b1b0307824a601c08440c208461501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 735872616 1250 735871366 735871369
    0x40905070503070e0405070906061b03030609090f15062301030212070305150108100608100503010e071e03020a12020103091b030c0e072321010303030b10050f090f 72
    0x190f582050182c51902420041441402c0050394000c00040030b04108060811800500490281401142d400250141c00c400c02d031080d8040720091a110340c00b08a00902803800050140c14050141c0e090004140e60424a2149100f80c008440520940c3c1480e04815180c00864101c2c4203041414140c0c01d00864842c0409900814070420f101c0c0c2d8001410f141c01c102540044155130007a0741004250b0701004012100103580303a0660b00c041c2061285503865034208000105580c000a40550074401c440307145040004000d816200342e030107400d07040001302a45400c0307100c01c1e22000c0e5106002440800c411008403441d0b200e01401850045009015610740700940c0486a00039a04045823031410404d2000c544100006486030060350b05c2c0904000000601d070701002901c070740d0b15001c40441865000d1618085980b507071480d00c0c034861044940e4034035040e80c801c03d1009401080c1800b0940049107010410141d000e8a5a224030f03040c503541c0c45581c042d54100c190015000010f140c2d1b120204d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 735873866 1250 735872616 735872623
    0x51e01051c15020d0e01110d0b0415090e190201090e0405030d0524010e061e0d0501090c030e0109020a060f1407060c0e030703030e0d03030212070e120f0c040905070503 74
    0x342c1c1e0840b00d001d80d84054801800b42210b0584035178083c0e90740350140c20162081010b0480e1000e0010042c086100815203001800030300f041c1290859070752107014002a10b001075040350240c04116802d032074402400c40030750401300d002c803074000b400284104000d110007007130428001c0c0c100d4000d5003101e017021651944101210416104000140780b90555442c100c0409401c00c18200420302e0a044100d00312000701d141c5016100d044182501c2440d0b064008405040035248484032078a800e10555a603250880020300203400b400c00064200001000840014020070846650280111011707d00d850302c202c0d040e61104400f041085031905040f048401c10300081e00b00240510030000d242003000001505508280701c0d880c0c000d802402080010940000400217000340a2f24110583d82c450303d0220004d10859100c03078010740481d0140700d107141e408102e00e0000d0005440b089802c5c191982203e58588146a0305003055104e10004961820640c2018181c207203d90102d41074152140700003804c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 735875116 1250 735873866 735873893
    0xf0c07080c0a140f120f07240605010e0a0302100815060406090503250603051e0106020607090f0b0a031d070b03070e2b0f0b0118051e01051c 62
    0x41c96184184160741c0f102d424000301e04000318107002440380003d020061100342c000d2007007130721604402003005800e200c0505038148240c01c4c10071803980c1102903540040010000c03030107561b000a50810b903c4020342004104207040c2e0ba0018036080070421014400c5810b018003c005106000409282407260b4a540d405040544000e40300c0710312441c00c00060629141c6914aa2a040079030310300c80142c100d203c4514001943c0f501e14020407a036681200f0301c1801c40d034540c0003801c0d6003c2e0000004005501065250003041d00340c0c2d61701c41c070990f940d0717400d051011180112103581c1c9040080b004101d0290f44100d4030420312103400f2800d485409010303030800c451076124001302800041042109a8441c11030400c9480440780a04504500b960142103030921080d1041031b0740d59a81301c0001d20281c030140c4107070f00d4ae0141400c0159078440302140414407840310500c2038a800c3c8000310f44c1224400b18500d072b0044800b45081078a81c649801c1098112500c00031b54050352007213071203d0104500210701c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 735876366 1250 735875116 735875123
    0x15070506090606180703091b03030e040c0917031225020a020f040e150411010809030f0f09040f0c020f011512171c1b0201020309070608100503031c050f0f0c07080c0a 73
    0x518140382d0302b8080c01c60024101c60350f00c55490103000024041d0001040004c0d604190040b40b030045052002da49113120f06142c80001f4940314040118a401c03060000074411200040948550903d1805990713560049500039441510114111a14180b5503c0041c46a88540446903058880086602184800d46e0181c0f03100e010007002245658020f4001508140844000c628102c80110044024015040e00d480000c07000105450990f503540c0004052658115080116820241000c0e58a45404041d05910350030441c2d0250342c00d0130440400111f43d001401640c40c0d400641e60104d102524218040c603015080c008410080b58015a844114061080002d0f1015070806420800c2a400e07408004580c010020818041c8000c00c6c0c1030201e900d581406036080d02c0300202d44031021065008250984808103d031000140b8003044131405940e644420007840c0c03030782c000140c600b1902b121141e000000701d50100f8001e642284c000c0c280c0030f0103460032504060200980b9401c0102c07112054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 735877616 1250 735876366 735876413
    0x1030c091e030f060c0807020d09060516120e030618030306042304140c09041220030c060f100812180904051c0810180b1507050609060618070309 64
    0x250461758120a1194015609000030449076041c068010078410340350092008111001c40d0710421040d000c5003640c00681c0c084403203850f40154407002010b014200c444540b09124040202c0e0500845600d0480d8200c260400344d469135544509100180c00000d10301880421041c810b034440d05441090a4001c0384223407411a0054005c0c46075515060890700000d100b90641c0c8144400543c1001408012040e00d003050340090207240c610000b0140c01070f038540007034040001d0070500c1050109a291160b0642c58000c48507884045405102c00d800d0f010f540c0d5150b1101e00c1d0042071001c00005400718580c05002c03003040f44840700100c1c080700d0003902c0482e501d5100e8180e081a51842d0542034017801001c0c03a241a0f43c1c904841c050320700c15a40e03c902c0d1440d14070410a1003031002103410400c2050780140c007900740d50106000c40c0005600000041d9003034000c07640410a41e60300840c80318041c0c0d5000748244111402e82c1e4441d81900d102411106c140f50f5296546400210187e15141006800011a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 735878866 1250 735877616 735877631
    0x40506130e1e0319030b15130608090d020a081c060b18030f0d0e041d030304050f0a05070308030a0f0603030e1c0804260f0304031101030c091e030f06 66
    0x201c0642840244500b5140e0030a120360b1400c200180007854040c0094a00032880011020110b551031900410822903041d001400300e03099103100d01e40b0f0b021a50a40e6074015a50303601040d41d616070300e05800b03c2005030031104140000c114407170040c100e215004402e00325259811041d0340100c6010b40c1c0031031202c00020503c0da1031242d01c11514000c41200382c0161440402182c8027503140e4140300c4800b41440024019075170b1030b031115440f04076200040214804094191240c4951b80e400480d0110340c2841200c4489c1e0f50f641e400300e8055803985e840b4000300f08840c20f55030359880f560001082c4052141d41c40481d401054001d0084a00540c082d85940211001d00070a0020344040e103032121000d5107030300d544030000030040c00c12142120b94518188d11140e10525400c2060b564203070100000e44580605812500320201c01041200c1c401c1202200e03a017220320042d410340b081e0503420404a030320a54200132054a451240000f4101c0c1c031079018605840399102540504006400d44400d6540c0c2d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 735880116 1250 735878866 735878893
    0x12071410031e1d010e0a050d020304030b0c0a05070b07171005090402060703020a200406090509031c23090d030209060d200703050a020601090b030a02040506130e 71
    0xc003204108a03501d410b002901a4501200c180a1585880409150b5a0000310111481100e03c080750240d00d00007405030000c2c11100039501c1d03400241c251031602604041140c4180000112801c50340c0c002e0155450741d40742806800940c01091a03070702445010425440010703980d49000e441001070752500b01040500e01105588d05034010400d860743c1d040e20805024560381c0c60340080d480b944c100c8069640c2c21fa9841e0481c18051307040402040714070070300c840001c070b201d26101d503008054060350104400c0340e03034370b1001c001e9910541d07241c0607980007044840e929801050040d003000900200100c0e0242c550040a02e042280c0b04402008200b48001e000301a10306106200d00d0070414030b01942030920b0040000c81d9480b521140e0080561789100b824005080700103000c0c0300e500148030183d100c0841d810003403b143c3c841d04a41006006101c0040307100689441540784144001c1e008014416107942444001c0030040d080c02d03801644c45460b903000c408140102003010401c1000b511240c0c0c003645 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 735881366 1250 735880116 735880129
    0x114060109080c040902060433020d0c030c1703010b0d0b1207050108220602070311070b0a11070807060c020a060c02060708030601030209150a2318120714 68
    0x284418100903190100300701141000a0350003840070202c0703000402c0d0119100184080c441c03903200d0b508008540e190707402502c44151440b02001d6243c0050080f1000a54007207803035a030440b10f030310013040c80d1201c4079010921403445015280d02c1404c840603441c5541c4c2c45520310b500f007680203d88000c00007440c40c110380c0090103190f521110544609881007031032003c0701d4071281e06005140c1000030180004201d00e2200300c880c1040e17100324449030040c410307130300300a0007035440f682055000c2108012911040400012014116583c01c0301da5800c0c0104140203c9141001801c22004ca1240c6800803880349801e10240d4010a010b03180c200b450126071041c402c2e51280c5502c03035001d002c29645083c0144c0c90300412102021f40c8040b503a9540d54820005038000d000f642409a041161040b03181c6500d4015001800291555100d44280c0303089901b4010600c2c00305400c1e0301c00e1a03000d000659050302000e9440c902207000400f0340440b40f02c500381e01c924141d201c1d4410030085050302c400c00803500340030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 735882616 1250 735881366 735881371
    0x1b0201050108120f0d060b1305031606030f0b120c100206070e01030b06071e051902030c0405040c05090c0414010507050c13180605060406140a091a120114 68
    0x5000a011941c903103400d00d0348543c0c4084401c8541d5600182607130070055000e08440054509a00404c0401d403035140e400c1d00c0360852a0a081f8070b8800090120b05898005103480c56039500000c85a040303424441c0c101d02810966001000e21038440c1050119a550342840151158840d0b00501c06602c00b04200943d03000821681415904807805110b01954002400c8415090a09011640c00088804940f052041400c0904022481d268820400000d02c00249001d800745040b0340307401d40200034106007540e12a000079410340c8009a203002c01e04150b0460b40e8441c2c0108001070354079642e1001710f0b00210044900003e2960002800c2c0144a00031100d071034855402e1a02c4ea040c41e0080e44c1e21075880c5030b02042103116010070003900b069240260442034640f40c1048041949000e9441c003240500010f032044c511560902c840072130110240d509103081ca00c0000d081450b441d2030803080c2c1c001412810120f1184441c644000b0100ea00d5403002104900ca034080001604500034000080c2c1100c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 735883866 1250 735882616 735882671
    0xc1203110f18130b0a0e060a030b1807170309091801020301030302031309050f01050402070c170a0b010e1e0c040317040509060a0305100b0d060c0f0210290102030c10 73
    0x103100b04e0b00d403561288071010050310342c0c0e1540d4200c192902000101c000d042c6a100400381c103860801c2101240305520702c400500d940404403142140c896045103414604c0134191000c03a40240550207062030030b6131100380c02c041c4c0400c0620307010990800b52426a4400d8005802591001400c032065544040c584030090003106400c100d61b0030100000f09445c1010700c1100d10454001c82c0200920080703002107002020b41041907a9294011854103441e0741c21804141c1c3c150042d40e0000500314403420b1698412380383c048544807001c0e4243c404040d1500c020b089144025010700000c00011180101d822950035206000c5c2c0d2594600780030041c64000050111b40141001102000010000264101e81001141004c03030030000c0c90020400c0a22000d80140c00307982011095064960841c030b04803903030182c81c0d0030344480c0409501d00009031181100324003228841d06649243d058070080340310802a10520589180607118610036203402c1a82041800f115903074070145089030414040f10090a41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 735885116 1250 735883866 735883871
    0x6070803011203110d120c11010c0e0a0e01080706031508193e041103010e0103050715170c0d02030f0121050c121c030b0f010c1203110f1813 62
    0xc00b444004d18020340c040c0015441c43e11140c03680041401504100c161192340c0008024040c80001c0c020041c0c210704100303e029006074600070985594680303c040c161080d1100912400380744c42000c6000301000390101010b130065500220308040d0503c0106514050384038100f1b08001642420300b1410244001100d82c01d000d00c4400d014030714444503800742146c100f1522104042d855000c100500495150000b41c100e0003c00400c80032035001c5804d050701d000b00700b118106602c40c65160313141209240f40c4800f00303580ba0707240e40c001c071503a070822584001200041030500303102d03145c410142e0f0000e9424041040c0c030040103000b20720014500e1009405e40150107550082680c543c141c8501300b10502c03d0088a200c420411180c0c030400003000143c10014610010509a100080080c00c44044a6204411904100300b99600c56141d80359201e40003a000c66407081c01c068260010400c61500e40408070003805415030664044c3c02078010039407a0360303028a1042e40d440810290102c0881c00d80c40552 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 735886366 1250 735885116 735885133
    0x12180b0406020c090f0a0b040612030206180c06040e15060a030b100306061205060d0506090604030e010f20160b070b060415030f0314041421100b0607080301120311 72
    0x240c910040381c10150305003001811482e400e0104019251580050a42b17210b0b40d80020105503000800511074100803200305008045142415142e0031400e803010390020062105200c5220480e11541d044841380000001152800c8046000c42e04482c18002c04603503500c440c050030f41452142c0803d942c9051900b000020308010029021140030700d480311040e6611000503045490f12044402250303048000c6603410b150542d07a103a0355aa00b202c0c03c4001429921035003441d03501030030140c0c0205201d915200400d0108041e80d0440028000c0000a030788030340304002c00c40c07005080140c0003a242e002e004564a10385410314000108000e88014040c9182141003055601121101c0301601d602c02140c1030211042e050407145031a10f840428218400001c0000c1c1400a000780c201110100340c7d42504c4400743c5400e100383d44c0b80140c5404030680c000903240800717101c00742e01089050900805031405c01c5c1d0281c649500a030801d070080c01103451a51564420706401030365040a01143c0c0c2c004140c0030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 735887616 1250 735886366 735886381
    0x402120c0315091e121602030601140a0806160c112e0513030204052a0d0605010f090905091912031119030903090302090f040215070b0412180b0406020c09 68
    0x181c5d04181c4400c04504003241144038200d0803603178141e1070358009003180c140b540c45580b440c1048504041003441103c0c000c01c00030305c0d28000f1a6a500c41c3d2444500d112120142c10400d503060007141804a481d44071803513a0606958590f003411182c109013403849005030108030720032800d02215010312400d0040c103204020804103200c280c0b02c10b0340da0640b00401e50361919414007040d050100c2c60700360040307070800d010200c248401e00134200420710418240a01640c9400541f29001e04030654000944624814460055640c01131500a001c4000b200c035684080940b640c602121604203c400c150403002511035241d00d8002d5031804801407415a00d0724890743c4890840940f894030355010706807100e07501401d142c0509504801150040d02d140d4103860000d02e490100141202c0480c494601008290a0341850740700380c80a46a00c8a001d0180e40c4854a608125a144400141c20008590802a480030203060244014048404541c0d2664100203019050001c0080320a0150b000c100811051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 735888866 1250 735887616 735887623
    0x60a0c0308060a2715060c02010e0607020f0405060604090f1a090c0a080709090c050a0f081509090102090d0c0f08030f04090b040e030307090611150402120c0315091e 73
    0x59502c159130301c030113601c40e0030b12460182910880c410a554240400068125004440400c643d4401d0341d0f1088101000c404101c0140545940650408504d2849503818181641310540200004202c0c60500b5900c43d8450309441041c0c0c80424180e0302d0300c15004484400603900401004221003000396894400c55825050050684260070014048089844107019130b08200141c9050401805140d08031200502150300071b8010400140d681c10f81500164891449a03014801c01c02c0c81c0d11840e000301040001100001d082c1c1c5c10995403c215038005503880c0f040019501c3d200f000e800f03116609d880100e0b02480d500b075201c101a82c10410001000010400407a01034810090300080e00d0103400d00403030001c20ba101403c9403203100010a00420310b400115980458601c2d9803001140c9a0540b0825110040c80042c14081d80141f070101c0c0043ca01988071142030070b0f4881c1102d0100e159000082c0c913088940810058441e800801d12403208000d0052481c00b10360894403400c20101011010341c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 735890116 1250 735888866 735888899
    0xb1c0506010816030e0625110d140d0e07170109050d03090305090406090209043801270e0604050402150309100510050a0608090309090a0b060a0c0308060a 68
    0x442000c00c4200e0703078456000c1c3d407105c5118404081100c48a01c1e0007946003003006407200840d0541906c24861034000e134801c2d45003103000c960407000b40c0b100c0c080100c401c1d18009104034040048041c280103803107486a035485409040d0084030005c0c4121032030011010394210342060482c110b6410989028049000003072641c8140a0303c0c540091044481d0400703c446018000c0000d500c0307400c2590004180100f50084e0020540483e002c02004602445c403480008400c0e02c8030f8815a00c000e01002c490301c0b080302408541c01c2c181040704aa852024100390400750751004078900340888441480404580b8080170b5100030103480c02c0001d410a900020003a2140310a10592103800200040484a02384100c480c00310300a04280450705043d00c034070260701c0b0103010b040d02400d50308400050081c03040700410700075100c1602075494041ea0380e080c0401044024602500240c0344d102e00505619064020800201e142d65600407929203803400030170740e06025055034032070803510106112643c0046107620 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 735891366 1250 735890116 735890131
    0x161109010b07110114030702011a0a03240219050c011805031204050c06041403060a140c0a1704060b01030b1009170705041104031406070c080d0b06040b1c05060108 72
    0x10a840340c403000486007170300340c0701d0032601070a0b0100a000d051501500400d008492038010615050074140a200c9859641e102c0a0b01c600340010b445d420600b1000c1e0111700d01303c0701081c00340c0303030240a290165208400c0943d101c005080015021441c02081c803070703101d010848400750745901805131285030b0340380034080c079845489400078041070070014208141c0002d02c2e80a00556115640d462074188041e25000e041802800b4220000701385080c18801c09120103000c22002c129030b182c40d20030029a4018480c15001d115601d04c01071400c2210050040c41107201c4d04c400300309240c01400040903548260a00c5001e10001801c5620305500880240180e80f91038880711140311586050394a0444117500050b0040d1030b121a142100407410014000d60380200f0b055102e410681603440d0765408125042d00002e101c0548100015000000401c541c00001034041780c10740121002031950351090b800707824060400125920b84400d003210004030840020070030495860242c0000c0e240340030007442013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 735892616 1250 735891366 735891383
    0x2030f04030308100e16031b23071a090c0a03080901140403021206091203070212090d0606090b030c0901030b060108090a060905010c0917070e1902161109010b07 71
    0x1601616840e8013003001821006014102030500003401e60340f00303a900203042d000a0800900005c0311428a500c000e14010503550041c0e080a0050740c4080b181420b00f0007090040100001d8010840c450303114105080c02040c6a180340c14620001443d01001e02030690044541040801c04544170600780d8400d1a8207007041081011743d09001071040c462038100a501c40680e010907100300600084040c4580003007000c80c0d0301950803106076403207400100d442e500180d01020701d144001001e10060303c84880d0141007410740c1d040340d94443c0300740c07262034002c5e41129503188113000c0249410803062260401c280c40507409541142c8800c000341078014a0a81403100c803030082058080100b09004095400000c204111416498140d02034522820008002400c506010a082031210903000903411250f0090bc0350500d0312041d0006003400400042d000c8201180f6500761705141e0000301904500f022880a8140342481c05030300400c1b03010891409802228018404220030380115910140c02008c0e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 735893866 1250 735892616 735892621
    0x15132102010e010e03030411010903050c31050f01051e0f0d02090c1e030f070804060605040e030702030f060606162f040f0c05071506030c030807030306050102030f04030308 76
    0x581c050148101c910141c1c0d071a01c50385019032603010001e54000c83c8200c9101500c60b0407407004441d002d450380400b4080e80c2040c101c0d50f4079481d050341451041c12031254055140e00605004592451400c292003480300e444034204010144044001405000c084800c2200d0341c1d1002400c002205d440d00e8564081d004102e4100304541d00d00c039602c2c10685d1700030014012071030700c040d1440c1c2c1c40c2c0101042d550320800b049400318034940101d058070b20603445801010303103542e1400011036000c900640150b031071315601d0001183ea0b4071036000c0d00180d81804001503544000c14030500d031804403501c0c000c482c1c030740020061007034a50720681150000c041800328940412035504001c0e10304180b0f02c81034460310070005100d8820001d295415036840104613401c010980c01c40c1900029106c8440050740042d030104410030000e60034902505130904c0a040c0002e01c04d4803540c0d41b01d070a0b00150810382e508000451400700301503141c064800509401e2024506100c4280c2400680740a1230000905010031b0b00d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 735895116 1250 735893866 735893933
    0x15040501030e100e0d0807030c050d050601090906061706040606020d080408040f090f0e0708032502060f0c060901060e011a0c1f0c1419140c1513 64
    0xc4190f0300710b40030074200210343c040e064842d641e2402201520100d6094000035840c81e010344107584c1403041e1500c8040c54056041d88400c01007400401050500c07208001c0456000d00510500010b4450b948a80790300c40b4803030065485601e002001a44a28100702080c414940e0215020000c101141801c01007601d491404202030b0040b5000791603003174079000d0005140907050f00300c40207180c60610108080030700d180d04151900d405014280c407030f80c008c0112020700715034990420055580510800804141540090050f0f403160361403c045490101d48171000103000d228464009410308000c0110341d1070858079011040052042d8180c80440b01c0101e0340c044560700888110f41007410a982c0c00c1e44070001544032854160a003c4407482c5001c04a209240c0a10003503e07588a4a6100c81e003042e00120000010302076540c018403c019408922809020f5801c01400e2141d0713292014004400414158100c5804014190092404860012008200040340140203080b54110400c1c801c0094031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 735896366 1250 735895116 735895123
    0x915060906071a16030504120e0a120b1b071709060904090b1b12010b0c0309060406080a143310080a0c0207060f030b2e090515040501030e 61
    0x10000d040f1030300703109002042c042d604904612a03121102c0128280d2402c100c00c0741265411a0300820561142407003110b580d004080702d0302080c20080c01684078a0311220090301c018200032088840b0110442807001e100501e40c803844203200d20f1a171b081d08048503611603803520340303100c00a80d044c0b1070000b0b0400342c40c1c2c40f40700480e0300b0707448041d1050096500300d15117094040d10031a20b000c0406079081d01c00c07480784c400404440032180107441069060b4200b5015910651003808d18a865110400c80c100003621400d025200410072602e074140c20741b4148010710107450280500e0780e080e01c200f00800111000d07407003000511218681c60140003403240c4401090350030300003110680c00018030404c1a00d986c2c0c0441500d210b5005014280011120f01c02c00b030340c0d60002070091101203440c81750b01c0c40304184603500181e1105401040c00701d520068040c01c0c01e1000340f080000c8800c510b035003015401d003504195000d005050650760900c0c58100140b0001e0b01e4091800380a04150720780704010110142003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 735897616 1250 735896366 735896377
    0x307060c0c0f03030f0809030316140409060b18060405010804140109080c010e1903020a0201260403050d0b012f15180706050309030d020d23150915060906 68
    0x480c0c01c0b120440c0c6a04000d090426990480c2c00018070110001b10350352008000e403409a440c0d014501c0c001c008101c019a400b500154402d048880d051100041d0503c15016401c0100214070364a80c0c4d40ea0300100040c03800b1180c2d05140e0044104010400840e617001c60900e501540040c00030720403943d455845809400302d0b14020b0030781c40b80401c90441c442010350240e040302080744111000710b0362645284880158403240640075800405000d030143d4060507001c00070720545408107001c0c40d0543c56000031900155815000100e001c51800d02c102103d20035040d0b0081e09080070f41d2400c280c181410300b40801034038446140d4020050340c440d240420084218040d140072400350062929002c035100d50071000300e8905141c86142c0d0006013040c050301c102c80c081c1841d0000f6619059000c02d240000e9401900c0d60144a5a111941c0b042c17a5a080140620407103c280740162a051614840b0041c0010103030180c0b15201040a020294030200c032070340c800c030209661040e1141a078000007040c50040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 735898866 1250 735897616 735897629
    0x1120206160b01090e0118120504030f0b0402010815030703141515041803020604020f01140c0106080d0201020c0312040f1e203a05060603010e0109020307060c0c 71
    0x60140d40708000801c0401c5058070890b070340030440440540d520340e081e501c81804442c070044001342a03402145048100000102c0303242000751501d0b542c1da440011440001009860001511060008540e4000c400d0340e0081542290200c1c009074003000207440d000e052000600c0361076803421751825018180181c044200c08514070940030724025001c000d001c03514240d070714411450000c207032082d8980318400c00d00264240d802855966117650a000307060f605002c0703003810300a0b080240c004158101e401484c002c0c9082002080c4a40781825142c03034084a00f0042096900500c00d4803045d01001040d40c07060164851543c0e6507031186e0410303201c08410340c28041d041c010300c1d000c0711401d40559946400070b07a103e02804141e6010720301e403000b01c50410743c0340c20f980503011100188030700911281c80000c031160015a00c4030050714440024103512044000c49a80d040300c0104006460203105119401c1c06000c000d005041580c0d0010381c507103110b8020300302845001480b03041401051003005000e0100e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735900116 1250 735898866 735898897
    0x1416020f030a1805120706030e012a020c040605181806012301170f07030f0f06050a0b041214011b09030203161a0c1510170106030b01120206 62
    0x785040040c5207160f4070f8418104581e18020000d024181142e0200b10400900050401942480d6048015202048407402d131503490328442c9002402d1842001160640200500560300a001000c0e08004c00300381074521071407030603100f0090f54613119402e601d0009c03032440f21219603849841a0101c0c804030503404e0712500c903003c008120020b04541036032526803034245a10608550f01d00440750300c08044124107010703401c40007041740700500850503500030315241800b0448220880d10321007181c00b0000300700100354941e081008241022006039020b021100710203490300b400d14103882150342001030001c256048214074a0b0300c01800398803180a5030b41d80310300080c803032030302c16001446a441408240e22a000f40c040b4954140d0015120008071001000360a000c00360304017a07040144c0044544245c1d038094a041480212040040700384503a60a121010506040441da903548004e01442140c06d0b0385000814404a0407890040d41110000c8d1089041d5003650300c0458001e00600710086811171 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735901366 1250 735900116 735900127
    0x9090902210309130e0c0d050c1504090b03070503031801020f0f030406030614030a140a0206030c0c070519030f1103010f0b100905180402011403090706030f1416020f03 74
    0x203501100070411110f044a0050b40000c000000008803005501d8100181d440001042d0941c14190400c54640d8011001c0d41d881d4405a800f1034804555880c81e5488500006810b0210303000901c1100ca401609038010101b49007800d003c20795901c01d40ca40c5130210200f080f0f450416a2017080700003080c85034981681e624909495244e5a280c01c00d0040c000800d0a017100413950503504044c201900000800414407401a03403940501408515002000703800344d44103202c05604c81c0c9004601644a02091a60728102004d00c1404c09149800407440b4108c0040020000098100f1b44400d40350090503c0401101d0340c42c004e0140e04010050750b405500341510384440d0302d05640881c0c4c13200c0003a80c840c80155040d403021071380714841d805015440301d000302029825040d203e80d0154040d106041c130b4072000b481c00c1c201060940040310302c15182d85c40418103221890385405140804007140c201401410350307001600751300180c01000341440300004160585024401c000c2d0011b0b00300c8000075a650752 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735902616 1250 735901366 735901429
    0xa022107051902040c0809211b0a0b0109090c03120915020c1f210b181e010b0a0f12021b060c0a02030301060c030e0301060b070605061009090902 64
    0x9040b100c0007688502c0c40c24500c0c0c04294007440d106486030804202410140100c140841d4000e00e882c500d444122030b0170700000c519104002c4041c0b800340c150b0401441e86501e03d15083c4e140c048160402c070149410b081d81c603000100c0050146080c0c0382d002d008440c29407140002140c4100d40303036000048140d0400e00500b90b054010419510400050703ca60041816990150031643c5204400c030f8006042400c0d140460b074645c0c0e1000d1030401c0c40301c0700800c40350701010010b01c01e6448580504804810b031307800d100c28000ca01d0407503442025418a40300c01907150500c900b00d1070040030301281c1880a144009482c2a205182c50781040f500340800b19150080c4182401c600b01082400d441240f1545002c079002c00c806606a0b07040c042183c0c02107245a0074690f0446003039100e00c0f011014025812619a041c1d5028002d02d00a45400c4548580b1041681001d005561015003e20702404c10030300c00c0300c202c41e8400b241c04141c51203070101007440f0b07110348041100c002c0d511125480c0755040c10b055403c1e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735903866 1250 735902616 735902653
    0x1a0c030d060324050c0f1e0706140f060d03080606090a090e2505101e08060405010b092407050111040932130501020a02061009020a02210705 62
    0x140d0104054100c105081d09150804880054038050117001007030041390200303182d01e8014901c4802d005074155419043c01c1001314640c00141c03044510342d0312400161120318000b24803d51055803013880c0c0d09103082c01c40c04500840596030000e4100080b107030004806031a02006c8a103840380c040c0c808084d99584e121083c00510102d103000c0640e02910161045291000c2c1c1c911129900d034030704640220780341c8400c02c9400400142c8a4003446540011080341c2c203140b140d1b801021100d520345070310300e01d0300200300822990305801181020a052100b000c00d503c8035910500040c6c503085442d071403188030500e48031440c000c02ea0028410f40c02c01040807007192200d4081e104a0708080740130b0011410841103140c40c117003440c18594154005410400040305501849508800301141d00c940e00030442d2a81426a80040904000f5070b00403024007105200c0e452120380101080b400441c144a5024802501c0d146991810648500e91001310580c59401c0c0040f07414095201088600070301c40300810890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735905116 1250 735903866 735903893
    0xd0503040b43050a08060418020d030203090414040510051015020f0c06030105030d0302090103151508010f1a0904020904020c0601060306150917010e06090a1403041a0c030d0603 78
    0xc202c1541c00034519000e442a01c0300c01050b500c03140700981c4c5000c2407200402ca1000e90103202485070780b2040c05070f00ea0810441159000343c2c059552341c1e105106200a441c11840a901707803421074010800030074004940f4004d0300f1000e0070003141c240c641c0c1c4d0b81e814600c00c480d08071510080e50a0260b00c18982c000407207559641e212026501c1d031942090030803460740000d11500d90543c018261424803030388241c0c001d01c0c0450050400003080d100a0414500580341e40d0031846000494041500d01c140d040b030101c0c0e005010070891418034500701b9074100010b44505000130b00741e50b0b0110300400c00d5515038040d82d0505002a01c11034542414680319030399040e0070f00c1800082450000003242101d1032200001d5886501d442d480e00140c54010b104480e041c1c0c1161304c43d41e5568890110320304010034880307540526061300041880001a007403c02c042c08c0911804205640200001c2104070800c810b0b030300d0803101e0a400d46465032156908203065200c0c0e010401102858103201004020b910b04001c1c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735906366 1250 735905116 735905221
    0x7080f010f02030106020a03051c090f02010e0f01050a18181425051b010603112d010813060e060a060e100302040506030a02120c120d0503040b 63
    0x1c14006440400c1c000c0348020f024100042e08240391003400301e0b00030b20040c044007607010725988860b4080b01c050030407039040c05400c0310241801d0152100395a44040200700740d18040703450101c1700c9490f0001901a10412030443e09118904055081d01d14001d0300042c02403940c404603a02d00c0340f400154100804108800b050900d07541d002050700c1c00c8001072803071017042d164124032000c803120240036503a82e00000162a0b02c0d490408035074800110a0280100452040080c00d101e101e100382001401c000c3c5a40f0601c503100640700c1c8101b500464041e441d1191000e081508032070b11421990201920140c002810a03801d2122007440715400141407440340c4c04203002000303156210750b08a49103401c191000050f51030507040c1400546030aa006030f41040f001822500f0f4841c50341c0c00b00d18284c49000440d13a850300624105181e60401c0c41130b00307242c0c1203100c0260902e04d54140700a0247d000c0a0310140840d031050001aa505055920f100180440c0e8000d0600560741c2e000910000f0040b0080741 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735907616 1250 735906366 735906371
    0x120f0504030809060420040207020d03020d020d030b0a030b0402120f060702060717060f0a091107020f2215120b09010c0216090f021306051314011407050c0307080f01 73
    0x1603403d43d0301044032809103030310201e000340c900107111803440c41c065282c0000340e0140c0d0820003040141d8404158054040c826006040d0f9461030f000c001e420405018542420f0506208503008503030380d020b0300c01040d658414400401c41e1a80d0000c0392011103800c400075109e21520401b0711103240001800e0784541000d60854000b540c400e00222207036400394950000884031030000c11054500803040c216140c80c00b524490056550741c81c14019113525010588d5601400039003103055003445288c103600000305840c800f1140e00301008074065113000725248000981d13a1443ca58400480041c100010580301d07000200356039190034076070b001c20000d4402000d150318002d04205054000700303a040d0400c0d542501115846c1c54102c90340c016003c1020402d1095500700400312400c4204a255000703030941e41e903419115601043e4011082140b5041440c10401b000c01203481680d00845440c003800504500c0e98076014240ba02e070345011006e45025505008888002c40c010740e00040004004040c0b9009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735908866 1250 735907616 735907621
    0x2090924010e0703110306091503030a05090108090307020d0206030a090602030709150e0102190503131401090b04030807030c051006080102030a150f05061c0213060e030313090c120f05040308 84
    0x35400c40391180000b08005c0010310001c0c00610709100040e903c1070045407000d0180d61b43c48000303400e59001c0305289012542c042480165968000a100e5110f4080c6c0015840d048054001440c40407003000000d200c0d2030004005201411a07800211000307501900640d2241402c980c090113a1201d07000f200382c00b101004d85000344c24841e00c0304185690044e00989440c955500300741c042c4040460060f142803200300b21444e00910892031641c028802c9a07403118100403524001407134500d0942c403484105009000130301c082038050007161015a0b06040ca041c20020914002c1d0403d61007141b04030b01c55140001c000343c1698190004d6114420344c4030104508004882d280c0c4255645024030311030000307040e10500c004e041660003085060301c12000c5030f50907044c0240500c02d0368032510410464100c0c0030000c100d6507404c85004105002c003140a9400d111500c44c1e003892151f51803103150309003034581c50301c50200c9005030750344044c7c64901802400000d940b004440040c003c10b4400300c0000d04580300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735910116 1250 735908866 735908881
    0xb0f0d020c0127020906100c0c1d0c0c0303060603040c09050f040b09010908120c04030f08090a06032d0e07060903050f24061503130b010b0309070302090924010e 71
    0x643c0c01c040f40d009141040726100e44080c417001d002c141101d201881070409540002c940050b01000062014045e0619020500e801042d40d11101404003103900e03009120f41c0c8440304003c8107032070380b0207002d5444039140c0d9190b04280714440480d6104003c01403600d010700c9041d540814815100b54001e0b0003040d07064546403019400c90341f20881c00380c9410010302c20384044103d10300042d5000301c070740300c83d007400c1503165200d00352109100f1030215500c000010350b030222420300294082c01000306081c20003400d0501414041e0761680ea500040e2180510054443c2001040d4880301c001065003003120261515040040d000650f54002076480d1301c25068041e0b1001000500554000840500003071100094003010309030103c05005541c3c810200700007026410010340245204050211000803004214104180c040c0c00682111303040340820002c1004640c0f0028048003106d17810f8a9202ca0b554030031001c941072500354051817402c1941032000384903628450901d00d041c0d071010b01514203140c03200324 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735911366 1250 735910116 735910181
    0x50108060a15120b04022412060117010506090d050706020a03090f2907023105040b070f02030c030706020a0f081003081b0109060c2006010b0f0d020c01 67
    0x4070b028404003246800c3d01c00210301800c4603822900c090305c11030354848050412001318041030602c400c5c0207c007060b904c002e822a1050b69400150030b00b8060383e2510080c10071141020140545800f0f030f07500144244858546031600005c41d0b41003000d55114030703160000207440f5000c5001c141c00003150b00f14045a0001200408411240c4030542100c0720300c640e034000240740c540919071300a40f2605000700005a11240360402c821070041c02c12859145c0202c0840c0100d402042c408410149007104110001c0d000710001170b08807001d42030900005050010481c514030465000408500000c00e0801c01c014454025181d0080b598492000c0900e202900300c030407000484a2a50103403450204001040c0790b080141780481c00000000d440b1350010102e6070954818050032071343c1580c1e444801290036445119103059240c1214144051004081c2d510754813081030251000304840000e401100b00131a004a5280c201c42401c207540312000c0e040914020305201184020301c8100c0c00ca52280c5140c140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735912616 1250 735911366 735911369
    0x9051b0f09010f0c080c01050609090c09070e0f0418120512010302190801150f090605060912240411010c081608040b1c1b1e05040504050108060a15 65
    0x1004560038007118000444203001401c440806100782d5890050114102e0402030850f500d500c0004030725803e10720248507215000600c1100c05da04015040303a030070f66443d101d154100d401c81c900f50400030806000174504407560900c099001e854100880340180101d10810502405000400400101180c003a20f0910440f1418a070300201c2c40014001031401c101d0300004100d51446074814151200601400c41f103d101c540b00408080c098100b04a100b40c1215030090444100c06001c10351800002c50701c28002c20503098805c6244031081501c0c5001003080d504200307400b101c507101c1c2501c00728640644550a40f4265030482c10b03402e402c0902c0d40900350701807172140c1c015910b925000680540114900c40c654046903100390070400010000d0031480500f5160314036030940300c00070710840307075110031100c0d0b04402c518240702c28094400e0080d002212030111900c114110880780c80518422a07075403003190445984145030800200d410180000c00c1031161612400800007401441010141207605 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735913866 1250 735912616 735912637
    0x230c2b110c0607140d050108160b1c111303082104032f070f060e090609011701020702150c1902060a030b2205042306011a0702030709051b 61
    0x1000210303c0081c8502000146080303040f0f04c0c5401c00143d08203034070580c0c000380d21030b1450380c0c441105002c4002d08415000c0090150086491034640550700720360b61000044554600d05a56403c01c0420511800c2210b25010320401d510305115224a44210150080c41e0000d40d0ba03d41d20450741503031074204101ca40103a406485411211009451785500784000080507202e106d45503030703801d041400c100b06500142c602003640d80c4084c2d083c41001484a2035011845200304100d000f848095115011003a06607000101d0346000134000142060180c0b0803030000a4000c01d103051004500d03800c43c3c018010703955105060b240c40d840c10422000281d18101c0000c1e50000b0308000321000031340242c0c025003458401900d400046011200100c24a800344919001916261303c104000c11003006041d03880b049190304100c111039a400202661010305020301c1003000380d0800b10003502c90380c44095030380c3e0381d40c010300f2104819100c08003070014082c02e4440105040d648981800b03001d1403441580c0300d4104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735915116 1250 735913866 735913873
    0x50606040308090d14031c02040f050418052b020109050c0616051f0522060b01090b070507050a080307020306042604030803011404230c2b110c 63
    0x2591901942a8000c0e01c1041d4042485801000000c100c40494560744100c940999114a050020003984081c07181c907d054241c81003000340000140d0a070b080f82a40c2d026503000402550845820180c0f40c0d669901414a11548201002c19000c20408003800360200802c41142c080041d0284d0984070200c100510a0f04602c85c0000b40303040c00350284c0001002c0e07002c040841011504c0d0907084c08039001e100e100904401e43c04c0c05081050703006444d0800c802950f0080c898001d410341104810300c444e40140f0040c3c5030071705106141e10070b5140b0400f41c864004007550368001850010755a82061207880e02580c40400700084c4070340c012045d291840c0c0c01070068200c580d9295101200d90015108503011300c2c4140040e170440c00f030080c0141003c2e512030111030366a541000030340207049080b11040e0f48182d0900c51400407440d030090419100b10014001c120883d210201ca40405004a0b03803080c182040040c07048084010142040500d0064078204011402c2090038058883c032407802d84090560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735916366 1250 735915116 735915119
    0x5070e090a0b0a0b04020a0c05061e04030f0512010b1c2013090504030807080907050d1b24030b060405030d080a090203070e041101030c0f0509030f0303040605010f0905060604 77
    0x82c11110707200e500c0708014a00003105000900000c040f41c0216401c0d0b80000c082012420820104000964101c0c24280800c40710b403d10796072440c8240c01c000c4c40241004215006801d801e4050705c03d55110207a5010000d04c60b68440c05940459000001d422600c0d1210000d10100100c26104500b000d00c516207d5090710226403030b500803185c1c0083d034014003c035200540060144028030a00d405075100b03540d00c41040c02c01000051029074050900b211541082c44200915610b440000090540c4036621040b60040701c209000d183c02d013980000c140d81012124102c111120440c200d5103c00d03151803c200030740d11441070005501841c052550568400704d10401300c14052110150b02100080d008038041d240e603400309081880b0741c0d010b039441c2e0844006202c104602003040d410090f40a1030100080c00381030800809111403010385c84144040080d080682d46c030240144c00c140340c00c54040700da4900f0185000c1c0300501c0248624201000b4911005c5400c3d001d50144078002c5c076008100b00d0515 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735917616 1250 735916366 735916373
    0x10b07210504090c181205060108031602010e1c06020a020f06010b1b030d0e030d05070201140a0b061b060f1006090b0f120915060f0a1505040b0c030705070e090a 71
    0x50000700020300c11303c8013944182c0154a080c44105e07000e0080c14035106011703122450000d18045c810380000445400920904420398100c01500030150b4092038070180d04940d085c081242c480015030020108481c00142400b803000c290001c205003900d43d0708075000c0340f801d840105c1d15980280511078644e1001c004081000d280740002c0c50325189100309403494071200c004510202c0f03590f42e0380c6c280560000300300d100c0403a09078030aa036841410340c0028802d0b40c00341c455840450200070101500c0907036034a01805661201d60540301c40c03403111401880040d121071a0036544101c11104141072a08000c00166072806050352403084403919210001c650341020305405040d000844005026141404403440301680600c2150203600700070b02420841101c0b420407001c0714002800d10f8022a0032804145a41c1c40e070070400c000f2034a040c00840e015903a1101c08503500c0c411980280c117444401300380004040004001448680d01c150701700c8206998a410707240304110b084509047c0d40e0061004a80403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735918866 1250 735917616 735917621
    0x30512090102270a05010305070806040c05040513090b0127200a0e01030f0b030d1101020c07030507082e091703070e21060106180e010b0721050409 65
    0x1228900d4005414a501d0101c0c0d42c1c0c40e07551a0f520781030220502d07181d42e545410100700e49030107040c084ca0f041c1321907c0d00e00805403600202609150003550741e0545c00b60035912810648000d04002048040c500c0d041440c1240500032804041c2c500100301400003401c00310143d4400242104280d0141914641ca001907009110016105840c1581000b0b034444400246000717100b03e009a4a41c6a0000740070303c0011f04031461a160b85103014034003244150305131b800041b0800903503c540b80080a07100b40d01c012601a0091450b41c00c01c81c480c410012040000201d080000d88602508880043c0030b0120b100c0030200600140c504483c110b0b03801c02c6a000082d401075010f0f140a02200140b240215001c1841c5501c1220a80700184403904002e100e071a10005820313442107068043c80058003c003030144c0d10f407041031140e8400d01800720304080c0c4258040940360003c041c9140452071315030b5524000380c141d0f0f01c1075400315914000702d00c5144003484007542c400030710b240c0340ea5510305043c10201240c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735920116 1250 735918866 735918871
    0x50409050c1905032203030915050601091806030b18060a090f030309050c030d050a0912111c0b0a0903031d060118140a0e19051207060e06150907020a030512 69
    0xb90891500c50541503050803144002c064803987c1c00042c402041d04007044c05038503c6050228546c11721007032144903a0300601c500c0c195038040005080c07064001d1261002009244e00080c8240c0040c4d040120311071000d02d01031003017902791090701e9076607a03140c1c0c0b001c046a40c4000300400c0b2084003100c0c030340400d00c20ba000035001880340c0e0484110502c04d000003490304034201c1519002400000309110240c1e40880b0080c01440461026268001c541c0d03284000c43c04162160b07400381501c00707072586000d09500c80d0074604c10703001602c1100c90306204d800f01d8040c0540c02419004a810704034690110019542c0621561006401500040e400d12804480c4c4611400b40c11650341e84419200c072100c18a10400c84c05003603141c0000626000b00307100d40b401c01c0700d0900391450050400c12140045140440d007141d10917120a003190b60b0f0011454140c0c020071403614080401e10074041040340e2041008072031150a00200d0b15003410f65158003089079103099048000700000e0b0180705a00042a14010258 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735921366 1250 735920116 735920131
    0x10e19111014073906050c10020309070b0714240601030b04110d050105090f0103030f031512060b01030f1a0402072a030b0f010509060607050109060507050409050c190503 75
    0x1080b0f1500109016070340040400b801da13085003036404600b910444211071000510690030900c2c00c0104988149842d00c00901c00c83d041e083c1c0010000780c0f00f100a2007000301901c8420003c5403503000e02d04180307400120042d800d5405115152746d0300e95420542d0601107040c0b500c0e00c1c20100e1079403640011009480010941c0d90059100c0c1b00c0000210f81100251000310000200010150714050411085410180522070005140c0c0c00500200303610004043c80d406c0e040c01d01203a561031024401c83c0350700c0d03180c0c0101c9445007041c80a0341048519084446008800d0f43d00344a004094004901220801d005007554485010034150f15400c2640140c00c14a0045402c40d010074410f8090035202040c1101144080410300d03000d008010f00310003a03941028401c1c590118540c1480085051450b0240250384924000302c0e4038410840e00b500044000c0c0d600950900460600c903001614580060040110320750804000845000c82c403c1542c0342d580701944560000100030b401074440798800762040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735922616 1250 735921366 735921383
    0x7050106031e110d0807030c1b030b010e161e09170607021002090f090a09170a2304051504080a051c0e01140c010e1911101407 56
    0x804940d40d038a20880b2034081c490300140e80c110343c0c40c00e041d0507068a220749204040c820b0041011801440c140c914107907050130322042c0c0c10720030b0410b06200f002a107070741e4101961070038000c4100824000118105c4030820074141d070644602c111242030003008205000081d640480c10724103121600000f110030310700c505066600301d8503121441060500d8039128555980600c1c00d0205190741000380e20010b06040c0e130218140362f2244001000c010a0000c020b01c1814901c001c00c42e480700981c800d28009074041121190105a412084040e810055880d00802c12003102c0c441440f075802c02085120201d001481e1600d803c000400071b071003855001202040300180310119142c1700070442a4240c5000d040240500032900c01e190031540100714008080000c5c08a41c1012640c01469020340c52615550386074403640d40c1d4060707900400c140600503441e8440c1302400d440d0045c00302840d02180380141c0e00c0004006616090005c054000c000381d100003010304492000040c03c3d074014001c49445801030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735923866 1250 735922616 735922619
    0x10f12060b07050106080d090f090f0e150106020c03150109050414030301060306090b060a020c090a320109020307090b1c0c120b09060105071b0b0403031d0f0a0b07050106 75
    0x41441c00d40002004507030310783d0b44810510003038030200710400e81e042c540d1501aa4a500b1300c3c030001c0080d801403041e02c24032500d038080d040360800039420a441c4850580f0441c0c0c0340100448006002c40c5083c0318038005070041002d601300300d04000c10708041000c1c103404400c040340d2810010000420f401481034400291a810804c0e9403602400114003d2900b43d501203010b0b810072080d4000c40305131055a03131044408115040a15401081180c0b200c0412111441d1300d548140094001c6c00310b480d81100d01441140c81041e203100f030310827001c1842c2085605841c03140e880341008812444240c0782c3c40041840303800200f050b600000000c1c24401c000242c4000047c000040c8031096856408400010a0342e140031344407407007420700ca00381c04080f04072a0b0320b4a50030405c0028002f40318107140036003040100074000c0840695541003070010000e0700191682c803640c0b030600509044281e0040090070581180d6111170303180586261040150080201c41110701c1c244001c1d081ea03008940c02c070303001d540340e010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735925116 1250 735923866 735923879
    0x20f180a0308041d090d0801060c0311030d09150b181f090204080d021513084501080609190608010c020c010c0c030b06030a150f0b010e010f1206 64
    0x20308010142842d40403284d03601c02e0241524210000d01c050000d0744210f000038801a40510707107904664140c180804005501d007000c035026115041c41041e41c0c8000030b09100704001030350024107003d00680001100402001003e01075076460400903510420b41a140f40300c0c0161031400940000d02d141d50300c08501c165840c888004491980302c0c0406517804a801c0182210900008018101d40c1c07001d00204000580703c00b04144014103c892254130a41c43c02c800c20826008607846104060303030450241d40c200c0300c40091940c079110b01c014000c44140c4907114080030b14040041d5020140c45642d02d035600e0809024040c24010f01a20303a1141414203222000c22610902000e03004400000c9845400c194001e85461101c0c0d841c03e040105006c0020041405050864103403548200c11282c03a444440000303291200c0060007622007aa54540440740e81c01c1ca0b40500f0b0001e01a4106001444030307000103468091141070b105d8041541e404804040501c030b0748540c10503280038040052096159030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735926366 1250 735925116 735925133
    0x3020312160f0b0106090b070c1502010221150303070512070822090614011e0e03071e05040209030c0d050f12120105040207020604090e0a0204090503130801020f180a03 74
    0x48059450b0b00030f000c01808020380c840c4102000d0007004100d1481c01c0610741e10200740803041c1c07140c8110703c5203400c501c14980b4030039012548140b0b21101000600d4980c1c4100340681340c0d060340c441e10b00c816030a08410b580d0030040b00b510315180d00704c000b4007840700500068600d1030380301000440d201d800c104030042100031800302c0300000c4d003500b4603164a51824014401c00311103e0341c001d243d019014024110150380d1080c03052105d510540840050341021203825210054000307941e0343c0c14003441002140100c14441d148858a143c546035681080d552424001213208042c045034042c3c0104889030101e003044031034551143d124008945101c03d140c0422800d0502032050320701c4208000801d4807041018485541c0540f078210b40c01c5241c044140e0001d4100c1c80b4505c61691442d850b06041c01142c40706200141101d50090302c284a5407031709151103034403503020801c0c1c0060f80001c1c04003c0b66450b0140300341c454150000941c90716003180f1210740c84007400071409659010754031043c080300040c0080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735927616 1250 735926366 735926393
    0x1508070903020d0b071106090a030509030a08190905010512040b1b0c0d12050f1801110f0d050f04021c020a0305010c030212090a0f2a0e0a1103010302031216 69
    0x380703140713641810901d1000f048144642d0000c506a03104006201c480c000106490034403590508190755500c05040220b0300308104000040d003130030408507460450040ca01c207140d00e00b02c243da6803c00304540b079a0040d00c40f07010b4804250302900041c00018009641819002c0e0003a654a4074520480341c5829049501e42c072581602842e50429628200e40c181c00909400c124030322000140514a010030b4443c5076094000c2c185041166244001c1608240a510581d2449008003407242d641c04880d4000f0f03e1980160800c6000c1445c1100103064400f00d0785c8600c0c0030b40d80c0103190070b0084094000c01c0d6143d80c4e15541c1a070303121960f200000005002480380e95a01c10b1591400760322151070013508000340074003c0c0580ca80b5000314142c0000500d01c0e032001615980d0281c4850040543c0c0340b0000e40300032003c0c240e868200d0841d1804220545800c00303180c4035910300b06091240019140c064a414002840000e40541c408200f4280303040920001d804600e02071441c4125003070a9803949008018503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735928866 1250 735927616 735927623
    0x90204150501090807081510120f03090b03090a14031210050316060c080a03180b041407210501241a03070e100504050303040905090606010201061508070903020d 71
    0xc09904011658000c0d4481c40101a45400381c0286031505a03516218120304a9134441c2c1a10440040c0807070305487d4900002e1b0842400c0c40356121980d20f814141c8001940e030030343c0070a5030349a0018031840f05404484c42880caa502801c400c01e080d0b46c4e000407524a0142c2c0c4c1d031160009000c41d0700c11000004072144501c608a28400c101e500c0e00003450308042000761940c0800c84408814000700383c0004e081ea24495016150a56a00c0501c0c404c400800703c45141903640e5514542d980c050150426a02d8003490285051019201c0c00141d201e60b01d007807500c200e52015100407203919250315003003821148240544004038444052003203501918004d5080d0000c0be90205400b031000190484044034418400304010b46181041c82d80034210800802840d80324494007450980805c1c8258181c3d40107280203800c90b038881e911001001c024140c2103561003100d110b40c00001c0c06941c414002d903c1259010795005101100c65282150601d100816035070070b001c10f207440000141c40e00b582c0c80003a60301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735930116 1250 735928866 735928901
    0x2040608030d230f010b030606040e0703050603070609061b1106030c04150c11131e14060d0c150302130b120a110307030f09080705011d010212130303090204 69
    0x40354001c486801020343d68290049440c82002041d920024082d415a4140c0c00307110380303980d600b00018045d031056030012070050b0b40c0c1005210240c0d805802490203100d0480a42d0469511000e0440c1e030f105d014411100014104540760505a030600b010851503406250101082c0050a0218156500a603960603240000050400480c07102d032a1904a0303058601e0911004034480d21901140000000528400c5c044401d80101c08200c42d4041800c0210000003103800c290711084000082c0301c2d60022801082c4c4800c0010322900d04403228041180d8001da030fa141c5c15081c0b020181c2c0c80c1d120302d03001c2824940d080007002000d84400c00c000c0020301c426000181d07645440038203070020340e4000d440303100c800b42440c0c45011165110000d507035008a1a00e070000e01d454510090350050185000040c180c0380c40013650206101064100200000c1c40f0010184120981081b140c00c070b00c03c56090b00242d81100011a03000382520315861070340c500900c3d01240bda40550009403c0b1030040f40081691070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735931366 1250 735930116 735930131
    0x2070906060818030406050d1e0504030e0333041a0c0310090213140d0f3206070825172a16150c1b030c02010c02040608030d 55
    0x1900d60352800003442e070780340113141410f16100c8003900f50f02070700100d01d80e40c030388400c501400101c0c0e060b540052060704110503c83c41c1401d080140c45403d807007040e1030003406000380c20501f4030f0b140c0d8445908040c03070710349144803207262800c0c16091410240040b0341103a41c13040010340400e02c80f41c1d00b50280e2448803000303580381410340402001d91003e60181041600600080748110450ba10a03001c13610301074401065016034800056030080d04100003010900d01c0712030102801800750340582c002d03050500040018140304013003800c040315050040d80a81c452400214903c0c443e41e51550003d0301075100080d0030200324010203104002c07040c10b800241e1407464480c81c12a0341400f0a810581c06400d2400d03503800e242560840c9030a00080454000000544070b80c4842c9a1001c1000b01e0f422080341100d0803003480310040580486400c83c0c000481d01c0104a2440030511008403540c2d40c141c43d90710b900b0160f603005650528040c0c0c4241d90040e52240001100300b0140010290401004000a03011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735932616 1250 735931366 735931381
    0x90206070b0f061507020d140106090b030c01080c0f0a020703120e030105071e1409150705161d090c0306150102060f04030e0121060f0303030513080910020709060608 73
    0x102001800b0b24424a020308804c003112100700c040b141100d4050340e20b4407114549080903a4080700c0c1c1400e0201d90740c0780032000141c41d6802e900030006442d0841c10b40c2c1003d10983d004488021050700c89440c00c100c200504405410b56100070420603007a401521580d550725141c146d8010b0000c01000041000c2c144402905d240078810540d00c52224240450741440c204180502042c20301e005005101c0e19004002c003030884030096400011005040151035448440c520380780d504050812241c52180d260140c12546000e2080c0d41624950002d00c81c02c82000b082e00d47c2e6001c00071700b44424038050754800041540382440312a104008079214000541c60101c002854007074010021511466007005210000384e0100780c440d2085424031704410004074800c0c0d480c0083e49440d920072402407603d1000036142640a540384100d0780242c40030840d5564500701058040210a0000c003601d00c00c011600c2d903481c14901542c40304506104440d01ea644035001e030401c8500f95040000450244020003010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735933866 1250 735932616 735932641
    0x6020d0e010c050f0d0605090103050d110703031202072f010e010c15090c0905091e0c0d06020d060302091911040807060f170703050411040e071701090206070b 70
    0x40c1160003008100d540024500108980240800148030383c0001650501d1550603402c40c0e00903290040c481c049550b541d20380281c1c0c070052352894002103030f514007041c850703c1c40104240d82102d8140d11200d024030000e07410301d40203500c030200c2101c0c016100449404141c00741c0c40001420b40c0c21300202c07003500007800000350980e1a0000c4050411005443c4c030800240b0150300c07a01082c003c008085102c0b00980350102c1210950741102c00080c0c9802e007000000000010148505107101c800040c2009000000d00d807a0b031900b0b00b8994021174a42c07010000150641d00501c0c0660a0040c00103400d5140d82c0000c100742015902c40101402410b1800194065032045400224045040c585010310f0840c0e0329444480a00c2000309000d822020b40d100517000718203406480c661181d5002c0586000c0c1005001072006440c20b8900001c41c40c0007241900705403140440c0d141d6804003c100c1c0310f182650810100303000b02c0c248000e5548820100b00141c807500050165144210311014491034610354034046c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735935116 1250 735933866 735933881
    0x403030f0e1f0c0525050d02030904150e04121b0804090c05210402130f1407020f031e12010e0403111f0c02070510090911180d15020706020d 62
    0xe091805444071034144e003120454440c0051a00039010215258141400e0040c41c180050241e02580c0300329100c0d941c2c0400200f8100310201c80130048214000101013a4111900520203418417800c0070401196029414402c600f00a1815102d242c11008016012094000c2e0440e98054045400c1c800d200c0940143c00f85030100389046030610b00c403850a03003030694487c0700d003018a040880100d425510740c000c4910318250b0355003043c440742140c0b500043c028103044031000c0782c0c4280342000c80d600c20302c0410610b41c141d8040000314200b680250035100c080c1607a0704007189041d41040805401d955082001c2d000307241e00c1c010440145031a0601410303001500c0c55008040e041404983da00c20400c04070251032603245140014080e03600348050345800e115411842d80701c0301d170243d80700f1080e80c005d070701d201034560b1000c05000090744503600c410540200d41c1c41c0c3c005211201c21007505800d0801000414500810061a000840c080910200d038003418080e5403050300000c0d4143c5d5096280103102c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735936366 1250 735935116 735935173
    0xf0807050c06130821091e0607200102060f06100203160809030f030c0d050906070b010e2202030606090705070803070c0614060109060e0f0307140103270201080403030f0e 75
    0x1410700440c405e8240c898490348070098818101c50080f0b44100020303d8580a000801400ca40c4d81c030b8645007440d00b4010b40c01d8642c004000c0d82c40c400011154804a8201e002d80c5910344840d80c42c1c0c44074010400d80c503c000101200b1440180048568038282507640b03075055000c4c0746855030390b525280605040016101201180d64001c02101c92402c1c0001130020a6400ca443c3c07082d2075034600c20024199109801d0064814902d4900100d10304500b02c001500a460041030f84000000f28000390713030140c0140c00c02030340c580c00c41d00002c0c03101c1c184070703440c2c90f445030303251415900d4540075070307541c2195420a6605034005070403420b0740800c100880c0f0035025000c4590000a089183c1000001e151800d0b0f400703410100001980441000d44402e40070004501e0010140ca060b41d441e500d012902407840714207580020304000309414036169001880d950041d4851351191010340c140c0064030354540c003900071001c060b6203201e496000780f030038400d5095602040028000d03851400f800c140c400c5440c4080e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735937616 1250 735936366 735936403
    0x12010306051006120b06091809071a1914070b100911090409170f130506040506031311041a0405090712230610090e0a0f0807050c061308 60
    0x14070455800c40004258004080c101243e0140040c010603c80d0003426583c0b500102d23002c2c49080c0c070940c188000d034803a009010455a1080d5141030080b50800e07200110744100c0410005400ca8501004004142c00e0303d038208210f01840a40303401d11194480c0c030041c1c800304d41c2c0d0802c0c0203607601085007130001030107010001d012501792001611300f40d1048030b0816100c0c6540d0f05020313003040458400408484812401a42c680c10b900101a203140d0100100c4492240c6180d03012440340b03400803da50075034901a2034a41035640b440c040140c5a4900c0000f03841070304654101c200b040c4d596018104410400301d0b50f041150404005120580714080e05604c0650007619080c0401b2182d060460290f40e0000701001642c02c00e05105800f489a181d041c03403190103502e04014080c880341031035204484c070490003001080c108450b039035100c20786104010714034540d0341207410100380500080c00459008006880b440d01d11400002d9080e40a1210400e654201078010010b110041c0264907060056800c01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735938866 1250 735937616 735937619
    0x360e060d020a0e06030a020a060f090b040f0501120b0312070219030b0c070c0306060e0403020f03090105090105090f090103060509010b03010e060403081902040f38090f0402120103060510 82
    0x1002d01980e4002d02c404034070000001582d076034040040950441d0003410407807141340c1340d0b031008020014240200c1c0104000600001e41c042c201c030700329411214075070a80590103007010700445951110041c205400e5845868041072a5414840710b400d200008462681e0b82c4040e20500140e26900300c035a4441136142503003000892880080554071200102030585d031840213241418006690380c101410b100e1400001003550044208118007950080d02124801040842259564880c1f86945800208203200e02d0751a540594081c1c480724200030172b882c82d450b07092008614440001d910655007203883d80c0a20101c1c58084c030490b030300048103800a01c4110350304001260341d9840903200034100048800042d91000c43d62a03007042c19050310318155540d5607518807c4490001c2d46c00360f2200c40c095010040c5007540c1c800e460361580040c2c00c0e100c10b80c012a14054004a40001e800d080e0440756000a407409591244000c06041d04003800c041d0017941141400811241700800c3c0c007910300740c00b510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735940116 1250 735938866 735938869
    0xa050c04210303050601111b0d14060f06120d0810081c03150308030411030705030604121e0206130302030c0703060608070603020f07060203041a04030c030215010b0a360e060d02 78
    0x220101100002c1c45ca5600500c23010001c140b000201e00380161030582164911000400049140c42c0140284020034120303856070002c216150694041c0842c9a41c081d2544c100890b00a12450350b11008000c80c1440c1640e5504156083c035107007460721810f00c40d11195541c5241c0c4c0511404d40d400790f0303c0b100c0029140c20f603942c5400d82e01c1f001d40003820442c10100c040b00c43e940d0400c518409458040e007643d00300d08183c50890110303590800818085614000480c0c0b40103e200e90210303455035107900511598540403810050101c0047d419411030000b08a00900100c041010f00010352003410001a00c80c030b0f128056082c19800c0c0c0025041500400402005000284c20b940d01c16030000c83c0180d50381c80c5d0b8a0448080b41c1300c0b980c00d43c6100010310402c000e058010341c111120318080d4003980d00801e810740740e9a441000234044c0a800800a00010000c5445114412030040403100b180348000441440307500c1e1700015405402040c2a0b84005000d0f40510013003245c0c21030426140d41104400035070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735941366 1250 735940116 735940123
    0x100f0c020d020c1518030a0c030b0f040f0b041505010f050a0905040803041401091e02040c0801080303010909230c01021501030b0c030c12070908010c090302090a050c0421030305060111 81
    0x2182130050040205608118210300508885510002401c960340c50400b45003151003e41d0078401614400c1c0d6203c002480c4911702e0150a1081d0b0707100c001400d403514541c1e2010300300040a4000d41c0d100d42100c0c0920b034011094468940a00700d418009101d01d0701d450200409442903822071040c06060a0500c0006a8a00c050342c1d0010381c0002c48600c003115100100d801010100c002070069140ca840741305121109002000c4040c0c020303035090240c1801c1810070781d04280e007841240a0740c2c2c400c0004103e0301800d5442176000c83e2040204800f0f4030314071070400c000e00f000d80420707000d190085d0340501034a46c4c04100c0d008912090b03044100d241c3d85141c6a44480f003c1c000d000c091001c0c070010005200c113000c5001c4407181100401c00e403202e23082494008001c00080d01445206602e02005000c1d00c0e40034081c000c00f225802464442a90307950034216002d05400b8004043c44003092001141d00054203210346a900c004080b030484000e41410700a040d0b0358060032284c1800f01120048a20340c0010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735942616 1250 735941366 735941389
    0x1d1c060209131506090f0b031b070f0b160f0305060d0b010b0307030e0d09180e011a04050105031506190e07020a030210060501121a040f090203060a0e030a030c02100f0c020d020c 78
    0x1541f00301d480c1c0d51450840300400103419440750800c54005012401c1058060000c1a441d00401c1807640a82d101a00c140030742e98605807240c0400e010100b94a02e140c460742040b68406070141c4a0070242c109a664800c00020a0300800c601240c08010030666680c544a04410130a20710018012000108405041c0302d800307015922104905400394900030060b90400341881d51080c008010000200d8641c0d00000500300f1b4580c866420540000b030a0316000641c0028440f080f21590140e48529082140c0181c031000440100c6050200001d00302003094103107445000d07907030044c201d010710310300d8000c2c2001000300d6440402c6260003410712031030741e20801c40c00f00c0500e440c000150720119600c030508a1141c5140035544241080380c911040c15a81d001011018420b80850313010f511a070900000340d0f03843c1380c120030840d0300502400803090f22940015a00c2a014015250071950700c14100c0182c90703407440c0340e00c8040c0d150003500400603410042c1d800b00078040d2002e8040e4610740b5001603140d0404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735943866 1250 735942616 735942629
    0xf09030503091219180b161704050a0504021b030a11010606020601030f030c03030f0c02010b1203030609040b0711010c090302100f080c1b0a11011d1c060209131506090f 74
    0x349540103850584501e1030300003401c6c4800b040c0f41c4950702c181c000d0102010100c81100c6454540019400000108050b2010340f40000c1602010b24104401c1c40001d40149042494000511880101c912001c4c0010560881c45a5500e680341c48d680d02e21909442c81944940210341c0700340010408945100c80e1000d0136603042c17801980751045424218054103010030301c1c0c2000d034502400c64000302c1e015885088280c0302611302ca00112580c07151207880380000c840c4c494110f40950000b40005440d43c1280368414a00d041c5654943c00d0f4580c1c003401c41702c820002c0000318410040900c15480c2c0928070048001c2940341121407198440710007001e9040c06001513003080030105a02c502c2140c46088000101d04007812180c104485003004901c0d030711100242e0f070104403030b0705010152050b880c0085d0156107000e0400c8100c12010b08210480340740c00030003619a141d00340005015540d4941d0407000c0702003240004079603074078903608005600310780764080300503c00b02080800c942d84201e10500100d410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735945116 1250 735943866 735943877
    0xc13030206090424051009080703030c020102030c0a1b09021e1608030a0c17151026060406060215041e020d03022d0c0d03030f09030503091219 63
    0x8a24001c10083d0021300103803c40300f90300300c1c11041a400b060303004504445049a200041c286106019108808035003d0844c40d50048003092000c280111452504c0c1031040c4116850f00780442c007024100200d148044506030301074403900301c855502c001c60001a01402e20304514003800040b9103558803176006426108030402040c40b4210a65000b02c00341c107507030002c0c00c4994914120760820000c065440240d40801c520041c84030241426860613403188000c1760f00d451089007207800704907807644d141c084042081004204807042c40b0180c440c0001011503000e010075141800d0302048280e070301d5034109a045500c00d80c5905533901d00d410500d50801d4000444035904d44050b1010701c0101c2040b08080e412003a4240c020381010741c00031795080d50510380090808880c01902010b1400da0400310b032102c2591210012810618bc6040e80040480c42401c002502c2c0602c504800c064030001c11007540803800200810035824400d100704110804894030340ca00d001e2400410307400110a00354034004008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735946366 1250 735945116 735945127
    0x1030e0a0318180906060f0302060f13050a030818030c011706060c010509070603150e0a0b010e03010612020406290c030d1404150501063504030503040b0c13030206 72
    0x5209904103001c0c10750b20344030394455043e0b04035110141501d041c1c1200c1131403801800095611103d0b10203401d5990003004207151000c1c810318580c140d08aa1191000c2c4030286034002419503031419188000c61040b01ca0301d4132250940c194080008a91400074080e410440794030300141c4e030041e40d22580f60080841c1050503201e890200307a5501618690221641c42e1000b0b000c82c244d8000340792800c440069070248403804107100101d4000b080c030300c2002604a80e01000c941007d51907005940d03440170625000e8580e25881c03001a00396100c0c1e80c019803100c01c40f8044401035007458040c400c0600700d0894050501700304d010b18071003d843d404d141400080b80115010a245e00c06004842030b010440c0418400600e02c1d800c0d0001c0c18070705403412221882802c0c003503842044a07000d00c42c100c600d142c541c00490b01c882a4080b241ea01c0c59101d03c0c5843c1c9480c0c04071000f0811440c060340c0901e000c0d46d5260b4480c5024a0054031400000e402c4402844042c44040e0346003400710f071501c0c107480d4103903005526103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735947616 1250 735946366 735946397
    0x206061306030210050712020f030d0506041e050106090b090310021e210a050609010303080702031209030307030608120d0c03020d0219030507030c08130203160e06010e01030e0a03 79
    0x1401d00c0e0304001c0d8000110781810800b42d512101820107940210740821101e149054181d80e501d11080104510390010b2240c00781c5004660b000301d07071005000e400829404480f09002e1412203074012a076140f20b81c2c407030051058540c000d0341d060281048161040c5032509000000b69a07000034a03040710181e80000e404c440d640503034244000f216040b0075400c1c0c0c881c102c0c00906240301c07003003056503080c000090f00014054103035070099078000c000c080d15920b80360b400c6440446101030300809c540103500c000c0203580981c040c4801041d2049520f14061900c0342410000201501d1240d031180b20603902c800140c1c54044417407001c1300d024480d20940011060000101580079004103980303816458808140203a04408072414800315800d1585c04011958400409800f11080c200f03600000903100f00000701c8881c14000e0350304400e03000404a036402c541c51000104894000e42210499020001c1803010650300681c10f44854002400c0c10712040d074802820590340c0b041900050200302e02e80c600c02c90701c0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735948866 1250 735947616 735947621
    0x11802131206110a05091009120506010e0601020705030304060318021c0506060a0803071401110307020f100c0e01050319020f090f0303130b0a031803090302040e06010602060613 78
    0x3044200446a8140c1c1c0c1c0542103914500010266111801c1c03070040780c1c1d00c02410b4111258228683c944e242003908101c1840f001c55801556441440242e6001003041c1c00f6403070440d51154070940c0103129a604104410130710f21000344c012410755109501c03d10003941c0c04001d450079a4290320b40080d640c0400d0130300803403141102401039080340300c40c030610113060201300200c0c0a0718010300c00c0701d0440d2600b500784071060506120f043c2242d002031002e44001400407590102d14440c480003c1004410b03218204010350003500c2c0c80015a110b116045845142800015404450110108040816440064100306407810740a04200e070010019006070f11918000040c00303e0301d0401c40d11510a480001c586030b00401046100c1d0608013840822440c0010803611200140303101000c640e03142c15295000360308030004803428141c07988031098440c0782240454400d58041d075a62241c01c1e01d180148011540d1800414089030410340c014041d441c1c0000301a0380000b425a800c840320360007655007200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735950116 1250 735948866 735948877
    0x60515030f180c0a0f140f0312090a09021603081302030c090c0c010516093f050607080f1f05090a0e01020c0102030105010e0319082a010f0e0a030206011802 69
    0x2401303411100e012810418290441e402d0380c0c1b2004a0b409440420400c100d08992030000c00d582c198170643e00100b0415802c000392410000141c00c03100d4a0351038000420a82e0002500402629000c00c0c1c00c0e002c0c140c0c011000d81c1c011192880041c0c1c0049613801180e22031101c810340301d024070400303004642d001598008035017280c001d100003040542041c3c0f002900c0003411038540c01c0014020308000c0795100301c403500c4c405045e03110f8945018100410094800b81c4180080e50301400a60700c454001058007440038502c24072444e540d0913500e161070004c41442e01b0010f40032540c40c2800c4494400c001e000c00d22850195001142c07903500c2c80d69420a10006045c54100c0c21015500110b030108180805401440c140e6100740c944015200340c00d801e041d9550002c280f04a00003641c00c032290040398a0800829416803410a40150340e0f8101c11340d07810140a08403030540c160343d901c40480107981c547c4500b07040406044058000e400d0184c8000350b0733581040c001d00e1069503444462810b00348081c0c2c1100d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735951366 1250 735950116 735950119
    0x15090306201306020f032107020a0f0506040507090506060904091b030524040506180a020a06051206030606030c12011b0917010506060d02130504020d060515030f180c 73
    0xe40e1240301c2422000d03421180d1240c00013610614403401c40c451404020745d94014007080c89401c09580d45401808590030240c070900640c002d03080004041101d030000c9034019801600201002e041c10b2600c5460f14025034400d100d194034050034000d5940e50703803046038803280d0100e401007038480301818410710650001d03041068200b0307080000001c00c203011032090a00340140314032000149100b07034525140c00f002c5400078001d030031040004400c801c51000c2c20040b0306808040b250900341c0c0c2e078045220800d03542c020340085000803d88403030303000300070209a61040c1c058025000c58188070340802d40d20706a0010303a51040c409000c11001010b800d500004102c807080e807070007105100000020b06200071314003038003040e48a1051001c0440b04140545801208054002450044c1d0707202258029013082503444109510080c000407655201d0000e410040c000b181d00052861400300dc01003540c0342c01201902401061041004085440400d550310001c0400d58400d14240608000e050a00089905 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735952616 1250 735951366 735951431
    0x51b1501080c1804080a080c0d0f050a0e1506010e01180e07020d091a07050102071a16180605130f06121a030c060c120417060115090306 60
    0x20140c000144886040d2070690f01412401c801c80b142e4420041c00b220050400042001801c44052140c5081680701101640440c2003000d0040032506035410795500f0f49065407542d01f80304000d40180721700083c003000340009010b0011505d803c0800da1000409150501c00306d44174519241c0d01a0400b40012042e40c0c2c10400c00c25100c40d200001950195904401441200301d1440d0041c0100b40c036800361070810405100071801e42400110a5200315000c80d80c0b55000d0141c0000103403680d00603d2103034854201c12005192a2401c16200070201030850200002c0c159802e042c4c1c1d80c003400500aa038958a8541c1c0d89910309a00f0b940c202c0c4490303000100a5a001000103070065000b00e14181d803400c2d4140c02e000128400010354441000608455030540011020403040d00d003040090403480e001c44103550002d4051060440320b82c000c0d600503140f41e20321001504040310244a5140500079070500e140315680c035180020b040254501000704010b581e81d8000344009100401d080304544502440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735953866 1250 735952616 735952619
    0x606090905070b040b030c090418120206131a040804030b012702071a041b030507240c060e01090f06020702150a0c030c021f020d081303051b1501 64
    0x9009011586060301d00340610300020600818100440b42255842d0300100d046032143c100001240c0e01c084006907000755544200e0842050900041a40c6400b4a82c100c2c41c42c4500e001c041c0c1001d0b0001c0000d409048a40107120000d400091102c1c4084a170a06c00011551280b91030300062044d40c002518a40c408000050b2081d140200d02c041c0b048903003103032102034283e02c50300c00c140e000e20040240002c54000800d10855600390b01c465006000d40c203050030b030940c40c07201003922892680098a5a4005e240280203052031032084001800d590100781801c3d400c0032030000d04420240354000d214540b12251249990000d410520030290482d1b910507030f0260610b0804002d50282804902800d4120450b0b920070300317524141c80812400352907145242c9603030354049070401110b01c02264841c00c01c0111540788400800c0922903119183c0040c0b58a060300d48024003501c4004100c08000500d207002d8100083e8408241c03107c0d21494904140d009040030041424411444420380c0c02d404031400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735955116 1250 735953866 735953879
    0x803030c130617042603070509030f07031e17040b0a3207020d050303010b1213030909021804052d010b0301050d0213051501030501050d050d12090606 66
    0x1000c0845010011261003681d9002c25220040e00140c000381252511000501040882c22001280708203401121061136055540101c1d541085d00c400e000030b0307004510103116040c00c101c2c801840314850010702456246959900000107041000d00f08400208080020440283c256070480c2e007255514540f210346402d001611034200641c0c80001075410883c0c003000b940302c3c0000f183ca03d101d000c852000c06510742e0030507089501c040f80407030308464011041000b00c0c0040c0040e50180c8408142d2070380d10210805c0340350007088064108465055250004070000e9001a0008102c419650740962101f010356861071306000209202504542810108058248240000040c1107402250075a02020b03200c00903400c50800d000e41c644e51042040141305601e1300c00c6a6580c464070080c0a20380c2c656641d003034001130707070025941101c1c400d00c60404802c4940e058054a13001d0b00003969000040300705a2a40c940e10380c40110b50310103200e048907038019030040300d400c1072402c250010000d0106903510300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735956366 1250 735955116 735955141
    0xd03020f010c1805090412031a15030f0c0307020a1e14100c0906020304031407080a0b0910050609150102011d1501060507020d121709340e10080303 65
    0x603c000700c030100c4408103441c071704012a1400350386c107c8060309003001810015402440100c920302d40c5440303003150f076801550303030b03041440070100132420215102e04060060a1030108041c140c612640c0d000d00411100e01c0d400a42400c0742a04041800b9540721098144281001d5150014041c2d20640280711003403400000d48030131803401c802040150700610842210894024020440180c008000400210301070b040c400013000c42c048247d44e1003580c0d818465150811885085444003510401c2009082e402e00030995521030300e61040c400c524261002a600382d400034491038400010204000103a4030035800b003841e03964420341115424880c0c59140c0d603200d08824080d4100e4411000124580c1e01c03410030703941015405045681300008941d5424980c95510311044104403400c950882c03000c4c0c0c40c0c00c099000c1d00d1040701510811542100c330541c002d845804412142002a131341e1031300c80c1003c86195086401e01410000182c0315107282420741d620580c00740382d0602c0302000340403204103401d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735957616 1250 735956366 735956387
    0x100b130b220c02100605180c040e09101b050a050304060b10030b030601080d09180b060403030f0806042c03160506060a060903030206071b1b08010b0f0f0d03020f010c 73
    0x5030220344580c410750813102d080d50520701030a904810b1048440300c14480386000c0f640c01c1000a2803803820943c48160403044414200c41050a03548400030700305081d040c40c4120340d40c50085130725582c1c8003456060003038a280700388054402007110000c005424000164088210b0410080440c1c24005002d20300a02502031040302070311a02501000003400c2000061185035845c5036211191003600c0c0c0740c4004414414405040fa1041c0c4078414004a5510b500c0140f02442c429100c03180803d8000c00c0040c41c04400030a10740c01545480c0e00c50540042c401d521600b10b010780a50342c82c0d4921080c011a0550103070704410042014001141c20801c000800c201c1c2c0300c0c1d030003943c80c00c49480e95200300b21055855840090b015070489004120114416144560704145441180070f5041c1650354423148000f01d40e4200580d24009071041c03005060038043c00310340e4401120f400308850319400029a10124806000d8401c3e640c1a00c01010076009001c003030040642c00c1c0c000c0014014401000d403003503000e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735958866 1250 735957616 735957641
    0x30b07031103060a05220908031608090606150d06030f060b09070f180e090d0e03010b0310020705120f04030303060e04031209240e100b130b22 63
    0xd0000c454100c050801c26a489940001e00213180140b800301803112401c0c21400420000001e090400c501c0a4035000304004070340b080d07180079620318100f00707030a08070403511030013208204003801801018400007c0301070300141c013202c040c500b44a14804c00c240503c14004031a0b071160415400100313102c100c41e04005454000d00d014000000d60400b00050071f0022503218020440d40c808032030025100701c03858548040b2000013644842d441d92178181c60048212035041031341d4404224a02d445a01038000498114282c000b80183d00c0c0380c0c0b000940f24000012191083c6501007a001c050040400041c2c54000f0307a54000b139503a608443c00240300d580320b40403d9000c2410204000345214001400a110f103405a440031802c0020125900160035039100940307260069001c800805050440020207000c0e100e000002c0341414540850b003400740340c00169070090306d8514181810744404190092260301d41400040e070f4074412000039200c44c207808800c00c02c18110f0030b4402d540314065204141b4080b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735960116 1250 735958866 735958871
    0x2003040203011b0c0b060409020a080c0f01090b0703050f04170f06060603010608010e0a141021030212030a020409020f09011d060a03091e030309020a0605070b160513030b0703 77
    0x8444880701e0080185281e010001040c4c0060100818407861580d03400001c014000300d115401c8d600080d0360348081d900414521740241900c51118070708400e001c01d080c40f082c03c20580c0c1910301011036103a8003a14002030140680000c02a400c040d1a4007214003405481c152000c54007580d00400b0342d00c5c490104d80d11200d201e200701281041c50148140c0b812141c00f43e4503140369030300b050030a00e0134810180500c0d210135141c54003e1443d0f55416884d0f0310a00007500c0c0d0010040c54001c07020280b05a66104c0d41140900707403200320200b540458510810890600803550740e0316060402c0000b4410b1b6400b1900180c030102d1a02c240c1c941d1036000f8840000c003603842d40b185104d6803600e1008000605d00780c2c0e601510803c0348a4040b4029080141d545010350040024018400003080000b10396106c11400203545010074000c500c0d114203004054841460614101400f49e40d4144800401500030041140d0b102c00c600035042c465401c0707519440250ba460321140c1c0d0b89190110b035450041d42c0d004042030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735961366 1250 735960116 735960131
    0x1635090a15110403030c050114040b06032a040504022101020403151514040b0d050c15070308040627060f060506090d080706020906160204051e19200304020301 70
    0x4074081c200d4040a407024a0f498286941d4040d02c03210718642d81201d4654841104100070035910810610035406008080d4551420b4030405041031403030003410014208072003000700000715040c61803c0003002942c000030f0076103840c000035011402c10300c07110074400030120708102d4203c03041d005007080760300c1400c0e641d640c0303030142c40c80d4004e5403810102e1036101c10f02031b242003000c0c0300020000710001b4006400015000c24810101d242c0c040c01c0074090741c096020301c10b8880b060401215800074620100e00719402d00c425540c0040c028000600042c1c0340740c2e02c843c060740360942040e0a50440c036800306525408414030b85410409070502804845240e46060000207850030818203c410f015001003010405020550783c2c039040e80c000000c15141c46a0900921020741c03a039800400040418440c0d03001800c4075441040152900142020914406c030a2070780700c058034000c40241c000000074a070a440c0350145040c48020200603400d0343c60000300c416000606071400d40254004c9000360001d1001d071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735962616 1250 735961366 735961403
    0x40f0306020d1d0c1e06040314061302310c080a0b0906131d030403030903050c06120c3106080a0c02060c03100e04060b091635090a 58
    0x840160210303c03060300090500b04042c41d040c2541d420241174071408480d646032880100d501904507801c2183c030300101800a4896120421120350702c40c2000f003003003041c0d203115404100d41c003800d401c12005c201699504c841c0c0303000c041c92040b21109940d04040200303a042010042c580d54060351201d044034908a4160a142850319115219410180000251002c42400c40303000700360000c10103000071044003003441c0b40403040c002080198026600d42c8807841c00d41c108981002c4403c440da0344101f02c20420102d030003440041e840d078810f1200728070580700c480000b488006884841500788072540307449052107402003072542001c03c0d03c1a039039820714550341301c0c8903541c1202d005850b43c1025030f003c0800a0800b000c1e20340210360004100d0f0601403c1d81d561170384485c401c00c042d1411613403503454021402c46420040c500b5a841003c40c0400050042000000340011140c4103403482100b00154003581c0c90f0614110750010010440b15001540c5001507086480b101480000c4440b03030205c10200485 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735963866 1250 735962616 735962651
    0xc07170c0a08073e01140d09051219050304030210141506030c0702090405100501030818010e090601030203060d0b0408040e060a030c1806090507080105030705010c11040908040f0306020d 82
    0x1e1a030240d10742c0f40d1482010b4144c5950758000c0006041061583e42c030034420a040003d00b80351218004081a40b1040b840e001c2e041c5140d02c480c161686100303105c411001041c0d05801c082e0602541040c950340d4580341000c9080c0704145054005460038503070100700d41620281000c0c41012900900c4034a000e41d20200135aa10003503c01174040781c014402032016292600045800900c6241101c24841008005000307491090f0b08c295650340002c100704142a4078000d4a5041ca030092810407980d07a103a0001440017000a0700142c10154040002038040d182d0b21041c0d44042c0d00402800d00503d480e1402c3c0400303501c10701904103248040d00c040340142c01d0024140040c1ca81c0310314000c440301c0c10002900c00041d04e030b002a1520300d8a49100260460342849000e000300803e43d01c508075981441c0c01e042c6000703403e40c085410041c1e0201040c01140820a40e240303409412a0045a2004a410840c0b00c50107190414801e84850b00000400c001c403a6004045440d40f9200c24000002040000d194 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735965116 1250 735963866 735963923
    0x17070c060e1008060f030f100f060e0c0a0e0102100f0b0a0504020408030720060a0e0102060906010807060c0602041d04060515010c021002071a0a030f050c07170c0a0807 74
    0x1051129012900c0ca103041559042417003405400c4800c88640c60072030500d00101c481444206607a00c1014640b0005a4003840c8080d0107201e118681d582030144084110344a0f04440004019140703140f001e507030703109011a809940030f0b4070701800310480038420f440007001e10300f20103072083c803000c940000c05042c41d000351400c8901c810301650403e002034880d155009010003161103c6402e44144010581d101d1019200e00b03e003070354900d0b9100072003e001a00c1d1000240c110041640200c00400080100140c810292095464100c0c0c81200c14a803003000390050341c128030b00c1e0029414802c0218400580010711031800b0f100107004503200c445014400340022650b09000401c50002140035050021034040034202600c1240c0c0110f50301c0c141400b0840b416003091325860000039079080b00365814061540c40340b40e400d8040217642041d0740c41508030311411400510702c54207035010050039868070068445c2d034001c8000b5554222001d00d0458040c3c1d11581e01104d07000ce001d5024400180c0500c00c40c0e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735966366 1250 735965116 735965149
    0x5160b011e0f0b0a050a180902040905130206090114121807060c0c2106050103030809011104050f19090527010e06010e0a060518070905031b0d17070c060e 68
    0x213140c800281c0c0300b01e405a10580a80c814018000c140b41000d0082d4200c0d080186180300c00161500d0908044006a40000d407550400f40c501c00519005a0348640484001c0542401c203c1411304090411510b58010080c55070700d501115010051480b0801045148088000d02626482038a0300c00946212071241d0000e000c440f180c00f0f00f400030100582d04125441320407103406e400191155070b60000e0325401d8100b100052840c409024003490240034051505815280050902e0700740400700d0481580014203a209481d042c0707000c801c080103041c0e030a002e0310340c200d41031006140c130340880d02c08081800c50b14404924220010000c2d418107202c0c0305444800f0f5400f800d000d910344641220f0303201c1c001d0281401540d4510001a0b00c0e501d10200d03121401e02c1d00c8005003a4075111130080c00728a00c0f68000e50082e000000d0111000880884640807080120f8070030340d0300b0060b420809003c060002c05090862400038030a024030804040b07060894607a035480355603803800c2c0c509010945000c8410607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735967616 1250 735966366 735966389
    0x120f09021f030e0f1f0e010207030201061401090515180a0f180c080a0c360b03070813152d0209010507060e12070b0916050f0105160b011e0f 62
    0x5800001c0d15400110021800d174000300743c40d003060603403d003240e10151045000d40c1d0348490402c00743d000030024084140003406e100028a03e4a0081040084510412501e5100000300d150b00410500c0c401401800e02400304442680c5440d480d040d09030301c074021450043c0102400c413510381040c1c01350701c10185041c0e58151184c0c8032032090300007420200d41c4e00c6041c0242c41c903070f401403148803003400c25110485050443c0740d00004074200c01e5840490304002c41141041041100041d045284035401a003c10030302642e40e1071f01c0c24480300034103c12003000312550421049a0104c0607201d01c038184400240d1080340420800c1000804a01c65410f1240c01b060050080d4808030340d95511540300d00340c820081d10580f01071070441c01aa40c0c04840200c9105103004244006950100305914a138036445855001540c240400203003964508041e01c1e04100000408000030114041c1d035034516a8412880c144c0d43d40c4880102007150002e121100307090450a4002990540b00c00702c6404480c2024101c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735968866 1250 735967616 735967633
    0xc0607120806010e13020d0f11030c0a03090506070309060c18050d06090b070206011508011206020d0f0f021b1204030b071103030106020a020f030d120f09021f030e0f 73
    0x1500c281e44001c02c028180090300022411a8803000c040c41550660454011380c0c0d0b403545032110b41110705008241441603c0c18815805031004401102c0d04035810350402c1340c8481c1c9500c000c50107000000c0e0000d0503400342c034042c072401d1905500000f400610030b1405100c20084200c2c12a8600e43d5100c5140c2d034510042002c0001e414601086003c01d07000324404910032a0945071410580c006980400050b17011100404c241030380314410f100f158009103800c03800c952500ca12504121001d043c05460141d0014608040402c036a1000c440c500c104c038401d004880d0b40000c003c0094102089440b04c1c0c95001c4030070000306001041c4000394001901c0d240b428a82903403582c03000030400914140c1888100800b0075078981e0100081c2d0b0082032541e00030503031070700300e0f1042c00f528050034114580a94084081d10704501c0e0860011414111642000155403100e5a0020302030300006101940103505401c0701441d0149000c0c49a0a800d034540f0240403d00f444c841c5642e461074114802a00358200c902c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735970116 1250 735968866 735968903
    0x62706030209060d1401060801051009090b0a1503060e0a0c05040e040203010902090f07021204050f120709240f06080a050406060e0c1305090c0912011103040c03050c0607 75
    0x34018158002d05a036040c0342120702008212003109440034640107945c80100000c9a1004406000d800243d9414911003070144000d0140c444c0d43c003034820090703140c030000c1c4426114162308000034252200001c4c000e06140300068001e000d180100e2007424920301c0003842c08400e501800f110032800340e40b4607207064070300003a0b1010444058003c076815501d41c200c1101690315081280e0040b0107441e0701e03034003509144001a1500240c410246080d88040c40100070660701c4505107290780c030381035a114081c40c034150020380c100002500000c1d030492820030303c10800c1004007903c2080364144000e0201840d02c030f40401180e00c5c480d11440d40099018800606844003070307003103590881d101d03a00119400751186c240c0210311004035504116040041050407035480790220701c00007030000392040b9406050080c00b85400748204140680038004189548008440c00d60060b03040b04103441480e5100d003064070b8480840c1c401440142c84900c41c1c4406611545405011203036642d5000f080d0f003014048048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735971223 1107 735970116 735970121
    0x70f08032d1303200d0c06140103020d2409080a0314010513150515090307061b0f030e032b050702030d11030f040e0106270603 56
    0x1051200b0780b440009440500d42c0c040c42c02c1c0180d000b58042e1408140c1600e81e80010700d102d0348100c0d03a00590300070701407088240314078401e22070b600340801e084105a00038040070750311240a0340c22400040c2404582030402c0f4001c0500b108860900711004112a035070b200c181d9500c07100103280d040d190351601c180b20305611040882c0c00c03594108004964000b08212100702c000da980d40b4486812070b800d00e5500c00402c0028694140364000c00c5510b10030360080b400b950702038071038010041a0030b4043c2c1c40c100c0d080c1001c04061408038050f81c50b03802000d01810030960610540700246045500c0c01d000d601c1d5a5004004001c0020078010040411015001c85403000c200341840030328016070380031031000c001d20b0309032410f5006c0c40700d82300d03000341588600d11114146180c001800542c40034084c820720f04079201501c858111710b04d490302c02140840da104456404e4840c442e0180314450103035 = true := by decide +kernel

theorem cover : BRFrame.Cov 735791366 735971223 := by
  have h0 := BRFrame.cov_init 735791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735791366 ≤ n) (h2 : n < 735971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
