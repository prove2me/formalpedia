-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0943
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:19:00.925763+00:00
-- url     : https://prove2.me/submissions/8517de30-66c6-4f0a-9e37-a0068cb66eee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169424460 ≤ n < 169604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169425710 1250 169424460 169424503
    0x30516020f0a0806090f0105060603070e18090c010f110c04020d06150f020f0c0a0b070c18020408100b0130020403060c03051509062205090c010f050304021f0c05 71
    0xe1042d414104606e04110407a4107000402c03583e966907500b144c2e407141c1d031402c01c1d0310001c4010300829114159a154204200c11240501070100c0001900800c0820240da4102c2c24141a400844a90030050b9180307283d40c1c00400c00076243d03e800c0d00036041600d207460700014026503540700d85180e03420003c0141c1c04641040c0c440305d031042c0d040c00419205c40300d00e8020188084001c010407803603070040c40703151404d200c04a03616040140ba004500000e00740300715500814074000421100075442032140850521400c8e0030251902c0300c0e401707a010784542c140c446104241540760441515001c0e03540a06608042000522221a542c07025001a50003030074002005414040d0103002c640c405031220110390540740920140da61000d4a540e40000281c4880d069205101004500c00461848940c0d50508200405c8407070100094031155584090386c410302e140342140019500b5101c15079010f90401c0c64150710790720410040310403c412107060304e000c45c4565916210035040c282c20003021960850b041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169426960 1250 169425710 169425721
    0x90e011e090c1413020a0201150e01050a09051512070b0a030c110102131403032b0c0908121804050414120906030406150803070303050901050c07030516020f0a0806 72
    0x306490b070240c1800400c01c180c40c40030308009094100c0c480e81a0300341035000113035007a44078402e4201d1100707a40210f5851950702d8a4011040300d100c0309000710350103000440c80001e41e5283e41c2c0246c50081d54401d403500001c95a9200780106072080109170606442200340c0001c426101d0401481e0900e40c6640c00641ba02c17030800001c1c520a04410050320580c0140240341480010300c00420803a6102d03500c20200c3d41c091000b081c1140560603280c04403018040400600c00324140c00101d10582c400020003150310303805d00c2950101d01030300400050781c1c801101400d80e000c0e80c80042c10940200c100e072815800c0007400180a94508640445116001507600c44059104100740107500040341c0e4200d00741141080800c0040c08014070140000c0d07290707039180c0e60b03000c41c00090001415104040e6607441d081820050003915060b2a221120f62030003000840101d076000964a20943c141d443c20300d0032600c0c0c010f5030282e2030884000da0b8884072181c2109000c0e40e60340c103018010030003031020b005030740f505 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169428210 1250 169426960 169426973
    0x3180f180c090405070c030806040f06120c091b02150a0f06060507060c1103090603060f03030403050d11070e01090f060b0c010c031823070306021206040e0c0901090e011e09 76
    0x217004c0c802403280c1030840000094010b01c000703910010135107002070381d51180f424007400f503d420b80c0400d00801d030f9031100b14203204144ca003a0b01501c145200a20011000391400004d1820261a03200142c124460103414074060030700c801c0e04020420000300e9140d440c3c0e5101c100b01c64461340024003003480000c035802000502c1c06003401001c2d13181401c068400000381041d44903c108203503203100c0e103c004000307482c903a0354101c01c5900c0c403800f0703044a44454503850715658801142c41d91101040a90100364591580000c440b0b0a5441909c6181226464440c0c0705002d0504107005150250710b038500803a6102d02c190281030189040b00011807901d0b40710001a045805102001c1c600104407854103005c00e00d050301d00144214094203604280c031000300985e080504903080100114000104100c06019469840d03020b0710040b1000c004a6080e102c00315902d4204d09440c540104001004000700807141c0d01010400840030004102640300c40034542650407100344c1020341c40d07030317686d04541406003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169429460 1250 169428210 169428221
    0x8040314190f030606090b0f190e150f04030201050309010f0509030301050118350703081908091c030b0a1206050705030103050307022b050706020f03180f180c0904 72
    0xb541d007000c0042e0342c18010700a05452841c002d007a00504001041d10007003519404960700d141244101011010310344400404159211110724032407a00e4807034884200f20400111041d11840d05590352910303103140c2c01981e42d6000101000030302d569480f003c0c9080300741c6000e5188942260000b071a9a503040100150201c0c9074080d8204041d51403810521000700b540b20007494040341e00529040300c0384004856810104608010016400f5140c400010070050402800e80f0000c9814802802c0a0080341291980012207490b085075116001441c0d0084603003400501d0340c02c0380c0c60301145102d69400451024403007580702d02418609200701e80c041c0440b51107800d407ca000c034038026203103500d0b40d00d405503a4014400080d00c500c030004d40c0070303c40c1c40700ca43c03440605d24001c040900804da15070402d1601c1d540c2034460703013000d4020545082c14000000c0708440280300130740310200d1030788159400c4c040c1001a8141054018881c0003a020030041d8100089110f80124104d003a990001030080c001a41c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169430710 1250 169429460 169429487
    0x3040f02030115050901030b040807080a020705030c040b09150316120209010815010303032a050d14060109090f0212040b0406060b070c14040b040e0c1504050604060804031419 77
    0x43c150602401a40d0b84c400300103044907000115010161500e05028601d8462440300400f207200c0024a80603e94012a00b43c013120400c6003555108032000c0e05000546400060701c1da44070710b41a000a500b14144003003c40504409012541c0f118a00c06181c68401004d030003d44000c141500907804514042c0b44036405845500050408000c0c41c80131040016810b010090900d900c0c0c9605c5041c0f46501000d0740301c030365542c0d18040c40703441c8030060207032440d0302c04204150a94100a403031700346030620f41a5540603100c180d454180e15840c04104400510050140084890b02001078500041d540401c59002d903004141e191290b0516140c004120b441a40c82805441c1050203940c010a06d45440c82040711800d8039062440f04da8100041e0003000600d01880d4418501007540300003000000d03189000e00c01c2a19003410b200c19480d41c0d4800390003031384030303040d80301c1010002070140360b2080d03a030203401034401d080030642800000c114501a400071248541c80d0780000604109990740b0100d440c0078403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169431960 1250 169430710 169430741
    0x1020d1506020705060c151503060901060f1a0903030a110f06070509061b0a0506010609050909030711010504030f12090e190b12100f05010510050d1d010203040f020301 74
    0x901e80341000e510b805952103114410072010410591543d01407103481b4104e03414a008102a01d40080c144546c2060752440234000d100300030001d22220030511591003503507000c9e0301c020f100c14a131001d6a251040500d6001501c00e1040c070841645850402c00b410544559866056001900d05065850a003401c2d200126a5200385d00340000d080e0020221101001e040d18019503d003555082805400200c0c049021288140c158203420f000d2b0128100b07040e01d102c3c3c1e4038044104d81e25000c10402c4c1c00265614007564000700071583c0007400c01c00c03c1c40105c0206060190400d03507a44c40341c0d041c0000c038010035104105150b90352024950b00030340a0001d0604100d00320500c0c1428901076241c1d8100010001e000ba582e980d86001e256030b0041d016554278040350440d101807102c2c041d4140a05455882d080781c41e802c000001c241860000070485110740e407955480e041000a1208101a0003a8010304580c10450700b10a240d06500f030000f18860381c00f4090601034504e85105043c00c69980707014001e500e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169433210 1250 169431960 169432001
    0x4140a0c1103070c050f0d02060c0105040201080a06030b0a02130f090b0301050a0908090405060609100215070e090705030a0612030c0c170706030b03010e19110d0b0a09050a021201020d 81
    0x201c200c82d50606076441039601c10340721b40840300482c21204428030003130340c000307008202d80c10b01c1001508800e20961003aa03401c031007911101c15041c00c0d10701c9400000e01c1000c0040018101541c0381d405462801302d2042161120b41d5a581e01c00010003da40148400b02c3d2104080007050609001d4183c00500703640d01004130300c031140c88148840c0100000b06220726100d001252040d0307a040c0c2601d9080d03100a00c620941031038640044e68030345800400c0f400e82041840004c041a010302200090501c0140c4640440c0c0c2e5194404c0b102680010405074a9551707a6901090030a100e1a005890a101e0f84404c001120139003082c01400d4032039407200800701800c60507000303210808500102110454103003c20009403000c00a4003410800700744800620684200502d030000410205113a40d028107035000c0381048034424401c000e070100001400100107032000c00e100d1400c60f4842e0420501810a0b601c4914260f800140e4500399020310280d540e40209000303e01416501c5440801c00050900717414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169434460 1250 169433210 169433213
    0x6070203040e0a09020102150c070605010b0906162a03050115050102071205120c0706080c070c1401110109080301090f0b030a0206130e090303221106030604140a0c110307 75
    0x80c03807030050581c0105a04c079440b0390116402004021100b1101e6074881c2640d1500310803500d101d40000d001940c00c1b9041c00000030380d10a5080c00c03124404000340c02e0a04d064132404c419460404c0c0e44200310344901240f00058100c01005000e05503500d400004059210310b10704201e4217442101c06200c1d62001c070b0f40000c1200ba038000807204125000d5241400070b040c0c20303085c12818600c10501000581100017100c254000021481506a40319916a2405070311340c2803030388000d030142c10700080150703103803210a00031000e070fa81c1c0e40c0850140500d001004000100041401d56600e40402c4460130400300050101007443d00945560a020801c10401c1c83c00301d200190703030340410090103406038400107808a01454412011000b030310304a01b45800a05009110b0782d0790f03a0044131600c0c80c1d240725001820040c1420105005091781002c818840111010100305a0f0b80c409000c00b40e00641d946201c02e800410700110307500c21984100300095113607008401416058002d94100082d4208001010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169435710 1250 169434460 169434479
    0x3060212161e020f0616080c210a0f0f051503030a02070306050a0204050604150f1d090a180c050a060305091b01050f030103080a090504060b04050f04060f080303090607020304 77
    0x109800c802e40c0c0c004410804007100380c0c24442d049113800f2180c007501080100702c20421512044c0c20030142e44850099441e040040014024580303815842d6920340050030301d0701c06008030560044088a40020200c4189000e4000c64118ac25421040c646450410071040b2400802d500c542d0070540203140307004983e9400a445900034007008011642d1013001c0340c404070480d03040d500644400380c8969541e545542141e020f41c0c0888a200d40020307101d0041c0407480e445030904e0840c8001000f214105c070a40c00301044040c8000a107514201d03a95007810407602891001100d0986005001c080c44241c20181400001e80607a041030b028035041c02d0500000c920002003c0c403000314081003100700391945000403a030a10842c01c1052806078088000310520a070413004101c00e5040380c99402c40183e0f644107001c2920038a100d0300c0c2c80c102d030a1004100034200b043c41d5540c07102000300300040080d250608140c41020fa90400d030001d40c400700c00c0081030705041040305d4009a81d0700065040525003075248 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169436960 1250 169435710 169435727
    0x1080910050a140c0d0608070302010c02040c020a02040f06030209010e0c04030b070203090915040c110c04090f060c05040303022404110102150c09010f11121605070306021216 77
    0x480030340d0365000052800340d41c9610010750854a41a658018140581c990340190440500101000d1400c1c10006401c0d40006a40e0b0850340c3c1a11143c1e82d8403100d8007000010801c0304d5818056008062994005030754610a179111040c40207400500d00f07081d070050140462058101d00f400603102e4050002001c1203105513411a540121018403541e82e11400728294060800b515410107000d0003400204900729000b608030320030a94007044a1140310320104c5104168207042441504001c10780740704d030705250300104500d034000c9480f031408007090395420702110655405140068030108060042503414007060700318140c2c02130b00f03100c00484c81018281141010300001c05149641c074200750a80d000b4003030755038070440511b244079041c50b0040c0e4030f02407940010943c0b80002d04920902034818021700070241c05030391160051403140000f50303250343c040e4400060300d07581034100210705000071010440d1501842c410344001d6142c1d02c98400e1104142000750234030b842196801c1d000341c2c8260f88100c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169438210 1250 169436960 169436983
    0x3020603011a0417011d16090e0c060c0706200d1b0203010207050a120203040605120a1503052a03100c03180b04050609030310030314090a030b15010809 67
    0x110b0800300485100800d072040c0c0c1e0011507001e103081942105034406601550070011803c0502c0d181d143c401c43d005444048000b00010a004195010310010b00c032944a111010403101c2120b60080303c8d0700004d00c2c00c0d0021080301c00c444e88404010f100d5168800380002c41054002d40155072040c240409544818401e07100f0010030841c0109420181c040000c951080c0741c001e802155103103a01c1c107111782c45d009110019a012400b40c2d0b01c2200480c4000304a6080b100c15503182030070f0101980395421440c0015028604040d110f89588441c10005140840103500c81c0d8000d00d40c400c075800300312031501000445619009800ca00759845500d000c600b095184d1f00070400060802c000c3c130740c1600202082d6041183c000c1031034460104105446408901070707070050707080752030f01e503540c0300280d91702e120480b90425030615204007000042d000707003803074003a4840300b00d04103040407500070100f0303203030361441d801500d8122512003403010070a0305842c030024055081ca03217294a440c02c0e21b440703503840011150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169439460 1250 169438210 169438229
    0x3f0b10051608041d1b1b10020c0f0d02160e07090305062e050d0206210f0414070b040b07110301060b0c070e01060c030305070e2d0108010302060301 65
    0x4252281003000c8101c214841e0307000300d80c9500d454480640030328040d540400c1042c840d955001107002440006428094109108803140c0b8152203181c0085401510742d030034185905c240140c0d001462014000b03803010041c070070000e1044017190744140b071416448007409000e54110304000042030314444400402d682d07001c4880da0300361300c80c00c00450341c0407510750000c0d015001d10320920200d20700000350004c03020245080c8041000000059807144006441a20b50008141e5280c0c401424440007402d01001d8140b40d908200d1004001803446001c00c50784120680d1046040008002c0b900000042e10400c1a00a207011810020450300700d00c02c074040c41c20003020116100082003004201070815081c0030b8002c4c460103a40b10100304164000040310340450081c40e03c0822580500c0041c0ca040b41c007030b50340c0c1c80902c00a41e01c05500818020301b1030b604002c0d00080d1f81c0c69548406c81e60320480c480e80c00e0710302e080152030303000031100140b80c0c60400c2c1000103101c01003002d42e03600c01c01c3c0c0b41900c40c8410f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169440710 1250 169439460 169439467
    0x605120603100903120c08010f060c080f0a09052805010e0406090f0b0108060d0b060105031509090705040f020a0c02270403080907140d123f0b1005 65
    0x40000c0e151100788900c400a4600308490002003690080b42c0e2080b2440000052041c6c40c01c068050b102e00109029000320041020f108000280c42130080103080d074051300fa1b0381d00d00103040b900c1c0c10b500d80c8411800e82c0803400c00704e410002c82c02d00443c4050306411000d00c0010445c10100c61440c0020780707210301c0c2e040000c1e440300b4607460303a503036406007000b0708000301d00b04100004e090346d14002d0300038503090500ac607080000080380d07402c000e41100000da40c00000d041850340e951005561542000d0720080450452901524854440f00000d500176469440100392051901c802c00080da01800301803000180180150040240c020805040e2a68116019004608103451003080d80c003040c101c2c1c5803050000c00510080c16001035441d4050b0f03800b10305503201e06c0d03180c81c400394036003903a0240190801c010000c188041b501c27108058445140920300307080b0780d00007400e20380d020b8030603010300f0080305100302d0040c0490310003049800c00e50003956100b80b10901d150070000300403507688203202080c8500007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169441960 1250 169440710 169440721
    0x1a09040c021006030b100602031e070c0506120405010f0e2e0203180d0e060406030203060d020301050108030a0809010c2001020412030306061704081b030c030a030207020a0f060512 79
    0x34000c2c00c0c00e18016010401a0070358a040060701001c0560b482d204505011002041d030034401700840711074400451000300c40c101a1400e02d442640101c100307490080c000d41000c1200d0f503491008101f00201568140054101801d00707508403810400d42403041450039810510305440442d855400c40e03580c16204420002c0300c161140303d21072100071585642d1001080141000742d404080e020205120708a03648448459800e451610303030320407059480351b07050204004480c072079001154061000740034145107842603404039080d0b8600b0707041030055400101d60907001c103501640c2d081c2d001c1d4610b8001e02c481d0b001000c0c082d204808012030710140d052049034210300c0b07400c2501181c0c002c102248540b00c102800b400e00030000d00050041c0000102d042c815519408042184603000b5508404428545441c25400841c801481080860540070501c00b0285103d0148060024002c5503140969501494030401203401c60503001040c0c10884402d050004030740c080191070503d03486800000154494 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169443210 1250 169441960 169441963
    0x3200a0620031201180c09171504030e15030f0705090303071a0f01090c091e050607080903010507050c0c0904030c020d0f030e010c05121608120f011a09040c02 70
    0x21180320307080750300c00003800350f084024603040c0d01c0c100d030601708541d04104200d0703144405903828001e841001580c180c40038082c48848140c0c08440003d80c0046442006025104082418048605901091440d04466006d0802d4041080743c09142018545140741c181740260003a50003401c9441080400b01d100f030040d4800b00100c2d1540754109108814800101400500040c400c40304402d0520464000046541540c0203940500c450380d1200d6a400d810303c1082942c1d02130f803e0807010601da406500003006e446070380c002e20443e4010036003503681c2d098810074542034880240610701009020041d80035000c401182101a41d101110b038001c9540b12810100c80400508030080c1d4050394007040202080486122400800d1003501c9188042d0910801501c4254852030082d002c0d0700b000160b0319a42c1d02c1980201503407a1840414000c50604e501c1d9603406820204001182944d01824012243c0c09203030301d2401800f541003403880c0c00e400b111480c4040e00030b00705c034607008648130440e00381c10900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169444460 1250 169443210 169443257
    0x51303080a0e030a0c0305010b09281508010225150504050109170315030118020112020c010207030216050a0308180f1906140301030503030403180506040b0403200a06 73
    0x802011940c99000d1424491702100192200b150250b20b1b2134112905814001110b5104d0704d0302c5140ca00c2a00800282c0d20f10035245002d800404656546040b612003003164099000750020000040c0c40b11041d00402c2c5c0308042540c1d0030401c403c41c11181900081030b000500003550820380d4085801e40ba82c1c68818007400345682c00620a0000d400c20021407000f04e00903501c2000c41c103180001000001d010b0508030303110030148031401031072110f101c0e015500038103052100700741c0c040e00180382621017a581422a00b1152003203005030800075160301c410700200c51041c050841100d20340c09083c9959100c18044c0700f00e40a41c0400c692008800f040ea503640004522000d2000d0400c00320b0105401c610300c61a956400303480041412007031002030007410541030703d043c0d0340e01200951031a110303038030181c0d2001203003c00c0102c0b401c061100441d00e516041c0141c030003001850b00481e241e40c11071508030008110b202100452002c0c6800d1403640e40e440400307800448000b0704142100f002050000090180e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169445710 1250 169444460 169444487
    0x20403050d0c030318050d0302090109030c0b07030f05180f0d12032906031f080a1b0602160501050306030106170c010e03030a05040603050c07020d0b16051303080a 72
    0x255120207100580c00800d8a0b040c94402d5a04101c52074044508840c5c8690042e0044e0059101e100e4a0f10094000d80c0245a075090504010501075501c0d07a40c21141041a0090340080d100407849004168101c0d400c0300959a15041450400c0e0f040c807044411003069881d050300c50303110303501000780d1506e179103514400c0e880d008150001c0c003030451395000d006024480200300c5c010030b18110344000d40000e20940300c54404000e085070300e1a242d118800000700c0440d6121288609068000107200c06c0c00c0004001640c403620421407090001c05610800748025400b0b242507400a1001410400840b202082529400d007040c5442ea10343d040840e0041801d81c0000e071101c8a070031145181c0b00c0b000030307145c0380300c0e8400da0320300c00301c0344080052549034094071850002150003031000b809060300a4100a600c0607034025603e041036040e40015080c0c03034000c20103070f4140b2045410b00c282c0041d4501c8948a102d10b1b070401130b180ad07142140408160609210180a84101190b5041310900c503210307500158 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169446960 1250 169445710 169445713
    0x20d0f020a030e040920100906080a0b0303040b0403200108060603160203090a0803130605090a0902090315160314010f030323042709082a0715020705060f03010501050d02040305 78
    0x86d1801a000c0764081b001e000214030030721102d903401307000c1ca100701900e809403040e9540d0300009071a0030034145c001d031540400c5203070b240c0014040800ca10ba480c00c040c00045000d40c2c00c80c0c66090304101601035521100c2d40f060f0402542070200320f41a1182400ca980003440450007140000f98904103e007140141c0034021740c013540385040056807000008c042c0801882001002d03209654806c2c0544a0303202d001c6500790009903508081000d0103441c1d001c4d108224001c1e0603110f90b8560450a801d0340c89003210100304c0c0c80c400f2044c1210315039061103541e20031540b82160840a50602074003400050041c40010304000c40c821405003000c81c032100201e114102001c2050710340d0b8072940384142015000310941c6d40014060340070211a981070182c085450b41060302a49094035200c102450303165900c8180c07500030109180352070403030780c204030410003400c2c0da082800348004644802401c100507a801284111014800c401408066004581c11101c007402e00580d101141010600079001e19031018186 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169448210 1250 169446960 169446983
    0x150109030b1806090114040f0602070210030617010504080906090102120a030501150c200316080f0f01050f0604090201020a140709110a020a020103020f0705060412020d0f020a030e0409 81
    0x202c0e001d0829800890488240c840c40e9403001281401c85200e50b0003010220000c0300071501151081d050141894002c80c0d016181015540102d40c100b0410141500002d90f9140c0404c403030301d94400085509002e0a00034000ca00745038860351814018440054031440001400302c1603603000b000044203000b002c440d420384074a85140301600074a0240f2032a8400e04109100c001c00074030802c0c070401c2c0540e001a18800c030383c42c4040e8017208408a201620381611a184500985410b091700003401401150020540448140c2c000d81c1013001200c2d50300140d0f1b04000038801071070040358990340d1110381501c00082151180c00104e00d0426401d101508000302ca07a80309000b0440072441d007064991103071007071003070800a401d03103120780c0f00789400c0c0b400580020049074010740c40382d001002c0b2044407142240c2060466150b003030038081c1c1a10100c1d0a4a0201910514243c05001c8000c0c48000c42c02c04000100d0460000f03526080002c00040403c005d60f100802c0c503030741d290700050700c0c250070103c140344 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169449460 1250 169448210 169448221
    0x1050f04020a0815010b0d0605040515010201060909030c0210020106030209091605060c0d12060b0a0306081e030403031b060e0c01300f0212132603150109030b 70
    0x6810a09580c140d0250090500203d00c9003000168803048000301c661000040c0e182448421054010542c042a0180c6801d80024030b036860307004007030044c081c01c442d0410140364031001900715141940000d4589080c166840e01203034100701d40300760890b01900c10916141d0080350490051a041d00001e41c001d05420a201c0c6c1d0080005d480360340c20f058544084546502c403404c02825008128031a00203502c000d1203608000d119040482c0030340c16004001c200181c80e035002c244140c04c044074080019903690f008000b80e007010004110740c8403001c00684000345c20094800d031207214901010f0700b400030f03010030302545042d0502901207086c2c0040041050440c1c01120076260310011040078000340306200751007050705070b04e100380c0d440140302100c500125011400240c0540814140c03969410307400d010380081c08611a2085205104052030020817865030314000300143c03100c030108a0035000240700807158035103d1040701d8101c011860b502076601881c2d40122140545034200614482085c0103010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169450710 1250 169449460 169449481
    0x30403050114010311040612201513050a05151c020f04180c09140118290403080301060c14010f0608120c0601050d15050c071403090307051504080105 66
    0x34184da229a00701504d1000400401080d0b80707070703400744101d40544081a20002541c220750303d080b849401400000030020301c4000380074441c10400502004c0f200180120b030f540c008000c50b6025101c03ca072902415400d2001149104642d0410402039601c0061041740041c008000c403101004c5450003075641c1c1240d41c000d0310081d0840c0c030817088010300009040744458010700651501c1c606c1955201c42d15460315403c000350461140080e4117200d803450f440501000c036079614030042c2910a1010b511501202d030b001540e03c18a480c2c0e8001c80100740428000030711200c0131241101c006123400ea54401903800d103072502200c10085020075600e000f00d400385007280c640081e022603040d0707429540803000300c5490300d40c1c61041e28600c0d02641c00100040c802e034580303030441c1c1484501601c1117401e071054104d02041111020760710200c11100219043c010480c00000c1c7c86a207181a0000c0c6052600203800710740da0b1101c50050034414525101304e2001c80310301405803070042c960b02c8020300241c1000850b84 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169451960 1250 169450710 169450751
    0x62802031303030b012d0306080a140f030f070615210203060703060f0e0a0e0f073b040201020c06040902030a061a03010e070905100f02211602030304030501 69
    0x110b001c40d06180140d8102c0d0f00445217034942035030307150000c4c60444d01c052605070408034400d50101810f56035640030034071103002c1146242080c803070350706481c100c0705a1205038074101d085c50ba04581544100a616074020012040e01d88469002c40045010b98070340d171700c0c06c00c10300f000d42107614400d400d02080086c030201d4001c030300162030080d0300361902501c41d06030803016500c19000381e00580c82d404404004040c961440c0d5684070010f400001403c120ba0f0000c141403a03c946c0702001c0d00c0d400100306000f410342d0b03001c030311001080700355100ea11400500c1402c0000310a0071a0070308070310001c60024003564024024100c020f0001050584c0d1251920103000007500181c41c2141c41034682040850301172100400003840304044c21815003541c0c40c0c02c01c035094040c00202290100440d1a400240036110782c2038144440c125034135010342c1e841034258003d1038030070440300860740c500700c5403c5100d151307102400b212400c00d000c0361001d01000a46c00441e18610031588002c00640c40e0503014081c0d00da642014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169453210 1250 169451960 169451963
    0xb1c2901090e160f080c04050d06021204050a0c060206061315030506072001060602062e0e041e0b0c0705160b04031205040e0f1302030d0807200628020313 68
    0x590f0102c000310001100d1030320007151260a046c80400040c030440c030b003030262400401d20602002d407034000c040400c0c00b6408802d950441d49076206c10128004c00100304500702c0541168802040d0500c0c0110004807000b054002d180150395582030610090500030b03481501441d0058101da0b41810208401042c24500000c12014207003000000303802d591040c050b40040729400e60050589031104442e00c1c018400c0c40e00307485024070650700500002822083c10b0750003407182c02c050f84080c1c50035040010b4004a08000e00c0c2049582800ba0000035112184403034001602800c1c0d19150146403500c5407900748003803002111201050000903458012030000c005480c0f02e0420001400c0070030500b520039010318080c60301d000a40b180000c4100703145075480b40d0b102060720902520f030041500402d04100c2c413680c9003c0010500c5c010070280a400154005460714185004510b4030103244419440300b40152a0304002a464cc0010ba40310009044140001e040303000215a40c2c01c03c0303c9141d40c001001c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169454460 1250 169453210 169453217
    0x2100905060109110415030b1f080601080a0207050d0302090d0609051608150a0b1f0c0b1518040c030b010810050a0c050d0917040b1c2901090e16 64
    0x20610030741c02c1c98105450480b41e6103003011b070040b4502c40080d00036240c200407081d0480e42c2d80180702e0f4000079211b410189000035480700d400301d080c000f00041202600410880d1054010041d9400003100007420f9440e100107440c0041e12a24000001041c0204005019100c1410624010144070000c0341402c00b0000f03800711040c0403503a503090288c135200b80e081001d00070190040050ba51b4041074001501c804d000511024070070281281c8255501c3d0915520300c0001e40c020011020011040d10851b0081460410305d07400c4d44054001862044400ea5600380c8614050003141c100b081e05450000078640c042c8080e0100e6071500c510302c0d80c84054452a5424500345008600107c1c0c0c070b8451480240d00b0740da9804d240c0940024400c01401c903000d01215204d0081c00380031800c2107900c0c00f0b0310280100c4400d1603901c5245065001c003401c8800750801c030151a00d201c400309c04c203045840b4001c0d2000201d0035180108410700680760050294003120541c4041010451a41841d8103000d003c4013803902c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169455710 1250 169454460 169454471
    0x31608101a091003090c140105070f150f1e021809010314010c080f061002100c0c050106140102030a081009051503010c0f0f050d110f090310020304020603040b0702100905060109 78
    0x8405685c0607520150401c58402001e100b0310403841c101081004e018108189480c8907544d60311000c408182c002d8901c0420341180c48002c0311103001e1281e068100070014407102c001000040302ca5020102c042000f5640000d05131020030b0b103c2c81070320b980c01c00201f0a0389550707902d05240114003100520701129528040044501c1805100384a001c2c1069405030425503441e1820b203c1030a8800c03507070009501c00c41c00d007511801c0040c05003000310faa10341e031212155070b10380c51701c1420f4a0080d00310030049030340c0c0c80e9003401c540d0340001550703407603200c1c1d01d058411038a5140c0b0110b48030390160002d00e04581004100302d80c8a9442180b821a03020070b0700200035546407800d0407100c142d41c0318104400940ea4134200c5548a12401c00346c60080b8004200148003104440410b1850780912080078a20320082000030040c40d00380070040302800307183d00c154a0740c175299000500c1480010f1004000c1044080420b40140c400c21a00300c81040c070400820043c2c0407824015580d8109205400c4020f0610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169456960 1250 169455710 169455739
    0xe01060f03180809030a020a0324060b0306091e01080a031d030c10031d07030605012102100e0316050f040b0102061911130614031608101a09 62
    0x207205041d200d540d9010074094001c55592080010f41c484c4807516030506ca094140d80140e52111284d000851140c0702428018a0b90340c20910540758030440710606030310f80307000cc010001801d003c80703600200444820006903501007c1c1c1008502000d620030140c004040040b44044001580c44e028901070b4440049440541ea408082d500d8070310000f5401d508070004400c41414001030485035030301d03c5e060209803404064540340c0d01124680517400154441103080080c0401c0344101805007013024409402056082800058010200d03030080c040d0040b41c0078000040d104034200342040c400281030780e80005a440b845103541110340261886107500c4950b2125a02e420310484c808014180c024010302c1e0b5600c111045a41483e40c0005015031b21680203441d4601110001d101d009604a00420f215007880300040200b00c130390a00c100004810400d00c0400c007218458603140888c140b800c0c041ca03940311501e481c0c000e4080d902c140d50071040c01c7c1060302c1841016000d401c04c0f80f82690b05800b201c0b001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169458210 1250 169456960 169456967
    0x60306230f0d1b06080c0702130903230d0b0a03030f0509060418020a110606031203041a0903030a0509070501200f0105090114060d0b0c070507030218061806010f031e060e01060f 78
    0x1407c000951000d072007419400d589025400c8003a00c18000c4c1005001580004031088a40340b83c1d02055000050006078200100654840c83c525107100740c852503001811a64017a2010100d59403136028404085164540b5980f003a0450f8050100d01501d4003200801e43c020070042d42120701110301150121002c1681c001700003400c0d03445a0802801803003014680c03550b00340d00b6030000c0c00960301030385510301c0c0c08465501c004039180246a0640155900d240c00c504d4130048641c041c0120f80b494019003010090386c0e07803200a6020099100a0340800da40080030f105140900940400c5429420001000350040d01940296900e0700c1003c032000183e641d0030100000103c4c007100041c108007005020480c0c1902d07850140100e544602c0445c0e03000e90b00da800180314a1003c2007080c104200240400240f402e001e11065010f2604240c220750078200100040d101400e01c5200304101952072160b45100048642000f010541d0722404120280d12124100340c1d2200034010382001c540c2d01121540038620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169459460 1250 169458210 169458217
    0x1409010c0f030b010e1002070609170601050f04090b040302031902161202030f1501030606090207030210020d11120702060106021603020f0406091401060306230f0d1b06080c 76
    0x66a03034aa40100e07401203000d800030311000078580d040169082403520780b030b19518aa032010300513a17002428014600200180740c0703462504401903100b403103107014498420015100d410340b10100d6026003520300440100e4002c121002d07016090480642c203000505130003000030300242207906048504240c44480a994900409c040a00714813000c100410224031010030050b6158030003015100080301d13028004d80b0304040f91001c0252070200340010401c12a041c401c00c0000c00c2190402d5080c80e0b81034901944481813001d40b021204c0e000140c1001d494615404003c030400307a11482d80d100c1e10100d210f00400d4904403001d401512400002164a5000042c5001000440c00756040724500f55824099078000807089660025100e071000300340008240281102c50102d00b24842c01d0b50314240000302a90310540c0803002c0c3d8800030000d00c503c0c034004c00421449013400d80b14800d5416454010030788104031480080c2107061000e50182055417450100c2c001c40c2c51076550810940c5a00400712a01d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 169460710 1250 169459460 169459481
    0x8210708250b0c0c0a12020109080a05091c0305070b040c05030706020a1202070e01030f030512010603150e01050f09090307080703090305010c020d051c0609020d0b04050a02090d02061b010f140901 86
    0x6208900004c0014100c00317421106c203e1620000c10310003070a0b510300c413071307a00506183c0d0007042d0045450822410a00560080c900b021213440c007696040341c03000392886c4640c02c009000f140500c4005070502030103902c41002000c024003103030b0340c4a94546000b52242c809401c11240300450840703c443c503a20025503541665100182d4044603482e5954100b0f01d041c0740781c011014098280b0854a2414115204900a047c5030301d010800c1c401020b00f20440708565040f0089640a06005001c146c4134480140d0241d007042d0351100107070301c40080d554036502891500500400c2e00142c410209580b002d5074800b144c0c4100024008951032000590b01c804031207188070006217003446a6a4a030751921403003112400c0000001501940b82e80118003664084c03001e009545480d0440b0308000d082511410b40c0c000715440046061106080004207410140200a4411000400c004c02020640e400340c1d09805004402000208004180b010140c039849032081c000c200706100140c400881070040c00082c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 169461960 1250 169460710 169460713
    0x303111605010c030e090106120f0510060509040e010606031d030c030d0b010c170301081006030503040e06210c010e040c0c03080c0c010e06090708210708250b0c0c 72
    0x11400c220045804109841e404e030100300d10345140a0355503d030300100070b0103812150784440d4030701809038800c42900da000800c242c01514080c10041c08401c47c0582c1420346800b4600a03039a04200000240500011214041f032540380000004600350194425940440801c0d0074064100400400546038064504042002e070002c108855140c4031035440340f115404141030043c0d02107490b80710b21280c40c142d5100050401800030046c00f5005042000707180c16002503c050140d1801c603511075407240168400d1940c00c581490125081d56104007401541c440304044045440d4151440329075070390020400503000c1500303200050315600740390041c900240481d07200c203034078041540e070111458100104140000d0500b44500c0e480c654007030103600c00e441a00d03001040503040c407007209030500c000d5034407007a01c03a40004403024021200c28801d60051404c2c4070403c2d20780c1150704001b481445800c4542c581031030801e00184070030001228a54a80380a5450901d90b950380c03a001c101180b248809d0160a0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 169463210 1250 169461960 169462003
    0x7050f0102031b030408030a0213090c030c18050f1905030f150703020f03060d020307090e0a0b0601020606010804080c01060b040303120609020c0a0602090609060a0801060210020a09060c050f070609030311 90
    0x10010240c005082601041d84ae4203013041e95281c28104461001c40254006a19080e00481d0b044e4004510740341100510400032602d8070f00000901c48602820810f40100800310f4030000c0c0c2c0007140205030003800042c0640e800d002540c85c0d00d0ba02c403c40805070005038003c840100320454824801e0320b801c80d02c001e1840e869910343c0750410108030004130013240e040c8a07958010400d080c0d54000e01c018011010010610803042c1e10b008800164003c010904640c802c6c1c080090356030388564450741050700301d0800c0d03644010308010039014000a410400080b880081c0c00402c05a0100d96034114110000c2c003000580c1e1104104400e82c81229030401403948a41305141c0417820560040ca1345030b4006024a1502e80c100c00443c0311500401031039008182000c0042020a4050040c1d25988100c40011480d16000100180805100f402007604104e040243e850401c801044a150002c071a0305c01c990025507240401050000140002c90004400000f0f41c034140100150000c0c514090406800c071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 169464460 1250 169463210 169463221
    0xe06010f1d0a0605120a05041e050705180708090d050a1b0c030605040c1205060f070e031e0706020705030c0103150906030507050f060a2307050f0102031b03040803 72
    0x7094419520560103000a8401c0200682d8036202544003c0c0340700c2c4c80752500c0302c0310304494000c400030082c2040b15032801c203010440081c01440c10054134400d9007940c1106148a8180302d46008101d40026420000030b10500880c03502d044181e611a100e541c1d10388000b6507030310340c80c2600c1d1012405c6901c0401d20a01c5032103181c0b400342280078070100401c0e24541c1e00503110788810303208080d40e62050741e9075aa610240000d00000184000c09820302140713a60361042c5980e83c1680c0d400d00141404080701400000c034449501c9508500070026004040718420320000084c144104084c1d00d0914061207500c1c0c0008109001184c40400c442d00100a8601d80d651480194040d160005180300407624401d00419203030254458500614014001804039508001c00c3c440d80c002c90611051180307400744620306440c1ea05c180005060809600548090010100070340340310b0244040061546c09410403001903908150301442c8507030300914144200010316986105584410b1b40c2c0609003010800020b034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 169465710 1250 169464460 169464467
    0x114090106030c020c011412010f0501030e03040f090504020f03030319182f0a030b070e0108040f031409040c0806090606040b0d0e0c121605061c0e1603050d08010e06010f 75
    0x154030307035420047c2a207170040302c08850841203001d23045800404a041010b01455a142c0700d0741491281d18030046140500f0503070400304002c410f1144480e03585d220750000b0700b103440c5d2050304016444081c088944904001180388204001c44c4919491a8a004500c10080c822440c50380c0540e9000144040304a50102c001d95a0020007190788d030a0400c0c0020304c51054440003145e000450180c0c1420f8440d06142d0401400c52032000e001c80c0c10003c12409000209107410440808994141041e2070081e8249a00250030b010f411545a801450207801c400c12941010307609210b248122480c811941e9200b0800c000b41c0168040c1254411060103400c01c0b162466011401d07400ca01400c8403d010060b60001d030310f407250902c0d00201908180b180781030325013890f029003018102c2190030030704012100700d1070f09048041c15a19000240c803100d04059544080c001c001e910b0f40341c410203420843c0c0b00c0c20300c9592580c0c0c1d4110070b40007a203030340c1c0009a0b8a446c1102e8900401d416907070728000c140300200c1103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 169466960 1250 169465710 169465727
    0xd05030127091a010f0909021005211006170f011a07080a030b04050604200f07052b0f020a0b18060f0106030605030c0f061b060114090106030c020c01 66
    0x101c90140d58405120202e16540702c4001c891907000c40c50111903042c81300983c1054250782c041c001007424400040c0040c5e0345c8940009102038140b030010340b42ca80700070301064864039070100d200c101801d800c1131281c003590706104201031740c8240e11280c10610740c25152040a0300e08440da261303580b02c018014810400e00c0e82ca0420100e6410080c02d0511306c8648400b8000d40c001901807001c00d564844c00c80c500d04040c0076456000b10215400c2203400c880303100070003982514240210410b13800007114a008198401610b0b000e5820000312058084440681034442d0300c00c020044240440401c0300a207240b140d900341480c0e10040c0d01070070b00d84081e56114003110301c025120781042e140352000184010820064036129000d0014035901d2549031104c090200c403030a411050207904180c4108099484106201c1c0071010705840c80c1d40c0e02e4601407004070f00e0340e180d41a04007541c0582c0000042ca0b0107510310340140c11004a41090b8a6681c5120660448804201280c0560805807051030651b0080711203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 169468210 1250 169466960 169467029
    0x60605070b040209180d020102040e01060804120530010806100308070206031e0403170108030705072d08010c1803201c05070906080303060a17010207020901170d050301 74
    0x8000503031494511608101402c4c0c6c142e00144e41c08a8200885400b4410040c01045582130400f010300342901d5030545504144187c0052050000300b1018046880c1400c00322588490700e02601071038002041482e03510213115034555032040d800454100c800005999045a50000c0749901d004080c0d401d00c812a000103104d00c1101c0e2802c40040300b42000ca800c024461840703551000d1b030300e9407040301041e5000010781200d407081c1d109016440000388005210b500b42d071180c03030790240c0400714400c400050012035086c0d106e0344052944005150134054024031011001500d0307000d668560940703600010202480302a107107540031881442e907020b207000005085079020308407035024140b404040c400c0d56180c15003103640d64001c490030000c529003841004040c0807600091807860603c4000070340184403500500480100000b076000a00b407007541110401359000c0c01e481001c0d80c0d106880310030b410003107004008600800e8900f00e40f0602c80c2d01124145d480303100071103583d1100d03030000c5205000d40000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 169469460 1250 169468210 169468231
    0x6010207050612070305090115060c02060904140a0c0c0308070e01030b0316060813030e130e0709020901020c090c04140f04090503220b030a091a070201060801060605070b040209 78
    0x30085056100c0b40300401000c0800f141ca03030310030b0a02c500d004040b42c1c2c0052403001c290b45000610754004018240080c101e980920388403000f440c1c5800080d903d8440c20011940c81403030701c0c00b0340c000148603144651142c0c4d18070314104200140400c003940c0b0b9403500d000081c0010540360006407200e006000d4441824410316000583d4480c850201c0e01e0714094200303200c4a00d00c50713482040200d6008984541c001c80340e0342c1181c0788030703d10358020300344001c401001ca11450390f282c0e03a11405003c5510100300c942401040b41c5000d40c0e1000144001e604c1700407000d00500820701d80038050700700955002d004030130200c9a81e14241c500b80701042208038481e01154000e10300d600a010355a6940104c0000e076015030b020710380d21300c0c4440e074100400c00b02c9011446021f507480e10170400d4001200070780740e00c0000e441c1e020411240e01d1910030100c900808030400411401000c2c412150350562005099a1000008004050701d415051386c2901440301d0003451403241100040050904152031500450350a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 169470710 1250 169469460 169469473
    0x604091d0706090504151a0304030c0f120806041e020a03020f030f070306050d030f0f0c020405040302070812040e13030311040909050601140102150411060a02070e0f0c0d05060102 79
    0x800d0401d0500ea00c00c4001900703e80092240b858584101c0c5c80c4400760b6002e04006134540842040018000038107034005036008070000d411325020f29054104254000c0c2d24441c1e0f000c803450407048960904810f1030000d084640000e20508080c41034040c50000c84c4040030b5003c0700d541c8020065032040c81100209a02800b2410b04442010043d502890405406d03400e107140920300203007201c0f010303030016105007003100721100405d801681e2030360282400d2900307140500043c0340c103843c08850070000075041442c000400c420f0543c089a26400c2c0c890080c180d40d00c10b400b80b500c02d48207020340e000741d0506008503404904080b8560b030710503400c0751090501140c4c0081030030300c83e40c998125921035124035032100544420040c0a10109024002c40e0486001c5500da0400003907a900c49085070201900c3c044001c2806d220045800002c0288010146a91038082c6034009480c1d4299200d1804100707034010100c3c40030034020b2140d0344a03c0c0d170381541d1404c1203134041509010703003030140415040d030044a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 169471960 1250 169470710 169470761
    0x1109041e1418070e150103060e010602030c0607020106050a060e0d080a0908280807060603150f051303171008030403030f0e0a0e0a0f06170c031209060409 68
    0x1402109003031150724040c11080d107805402c41c1140c00c4035200c60080c580202c1c0701803041c2481601d00d1074100d1000554642080c15043c01a0000d1200741c001c0c4400c45566000050003d5001000300038020700d510a4503400d031103220050382611000d02601d9484200d90302d080c003650740b0500409464440040000d00c40c8811034442003220f40c0550800000640407420901a804040140081c0b0051048114443c001c9500500c7c440a51100000b444001c0010701c40080c0711081d0482c2000d150440320501102d070b00c81400740024503611319040789050600c000184611190b03844043c4c15901602c2d48290402001d00c4007084170401403081d200307010f00c0c0501290003041040540f01961194403268595100207a015126088101200f4899030140700d00340210302c1003420781c03604003100e080082912003042446401505564200004065080200300300f83c14000501424400041d4156500c98181020511451080034500703034102d242000204201045a4040202c03103004130801c10058556 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 169473210 1250 169471960 169472021
    0x319030c0f03110d02060423013e18040203040507172109030a02040e0118060b04060f0608060904140307060507110a15020901050405131e110904 64
    0xc08805800040d40f4082032103919008101e000c000c101d82e800244114913103035071407070190b80c4244030110000c6045101e628646209402c6018160840f942e605e9101100e050420790700c0360031101050172003903042401e65041800b40120390507203900070003489211108200340006540090700440f218480e03020006100d44680e54140c01c10031b0a500548074001c100c205407001c24030041d0303022002c0f0348200b0510380c0f15a80014040481e940c103440101b04a0b05814119006100d13038006404003043c03000140c001c02445511100e4000000c40c3c042001688603424410160860f00608011449183c00324409103821903105522902c108810300e0000504124282075401001003103800c55281d00901500c1030f0070032109001055001f0060101c860b2030344540701040311030303040c500307940b540003030035a90302e9114104440151001604034a9030640055088004240d242001481d160320b05c1075141d00b5110b039002d43c0d400c820003000001c1c1004402e008000040c041410060184500144d0964a83e0344 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 169474460 1250 169473210 169473233
    0x1205070515061503071b0615060e040614060304030c05070f09090b0108060c070201030207080f040803040303030609020307080f10090c020102040807210803090c0d0602041509050319030c 82
    0x107034440d41880d50306045092041d0345101002c0300c1020b00c010b0013004001c9912801c0815100041b503c10140c00d0120304204d402403400d4240034256800303003080491f9282c0c00c00981910311406442c100f002603034031204904440001070702a980000c08002040200b40700d921880c031410300038801da4418542e200701484581c90309034003007a00580ca50078884103224410f1069030040003c07801808040c905075603800d1091007600c0703000f030516601082c084140080030042d6007a143c0d01451499640341c45510031075a0380c00503c0110002801d0101c085082c100360700944e070013092035866001640d11800c0c41450900c100034855914000c0e107160000300300469008500340528a6000180d589090610541c20700245810004d1907461484146071001500003946420740d401070340c200d44a4540c25070713043c01d100c4200b60030f65204c0c0140d01703410180446071b03004200726030b2210402a00030405040170b50752007041d48200c9034035400c01c8120f02c0041c50702046140c0a54030914000558904a5590258284 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 169475710 1250 169474460 169474483
    0x90a15060c0c08010504030903110d121412012912180f01052d010302030307030e0307031b090605120c100306030f0c090c0c200d050a050c0a0b0406080412050705 71
    0x4017003250400a01000e00110700500f05c1c15101040d40a2003500e43d801da500242401d081000003601140c0f544de02403500360384044082100440c01540e40750303030300d15401032202d40d000001c7c01070a80259080000404403110061032841c40300080d9540d80020312418804d0040800034007642000e030040f0301007071003902e00c180001d0307940e28030301030400101d9a0904440540070268422020060026035000425500d406034985040032001600002103414500c8540c001046011002880050342000c0c4840009075200b03542c00b00052942d0b0010011641030100b444005a009070240440c0f0b410039000060b41050319040205071f05940f5640c1102900342c0880940c0d00102003c4180303d0110706000d00050f0000e98a4421944143c0c0d40b99518080995a1440483c80d0310300728a4080383c4504401c90740154100050355044071490600b2900c840c00004602c2c400c013002c80380400d8040c900c1056070151001542c4094181d40c444c0c1d11044002400d130b420390103021081c440980015030400117600c111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 169476960 1250 169475710 169475717
    0x3070e0610052214030d0801030807020303090306010810140609061e03071211190e1b0a03140c04080a0803060301090c06020a032307030507020d02040e010902090a15060c0c0801050403 81
    0x40d8600440703950000784100c4c109102c0d800c003549100707555501c8a01e00c0e0549030000102581c90000e840003900c0c6102c0c401c0d00e44d4041c003402000141ea40c5002c0b0385665284c0c8562030a020055980100109001048440c02c1d44003c05201140a80c1040a04000040c03c1d80300c41281034002400021b06c0d1400f60351281c408010400300744010002c4040190590890035200380c1c070350415089a50942a00f45d0180224900c0850001480d1880c1c02042044914020a00f41d03504c1c803030104002c0241900032410740c000048240800c044c081d420080340c0441e00b0600140c50800f005a403000c92541c00504029490f40d258010700c0c1c007180214005c0d90003014603400804c01d54519146c041d200c08900c45c4400c2a45074028110040c0a418000300c030701c616410300d851903903900c061002907104058290069049031400385011608001503004a0303056008a0b030700b41c8166507042c40d5400351440b842006000d0780918104104d00f5001d2400c01500a1181359012034040d04c0e13401003400c403001200c0c181c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 169478210 1250 169476960 169477027
    0xe0a050a1214070806010b220b030105040e0f10021305030708030406120207030e060f070f060518060c0703030e0f150f011502060114040914030a080603070e061005 72
    0xb00800b0100101a110106010f022520714000c00c444e1a44814480d80c1d841d041c0004844090700b0028603c2088800a0090201943d03100d642e221080d80090140b140035070700c6e1640310b00c03412400040c03100305071070750800902000762100e4840c0d0207500480404410040000000b15440d42c042c8249405801c4210085413910319025006000c032542134207000a10344104030090119a02c0400140c1c445401e4444559400c040c11501c44e0b50301c24801d02400300d80d4840c041c0b20401032030341c00c42c501945c2a00100c008107680d103041c042c0c44400a55075010f10322001c00203440024000d030008117103416208251200a41d080c441c00381004400b81e0341d03000c6d0500c102e0420807c20704440e5058090517050240e0803200c3d44148000e990f4141c103025101c110411050800380300c0c0d42d83d401030b43c0c41c0b03507100d00403202000061078642c2e52a005002040c000c5161400011458200041c16900b00d803c119220f20881c0c4a410501205007204c0c904001042010011402145a80209100381c0d04814480303114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 169479460 1250 169478210 169478213
    0x230d02060903070504020d0906200306040c05190f03051608040b040809060c0102070c060e03060f1b0d090c0509040f0809010210020a0806030d03021c02030a090c1d09070e070e0a050a12 81
    0x849072145440161722b811032005070030502540090700c1c0d10032016100080c0d01844504151018026001c420040c0310b1000c41d03c00c40f841c0d000d0515181488141c03130a01503516005120300384007030805040800100020005000f03c0c90440c0749030f82080c00340304d80342d01c7c0c4190f04000c0390300742e408207000741410380d00001c1c040f0400c80c041840d45c000700314a10301030603403031220300c0000c0d10717504003800c00300849823000c020074040d81c42d40b00c84078410103021606130355828020141e0006012006030548058900500c00166030031702c60444d91140d580450700154030740c425694500d0f0341d049040024114490b07215000d400c010644020940c40e1925165440d00e80307050801c26150031035071000c0c4070030940180030101c2c0400a60070004100d0308450005038490b80d41030694001418690005822032415003c0015145110195541d440c0340444482050780c2e0381c51f114594030150340c4601001c0c4080000022003036072045004081340c0900030203218102c0d80d5500007403a0304080f60002540707107102c10b03035000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 169480710 1250 169479460 169479473
    0x60c0102210109050f06100e030706031a0301020406050f0c0c0901180506010c02060405040c050904060608060901080c03150a0209120d030b1c080a050c0f0106230d02060903070504020d09 82
    0x5006101ca000d060044c2d24100021a0f1051405006280180445105a070149000e940074041442010301101d81c0d803562540010b004d800c80c0b11100c07070031080115140c811410b042c021141902c2d00d1f074403164030303001020414040d660301188801300d160113400c0c644515a60b440030098020146082540403412401c41780e401100e4000c3c0c022030600007891000001a00c4a605407011104211400a1242c80c00c40c0192454800d02e00102c1e441458030601259160304403000c0e50140c03c0586282101daa00c1c0e880e900e55501600c0886549a840302c01c50440c00d0400121081e40036441041c05400c0c140d107240071520381300041d191201a0342004e03003404200b0784c1c94801c2031880c450454943d01604032500d08410b4138071342c030803002e06501030028070181034500800803151443c0018044511011910f02e00d01c0c02041039001e2540e1000c10190703d030001c0c04d03035501040f131607220062034400f034200140e007003142c103610031643c07690035004240b4001415a40c91010b08580318800c03002003560781480c903065 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 169481960 1250 169480710 169480777
    0x12040302071815140406050303070501020705060f0c07080f09042a05040509010e0a14090c0a0501030908030a0509010b030a05061e10063e0d0f0c02010c02060c0102 72
    0xd249a4648a203902c02103d240803210b044134030328811007240210f0400807078080c15083d005190588800a440401c124056000304403a501500035102e0948032a071220b035500406072035001c1040810710501010801c2c3d01c00401d81072100024461a288041002c1400d560040d41040314020404800c004288584008c80d47e403140c0340d1030441c2c902410a40012498441070042c1c1804600308000100029a9503001c5e078401c0c484003526000343d18001800c01d036140724000c0494015001064000390650003801101001c1d507200c9416819a6a488000002090010440e411a64854401c1c00c4240c81c1070285046050007400601517605c0c10100d141c2c543c2d0061f0300da81c00b80803400802c1280c1c040280d10040e080d41e01c0ba141c002444000303640380754051084403001840103103180f001e022104000e004200c407001c00300781c2903501120713074298141d42c0300204540d1039001c140c4035103114006600c03030080320350310034030040000b410180503502c194226080108140c0c503041020700d40710201d006401c6c54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 169483210 1250 169481960 169481999
    0x90406150b0316051303170a02010e01050f07030b01210f180f0b0a11030c0403050c040c020618011b0906020f06060f01120e01050718050a030203030a080405031204030207 75
    0x21a8030b14144240ea4042140160030310000300315010078483c0341c2540c1e007040310000f10780140b000c40f241410043d1008950f0301100342030b40590300e0880c54541108040c09060710030425203400500c3c079540d2034010740190408850a0341081f010032441030140203614030200c01d00070440780001c1c02121080101e81111320b00c07596144110f1004180d0070004854a100d803540300d81c030a03602c204030744404900c6000703070510943c00c108600c2c010041140ba0350704940900100da01920480350412181c406000443d005034541c00016002107001811450310f503013030644a215144000030f65000800c0c0c00f1044070880510000001d48105802c10119504020b4585800d040c03002400d41400e210b00010340c0140c0c0351500130b061092050301c40c940100942e110100002c00040203028900e8a4003004156070341c07000c0449800c002d401e0000c40c0d03d013440e291840c192a4098001d51074007080000c01d44042034010011a074510080043e2241302d091002e4050040384a81c0040100c941845c05d6003c020340d50034034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 169484460 1250 169483210 169483229
    0x602070b0c131202030601090c110a030305060108070305060307150c060f0905070f082503120305040212030a0516050102091011010c0807120e03130608010927081809040615 76
    0x403d0016036030224141d411519000400181c28072032190903191908004581002805400054020708d034242d00310b02d202c0e200990340d25600740d507000801d40c00c450003035a40c180c045e848041c00b44615111700b1040031754210641000081c40d02030350b0311032058460660b024140035458400c0e00c000c22004000a001401180500c481800e0400c81c019a5800105003421024441c840106110711900c0102402441c2c001009140140d90250082c024000c02d075012070041101a407074108510011003690005502542c500b4904900030b0802d0b012210204000d552a550822100c000c55407500c0841d41010700d07a484900d600d03c0d040f64000d007100e980c2d60000091115080400c4451684203212982d07041481c41e00182514003150282c0c590301402201d0781800040c2180030030b650b900003a21904944070b40d442030142c6102291810091401c5840302c4031300e1044100007a001907c50000380c404101180511120071341d040c0c0006840f200b00b40c2d0700b9100c0c40e90364549103201c2c40c002c90905000e840b0613607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 169485710 1250 169484460 169484489
    0x605030903070f0309090921020106050a030f020f06031e150f0603070309060501060203180a05061c020c0a140609010911190f08150a0b06030406090602070b0c13 71
    0x10340d503140c0c4960340004241c1d690382190365003090b02401040024020003401041980710500d04078088025000340800c0c0c3c0402e40034000c540510500844041e43c90281050300e505146076601035250640c82801c9900c440141445141c6807180ba014500c1501412084428603031840000000f8980103440b00740f0002a0556500071611703400707005114a10107841d4143c0c2ca58540031b08500601c41108010700c90340c1003400001d41c107680007018094038211640c01105109a1008004160b03074640301c1c160300031106010403094a0201c01d081c0000205404001d403412100700d00d400d041802000040b079281404d10701d0504d5020040000c00d9000b11100001c01103240c80d40c0710f14560485161200340704041c40c0340000c80c111016000070004160a040c00c919907601d82e1440d0361900102c14440c402c039600b80d00042c801490a00a94001e0000900075900e5502c95884010140064501c02d4076155000c0103603100050580894a1041490b002d1943d2142d0b45050303240902200350f40110b51030300700013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 169486960 1250 169485710 169485721
    0x3131e120201120b0316050307050402120a0203060123070b01080d0c02040209190810110a23071505160908032a0304080105070e0a08030a11030904020c0102090307060503 75
    0x110314000465809003010a245480400c120380900004082107405001c0c40249401011680b28000f050f90710403411381c1e44507070700d40d02403100b03e000d080744c00c02682c5801c4c000304840109560066401c44418900140540c940390584c4a071105000c10306075204000050032400c1c040580c020902402c04400905600140c0c00001006050646030180c416540052028001c2e035a81c200240b002c0800250441e000e0355400700e107615008491079404034030741050f1055100e1441c800407910000002d4854200800340041310000c08108a240c0d01102403080003154042249880d407021a410381e90800725080c40c06540041401d40041034800510607865014011403002206417103524110748041b00300001c2140401c1081c580300c80d070b01000740c0400240442c03025010b4000c24422010340d280c901400306c0513414084034000e644900d08090300300340710714080607115a6143c04003550360f030b007140d0800b4000c400280c100da00114042d15681c2d0300043c40d146608050100701c0c020001401c0250452400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 169488210 1250 169486960 169486979
    0x60504030209061e040e07180b010c260f07020111010203130201050706020405040618050f0105280807120204140c04030f030309050a0305040314070302060d0b03070803131e 76
    0x282101d44100e24401094a403c540713290300c109040300040c42400300d00d800d400129141c85050058201c10400003481c90040d100b0350050000424060b0755101c0da07003085480b164148002056550042850340588040601c0a0030142ca184079486143c00da135003202c1d02c00074000400c10f200b10300c403590040c0202301c40b4020803040c04880580a080890f40c0e1401490020001e208542189500500e4034001252151003100c40c031072a0036412404111039200d0048804e00c0311405d1040036800140c440a05411a01466210400e540740c9041190f0307044d12141c111341008110b4020170b0b0f2014030402c091056240c9400340a09041d80b2a401c41281d0401041e1030060b840b490101401c40c01500340d02e41c0406210f07a00030885242c2000581d04141c0c500c1c80c0041c502c0d030161000f82c0c1d810514480d1540160300110ba00d80c1260303402085246051a003403012405402c510b5400399050181143c00109004240010a0b50940e00018062064102841084c040030403140c1d01601c403025280c2403081d28034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 169489460 1250 169488210 169488229
    0x1b09080c04020706020c03030c07021e0a14010e0a080c15030f04032304060804020a05030303131104090506040c03030201060b0309030a211e06080109080915070203030705070e010605040302 83
    0x80c2560096030381c01d10342c01d108000e8403681240315000c0c4000810084400d4481c2c01802d84039200715203250401c001842c041d0310b003280803074031a17034010a45042001400f0600031500c09440040c1429440300080c01d000400700e00d0240d1180c107494020b20f118207850f141c202001da5180c0c0c200101103003141010b08545528460040c002000d0120103803d210880100c00d03034600d031040c0d040d00210380e5103403545001840c0b000300340c82c201c1c041e40d1005404a45468007106583c803402c940800e809803081c41d900c8503402c24078072044580c1c0007507984901c6008610140300715440b4a000d5843c56489901e907180003401c48009a114034010b41081c0140004084044100c0c3d56000061810214145490480a540040b003440c821342c1c1d180391038003040b10035a0407aa81060541c0b044c0c0c08004590355062040d00380e910390f00c00101418001c011021070b9213402225140b21101d0800c0e0070b0704011b040d42c00f0170319503805900b00780d826500a20003002450718a0f0000e80c0500407620303220f4200361441d4081038441d40d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 169490710 1250 169489460 169489483
    0x4020f2e091d0702030408030307050c01060501050a0221130b030f090a0312020304061803031e1104030b1e0f010305060619091e02271e090c0c0307061b0908 69
    0x9401c02c2c0481c151a1080055030054050b80040d241d981c01d2030390000d051a404902060119401c00c080040d01d503014409a9038080e40340d4016080600303082c1060440d001b114420ba0b100c011007400f50504441c0e900000743d0140002180d410303600c1c1402550304100c008006c0003241d0759880b40c40c19400280d48a41c03110800482c04101603200d807624a001c00140c617007900b424551048500f500c000781a4180c00c4001c4a0201c603100b50041009940301c01c003520b44160500c503030320804000420001d9106c890300b41c0e1200c9154070400a011081e40402641c0c2020350f4120443d85040c03006109002c0180311868000f9011619031080314800003810041c001c0502c00d100b030b182c1e500c07185070080c004d83c1d9441484048001308119a2441d0040384a105184808078813410051085810600e41c1400f0910540013610342140c207000c041d03a6000c11803c2c25004051440c860340c28003501c1d05000c002c1010b030600c03501c80c800c04100c0117401d5480d50004040300548070308010000100700080301e80850b4080d0600c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 169491960 1250 169490710 169490759
    0x9080c0d080a0201090215090414150d0224031015020a0201030f090b09100b010504050a050f0d060912030c020312040308130b1f0512070e04020f2e09 66
    0x101044842a4010b00001801942044a18030180d040e0087d1000034946408202c0c3c0801103c200e642c0500c0390404215000081d0003051942081186840c04480d100b0f5403001345089068404c40b042d18404000050150030100070100502007220740c00c40280c4080d001440400b41c80c10003024000396101142c00f006418142d480020410b010a40d03000200d071103400c82407c00c5a13040040600307a90315680403051451a00e803a20042c25584100c085404030751006220210450a003c00c000d001d00705408001d61001e220b07104400050924000c10791900c5c0188074200041c02c048802809403551155a841103400801194601c41280b11816801039098a0031500540d25071840011032941c850b0040c06c100c0094042108050358500c0321310340c005001112008031540e600902c02401420050600c00350090f4100b806000820209135601c140000c04e1051000d80950224903403400c141d0030403d2600c1024001030203d2a0303243c500c0c42c501800c1ca4400c00715031500c89102c03c00302e505003145102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 169493210 1250 169491960 169491967
    0x21b0103020d14040f021207031a280614091e0606040504240605030603060403110a080415080601050c07050904110907020d0207050108011401030203040c0308040b090109080c0d08 79
    0x1160002c0e071200d03d151005640300866810710303061400b07001101c0b5004a04c100900784142c1c60024010809000320b981c41041306220305041465015030301001403a401200100d410203549a600d00404a1848109c03d000010a281450309410f02e0b603e192034207501514050060014821444000044c0b01c204041c5500b01038480e000010080d00c01c5900480d4000e0802440c030840c0d140000c400001d4216a8103240031542d42c449090342c0fa800112212135241d046800020003085c040c0c624030300d1849840003074480404003662010810b42042e000490041e2424510001d4590040c071103580200b02401d0190a00745109522580c9400d00d000d61401a07101c4000f140c01c1109101043c82200c100402e041054540394800a60710001064000300500c90700000050030b500406056040e12039241030701c90303000341c0b180c0123501035030014104499412110300000007286d100400742000e09180480c071560382c004d0100040c881c0425402045a035001640303900f109940b045403507400c5691010130641c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 169494460 1250 169493210 169493227
    0x4090f060302060a0e0f03060417030a06050a03080a02010b010903051c021203040602032e0302010f110f070501020d030e0d080c12010603050601080901020304112404090605040c021b010302 83
    0xc0d010940c0001e400c0741002c9095582c058004444000c0c0d42d00130b440040d92240e1210405585032001e89000d010800d90300030180c1030403070071401103500070003200d00460361a6030386021401a2416910548520b600840c0710291580e0a000c3c400400d20240703060341d10103042d500c500707444480c01040074081c00080100842098001d2095050f01e0801c00e0074240c0303e242034180040070b5802220800b403403d08650540d140810004501c1030700040701c41d410420301c2c0c20341c0e00544540710b455401800340080d10138058015002040840000d90024002d880c3e00781c90500064500741400c040c803030505040c1000d0300c8070380304001001145424545005402600c1324103600620f44542465006501000740c0003280c0c0c43d40541010740079800a0762505415541c02508600301c2c001600c00606011013200d00c15401e181408a0b00d000c6d807001c175002c0034681c148140480341940558085200c44da2210390401c0f90303103440e106000342107542d80042c01600c25501604038404022072122411f044d4007261030b42 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 169495710 1250 169494460 169494491
    0x180610060f03061e050f010914190e10050f0d05100b0105041d010e0c0c0a0f080c0a050109020307050402040e01090e070909110f040209030703030c060219080403090b0306060409 78
    0x500034094110a1100794080702001108081c00d40031701805001402110300b525441400320008940c030004035421854118010814a001e0b07103a0900703c409400079020515005489045003d403440b0500c0d41581440d103801d100d848074a03a000d0380e1040415030440c1e03011500106030004c0141c019100000c64201c6503006844034081c42d001801001d0f4420011047e003c030740884241039801104008007103036901090301c40329208500c050141600030711030b10b000140c0000403c040382031207141000e04103207000321898540000604240e406a44070b85885096040920008014050541c0e00f903191600701001140c1196043c4a54190341d0303504c8444050000c818003441c2c3c05420a042e051000303d04500740845407100507203c151169000c4405140f0034585442100d003025409005046c04524540b003d4940c03c61400c415a1426005c001d501150880401c4000703440203e603c540c255802c10b0309005080340341607008000360f800300b0402d009469451900b600c0442d41c50400c0440c0272001c40c108103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 169496960 1250 169495710 169495721
    0x50603070f26011b050c120c0a020f040b0a0e090a0b04030e13090b0c0a03090b0103050321010e06060309100c08073510030b010e180610060f03 63
    0x840d80040c0320034040303501c04111a07803260442c44884040090b20300c42d03108600725926443c214800b6018012a080c0840c0144003600c41800413400b074034404102560106417030340c8042c010121740c0d001940c0710b03000c615043e0400079840714296410000703803081c0408034114a4003402800e0024401030700144201d0300030800d8085c1650300100301070480c1032a15000d800804406101da00c680e4220301c0c44581e070400c0c4e1155109490700403036040e00d203072501001035040d6802070101108060322806a1004582d50011481c000c5126900a55403540d44e41a407407030100c02000c0780401c181206d801040030310b5003065280e41060303089410300d90301e1311681541850304024820030081a8208006980c8582d0030060452240c0415210403510715402512035815400e900e0310f98000040700c1c102c40403c61040f10710346620004e03080100e880982c5036243d280784030a0907808610155039510401030341803202c3d6140c54990102000801c4a8209000d80780c41101c954080c0c402008042d04034007510600c40d4004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 169498210 1250 169496960 169496969
    0x6021f05040206280318050d0f020f03041806120809060901031806090c050d0c09020706020f03011203180b0a0c02060922050108120a18030c060c050f0304050d020405060307 76
    0x220710006052000c001c1104018001130082440c00e48840b0b0402c83e045194003c1d540d03c41c0240c80e51400c075000c03e94041c00c8030b030342c80c00c00c40c40b603020040f803900e10420050001d4141816459030011510090070140e6269401c0054248a90b414040001d1b0243d0b00361090b105c4112401a00ca0700d200700101e005203910030501c025101044e02110501c00e8680c003440409004003000491551a0000e01100e039050650003000d003480002c0c10400003400d03502030422144152405883c1c00f07000080e8100a400a0300200000c503001c0700c050302019000001e01e04a9a01c091510f1120341c9804543c1907140181c116400500001d151060119078a01003284c070f103034030010305180130056224501880c20b034260281e0070712645400d0001c5203461000408528805070700160340c0c07602c0c056100455203070400e03010504000c9040031012000404c1c51001e03a02802030380c1e503405441a100d045c180d00c0c198500001c049d064008100521254540d1408095801c5d0151004a0f0b151159408a480d1030280d601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 169499460 1250 169498210 169498237
    0x9062503030c02010213120c05040903080109050106020d0503040303020310030212071a0c0606100309050d080a0b040507020706112d071a1215030d021606021f05040206 74
    0x206a68a04005140542050296408120441c5942c00c1a401c034800c0e8100540c0d15104480c04012864179140c40036003080c421944081000c1d605c3c408581a00e00c03500c0300f14081a410401804203000d070740308950041500e40f004260158009030003400a220142015007055000400286042503071040100211360182038110641c04000200e03855828600404843c8540c50366200040c03d6950241e40c210590107001d00402c2d00c0b4242003000011b2a0341038801416102e0600e41c021940600080e03d101d1040c0c0c0352250186000001c4408035050107039568070440c034141c2403101680d400541d80c4196441e03802e01c01d81d0303c0144a42a45000314028200b00c0e0380620310814421000745281c9000c000c0300c07010031144076688491380c02032229003030300c03a90000500c00d228405101c01c03100035079a0402c1811441c60015001030011a00b02051491140c0c0564426005500c9411404049030010240e92028142d08600c8111040c02e846020080034040e035250700218042d035803948201d80d00c482c0c840c074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 169500710 1250 169499460 169499497
    0x130803091608031e07021305190501140a0801020c061605070c0f030209010e04080304060b120d0801031506060507080a1b11030118050a030807030b030304090509060a0903020703080906 81
    0x4001559940c0a00031103007081c0314031381c0881c104d0003940c003c0d507924550050217000502924940c500081000a00c289104c00443d90256a10a15440313014081e0448210451b0700f080260140107024085901210b840c4c0c2c0304120b180d0180402065150300484044142040c0c44e007011000c40c0c09004000300604409800340000410050030015070080780d100b41c5401c00c6980e0b80d11756039510745800301e401811000d01000013a00180d81a1702c062072900b001005000f4000e4040002442e291000d99003c000c90b03002ca0040c414002c0390825403c1c08504180e05000c190b0803c54010628082c5440c02030481c0c401051805505005184482914040d032501c005001000c1c14003151407000510880d000354a0b114280d40d10803030f01d03200001c035075030880014400c050851798102c40f400d0004040000301039648145c800c1d40d503400c0c00203000500742e041000c10b20303081114000e400d02801500d010700061401c4240000039802096610460741c100405036180d60001d8041100d620030741d24660a04040003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 169501960 1250 169500710 169500719
    0x9070503010204060201020c0c03070e0c07020a120f03080f0615030a0e060c0409060602010507051b010b0306010b13150f0c05030d06150314040b0115030902060a050703171308030916 80
    0x1540a0010140740d81d085070309e004a0302040c552603240e0f902450a007071102e100000c624509100090103901c0c809801360000a540e1080000d8442038094100e41c09206102030300c013450782c0096090b0704040004080e04050030040d0001d80b8100048490103150000440010310308407265101807103200402c0c0c00c1e604185130440b40d84100da4018052902c3e190701d003036000b0510310302c144607040c8600c010740c4400d880c040080c0c0c0c41281550b00c060022803150340b9050450040e40302480107038020014082244d894081010344402c2c580c8507908015000000e851001240d0350f8401801100401c450405041c0307203840e824072504503c1407441074a036050429034001540803002030a40c1d8411610740c0e0030429100d80e0058160414400d82e00034040c424000018004031080135181041d00070b0360b050004e04503915a0118415402c011002d401107007000c50078001f80368200900c00c400001c581080b00d45460300c407030100600039002c0c0029010410100000d060b240782084402040c201e4143c4050980d640c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 169503210 1250 169501960 169501963
    0x5030d23030a09050d051206090c0705070602100f0e030405100c050d020705011e140c030c16030615060816031112090c0604060c060c090b07060221061305090705030102040602 77
    0x1d400c021500c03171241c00b10300b12120340300f807003681e41c070b4103078281a5107443c0c0341c400402a400700b001e000080042820003403a000110100000c0005041c1a00a0710111480c1075a040031942d004801e0b0100703506150100603148000710444041c3c9604403585403001418403002c0b10201c6850b00c0003401803040d00c0d160040c2d0707900010031000b103070001d981c2d2161030502a240d5000c1c00251041d040082030900e00c12201000c6031030054050b159828084905000d401f0300d469141450105078240741d02031042082c004c0c00321a01848641d58140100d075119030b4a4003000400c90940140410400706801c091046900e100c0c1e00301d042429000c19010340c17203629512101800c400d065500c3c10003881201d41701a40b070300342141500c0c01c5560507250040083c0044d121007006c0d01c401e4240a08005e04a540400c003800b100d005054075501808005803602007400c07a103030030804130008041c0a011040c007084103568034441143e0001d0007094000c6000d8485d2080d00f842c2540c0d540120783d055001280c0402c0c1301b0790 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 169504460 1250 169503210 169503221
    0x3060504060b190515070308070818150109110408072108040b0c010c021c0825020a03090603091709130f0b0a05060a050a11160f081605030d23030a 65
    0xc04452045d110038500d40d0700f8102e03100700000100820601400142c8090140f10219407044803404101e1400c1d102c103100c282050702082410140d80007140c014000c00220740b058964a901100c441450309040695440c0c0d562098420201401080c194513081c210b072038001600655400710300b140d212500c40034514840c0c1c00140f40b51a4941ca0100c454401500c0080d050280032500700c056420b40ca4011030850700705000800388290300303c448481c1c1c0c40d40b520b100007a5250743c545174054000c07111039107001403480a00350700507005c150824580788041400b1001400214140340c03035880da0b505940c40400c400c80c51181c01030460518110015401c216a40c0119540b014101d40c000a09a03d0300208122809210007440009900b03100d413140a40c000c0d04031050745041c2c102112464210185a007120b034074030303400c102081074072610104034a480c100600c501c00100c840720110349504000100f80d940754442118800c1090b607920721005001654240030381800c0c07a862040c0c1e030746000e5865101820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 169505710 1250 169504460 169504469
    0x303050a0b0f06090103020c0714100e03030d0b040e0a1103070605120628030f0b06010804030c03051305130207020111190b0c090301050709080105060f0a03060504060b19 75
    0x24180000a115000c15200700c00c50014000c0c080306020749000c05010752034002e5103100781490b6081001e01c030718503020020400185415040d05004800580910411440911003a01480680c10340c07101c0c40e6901000b13480100e1520000041d20b080e401d0009800741c81841c1400f041c2e40205048201400a50240c414505105500702c68480c0d03a150802c665510680002e035010b240008040380e80c0c1d290142044000d9082c2e0080d9400071504480f185440c0c030002c0c0d10484140344402c045000700900814100ea1040013400c0c283c10500e03003900c002d40010b02418000302000f100140718100000c55100501c06020301134048000710494442a00080d44104800e178081000e0766262104460300050644401c51004c0003001d440040e40e8071041c8414002e0040a0244014000701c1700640302403083d544240c0c1d680d0f4401e54070074545105142141c901804060041c20042a00c55882c0c403040a28802c60364421000106aa51814064001c0034128815584200d0f00f0f441d11910b152801c41000c10746 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 169506960 1250 169505710 169505717
    0x1120c0e04060b0a05030f062e030c171b040f120c090c1b06020721090b09030a15090203250914042a080a0b0109020304110d03032703 59
    0x142e280c0e490f602950103248640c0c40080c10400c00103581c0d9140c41722080c1c001c1030280035407001c1c01000340902c0480d140704102d031a50302054280840d02d5640b5000e5118507100070309214040d40c1d6a0002800c8042c002448191103000c280318100d601803c40085138020b0422980000c5000d84811040801e00040c407010790344106028004942e8070181e2040e81c0a080203903c6800155181d01080c46c3e0f00030102200340d80c0541c0c01e10030280418104590201d9180c4128800b45403407414801c041c040b11065002014901400e000b441182e440008044440c250042c0b1103680100003268280040c10811000030741502409031081c074070082022100844d01d03200d0003100802c07a103400e031200454040da0a000c1c807a0000002140c08074003c0401e8941014001c25801d07401d5040c0d50494480224541c84490075500c0940f0140a00258800c440d0242a5030041549141000d4484449050800c05d07102d00c182d8810020408050003584000368800c441c030500920040b0b039a40805108505090aa020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 169508210 1250 169506960 169506971
    0xe010c17150924100f030f1503150605060d060e1b0315030703020d0b040b07031505060315120c0a080307050706031805100b12010b010c0602090a0e0901050405010b0105070314070201120c0e04 84
    0x81045004000c4590408c0045507021465500d540740b49042051881d0400b681e91030001c94070352030300c1004201c0b80000000200310035260280c6840c0c55400205483c6031500034051062060320b000044030741040040c00300f00e62400300e1000107400d05005a0009521101c02c0052608010071600d80343d1246001d030400b0403050746c0c0c15000340c09481c1c0d41d1a052000c0d030030aa80501452401502564000e0041e0007102c1143d4a08804600c810724000104811a0b02401064589107090003620000d050114083c40c203210b42562815030300c3d207982c042d003001d0585880420f50140c41c0212084011a0044110b03108610002c46040007441599000f5000300c0712901e19130740160f014028003180450682d11b2400741043c90711104000c3d08652007259206595650015076a41140300360760007200608000502c2d4181840c0c29800c480e01c40070100e040c050103100000c0400e401c4107117594008904100c0e940e80301da0034401204c81c08010b207000790100c1e2408242074189944030b40024008007040c7c0d0108403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 169509460 1250 169508210 169508231
    0x10e060108070803030412030f05190b040b0f091e0406020d15050907030e0705030a030e0f0414010306180c1502100203010b04090e010e010c17150924100f03 69
    0x119020b2a0150b003659a00400c04280001e48203018480004401d00c0e0000c0c0d1b44500e54031100650b0b0054904d40089000c844036050485901c0c0708000b0a03180898007086043c3d4070340041541c0139003005150307100d10785000010b401a250041b40040c0e03c0703a10641c83d02c192801d440c1240c000d401c2070b441507141da0b10700240340e034000900060181c00d0f540004c0050485030360340001100070f0404691021118025040c00080700d40701001440f400074440c2d210000d1000c6000180704000c1020700c01d2902ca5400e0a060241c01c0100f01d84050540e038000e0404038100381e620602100818014400420041d04040c00060f40541c81d440700c03045810580c29550341c601400018001c2e40801c2c0900c2c090040100010041910340d8ae00070000c0741046000820320b00500c4d242c150840b4070441ca03440126006032400aa52071046a8241d4002005101c800401e40c0c0302020030712452000b05034102904a2800c9e02403214000480340c248088010041c40d2400e8400340000ccc170384191031b150f1401007410b0141d01407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 169510710 1250 169509460 169509463
    0x110a0203030714011802210a1b06020f0c011b1e1401050603060603100c0c02041103060307060207031703040305090405090309150c0a080a090803040f140405100522020c010e060108 79
    0x85c000341c0c00030400e11140c080030342004880c15602030300c0030701e610545a149001504044a1000c020140400c00800500c0e000010341032640111075018503420008500f500381c0c0c0c010a0b088205246400303110580c01c0300e4039040303801652009070b40e5408954208604208a00760210141d00c5541d40c00921158464100341a42c503001510603683c180c110300a80401955a40d0140b41e403601240791180040c8980d4000c94102c4140c6102018002800030402070075080400c106c0340184035a2008045040c80d6417541d001e15007038140240c40c0b980002020405252103078081d07030a1b0b901c00410400ca1414190400d640c0c980c42884100c0c050001c20400b4040c240e00802640c0c5084004e0016004c50780003540d880b2203d0b4800f04600c41030240301c1d035010841c500700304058406000c0f08a070001c44681441380d1041c007030b401c1d00c950500c40c90030f003001c02c001c0c0c0720604000c070304442c003d444e002c0340d5904c1030068140320400d0001d54500d0a1004c21101081001500801c590342d20030419282940d80b00e2140b01e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 169511960 1250 169510710 169510751
    0x120c1c08070c110312030a02040e1b040e0a0f1806050109020f040905060d0c1d0c1801031a0402070305130b040305030f0c0304032310050603070501110a020303071401 73
    0x52010414100380d45003c0b82c02421402d041181c01070a0310756130080e0602d803d18a410a4805504031540410701b401458001c0301800e8010241c2c0004286412040c1c0d2002000d00c40c50203001001122440031a0f0b041e209608041030081c0a40d005005041901c0294102e603e280b000c195030302070030076000168485041c401c40b44c2581002e1003841c030f810b0900c0c0d20342d4082d000281ca100d40004000000c14041001c2c009010094007440d0b84a80f405000c40144003880388010302000c0030780c03c040107a450007006103e80303a50304d010b080c00c0100e80017040d410580030202180c4080b5801138000178442e400c142c1d101c001400921840c0b003c2c0c040c01c3c4c1d199200c26902d801180001015030f4010001340e440303100aa00542001ca90b090200c9140c00d4907581c4010100f05503a40c2d1320000710030a45076800451043c45039040e00000960200060310744040000e5542c8000d2183d6811301102074204032000b0307018401404295000b400b266a00c07104c624080c41c008047c805800c0c1c10b54600b2000500d5500c1c1c1040d035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 169513210 1250 169511960 169511971
    0x1020705010c020f040e0f060601181202030c040c02030a0212070f1b0902040b040302010f0305070219030314070c021f020706030e0a0b010611100b061209120c1c08 72
    0x60404904040066400100c51641070340d02259501d4440d01c00c0d134580c09002c01d01c0304030001038884280c00b1400c4500d03102e40070740142d0600c61041594203031420304121038412a942039142c07143c4040e040c0017080c1401c14500016410500b0307e081041c40d1a0000b0050070312030b1450313003107982c26003950903000348030301036005e00812a400c908004400700c0c2c2d0b0b0490704200192400e80540301255101c0c9900d080741e1142d0b000180404010600f00299a0800c10302100418030341030501040ca0000320081d201e80c10500740c0e01c4001204014001414425485001035908248034a00d2a08001401030034251074500b00700d00c00d004000165030309040070751200d8800406034008116003800c06906030040e243c0701e54210014880d8600900104d402c00c000c0c94000c00507501c0300c400300007030070041a082c0340700221508241030170801c0010954035884200c1c0c9100301415040c07641e60b04d50700e9595041101c50614145619800320b911301e180039000c1440c140c2c0011086030703159152810401560a884203c88 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 169514460 1250 169513210 169513213
    0xc03060c0f03060a15080a050c09030a02120309030313170a050d05070f0b0a0c030b060c0703150b03060108070906090e06061011011d0706020604020904030509011808060a0501060302090102 83
    0x401c0c250310501001840c0c220720020070510190ba21403a0200c0490030300406040040c1008091103800503032840740a81140c000e0400c035140801d11404a0381c0d640601c04028011209614181e84610060094504024000782a2903481c00341200340e10302d059180c010100036040018010319000000a0082e80d0158000e010345610080c144094405401a1a042d1b03428030301c401e14680082c404030100c0c0d02c140c0003850001169100d14000a04480c1c409e1007180c081c50003081034200044000407111700720307544907030000c4014a40300e5144001e08411041290140f040304008030381580040303210000c1d82c1d202c407410410b1960b9032105a0a80d070981e0305a0040741c001a011078000d090100b008000842e041c1400098201403085203070031122401d8002806c44080903440307128800c01e2103c08020085403000f0321250400e034000807423040c8041c0c4010700748600011071007110b134040d00d200100b0450920344000c02c03c0c2e48075091512a5800c84000b0300c058940000490b940e4000d1095446801060f030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 169515710 1250 169514460 169514467
    0xa0906170307030219080409060314010c091a180901080d02010b03010218010c0303151e050d0503040e13050a06020705100507080a2703110d030902090f2211030c03060c 74
    0x2031006a0301110881990348800801000c260713490a40240b2740114403485042c407040319a0468030b030856040614220400001c0f802c1006101c40c1414241105200004071703996991074040410345181480c045a5044001400001014800400c502c000000c1c580c009001c02040b01d030070103080b442108400255018041d51480455115251100e240c0b4401d0070002032820020308040058020baa00c40c2d41003c0000301d04ae40020940c50810000702011f450b8039002224a5403610340301e00407070181e035070325a1030b40e40042c0c568990307100154140d1340c000060b141d0b05d05840c2428006544180e005441c14400d80c8060301c0008003522800c0d02c03501c0c09945410454030703000c40f26030182000c1c000b0030540410300c20105c030b508000b030003611442ca0b20030b445080314100b20b050880e040c581da0070182030905240c880c0380000b5891b000050f5510030482d01002405655207018000402200352042000654156031402009080c5250500003c0e04500701c40c0c4020a071010140e9414007101c03401d20144c810b2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 169516960 1250 169515710 169515733
    0x90e0c0306061201030606050109050a1a0c07150c03090b090a0302090601050c1510081c032d0b03060c1e03040c050306090604150e031c02090a09061703070302 70
    0x1602468201a0062059150802c0c020480032a000300781c1050700c02c0340d65604104134030f681100c2100010041980c428034040e140510040600b048801d95080380d110025524076081424071085001d440c041003214840b84800c8002000900e4045048001ca0481c1c5c41c089144a4410192400321000030b020880f581c0c250350074000e844a0107041e841c18030509001d440030b0414103100e00390b0440c40460440b4417610301500c13241c002000c190300417841508400f0002c0340016001094994000c0241000309804c00012240d03d00c400041c181c0300c0403000f001ca000308102201d03800240d5512411012603205031992000b501542c40380e030038a10112100145625000d0718040c01442d0310500514134890b08a81d210046814110201c6ea94113843d00010100005c00a9100d0210014109800c08010b02d2003d202000d6580c807c190701d40744001801601c076507542c68280c040362010b040c06015600c1c1155644004005001c0c14014216904a00c0343c00202c600400419141c40f50b03007650080c62518030ba03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 169518210 1250 169516960 169516981
    0x7110114090d1212020d1410080a0305070201050f0307050c0111031003060e0106050607081201150c0803040c08010234110603040f05160305010c021c050d0603051b010906090e 77
    0x10f101403c061054040000341480d109201910f442c2e40007400100e42c141104500c002c0002008112100007129003509010389030700010707030f40307a82a4035061443d5502c1c1c883c00180c07081e0240c1c0b0040388140000208101c0201d80c0b00002c1c00c510001480207100520300e900c00015a40800c42e5101108080220200040355042e04840000c00020b070002032002d480b4408200180e12210f400d81c1c0055001031001d0b00544429003a44c010211150301600340254444000d040072041030003c1c0c424140400844d0510401581c0c0000400f4681d000315600d41c0c80e003640412412908100d1074101707441c1424154a280c02c1e907110b08501d580501c01403141040c0c1d0f0200009900090301c161007180800d40c07110300141040102d14039207681102c1c0b980015103149003060944204204000c2150420042801d000a030706034044503051582c2400e0b41c03101c3c00080820000c0c141c0760300140c400d100381364000815210540700103d8200742030342d451300210f44070784040da45a012407081e81c038881e1403100000c030f28030315 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 169519460 1250 169518210 169518233
    0x4030e060d0905030403060c18080706050c011803080709060e090103080a02030c0105040615140d06050601030b211515090c07230105060d0201020a02040b030a0807110114090d 77
    0x7510000190400440c0c8a040c036542040e041103030000e680780c118100540d04100407080c00300d00d41c1d01480f00c09003450505a140d0881c2c3c130900051100200e00c41d440902c00303400035075440886428090800e00d807428020185a400d072000c8021802820011030030501c100c41050403850098074186007a4a59920000300d0ba006858810071800184100c40000c2400e00a1a006038025603000c5100c40b0b00040400c58088140e0100c101003903800c02c0504141c650100c1c880c0c07003a40240b00054a6030390400142c001d8810f801030300d5400701c940c105451441d101641c02c28041ca40e50011195203610704010705040401c02d443c06050601a821412124604106810f40c0460f000800ba03041c040070340d503035440d004a003041c8041c030350741c001c40700441441091107070b698000011240d419514500c1e4002075210091000064051a05c518000c40d00e91410003114001c25444840180d0302c90260503c1c040019000d02024001170031a1010541d40d10500262124600c00801d01d0409010580d5203950600 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 169520710 1250 169519460 169519477
    0xd08070303050402420f040f080d08090606220204121406282705010e06062103070503030f0414120d1e0c050a1404240e091305100504030e06 62
    0x9004000b0440e191210f8001f800080500c6c98044407698144400030f0305002c0c500110408010507201002241d810000b4119003080c010390b031001500c5c4860551265a1a026000709101c0d400024001100f04194952444c80b60045942c0c40c0c2c0b4111501810f501d510b82544c498101c0750056122911900c0c4c040e400c607112640f0108000f408a900d400840e11078608002d00d40c3c041c0a4100302c1200b400710030700031012100c00100181256280c02c400140882400c49102070003221035003050302c01442c0401c1202c03121900102140d840f407802038003401c2404012203040701c3c510008840380000b5030000581c45140f9985010450034000e0a0760707004010400b2194042c00750800305041d02001c44548105c42110b40c807581c90960318041c2c0c0b000a00f00c0c208001d0b60001c558401c00003000300080b180d64075008c0d41825042c598086c0c4604200721240d04001c484c15038020f50380b00500064050f00051000d51601c074800743c40705208050340308011501c0132200030b4041507103522a0300311858410020501c24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 169521960 1250 169520710 169520839
    0x3120a1103041e0801050a110a0f02010609020f0c15060f0105030a0b191d010f060c02031005150a0803121609180b01020105010f0f12020d08070303050402 68
    0x340d920300040314100084903024500e80300d9041c3c244088202805155841010070500b4404664196411500c502c1079110b80390070030041d55403024440e0320030f4020700014040500c0a5445a0856000030302940c00702c1c1d422035280c03051581240208100d640c40d60b02c2104000c055080307040b0504010b6425920007010226200e98038104000280d0302c0c1042040c1c0040900c1d0070401c1079051000350300311072007040c9408140c1d18203000104008800e07403480c0d809032071545c074005059440343c0c404a4504a000a0383d0240941400100f080c50750040c1c0c51240b0103003044502845207641c400316613440788500c050384035082103605c0004120800f9159010451000f62408404180d41c40b00d00c1d08205546005042100d0385038901c1100ca9a42402124050700c0684101040603242c521581c0c000183e42c03107800b0200d2070030f050000940d510415010340072030300300d04055a83c41135498000c1c002d14040f18101c0c400c0d041c100c00d2410350100a101c2c0c1203602404195003511400c19824005614840515180312 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 169523210 1250 169521960 169521967
    0xd020a080f0f0c0105040507080f1f0b09010603020c0d090501051801110a03050c070b030f0f071e051c051b07150c080106111b0609011215031103120a1103 68
    0x1c203454030000c0401c0f6450200006503414646000c0341000c0c01a4402d030f09171340c0014032186007400041882c2d807401c0051030030700e501304840b031501d10007070a62106460380c8003024000004407146c054004058424039081070b1214000b41d00b4003030300c00c008030b40030b65800203c0a100c800350300d1600445425803103074141007001e540d42e451481145862130b40b81040300042c0c0003148940701d0f050f00b0071004004d4503201e540b240c11071806c0c2c8260301480310028240c0070200301e6078020481250164640b0001703546240341c9950612180c007006050381d40104101002d42d0800702180607440f01c503220702d40c05480440108003000350300000c2c2120540010030141c400c0094413144d401c05d52810320810380c0f01442034462030340c1989486c0024000700340340215400039402403292071131100f441080c80905000c00300c0d0300684403810a40100d441c15440202c0416181ca0310502c24064078030140900103c03842960300c000d01c00d00c0c5205043c2c8611294011030200c10003440034100c2180501010741d00301014004176800d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 169524460 1250 169523210 169523227
    0x316140f07020a0504271109160206070212180105090a0806010609090b1f02032b0c030e060f070c06050703091403070f1403040e090c03010c020d020a080f 68
    0x5039000c2420300062a80c00901c401c214103200c81c2160007460b080390700f0010750403128154810250004880c038100310150b1224401c001001c01000015003000d0156460303480d0807a680d44003080810181e102611540c000030741c0c41351001a40c0c04542d8407403249541071000c0340580c91009001c014410341480700c280540c507480e40b14002140000e0002c1e90003001310354034102e0042d0003014542c0149600030304010194101d52102c00e040b502d00344a5040c2000016083c9100300d06501401b80d011000440300e1005032650316000641210040100d00308010154913084240c2c120740710080190469008440001c0266004110f1a54000d485003403a0b01c0320172142c0d0303801084580032608c11340030a0765800400c0521a00700b071114015242400158940b42054942c0c444110755400001c02c100c00d1003030021461001481550700400078121034840d035084c6026501d48480070b41004078025880e00060b52007007807001428000e907800030f170080d10180700c0c49c4c0c075200c03295031040001c480b8541c8101305808 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 169525710 1250 169524460 169524497
    0x907090e10050a090201110604080403020d020d06020307030501030201030c0903170f04170604050c04110306040c03150806041a0c040605031314030306010801230108100e0c0703020d05040b0316 85
    0x20f00c103024800c000201c0003902d200141c05100d00a034010000d078072490412000440c090111030586e50101d89403a44441a4400035040d90b41c41c040c0242054008814403000355016000581603d200341c0f814040020f0405040350a8140e80c400503041034801d00110800d025100004c140f11308000700480d00d41a10780712100b488030800020442c10340d10000c208000e101080c0200c40583d14111000e12001c88030101d1b01b10140130241106100303c0c1e4a089144210340a603209441443d60314900d40085980c81d0f1030142c44c0c7c10125002d4031107031280041101402480e03204244118400c810060a003070800900700e4030b42c0c000400c201c5007070341c420800c2004629246500d4064504200065959103003d41c00104401c0060384206204d90507040c0b204115029164140103da00038a8940201e59a401314801d880b0419406680c0506900f0248291046403000912103c3d02a408075001c1c80f5001703d044400340b00700c0c4074581e041c044c20f001054548070107025000d283d0010340343c10b0820154180904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 169526960 1250 169525710 169525721
    0x5070305030f040f0504020a0c060209042a0905090708040b2a041401030605010905100909020a02030a170702070e1e0a0c0905030309060703080c0c030706050a0e01050907090e10 78
    0x100c41d0b0381030100b003c010541c1008040c40150009450a60a001d02d24a014144003141c400042160f038000c03401212a496a900031000285458501d50001c4080e103280c60481403040b008000203980a640800c05050054541d40034910681c1c03406413a54854541e0001468090000c0100b2002d43c1c9900124403202c203c03d00c80b00d101d11100b6a91140743c2840c002d620131000c0f130a24103141c10480f04100c103a030030a06070340490f0030982c5d000300d0194081d44c0c229020f000c0b0b6080b03c7c100c0c52000c10107103501a8000007030720501446440e07010021884844510b0b03420001c541c9240103174080c40062001d000301a00d483e0308001400101004c0500c0ca0000c2c151000c0c3c12142e1081c001c0d99402d40b4245250300070500300081c00158003562602a1420110b82944501a00a41070011490200741315802c0142101d0301c10a00c4021f4a0300ea4542c0c0c5085070182c0010764164840a050400f42c1d0420041031198038058186034009100300761501c0180000307010280e80c80003440c014142c1e20085088031307020b135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 169528210 1250 169526960 169526977
    0x3080405060c0a0f110a120512090111010e0a020f091b070807020931050616020c0612010302040501050604180b040204091d01110a080712090f150507140f070507030503 74
    0x4410488910b01d09028503400c1c5503100405d194000e01f009400300780003042101c800b541c0c0540299880000c10016503204803500951400740d844c210354201000c40c0860390161041c800c4a1a041c115110403c000c0440002e4441d64240c9004442c0c0701c00084070500241441e80c40340d2003941c204803c40c0c00050202d14210740706e012140801d01c11080c084120310615168880c1001d001013580000c1e1181071303486100800c5206c0200644031280e42c0103000300203000c0002d0008101540c0c40d1282e13200e05030411000c1c8412800fa5040800208951810700261400d8944151858215203445100d0001500b6051301c0706800903406c00c030100e80300402d4010001540000c80181d40703046040c5598508540b4140047c00d040c50301846282241c0303522020054002403145861081e00b040b11817500010088000c0040c021034804c00508100001050301112803050352004000341e0f52050400d454004400384c0b05181c0c10400c0010705502d050007805060b9031409041140c03611601e0ba510f091956121061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 169529460 1250 169528210 169528223
    0x40e0303090708060c1204050a0203120a02010b060414010c020d060c02011a0406050916021c08010302030c0103060e0a11040302090103050109150e030301030b0c090907260103080405060c0a0f 84
    0x2002401c003400c00c100e03402407561a00901c0986010021071949000380c0b40101c18150712a8003050501100708103141300e541e0014140c6d5503111400105251560152000001550802c06000018078202041d181224081801e90344040e09034401103607041d00b0707408101e9101480a80720301c00306190784140c0c242c450b2a17030000906004400004c50521414041c60b82c0703d5402c001e402c0c040e5445e00b90300b443d0400d043c0704101c443c5208100042c0c0c1041c009105e50004034030303c021900e0819910640141c1201e009034292010a06035000450a458150040110044140d00491080d00856101e24091700b0355a56a82c1080d0f00c9500050302880c0a80c82558179079140c90003901071040c2d5201104402d907013004c0402c49a40131242440d02d900051001508070b403040f800048000d00d13454211000d004008040036118644424081c1c01c10700c0c0d00c08001d000000040300c180130400c030355580a051340c1e0444201f42c2030902d460108804c0e94026800d0500c2d82c000c13491420006401440058100c0b4410b66 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 169530710 1250 169529460 169529467
    0x1805010b0418150e03070f03020705010e040c0815030705030703151404120c06020409150303080106020c06070807050c031605040b100804030e031e01020c01051b0d0506040902040e03 80
    0x10002541c160036585014640382c1140280003030451080a61510300e180c0340480c003400c0c55100e190450040001c00741404003134088640800d035001c035103c1e0559a00341c0300c11280904442c140000c444144100a000c41d809102040c0002004413080003d100c0040032070b03a4a03a100c070003081c00d00c54281d10480e020480b0001c003550071841805404040203403810800703194641034513940140f0300800c461030180240140c0030030501100350110b6015100701030061001c0e076600364182600400c184000c0d400185600c00201d00c0390710105101002140c0205020300f0700c1025201c400c070550008008907094441c0444121050720305020302c0d5681c40d8020000b01e2181e00c1c0000b84070949002c802c859124120600c2c2107941190421005a04941c0520306200117085490201c1c1c0b03024030590511501c41c0008054106014054005110441c805002030140343c5444071030283c16524000740e61107050080c04408406c40c103a0380090351044000700b01081010b13050700400d048800e4408105920740002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 169531960 1250 169530710 169530731
    0x30f03060a0602010c021513020405010303020c0f030d021b0a0f0f090b0d032109020a140f15070803040302070504060b0703110a0803011404020405060c030307020d1e1101180501 78
    0x100080700500c1c0c1c0d40000d11583c1c0320108000d440e07500b21404403080300043e001165940460a900041c050341c007500402c41d41d6102d042c00396681d8040d804892040b0310006030389180341000700d0035042890072a0000c01c1d42c0002061840003121f181c846481e0841100d4500140c20106181c4001c010075407501000d9481e03090401e00070076200c0c20003005000303040780c9000038002584070380e181025010014005602c8483c0354111005003200c0d12010758042d95059010441c90402d0b2802c0f20350302c0f411200c00c140e1100031002c0c000300f54109030484801600601014010850340f10085034001e01ca0300c151100c250703d4038005403c1300c0e12a002856880c8000c40c1c0e00c070405406c0009013042003400c4004103007410480c0d07a00c0017280b1050140444840302c01018800a440d1501a03c0180800400541c0c4804c41e0004c4c251756600101c501400510915000212060041c0342a03444810070428961104803003035402e0720320444190b11030980d50b40e5140a8495000c4148150031000d200d10300215050700304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 169533210 1250 169531960 169531969
    0x181a07050106030b010f0803120c0705030d090803180a080405040207021f0806100201050f06012a060b0f0a06020309010305061c0506010e0703110712022104050a06050715050402060c030f0306 84
    0x1550005074182d0f00400c1030f040c4a071002c47c0f07450b0313200800e4400329607940d51900d042d37429070007040c00103c040307400c01d01094104144000610b00c118010700195140038421814203075180b44540d009440c01c18100002e004600700f0750000e0400a00145c14054903040c2e000c001410804205107050008100380c0c103000f860716001c06040c000307084500c0240210f040600d81801c0d400d601901c154140300d00000188158039610b8501d1002482042d800807000809043c110041c00d05101641d1150b82901440768142c80c04011044c2900c01550085040c0107030a80154014500034040c6a131010340034081c071007614503500b60084c00901c120050000c5514102c00c1046924028101605160404540900e203400142c15209200c0e08441c01c1d00010000c240183d08102110742a84400812240d031020b404104034000c00442d9420b40c2c0b41d1007242d60300c02e0112001d00071007500402d41c1c0c0014190204054041d0000b42c2c0050000380340c1450030300c110070342d64690341c031603900101117501c0031040000b00e160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 169534460 1250 169533210 169533239
    0x3110301060f140307320a09051003140c030402030102090d03030f050108010501080d08100f06020a031416080a110d09080105010b13260304090b040507181a07050106030b01 76
    0x1010f9880d42c114104450007400800780044102101072400260440c00f5800d1ba40f49222444e41103002607464421042c000d103001d469011b130f40c0c0500717041821801c503140b10313114800031600320440711000d985401c3e42012203980054401d070f034559001d10102d16143e90301044c9403290b0b4441c0d14001050010b242d1184290740381607102841daa40f404004000d03100b03000c07905841c8a066403404203001c1d581e4080c5920f41c50255040314401a50f900c40216031a40c0004021042c18000d0b103c245459140c203204075485d00c074181c0c00d9a4032440e41c001c0c00740090403a0340504100e0318030f41004a42c203190304034060318050610709400300240456a04209101e002c5c880c0c580034042e960842442c01501041d03e003c017002510a01080300e0b0711028001012140360f5001d0103040f2508103981c1d865582d29050700c080d20180d905a440303580761501181d8071a018501702200520b07100054032200c1c0c9414904103e1400d18003040d51856420040788000807800c5c821480958480c2c2c4c04c2c040707175505080c0b90481540307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 169535710 1250 169534460 169534487
    0xb070c150c0302070b0f0c04120503070b0405030426030403140f2d06060d0f020d0f0602180906010e0907050409060f080c12150709031b050114070807110103110301060f 74
    0xc5400c00d000c1c01005080454040d102c1d501c21300b50689c00d49107803075451031090301d0380505507031009418002001004001042250340c56114a42566001d02c51641340308079010700d00c41180e104201c2040082c680348000f4125010070303801d981002e00340081c03040c2860480e0f42e072019000c200108402d04512864072426003504010000c0800d0703d046e10105501c0c841001c006000030b8061381014086640c1da45400355015840200307481030248900c0e140019410625403e854003407001200241c9003000300c2c3c5144a400140c6d203000c0b4000001d0140f040400c405801c0314100501004041a008214000c0d103000744100e03040b06003000d03d890009070030f0044406819119491080c05500341c11000248000140380c0304003038851340e440310101594a00802e07071000342a480c00340f104c640247d103c1281741c4210b407400c1c0c84640c1c42c904280341540b120701c14a0704c020300c045428040d100120b000e002040314110010f040c000342003d864004c40000c1d41090f4440000a10940410501241d02c0743d580d05204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 169536960 1250 169535710 169535731
    0x1050f07140403030e060904110703051309090209060d1103010207030e030607180e0c120405030307080903040503070603150b1b101803080a09120c0309120b070c150c0302070b 77
    0x60441d41c00030000c0c0c992140003840b40f20045014122541c0f10327400400e0080259440c01d555002c9882c1c00f030b03c2c40d041110394115500001c140021962141d015000c842e540c02840e05142c0c4c3e9503441084040c00c2d08410070380c0c4109a180b03524030541c400744020110079019440f030400a0307000e0b000301446d11038001c1034141044081c1f2524000380e030440c0d09074070588120000781c11441d40c40c080c203030400d806014894007072442c00c00b00340f10911101100641c080c542c1e55031446071641d2803801c11039a0307104605c90030740c050340405400c00500c1c0c03103503008071003040401c112101c1541e03aa0213050001c2e0080d03565064003440d50703200304550880410180400038003001d400d02240300390b41d285160644c40e1042c0031f014000000006107060002c1e620a5a1007984980d1082c070300507030380da070041909006403030403008074560303010104d15100f0034821b00070311990105000e070080d902c030780045a219940c550700300c1c0e000c000c089a902c170340c0449000c2c1c1e1490303860783d50f00141c907401c0d2403c02c0020070802506601301d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 169538210 1250 169536960 169536967
    0x1f0f020909010b0705010207060c050403120906200a0209070207081513140114040c05030f160312180623090a031106040305100603030810060e2101050f0714 69
    0x19510341c0d00510b030446a00d090442d407611401e0900a000e0b1246040040c1124940340342c642c0c2003a00800680107030780c06083c0c0c0c9000c610102c2800d44003050903000d1400401c03000440c800880850400503d01144003200717031440c020032903011403910002900c803603000da0042c850038084610300b00800e4501c1c203402c480a441504241111600d08030603d07e01400c5240f01e042920500070003504610240385124040d010303545094203000c1283e0710107000d01c41c400e00803a01c0074070141c0c200188180a541c1640c09003201240f0b0760b0359074030009038507111110a10002c0d02941280d60b03180003011006080c50b4a560b51107002000300165400369074900c0c555064024800402c0d05c0d150005400300356070b8002402c030440d0740c4c0f2000082d803d002c0e540c00144a4801c11008606140c02a000030741241d00c0b0741ca403480e140c3c99071400c4e0b014951440c01124000785c40120501030078134100500c0320341b5028880604030540c1915007607600f5150103d81510350b02040401b880943c586c010742c01c3c2d2002c2c1d20311416905 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 169539460 1250 169538210 169538227
    0x807050c12160b0d06080a0302070905070e090a0c0e060a0f080f070c11012f070501030204081209040b06161b08030f0c01060b0307120f110706020a0c051f0f02 70
    0x2c954000b80280e80c0000004110303c80394a100d40d0080000e410003204039403d0781014603000303640c0c141601404058904050200b240b5501550b50203102c2c610091018800769140d405050041205511041c00c000034842240900d8807136000078400701906545481d02d10b00000c3c40500340400c0940704400c007211580c10002e1143d1b001942c46441903100c1c0c004001101d5000040340c4032144520424880a000c0001c104042243d428800c40da11b4540c0c00d50b101032b540c800044d4101d014901c0750803059040410150303c1410344100030182b040c4028000108100c80d4030200b07105802c80d014000c05454080002c1c4240000301d0400d0a48040c2d8112a1042e50b040a46694a9002d15079001014134004182000d04540c29045000680007604119071a803803c204000c0c0340354001c0307003480e180c1c61410ba03130b442d05c10f10b1a000700a010958034981ca071603c2c110b5900da20080d401403000008100c415041100002c100744501c2d00d0002100014034038503210260200c01700c4441654000c1c482d40b04000303048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169540710 1250 169539460 169539493
    0xb1807050f130506150a02031201120f0b0a1e05150d120f020a02030d02010c0f02030c060f07050904060b0406020c0103052a0706050a0906060506070302070506030901090807050c12 79
    0x9000b0b00401401041c16155580400d1004a000c501e000b035500300451060745240c0c0c0040500306501c2074445415050740c1c1c0e4911034035020b81c0008003900601000c0c200101040300f0484040d00720310103c400240c40749011540340041c03c1d9910b10310045136100e000388092007841c0d002d4024400f03001c903980264001943d484401d44032580c0c000c582803102c02c0040c3c060700c0e40203010312003c1c2c68016082d2004125040c030024020f0100c911a072001c00d80c121401c4c0d14042c400800d5681d0100c4c521700a203042e450300181003040c00802803003642041002c109040c0380c0d44a6001e8140100364103d1400d403914103152000c0d04081001f009141094585420442400a900e002c0500b03c2d840b030041c01d441a15240403800d4610807408087c000b14204820702c46e045160742e00c081411801000708004164070303030040058501c00c896000c0c00582c06070274140b0440c54400000c54004241c280001440e290a036108070058000d008240c40300e070001100f00e081405c1c1655038141e9204c090001e010081802d0181d00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169541960 1250 169540710 169540729
    0x15020414090939060d0203010501140301030818041d0f07051215040f08180102060a290102010b0a08011e151202031504050c0109080105072102070b1807050f 69
    0x154581e030340ca01c1c01c1c4040600407203a11801e000000d0001c070365854118005d500039510a2164070300149104480c10300702d80e0102c06590607a944034440c00d280050603603e01001045c9002034030b6000e40e5458180a45041c040c070000d074001d040d8005007503c00341114a407800c0111560160340545c0c1822841302519201042e1004805040c81c5144220348a605148102070a41e15004148110010b0322080b0391416041c1d80340c420b5800d90841e1007030756aa411000c1030b2034400780300034040481d098070120480300c000c1c1d50b90307030b131200601c000141505600c001900c040c038540d0210105035900e62240c090040605454440c10f5210070043c007888005560007468200035119000300d500792800d20404564040c00902140020007010f54600d05050912a4a030081e040301d00b404208601c0000988003010301915100740d04a4445031507041044049000c14460601d10200507642000100300003042114200c1c014507108080e01c0500c812010918a0300d06c1035000700c0d00c90140400740442c183d5468166 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169543210 1250 169541960 169542013
    0x1002011b02012c01022104050601080a030507020f01210b030c060405030a0201080403030b06030f090d0e01090510022a100c02031009020f030a03111006031a04150204140909 76
    0xb4103010b03c40c4003075007600a018000210a8400380c60f00264400b540c84581280214080e07400d5032010b076130310000d869498800140050121388240500009807a2910030301000601c1810000b80614508480800ba040040c03410324200f9510101c520980c10104030341c0101e0710782547c03e00c3c546410400007903928108424001d04202c10f00d000141010301c2500441354800e000f030012910f900381410303510a00b000413195842c1c0d92160603940240b40f40300c0c100c80320034244107071110f11415082506105a07400303820844000c7d4401c0c01c900d082c0188100751907400556103540c9000e0306240320802c100c0c00e00092001c94040100d40914030000d41e030b01041e80300c81c0b0700c0d04140000712040b051010500315100f800c1c941c0c0c2e0500840c000d4906158004241030580707881d40c02a500d01d02c8000c80c0070030440c0c0c164000a404412601e2580107080000f103811500701e1f00070030102c0c07036401c0e480c50501c059030301c60b0708442e003100400540d10041c1d0500c044d8468101098a000d01030044c201ca80c0400041140700b00e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169544460 1250 169543210 169543271
    0x50423030a02130e211b0a050a11040c0516150b0a080105060a08070305100203061503130309090c08060609010207050a080c0109060306080a030c03091505030f060a0303050a030e07051002011b0201 86
    0x100d03040941c0100300c100c61f01c650013420740341100b041e414800f44031006807180d140614189007040031140d20803003c031120100d400b440440400f10320345441c20111442ea85004185036a4500030100b551030b04d035004010440d0b01c00124881c5404010b00c0810701c0705074465203003a0311161040c400141d012603803015030010f035040142c41e65240030014038060540031555000b03440006c00e108010510300c503032150310350283d2911000c1e00e17030f01e21301c6008480f0150440d40001d511000400d21034a071180040001180510448a41d207480300001071309810241e0084810703a2108d03842d2a01540c100ca0903030010f08190034204000307440d1007a040e881d240782450050070007030701c90b501e00c042502400d0030b14042c03d45503008801d548003000c0040c00c1030f801170700d0602003016010002030311450303c20f20714401d4035030580d52541000452203055000d00700070403402c00796009802d00890180c0341d17240b04134180e214680c00403504400b510040040c900d4008022070440e4100751040280d1a6014040d0020300702115 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169545710 1250 169544460 169544497
    0xf1b0f0b030a0f0903230904060303050d0516020a0609110603010e0a0c0806090408160c0b0c160305070509090f0a06090311011a060a02100507030912050423030a02130e21 75
    0x42c81c1446c0d031040d4000603510030310780a804400c0c1a400409864403030070f000da040005445666051090102401c500f40050f80600281400121150070904055100d4094100b6007030a120000d00c00390000d030800b5400d202c03d281004840e001074041c44d040908282045a44d43c14504049210b010300100094100d0300d0010704540c0c8800074154001240d9040280240d903a9102c100c200d60a51104405012512511920320989141072215404890740000240744080c502000d010031010020445016806a04d08011414030b003071122448280c0305000016107014107160152a984c626200c0c500245e240203028901010740040c603981401c01141d215880e01c40e0b011040345003007561404511140d081009000d486505900040c0769107204111001102d1000c52044903103014a10541500000040120078882445054240d0205010b01661220292600414440c85800710659007582d0741d80c10b8000307044c030213114008040e0b90000200c00d09640604a1040324010039040324084000c14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169546960 1250 169545710 169545767
    0x2703041211090906011a121501020a08030403020303190912030f18080c0d2d050706090b100803040501020604020603090a1208040c0b070f1b0f0b030a0f0903 69
    0x75503420010007006111030340c01d01d862840107481d80e0f000c0c81614204a841c071801003071000a1300589290840c0400070201d00d5540d00c801040c03c85941640a066002c0c520524020900490095104034003907002550342e42441c1c00b6610007141b06c00d142c041c1c0309151900440c006424917443e0944903840740340115a802d03402410b03000401d45065503002050003000e503c810004d0070005040c407071131040291210700e6413420054400305c0350350100000b040071994807210141e00c90000d41e00d08100c0c900d0318500b4003901e07540348030884082020507521b0240703410401c2001c03800c441c1c10314050b19104001d14102407610001075519000948000c0c890f20b80440041c80340e0104007c10840c803074124040c80e15003107004502408a180a9a06640a05000307402280d00070f1501e0844620540c80070074901180e95070303105c21070001c40d42550710440b5030042c080020000c4000c82c40002810703070326290300da481c20040c4401c802c503a81218840001d908202c03d140100350019560307450143c01e480200d841c60b900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169548210 1250 169546960 169546973
    0x109151b030908030c06061201051308130f060309050f0c010203070305030903190c050706080708010302060d112101080c010e060c0109050a060603060e39040606050327030412 77
    0xb0381e080542c1510000c90b50384158071001584500601c3e007524608070300320040000c1400d80702d0071500c218422552145490000e000a0008c2c030080c00b428a80351003990702c401c000500c2d15166804040020748440c0e0400600a06002c0380b840c414001000307100803025800040d4680c050020041d06005000c80002e140500034400c030350004c81c11522562109039215400303080c50030741490940d460700c11108003003007242c01400001e0044055464401d0703a60718580c20000203500101800585a0716140e6020715030762910007800300180c0c040c50303500d40c070818250b0052490307005038007070140d942c01491a94a80d0360001094503c0341000e4505a41e00e60001c43d0444c05048124401060392217025580410b01103c0d900c00c10540f441000d05018408811440656600040030310580c0108100e100c0d041d440c00b501c903aa403020070519926011b4903000d100042c1100c1c1c480c0d000e600491000001c000d075211034000b0403406120303440011a03820104c01c190542d02d014a002d10b00107d04144054002d0121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169549460 1250 169548210 169548227
    0x4090809030f070f12020a1502010b03010515040c05180402130f120606150f0f1809200301140108150d05010f0e0109110d03051303110109151b03 64
    0x1000d0100c5608501d84200c1c03d503144000d2103486110510400046900f4850b281301c68246038000b850903c0280c00c15401a10014900c00f0303540940d981c58101182684082c092244103d0311601b04002800540e01444152454211410104502000021740300105000c10580c2c04c0b0080d42c0051326200501000c48071800a500000030f02c0e0141c80c00001c000880801c2803210700c0c440d040074030600355078016200c040c004800082c4c01294280e210314118621031402c80503000100e1800c1c1440d4454240c074200e1400d141d42103600825240c24801c0902c5282d13102ea032090080d5940c80a00d03542c50400b002c00b401c40b41016440c10440801302048040790940040f181003e0000e00035030300e844613807404038002d001d25000c103100c0342e0510141c6220542e0611070060004e030041c45543c852610a002c2000440078160101e00b03102041c004404188011100b03400598442d00c0c401e00400307500e00001d06084090b40c0121642c81c18000752001965001d17001004401d0452102e02001e541c5103005d645590 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169550710 1250 169549460 169549477
    0x19140a0b0a2405010e01030e010615050702040e07081002031023010e030c010e09040203031603111203100621020a031e020408060610030e0a0b090618060105040908 72
    0x120400510001c00c0c0542d00c2110501d01e00e00032201482402451440d40b0340441c490b940c04141050700f08489940290401104119004000a812038880001c901001002410170000030300100341380d002c500b03140c40703070b40040390415004019191601941941d540a600041c0d283c42e600480452040d81e031140f0380e000070700300a09044110a09004402c2040800400a580081c011084008003818003052a1030900b034183c0d20802450060b1083c0201d410000c1c5c81280c15200401c151300c01c0f6120300f905400001c0c400d66402101a502011003440c2480900e0200c900e14010018401115a0004513004442d51400c112003a000d40580c15501c0c9060f45a100d45098000500010600da240d032142455034060140054101c1000b03264600720b0265002c0c070b1810754040e00100f000b44c542500030362008111460042034504a84480324240352078004100d40038440d000078812042e40074440168805050160102c8000c0715009640d81c071241881154061a6074100b1502440850021a032111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169551960 1250 169550710 169550723
    0x2301171003020d14010513060c140f0927090616020303190905060106050d0c03020405030a0204020c030d0603060b04050708040b01031202160b0307080619090b0103020d1d0c0319140a 80
    0x3071600442e11100f800d42c6410480f1302601d4003103a130ba27800307001c1c1c0459440c600c1703030610550408070304001443d01e03640004d90f40e5521103851076801d540d440c3c1c0b01e200681c0c42481c1c0c1903103510a081801441d4905440a802d90510004131091184d15550000540368080c56039907654800043c070071000d200900000c40064840d0140d10004158560007000a1048208018040200005090b0200d080340114040e0680c140c00001520015207065005081c44804010940c0d19200b8821911811115a580203d80f070384d881300c40c45011442c1900c43d140e0300c40380d2400d0003822803500c0d82d24110645814003004056aa9104075000d64600c00c0200b85411010644a900300d40c0d150b0b1980c103541e80007254284009685540020054213121f00c205040314031210042c1301042c100300f00391024041c0384a130303541056403e1101b00d95059241c022403c040c1d41d4003a0740c0790070f111120005402c00e154039511038001e9001c02901514146081100e42c0c05a800c921070050b030b0003c5d00c0c0240c1c100150490040d050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169553210 1250 169551960 169551971
    0x305190f02030a0b06010801120302060c07030e030a060b0112020906120403050f0c072303030a050309010f1a04060f151d04050f0106080906100e0406062301171003020d1401 76
    0x42141340290140240f8090f2100d406a13a40d520035112011901940140181c21400c02b01e81c042d00040302a10001d40301e41081e8107040c510702702007494407211007030580e2043d1302c0c4c041070f05281d41c0080481c800442503400543c079102400f0b0216004d8440d07000304016042d03054000a040c07500c290259000c0c08a401816655000e0500d20ba0b550740c07206000f6654113203000000000186440c001100e250100603014504128040100340e44039000241140b90741d540f01c0b0724a40782c1c140d05100742c0401c0c0310600041450540100144011500c103500955982003844000744075005810009900316044c82c54032205a1045940344420041d40300e25640d041414503042c0440d5041c218030700c074103846840e6102d10096660b601c50316500c0406850403411104040b1040c01a15015200b02c0d0348a40101c8020035411b658140758402d240301e0345070b800e4614031014092074071580d0000718061712130b00c0403074103007070b0350030b00581c0c1d50340aa0051000a02c0795400000301c0d010000e000c0b600c00300c5000c252000704403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169554460 1250 169553210 169553213
    0x50d020a081b040e030301030512030403091805070806090103111c020405010902040e150901060e061e03060a12151e140402150703142b0204060215010305190f02030a 73
    0x20800e00101080c3c81542820100241d030f580c00001c0d40d0489411500800f201d05480d04012031035480988240c0800c124400089446c00442e415545407420904000484d8030709450001e04c4980c0c0500664070640305d000c010170204908607520350b441c12080341c9907c940b400f0840e008d91100a004030081d0401d040000001e4241d0150380688120390a201d84200740f6581e2594890005c401c0403d0194000703500d10060007214810304842210f81005070903280b030701020441c0c07051401041240310140000c0041000f8550808851000040911700046404240c1603591520703180e000b50310300e9a0f00303650b85800700c1801000c1000c1090012030a401041031444699240480c2e56003150240e00800b050113038a44042124801c44000c503030999a03548106441a420000940c810001c00401c00d424141e0403038881a01410700020b600740050041c3e80314505017001c0c0c01d10384004011081c0c0302c4500010404203902290082100c0190348001d01000940c1c6405080c1c0740040d140a5090701c1022000760 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169555710 1250 169554460 169554493
    0x8030d1802010f083102041112011509032a06021f11070c060e0411090607060c11030a09140904031209020301020d020c0105040201090b04120f14120703120203070801050d020a08 78
    0x107080324007d0f2000d00880b80c12005100392880340042c0f44103001c00300303030040100c280081d903000303083c030710303d182c20416aa52900e132480601e1505611241049444541d41e00480000303040c8001000f55001601191040705420088454540e65a81000707481d500b0209d40b0411480071180496401400014003640b120001070680001100c5240507915111207a4403030740c3c45106960f15510000d044c40e1602c00656103031406000c2c10030800080c000c03c465542d107162002d00c0a8405020395071b48044042c5d1411203824903824401284034051110b6006100100f80e02c09140d46801c40d4002c0c0104103807140e4404240284500c081700d510b09880820241065407040d00074902540c000d9840d80c0c5002c0d125481c9042c3c900c603a10615a0000e4810106000030340203080c4c10560b10301031422501b0854070001203500300170f10344508100f40b42d400a500800c26802844c401e1080c1c0100e4030031415032074458000f520f4904180039080c480c01c4007504840455540d600503501a0000300c003550700807600c115843c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169556960 1250 169555710 169555801
    0xa050a030f030509072d0302090c0702010206011a041a04050a03030f030c020c0306130611030c03010303201203090a05100f0608060c040b090607060608030d1802010f08 74
    0x92001a080202041007450700150100c1a01e0a603021600c2c0c039445d242281000306c03901c068900d045c4011502c00030240e5585d0503030904c00d20084000955900345440020f09145050f0000140d960718170074a0441031f046002075400360380b000d0140c4600e10a05095122241c05160b000c2640400e520101004050b8403075407068842d0115181407182140c0030a0a80c1c4440320740c0322964042e03000c0c3c1e001507481c2c2403a031300c00c048c0c283c050700b00041c0c95031080c81c0d00a11944101d0705000c000c04000010010160321071a424410202c500101800c2e00404500c0b03500e0b8a112241519000340100c04030350710000521800c8245a4010101c84d07000e580405020060600f110002203458500000000e40303100102d11a8440d020384800e00745400c1c104156030b00d070f5070403142141d40c0201d01804201c001600c2c40c4582400360110400468407001c000c513290080d00c0c003900000c004401440b00500c0140d0b0403820302e41c018442c0d801c007520705070f86082d881340d51340c2003080000c100d03082c0f00c0440400400018005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169558210 1250 169556960 169556987
    0xc030405010318150f0605060d0506010801120b0c1b06090f06060321070804150503040204290108180a030504050a170307060e0a0f060f15080309010c050a050a03 71
    0xa010785400d520401030008850350000d0810f00e0024103000004565500801005d249020f0001e07419444c2c0000c07a90a4101c07020001c0b0b4103075a441031141540c0c02002c100c0c01054a1b030000c0101ea60203a6070002d851001034000c00e111f5001207440c8800d41c2c40310894440b41e21403801101d4091424a0f0850b547d110b4544420704140545008a111400c010a060181c4120050301c54081035049100c12101d90110a0940d006082480041940050b4030002800014141d40d255180d0030705004000458181032007152684413694004261420008a004210b40003400e01c0421956404105410011140c4049181c0c5c0100051030003010380000180c020f6810640f81003c4961b00c400c0038011441c011300f0415403e0740140044030001d40306400008050341140196810314400741c1e00c020f074500c9140f004469041d1200e0f0001044205881042044003020406002240c90184290740364400d4a64140c10413081603954414070004028242c2103603070000440d01c0030001801c00a19042d502c1c1c40c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169559460 1250 169558210 169558217
    0x160b0c1903020a0203040608091c02060901050702030403020a06080a06080303070207030b151c0c0b03010609090f05070509010e15030a050601170c0405210a11032406090c0f0c03040501 81
    0x1441030940e842031003902c1c0d02c03254940041d031800b801e0060640b014007000340302023201d201e640e022a4600d003426071449507103180c81c3c005000e41c0c1002d41010b400d5070380041c0740408540c0103100400141c0d0b50300c884c031402c90350241003282c0c050b00c5031203010b4003410301a00100700500c800003c2c0164030703034000388100031607001d68403402e1103031500b2402c5904541c000800c3c0b58002064000710204415403910015128440d402d020340490f902d4003890007a4000b40c0c0074001044159804210070710712400380302208404560104824504110082c1103405800e01c1c550400c0302c44103429400c0d4940240d07000702111000f044a13186d25001101002038502165100d001a900320003d5070b05051214000740101802080141418104410300c001c6544007059078420101141112030580e000b40003601000d406070f1003001030650302000303041c5800c200c406030001c00b40643e480d80d010880c0c17506030346422003411521000b098458411159042c02035826889041100089500c010840000100101c0e5020388 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169560710 1250 169559460 169559497
    0x16020a17160305030306120f0a050d0807030207050d0f120f020904140c0f070606120b06032a06070f0b070509090703050106050315041e060905010f030302030708160b0c 74
    0x211126410342d2000900325881400414014a408110030b022076044038200c4031851000c2c803416280141941f815140c50708203082000c20f40707504c42c403220f510507020309041d0b1904c0070341e070355065403103030310090420401160405844d032040c451010503400700500d40045c007051000c51441d8000b9804400304a1180b4940b8941940d0919540c0c0801d2143c10044203880c2821102e184640c0942d0020000300d400b6a03441c840070907211621030880300054028810140076140800c02d2615003009848004000d92009056a29808900700761100107881070300d030240c031801285810040540441002031050b00150200042258048050318204104a070b40ba401603c8003141502141c40c28051100028000c1002078408040210100d40304000900000f4180c4100c1c0550403c181382d41d880c1110300d54868a0420214095000300c40c054000021109200c1d0314654010390f507841a400001c080003804140c110200f01104c01c1c4850042e000740f594111442e000c0400703849030f40700d02d410620a80440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169561960 1250 169560710 169560733
    0x3110706030212150d03031a0901030b0901110301210203070b040b0307090918020910030203010c0201020a120506030a1704090207060b0102211b07150503091506010504030816020a17 80
    0x1c0d11048507200e8081c1500c1c0101c2c199446c214007402981207203c802403e00c8000840b50744a8a0f5918002d5000f085c50310081c1c185490700ca0b003910f49240c007050042100b0b10051000c800c0c03422840e0031190385024204030b844118404a41010001d500911142d8804580082d101c0e00c85002148120305541c1c612603519150002c0c5400c6a15400c0c0e00e1001c9005c0d61401030060400000184d00421605080360381103680c0d900280c2940e4105000c00010303500450868802c50700001c03c0c100d00104444280090b00d4000c010a96070007507054050300c0d50790342000d42e2602c030342d42c4021100a04440c1c40c05560381c40e003030b0501c1c0016100003c141340c0107101e80c0261154116400c06812201e05800032650f29040b94075090b101c0c02507201d10302c92118040d2100003e814a00e0110300c99208400d03450351512840c14850310750810002640f90240114100f0800085a900c1030442e0141c07540300102589910000682ea140d4408144000750400c03550500814a1089080c03442c0c08241450704480c4da01108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169563210 1250 169561960 169561981
    0x12030711092a0a020a150c0e09060f010c0201170f190b0904110315100311060f16060e2a010e010e0904020f060f03060108010e070c030c03110706030212 67
    0x3031900e08464951000790842e0080c0e1014000c03c40010310344100d0380f40340000c3d112020342140e620096418165038894140195400c00380c031039170b8070b4401c0f558034201d80351040200d2050300081001c1810091907404103011603009030a0f81c02da10001c910017200074030b810b641d881c070864415115808110804100121400081d004e944060000604581ea480e21a43da440c1403e10070350503496403600441700e4000e13500707440540b45803098806c0703807a00300384901d18200601404054100a80524800c00c03214652941076412580c8c414040346030740ea51805241000d100900a0082c1441c031405075480103582c20046413404200108100d0b00c246440340664015680c0548221815020645204e0214010b1030110b002e19802400504920305041440380040c1303090f842241071140080c400b20600c0040c2d40d1180046000d044603061405c00c900303040a0140c003401c070402c401010456803104100405214036a40046c8024103004c407507005454080181c083d41005c07200352440c084020004c1c038800c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169564460 1250 169563210 169563241
    0x30605090a0c0f0c022107090b01030e0a030507050a151b02010b03070e1503070815100e0a021812030a020f060c040608100503070e010306140105130b1203071109 71
    0x2503e031542c1000020409090342d803840c3d04d41c01660301440c040c0e94a401c0c0480d4881c03c1c1c0ca200c6c0254081c003c100c0c100002e0b001151400c02095040610b07000540548280008034002140d8150800a0710740941e890f2040c90700c0c80c80b1400a081c100500e0480603070003556000b28041c1b84241584205610b07441c00c0480c204c41c108440d4686c15407141c4800c10200c252203014940007000705a8581c140d80204010902d812882e40c400d0b910390744901001d400c1282d11400303168203da91080480a854a001d040b030700c4000340640310f0403603141e000454000c0103158504102d810071380600340d500800c0c10060156100c3e00401105005802410f0100000801c046001c40c450800e5020310f504040c00c01d00100d4200c1e400800c030180300f0700307140004280360360300308001d5008001d400c0018080d50306501c0e01600740d594051002d0704449581c00140171554070080c0000c1c881d290b0710000294000c0a100040149103040e112510a0000060300c40c20301c075100c50010913400c0c09645d490016110718641c400e0196 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169565710 1250 169564460 169564481
    0x5090d02070909020612091501080d0e04020d02070204050114030f010915050402150705010504110613140105090d0b0a0b090709090b0d02060a0e01090f0812030c19030605090a 77
    0x700216014056007520398003004031180041c00641c204885070f0000d0340f80c15000e035585400c41d444031051121642218540c1405002c550000d0280804030000c083c08844403c50418803a607000b00340e03c000c1c41c00315030507105100d0b0001c005200e1075a54081c4584c2c1c4002014240740603024814011f144c1348014052211140d0740002c120030404000c3c94001c0040502070000c03684002031024480380c921a5002a000c440d00507000000d4900382407410020803030598032940c1c0210800c0c03000c0e0521760482003904040725030140701e0340300b0480d40d140100c9880c46400c181c681d104c825842000c1c20700c01d004e08201e208510203402017150546541c01c00c9200e10041312008006004201c041c4080f5229420148010601070310300e2244a00a60005110303410006400e00001e480c044540899a0300c4030f40b1390020725220061001352810b02800544410b03640400e407091050000c0410105002d410458a2901010090520480b0140c20090140100e417003010303c104049000f0510108540c4a00c03020503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169566960 1250 169565710 169565713
    0x106081e180715120207050102040509040501020a030c031107060c02071e0e1b071104020d090b0609070e030a081b240106090e04060c020f16030c08030a080c0313051f05090d02 77
    0x84c2e60b40c80100300654480241291195000d104c002201c0d00c80c100d009001e50b00c94000540c842a21800050868001600310000c150a010100707400e200d0340d03001c0304e400b941c0114000c50414003160b000d92405800d039203c4981d146810741000841c51a180442c0180c45098441110545031100000f2103402461004d0f20307420801c000c940e0000d8100308202e165510090005810709403081031340d100705c0d25101010388109010908019241ca4900c0016520051600306180c2d02621140403c0d655014094010030300c100000b03051a0303640c403002602c00b0782141ea008840e400300402c4030b03100780408252580d0352149010000403610350f0103059154207a458010445810b039030f403503c80d032020304044a41401580106a2000c10b00b070030034845006d0804082c00080d4400e440c42c940100c15804035407191529030001d0001801080c1e1100341141c0200c046800e1a8503030b120f941c102c406624068000070030600c201d800350882010002c690f90001d16100314100503d940742101d084d150440c560b40d4038010f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169568210 1250 169566960 169566977
    0x3060803090109050613030803010603020318070321030b0303040f0321020a03080408090a090608070902030f072d080a050105100e1c02040207110f010203040e0106081e180715 77
    0x2242003000140001903203040380b5400c440e980391203402302c1d50b1003a00040c001035000400c014038543d2500d044d0704603010401c010690a4510389800202240c0c881380141c00c6d541c1ca0000d02655842a00603802c4814014141c81d61b5075038850350b14080440a11085412011200002407803401c44543c00341d030186aa005400b40244980e4100c41c0c10354020001c80e000e003130603c0f91006030f4440c0d10208008d48245000010030394207200485207040e01950103210103500410800952005295846130410300c030741882c0340418210340c1c0d282e001034801c490400c103001541c10071200309a408a8018015040c6943c10040c9903240c0c014001c1050b107108a9030085031011001c003140d800d111390f40d20100c089138080200060f66550025050380e114450030303505094a5100368443d445c080c1c820315240302c0b0900041d85007920b408106004160141f15500900007148009010b50072030011035401d401e004030f000001d41c500300841d00902030b4a072401c280188aa0302c4003094860f410028480c20702c11a403191003c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169569460 1250 169568210 169568219
    0x1b090610051c0f09120210110d02030903090316030308100521030d06030303090605060a050a030b07031107032f03040b03040807050601180e0304030b070e030109120f03060803090109 80
    0xa40b0890568644403c1d650340c56820868003522900358030f0b51003000b1645074030b440c007034009207050381003070321055030b40c0c0340258901d00074405204484040019050160b00c03a0303541da01c05800c0d0b0003034044064150180d103559680b91031206051308160b92180e2240e907065100c0303001c078203040340441c0210742e04203007900c052000103c43c1c1c00c01c2603800a50721046034504056064101c00340c2e84540d02c114080f035107400303030b02041203d0750058540c800c3c0b00780e4060201500c1d04000501c240503520014019070165404034100380e100c2c0c1c100034a05808600c9040d0780e00d1240c5001894000390301002c04801110001180501001d610300460811080c001103003410309000d07158156074409001242c90810800000c40001c0b02402481e00030040c0d038100007040002e210340e0906aa214044065094000b00300a00c005210f003c5400d0304882c8602c0c0c0340b40d0340100a40883d00502c00b203c00075152003403510044044581c08030100e099445280d1b0280105995181015924002d0030300c0745003ca408d02d5400e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169570710 1250 169569460 169569487
    0x210509062a030a0207030510090224070c1d0f04050c100c020406170609010603030207150c2001110a0f0809010507060203090109060e2a060c1b09061005 67
    0x16a0301c000708104082100080101d986154002c10091016800c660000c200f40b120600180c8091000c4000c00e2000344510740c0090011a081a1070358201c0b00c100a0400d00480c1030b405940d0380c0b5500c4801400c01507161482810002000044814002c1d03401d000501203041d51120140101c2d80f0000a1040510502c00c10400c0d10160008604120702c8096050160b038075405040000c00c18404400384541d81400410f090460050a48805a04098003080003ea0010300d020407200c044e40c2c8403254440f031400c06c0b145144c108402604401c01120200e000700c0d1a140361801011090701c0b180817040300e1000141e03c840600c00c01a12481c41400c00002040740360000b454105d034145030203031621080380c1d03440040342c100365810110781c0e6440d4410b80c204500741c810142000c001c0e41c01003c0b6154070025900d031103ca1400e080c00901c000c11800101030302c402040d40c03001400003068440985c031141c500200c001128456038032170041030011500504006078100b0121030f0b55980c03240303003281030403001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169571960 1250 169570710 169570747
    0xb07170402090c070218010603060510080f060619211505061b06070306080c0904050d030b04060801060303020c13020703020303040b0613060e180303100302041a0303030421050906 79
    0x10004010800ca64801a603801126180440300e200b000c0c900341d41411002801c2b43c9c6941c20080c000c1e80358000c4c0040c0300340c000814a6100c89031070b004140036902d94000c00d40600802c40b022102443c03c254081607150041306129200c601190186c0519500d010000103030740740c90490408141c510f40c428032a60a264005145000d0500d0011500c00c410a12041c0303002012245c1d00d000981d103120a100d070220601c02e81200c2c841c200c80340000b5040540b9229100d00448000005040d600c0d4580d8003542c0300c0e03802542c028070014000b00162a0b481c10060348401001050510a80b40d60000f0074815440d48207480d90300790154011420350707841e652075101400d0003806c050750008a1450090700d09074503000f510040c0110310318106032400e28a541d040489046201018550401d000b0031000d503022060b03002c1102d4048902189100001d126108903070341d40641075405020000801040c00403a49142c45040b6000c081000c032130404e19800c5130701d4000d414155600841c1005480308100325404035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169573210 1250 169571960 169571971
    0x60804020402211812160507050411090a091802060a030b0a0303030204030b07020d020d0c0602070c0f0f080105070503010905061306141011030a03050702070806010803070b0717040209 81
    0x10301c0d0503045900f01c0c260072095041c11014005800030880120016401c0c030fa050b8518200501c000054400e10620724040c906444110f0822460070609101d001c10240e8002d00d0094010051140b4039140c60b070039507000004142c0204c106c0200060000003e01c528110841c0464030100e84034010350800c2a5984011040f8080540300d450440541da80c2a075450000c510030f0302c00607515031039442c2c01d80409000500c0c502c2950000381014000341d80104421202219514206071031700e102c0d25049000b03000e9050054024080003c000c030f0243c0300c0c0d034854006d0f0750f070213140d5885440e500c41c1100c0c2a6141207034000300151090004004145c980d4108540202004141c941003443d00078401c422154164084c24040e0300303281e00c000e603070300317004080e1941012145032050040194141340741d07072440f6410380030040595400000b140b4510074000c08020706482402e03070390696502c004540e40c07600810001d4070010380074004901858080c4403003510448000c0142c0b80190784940030003c00d00401080f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169574460 1250 169573210 169573219
    0x90f0909100c0c050d0c12051804110d0e060702060609310204050f15040204030302061b070209010f08070e01050310150b0d02040f05030102030f130c1203050c0d050a0906080402 78
    0x8450f001070360034071000c03028201c0350780c1d80c031036a1505080901c403407019041c400d028060704100c00c0000400640000d018104180c0d00824400316000e1036140798495403082c0c01031246440344103410b01101103000c5024210075422106191504410440c520009598540a40b83c10f000340c1c03140344014180940402082003d100c607003064540118050341e0040711076071940d9880b4020003c0c0c01d04030513000c1450200640d8118140703030942d9401fa40d110000b4081090034180742400c40d0b448007120080307600c41a4003500b4940c40756514108882042c10b10b00400c034881c080d04002003880c4400f00d070094101c3c0c0f070060043c10540f80b02c003100c01c0204595071081000c00a254400b16174040c2001c0205081e6030104001a0b6407898030204c911420a25000300340700703900400611200a00341c052240d0401d15860b05c1007103003011490b00c10517801003a03110041320340b0b80160410502da0494080c000e001c071400240c40c54022414001c889038403601c42c0000200f10050710510a440c07040c2d124a80c0648080c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169575710 1250 169574460 169574477
    0x4020102070f0311010216061704020a030f05030304151b050306210d0219030203041a04080d080411010801080709150e010906050118050d0809030c040e0102090f0909100c 75
    0x20b810862a980c3c005503601c0765510401d010715641000b01080344481c41d20368000c2076042100040c03490200c90b14440c440100080800e05640c0d61040c1d4000565210314458814030781450a80e8903500200c80540d00082d042034402800742107030044644024041e200245150001402a02e072070b0005400c0036082601200407100340d2400495084011a0324002007204046102d4020314090000b079012100004484420000940000c2907800342d411103002d101e002d8404084d1504140515480000b07248201c07240320040c1f68001c0615405280601070502002c01520019100f120087c4a8003c080d400700c0010014207141c0c0e8480841580c00300340c604141952040c030054120800e810030142070741e90b010100110341e0044500c0d81c0c050410460808498070f03040018945100400014180840004802165030381c203010142550100810411040c074250440300c3c000d400540e0514040e11f20384884141c07625150003030b54070517000100101f6032200e81c600c2600c05000d607491944240407224 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169576960 1250 169575710 169575719
    0x503030d0914010c211506080702030708030f01051806030606060904150b040f0e10030f03030e010c0c0c051c02061e0c0102070302060a020405100f0e060d090b0109230402010207 78
    0x13801004800106030381e0341a26850660031021041a54070060a006031411608019200e40c0030245001c480c103d0900c0201b035581c0c00d03420303810351040e682e00078017000c1c00000f0000140d03026080181610390584003003461a91407503000c04807200c1034816a074142d11206c0010840c2c6051401040320072005400466200410403030038100c03448582106800200c00300707041c40240080c1d20400c00070803055200701004c0c100402910b06060311808082d240910b021282428903019803c041c008000b203800800101e515404002c002d0f50b0488011141194008800074181c80c0140c01072615041004003c08112090b41c208103041e400b00162001011410450700008810000500031020700e0310005030303490300036280003420042c000301019000c500c148800d00490b15502000c42c8070f00c41c40e00702281070808450094400f8807040768000d50014000941c10302d01072554200c019260303c600000010360342c81d4070801050f43c5000401100c45400e0000d0101e079000003800e020780041c010700540b881c1d207446 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169578210 1250 169576960 169576963
    0x22415011b080309060702030307212309010e01231503010c180e010b0306060a090807090906060806061f0302221d07050a030b0102030d09050d0807090503030d0914 72
    0x2100709032181c04020080220b00f41040c00000d41c403920078400f40d441c62402190140811000241e00140c080c40000081244000d56202145020741142c4240081d441c0403c05081e081d000c0b40c03902295401c07d05c1ca001c0c2141c0c14050901000c408a1580740a44441042401000c0d001051105040070351808000903880a1060500c0000c142c0e03101d4006a5120003250035482c0103500841415a05000400050000009503500100c046640551352030020808580d030100941008205009160700080c1d01c840c10350200c0c002138070900d018056546d8442080e502d8100c100c5801b60010740b500100f01c041c801c2e01140b01980704803801c0040c00c00d00c400d07030b030b0072803a081452803100cd802c0c00a10503ca100501450343c000b010072881d041e0041d140c00c010040a0740034900c11714007855114480e0f003c0ca40e0003441030f070304144a024010090407515051881d9660300310580381c004241284045450b1600c11441041680d07400b41c0203600e004440301c1c0c40001040000c40c103032a110380004240070702030030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169579460 1250 169578210 169578257
    0x70c090204030b06150406020c100c0203060f071211030103020103021c18140a1106030702120c16061d1c1b09050601050a0903020f0d050307050d02241501 68
    0x5220643c1c807500d410300501c0340d10381c00790940300494542480104140383d4001030540216105958040c070350161444c007079900048221002f9414055035040020020041c1811849803120b56290004086a00000c80884c5d84042c0700383c1240c44c0410050015500a030020400d070118510818901c840f0145000120340e08400b0603d00500741c443c0075001d10061a81604d00030707080ca0042c20154501e540c42e03082810380f50071103502460001c40024a028001d222240040304200b140b5960740394941800358031010300e1100358071803001014001c10040c0c410701140c1c644070503601482482072404005c0010464049000d500310402016100002503406480c1c0083c9030344140000c2d10305800d00740c2030815a0001030404c0e040180520003081d0450380000c0c400c00702c80d011f0f15120310180b1138401141c40d40d01c040d00060414400056238500304840043d5007a10941941c0c2503030021480803450403040d500c501805005240018003003100d415089041003c01601414002e1819114500500d1041b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169580710 1250 169579460 169579463
    0xc030c01060f0b0c0d0305090118030201021201090b030303191803020a020108060603060109090e0c030d0909050708010b041502011b03060906050d0203060403120f0914151b070c09020403 82
    0x251940010441030101003180005002030094180c145400e09507140e41e10b6512007003000c01c06d610340000c80d441810079404500b48520822105500035034504000c2d000c0c1d444020243e010003140e100002c6c010502c0d00c80e12035041c0005006c1c41c90758441c07000300b01d44c010500360f0078400982da540d5451a041d00030461119924840c3e0050100c0448500015020b698010901400b0308001c20030091140c2e030010019040d52044030001850b110780c018064034180762000c0140c3c0600c9540c5000c201c0d00c0d00000b0007008c9030300490091295a98608003201c210000f882054038002e02840180000d12040c040c24151020b0307031000041e070700114064101a03003a00000307100407039910001131018040724007071a00035101c141c401001c6400540d0209070f0f01d1400400c0a401c0040c034520020741310100d9008150903030b41c050341c01d1160707420600b802042c0c580e01000365211440350300d1000c0140100041c5881c801c0080d0b40904031120440035042c0065803000388121044541d481e404100714285202800156 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169581960 1250 169580710 169580713
    0x1a0411010f0809030a1b020604120b01120302030904230c040602010c020c060d0203070c0c1d07020606010e010810030605010306021b07150302090103020403021320161103030c030c 79
    0x10100000161020707060000c0d8404015254080207800d01c00081140c2c10141c80d49400c1d4241c1c1da029031110b000850440c2d00079403000c000a400126581c50012038103c0b18060400c0030040e90341c0d00c82c1802903e510500060160f0010700c603c250901e0103602400c80c039250b00500403420307014280b580c80403107002c50305d0000800780442c1c140300c140d60911800311300e086c8a00040030401c1c1803000056050080002c0500220340001c00207004a101c1c504101a4980c0300d800710003199140e1300702540e2840a2510783c80304031a540000780f030145c40003a4090182c01d040e110321020240080044443e2540100070741c0e0421541721001001540f14481c580c002d5005003801070300c0740f80d10241c40c44d010000042442d103607405100e043c0300810900300b241d0880d6145050050b0b540c40100010b170080e001e9580041e61141c0040c489040c200a10f82203504c0110350b6a03011041d401c0d0a0002041f1400780e00310080303582c10101980d200280c0d03c00101070075a080201120300b000d6142600602e541e0200c155407256 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169583210 1250 169581960 169581983
    0x31815070201150b030609100b0c030a030c0507031b050f0a030305041205130b0d09020d03122f03090f0304241409040506190920090901030209041a04 66
    0xd982840380c606402c00c0c1d0076560302807030300c0e15007400d07001d01000c0d000e10701c1000858086421003040642d0310005050300b40036507807146c0005414503201d030444020721000ca0f080031048071215104100311034182d80c0c181c81d00a05550481c1001c60656041c180444483c418071800658160041100d80c0141d071081d83c01150034580b520780034034150b810955104c14800103104654189a103000030505495040c14525210710480e034101c405071560010107500030800c1400d032424940e00501000ca4913070b00c1c0100384903200c204d15070000e0540ca00d41d04910181c03040300b5020210700e880b2000355041414807046030100c81d1915403d0703003940d02952126602031861207291104100b800d0075030b001243d40d4100000d207038901c031002401130300c940f41115208a41e07036400285c05988a010720308610224000f0004207940340c2044a005041d0256189400351600d50908010252001150604440a0300c0e00105910719401d111001c44042c004465041d4290b810250800c0101d240512032409440500003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169584460 1250 169583210 169583221
    0xf0c0f03050708070506030624070c0306181e03050f03091608010509030714160602011505030a021503060d171207080405070b0f1201090e1207050d05031815 69
    0x141116962103ca0aa0050704080000e6030b502c10070380303a008078162192101c3da03125280e03902009009018200b080800031400340180a5170104000540e4410ba00402400800840044030030404100003404900045607410303d400c01e900013403400c00c2c4030b801c0403804c10035179011510560b007003110402c003070b9400100c0681c0a25202c030680001007045078000c1109040131085c06c1d441c7d10801c4809040f4801e1400e445a841e6410410000310040400b1090015902d4405c0240680110640f480000f51301040103d940d02d00810302004242d4000c3c54020300d03400801154180c0d40000b0010755004103540700c8e85011544840018045040c80a140f0f640c540e039402446810f110080e10b1401000200020440040d20001b131100a94000e0708807280c640948407d801c499100d091040c091b43c043d15000040c41c4803030f9402859041031004140d80c0000a020101c20380790042c540041c180ea8028601c1ea10258012001103811038400c0e0a21403c0301c0c04000c80503d07166011818440d05003c1d40b01308903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169585710 1250 169584460 169584463
    0x11100e0102070b0c030f0a02070201090e190c0e03071e03020607030305060306011a1206040f1a030d0c0b0c070602160f0606090209010512090115030b0118060501050409090f0c0f0305 80
    0x6501460459004d42141040301840b10020f80050070b24140c6035001407080c003968028007844000b01950802c0c03a10300e191408803074a401d15202c0f040c0c40258100090000554000d10303402d00301d4100a00100021460301040c00d5216041c1c2406a2810100c10780100c090307102c0400518500b0b0194601203090305103070301403600e44181680100584650a11441d09580305441203800e06040003519030b200347c484400240c007d00d59008449425072401d0901d88000303551810b8128180421010384025000701c55056501a8150741e00030000c044030700001d000349107404040d00c0c0160040d0710060a1210402c0c0110400d484484150f5134081e004010a04204803400b4000150241103000e41c1025501c01c00649203004005020a0003d08840090110813003544820403404a2115a06103151b0340d050102000200f8041c06444150b8042c411000c580103005005c100c40069482c0c9250502e0621550000d040402c2e003250540c10568040c030200d42010f403030300b01601980c00d00415084c03444c40c0c8607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169586960 1250 169585710 169585733
    0xd08040e060a1202040b040b1e1203030705091c02060f04091b05030a110c16050312090a12150614040f0612030318080a0c0b0703150611100e010207 65
    0x1c0d841900040310500920039000e180d505410390542d404190724850340006405010700c0d0000c29040f9410844001130b07804060034458032041c06a69040c0c240340c3d618500c07034407840200c40c1080411010458403c85081c03804038140120f14040307051011480d160700180c1141d011400c1c940324800081000d001c00702051046003404071900003c0c40c030380b101100340074110b0f000091005000c00d6540586094a02c56a01142e40e42190b00c0240d13940048100510690102d1500809010b441480b2041e8818111f2100b1a040000001c00d00354840d850450441001030003450119420300030300c50464012031242c0180d0000d081d011070562032096102003440112200701c0d1086007810b007807010400c00c0745166400a1681c2e60941b03000701b80c0d0004111040100008a000144400c0001a85040d000e40c0007211045051040801101e140c444c400b00b00c00751034050441004546140d80c04002c400e0144282000b001602420750306076070f030100a00d408450903c01004510307500051044100010001003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169588210 1250 169586960 169586971
    0x2706041109010b0c0d031104081009060605060f07061d01050703060612091104020a0c08030c0405040f06060f110f07060c02040c020120090301060f090b041401080a1506050d08040e 79
    0x7014101014892116071782d210800c551000d15650f1003221686103400c100302e0f809485450110f410b11506001c0c0d00f00202040e09003640c00b10b240480210302840c006044495004c910f040580c10441c2e030361901c0000b0126941140c03900d000b407281d03850440b0380a0144501c280303070316100040c0300f5141140142620b4048001900c18030300d040039010001e41c80c1d1600c04034a00c000d0f42c1c0183c44121000d411740302c580c0c0c01c900182c850f807408410030105c00704120082003034407410394040c000354108010703040598900e07001d941e000c00c05003800c003261076121b50034003004420071800321200c403805c8003a81d50403c0700d1604820009981c1d20750100c1581040d000341c400381c03200c61000308401d01c1030344100c060040d6940c805250800d400900305007160707801d4020b03102a00b640804090800d42e07844418004100710103030140a01d0821141d9180b0142115800303040f952100301034921a07001c1e5a400b0b22032014220311543c281d82d03521020449484824a0414443c030903c00300399918101030040c0d4601e03600800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169589460 1250 169588210 169588229
    0x30c230702180702072c010b041a13180f02030a0204090e070807120f05150921160c1d041407050f040e0c040c0e040f090803270604110901 61
    0xb03018119600281c00300481b01499580744401c00070400c84540010703a0300c03c10068000740300002ca00404140d0080045503419414103510200241581d525409410003a001616200c03030208400c00005e000000c900c0e0f2041000a1152031000d100d600700e0b0020f403845114654003103824010010306215450f210140040149091032403c0c03101d5030360b000640200c0c01e040303107915640402c000d030841c60310560a5004045c0c40f180740280750800307090441201c1700740292083c0b40c1d0001103200d414010716004459800f1040c030785040b0389003100c0ca4480d0701c0e43c200c0d5401705050000940313004c1103d8100c201f03070b051080340180341001d0800103441d0b00582c200c0c42c06900040d5041200342e94240003081c12810580b004a07200800c081a1400c000f0240c0c0440e400c076043c800e00d0204aa030040c001000390304121303010040760071440807440c00c0303491245009200b5902040071651900801480d90549014410300220681c0b42c0f0980c6810050240c60413210011200700c40c41c0c181c40c0059003280501000d25 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169590710 1250 169589460 169589509
    0x102010c1b0f02130c0c020108010e040b0c0901020f070f03060e070e0103020d02060c0f0c0102060a020a020709111309020903010f02070b070c1115040e061906030c230702 75
    0x400484520000c1d82000306001203500c1804110f40b00d0300300c01d05840341480020098480744000c06001510343c264224002040c001c0041106004512090f0056801402e4a25150b4500d080054075038008405d45040d8410908003042e18a420420f00d03016003070a510400340d0354610f03e421000d4030700001d406e400c1600311080501940f40007041c010304403901100c2902d03100c1c016001241840c41081005c40305170090303c010701721154000407c125206401c4c0c0c21a25141d50303024001003280a00ea00b2080182c10070801000700740d00540041d081c0d65104940c85103400406a00c0c141b0401c40769001112aa17004107014009250a00c20b00c40880044401546008040d80c1c80307600c03449004155100f030121074070000007400031110002c0300703030640941401c64034002c2075018101908140b00d0714002c059868006031300350230038441e9503031a6806501006035103420031b40f0650103402400c44507401c07c10248a4841e14180400303240c16a038016054941d540c0d0404d00500110000c40c0000c88e500c043e080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169591960 1250 169590710 169590737
    0x10b030a0209070e190801020a0e010905030a0213110c16050108010311090a0e01020a0c02030712110111030f04140108070206010f1205010e0d260702030f090316140102010c 76
    0x2e5200da41d0004503403502c1804c0018140000f0215a06491040c2d00409680004149448154001c1000700d0807610b440166903484401110900110b000c1d594142d00248218001402c1c6040e0054a100d1002808a0380c0a486507038820250820150322140364000342c0503103c82d50500c91031801820b02807910004940c115203502e1814a8010001c500034180080050b1140070303e0351000811040b440002e40d40c4114111004046c40d0707440c07609074401d00803042c0004009410541c0c01c0784c45a400002c862800c40b04800650b0070319201412010240003c01c550003c0b0b454000040c009006505c444000125400b400101003800c000c2c01001554440710050145581222901080301d40d0700b280d04114404c41e1800c035015000266940c03140b44654010140743c150081c00d1000311042114924100b0b0308200d0304800200310035103454002da08104000d05c4425409001440342540c042d08803201c80702c940400e880b0003891350b440580341071850b0501030b206690a0040c1480c1d500c003481d0900200090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169593210 1250 169591960 169591969
    0x6020309150a090506071b0b0a05183c010e031c0b0109090e030418060e160f05070c05130903020601090b1c0f021203030717091011040510050408010b030a02 69
    0x290100c414822a405607071310410504600c41d1f4082d038003a03000c00040c180b80c901e03240501010382d000e00303544040c140c0d00d001d80180010005a28580c4484070308010f08000f200484842600c410000c400c03001c2c07001151600d000340070b042015441803001310355403410414401d85c490b07000d8829214080c2042c10140302c41c1c0e88400c0b000182c451540303000418040010041d855407040351300c0841c8040806003114501c1071207600101c112108060318856569401e810b1000000c15201c3d640003143e00c008410707001074030540140c84207502c01c0581140c1d4945900028075450164040304402c0c6482c0c503d60410503505018180c01480d5a8030b0038000d280450000560a03468010b500495001d41001d28080c03103004882d500410340c001d00405110041324800c0354903580112030301001702c2c0c1c44450301200f000352a2206403140450602074400c00c0c0303245c01c00340040c01e0f01d0340882426030024000031070075550300c10240310089550f468450b41c891030b081490342502c000c0c0001c9442074019501c0f03000940caa = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169594460 1250 169593210 169593223
    0xc0402090d0b06060c01180215040b070b0c13080102030702070501020d12091b0612060b031e0702120d090302060c0307050714030426010b040e0d030b0d06020309150a0905 75
    0x1e00c00000d1200e03580f80c0c2e0204606000c3c48003200c80079030030301030070580301c0b00710070f03480b025050094a40e040c204001401d001c80300d02c5288105035403000c040001c18081404081c1d1240c204060020880c40c09440340b075112a01b4503160041e4850780d5000040c0311450350100903540c0108820700250100307900641c40a0106107540c50218070050312810354000700b00c48000c0e442400764822a070034150b01e461340c000610300d0038412441a9402c3c0b91402c0491001307030440c10750b03208411114984907400c0c0500e00d040540c1102422070300c1948a5043d102104085020140803807021044000a41c5002070900914200020b1300c26500c1907400c20500048076480011500c6035604040f00c551400d0a10a0302e510b54459035104000e01803510f0071901c065410496145800b07002e110003448800805001c02c0111215054021801d901401c2000ca80300c4c0a5000034a110000a080b66040005502c03100c01b640d000b00e40c1c161036a041403980d404512903400b441744c3c1261007080300b04100c5445a846a80d05d45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169595710 1250 169594460 169594463
    0x5130f050f1503152206090f0302061e07050f090306041b050d02100e03070e070c1a1003120306050d06090501060617060d020a0909050d0e0102010b06030a0c09030203060f01080c0402090d 82
    0x40041c44101c1d2030303941e400c3c48110146e1040e4104408882420240818044032904500600038403012412481c1c040d40c107003291a54082440c8615100c070101601c541d40440b20807103201c6414012600300303030303400d0115910a50007100200c1c1c140114141504115565420680c401d0941c91000390158407404102202d50859003018070011130031100092800d1203d61001c0c07044a0307040100300c5c07d9540300c3c3c01001000d215802c022800388205000d0449460126440c2180c440c14401c01c1001c20410381c0c0c0c0040d40111800d0000e03240342c803540465141000300c04d00392001511220f42c0803c12800344a004014400d5140210034003a00383c0c3c25180c12034016040500c20240e01000605540c0c2c0d8807420b4008001410003009942c8041ca040c1d51128041c040a1012414000d2a0304440d401030140700b00c104030061030715295545650b000c1000300004860501000f02e406404030058504001860160101d4000e00d40c8961410026510303000502e008140901d005102c0c0c07000c1619594101032400b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169596960 1250 169595710 169595731
    0x9020f120303010e0a1d1606090509061009090c03061401090506040315020904020c012f04062001060b040e0a060b07120c020a0603090b090303010f05130f050f150315 73
    0x54840e0002c1c40046c10241a0072110310390b90501241000700e00090742c681324241e4049031001e544d03036050309490085892041c250002d01060001c2e6640c0f4008008020340e0480b400c10f6840903071110501002c80f41c03d1100303c00441c0d500c05040c0510300010840e043c003aa000d00e0704030410340c10040425281c1c01144001841882c58554041007000035070141d07850401c024000715210015020518017230041c64100304070250310303815030401d080032415141868101c01999580b030240361141c00c40d90070150800c0f0307084e60030b140101100d4490080c004c0340d0003042c9074540b1303644440c100680102400301c0600500c11451034078008120603020030055480d0070f0382012095052880b400e82c151803040381d00e000290b1002164402040c841c0e0503034080c410745402910849101d80d02c100c603095503032200780034000802030310150810062a00303440030070340555905404640d003020090824150f440540b811056a00403404010050007012004403190304205c00400c03a03107164515440000d00041c00700003c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169598210 1250 169596960 169596989
    0x180b040314010905030703080f09010c0e010f030605060708031b0301120303091b0305030307030605030303190c120c030b09090a0209160c020303190810030302071203111009020f12030301 82
    0x701d80d001c2d440483c0e51900801501d0303a85040b4500248641c2d41100c90b48650700600000c102e035050148504e251403100c40e01d8011410350580c1c010344021403a140ca000406482d4040418203841c0ca0015110343c1d441105120340702c0c106007a09030200041c00380c0c102040142440100b064032003000001c01200d0f00741c20700050034009e500b13280c2c0d004050010b00b400920b441a100104004001009502c075240a54041100b00e0322001056141d210689400d441418902c88690f00805103500c054203602d158101740415400f07111701441591400d003210340110780c2d40c0140d041d040c184007031004da204040c070001d00081c3d0f04581c005803800e6000f502071920500040440180c03107020741d41d003c0006400070100c82d186d103400c00c80b402901241002c0c100c000b503200350100c0d520312225152402901c1c0c2c5a0090700c07415040c42e1040301c1c010380514059040101484202700b40000038405c2c0007007042403000205004c4405c0c014000c0c0008a4002c450240b1040d0b41d0101c0d17103d07800b20559040d00e0700a0400e440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169599460 1250 169598210 169598243
    0x7050a050c0d32030c1c020c0109050907031b090608070c0302030319060f1e06050702030601060c0501020706050a0c0f050f0d090606050907090e0a18020112060e1501180b0403 77
    0x500408004080001d48030000f449098000300156900e80a0003611650344a00f0561b20120789601d44d21040300d02180074100144400e281100e0b80c2d9601407007501e40001d0400e00003800c00303070112840350340788041060803506004107170784071045951051070b90070b00050003442541e0081d9039110003005004210b91000030302a0700394140d0003503002030000311808a002c03030703c5448030b04041501d401102d100790885c940000303009003d0407d41c0d41c401c0c1c000303000c0c00e11070386841810b40d000404030f041105c00b55801c02007800024498852030f800740400760f200003501045035001818035000210340905105040c090494010b88500440e840c0c507074500b9011071204d00501d4040c001c0d10f860b4000303503030211060040004031030b4450000000c4a0314596402026100e01780700c101113030140070031030003006810b15100001d540504541e040b4050004000a0415561000900c1d44203003502e09403103461188210b4030705507a0001209103400d80601c40000002d00c0d10f01c21810781e210b2884000c2144113601c0d42c209 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169600710 1250 169599460 169599533
    0x305070c030203101e0b062b0f0c02010f0b030c0f0102030c0a0305090109090c0207050d14120c0c0f09011205160b0a0f020f0c0f041107050a050c0d 65
    0x80155030107000c64039400c404602c404060300b5505d10082401112909408403e003241c0941c846410b0082c01ea02c0c41c10150b10000c5500d000d04440b0741c9117a011702c901c40307041e500c000d116140401c0c00201e800606010460f0b8000d00f0740700140e20a800c414205044440950b4001c900c52814400850303d40390044002c0e4010f074218018801035410901504022200b4540c00c003008009002c002d070390712044162903402400407203103080d040900580c4104400d11280c00d1207c07061480f00c0c06181606008000140c51900c0e1414010026003040004520b41003074407001c2100c4801e070001103030013161644501000c9000000b05101d0360101c203020808070414020188686800c080c000140040815210000048141e20206102002030300b078500340000e09201203011031301700c0b44610251a101102c6d104010108040002142d40240e0781c5000032410304224005004075423144001c0c0030305034844c0c2003890030a0b1650000d030b4000d101d102505000140b00c140038ac01c9443c000401d40740d94242900030300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169601960 1250 169600710 169600733
    0x90a150b03090c09101d090d050912030a1101060506091309061503030801060f030e030d0f0204211403070b0103060504030201090b090a023c0616080c07050109030f030507 75
    0x1241c1040300c81c41805080d01c08400d441701038400403081141078000900d001404200110b032601e0081d00440d81d40c41c1c005100708020586450010591003000c500315240310b0955008180d0b000101e4012400d80c032107000f00780540402850120340f02401d118680010820300d4526917441500e541c2c1d2c2d900c03040100705096014070134413070449900214440d164036015298840038090340d80400d055000d40c0e250b1034400e01420444254003409182040c880e548200c02400c104c0e010030007034039000e10010074624811070442944285078600105551120f040c401c5101d6450b980d01480384e0010410038002c00c51880c0c2c121704480c0d1109001131140e030b50742812401001044002011201d191050107200c442c00209100c2c03550007107424040400070608030f910180c0356500110107810404104802121a0909140c202c4001400c02494a182c1400000e074200241004032103031b1101048200751604200542c030003030102820720099107421a1680e811820140070014200711001070500d08002100c5001d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169603210 1250 169601960 169601983
    0x20130b030615070b0a05060d02060706091103101d030a050f0a12060e07200d050c1e06011d040b0402041d010606020d0224011502030f0d020405090a150b0309 69
    0x403540b03603031040c81d00d01c4e85003000791030f214100c17424800030482030b142191407103408550043ca4245408170542e12403014000b00d0350103940a000007800501541c506108040b1b001401510001c1e030f01d01460250249a060b0100f20a050341c0180002d000c4e00f5000380c111902542c000e05115110120380d5011030350000513140103407800d800d1020000300c0d04010700e60503003d030126840c0c25046526500e0801c0d0404507480c6603c4d800c0d1712000708800c82901420041c20000c40040680c0d4440025074036011940d206c2d1040c00c2942c0d80714400402c03030701c0c1516229050a9480204003c41b900303054503401b034440800f9201900c01c0d81c0d1503e00c641c079904e607006a0f1100501711002440708594440029403615a1512003034054000d110a91900d0b00a040c41080111400c4184504503402e088214035480002d406040c203501c410018910040c00880c040e2002e80b0b0300000141e40c1d02d051109100d503d881c0580030114050402c4040d60b8600810ba5000c42520f10403e0300c0c0d83c49540d03d44503540340c810038010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169604316 1106 169603210 169603249
    0x4052d04050c0d05132604050603280b0a0f05060d020c07030b09070501120507051803070914150901060804080306150301080120130b0306 61
    0x49180c0044540103640d090080303c014180480e4415291811031008400396441048480c0714100d95913440e001c2071040503000a030070b040304d038051401424481c0070040001a00303a0380740020305211900c01c00c0300c1650480110040c800074541c940b50680034100b400d6010070000c3d0f49883c880e04407a4054902d40c940742801c0700c104025041310b80406103500880c0c40020210b804000701c18040c24440c4040d00015240c080094090059458520206403c100030003c900d030700002a10500d90072070200c10707060071107032000a007825240c1c1c101e901e0151502600c454446415071001b03100d01284602c495002010310708002d4540000d104820006543c100080d00044284c40034582115000d40306c0c017021180600d500480740c00980291025a5544040d401011303c014a40c0001801e41c118251411a8a4014601000c014001e030842c0220002c08224940c50308000f10340e00f000c0204 = true := by decide +kernel

theorem cover : BRFrame.Cov 169424460 169604316 := by
  have h0 := BRFrame.cov_init 169424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169424460 ≤ n) (h2 : n < 169604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
