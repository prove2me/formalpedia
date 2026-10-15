-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3918
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:32.061454+00:00
-- url     : https://prove2.me/submissions/6f1603a1-8b59-4cb8-a5a1-a6e08f427cb4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 704496402 ≤ n < 704676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 704497652 1250 704496402 704496409
    0x4021606020c1905101404030801140109030213020a12020405030a03052b0b030105150108070f11010218010f020105070507080714120d060e100501030507021e030d05070e 75
    0x200118000d05180d00071038071038501c600400458035411011200f04040400c50b0601c540c850465498000d1400d041c081c00051a0005a102c14002c40c1e15940b01c0c0d016070300c0c2c90001030321822806d11444c10030655000002c0580c0e01e418108403031600ea1000141e40b29000b1001502c2e42e585541c0b080e100c00e0042c030040041d550040f0302000d200d03405040050341da5000d2903400d601440328603400b07000300c0c140c0480555080120752102018040a070003c002a40790702108a48050381000800e00141140c00014074252294400c030540150609255203c840700580702426a004488644c4013031520b10384000042da403210103030640500300e000030030003800c089200405130300ca802409000382d0b50000c0d0b00001c00002c007600507421075550054858010b9680c1c04091143e100051990886e81007070004a005624800c16074042c03d040c03180514480c0c0303480c006401909000b800041940610741450300443c030038065201111401c00c025507a0360000c25160001c440015003031804000320380101c2203440d00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 704498902 1250 704497652 704497687
    0x1107080616200109020f01031a1c020a031103240f07050c0604051b03030a0e0f0103091b060f141c2408011103040201020613051501060804110402 64
    0x1d40390103900c0010080c8050a5415001c0c100345603550b0050307203060001820040d40300c51901c1d44211051002401154011000d60b8078002c20444801058142e00354607280c08140d0310300740b182110031054200510b4001881d0949547d00c2520000e004082080303642c82d0511100c59850441540da00107800c410124060b100d90007005801c07041c40c113034041140c0342e006800741e904660480301102c2d0036281c0340c6400340d151080c28003441d45864009010720000d10b004010f8400d4102107a071f6070208144010104030308000c0c1c0032703481818580d44044480c0400d0000c0c0240102c00039010103010362a141a00c01400152000401c50402c0b01c10450080c2c039040460480e20303055014484d441e010040f000750722008154052034a09149401102040c0c0340c10510308400803220000c000704024000c10158000c075120845000303005800810000c0c0c00000b40b40d41c4203407502e0040b011900085a041c6d02c02c44001c400303030000c1c1c3c040385100e0100030801c03022001d411b040c1d14040d10254100140c0c07000105505 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 704500152 1250 704498902 704498911
    0xf050a020a0516022e02070b0c3a020f060f36060a06030204060e010b04180902032e061401050703020c031006050907020d050f090d0b09030a11070806 66
    0x16030b078490443c4155520780603034901605049082011011550200030181c0d0181c41200d40580035004002074000788400580341c114900b41c01038040915200b0300c80101c80c070010700444550b00296540511400303481c500045002d101d400270300148100c81034862400b100140008100e42d0150201b1036000300e000514010170070741103081d803030203400d403140b183d542e142c180b01e80c1145104540c100b090501c0310b50841c40c2204c1c004d4500300580350f100c1d910305002440034081c4c00d107001030030030080024180b02c0d96280c1022003034410008000516a00203400c00544041c04194070001074034400c50903040e0081d140c04a00030740f00c1006918601441c0492540d1994505c5051100c0820008140f40c02440710140d803d00003801e45100c41840c0280130000d0015002e042c3c0681c1110000803090390000504074480403450b11031714200182c40700c07001590b6109400710307900400c3c1d0f1a11800040c4000c5625806503011001940e103450f610b42d001841440024101480f640c0282000c0011040103e07006030003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 704501402 1250 704500152 704500177
    0xb210114061c14011d0c12040201050c0f0307111807051b0f100c02190611090405040321061202040c17040c060219021e0f040e010f050a020a05 63
    0x1d407008180e803040301110b2410001122400e00400883c030341000c110b1541a01d020f0046021408a0a0450001c50f0030440780c5210200c41003040415003254400456846441407402a150040300300d10b10b03040010460305124943d101280c000c080100c0e1560760511080280c070304040b1000c0305021641c5108019050300305001c000241c4600320f5148444031140d03203500f0b60850b2015211402e0013a035409640d00300c0c00c0340350728260640000343d10109803a203415401d1802101c285d00d0540310b070b40051007280440c0c0c2d40324004000250032601c1d84d0140520440c000d40707580b035185001403510a48501120300944219180c81014070203101000742c4411403d805032030010f01c1444894017698006180c0c010844400c140c0010081000f007841c2056080e00c4550f42a00c0310b000c2c20b003580208035980440025400103141c004180400380c0000f91802d803181c001c0250307100c01c5004001c41d085501ca12580c3d80141d4548d4007109035546240100c035040300b01e4210131071a01e04c14010041c03c5001f20a0400b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 704502652 1250 704501402 704501407
    0x5060901020319050405030d09170a051f0921110606060706090c0503120711040b09010306020d110a0c0203010b0904020604150302040803030c030a0c020609100c14040b21011406 78
    0x200d03d4411801c0d5005004003400300c540c01562020050000d12243c8100b02c0c5000601c181d01c20402d1000c00c0c140441c5600038000d240500008050b01c000c07000d00305451170101c0c0d41d001800045200240e8900800c40e6140c0c943d10000050140142208cc0c1c41c100c480c8564846403c1c86603a4444000f103134050303500100001045100c910b0001c0740c000540e03201e1a40352240d20b24015440495400501029100e180009142100e51081c407040e00c05044002d42d11080c3d1500400c0807807050340003001a514102c3c00000c1e00c40d4103400c40d41035504408a00c40c0001ea06a1180f011802c0034826500d503a1400c03502d00715146000da002402900c5180a0b01500b080b004080110860081d01520050803030001541d440b8600141c41c880755070001c44001c1459414000184c070300f54000f04589025500301d001403c0c900f0a10341380c00f005441035040301c3c001c0107218000d00b20b880100b000a04040c040c0b5040f816131b0342c1d2201a680da100208550503482c1120b80780010032020740d85100c1b129001c1c806444054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 704503902 1250 704502652 704502697
    0x7020d0507060f06091e09020306131401060b1b010203090c1014070b06041a1e12031603030e28030c0204050f010312050c19020316080c0901050609010203 68
    0x405801c541903070380f508606041c004030360f01070160000d0000c1810701c0c420b0340c4400440b05501c1c040d0b40d00790001070342542003c8042807005664051010b0900d004e405140080141265010f0031105154008004003002203440d41c00d080d000d2680c2645480080c00070350941c00e01c6550740740c552504140d80d51140402d00803030311901d80101d0003406c0603881044459203c041c142000d440f0b011381260150702c1146000301001145900c0d8001c40e03c80c00029012503100c1d2220001440107021807110a03911081c452400500303407404000401c001c16440d20b07042c3d2124001d1801a0540d0100640700030150000081014a4201c0e00e80c00c1094840b080d28003081004641019102059041c00180d0064141402c01201d4811544024103d9114600380001c0990f0040d0494060290290401c9241c100c0c3c0300e10f07034481e1651211445810300013000c3c0c88800f515558601005007499104040035048004a0001c62510480ea039004140079a09146071178001d00000b5100c0c81040100c2c400d6446403407100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 704505152 1250 704503902 704503913
    0x3090203070e180304061824030e030c070816081c050d0f02071a090102030705040b0903030c06180f0304030c09054204110f0a1b0303090302060702010507020d0507 72
    0x284025110401542ea80d20713286c0e00c000b40250188070301004880d10135100060500805204000d0088402001e0590480c428904902030b121a400c103c1c1c1921007800030a12901c010b000e40c03030062000500800d44080f02282c3c2161100b40b90f070000f4415005402428000f02c43c1c03d800b8101c061551034000e590b4411211500014524030b5010811240301040c00410001075040400d9034403140d0b0b59500066903100744550030303440704403944000035506001c100030440c82d0703401074001c80a001302540e0070120706544491401c001110404031000d498026030303044441c113014400745804950055494a810341e255022074400c107110302c500710b5a0340d5002030000c80c074030b0040015481c1c406010341c0349804da500100000c0008035000200080209607520f080d4502031003060001c40c20414503030b042250101070442d00740c10024040d401c1c032604054283d00b140401c0c0d44c0f2120303e0b00c40e4800051102c1079080c02458540010901001d680c03511041c00be0058001442480d04e803802e140003981d032151460075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 704506402 1250 704505152 704505181
    0x1030f080f041d0a14100b07020a0b2d0a051b1c090f0902190c020a030615030308010602031c0b0f0a142b0f0305211603090203070e 58
    0x680e5020b040315000c41003001c500d19014001d01c200c4205005012441c05c003c8a807550583c0d085061401c0b012040100c442c0d00405007206c2d40c00100142c03981551400e94802d00d900501071100300842100301842040d01c1544c800c4c010034403500382c0e1030030101c5400700070b0007070706c00c0d584540b10341c0340b08850046100c0b00405c040c980d82d400c84540b01030703c9410100003030011017483c0a00546848145000f10780800503100350389031080401034040c820741c05840241e07011004120141c0e0005035010380400452858000c00005041c404080b1103a40d145082c0280354610603080902190800c00080c20009480780c08841c51010140c000140340e508940000c5c0e2298440801c142c100f0742c0b01c14000752200d860131b4812540c5800340c0d8548800c5040340d1002c050118010a60014403000f054090081400d81350408c00c814401d0074020700d089586d5500c0400c0c400c0120040c1165240201002000d991a800c8040300c00d00c0717030a0a200003603003030340000d403903c00740c2c091162050644400140d4181403c000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 704507652 1250 704506402 704506409
    0xa120c0c09200a0c2906060a05040e09030c1501050603040605101707090e060906360f0d1409090a0f15170d120c0e0405070903110901030f080f04 64
    0x2e615036100b07454074000e002c54412070010b9805001401181054640341e80c412000c00d00c140760b80f1078445d5248420800300741c20410018080010a10021450002c8101c601d03000d251003400442d1600e020f103109a10b041000521402207505000040055445000c2902c1e0400da01c000c02040e9135403074843c103031110740040d8002156a42440f2885031442e0000c140030b400d0b034101d80801d000f01140c0b000481d50744c02c03003510860216844240020b8503503152858224580c003c5505051036412260500e01001201c035034004d4091304801c8180020b21010442101143d140742400007068001085241c901e0040111290040000000050b60552903170b20129044020311001c01911040021995401809000700d02c1c01903613100a84000280000e46d00380220304595440c913261940c014900058074045510130107109580305640c80300c0d650340c054513105c0d565503a40c3c400720b18994100403081140c2c071120b00340180d010704010301c00311301281c40080b00d0582001c000c40d9508101e0100c8a4184903650 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 704508902 1250 704507652 704507711
    0x141801060302090f0f01050f071e1a090a0302070b0c0c06030901022d0d0c0c0c06021606031407080408120f061512012c090a120c0c09 59
    0x400450415003660281c118000241c1d80050003e0040e014400040440c3c450305010400611003800b0280d01c0e1401450400d10030000b51a04c01100e040034088640d1004003151901d04120480b01104e45541d4070591002c10340000b0009050b160720f0207925200580a00304c800800020300000301e035020006100108005440c107503a91403e96a020b0003908802e0760327000c90454801c0300c0d940340418040d13a14517172141280007502d8039080861050040184221349418011100f001a0204444454400c02401c0d0394026001e41040303840c1450010300203800c10b0b4181480e00300d820020002d03d54540f94002c1c494185002c103030b112420081118001c1c01200090220607904124039140c0381030b1aa80101e4041e221810640518072200c0c07114040c030401045035000b070100400090300c103600c0c40030f10040003240c02001c405001117603005101d022101c2900039485045507004004040940c6800a01a03260040300020b0703a0360f030342040503c103100b0503007640e1b00d840781001000c400700200c108016140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 704510152 1250 704508902 704508949
    0x20090a020a0e0904050d0f0914060a0e0603040c14120a1509140307050c0108131104020c010c030e061e0f150402030106030906050901020c15131a0a050109110414 71
    0x80c500030381d546c001c2c415040b0004030300c0402010701c81e0013051480e044d144d8803003400c002900703e44244405600100c580c40c0030007000c0180002c1e1511820025405140190701944220b030502080e40100365840340300a0042d001c80381c0700007031020f000c01c030003140603441070008031401c101c0400c2401605540c0300290a9020f18019001490000002081014412401c0e03501200c041c10054548035001c84002c1941d401890103000015070500d075240c14104010401170030320200381092800c403600a000c60b00425568464194400340800c400744c1c1c45415100c8140076098810010000c2c150003400005c2200e50310004a00d2010060545d41c18840024004640725a514940200a032150390801c0d43c0851a1502060411006000b10790502c40c100005122000314070401401c4c505000703081c8002020781c2c400b4000000c040c03104200084c000000c00c041c46003403000303100d821914182d0091101d1841d0100b0782c4c10b9443d428040c0e0701241d80705100101c07012100c6002c1510382681c00e000401d400c480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 704511402 1250 704510152 704510161
    0xe0906150a0309050c090705030a050105060414060c0a0b090703020111010504020f19030f061410060206130807060f051906050a1809210f030207051002070c0312020a20090a020a0e09 80
    0x205c0610710ad9084d4040c24451641d0380c1d01807015520072406402400c240301440e1080d2428618020070124403080201c4071030040c0c684031102c40034426120380646c5d8000030010410f543c2c0c840c07000b44c0b004908800810050070294005910500c00d00c0c1d402d80140d0b40c001380410305001d0034580000540e04002d00011034007842c03811100404480070f0003541c809908020400c046010100c900a4a84540080420340c5a004642e10f8120540d442101e06540400030f080021301d16004414181c9038925010600b82031020b200000780c480c41c6591041103285c980204426a43d801429085551070342d070415403650b060000c48040c00c2030070381c003a22a0444450340c118400900103402c0000c030742c0f90340e49540c01481c10012800d03403041c04030142c100d81c042c0502d260b182c406075004002642c4210104448203a4981d00c0b03805030703e490304202d00940c00401f2403c045c0f080031040310b541d410240403010741c40301554000503030300075000d0711000416030301107210400e0303601903d007551891500800d005c8035440e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 704512652 1250 704511402 704511407
    0x40c170114011202011709010207050a0c080106060c17090609040c110f031201090b040207170703091406071b09060b0c1606050d09080d0c0e0906150a0309050c0907 72
    0x40040c0c0e0030030310076000018210400907645810681e05039251450b084038079900010200c1d02a01c0340710555402c010010000b0802c101e0018298410148029494a00b660207400c48070943d00c18024410302d00f440c240064218092000516490080035442e0000e003008120140240142c01d60410301c2c20300d14018040d00000240300e6207a2560484040300603014a15889005800080c0c6441407400c0c014020300b041354004188c0e10101800041c101141c540726040945c0541c0d04000c190040060124203140e48014008003504001495807081c402c900b011400910a410014210004090303001c1441c1e0390b9403120100401e464841030003e01d0f15110500103561000a02c0300252040c00001c00d0500f106e0003003c4100c681c6516041c0c14050380e401716101500c03000d241159041030403c500051441c0302d03c582c044040700d9a40318a11180076806001c1912406010345104205200e1491121202d144c125280c22a152a020803980168a0083c1c58207002641003076000c00d400040286165 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 704513902 1250 704512652 704512661
    0x60504060b130b030c01030e121306031109010e091b13060e040e06011203020111030705030a0b010908030a030b0604080a0605041a0408030c0a0e1002010c0306081203010e040c1701 79
    0x104451603004002c1d945984001c41d0505106550580c0040d0940310b82c641c001c2c2d026258000c503130400e4812214010144006607400b182c2d03610b0101351900000d0001d00d50502c50302c0620f03003c440b007840c94550600b0010340040c880740b841d540f282c0303003a50004030520800c00100c1c0f101c84950b14400e440300c0030b0090000f801500d901a45002465600300326600d8070b884d0081025602851019005603402c2c00a28007042010b50425025507403243c18007000c0c00900f00086102d01e65541d02d49441c0d00b4101c03c2c0700e0580c0c120820103410031401071800d0060050110468452525900340002c101068401140441c00b456220404034011814400b05000720f0780c01a512852003454480301c040154031140d2545071013903802401c40303d0144006035100700724000621128401e81440545546800c001400600700481000c1c0140d44811070383d40d0303290f09801000b01130101c410207407004500840b100070181c0014800c5044851804020400340200000e0920103080b40e04142900a03840710040d90180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 704515152 1250 704513902 704513921
    0x30c10020c030c012d06030b1b120f0601121505100306080601090b09130327080a03090509101a090f0604030b24030303060d060b030d12060e010b220306050406 70
    0x82014200701c1e6844024400c450a41c8c4e1701140303208164480c102003030354041440001e4040600304120302d145100103800d1091240326030702c81a5503540303004e00006194002c943c40845d4a103003044140300700200040c0221041d510190303001c0e54207a845500c114042c1c03485502110540c0205c2001080d0f036030352500300255981c07043c3ca04001580702c0b080c0c00c41e2503200d0180082c0001f54084805500c00c1d0311505032070040e9442800886250b5260608a410900ca919003240800c41c01c081c10040c81c2410740c0340300e900c0721721b0300c5c0c48403101c0740751010042e41c000ea00002c2132858000051061919900c0c110343c1d0f5404500a0a101e0301d803912454048804c00054540c0c0302505410325040320110700c0e12440381541c0720081d000e9411501e500040c04401d80b841001200e00036152941c80200740c50401102005a6030360b500d0032178404400e030050701202d0321a0171040281140340010f20600c41a0001c580207050708005c0c0c10101403070501e500c00b04441030340005001c42d00300300600062080c1074110100a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 704516402 1250 704515152 704515211
    0x151b010f0608070b1c02040302090a0b010f050a0e0d080403060606080103050c0a030210080a140727060912030314010b07110a240302040b0d1409030c10020c030c01 72
    0x4958035107169540c0c0345144c0c8981c042c1502d003000340382c43c5100c211030181c2550052240250403d038603980028004c5100701ca900784c403560340b4031042c1d00315030780180c01220390038141c1010f501e403ca651a00401d1b0740c0300075107114018004031804004000b2074104880041d60006010403616031207582c02004184288001c0d1000d104507814051541751155440044a40c004d00c1c056420b00325950680e8480001400000129610013840328003080b48035455100d03141d541e03100210700f14411034100c1a08030022440410145074041841100d80000310307101518100c0f088070340c00030000d1500b1000b07044403007403850340385c3c049100000e2451200005803210601c1107000c03040006040303050200c0300507030744121a0191200594105540c86a01c06100340d10802d150142c902500c030304881c89241e0100780300c98841070382d46507440c100c0a03050101c03580001241e006507182000b80c9409940d540c5042c0c02c200600d940c0091010070f81c4004204451200d40d5520017400004c0f080ca8000c0c0011180441e80000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 704517652 1250 704516402 704516411
    0x40f0b01060f02070e060d05070801061d09120309030c011e050a0216060b0f030115050a0509090c01030209040e150403020111090604030b07031103040804050411070809151b010f 78
    0x904078094140342114100b41c1d4010f1180511709940d0003944a0064040751b0450b04184250000c29406c4c008100503103403002c004540645020040740c0316107282da4a400d000000c000501038500004200c000aa104030002c560712521854501820361240c0a11682c556103020100003071981e802d0823402c81c00c560b00c18104002d40c1ea10300030f0400e0b4172502c0041240100b200740d101c80007422a501c0301350400c0c00a05031140c0c808442c400b09085500e400c80c0c82e010114400d4042049144c158007a0780a03040a49039440720b0b0404a4409540f40d003482c101c94189500419004940d8941d5403007d03900c041420101d41107040392043c1c01c0550380e03065509500550800c421148004406011200031003000341000340b4281c0b4544440295200160101d41016143c0080c2c83d8842c01c00d03070195001c1c9009078079155030b880c40c110402080321091103620100d000240064004500a842502c40f441400d841404022110b080d52905912610305441512000752604c0c41c0380400551001d103440051400400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 704518902 1250 704517652 704517659
    0x30206060109120221010c110c190b16080327120f0f04080a1a0f010b04180603060e0f0106050f090403110a2009101a07020315040f0b01 60
    0x1110b120b09402030380301001c4810124801410031890028100c00d40030b8401e03d202e014842c2180c2907407100000400042e0b0034080034017850006020b00f0713500007130840b2181413004008804001848041c46845410840072400154045040d4a42009139038840f06403941c81c074040070000e000c100b00c60403603c03102d00c2200031360089241c00951706240111110703a450408a6015000c5110303070082c0388001c0042403c3c0000500b4680420940d900ca5114183c080400f00d00b8552104681c44c00418034844090a040100700781c1000e01d01f00c0e01610054002d10004000e5480000d015000650005040a1030500d080c07142d0f04c004202280030b0b1070140000d0000642c3c400030808060710540710300fa8098190004140000d02482903c1015805001654510b42603600c0c0c070b0240d01c0e9441d2503418500361061400006107040b400c5030b98400c00d000c14281c04541407049a00c03000c84050707000a20507500140c03950956a0400c424055141d150100d40030f5032170540b5114801590140c0b049483ca4413100012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 704520152 1250 704518902 704518907
    0x504030e030a02130b0d0b01151214040602070f020306010321050903100c14070305131e0306020a0216090204060f020604050a061d01021305010909091a0703021b0a0302060601 77
    0x4803441c50f0020502d25640c0031200f1a04014003c110b4402d034082c0002c011000080c290743c2d405402002c07640c529400a0800d058043c081c10000441d0102d500d151140e1060f05013202422a508650010b40060701d6a005152200e9940d01410780658144500800003040015200c80b03003458208000e511036058090742c0f81a2003500070015496819005078001400c0780301c00e6400002003c0c238a203014440c00741d00300c03290585035000140a60005400040c00b4490b07a5a40403c00b00605910702e203005010104001408841c0744c602004040d550001076070805540b082040300003065100b80144183d99450713000d400250b01503c9803102180620700401103050003c03460034851500000500201c0032240e407207500a280c0340505507040c10302441c469030103800c00d101809081611070101c581e002d0600b400540030020700d600100b4000d080144c1c482c0000e007110b140001030003d0359200701c5951904030003070307003e8051000c20705803441c05281104c410136400115121854002d03000d4400c2600c0e1007004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 704521402 1250 704520152 704520163
    0x27041209090e06091e06040b090c090f1005090f0f07121107060b030718020c150711010b030c010210110c030f1903060509040f0311060a1401051008010611030405030109060504030e03 80
    0x31500d030304211b0004000c40c0d4248000c0380d02030301820586001c0881800094402d134001d0742c10701c030603c80700d00c100281c09151440750009800c04450174082da10f0418078120007104000d040141c1c030000c40300813480f40c6000f203421650f242c20400b01072000340780e0340b81020322035005a5400c0d20541c0c1008010103407400c0216088040d680c000c160309801950180008000e9442402c89400b14810004280614030220031154020000c41c0d60325641140c1e2a2051829100317002d6089109400240a20030160307000100702040003c0360b00013095100003201526154095011940381d5801b00082c1d00f41c0040c82e0302c000b0229900e2003013014100300c0300b107441101250400d0044640110b80e040202e4049401c40388a000c030603120f1f20384039210802c054030850801d80140c41d41003545803214214804032140e8100075014000685000034803003244440103041503410705c90602031000581c11055003441c144225406490040c0080c00301680a1400c0d20041c0740031030341075001809240c0030081d03624001c0741 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 704522652 1250 704521402 704521453
    0x1b0e090a0203060d03050a020715030608010b011707030b010228031706031906090c0b030154020a050a08060d050d0813060e0c27041209090e0609 64
    0x4c0c0300d400c101c1d03074150340c6c9601000700d0400f50710030032400040400c50826904030802103550041a400d00e4140483e0946941666007414000c001c50848000d188080c6510380c8200c0300d207800700700400b46900503420b181002c000f00544100403c1c401c20b81c020741002c05401540310b40e860301c0c4a41c800308641245540309860941e0316400c5400c0b06c10307621100d00354030300e000ca020b8000007940b05140d546d081010300480d402200c03007030004401003200e40001116075007990424000b0425518101c1200c41104644410743c1c0b2030040c0380102e04070069001c3c281442c01802c140c008540d2264408000b07041038010001d1800056643c500180c0355080403600466a1507200d002803030a00d01307114081e602d082e0b004041e004440b60008404020805601501d0468148000501000000482800312000301d10507540d24101c0039040c440716451020810503407068020b0016104c0c45180c2c6e808a0f07900703405a106048aa00f041104220000041070050158500604031554200360f0184200c2c120040309 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 704523902 1250 704522652 704522659
    0x1030507030215040510030b04050c040e061e060313330507050903033c04060305040812070e0a08073b0c0d060b1306050a031b0e090a020306 62
    0x500400040c10102428003c0c6000418a5820141c441c0003258650710b4841203070700041c0d1200c0811025007080d01c0f0725904969100f001a2030103040103900240720502424060003955400c3c4100c1c000e0000c09440e40e003104005200540d82d080c51042c9113030407060a00180c0301e441c4841403e00c5020240301d0340c010b04511101e40034540e0b411170708c00304000b45001881c0c402807040400440d0610f0b5014402428150401000a00d0000b07105556840043e02c0c0c0040b03c00e1010703800840c50412440c002990300702e481c14a40890103a865180035440ea000e884450309515100005000340c4541092180380844070540d00300d0781007070341c1c0c5400c02d030b640100f441242e200c080c007001003540c003142e004000c4051441440415100203907000000034411000c80742a0100000480d10070640344690050f440101010346100741040d03042c50740ca1070b44050750b110305420721200003002c4203030074000d400c400c3c80d400030301d84840c0c10f070008400e003c0e100340d50403020b00740300e120a1000240c244c51613200b524010000034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 704525152 1250 704523902 704523913
    0x90305190210110a12090f120507050d0303060e010b0306100311030105151201030c050a0b04050109060c060b0409050c01020d050711012f0a02121902130b0603011e060206010305 78
    0x101d034141c90007955003c02d040b860007290b01c0c104c08100b81c0715002d00c405c1e18940d91154030500e09581001201429001220303a42c0340003040c1e4010940001d07100059460848108104681c00d203016001061160f000012400954000051800e0303d10061885607005580c80031040309216022001c840050060707503d2058240300501450404082c215041411203846a207002e220017101c10700400c003680201e80c09000303403e081c811811300704400390003420242d0481d0f041504200c006800703001580940c5040111441c800303818000940c00c80e8800c01006403013000402c5030390400d03c2d19001111099405441000075554500d8800d204076484a50060459800303048104011540c040c42d10415540a04848400c10144800004039600400c1101c0c0103000300d807128414844180c81c44911049250040402c5428451a00d400030b0001c0f541282c1c9401d040000d03142c42c900804254940a42140d00440003181034450030f100c0384c02041d40400b10403401d55071044100c0c0d0b40d040900000700540c018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 704526402 1250 704525152 704525179
    0x10908090a09231e150117360102030a0203010f0518340306050406050613050618030f01050f1e06090603010f02040b030126071505192c0a030212030403020a03030903051902 76
    0x595641484c2c82d101a510944d00c0c6108d00340060036600141c44030300e00180c0c00401001840f100d105120010a41520300c3c09a084910140e4036040348010000c000c0340441031101102241d0400000d40c020100d500012581d0301010001402403406e030041c940960314006010a903850008207450302503c952080380300c1c15003030106000550b000541302c04055174000c0040080b07903074140f01900390358440600000f19494038102921220001404000c0c031400080c152034481c2003c250150b45c4024203a40826183e11078802090040084d503420710540d0348003041c0803841020110045040f80e0302918400f14040c01074094500011180711a01b5050740003000400c10407042c540001c86002e0070b41800303801e103030401d03001d0110750442c800020009854030079a0b15401d15141860046080a001080600c40000004c00c0100d01540030192207004c01e03d410709001074040007102e01565000c0c1c031580102c0e0352841c0150150f0340600003150030703002d4000703103c2580c0350f000041d0340d495800404e101320084a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 704527652 1250 704526402 704526451
    0x15011a0406030b19080312070f0915020a081305030f1203010324051005040c1e0c0c03080a0c0311030a09030f06020c010908090a09231e150117 63
    0xc4500c64002444ea403000b403030400042d007604000c0400f170010b1a5111b090341c002e4103860300c0c01803541c001d111060072545a01a40800b610054451907168440c455510320410b03440d0400d0203c00810101c00029400c2c070040703607907032650201d07801034044a414902c100203007900d42c9403009944c115080c040c80100007042c0220301d15012081e49410310129241034a889405a942c02c94100c180240005401c00107030070640b0030076210311118600207a00e007401211814807909200448003c01442d80d4000007031003c0480180001c681c802700d0242d59007800031028100c00b40c419400c2d004900720080201107520040200e8801c0c240e9540d5040201e800c56542482400040c8010340e0520303402e10060325545000d1041c81c588034012034005c0c5c0c452124108001c240110780c5c011414503401e046000f68840d56180400c0c640400f0111614020740c0c4403480000b016204040c090900c030183c0040c002c0000c1e10824551014030282c0c0c070140c00c100303c076801902c0b50f9000c2d02d50355100d40800740a40c09181 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 704528902 1250 704527652 704527661
    0x10e0a150522060503010e060423060f03030c070f0611070b0304030c0b041a011a0909060f0904030e01090608010b0910020c060a17010e0106020a030305100f0815011a040603 76
    0x342c5480c10980c1e500884040507814032880c0c1001020a82c00401480800107240125038008001c40d0107000201c20028040c038101c13114440d480c1c6004c41c580120f40c89079a140341c480c078801c0c4041d0480761250707030304c50800303544031010701c20400619030b84040407071454802c140110789092600e000b01403591034210301e0743c0903600081c010b500f0032141421070030000d0001490280a2130180c0c207401883c002040c04888122010b9200c49050354159181044505030310080e9448220212074007181591117a020032400300c680c440f2540d100001c041041b04040e000f1100c2211a4000c0e62001600b5449181c1a06c2e51403082c010883c05c18014040d203d51480c0c4001048042481031060b542910707010004903055030041c00061000c110000f1601407120700c2295018010700b00954440c107603500d0700310702075220b0158a03070281c10980c860000603580c204046401d0b0041c1141e005011003203580e0a182a00c40420b1090b02e24000112030000038040c80050f21100780c01c1d01c85246900c2c16160030030035402070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 704530152 1250 704528902 704528917
    0x130e060d080412050c060c0c0f010e030706031a060a050403110d0b060f01030603050d1d0406030f1e020a090e010c020105040b01181b0c05070801140a02030606070b07030b010e0a1505 80
    0xe1088a125040f2a10f81c032000e8200c5e0300f00b281c000c4c41c41913542380c00c000e901c0146148c0d0904014024054101a5800040e0b10b401c5840c0e5090004002041c202c24903000e0030101d011603003006001490305455540701d40140704072805a101000303844408010045c00c981000c41c054000c0100341c001c03801c03510740403119005601050400003019035aa40e075960401e90903500c01c00c08030f401011560000031408401c0400b0f900219010485103055907104a5402480d04014280910849081d811203080c1300a988032240c00420803080150f50304604009041e83d003521518039402c2210003c0b00354014020603010702c0c2d10a01040b40740e801c1a0740c6030402410103100c0d1600c2902c8000355000001400c80003142e048240d0342d000543c80ca2400c20313900d00074030341d440442260b1401801006040408800d650020003403007002d6600e454580c00510540900c02d4013404410480e410700c01c101da090f40c40302040d0102a00d5901c04200c14000304003000701c9501c103d00c051125085059000c0d84500d0050554 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 704531402 1250 704530152 704530163
    0x102041d070504030b0f0c120f010512062517010b2109060403080703180f0b09160506090d02030102160b07091206020309010e06010e07120c0e040b0f0402130e060d080412 75
    0xb0400080f410016016059408582e0507549c9801480542010803680310800c0c05e04005024500341040612070302619040140020f800c01c0e02c0704054603110750b201d10340c89004002c6489084d40c440300c125110354041c0c082039807117008401c036412075510b00b00c000034030504800014202d01c0e51217407001d607803048000309000205552000181000614061006c42003070080402c42c000070340c1481e08d8460581c016184680d240e00661070045c81251500c114004d452069a8940c0c0700c1ca141c0c0045101c10000d550025415400071800154800e1031080104809004c1c005400d1940c803050b406459103030b86402542c0090b8940110b18002c20000e40086420140c08000003540e043c401c034010b801d00c8020b800030301442e14074a050000290740b041e601d40d03040003407860801075030a990b00e0207821600f15001682c000c2c0e458032a16001a59200c5146004520141065540301503c00110000c24542d0082c511030b00c502d00042038a500786581828641036200484e145003504010420011421a20080300c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 704532652 1250 704531402 704531407
    0x1009050607030c140a080103120c050d050f040e0a0506150c0304140a0510020609010f05070507200a080127020a0e041509030518090f011503020c0102041d070504030b0f0c 75
    0x480c010b136078005d064000d40350342d803620a54110714240400c4840c80d54214204512440c55002140d03011030070484201a6040c0143c2d101c2c3c14000500700c1c0d008a0b40f00c82c08680342c450401040700c0190300036600c035440480c1c00c1c0110315a0410800c0c0c1902483c801000d05d94024032051214010308401a03200620041141d8130256854002908070744440b140308005030040c9041c03040e80c0e6000d000351903d6030300c003480500c150b10381950700404d18090304001904241c048044410b41e800c1d852106189050040d201d90745083d01c0d074810f140a800055030300070f0340380140c01d00200100228480c070503c25a0080403150ba0a03c6d2108061110300c01420650b100b00c01c8004140d103040088c400c0c0c070010f13031081e228107444900c1912110002c02880514600441c0040c0c100806100745141075815200e001c00300d102c0080360050201d0080c010004803083c00e610024020441c03c2c02446040000341850481c1051561040300885440c0220300c0020131aa1844002c50040c1001306111940100390307080450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 704533902 1250 704532652 704532677
    0x52406010e0307241b020102030a0e010315060207060f170402150f120f090c0f1009080a0f11060c0d0509010e04180506090a02030c040e1203070306081009050607030c 73
    0x2140e070028401e500c515040481c042d165068001e0203c60420b00c05c00c0c0040c0c1d855003940c0010b510303031140807044020080d2005504400761702130342c40b0a00000f90168122140761700c0b5100030f96076140a0294801140c015004c03104038a105850044d40c001a03085060341d00e441e00d0b8248208484500c042c6010510284204800c041c848406070128803111003490589040004812510304c1001d400a5031940000690050584038405000c0d03600c0805d8405030340c04242c144048541c00c3c101c0c3c10444840c09a075070050107001d01c2c0c044080001e4040c50741008261003403010010144500c0c9015109a040969041032880c003580c050120800107040017070006465600007800c17036540c1003802c0d4181c0c1d01d10b449401030100410403207520140c000c0040c0b04d020100d4000a5440c520b40008a03c150b45501018407141d00c1404140700d04103000000586034100094080c0140045000300e40c028840c4412002010200b402105001504003010301516115032004402400755036041c80d00703102041c080c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 704535152 1250 704533902 704533919
    0x318081903090e0c0d06090902030303070c0804091e0c0206070c0f1104050901020c07090203060a1a090405090a05122803090210020a1b050a0608040f0b13052406010e0307 75
    0x11485004d980c0020740c1d8520610301d032041142c071030741c1140c510a0300d850000c0340180c43c00800c690300042c1d18205500003264500d00f0700004d200d40e0700400c42c211708001c1002c003100074800c41c0c45440110b100d002c0c00350222102d0304a13510903044a0410000c1d104000d80c0c00400c080340d08a01c0024002c1100c20b41100c4030102203000d9a40c147d541134502e070b50000710061110f50611103103000d04507521041d8550f0030200001004a0945d0040c0c07800c0045412101c880b4003da0400c071449150050000e1103903140010b8040e40b40c2d6040d50054a86010741c50303201c0c0000721001c040366a20036078015851314408845a058501082650b82c403002d05988074101c4015a9504400c1c0c07040004680c0104038a6405180c01155455501e884660204600d0028003144d550b140880c0203480035485c20a4981c0d0791420010f00141c03140c80b001e4100c00500007401040403081d0710300d90049000c1d004480524071680e120901000c00e00c440c81c3c458880c41d5002c950b16620500a0080b83d80005007140c642ca0345900700b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 704536402 1250 704535152 704535179
    0x8040c1e0603140f07320c010f06050906100207090c050918040312020c0f070b180a120201110717010605011704020918120409020a1413051c150504031808190309 71
    0x1b5801c4840000c2124212580c090103180b519080d4400e003409000e162002142141030080e01c41c1e48980280902c00d00288d00c204145002050710b031109001c400003000015086900500b00c0328050702d00c00ca01040704c001a44d40a5005079403546e82e1020aa9559508038001d4001c40c3d0200401c0c0140008421103600030400300d8080e00004c403a003940d8404503421a0509440075a51070300800c0c0070403041040604108602d44526020b0900150313103601c514416003001443c0d0400085205c2c101d1000d40d000d40b0541c080401d8803402e8a03040e0201281c12448916554100d4000b9400b10b07009000840d0303911035040000c800e840010884100480d00d4410b510b0541240d00304004250380031070207021590f400000681d0152886084501d000034041c01c21201707503014000c031030044c10502300c08015070003200003205450f41c1154003e5485004261114003900e000c0e1b42c190000340c182d400e50050840c07003001d034400b00d40e40c00380142541c5503545003c2d03008001e1064158140060401c0008407e01304800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 704537652 1250 704536402 704536487
    0xe0106052a0d030506030a0206030105150405150a18032003010b030d0804050c090603061b0910020f06010b0906040909021201020412031202030c040608040c1e0603140f07 75
    0x28150a00c14580d000f03040314001004203103e03921888140c8090b13128901200d055610944040440400b0390081007503170f1081d036101582290040000400d01541c83e005000440304941c0e03059981c0d41046406101c0550b1408054603a1400f17580d02102205030300032082c18000080c0c0046003840404001034104480780f800600072404d9002003204001060000b03e101100803101c110300ca00b450400300fa40c0d848004c10711142c0544084482015160f07201c261640d100c0300504045007000c0240d0000d4079100b80c500280303a10302c103040c0045029140c040035103500758000f400301c0b030500345042041800f5020b00c500a0b6000803114030006d085c5102030000b00b0240440c14994582d10401786402405100210380c04100f0502c14414440e406500201321401c5800c03600c2e1803411502c13142480b0b0b007403003c6a8041004181400d0400e2200301882141000711401510100324080c24880c0c940c942c050201c0c0c4041280426800259105000d180e4482d4894201500c13001260002c65001c2020f0b82641c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 704538902 1250 704537652 704537737
    0x9151b0915030c18030f0303070503040609081309050a050402060913061706010317030f06210d02010608120c0607031d0d0801050f01030b1f0c051e1203010e010605 72
    0x320410134924009150005041c00c1c2e0041480500002d141516070002401c4102085400004507007404443d402c00d070400c540180d0021b50311000300c0101c0f04041c0c16407054010403420040099030310074061040511030780e0050900b900c1d04603c0d00c10840402aa50030b007040c90b658540d80882c0c002141a1001d070307800c071208000d20940d41981031801810080040740e8021010800401070150300c0e141409820003c195a040c00303008401c180002c4031209251500254802d0590741c1b0009941500490101c548070000da40c1080c030302e0758181400d4410454210919071090002c0380c0380305d100750700881c44c0c02c908180d1500d0ba80c1d0410201410420144100c0c000500e54100601040c545994002c02d046004d007020081180c0e143c001c2900f0051000c800c0c000700390340e0492179192500410800e544141e10409817100101682007011501040c2480d600c0c9900c16041000700d0083c05800700c80c103807a401d204100c440da10b000421906603004002e0f452648258406a01030404440c0a2441450900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704540152 1250 704538902 704538907
    0xf01060b0c010b1e0d060b0d05011505120604080d150312020c120a111c0c030c060306030c0b03090a08120601080a0b0d08090a0e0c0309151b0915030c 66
    0x4181c40c25111803842c540d202d10315607020025001101c140390042003c041e10183c0603140340703040410061081414260f040b9082e01d29104c1000782c10341c41404c4048403580f18001c11602c40d420300c8804c1210b01c00040d410b0b0f0000000c40d01203400780380030340328443c820382d8007003654600b0a0450610300c0560b80100c840e9400d00b0108038503139030140041c02040c00240c0f0390120341d5a105900550b03440f130060000e04032590788403058245454105a040b5005418007862841c0790107890074280c001e204e48000d0710b002810301d030042580da200e805031404482e00401c90110700703400c002002c1c0719503001030b18401c0380c0e200349540200001c1803080901641c03200015510070914090300050b151010081c083c0c82010f142001c812803659134440e00103141074015088545441100010880044003504421142c150b04000c0100c0d1444410086100e44600e00542e0098079040105858031031003500c1c4040004900701c4598400c00500300508401c600040111101e0401c6c1441d0003c25442550300041a5000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704541402 1250 704540152 704540167
    0xa0f08041703190309032a0204050f090616020a06061409060d0201050a0c020a171e031201061412190e06010e0105060304020a0906090510060c120f020f01060b 70
    0x10103420030780290508026500c0e1000c0100055501c0901e1080402490360300c441a00626200c0c4000105040c0301c081d03055882005100007a905541f282801c0f8811410840015000044035640d075001700c0494006021030f89039603c012401d0030606450004510420316802c0100d03540c2d0081200412038190103107170440148050107007902008281500a905044c011001030743d0141c1201c0100b4840c1c584804030407040e2001070300202c942c1e40030601020454802080f2408003080c02201e0480e4050100c0f0306090000910b03480b0300030042420803041c00840104803081c084d0107414011700785041300354502400400030440700c2e41c00b510003190141c928170b60061409154450800698803200c000e00710380d0715110aa11210f50140680e074000d002c040040f90843d211440900040c02030b455087c0300c01902c07005000d000300720444103200d03111540f080009081d0700411390302c05020341003c40310041c0c52030311070b00f41c542e9007900304400118402d85440480c2d0003003c3c8a50000340000c500180c0e0303258407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704542652 1250 704541402 704541419
    0x8071412030a0b04180f0615030206040e0a0c0804050309060a0c08030f01060f020a0519110306130c0b1207030b24040807091b0f0302160807050105240904050a0f0804 73
    0x90000400d4500300c1c284c0c2170713000452010181145500c0e804480454000c402c59030300d000c080b4041d40b0003034110f6804100404c80010f502e00b034600c68480394000300030b01a411070084400714000e0f10040c08a800800c007020321405d200004000800c0709040440000c42d1f50742d580307522035004884080da5201b80070014045079502c5003002103507003440c2c0b0050003004555143c00e034a40010303005881ca000a07912105013000300351290064076036001030945005280c00220740c51038044460341221001e11420b0003080400c45802540d1046241a0f205400c0f5039130001d003030300140356810f08141e00000e6000d5425400c0444c61103143c20001c1c011100e9121490031000603d000d41c1b0f50440181c40d402c208040700c031003014082c60440e0161070310306140c030f40e100c081c000e600a12408180a004449070004102802003d030300800481e0320440c02040944e4403101144400c4110b682e02d02139502801041601c1c41c60440e9000f034110380207905031a44070015640c0d416220740960f9044409010103d010820f814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704543902 1250 704542652 704542661
    0xf010608070f1b1403120717010918020402030a0c1209020904082d03070e030a0206090f040e1509060123060319060f08010c0201060308071412030a0b04 67
    0x241820040c1090030186400b5200c1d90400e555042040b03d0f09240c0031004841d04030004410750028542c0300a003040f42200360300e07035201c5040700074030340840380210b000b05110344104401c240310b070640c900d041d90900010001600700f4a03802e60a05601d00303800c1c4096510340c0300850003114420000200030450001c080c2032102d00f17180d40501d442c6841c00680240e150929581e9000e0340c0506295030b2140f00b0f84500c010980b0200c60040c810304045837412034070009600442c0102415203840122803007031801c066070b88880140094201c4c0c030a11035088a8201103d084d01c944c2c0c001080403c0c0301e003001ca0047e180200158400580740310450a001003d0030a00c003840c054840700307498040c3c1610540c2c424001c1c601d211203440c01180000009440b68403104244500070b1030101003404015561280c0d036000503107a0295130b225510340031032410064014401c180032a0750100e00710b402c0100b103494070800701780483c00241d1035008410102c24962040c01c002c1d407081f00019070000f15141d0120a01c1300300c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704545152 1250 704543902 704543909
    0x906010e060f030d03050916050a0e06060c0a060b090a0509100b0f0904050a020906190e060a032306070f1d0303040b030c04030657020a05010e0105100e0402010203070c08060f01 78
    0x7450503206004c9c0d0f23158000e1017130aa8060f4040c0e90300301e86a07013010540d280301c0c80d0b401c2246805010400810402203404c121034022080b506ca14503030711030f6005841200c0c404c2c0c0c0d403d1219848004601503102d415009070032881c90082008041c9507251012a0303900700e04590403562500040040d00840c40c00e0181a078205600f40c81e401d10811080002c00a0305074180141080800e40c07200140c40da503582d840060155501c000d1148000d101702d9404903100c6c00c1e0020503d5203004610020704810f208010780e0418000365070b40c0c0c842c0f6036400810001e4008580c2000354060200700004201500003100540c020003219040c0381e0795600e1820405c0407510355814450080040c1d410540e1401118100c602c01074142088114841105e51001c042d01e041c0c282030005490848643c0840c6140c006c50460851402a4001e11000b0f00a041e80382c205d90040300d880c804009402e200b80040d540740d40c1895401481801101c0c42c140b20350f01d4043d06280c4992110340207500007410803507140f064142c4107004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704546402 1250 704545152 704545183
    0x10203042720070f060915020a110309010903080f0f040e1b0a2c150901030f0b030604080a02030f070c1403010902061602060d020a030615080906010e060f030d030509 73
    0x180e01c846644030310540b0f00103400e104419002c401030100b10342c030102900d07920520071800b600041c0c0340030029400c01c491010205041081100b06400044120744050105035200c224460031a500c00038241c1001a2500c07102100b4040356450003100b000520103031500ca00407210500d8181c06503c1c40c242c0540259200314020700025030071982003c401201140e600002c00c0001000d50b40c2c0702d9694206d004250303880300c50281c4820940351544d0003011418402c0e0fa00340034450000400c1403e4405803003c03660164040790000e4045541c0d000a0300c980082481a83c1c80c00d180b8200e00700d5250006141600c9100c00c20200f00b052104509408416050990080c0700c9800c158001800e213010703201001954040c00c100d00421942c400048961280da110002c54485002e00002401004c041c09068181c0d0203842d0140c03002401185920b11410b810001411107a083c0f402c2046011006030a10341c10154080d040306803030790305000c40005500c1d1a41c1c00501440e0166609181c4141c81c00714920 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704547652 1250 704546402 704546441
    0x23060c070b0703090809030703150e03130b210f01062d03020915122d06042012070f0f0c0f0c18150501110312060102030427 55
    0x503000d01450342d40401e26080000c0d01000f141032103c580d10914494030780c03601602c00044104003c030749181041e00d80c801810480350801640031aa02d01c901d500a45484d410044108100b0684000400c1b114080140301c42280b591000d41101a40b011350f400d40e6001c00541c01401680e91201102c504908030742c440080d0b118030b507000e1841a0944401350010183c00140b00d0104d900d49100300034003181c00910207555175040460349a0860700c1a80e030700803004400c0290082c0411980700c2803000101242c004501d42d10364408000c01048111600c61100f00f0314440f0241420150016140403078898900c0c440e240340007440100391004680c0d8030004e0094117086114460740c403681d850689644106074002d280114100b1041209450340181828010080070030790039101034000080700d04803842c450102e80d40720801034a14613409410003140c0e038010b001040703000040b808100c0d00b114060060324505178031450320b03800b42c0301688841b0000364035040c001c1070700b0740c11885283d20310004400f0003103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704548902 1250 704547652 704547667
    0x304201504230915150a0507021008040203060c0304020a03020d0302030a02010c02190305130f081e0c1e040609050c370f110714010e0901140111030723060c 69
    0x440d0260301401c0d144091004c41603100158580d03201c294841030540035025203e03641984020071a91215100301d000d0b50f407000300160101d0107405000d020b036900a010342010366546c10025426040144260ba200030822000809a2107080460718080d0080c2d000c0c603178030301010f14040e00b9640407011800c00c40d80521a1241c8050301a1030040032241d242c5415540c07180c0180c03074440b005045420822811200300c400040031078001411448816400c0c04d164080841c07203421540b5a05201e48003504010a00d80c511844044c10410410080000740001080340d2540c540c10110750b0115103814003400d000590000d0b0113480d83d03001000a00070481841200501360805416260003801d0b02c05110150864101e43ca0080c50700014240214048460041d82c440d0030081030418650603902160707000d810f0039254100480c0030350507500c10107403102804100e10011200405103103082d9030b80b400280b15070400143c9103900354907000c0903101e0420140c0300e2107000c0e03420800090801c0301c45080400154 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704550152 1250 704548902 704548909
    0x8130b03150d0b0a020a02010b1009050102100506061c1b080a060e010b0f0a1b0308100803030702120d0f06031428030e0a080a12110111030420150423 66
    0xb41d03802a07604401607100d40210380c00340d004d0002c44448640c06020102c0c10100e054bc02007150b0102d41090b400c41d03554050720b000010841e5015120250070070f00c20000303144020762100e55002ea400c000480050b81484820180406009520546c0000f640e102d062000c41c204a001d50390140103c0124240154540b10610b105446a6010584091804a81d0b60103440c041c1c2e41c01848900750384001a020030341450b0040800c0c0086403400c50100d004000850305074800800d070781c03040b80c444e00184102c130a4003040140702d0300418641c001c603a44480c5600003c000720301803080254441c0c0860043e074000d0500351400c00b142c00c04010141ba038648059241d001195824080254150a10b50380e0510340c0300120320400a15004090340c1d1281225541c104260010350a60b00c440e0b0f43e41e0540103101c180141d40c01e840e9140201103140c401440030601049200d42c0140c0348024000343d03510040b07915804940ba50800b079050f2000000045020002102544802ca0342240e4440d903001c0c01c0d48450001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704551402 1250 704550152 704550173
    0xf0605031506090a090c2c1512030405060d0b0a0801090b131a04030503041205030c040b0313020a1206110f0a080714160212010c0f0c08130b03150d 65
    0x1003072141d2150008614144d2003540041c480315040000d500c0f869846140d0441510395041054942e2001c0e400011a03150307110b1203550184100c0c2d00300c043c000b03181c0c2040000c405400c00340104540000c020000f140e5450100070701806040c1c1c14007184c0c1e48082401c20502008560025840f40d050094010004462079003d55008458079162144644182022007810040329064004000d0398820300092541090145119900c00c000b0034203503548100d4211201d00082e24072089890f0207000500644404001840c0c0c07100d06412030380ad80c0340c3c082c3c0000d09681c660f0341c41194288030740400302d03003444014050000c0141121784154542642c0b07034240e4516200755440e40e0100070300e04010804881c03294180d40d032081c0030811400e448003065020740c1d91180c0f00c0e04c400c03131080756034407017914501006015907034001d520340d100c039021700140c441d050303607442851403003118165010821110110704c10b00ca940068090440b00300e4480c906600301c0da58140007106218443c1800500d101c0001d0400c40301c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704552652 1250 704551402 704551411
    0x2007030c110901061137061e06031b08070b0a020a061b0f0e0603070305180a0302060601090915050418060207060221011d0402061c0f06050315 63
    0x40120541415081c107503424820a0305450b409050000009800d07640040c0b41c0e41181050000d56801d410705410402c0c60303a046070040c00d95402a42406408040e520507003408190151030302150040e90345221161500c1c2c009250746005a0b03400c814400c0c4038000c010740c41130441c0c0306071042e0303900d05080580d6500d844522480c80b500000040d0252254824050000c2c01d42d807001091146142d0701a400e800c1d807150301184400110450300301d210180c0301c0c401403031900002410f814515201d85208a000d410000e0843d42502907a46480301e030000200418015035003e0381c00761640d0f0501c100010a05086c030750101e2591802c0c124280d40222801e901801210011240000c0503000b11800e14894550742c003010b00124408a100410321541c5d80040c50060b07040a81c182c0d034601c07207102c040d0f4112070a0203515100c0450303444900502d604040c0d0580c200d0700043c0f01904060600c2d0040b0340d508240c442d101034143c2c4849082c200d4241c40c0c020100501802c50140c40328009206100160200007003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704553902 1250 704552652 704552657
    0x105060715050a06080d03060b0412031b08030f070c03270b040303020c030c180f06010e0a03061a04110d180203010c1d0f090a0e010609060f0306200703 67
    0x54080810007550318010701c10640c10002d100c6490304412500080125101c1e02d032407400348545140b602803107442018152001002c07198100350415121106504140c207044003880b01d14049508966021000503a0440c031403041969286442c92440000510191401051202c00c40680e0002034010402c012540c0701c0d8040c802d804500506450a545425800801c5101d4009004414180e01107500c400d00f1406904403000c1c1515002480148101c44c403950745075114420115500030385901c581070b0800c0051400e08902d01c0d4031030000d00c0070704003640110742c9181e45160300500da0002c01041004140300303c408200e40301e5103090030b020030311500881031011b951394510a000202c141e0581d14005401800800c80030650400c0648140c041c00c081040040c05001d04007032502d80114103032910f90000e885000240c48200e03815010f816203400e83e43c0e003552603401c04140e554083c4203800c01442030401854009181d07041205c12150104480b4104550041b0042c5243c44070f07804841e045545403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704555152 1250 704553902 704553907
    0x10b0c19021804050c1207080610060c03110c0a0e0603011b230d09140609010624110d0906200606060309100c02010f0605060703080103061503081611030f0303010506 73
    0x245030540c10205c02a00c0b0350350151001302002ca05080001c0e0700d6045d5040c000889425445072140c3d201e03440b050340f09550010b10041e48100010348148801320b11807000c2c40c01c0301c00986800c00003035407824054001c0324400f2200e01c1040000c1c9001d002d40c101c11010141c80896540a40380c0042c1003c81c030360344842c44902560038046407010020115425104441400c0100c00c485140c1000508a03803034034040d6510822022032205a010300c5521304030780c00c1207204c0c01c90045107500741c803514401f08088400c0c40309060300320820030401d10612074403131700c01c1d41c0300381e03400341040005016170040a00c014540c0a0040c8490f4207800d000840c43d40040c403c13641d4940b26511038021510b41100f0304841e001c01800c0c004014042c640541004903c18007614007881021b40707500034041ca42c002e403c0081e0004000c80010408110a40d0051288042049148205a4032503c1d403d05540c400541e001211a100c92414103200602d0b511a150020403030280181100849009a41e80818010217200e140f00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704556402 1250 704555152 704555161
    0x50f0a0b060d110a0e010915030f0209100c0b0a020f070b1503100e122704110403081c020a0816030b180604051b0d0e0f06010b0c190218 60
    0x219000d503911100b00070320074040314428155071000c41d04101808804598020320381800745d0300907440c00b025a00381c1c254402050301005811005001111000800d10b0303400c0004c5200340d2614445000030b0300603500c0303c980c400e43d10714155110050007481d20884502c181700c40042d008a500480b61801d030803483c01149170f215501c1100868000c4030031135500d072146881001043d003950304000305c1d0f15518800c0c1da0841c0b60040a1480b20700c10070141107072420100300c4c0c1040755009040410042e400c050030008290919200070a031603405030b0001d035402c040c0401c010454141d401c0c0e010030781205c03150041d41080e04440014081d40b02c0508040e220307508842d400c03030622744039501556901074000c04007544c40020448213811008207540301c500440c20080021010001100191f00034858508007500c1d04010000c00e400500c0b545454400d2801860f400502d0300c0301c2000424042c004615400365203041d040005450044130900380c9440c91280c00112380540d850044010785094070b0302c0000c03020750381d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704557652 1250 704556402 704556409
    0xc0212091503010e100501030510260d17060f030d05030a2009090a0603030813050f070e060a0f050607150e0a1202010e0a020306010621020406050702040f050f0a0b 72
    0x8401c0309868103094040b000140d03445107050f03060300a0780f8100c688138419448400450a4850803104a90540d40311481000060148100b501c480d10174070303401e07260700260040c8440c20182008500c0c40043c0600ca00380389a1034a845a00750481011500c1003640114440440d8440300c4544026090180c0400001e04100c07460b001580e028580010103014550001d085003503a400c42280580030b0b440c2c05001403030340f42651003400c0a40b509030300d0743c81440d6110008003416102c01481141c403401240d000c555001030800101d4054400d80381c40118524056040c0444152568007400e0882c8019800308610748419007200d044641100000480c5085040e0b03450107803a6800d042070403071040c1080e41045c000c4400201240e85c00769402400030847c50781e0f44540d11811110003941c550007a03401002074038012045000d1622084071902c0b80d151801440c50f049030496072141d00811000118142180b915115a00228181e1001000241491107001c0b081c8000182985190f650714483c2d901e0580c1e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704558902 1250 704557652 704557669
    0x21b010b0f030f1002092707090605031005060c010b12011406010207030c051302120406060303030506030a1509060605032401170c0d05031e04081501060c0605100506210a0c021209 79
    0x4110540d000382c18406024030380a0403808c0f103034080007030800400403e441d8422000c07240110551400d840711241403104110b1154421804640c40d503503031b15000185074883c03e40c0c0b200300082c3c1d1800003a091b05200400c10820200901140c11900034032030a0001803200001d1505407001501c528000c500d43d031404400034812400103282039003a1074104000c1062540103481035901c80da0782808240c480c03074241555911090001060401444481e544001841d840020020301070030001c03d08076038034408071b410040d142c0c0d03814a00340021860480c407180e0342d4070424010010041c001c904074146842c02516224036940541c4144044400e01c01804800c005440c0302030540c15000500d0901c1c410030003040ea215100d00980c9000324041e5440e5401080c01140c100c07034658841001d00101f9907500f000a03c001040d69000d80c80f1400082466110301c0003801d102c40e84c2c40088203410b114213245074080c50004201d0060075081c00190400b070f40d40410840040148030710281e440d8001080096a0103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704560152 1250 704558902 704558929
    0x13231002070924180b04061a0306060f280c0201201c03020a02010608010902060726071a0f010b0d200c07182a03021b010b0f030f100209 60
    0x80b10f2425010030802c02e0403860340c0011010704400c10810101d50144019903105205441c403036031000c82081c1a40070840000d540c0b0410003000d152909801150400d542d40201c0c03504102d10900314010700d0110503ca19800092050342004090890307164002000b91640030119422800d0b45e102d4065840b20400081e02c003103110342c4000442c10540e2000034000d4009000f04001907090840000c4d402406220706880150003400c010716205098880508441509100600c05c0071044044880601968050700021f8803680c1d10500c50076060155070351145000c0c0802000000f240010865510141e0071146481d0f0b540c8004103503041031031854003003040c204940890f8080c1c0007604070204140410340c002075904461a4001c03400303180c1042000ca8515030310003000005103032200b880698400c2e4103440c540d181c82c03801619084160002124200c0c4000c007666207a91100440b90710703823401100e003440a51066004044801140184075558a4899200362140e94005445015511481500020b2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704561402 1250 704560152 704560211
    0x613020f180d0c140a060504140f0109090501030c06120b10031a0a1202092809080c100b0406080a02011407030c2103060e010302180705132310020709 66
    0xc0300e541c0c02041c6558013080307507054418100e1120101e01d10780110240e40c10f88141d104100c90440880c02403000c51140300300940d041c010524000100d048150007128040d51003140034000d0b143c900b240140c08a505061804051400d048044446071106410301c083e510321032402050704010741c00c2d602c00030007400f21a250014040e05001c940c0214008902c04040c4c825900b00c86e840e9280e82e0030408540c91071403403002044c0c2500f021540582590803042543c0d02420000b03151030040e000c0c1c02d14218140790980e034050b44981120096103418030600000305815405012100c407a580000c1100403040c0c50b5000d21840412f103142070501c1603071101c03400303030740f0104051820340701c5c0c1d82040f107410182031920006800d00340046646030200340b0003412203a0140c00d1000c0d880b0b80f00001d00d6140002031101003005010f100c45550207020b0408500203005541205030100005101c868666100050f581c0c02080c900107002c000c103038001000c600b16a505800003a107006610349020507642c0103190b1482d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704562652 1250 704561402 704561423
    0x3090f030308090c041824020412050d0305090c0d05010e060405030d0b011b030507060e010203130302070801020313081605031206041d1e160602060613020f180d 71
    0x20990405542c60084a0759000c40d0100c2c01294100415115580c02c8207407020840f0140da000a1460784415016901c5640c01044001d2070050200481e002503010000c1c00711481d05100c1405410f01c8484010001031030700f03011600d80054910303920340740500c00310300965880c00c4c6501840020f607c92401d4a0702c0c40241d60441c2414200340355280c01c001c189078040ea1500c0302101c844e602071085010440c42a641d1102003005a46040e1a07580081c20241c9000fa1104990b80200b40c0c207100a42c4140c5101044000000803410020f1605900350890a460f038410406e00c80c0304200015861215980513b0850380d58148401c032041c00c5058420081451001083e01d421845078803640700d1007100191010003580100728044080007074071081060135604031128101043c41d604800c0d070401011841140c00c0c1e94a4246009a040c8a90b0301c0320300140c03c844c050222502e00307201a000902041e06040d4200030141e0800003151068002d016a040c2d054240b000154850700d01c44c0c400c00790041510b14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704563902 1250 704562652 704562659
    0xe011a1008220f0b07081b0c0601051c0f03020319030614040e0a0b040c180504240e07080a1101080c0d0b04060314060103060501081b04090503040528050a0b120403090f 74
    0x2400c901c400c6c2c0e291001c1c210121f11400e0004601816501040f460a00a060304e918100c24420715409070186081412940d6040d440490840824211901d12a9006546e607a10341c825010b145e580c1018010105410402c0400000d03064412511141404036800100281c01d0100fa601c0c01e44103480061480c2c98003010801070103401100741c011030300700d03e0141042c081e507044140200c0e141140e00805070401484082c00c00001c0070198280d07055030440c0040c184015040e160b1a00d02c00794403000c035030f078080c041eaa81008a0300385800d820340020b00b000b00aa0524400700540350080d8a182c00251365980030100e01030361541c0004000311340000c0404075000c2030012954542009000a0301c03510b051500000d072400700001c015800c02e20720611030745840390309070402010b803c0e0828166101e1006220202e500d0742c944e800c0302c1c244105400603903500000030441118924032903020034803a0748000c608201084401d02211410a0810b880d0310706560341c0d00c3d091b41c052003550407082c05868603c0012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704565152 1250 704563902 704563907
    0x120210210608100501080a140709020c0615030d09061101020d06080a030906081506070f0206030f1e0c0f0a02010e1b01080a0209030c060d0e011a1008220f0b07 70
    0x14410799101c0c4041c1c0f410355001c05084425907100b84900e1075a07038403809815010901000c0d0041c1c0c484045000d0354416a901c4682c072040c1d0304032007040d001e190804002d000701c06800c80d0550100801c1507028090b1059601405000e0012900c285024022142c51004200c0020b6040310119001500104645500c85113160350315412400120042136000324042400d5015155a52203200e8150034400c001c0c00000038064560400a02180c000760480030602c01a540c00010f544102040201c0301410b24000c1c001c1400c007904058a0400c0140074414032a141c01810110780b4041c58007502c075581d82858200c04c90040200c800b50b0810760003203000303003651070088a2680842540c02d80e1a10126242c5001c00000ca1007041007a0b581a80541d10320001707400c2404c05081c0380203500d070000809000823176001d42074500c02d59025841a00340740d640419860103400b05400d4402910780703a640da01c0c00380d400150001f00b00c032000f01300d40020000a020401084d041280c0217034404141540343c02c4c08a0003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704566402 1250 704565152 704565161
    0x40b03090a06091104200a0e010c231902010507060207020f0d030f0201060501050309070302090601260f010b0702030a0b0c1608040609080d080406020a030e030703020d02010b01020712021021 84
    0xa0034402c500b4854202501000581d0344549101c210821500d8100050000da40b0708182c8a242410b1181005042000c90bc0c2030310711885503e074680031a0f06084080240c64240491520382c000480310f02212000541d80c4501510101030740f104005a6400c55400020005003041d07052075032004190030104100740d4440501440100650003d10900752034100540b13607400104d95110f00303984003200800262410460203900078030181080d802c217208442d06141c810ba4903030740026440541c102400b5408031031610090040800700d000c54100459540000d40b1031640040c081c150580d5038011074078440142007100c840010280f028842e030a1507260540850308503208080204d03482c440c00050b03003c1e0216407440b180c100c07a642c0c2030b01396940703540f514020b41110030000101651107131100002078040000b8610b0070f01a40040c100429400402400d46445200003811034002c8102000f0003507480001c0c00919a04840a0508081c005801c59944001791200c032041c0c0c009000401c040c45a680c00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704567652 1250 704566402 704566433
    0x6021c0608011a150c0607050703090609030b0a0905190b0108070f120b0703060504020f0304021306080d0509030a02190602070801051e0603070902030c090a0e0606040b03090a0609 79
    0x4184552a5100360301402c035641410707000640300c20340100480500c3d10141011308203092010352030511601c0c1c1002c9103000021240a004038000241110a00d500310924200411107440d1103682c05007180d0b43c2c0c0d48801c00107040800d15a40b9264000200b01c0b080c400c208420815126040d02103c05d070a1540480c07000303103d04e54650240540126001984100140644144c90720350285004140e070380d040300e280000e0808040550700c041c0400c6682c0c0c0c0d03000800d110405201003c0c0c40e420180100440da03454250394100d1241750000c01c000f685d1000c9103509180d290307824001d0b00c4032000008241007103503000b070096111280b400701d2031500c617285400505685103a822036095603100d4403074500700c96080d103451145c00220982900c08240804003240d115202800344c0b01c04a03510000c0006070307003042d10201c10610000c215030103070f03080039400c0e040148212440c803595400d083c2c01042480c459070190001c52840040000c0d18600e080151521403580803008100a030a54148290781055840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704568902 1250 704567652 704567707
    0x15040509090307030f1107050a1d07080403140706060b070b010e09010c0806151210051e0a06030b1f02060a2f0c120d05180f0607050310030602 63
    0x40104011070303400801d0340c080c0c680c035444a0080f440900800c0d29180c401403002c2880e8820000701054984030384900c40003d054401ca648002d107980000040410780052008081116000400011039848a6440354120303003038011941c0e58101e4105100a0011038001481540001951030200318081c4907250407591094004400c0d85c43d0140303000c0c240c07031029010000103119200441c0492521140d06a0394050a07000d440c07906051000c08051007070102d8203004010500702c0c04102070304014030031056180e616801c0c2e0540c0e07a5110002000c4041c10b005e4a420560744400e0000e142d100c241c000b1140c1d1088411103907801d00008402503a032a4101c070b441010508043c18203002d510910a184074006040041c10303a000040c105494407a005030845410a03c80c4424212042c24010000d20081201d850013007180e2070506402040000da03003048240c150302104001c02c0c0950046420f41d0445d0307071031500d6a52910b40c024400340b1030040e504042e01052000486286100d0389000a0b10140c2c01c0c903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704570152 1250 704568902 704568919
    0xa02010b010203070804050405220f050d050a0903080a030e030d06050406170a020f0301020d090b0117071d0a1d010f0b0f011202161a071409010f0e0d02150405 70
    0x100c01240c60380a003d80081c080310040c441840185000c1e0030090f03004108222103451550007040c0007102c003400c0101552600b04c10725003002403040511121540c1021428024940316400200401440c00c910000c0c0208501081500c0c000744139802651440108004aa031654010460386005104134400c65201d140340100004d4030303503505015070007045032071400742c0f000702c03204d03000d0000b00340700e0340240fa40c595820404400101543e12844440c18021240501c140d81400900c00c84c103085015a020168080070080081420702d9210ba084a030b000031000c6082c1d1541e41041d000b810007550b04002100c000f40700348403190340560003c04031128411041c805005442d0134040300c0d8844d1511203000918030760b9122040e44054000344030074000404410681000c0e44c480c500c0c034030026031541c4041001c281c02c0c09180c0c6d601211000701c0055030312180c0e00d0031030314600281c040c6050280e414180704181d2040c200a6942d80c0449840b141c014010080301000681200784a40c46400f815115208a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704571402 1250 704570152 704570171
    0x6050615030c130f0614030a090b150102010b0d020a031e0605161805010e19050907050403030f03021801110a05060a0b0a171b19091406010e090601180e0c0a0201 71
    0x24261020b0841c2e071705440da41e1807041092282032081d0b20082c4107004a40d11000788400060304c2c01b400318801e01100d0400c2d42a138005c64002400d54000940ca00d00c18010351054801581d035070a00035088a602c4460124400c0c07d01110b0704c0280150a03002c3c045078a4070b01041600b0720a25409058042c0a642d0030002c181041e48103503000b4040d016650000c0c031290281321403814002c0501800d201c06007154050304d580c620014900450458004000500c0803c08104250700315084100d282643d050075400c2c1b10503024100c01a003002c4403468104900c002210b04241d4003840245a1640c20a055900b42e1900c50302c1007001d4800c4d07070394240c01072804480001e5900f0509006007080c21a000c0a00115588129090f0120003c0540740758005084d4102d8140260103c64a0303005000c05c01000ca9130704030f0651813103111840240002d061000051001c1060781c3c503601c0707a5501c24001d007003d9802c1382c5403c1e8062401c070150740000308158100d006010401800d0006401d00100d513034005c0c000c02c2030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704572652 1250 704571402 704571419
    0x1c1514060109050306040f0b060a1a0c121c050414063103020c09042409110621070306080109232a040902040c0518060405060706050615030c13 63
    0x400f1240500782e2107c040c01c800025030400c0304035401400c0140400d808039103c0105006004c5c3d1041e01c400c00700300008402c4c07c900d05c00d002c07042c41500241c2e003460514540325010055061303050242c54005a98a00140c2004000321443c040284107604803120b80c5000c568601e1a11201c01d140c0c5030880101c000201023804901d4203000b9240e05501038080110030a0a20425a2000d0b01c03c69100381c40800060003401c050302010354605072100c0110701d521660500c2c0a100c1c0185904070b014402c00c11806c4102030068403044041c40500d0403201281d0b84000b011030003000300350091480e55080942c1d19080c800104000c1c1c4041007540d6018a030a0b0038802070301c1d51070f2600404007426003d4445c1003540d078881030030388075a4260050004074148110340e0008003211041a00d410115802040000140031100244000d02c0401d0341c0346440c0c0350405001500034040c0e07a00051829403141d002800c1500c908800c4500c2031907400719540c41c0d050000c14500c464101c80e40c281140804100001203845 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704573902 1250 704572652 704572663
    0x11503060e06060703030b030709090b07030506010914010f0309060c05090f030d080f0403141b0f0f1209060909010605030f07020a02060a0309050f070f051e1c15140601090503 77
    0x1038000304103520b4511245c1d815009480c07c010b505600d4040c00b6000142c0c1c1d442401000d42047c81345002000510340000e0150480b0300240c0940d04004040c2000c0c0040840c0001512089409080141c0c0e1480e0a25007180500544000107240360701b05808419001c1d04003003c0e02180001312580c402d40c20543c0203240c0d4504aa442005c0082c01d8000481c0a12203209007082d00a4000d1614900788010580810101e90248008039a512001036013042030490034840d01d108a0300c2c550207092407000006005640b0522074144150700e00d40007450303180d035070748001c11124102c4c000b030050603031582d4030080078115130400c40350320200080d840000343e0000c3c400700b61141c0350f030b500601c2d140c00d0450080c006c40c02020044811a41e5200b01c20507044020002c006910080c03405407040007916007094244003d1011400000c1021604c8071031900c0d140d42c4001c0120f22007400c40b4801100100c0d06d00f8440c030000c032f2411030710b076100f403900d091400342d81d000c2da5086218640a80314855216030750420b05980d00b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704575152 1250 704573902 704573911
    0x307080115090e03040e091e0d0906020a0302060601050313171201050910031104020403023003040503101a0d0f02040c08070e010f021f06090b0108010f0306021e03011503060e 77
    0x2600204410b100c0c20046c118000d400c440d104080b00c031640d00341d01c1c0c0010a03030045503c140460303220002040d1182e6019038004080c21462010300f6241420350b402a5036198058001414050040001011684d90b034040004243e04502c84280c0c90f829402c1c1000030707030f10100a1004490b0700e640003140b281098011140100c0c08486464031551841d12500307000c0e80511843c030741c82502000000007607600c1480c900c24080111840d021907207601e0b8682071720400e00d40f03c1504160400d0100b00269600811091224003050001003484050f9802d01c160b0b80b4486070303019500500001008044c40007090b04400814420303034082042400d200c10a03034407900c0031500302c400110680701ca02010f5200b00440e254080841c0110344080d14034500e410040e032490b6034216007203075584000300a184400d002d403a10f071081c00e092686903941000b48407514030b00341e4040908841d80010700d008082c551001c03805c95024a07001c100d6200c1d61142c41c204c0d01131208490400010381000004a21440c0301e1110a004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704576402 1250 704575152 704575181
    0xb0306041b141c2c0129060d061e1a0304020d21020129060724020a0915020106052b15140708070203030a02030a0b030708011509 57
    0x7a030340d4100c000c106070780003003803c0c54512014070310240740f00340e10301032002524007aa8410b0084080e00400118200102c82c40040c01d031704110710025801803284081030340c40342c00042110343c0b60b00381e00441c4052183c40a100c284629161002401c00c481c0a03201c0804003071802d84901c015500d000302050036200c210202c404120400c0401e0061a0403291500014480d441154100d40600d4205840c08d060b1805480544d450340385045100f20802400c404c524480c082103c00013183d80b0118040340956070b8010004001102d810041807248504507041d40c405000565440c2c84a400060a110062203610f8054070656035000255006004440c00e60380054007013107040d443d600e414410348c64000400c061104c0f20312000c40200c2c144601d5503800381e8040e0f9010603000501c950040c002e6200400780f07810821032201b4030180ca07038080100d0f900010340220160310b0303032502044440100b80c01c50f207030340c0c0c14458054006407141041d0002c1c480c540b004910341400d02d0703484000f0420744104202903201c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704577652 1250 704576402 704576417
    0x10031a042d051b2811060903030114040e030d0903050c390f01050d0603060203010f0302030708030309030f0a261506070215070602090901030b042130060b0306041b 72
    0x780010f2142ca4010104135480d041110b00340701c0b80041c0c14540195100d00c2280c10000061000c1c4d010300e5020500490250350400014030348d100e07032030384a002d401d07540ca14140c3c942490900f4076218200b594008901030040c1d405400901d030b540907403400c003040b02e01d8411489088141034000c864088074505d03800584158000c500c0c0f80700465040c0c0c0b1008070800816074501d40403011500354030266020789200d0140704a442d0840c0100340c41d100269004503119841001000303030b40c0901209440b03484d6000c0d00c08580780d04080740c003516410a040c0e44d02120307819507c3d061107120496000940586407050100741841240c1e401e200c1c1d584684580a07401c2003030300c0c0030030a48040c508000d140c2d050150b14014201314040c1c000a0f8144000c0c0d00c203490b12203e240501c000e1018418019481038007070850b0640d4941c00d408094420041c2180111440001480484024203015802c0c203540d00c0307209003001901c0d1282e140c0c0d6515041500c10764001c40c035011452407421151081d4a070004101e0303e4018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704578902 1250 704577652 704577697
    0x20f0712110d030b0306160315060323040c06050c0c060c0c0901090e0a23060106020d0e03010603030c02040c0c0204240b030421110a0b0610031a042d051b 68
    0x8095600011007410940d82740640c0402c1500da000c03500141c01f56640c00302c2e0554840315509200c03503124411f5841030103101c052200040030036440d00200c0d0039500b8426150720101d0102810502840e04042e0400400103004006a001103031b0f0031003194084540052998803010084215040c4103107101c0c05911510a11010901e9020100954800056135210002441d01c01070305021080e403024000d03911001e5982c00d41600001d50200700f60056008102c010b00d140c4001340a03106e0104042d0003255a069111070252160394000d01c4107402410621010704103407181000001c04903451840115022804144602a0790072a13000d2900680c1c000800c04d4000e00d080440e030032048600c0288809001000d03071180d0f0a004407007081e4021a101f1440e07103405014802d840c01c0803945041014900b0038006201c5818200a448010050724006400b268448400200c07000460b01200d0300034064156501e40c0200c1d412442c850804c03040c40008490105980490900a5050007003c0040081004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704580152 1250 704578902 704578921
    0xe010509040b03070b03040b010e07080610030209041508070506030408070b091903020a0c0b0304150c0e0405010305010903030c140d150b03090d090803070213020f0712110d030b0306 80
    0xa003100302004100140c04112040040c1c94402560700214054078084104401d0044031003405005186807500c4044503d01658010104000180102c1c442e186401800d081244664103480709694007804c02c02041c09600001100d20b00b2611498801d8807604d60082880d0420000b603d010303c1d07000b4510b1703090900503a039450796004014120350144c81a008070380c18580000781c100c2283c6019801911620a42e0305120000c1c0910b40c1254051034010018040050303800c404618075420400d80005600807030540854000306e0090304554400c3c01c080021003440030650003000c100c0d02c0380d02c0411003000031103811361324030729501d03021034042c42c05000300740540410790002c00c0c082508000e050700c025141e01c0b2400c8180c0054544a5a641c000d811003400c25801400c2c0d10007801c0d083c1e0085060004550004002c1e0320800000c6801980226150000c0007161051706c4600d9405081c09e407116641180c0148440d603000080c240b41d1140c58410b100041c000c2c0b0031144110300c054041d00440d40c43d680f00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704581402 1250 704580152 704580157
    0x30703030e1e061809060a0302030a20031609050603011103010e070c121101110f040603020d1506110c061201030f03140307091a0307021903180306050103210e0105 72
    0x3480c40b406501d04214070320b5540c81e0010203410b00d1004540281c404100240300036160010210780c020410340d002480517036400151032100b161305ca22003615500b503409039420082c800f042c00d01e0f0584645e0414510382d210302c0032500d05880f850a4204155034a180405013600d2214030b81c40c403241e2007000184100c428200d00c0c0ca81c1b151441c1000c0b11711400958400c0307290040d03483d41e0307000584803842c48c00300c02c10203000b4010250200d022950502105101c80c4031544100c0c40f0301402c0c0340d8005207449203141c0036004a10801c9202c900106240d45e50140903140400d1508420030901822103100d000d4500b5106840c81400c04001e034803266802c66170781e03030300b40071800d5015814404000d610303010040440700114802c469543d1103409492808100d0520300480c41403051010400b801080034495000410104807500c03074003250030f090300c0c074202510300c05803c0c00d003200d012a81c0d03c4044184200380e004079040700c3c4101c210340350181044c520b00b4220f4004507078000c001074003006030002941c030807400b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704582652 1250 704581402 704581429
    0xf030a09031704030803010b070b0a0b0105090402090409080a17070c0507091a09041401062c040f050a0b190b010207032d05101b020d051c020c1605030703030e 70
    0x100c02e40307032640701d03201d4a40580003607000745040c0c0c50004604081002180c1402c0e0070144070f0b14284502c0d83d880c0d001070154000d4503c1207000303e0b0b000c02c001d44035989942140300d8594010024a56552040200030071a10340344030305090741e90180005c40c1005100e601124007064000018104013410700403c0409000c000018041340165220b101c010355440306001401644a071010a240000381240f0500303560050748180343c5030401801c00b080c2460200e916044218101c40240072503039451400700940b41320001e0107081881400c88603420001000c6c1014000c580542c0629100034040342c105003541c0849003401d00603040000100000380042c03200c002d400c0d039074030041c01104256011302c2c0d90300403403198103407220780c40042800c40711403076440f61140240d00103151b5440090522806551342c0c6c1d06155100800c000040c1120406410342c1800000c19404401035546900e90452541c0d100078800500c860309081480008a038640050305808680c0e16444002030b08255004010ba10701c0e1900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704583902 1250 704582652 704582693
    0x240302071103010218031002090d0f0501020c061005190617090f01090308040c140a0e130c0e15030601142826060105180a0b041506020f030a0903 64
    0x141c08035000d079400c1c006000f5074180010800c0c44404090100340c90001c2683c40d4688551040141030b4613901c92605d00d1841e0741e01b0550400301c45810385095802071080348175212041c0540d0044c003020900300c4940c001140c104445100841c0900c5c0c00c0391640e00d25504c20740c1c010a410302800d00c0784841c5106125030040600c0180c03041c0440a44015095072a01d00040380054007c604100410081c07000030b0300540f01245686411080680101d0a50400e07801000880d100c4100012410901003029201c1c241c0d03c1101e55845641d02e0701d03c5a107605040e44c0c1c1c0160700e0021680c0e07441c142000110035040700d01c541600703131640984009014040501d00e8107441c5e450900078100280f05924028800100840303a00c500b04004240110080c601c108114400607420034401081255a40803005c40c0d08144020b2494080d125541030000038a421480140c00905140c00501990b2124445408a803a00e03001c0d44c2e503412100007425100d205030248100030414109090010410000d0440403c24110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704585152 1250 704583902 704583923
    0x140103090512040b070309090902010f05030417070804090e0f03090409050c0301020309031207171605090405090102040501120513030806060d0e1b04020c120310031401090302060124030207 83
    0x10b40016940ba4419044a4100c500000d4540201503005050000510034040c08102d555290b41c0003c1109090303001000821101001007014864840d070f10072003235070b90812a0b03035480744680381090158016100d50580c692621001d0007000e8804501c2d0006441030b2070280d40f0302408081080014401c0700f030182c9051141081000c407540f000d01c02940a86004401161521030b88a04c944048200500b00b004010304e01d81420300c20035200c12100d4010382d62406110284034902001c4a45000d40d00d0516817081c1000c0c01d103e07005030198020002c1d01c2c0c080c1e0354050f018448a00f0807058a60940b417100e100c0507009031210109101e5041160810f400401480c90302c0d40d107454072001d4586d00701644400e5084881c1b038003941104620003850001040c0c0b0150704040042c0c00081d00c640700720341d120003010b82c00000a040a1690860038016681c0802d5084040320315224450003000c000743e00f200036108040011520042c1c0682d1418042c0171030694000302c0404120880180d007140100b103800880f031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704586402 1250 704585152 704585173
    0x507121109060c0f0f0d050f030c0d1503052103060405060105120103060501140405010e27030a020619110304030c0204150314070e060a09020f0f121f1401030905 71
    0x40000600442d44854000c104c00c641418500b4204500c400c440e5803150310440044051310781000a45142610000c50740f03271030f03a0324510240045c0c41401c204c0030500d07240c804040450400d4102010549004000b19400c9455242d505000f01e51121400d500c00802400055842d11707086c0c0013181c6c01207041c5042ea04107005005468400c2e41c0a0b0401c489181c1c0b83e50060142c0688581017a40040c000c8506001651409010500c0c2c510081c00c07020b080203500940542640000b44601985d81043e0101c0e80c0d81d00720b0800081d02c0302015103800d802e40c0300311024840742228a0081c0c05881c0c40c150b50703480c915112075405803544121075800b240c015488034032100c292004102584c006600505141080f119005645801c0c20800c0c0c200e0304000c01110709001443e02c41c2c20031001610003030040145c4e100341d0100700e04150f016660144000010001e40905020041070b031160240b4410a01e200d28461039219040000400d40a8250f4801182c1d41500300c03503100386c1141d10224011400d43e6500c154 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704587652 1250 704586402 704586409
    0x80702070e0a0207240c0318030c050a0c060302040501030b040213054b030f0601060509030f0d0f091d0a18020a0312090f0f0b0705030c0d210507121109 67
    0x5500780e00841160342e80e00d090010744203902400700306c1c0e0740501d01040009032500c0600302000080002030100b20941c0ba10b031040080c2000758050082e00143c00b00c01195a6901c003d0196001c0d004090010b03081044800a40c2494020b81c0c2d480ca111040c02040c81e0309000900040310441010414940079006480490b4200b03906400d451000ba0a0f4030441c0b0401240c0c600e14800210180501a0340801030103500d088010410f40d055900c140b03481681c0780d2525000034036040c140b0007803080a0092640400c0f0407170704402c400304500d94540f91a24503d0755007105038002d0042900d6070404030500000120f07484082d5004100c880408103a88150741c1c510b801150044141b60001c55040c5450540840c080c2d4210309881c000b022020410801e441c20021801e800c020b40e849140c2c1c040d1004141a010403906005554009219404444562100d40001091301d10890783d00c1040011460300c07078120301c03001e0040d5031142e100754490441d0208e03080b9040004004103030711031051a10034044811a90f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704588902 1250 704587652 704587673
    0x60c0903060903090924151218020102060603280312150302150702010c0609020d1b0603061401020c151608030603120405150a02070b0307020319080702070e0a0207 72
    0x41c004c0c1d58400610307040006190407110302842d088803003002002c014081425841c1c01200b6250304801d50b50318a4006501524518010303a03000601906107018005586a29449034402074006d900b12640e03506d510701030645030005030805212400040c11411450b810b5110ba002c0124030a1600c115900d084c850f6041c120313a0000409413061030042c0302041980380580411744000d408001003031130401c00307a0001c1c04014607400d00800054035200580d0640d034481c1c0b40c1c02030242c0c000e40940725034608503442c45210301c00b03800703a00003017032030080d01188540c241080380c00e400c00180c00626110901c5d008110b008a50016100d000710f00401205505c1602140078900b0603125000c49612402c000c010581480100c150f1480c05100c2030004004a80d5041e024201800c1e01c070b0001075483c01c20f00030490806409030868040c6140000c144130420358000002c081540c851040a03031000c2e0040c0c012242c07000c0a403540341c01680017400612588420500791504a6000031006207840415a203c04402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704590152 1250 704588902 704588921
    0x52b0c2021010507110d180b121807061718011113050907050912010204030812060414010b190329030d050a1d0f04050f1e04080403060c090306 63
    0xc0703400c0d141581040724240205a000191400c181d1002400d102002d65600091543e0310104400c42036552080319180249101a0600041e401d41d103c10b2142d148001d40d0302507580005e140005004000500c1000c070b0715406440c0c0a0780d0f299000445000d020302d1558000c1c03c0a00da40c4070328111201503010034460501503007164141142c031200140c0741c03052288001d50026005000010400c010198000c0444824110441c0c06071000407203070b69401d0084c00b0b183c10080c51747c000090b424009d1420b02510610424017200d003885080d07142c001c131151224080c8524114000306012028001c47c40350000c02506c1003500d0001080d4101c02d0701102d001c1110054040ca0088030200943c40c2d06041c80441c07445200350030030901d024051440181058074821891100a00040e130301050707983c031302c3d0003261707032101c000c0090100e41010b105034074914030182c0b0300075805422490001c02d1039000c030082a1161b80c004402c9030a00e460b54a407c1c01034074110462100700706900704044005800342c81601c210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704591402 1250 704590152 704590189
    0x2040c1b1110080c0f0a02120a030902091e06010305060f040510050a06090b0a0c020402040b13090c0c0b04080c0c060c01140c04120201031e0207052b0c20 68
    0x3109241d4140300c90030200854400802000404006018003c10120744100030304d60002d942d22034410300100c0c20016480810540811700041812980c0d5158029134030107402180c1e01c1c02d09454410004141c91480304d03d410880e400c04001403c15030199106e1603202e0300251581d4000140100010204d550880350012468440c0700140b00d5420700000c13075805442c0c03a080801c215401e03c0e500096034080c0161050411600349545002c54480da01640c0003088000e101da511040840c92000c00924140640840305141c4060707981d0140c85655032a140a401c03414010044d1544d480c1c03035115a112100e1a2040c0c401c890a4901980b290f00040c030382a10355000005580c1c882d0a1403000621000e024110300d20300600041c09140340b0501e42c400c003140c1c2424009103442c10000d864030204128900516040d20205c2e8107804d2100114011117141502c00f4040407002d11412462461980e559422001030714103402900000e011a94408002c0c074506001c0a40c10011030005040c440900703030f250113 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704592652 1250 704591402 704591423
    0xf031805120f1005040f0f17040e07031a010906080a02041a0c0d140901050a020c13021810050318070302040f020703170105061c0b040e01091203020408030702040c1b 73
    0xb1464800d001e5044030708070980060101e800d25031200c0c03002c241410b00c068074106e124034800c000c1001540074101d05001d03056072203440b540d4a0072080c000d4902140d1040229041008404800071031620449036104161103421100e401c00c003084840e214002c00c0640da00780d0821011950b546c0d01d01400140d4800c200320103135500310701c150107420920165400d03018481c50703018030150901c842d016640944020f103032640d10350003c090102e242c8401d44c0d0580f0303001000220140510b00c40342e0010500c140000301c0ba6580e00d000d000520016000840c90500040d90500100340449042000325000d2002d201c1220a0b040d282d0300018222022291000d40e01c650000d40e4900f0140c1040005a4051207060003012662528001c00e01b035102e8105002c0e159000020b0b0300c100216554852550a4030180c81004000c15406890f4001c044041d01651203040122400c94064403c0c02120203580e01200a1400c04032203600f070000ac2d220101d203940901c818a1700030101e01124282c42003030b56025101c1c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704593902 1250 704592652 704592673
    0xf020c010c1716211407020d09230622090501080d021203100f090507020609060403020d08070504052806030b060313020109030206030a050601080c070f03180512 71
    0x40409810005004082c0745900422483c050035441d43c0500c890f003810101c065440035403c10362032881c107042031840b0714038051100708413250202815102e40d0301602110200d03280c1d40020799848050384504d14140083d200141011034200c0d1000481400140803d81040c0c902c44260b039070703c001c030090124080d510b0748041109030514081d03075006141c144040c16482140410083d168681d18448291035200000410040704a4030391401c010100700e000d4030003154a507009032003d0681511001d0041c46080040380b16004040341060250358141c004210741d010910b41511400001443c1000384842804002490f89404400c0b121141050003040721013054820484480a4960055010542780c200c85555036290103049a42101c840d441d4450308a9a510040320300c0c54031500005c0d0014000f0050045902c60741d04200d0143c842601d41d6240b42da500e9100f6035082c085e200f0042c0c014002d140310310003c40d0061920481850200c5e101c005a140c980300440d21704040841c1d5a040e42d8401c0c0441c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704595152 1250 704593902 704593907
    0x601050903061602012703120905030724020f120601021c0c0c0b030403030b010201061a0f07080405190e07050a0c140f07060c202215060f080615030112060f020c010c 73
    0x200da40c8d10031403c00300510120340e10f0f010b0b501e000e01c5000603d00b64901c03002414182d2408450042002c440c10150b54409000700317580c5654111480b0707103003005e0880010a00a43c0041100701814070400c1a00d0702d03400300d00e01304940e00c080003402583c4c01da0fa00000031440081d540c00862040303001b0f441c04545c94008500083c21610190300c201c040701c0241c1d40440740c00c00810100c90b0380041c8181c016031a0380e407a08090603d84110b900035584480307640f2121500f15000c5e1441c0e401c644a41444800c65540c2c0c00c002d503000c0c40340389040700004482000202c00660a42884001a82da0070101d5a403406074001007450000f03150410701c0030443c520343c034104005d8001e010320180000510708082003003600000c280d00c00c0c1001e0030703c1c000400246a0901069080e40181e03441503d210900e01034959845000d44a14011304070140001c1c1280001590303802c0000c000e42c031a01c5c60300f540e1455070b8600300345010410061401202c403a51500088180c00d251800a000141c003000000a050818a07002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704596402 1250 704595152 704595167
    0xc1716111f0f1d0406031a10030206030a09060e0a0302030c0f030405060f030910050c18010203090d020f0607020303030903040510090609030f06020d0f140601050903061602012703 79
    0x390203031800d00d50101101650000042c8021030041c1040c0490079030000d1071075204071112800302c0d0004c0c90b10360008184489080340207821640d140c1181a2034480c0c01e407040d420011800040e400030340800100e00da44440345c0c4880d4070316015031800a0f540c60240380d47d03030400e860a0402d600603480441c0e15010010240154648213191a00944c6401c0c60100030130a9400f8034021180d41c030a007c000146403003400d0140c07151507138501c0010401ca14010303071030912135008511801f1400900c5070055070b055000108407180e504004200b0446c40c45642c0c204254504180200c54024400313201c90320060b20200051400383c00f0742401386480706d04100511012884000c0d50004004000c1000c101d020340200a44040e00e801c500404600c1003a404e050b0003900c1040044a8090324002810b075000c0300d154403d00d418100320316a505c29454050046071070340940300c40594103802c00000709014112002c40e500103c100e43c000401d9908111110780c3c0c040a00c20f0300241d00f1092282c14038201070f0311040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704597652 1250 704596402 704596429
    0xc0f0803040b09160f1728030e06030c090409080c010c0909110406090b031b040303030506030c06040b0d05090f010213030515040b01050103020703200a110906010c171611 75
    0x1182c41c1302854442c200342c941e10755118070300014a450010600081c004d002e10343c01c402d5410440701c240c0880100010403026089000d82c000341003402c21040c0c601e40b403c00c0740d014407100d0001900f44401b8504210091100c03402c02c0f11101000c000b04014500c007801040200c22443d21450001c6150260040c1500c80b029043c01d110700d410002404101e401000c0102510380d000c2c1701c1a01c2c1c0d6607080c60b0008000c4560400707120260041030000800d80d06030040d501c074520681c1030725105074882d030921100e802117004980400347c0602010000315502d900903540130101d042152380300c00400021500b240c2c003007801c801415114600500601008000c1e00019182036081d0740d20500d01a220048016010701840381015000200b901c10f02d446900c1000c0c2c3e600c0c0011050904005400c1340c1e60380e41842c40000c03604d039000040d02102529100ba00140f10390010b854000c110100c5a450100000100010b075150200600c00391203561020114490168825070202000510f00c40c20032800c00307e2a203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704598902 1250 704597652 704597683
    0x60b01020705101d030f0618011107121704050c010c0503130b041d06061b1c030b03010e0f0309040b1503040605041a070914210105070e0108070f0c0f0803040b09 71
    0x60800360840300003406ea036008d41070b8000c001c001c1c2018860a4054900d590040c0103a443c0410581c040c04407007222800417031840e8581500c85c00d100b901c0070710101400c8038050f041c2e80006440d4035003540030f18040c0c0344103441002a24544140a01054119481600000b495203804a0103106080c401021010034030701088410000385040340000d0000d10403502070788a6079081d040c00003803440040000031304002d038108040c07002401c0c805e40100280100c0d11414880d608048540b16401c0c40410400021075010000d9882c0042c0a014840a00b901c002034a400180440c00428000030800c080d6001e14885c080208440c1002e0500a081443c4001150442009042440022038106011b04111502c1f541094400c090440c00101300710040002c0b0b1000100c410b80d00c160380c00701940f00c3c0c0d10400d850b4441c05020001100116200030088500700702003981c248154407501c1c00f44604595080c40307646d0f100500109952000c2c01e0790010b0318121b030320319244018050442800e010700c9482080d000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704600152 1250 704598902 704598913
    0xf02040906060914190302030105040b6102030a020c1827030c0a020a090603120c06020d18060b09090d0c0c21060c020c0904060b01020705101d03 64
    0x1c60056100d0502d070300381d04e03c40e0900c0c02d815a05d0f0200102144000c640080003008949001e0500454600d13045400c1c0e4001c2140100c0f061080307645001180e4856112100f1080a08a006900d40f150f800d00e60059940e80d0030710302100032203201004070005844c2590285489168a80c0041d29181d003e040c140c0c4101d03960081c4403a4074540007070301d40d800300c0038400d000086090020510140c0d034a8a0a0001c140000281030380a448006007804074030388241d8400c03e829942d5000308086402e5800010711003c001c814003e0fa0070b200d69803140c041360081000510b4004284002c00848283c4c4000c51f800000d01c2e4001e070140403040c4120b40e0722030400d5030201024a00b11022503210400521654240800c0f06050320500071100101409403401010400700c0c3c0344d0014458080b5000040c08540090401400c2600705201083c51141c49402900e404442e4a80e5900c44025200301700e84c0300d0440c032500d84006000d6440c9924500010400d40320003c08180c00078204000958200841703001360301c0f5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704601402 1250 704600152 704600159
    0x206060d0803040201270501120506100c030e13060501030b0a03050d0f05070515061c0201020a0201050715060902042603250506011401080a051005040507030f0f020409060609 77
    0x282100040030580c0081d00c5980eaa841e4801602c03240e0080c15909444d15610035046588000d04503807070309452003603e4503108403070600300341000d03518111145034104c8410151110700c43e020340c881003d00c83c0300781421000f0800c900c2c0898402605000c0500c1e1040c0c403410100821758051199100580c41034403510842411a00c600c0c1d51482d9000c1c51404001214a8090ba058418019070700c0d066400021340e80301e225520715040307c0030400d9582e14030070150241200354090a24040741c4110f98103801030041005c59400641d42c5030044e402c00d03200c03010800811441c1c00718a00c24000500040d0500507203030b50400840078007105002264100030b00c503450700c030340074414000140e410200a810604c01400600103980030b54500c180da008002d841004004503500f850003990f483e44407400c0c2e807084500d948501d8900d0503100203943c20207181100f10800d1041d03003443c3e040564000c2c40c0d428040769440c1640b82c8041110302c14031260103030340c0d130100b400d001441040c05008010300103860642c40312800e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704602652 1250 704601402 704601409
    0x1003030807081621020d0603050c221a130501080606060708041802130602210901120b0130230109090c0302040c0c060f020307020c09040204060b04060f0f020606 71
    0x1240221503044c4030300c000100a64049200e1000c400c0403950005548a0365000981c0014141c0c602089400303000740540400a0b05044840007090703418603400044154040c0748810040850751f402803110126110790403a03e444105184e460a0207258002409624100c111420610050300d41c42c46008104156004980345000780c2d015289021600181090440300c0700340203115a404800c0e511140d003c001030031a40105e00c1d0130403041203000d80301c00201061080035480c402c0b8410140410b40300098080302100c641d00101042c0d0040c1070240c0a180703411071034109c11540f41c10361030440300b00e521a95200c0d1514000d50803404000418640380d005a0114401428414010b039050a40c0d85ca15038070034442d08168100c0255006002040000c14a4070000c0c00d80600b888241d5202d1305102d0001c80d00b03001c6208881c030900c03883c0c0c064500408000c00b08418110050f0040e85d0140d125440031a09004800c0208001c0c6059201c828451800c0c62000e000030311010403040564105800f005581e45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704603902 1250 704602652 704602681
    0x10050c070c08192d0c0e010f030803011202120708010618020304020a15120c030903110a080d020d091a040c080c030606060a02160f050f0a03080d0b060d0203100303080708 75
    0x550016001080286804007140e641e1500c1c0580c035800040c4c03007640c0d01400344545d11031059499051010502e80c0e224990650002d44030b2000a0a20130104010080500000d01070307046144001c04c1540100c1005000529005554000384000e9540b210708010354541108013949007484004150b05520386174000544203016440340c106e031001d40c0f5040075603591040035050000b0301501d0b81041141e610000017402800300380e9013100810170007035004040100004100520344d601402091a00954030281000307908032900404e0f045031075400d0000080c00c0c05009100c9400544048400d40c5010700b03250011350303541d60003070065400c0402540340948001c640143d120200740c03007040e91400c03401c900b21300d80305240321824002d045481001c0b810042e0100c495003110300031181c2d010130007040300800101c41f551381b20082506008000101109000740c028800341c1900800f60b90503c1c1d80340c2e150005a030310849414030f10624448062040642081001e0340203a0585000345403450050304100044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704605152 1250 704603902 704603953
    0xb060f09130602070819030c1710060f0203090a0e0609010b040303231b0d080c0f07110a0e0c03040b070927110c0f010c030902031506010210050c070c08 67
    0x5a0001101c0c4d081c000a502120101007403030b50f08080d9124070040060051000c446d2030000a01b229065058041c5240319882c01500708501d10400c4614040050301c001b039080c1c1c100015400148007202150340c42c120004004c22000f0303008c0301c062404e841008503450f4160420f080605092100b0f2002c664030001441000c0344800c00c03803501903075000b5441040d005502e040d01d189031a407100e40785031070400320302c079414181c0c103440700406611108540d80260140d404100d41c914014014040416040300307075809101800f410004040d42c5030a48500314840458240c00403603400030902041005002000c0e80c04900c9141071803045042a0802c2d0301282c4882008030300041580010000c007103154015440000b01001d4076030342c2c1c0054045a9114000707150022100e504c3c00d40345d0010321b402401041100740e802005401d49003030244440d0410300001d409141103104590901e0002e14580c49554040d903003145d40591155107619082c8038000321074200d540181c011180b0380f00d145818200e6200d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704606402 1250 704605152 704605163
    0x513170904060e190b01021b0d020402040906060f0f09060512151f090f08060c03091908071b05010801171c08090f0a021f0c06090b060f0913 62
    0x212000440080c000e40640c0d00303c0350314001c035041403105140c140036100304406841c0b0300a00c041d10002c8016602d0300e50341a2010710f18401d8851001340c43c9011440180380e680700900041c01d0640340c2c1920320850b10140c0012000c03440308010302030000d402008009a6044038900b0b0b050180c2800001010303402030284840d0800f0b018004a0301568a18044c00300d040c070043d100c0380c00382900240e0002c0300140b402c08030005c120131100c0031425606d060704002c243e5510308014280c40d299014600c44035803004140035001e01580c11850f414040c210041483c007405044d00544a03100c6042c88015003101600110449242c00d50821150340c0041001e41102c92070007040203503038481500c29082c80480709021442440d460000c2d880c841e08020a180036011110441e400420b81c0100d050795088011006540208a40111030504024840440c1701148626054080050719038502c801e0703a20400c4110b4207103902d401042020f050101e041004c03c0802c40d501c08107800d01e60201d445d451280f041c040c14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704607652 1250 704606402 704606407
    0x150708040e090102070b042f1e03160b09040609020316050a05070c090501090c0527040905030a021c022a0105090d050a030320190905040903050d051317 67
    0x1001d820342c180c0c0d005c00d421500d0501c8504c1c1c6071030411250444003810445443c000c1d05048011302400003118000e9101400031100c4400d6409000c00341c400070562958035101b05240f990702c42100d60214002403e07020846600c0d40c100004000c00d948154000401551040c420803c20007240c0c403a003405406c42d41440c5954608418007180d440c0301e2040060b1200c440180001040001a03110504a820024041007001c20003502240c661081268a001c03e20003114660312406408460100c8480010320005085200b96030321800c6030070006101002d60818000c1000720410185009200c1c1c0d00351018203040d40d03890300d108450740841e11001f80c6a808502c0d600d0840d0340138204541070700400038407803542c24840d4980a0342d10140c065040340000c1c00c00a500703d4481114045142420000504a040251a5101706407001144001d070f001c1020241000509d82c0716440b54022150007595a0f641d150144810201a03841c0948030350400b1699551400120f184900c0900d0f0030b55580712050ba = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704608902 1250 704607652 704607661
    0xd030c020d0e150a051c050103080a050c03090409080703030c0819022101030510060b030f040618150f060512031210080d0815042c1009030905150708040e 68
    0x10300314500e0f840c162183da000015410550354102c00640500308407420814980c0c03032900c2c0307200c081d203000307200c000c14600b424000008030301d0060000d40200301601045038144143d840006003071b02c6d104070042c3e4124400041020034103608d8090f05113481d032542040b0a660a20701c042080741d29000b02c0d4000134541c003040000c094004c1610500e90301d4000c031407824880d42c407401e040361900504104800101e1600b000042e03890074070800d40340714003404022401d43e5511925400c014100030422050460b41902c400c10000e0548500d400340703a1540b510009600c02900d42e030700212282030308428810194804c1980700e21100004a0360b4012003c82103100e11784841d0030500142c011600050114028104035030881c41d405460035104151000c0030040b150f00100a003c00c480e03105a10030f081c8031541d2031010903001230b502d068001c0030f07108085a00701f02a46050b80100c60076810301b180000d555481c100440d00e04201005071400900901e130f85017207070035658140903101d14032070f10882040c1c0d0320008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704610152 1250 704608902 704608909
    0x70503162f19050405010303020f06011401050703050a030b0301090c15050c0a020607020102072412020702032e020c06100614070b040f0f03110d02190b0a02090a1202030d030c020d0e 80
    0x114003c040181c41481156100c1c03602940350380c071407583c150b0103100d400000180da191056406a070600180c480c0da00c1c01d101d94400b228aa0310403d0008285500d03284004800d807000d200303005801c2d00402c20700c04080d0414445420011360b16010408000c0240621000c9480224903110720310390441c1c0381692243c071880140d04140070b683c8454640200d401481041107030200135820f94200560f90440ea9102d8001d01e00100c0c09101d00194040c2d00541c10070060280400c076405800043c2580058a2007280301c031203041c2d81c4040e81c4507003d03810050a028948070b0b6144a4400790030346040c80302e03c0b407080c1c07001414540240d03039015200041c240007207414000300c01d046007079480d000303500800301004a080240c1501d51203900c04c04188203003625040000c0c4041208011483e0390700c00f00000540c191a500101c00c1c4c080d00843d40c950303080010340815501c8802c140f0007403031401d00070b40304101140101402c10b060754404000f0306007450301d2240030550106100302041101d0800044e08506100031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704611402 1250 704610152 704610199
    0x20c090f0a0b18040b16080435091c1e0215030c070b37111b01050106031103011710050901090b0c0705120f070503162f 53
    0xa41c0025015019021001d1000343c140e116500500d464420b0b43c80c1c44c9003125410100b2112000014400310100300001c00010401c20b071211300110b00031a207030011003490901402510b0952000d0000240c541c40303401c2000002c4c4102c5443c141003500c3e420591204520880e1000002c1e94810100030032108541c0c030200d072039103504042c220042d22450030220407515907204540c03d9404030703101800a42040707881002400c01c1d11541009080c41508000c03903101c0554000000d800082d01d03544101c0c0e10b00d130070f07a000d040c2081382c580039905d02c2d0206892890031500103800c402d040504055801d00e03a800f100080741c1c111803005260995100c4207090850400840700b00700c1c40303050308110034000e85e8501508071059140c011414483e080e141d000124040e445404401000d0b500900007124070701c0301084c05803920200c0000b61519000701c071303940c5901310f9004003074240074901000e9989061000c070402c3c2c4168501c08901c0601000a2046030024015600b10400d1240c00e40340e007140e040d04558a02c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704612652 1250 704611402 704611421
    0x7081306031d0c010203160c03080a03090312050601021f0209041b021218010806061204030314061c062d0515030d080c1b0f0703050d020c090f0a 64
    0x200410550321030000402401090841c1d0041e5018000b00c0070301c0b400040344030003404405030029443c10100719450400c400c0301c280c0560340400c0003080040401c000c10010318014041d581c0009490440707140260000c2003068002c0c51681c41c04041007110790b00083c1c0580d01c00351080c4510740300740310400c51102910410f0380312034006041a4011040941045200280389580d070203035a031344a201185100680506100b401c4c074408000d00328645540103000c11f68203c00058022450b1100d6500b0801444c102035604500096a601044041060f080c40303458110304102c41c9184007091031001b10600c64034201001d05465510880c05a00510700351903885a40d10b000e10a050740b5902d4002c0744000c00342240c89803030300b01d48804443c50358500450a094079500782d131141c0e6075545561080c000e03980c00c400745003101c1030801d00305d04e0303001d040c100810b039900358802d00240901421460401d0800c10180741d480255031102d49614001c2c3d98018090754802d4203540c01646541c0c42e11104e00c0944110003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704613902 1250 704612652 704612677
    0x81906080a030e1e010915020109020303181f08041b1d060a06050c06160c080d05070f02010203100608041a0403050d0b0f150c070e0903040501080906010e04080708 72
    0x10200002c050f00842c505624403421a034044442c48805074024480089000c5640040c4864074180a044080039078024006e2462000141d18036103a40840c1c69940040000002030000381250117151901d0704609100d01400030001c0b548846052020303140a101030001002010708014042c18030080040100003001d6140c81440010302c026407840482c2026648140550742040010600702d006208485030440030314020f00c030a584075908010b01c0c2c03065043d81d104010011a16101280092015104040e00100d000581d4204082d0180216550710100c6d8290390040c4200100f48030303040d00380000c40d0b0060903c480c80da952894072080100800e55440003080e020401d010034103900002404114880a400b003055140038820003041e00c0350800324a0703002c5420740f180a00d80030a20040c0107900803010803114010346400d88081c1c0001c0403500c200d01544041000c010030340c0d00000744be03000500880a42620b504100304016032010042010b00f51340ca000034910108044a070403161002d0145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704615152 1250 704613902 704613913
    0x303080f07050406171f0f03050f1605061804020d061403010b060306010e0102190c05090912030412050c070303030e1b03070521070905011814071b05150901140708190608 75
    0x45540d8447c1110b0750205079103030701c0749034650314415100103038215260401d114039000241c502001c11421798001c00e071503400810b0702d80c981c0101e41c582c1c1c00540b244920740c200100c1d4407401d02e0010b1860304c0401e0200f501c03da051203162081d54450000703d81d0050001c2c82d2440d101c14070200181d244c0385405040010302400c11620a0620424800120541d44122026092030300c0c0e44103c960350f50001c40000c05415800c102140000d100604116001c40711414a90b04020860b211181824499482030f004039031140c91151840c0e41c00e0109440307908550781c1c00309440701c0032030210350b685c11140106401444100412181021180502540c4c9580034007141d09240d154200c03007028003800c0c0304561180000650400800742e0500400d03540d014500e50740c00d07050396614030480705540450711000c1c600e026610744202051050000301c0c4c8a9070441c1401101c0e04000380700608440c50b8421040001481ea814015825408030820360414040d0811501840180c55040001d0055070f2001c407052090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704616402 1250 704615152 704615159
    0x90b0705070302030d05270409050a11030c06120f070215180d0507201f05120c0405220b120a03091401050412050a020a0303080f07050406171f 63
    0x100300c07041d03e10a40c25a2690b4800c00410380300c40c01050542001c144241203070005000240c0b2406e4280c62000b000406d0900040d110310742010088081951180042c4d9004856401c0800141005003020340341c03e8079000046465901c1c1800180154031400d1904e40841c6407240700300018003140c000180c8907801380c02d1060101c20329010880c05510346020f080211a0100c0c050015501c669410951f0000f0b006420840640c1a41d4441c240e560320640c40b805100c815818040a81c103528556103c10740c0e980600c2017168480800104581c3c02c1c480700704000e010355190304910000d07280381407030002c824614912001002e04800d50350260403c0d004100301d100514006444d0003414040c1c0c1761000c1150720b0301c0c03800f180c030364860100901103041040104110f8000700c2d0a005018020029609212031550002c0e40c4180c1950060f00015241c00c1444101464a8185904123a0034180325240c685003001c0a400d4610001250340d8003003902c000181d411148905541802146030803000e0310544 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704617652 1250 704616402 704616413
    0x402030c12150105010302090a140a0801110408010b040209240c0d05030105010807030603121412100617010305070902182812020604151407030e3d090b07 68
    0x400c01902c0c1088984000203a154000e2007110707021b07440900f10078090740c2041c8103a480010742e0a811608000c0380c00c400101c00c0c80c02e105103545540c0500125030b545241034a46401d446035404d8a5102e18030410020900740d0340c2c840c4d00c141004030500c0c0c0c0b00c00c1c80c000c440481003501078034162185070700030001000e294a0b0701100850503540700b62152a5142c403440380c100d007210ba05003c000c0c000c0855018900c141030140c02c2542d014076400d8800c0c0d180000540d000d442c18101920740f144940c4e074004091003615000282007a40f101400300280b12585192201076840045104803240580c5c0000e6022030300400b10b40120074040c01070100c2041081c00c04075480d07201480800007400d80500d1358082030107040d61010b4600c0d290000c09a0341005d040c50381d00c05290b00004000e40c20301c1440b42c01c0701b05100c0c1d40b4000e00b1300c181c0292900800071202c1018002000d044104421140c607400a8180400b031703d203d08649001c400e5501c040040c800048207960940e0b1907008000031040c08140c2d0f004024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704618902 1250 704617652 704617663
    0xd0203030402090f130803130623090604030e060319020703120b030c0a050f1206010f031a090d030903030e1905070f15080a090c0303270501090e0402030c12 69
    0x40c400c0d81c03c00c0907070f51100d00513a00c8602c1914a1800703600c1d8840c0c080046240710b000784d504041188600701c65500b039951060100c40103001540350141030a50b03580d60301000c88081507403103400c039001740450345040d41d4000e11003a000b8204902c214070100c041002e00790f60303042d558a50b03101c0e00000c40d600d040034280036104406001080c40b0180c24480401801c0c200450f600c840d1102c05010303030482d2810724082000c808504508660404c80c1d154100940540c10400c0074020150304860f050b0721030540c04d111f4a0161824040d41d41c51410300b083c440662000941c542a40307509240020b011113007442c04401520321418440118410038070125204032004010311000392045048070103503940c455503481c1d1028284640320b16010324188030100103002d400803d6002072403000011b030a5689517103200000700c4a4000f80c1c00030710b100343c1341c4060b0f02d0541030310307560445c503070240648a602d0080020070b0b0f203109000b1030850700c004101203011514200121034000e40c0040c00c010512801101407982c90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704620152 1250 704618902 704618911
    0x3270301050106030608030d0207080909071e0801051503070314070315080c18041a0c09040e0a0c050409050f0a06150b1612020a0506040302010b031b06041a0c0d020303 74
    0x3035280800001d06240244502821155184040c6090145140c1d000000b90401c00c1f0035101e0030020412000103030b95443c01d10303110340c1a90300c840382c10071250b81c04000003010f400130010078405400010b00465031440391400018180c0e0b1a2282d69644e128800c901912000e1210064030780c3c00814406916096080401c1150181c156291036a6580c514555a1804849104e81004454040600003030103034240f642d005006a81c00d030400412507103034000c451821122081441c0d000700780742c1440c0c54075000e03d01c042039216005000500b40f648503a005250280324091280b42c0d112170315000c1040510a68a41d0f0f0f80c08025510800c0d568200b1501600380d0300241c0c07911b40c2c0700650104002d45030b10150b910b03035180610004070031211966406036680d1010040c0041d842147d24860000c0e008000c842c0c0700c1c0d80319a0000c5030140d03c2905140c50704024400446905070185c401d400d031a120303807080d80c04444c0d0b424454400b100c0f030750403030000c144103540a004143c029021403d00e1142c001000794080e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704621402 1250 704620152 704620159
    0x5070522061410020a0c05090702120a031a090f0606030709030203160501020f06071407030c06231003050a0f140a0503031b190c06110d06030605010b03040b0106110327 74
    0x40000903c0803070310380310105001044011495020700050a00842280d0f0081e854012501c000c0019400810303c0e81250f6080c01c002611240c80c80101c0c070041d04446140c15065a002c11941081c130310300c03805c00000406503030040401000141100f80b0070f061210095070041e003500e0043c50b0003d00c1e026040004d0141901610548664070385420f4000340e0705104221030f50340d100c0c203500b0180b08445140c2c0b1042c0c0c141c0400c03425103503840100c0d1140c8078030151741100744200c3c1c1d042d5000300581c84a440004151541c102031036803017000820000f01c0caa1035000d07030051400844100324501401401d400c143d844e0070070300c02c50004c0c82c2004800001540a8061740000c201068244008a4290322580e8a08030107804018031106d1000c0c01002e03084100740c41100e0105034081c80c0c4e5405180f94204400700540e95407100e00400170300540f131241c58050902c0c00c050524516054680c02004601880743c0010010300711040010300c00e0903c19922400d6424420420182002c488142118041500e081c031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704622652 1250 704621402 704621419
    0x51b01300b09010e070509010c080406030509150c0a0315120b0403120c12050a061e030311071a0c0f06040b0402030d1107150905040c02061f03050705220614 69
    0x1541c1c500b548007a812074803649900100d9560304442200d00390009a41d45043c015a80280c10001d14040b0103000500b6040da0f00046501d80181c0042c9041e0f41c000307280000500d58030600510390250012100e1420740740c06d01040201c61401441108885070340045e13303100303018948000b084a0007440034040c85c000e035110a10390000c1e01d00e21085172543d61081d40401d040d0550401b0041c5907811855100e0f4000d000062050358410740086540c010b8440341e501c0204c0e0400902c109038102c0543d00c80b00304140000e01503141022800c00b601032061460480900001c100740081c0b02040155080540d0300400340c40709414a85003002c01d24500f81c604038801d0152403a04005c4910646450003207121500062002e04c1c504445c048a915541e044501001340d44240403c4548550207125250801d0b9801400c0c54541000080c1056034110b100c40703c40b0407109400c2020540000e00700003036600c100c1e90700902c072a1410820061140c181d050340c11050a180000a4025000c205d8242103101500e4005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704623902 1250 704622652 704622671
    0x5070512031b01020405010c030309150908030601090609051c240209041407020a061805190c05011b170702180906070e031005150307090f06050d051b0130 68
    0x500f40d0080740541b03400074410321703400004030740310350007c00c0d105008450320501c00c100b10480d0010307540c0222040d80c10341800014000c0d00d50340450202e00404a034949081072504210002d40d030340c9a030822018118045603016800c0c0078101040060f0351102c074000410780d1603a480058040d4214010032841603240c000c21501071991046d07118813a82c11a40604100145070781e445004007865601c220003480030003840310018408000b0300010391801e01003091401c0051030040c1d400d0f0055040345040040c4058149000c07041006c620420302d50054025035200c040000000b12030180101c0a58085c40380910b009800c00e618104034081e41d1181c0a48001c0c0e0b441c490213a81052a0170191a0180d1001c1307203d600e40f061951220341c104003420342c0e204d51044000c000a18003000c030303004401000da48210600c0c0d071941c544038400080138283c51040704400a81c8800340c0350411026014010700c81d606c94959a0f030b101d0041750b84800070850041001d1880200103030a07041c40300c280e10003054500107691 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704625152 1250 704623902 704623957
    0x60b040303200f120319110304030822061a030606011407060e0d020f010b09072106050604080a0611091c081204060b130c0f0c0507051203 61
    0x4906594041c0c803810216001240d00c0b240e0903601a6408402e40101d0140c14040d040a1290303d0000151000c003540301d0810b02890b9141030b0588040d00c010524044030b0242440380c2070b0079a03500c0341d01070070000c0340c56070365240c80382001c0b40503803c061452501126404c2000515400303000601c509140d1908010a500145039481c0d40a980186c04109825181c1340c0d0410b0703100c010017a00388108804506070300700320034061902c3c83d42c04000c40541c02035080e603054400241f045c03100021080701d02540a082280d4042c01c10300e82481c0141ca03200d00b41661140e440c4007a00030f100104000740032203136503136aa40e00c0280c440011110403580b080c02c00840450303d240d480d0039200410300003410310118000c440720a419009000c101190012400d0104d04481900016881d00c1980641c0001c1000e030044010810750260080340038030b80701e1a1801c10610f0386e9001005501c949101d061401c462092070030700030700d80005940803d504c03040c0f11080540048001c0040c00503800090040b801c09013100b102c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704626402 1250 704625152 704625157
    0x1803290907180b09041406100e04060906090f060501080d090305280c081b040213170703060e030a0905011d1c06050f041e0209010b07081b0c04060b 65
    0x4011680c0c400d034020701481500c442804101d0025040c0003400f000c40c031010a009080440e8203a4201420401c0012001014032505500c251451101e2205a00300500040705090250001e841159920000c0c0100308030b9500110409410203070000c00c90310945000c00160000f401020414000c501801d66624020506072050700d44c090060311100a80340d1450050002c0c111342002d4000e48400c0c0b460220303206141c0c1c40c0152a6050150509450074140520524000003015020b244100b011b07039500c0360312040040a495a40f00c401040c03001405c0b41030b18051071340c0c0020340131a15020b010301c07400c20300100402c140262515181c000701d50711001540e400d02d00b0b003944544a4014040c0c81401d2503d00100480e0500340300340c8102d582d4080d00d408085038000c40708010100b1408040c0070511803640c2039114415000041480069003603404101c0002d410f118259005401260220802504006445020821003028508900c4202401c2c2e6140c134011304060040b8980800890380c01c280c5403c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704627652 1250 704626402 704626411
    0x4110307030308013f05062202040923060f0606040b030f070504030c080a060b19141f1e02060f070804051501090c140408070302010f180329 62
    0x68505280c1c0c039100155021140c8017081000356801140c00031031103403040441804440c8407000b820080781d01e521b082440c00300058500e900031107112244541800600d186031001c40d80c10354000c51503029514040801440080c40003254120340318880504900000304c4520440c18810400071a80b80c03070042c043c00c0e01c0703940608054000104006001030743d2810340550000010301c0d0103032609540ea20307030b00600149034010007844e80201604105000d01e501603440c1000007102c00907030850210040c510400614401c030b01e0000955a07080d501a80c0d481d1100c5c410745903410b003001802c044c0030302c01010f180100b5080e007803003042901d00e100010b00c0080e40780d108501c0341e8424041030701c40c03030750a4941c1d41c0c1c0208100c403103100d01c51a8a07003024007400018003c00c80150f01250310b044003a0042c0c44010000341c0c00448240501c820006d03490001030300e604a03502800e1451401c00034110031104442c08411101400d8140320000041103840c03480610040c0072403649100c4690013040001600300142e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704628902 1250 704627652 704627657
    0x9090c17031909030c0e0405010b040605010509040f140c120901020304051b0f0a060e10030b090c0a180b03011502010c02150703021e0304020f0303030106080a0f0f0e06041103070303 80
    0x1041101042c4180428500d4001c2e5060241e0300701c0d500c0d55100d242800319046140180030b20018002000300074000e001e41c000e400c48090009a0810300020030724007413000305911030790329610404030707500290784080180d02150960740c5140c608682d50300010350181c06040340d00442d00000454000040c420750340600d0780800644001324094504650440b01070030101c0d0720a00002103085241e560758514030091044d40c4a0f101040108400c02103d0405034103008107260a1a460724060760315091580c1e07000c00b081400310707192030f003505040302d4040343d201c4088402c40b0341007008100b116801c0c1c040c60403642d04014a4000000160040342650048100c2c0c10150740b1111603401e0024001c091580c2c0113403a85001818a07000003810903840440c052001504c29000044c80294203044510080c0c1d240300398000d504d99454140000c20800b001403100103025a5500b4410010f595a0094100f0884c000d0081c00140764035904540c80301c9050b28100c4604495034642c551030309010070100704483c0c240c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704630152 1250 704628902 704628907
    0x306060a1202060a2d03060611060a05090a02100206040615050f09040311011a0a38070b090c0103050906090c19051203030702061012080a03110409090c1703 69
    0x40d403e00ca800d401c50002c410034801e40341c0704080b4819101c06044007511203101443d00072144214042c00f02c50454204030100846010a401c407a40001162a000541b005001131259200c55280d4101008618001d40c030864000300b5080999002403401c1c01a401660300300010310320030366604022103151140340d40002c100a46079603280740c880e440070f40c024001d041403404007810043c05802c40300214550600c101d810203200020741000715580002d40440320f556400609001304013035201e14011150074421580030440c0d08a4890081a10a01d43d84000402000c0c10500700c003980710b40309071100d20f0000380f46c0341c0000c80010340050010700a071911030150208c26682c2d014800c0d00508011401c03458143c201e0b0005950300c1b402008a80b00820303002854490500f540000d003401000b815610700d541c0d07449400d11070010300b000800f2a80b030f800f0341d03495602c104445041d0007070b2040c40d9421544010104000550340c03030503086140caa074410f0404040303035070301c441c42d030a0f03007107411284003940742d205 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704631402 1250 704630152 704630189
    0x804020f011b080d0c1101140412140301060801061d09070e010e060d020309100e1905210a02120313030e0d050304140909011a150d090c050306060a 65
    0x40e081c0d02c03004401c11202d04060b00d8064941e040568030650310001c01c81d503165041c040a503800341c40f8100b0f00718084000d00c08541000d04455251070090704c00b0f8078100d101d12020710503d014004828007a55103140c03658496170f4542018041c4042403051101280030034042050241440c400804e0007a070040580080d030f10780c14000c4419035451000c0c82c1c144000c03000f20350340c950342d00d10192194809500340980d403841e000f8450340c00e00b80000e0302020f1807800c1c810780d5080d00d14007103015200619480120300d0201d43c541400391400d29840412228011514009404200ac1000a01160442c0d400f103ca1500c0408522207141c48116000848040e800800c0c0c40020f1184c440a0031801d170040050032084c2c4240c0b1131500350b91165000c10110700c003c0c400b030317411030400300140b96104511100805c0303006442400f54401040c022409071052942e1f40e02810703105ca1143c141d0f400100c80003404c0014080320b151503450700055000e0507220340304920014143c1e2400301c081c0400e071110f5a1150307803914803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704632652 1250 704631402 704631407
    0x140a060b06120c0a1b0c0602300d0209180124170601020718050703110a1e030e1f060806010b070f0303270210090b0f071a010803040906060804020f01 66
    0x504502085001241c2c031640a641719061140c59003d290010f609924080000c0e140c0714a00303009201c501c24980315481c00350b4a40032034042c040c00035510107540c0c0b10003c2c0d44000911800b4000390f407110722036004c00705210500800f9416a00e041580320b41010005041c000c070007040d0341c03404000440c1820b610320000403c104158002c03006004648486480d9501103900d010b034540c90503800b41d40d030420800c11940c103001d00e5041105062480d4941034070703440010144200b403030100d00d0421044442c103450034402d90151025000c03400982d42503100c1811690a61078020131118140c0e03080c640301160038440450818100c480c031255041c40e05541d503070780100e802640d0344160103041c0d035549040c00400030000310810301034603107500640c000c990303104024401503203d10200404c144a0310078010429906e00b00e42e00e08409081d4151643e030340703261105903900b004c09040c00400240d800010038040000103041580e07460f000a101e210340781e1204403004e080c121006544108004556a031030b50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704633902 1250 704632652 704632657
    0xf0e21060f060a090e0f01060e07030b0402190c0c230102150603190303091b081005150d0501060302060a080601090617061e0a06050d0b01090513020313140a060b06120c 74
    0x310001b40c403000791890850030b08586980c0c4c001b800000b1110100f11036a40e06101d032024680040701e0841c1090400f56410781c26120071404541801078400100007404426130f00040188500380da641907000351541c00311090070b000c844180c090701c10200c02c1d80c81c0d546613045040c0f0402015005280384200010918847c034000d81040e81415515498407001c03507038620f101108130101c0403614201524009036940390104021600180616203800d02a44030320a13108644034802c2150900802099410a6401042c03070394002548001700051421200390041c0b4000e2090200740c03503602d0250f580713032810307102c0c182e05c1450341060141442c002006851b01109440d01039021a094500f03600c440c0c00072030b60700708817600108040707100842c0c41451490f041c020710050410038039209104901d04400300e004c0720550080f50740c0c1140c000c000210300480c514082428290400c100007880710328202e0103610782042072030550b22203080c04505142410300004036400c655060180c0c00c15a520403d28000d5038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704635152 1250 704633902 704633921
    0x10306090509191e03080103110301051b1e030112020f03060702060402010f052109061605031b0913090c050603010b0703030e07270f0506060a0f0e21060f060a09 71
    0xc0003840a0215030300b032008141e1583c4d40b1a46500e0b84550650518003031b170b404040c1a85119a0405080100118680700392044080030340416507190362014006003015034020a1003140010080000600507080814001085000fa0b420424603455001410346501c400c6a401e000740c0d000e5030101d4019407041444407099011458110308041d8807003012a080c181400100003022100030a00c44401c0080c400140c110f240084a909040040700000d002030200811079507540c545948010b42c40840d0300c044443e80000103210503c1c0101c0703070f40d8100082c459028155000c03070242d0740101356418460200d07030603a0380200d40e00c0d0030512a0341d800c1b8050510154844214002d03031100281c05038940f501800c00344100b078100044503c1c0b0340c00c8002269020203213070071480d003031000380700694032500c3c00c0f00c1d184c280c5442e05008286071a40140c4000c90044c24083c2c00440d904110011600100003c09055145200f0303036040351140d00e00b402201070291401c66000603581001c22100400c0d91143c00c02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704636402 1250 704635152 704635163
    0x7031b060902060309060a2406081b030903030106110d05120604090b0c0c1908040510030b10111c1d12011d15040302070e06121b01030609050919 64
    0x14141c00c0d90104446810036602c01d00d1030790124041c025010741c00c0c01035041c44c8050344029000000c0d1440040d1034401544210824409441c002ca000007403110300a1400da840c07e180d580e0b881c1801c001c015540c0e88240f10722000504503a44032040390901055050300b880160ba503250402c104124403091020015055a900a40e604900702c0010400c1180e94852a4007642d500c1d200d40c80620402e042031034501301c00b4011001d40c00c981c0001540303141990180c88058807119150301800c01c081d0001c0054400f0164840e02d0f0300a0302c050f0590042e00900c440c1e000c01c0542d48005d40c2a55004511a10621050701245800d803181c05501510100d0b03180d11280100025040c0c10680401800c44000300380c100484440e9241014028030104a40c215190341c60500c00f0702c074a01034800075190380c480d01414142019901c0400c0c02a40c0d0903045c1001d018986013a02c0a0b9400d07120110400147c140c0f0301030104e03041c000d0005541d000c9100300ca125032020009803041e0490008646204d10343c0640444c2c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704637652 1250 704636402 704636411
    0x3041a0309011d010f0b0414070c0201050408060c090a080c030a0210020c06040b34030c140d031a0f010504090b03031b010507030b040c020307020d0c05030f1c030207031b06 76
    0x35400c0072004080f2602c030701d5000003e000441c0d09005000c2d55201c07034409001c1c0f42091403122101b00030300c10172540b2103810324141c0719501e080c0c40100d466115a07030000c1c480c2c0c401d0505000242ca5568024254140226001142541c0d16448142c40d206185160342e0305410509110015040560f503035200d03141c1c03610680c3c00d4404001c0000700f10360815003021000060104e8100c0d10f181440000390041082c0140b40703440b054520300c00030900b00ca1914010304018070068042d0422984c9412030701c550417503c055079400031071208018010301e2000001034a07581990903000300c03030512101c88500c000d4103035240c41c43c0c5418140240c01920340c40402640600c0104091080716a030741e90002c0e010f03401c50001083c81d051090006050b1840c030440c40d80304a00d020248505260000111160154152007c01800c801400c20101c3c49803140e01c070a805004419155030032450120350f0f180185038000f43c6e0314015914a20031012400f4016000700071885600792901584084955140658841c000124 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704638902 1250 704637652 704637671
    0xf0f0c0c070902071101030905062410020c190b220504020f040e01080105062101090506160215130b090c0d0c06030c08060f0f03010b06030403110f03041a030901 71
    0x3807a00c2041d41c4080419580422140c0811600c807207a6540140246418080300c403554503007039111600941040308645c480320004510909a026800c0701e40c10042400305100d100c010081d4880f449265120f100703d4000d00e9018035000c100d4160010348014009160500300101801ca00424280c01d0403001420283c4001625943d58001480000c0b800c1d07400b50703143c52404040b00b45104041e0444040ac1e410201040b2454858205800e401c7c84888410011086c1c44056140146010322002d0070500608080010342e4900d0200c5090400d515400c0780d04060984401250b0318000381c6078031101e4040444034a000c5030701c04071650f82050101c000e45050700030600000b08035141d140c10486860445c40000c1200c150903120740c003018429410a1000c1b450040001130185200c81a0184941003085c400710316034a007580300703081c01c100150020759241420708020f04910255203c1004d00d111b041004140014048180c800701c40d0b40800c03032000d601b01a80700325120780004001d4841340d9030b16006035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704640152 1250 704638902 704638927
    0x1803090901080a02121c0c08130902190c0b070806120a06140114130e0a060504050a06051e07030c05120f07180b091c24140f0f0c 57
    0x160003080c41c1030041411105601c11302c90224540100c4101c10303007048520550040e1b030103042002100c041d2800c1d00801c841c5181005603409404030704510a241d504010508440c0b079801002d9000d00706100c2105000320400490710703400c0510b8005c02c103001010100b000c0300c5c0140c121700e8002c0c02c000c04c021f0001074409400d5180466442060741c4058031075568001107880030003203502604614102d00e40701101c03c00864250304d4910b000703c450ba6035889103405075407030600c080300324964486001e016a05007410942e0345d502c54050240e03015860600495412492100000030038241440144101c0d61050b50903002040c54840540074440c003080b085440d0380100340140d100319010703404129641440c890060031082c0001401c1c0004089000501810021206030f031078042c0d0071078000d20107081c006142c4101038003002c00100080002c41c0011040c015440d6a04500e002d00c4808121905100000091034907094078480c14007215000401c1020903d030310115030014080d50b045182032517482a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 704641402 1250 704640152 704640169
    0xb040207050a03170708010506120703110c010608060f040b150109090c180609060c0803090c0409050a1e0c03151508010e060c0a080601050d0e01141e0906180309 71
    0xc80000300000d96030903001d4540300c030341394006100d0301c0c24909030b604000104416118481800c043d104c6c40741d00040b1018403c2d0030480d0f00500060800b601c69a81105140c0a000e070f6000300f10b00e030700503080040c205050102c2d000f4070554125074800300540f00c01ca8142c5422605d010020704000341e02c800801c00d82007501400f400c105450342c03010103480d01401c28201c50040d27608024104540808100105907119491520792508280540e41c2c0351111400c0d5840c01000a8003a5085420310130302c0c4023440310118250070300600030002c0000d25041c804200a44035854500109600400780092020400f041c11548444112041c000380000070154052102d4400b0381c03043c0002d80d1070301c1d0034604a45d000e00c045600915048400d90c1048603e880182000e04014030b9103040110116043d400c041e1781d500240c4290400c0c0d8002c1220300c0c0c00041d0080556021545a00f402503103441e00400760107c01140e5200e000007a000d001280c0328190900040c01050300c00d08898801800842c0055036408207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 704642652 1250 704641402 704641423
    0x20309010513090603150c2c0a0509040819020a050304210f050d110312130c0f0306021207020309030601140a1a0415020f070521030a0903051207050703060b04020705 73
    0x4a8611207a450710b412002d03581500031000405c005034411014000d100013100301220784a03235401c200c0114001c0070841d0180594031140d44a1240001d0006100d0003034020129007000003c04c1c602000003c4c000d03a518110024014441e03401041308010240c0c0d000c0740140c2e80000d6031441e189001d442d031030300490001c43c5802a5141e420100c2c0c070b20701da160401c5034400c3d8001e483c80507508000030300c1031010b866030300109036607030b443c0384180c2640c100300fa0101000080e01d0003a405000741510f0741030420003900034a0040494820207004509107600000598060780f00c014010003040e802d00d040300000600d4041906d070000840c9002003126040045c2082c0141da07000d0120b5203c510b0b10840d20800e141c0c0c82014815500089841c000c1c00303002040300742c1034907001c0d1742000100d402420300b02c9217a0b003c51781000c40c0b4000801c9410010340d1100c003000c100c078041d2044407c05044460003019910030349000a2969000420400004070180c100f8010403400034401410309c15036455141c2000038612 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 704643902 1250 704642652 704642663
    0xa0807030b0d2312040905040f1205070b1506030411040f1a0f010c210c0b0403020c0906010914150408060408120c1c0b0406080d0e041b020309010513090603 69
    0x3030701907000d0307449a41c0c2c401041c003500000c02d00d1039504034130349416208a00510480e0382c0c40f50b00103000e101d0891000c45400ea842021b24448604e1201c00410a4101400491701113111102240c43d10a0054180d90800c40050181c0d00d1900c4aa4900030314460001c5141d0b0480c1c0c441c1100b811111251042c02e000d25214401c02c0300100444041141181080f030105040c800000401d6001c2501101c0742c401c10032402c481c4159032111803806a800380c0d00d08074000c0c80003560320204020554041030011203604160750342100c40d100c0c0401510315825038014810004c982000c15a09440c052039080b42840c40282114502521031243c2810001d0440f800d5030780140000e0055600400035160b55440560748419a04000c80c0200c5001c1c0d444600704000c8804d500c5a07092403056503260701800041c14444201c0b00302d40103464000c0e01001c1a40150b40c46185401f041c003040381d102c070100d4540903509901444c80c04038230100540b00b54014204140d840010003c0200ea038410314442c00d00a1400303071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 704645152 1250 704643902 704643923
    0x150b011d010e150c01180c030209040302010f051003030206070f08160e1201060e011202010807050f13030b1e0402030a1b08010e070f210b06130519200a0807030b0d 72
    0x1002180c21345071154106e8400381140b2050078045988800c00300700b9250304031140d0b1079944440c1000c0b80900b10380321800a5603440d050070300c0304c0300d2a000d81030000c80f031081d0280e50903662040707003c0d83c43c00203025415012400b08400500307200d040c0104464880100d0a21161881403a008551080e141032092201a9900d24082c01100b00401c1d003613006003180032a03052100907590000308545c81c003620340300a024011804645035800740f429241100d848080700c00c2034550324200b007070040009541500c08020500c00082036680004101403045802400420384840c556980f1800c82c08080c203220030030b51403010007007280350f801e001c0da2460044400050109178100114503841031120b52015058050100701d1410400d46a411080c2c0c0a0304994045801d43c1c4250106059032032801d40c2074103642c0352104004901d05010412003402d030034000b08010303004442240100305a805103002c0c401000c144680c000b411721a680c420b503c40703038914010440226034404035841c0543c0e000d045480400f075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 704646402 1250 704645152 704645167
    0xf030901020c120403030c260a0225030215030406020f0706061509080c010c0606120309170601122022110301060507060902190b07150b011d010e15 65
    0x2000705220842c200f107401d41c034051965501800712603c0e01030041064a109000e00010440202ca40310b001d0b03407090740c407941e608403010000e40340c9401c5079000e40744080c03001c50302104000348064071702904da002e440b0381d181d11610180c3c01c1c1c064200610444085408110614901441001900500303208060202e0841d013400f0341517203e818030803140030810018103010480d80c540054200c0c4034060a081450303400303230030381084d60180c400d9400522000c01ea526041c010160300c40008822a100024902c07031350880c45500d10b40340d603000e10039007065203900e0f01500c021905402c41251000a1091010b007248100c0e4007141c00c03c0103207080e0004000090500300700c03507080e5000b00540d1004544c505403030b6604001d07001d0182d000300f007000741059580d4000001151140140314059a0140c1c801001c0f0300e641300e010380480d500c2050100c0701114400e184140341000d41c0541c3c0b0000005858090012a051280011522802010904002c1615a80e00142d1101c48000c2c051440000c40156908039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 704647652 1250 704646402 704646427
    0x1204080f0609161202030c150901030f060b04060f050904060e0412020105072a1506031b05061b15150f010801080d08071710051f090312050f03090102 66
    0x40c642000c40d00030f035482c002007205485061041d103103041e0b0038294601c880d00100e850070945804484d0445842e6012200b03181345c802c090845010240d80501c45044910690400d4074500d21610711240c1c0d051105100f000e024103071103020410a86001820300030880c000a007a10510380c48181c81c84101000d00050018509810301c8545c41230000740f14a0401c05001002e0380b003583c0d8040000000c600188460303540344490092110b410542c0f41d80c13a040380850a60042542d44021200150200180c0c46541d07511241e1000302c400c01460f49051a400c14900d414a41c502d148500c0c16000340d0280c00540d0308801d40503409110040d210800000f5000103104909844101560510042000410a0300c00000d203480c00340301180340c01225a140c84a09556490780c014642d1903001a210820812040d14080d910840e00c044031a52500c001c8101d19002c0d80107152245000286440d8007440484e4405058400d81c0186c0d1820501e00858940c84d210f9540040d10083e9040c0d4001504a5481c40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 704648902 1250 704647652 704647663
    0xc030d06150f1b11060f0c07260c0609060c0a030306090501080f030409152408010b0a050304030c080d091a0105061c0509160303030203090616120b031204080f 70
    0x4205040050801500c0e143e114682c5000300001807140035442200d101946a2005440c0c1c1450188000c0351074005072000340703450305042d009107001442d00301c2d04101b0501540c403c20301e4946180010345550101e0400f4070407580d02500c1c400307401080070801025880020800d801c041c0b8000d0b40c0000703449040c007101c00305481c0b040e440300c895940200c10040100401004582c101c07103c0d1103000450340100c41500c004800709070302020a400341041c4009412850a0364040b1200140d174800350b0b43d030b881c0c4965080078021003c010000400500c00900081d0169194445890044100383c0c242007241080303c081d5450135004440c4901c00764004411500d403d0411805803074111026030030300c07104685104851140c0c102000d495500d0344082200150300340a0f8054115009100f01c42c21a240d0a010b8080d501c25a003402240c490240014503681510114000b42001980d40c44803044188405e1406081195503403541800341b54080400e000b00c19006100404e2600060300d0b0002c00f1000c00c03401c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 704650152 1250 704648902 704648927
    0xf2e050931061401081003060e15130c060c1a0a0b150c0303060919020f07260f1b07030c03120e09041e050111130b041a0c030d0615 58
    0x382c0c1000320a100c5024805041910180c2c2071810141c2d9030744009001141180c1e644c0041c102070725148142e070007010042240031001e551302c81c0900d001c1d150580440c86404840c0382c09030071400802c9003804040c2c801c1c4031060820b40504c840c00110b81290f94403d188400c26103001140d20303502c503030701c1005083c012118a0084540007060707040c0b00341e405c011603d9210041c0214410000040042c0540460f2004d10300700c0740e201e040464965000c0300340c0303888c0d66001072401c0c0c0d2000e51060844817200106185100752050444206041c41c29403421503031103402080e44003290308400110071403119030803c030010003180207401c40c0754000e166060030b8100d850a142c070300d000c00c04051081c001d90b455485596410581c003500a0420880b04903084040c1094160000c0c0554203150001201d94202000b4082c5000c5002d00e48800d03d42c6c2e0300644006118a00c20417048002c1d541c00301071651094400b0b000245503000c01e40303141489411003202110415048030401d1840c451060f0119a4480003040381d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 704651402 1250 704650152 704650249
    0x2010617150a09170408030403031b0f03030507021905060402010f11030f130503060f0a0f0b010c060b27090d0311090f131a0f2e0509 59
    0x969110040d154500c010815000240c0700c050020800400c60101c103000d1440135201a00d50780c855800b00c1d1250300c144415400244401e03045000300c800e9603203802c1c40a07800b502401655100396015000380c0401040c001c01d500070441c5003510503400c01f240c440903d10030340143c69075107454070000d01001c1d400748011080106c91445800c2c5400e000044500fa80c4a41c01003946410f5214011420300b84240c00164060040390b0038001c45004400441d8010700a140040c00181421810b486c12580c80c0159680040e0350440d5550100f40346078024542c1c08405011008000001d130a030004012024a51090b1100201d08029030b0780c009102203500ca6010389014080900500c1104000d0300800c0851481528160001d0403190340b904203000f0103102050050241d408941c3d0b1315640802d0303140fa4a80905000d0f50401c41e28600901080490956403c0004404007804c0c2c0103204900ca221201081c4542000120015501d101c1010445140003001c0c40800004460409007a43c0751a41341c2d03203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 704652652 1250 704651402 704651413
    0x90b070503280906051c0222080123100506070506071b08070803181605120706090b030403030b03060a1a24090a03152301081b060c0d02010617 63
    0x444680c0070040401302d0f40f0500c3c3c02500e07480fa92441440c01340c3d0008025003030300c1c030000c1d0300b040c5c0f44840755610804014000da0394180310ba441c0a03e600780c40d89008644605c0d218031494480d070031055004290040c02d1501103124141e21440410b400394481001901c81368402000c001d1030b40e610606400303001c0490541140c40324002d07640c58080d4011043c000345211800300009280d09075400c0b013945658000011039444c0941c4250020740e8100e140030749802030307410903208800103400090080c112142513907803058039490040032601c40c0d003019000f10101504c490f003c616a560801496010f01641c0f0b80001e5680c0c04510016404c0040205140c01840101e0700b13140c0d2028494200d000403a070680c1c15030307038685c8c0140010f42c80030b000e03810083c549031000f41d0401c0c042c80c940d4480b00501c260001300500c08040407061401d140c00074030444017194000c0c1c6a031400007200782603409801c01c010b00a42c1c18014004001ea00b443d030011000300050f90b48000821200a44068028104084502401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 704653902 1250 704652652 704652727
    0x50c030a051315020613050109021009050315060a171c0e041406090f10030c030b1005010503010b040b13030204020c0c0f06120628170c040e06040f03090b070503 71
    0xd440717035401020f50542e22140007841e82804404e4101214081d4001c2103540400c640c0c0780c024103c1802c500915009101d001d8941d542c086c03c1c0e06086005020040040d4405860810700603442c001e50040c2c07551a015000211902c1c503002400e10016001649418415804c1d00040c0801c0300c03802d44a603112184400c0c00d101b201c1e20360002c6a9000998180e5140c8140c2d500409001c0b440047d9000800028000400005201001048500404000d8854820a6515001120103010070b005024448600b004200003900c40715000700b0251a400d49262545603482c1c000608030f1700280c540304400e81142175908410301d080b54400701100412100365080c10511307441c1408100d401001070340602140c81e14203150403034120484480c4a61030000c010701941b02c501040c030030001c84114220780e1088491061082c50507015580c0240980c00041040f036035107441d40480031464020075804d2044602d0040ba2648209000307210150094004540c0c0c0d1300d40405044100d00200003080180d104a1030b010f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 704655152 1250 704653902 704653907
    0x11030402131d0703050a1a01080607050d0b12150a1e050a0609020a05040815040843110402030c0702090901290909010c05040b0a050c030a051315 64
    0x40c000e0040c0320500181880542034200001e00b00249405818821444000100a130000d18015128411705540c00eaa29139803400c40b289110038043c8071340359000300000903542c2d40314070080c0086042000c000305007803040e40041803265a540c800301d0f00304d40001100090382c0100c5084e00343c0100d0316030010003038401412101d5120b850951000c0900303d8943c400b00c1c126aa4982140001c3c000d0350200319036600c01600044c107254001e20800004d801800b0044001d10b003c8040d042c411038102e1a11450304e440051000801000d1074990340070800c41074866110400c0400c5903040c0299462409117103408541000404030082076452813040c0d0041007049900e00780d580580c1c1ea240c2c1d05449507070b0b094589150a90152040c1d0000c0c60550100d400c494400300360502c814036400c01b0030342d05041e0700c3d115000d1042c00c0c0d5840c00540404240100001c101242c2200014040941c5030f203450b50030815141841411940100301e18000503001089504040100307103030300401810046a040010342e07201001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 704656402 1250 704655152 704655169
    0x105040c0806061e0d14040209070306080307020609041e020a030609060308090d0f06180c060e0d021e0909030a11030406210b09160e040b031903020a05030307030b010311030402 78
    0x9445400f003c08038082da44c12840800d940e2081c060840c01d00c000c0c107080405e0382d6540c801b160f007680f01c0d0340000089a911402031007100169034201e0003441c0380c401141c0900109900000403240c00941c1e409040c0d5844d41c80409540a180711905c5c05aa58900240014265034494000000f5a071401b9010400240b800c02165010b0b0401e4403031608249080c1004611151000c0c8003030960760034800105200180171100175031480c401c000c842c0186803500011500075100d040c146820801d01c8115102602d01841ca511005295100d01c403880c0701c01401064038000c00340e422035400c2e40301043c5501c4840c0c00c5040062011403c01c021820170b858224010440c2c0c0e0005e040140e40300760800028800d050b00c0d00b060362000006820a22242841c9461014024a0b417801c0301c0003e41c031a1080403180707002d00420600f42001001131070710035507a000c15100700c00030400c102c0542c4a40701c104000160144040e5108114544000810f00440d0001409032040400808600a0104100801a40c980b00c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 704657652 1250 704656402 704656417
    0x715050702100908030d060e01120f02040e1905030421080706050903070f030206090723010e1f0804050c0a0b0415210c090e0405072c0f0105040c080606 67
    0x200480481110350b4141c850041a8022000501000650360448132003500064121a0201c40480c040c0c0e99450781000704010381e41004095600b0003081101510789a0060b2124122860988000d80c080e500300c3c040428a004048486810108e010480070007202d828040108032141c55103c40c1c110380e919842d0310310400c07000826555441d000708020f10020002e945005900c070000851000b82820040d40d2a03104507803103140344c4201040403590680c2480d0501750404525054490801544010f4403a440304040035504000b901c0318800d10311061030603845005000762a01c0d00b49083c182000c50500e042c10300e03400d00031403000008101c1d20004500700c904075401290300790514008004215906500aa02d8140040310b0008500745854030303600c030031806841922495516552100050305005085070083c0075034100810421010312260700144040884003110b0008110425000e4208142038400c0c85020442c040140420b04043c49803841d0300c0c2260400348410302c5e000b0001280f0744542507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 704658902 1250 704657652 704657659
    0x240603030f190309290a09080d110928061701121109040b061311070605070909020a031a06030f0103080901090801060e07020d0c0b01062604050f0715050702 69
    0x15110900750f2180d8007804040ba0b11402154003414800d00c035034502c071030942c004c0c4014015a0301040003001c09101f5144002da0101c485410702999040f0384c00200540711a86142010030800f03010300e0307601c0040c600180030820340845060084402040114a803540041d8280003041340a00b401041070751b076a5044400600c42101c0b2803900703141116218a000007081c2d00000c20b803003404104102d4003042445407005a611084d42080d500142c0166162464075407801c070010440800410001d030031581d0701c45103a040602095595545c003208903444a543c8800099860040301700c1611060390a40c4200b108480050660510030b0107184108810320004020b00c5000a250100d80d0080c4401d10041014100070800360760340d620b2089001e00300702c0f021001802003400184255005480c00e8144c143c1000c81b540e96a8204401503d220301c0701c90800651800a04c1c0ba4650305c101aa03880d03104502c10390107450b0303602150716540d00c1c1242540100b41d25485402c3c400340e41550040035104400c1d0102d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 704660152 1250 704658902 704658937
    0x150605190504050616020f010c0201050d0c0509130c0306060302031512010b03010608060103150e030d090507150f0311211f0f230d2003240603030f 65
    0x300d000c0d140c5104507401203410400214840b41983d8490201c078400500988002c5136240b81040116001000031400901040301400a82d09482d600e92103104001c58070304049182c0081c141c00a12041170305800100610f413108514120103a00d030103040001c2066060960860500080a1821403101118540210505484820080001d401030000b071503000c5e00820000e51039202e80c54035000c0902040d681413000c41441d00300300712940f1a4445484031400a11b0400d240c071360749000038148803001542c480c0305da1030300800c00c2e0042c001e4a20746407801d512028055880304201806403000d2840b10408004244032264604044a049400c0c0c5118000b1071319642c1d84800400804040c00029614031070810000810740650400300c0304190f400030010a402003100b1000680d048881e0001907401480c01429503002500081103074030b09440e00b0441d8a170362101440031a10300a07060100304880080314211251080141c2a62500b00106074007852800c081090700307110b18801c5880d101c0f83c10210 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704661402 1250 704660152 704660197
    0x10b0a0501090308032e081b0a1703040b18030c0328060f0204060c170301260307050607020c040e0c0d111507060203040b0702010b0121020d0e0709150605 68
    0x80e5032006400310010126030b1402813039184034042c0d800ba2070050654070b21508041d231403525103401445c0003250300144410310003400c04200d1160002d400a0308210b40c03006000106070b8801c02c50141485203501030382e4070355013910036042501d80418100c07198001c0d0045c0c0f09501c0112070250351241720036810003901c0726444803490140020001c110690340124804180420f001d6400700480c98181d004002c0c0c40203007403400700704012600c821b126004280240144a0940f10052a00712840301ca0a0056900b014003a840316400c0900480e1790b100140c03c05148194545094410030303500c0940400101019026500030420071a4030180203490880240440c40056581c1030000705a01044248141c50350803924210029410949041700c000d00c01200058120b03105114042d24136405955020071103c6c001d60307094042c40b001c41c82c001078035020414117650b910305009040000b460040101091803400c40100104c5031110000c103c410842d00042084d50791001c152442c4250002c9031105030f151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 704662652 1250 704661402 704661421
    0x1020a03031a1804020a173703081603090c0b0d060b0c0604020f0906031e011d0703170306010c060e01020d1107060b0a3f0b010305010b0a050109030803 67
    0x390124441d603c544040c10140c24000750084a5001d1442a41c004035101d45400221945e04c65601540213594402ca40d20801d80c03060740302c071030070718000c5140030200c0700c14002c411102d1070130082c0250046818a018000410001c68019140c00300f03515081003903c100d683e40c500240a14452280f090402181c492071448095010000800031403020303940d00c00c0c0004906403988000c070b5040c6e01c1095030000070a031a0a0a00b941e51180364010041c010380c2c4132080103404041145086c0800c2c43d035a60140c5030000e109080d90313010601c8204000d141c0b031071451500303209610707003200100300c511018018000940d801c9203150f0841ccc0e50109000c248810840000380c024007408042403409400c2c448240803050014009200b401d000f00428042c1003010403c0c44170701c207410310854403c0e42d007144403100140c900082c40c1c0e0b4aa1010203046040c000d5a010f981401c40d0303000da00781e0f685030002004100b0030000b41704040080c1d6003581c031815014034043c001781c5101507a10014000d2a00040006e00e07a16 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 704663902 1250 704662652 704662691
    0xd020c0f0604080d02060a0c0507031205130c0807050f04140414010213230901030201082d0f070807030c0905012d090801061406071e0501020d140f0601020a0303 71
    0x600c5504540301da040c480c0001b90764480680d0341450103407030310301c04900551094045601e0250543c4460300b20300341a010707a13001018000c0c88805620501e1010360000b8200460010080c203070200280312240c2044d007040b130080c403094080382c072030740c50900001c0c1c0025140b002c5984c01070300304c80e8495845400049440c0a84680c4440103c002480503011074649800a15051400c4200201021000026091000c0c0c1c40d001e000103400305604800007190182d0210650101c1e808440440b08e8034110101c8941c0d10038000c0d1412405c081a01041001d80ca50200c0125482a5103103028000c201c045440540080420b001e424100030580f030802d803a101045030444d0501051010200004d40c0b0031000030400703119405010012b500f0b103800018650a490394140d80c1c00001000c59142ca0301d542c0c0d071030030740c0020300c400051900c400540c0000814801c2c8080c02c008206242c000c24140a00342d540484448020200998211940244810750b40d00151a0a90035030509000034281c541c07001060804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 704665152 1250 704663902 704663909
    0x30706291c17070501060f06080c131403030706090b151512221b080723150d0f0609020703050a080a1104030305121b0f07021c12020607020d020c0f0604 67
    0x540c00c0400c0000c0e0b02c0d0020000c10210723204d5580d18140b648400039007004600c82c15404501c4c0149113541400385020702c207100780e901c032001021a0301d405200d0351000155140a00c4c280c80701d2559008112010482c0c80100106074001c89603032140c81d09070031503d01d040c0515801c012240304800c0001d010491400c401c0c00680000c4a4048807200305840c2501c1c0020484030000c0480d010b81c02c00080c800b03800a950800d49913000404240206403103010b03015541600c15540c0d01214051031407500c00f260b10000d0401c41d010f4040440d40281c3c1502090a8a10582c4120080351040010002090b4841d007656020b00513032404440648600c0c46000244c800601000036642c2c1c00500007040642110003004e0a0882107907000b4165034504c0c000c01002100c00c46002c07100300800003d00001002c0008050b45480101075480050034020422291001d1101c2207411000c15946082c500e501000041e501c800701344000e0511420a400003900e400143c020305004003803071125100d075503503405c0c00c1d01d019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 704666402 1250 704665152 704665163
    0x30a0b0a1d04110406031115130e09070b0408100b0d0b040212011413030306081c050304030203040e04151a0a14010e03010c0c170901050f0c030706291c1707 69
    0x41780d01d90819070702e902404c00003d8414850804100e540380704000aa41d40030810502c40d1014a00c2c0004c0c40344403610080c641003c50064000200b00000c0110182001c0c000c900014428014808040c5085502e0004d65610031901c405d420400030b45240c0c0142e504c558141c1c2c0c0035200350460101c0c240036005890302151b0410f0f11008011030460340b0b441c2d04c0c940e0340c040e503010302855540310400c0d5201c0780c2c10281030a644010f103401c60340c4a0700800045420621a104036450256511008119840e0991b800c07100141101842d4030003d03554010003100301800a402d540d0b409403030001820b180d81e1841044121480a020310140380c0c081d524a111040b0081d00a000c90f8100300070040c04d40c250894110b60f4400c4d1010003c00e4018075a041e01c0d03400c001038480318035003407410f0781541c16600504806041c510003041808005180d074080c0040c803460000f070f50400000f800b800040b402c1c1c6803054581c040c502100761000c90769400080d109955400054605048032140240116845141d401a04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 704667652 1250 704666402 704666411
    0xc1401110d03050615090a0b0f072a0602030903280b0c091002060702120d0905160608090109050a020d030201021b0706020705090f06040c051e030a0b0a1d041104 71
    0x1034181c040c3c11881c820342045946400c5004181080c01d4140944449141c0150800d4004d00c1484428402040d00308291b0001c10708000c1d103559804d900d41c0156056078510389a048810072964400c1c01c1d10f8000e01658005541044070560109544012105100390350b0641d94000c0e8150340c003070400d0902070355008904824a85801d11070303503c481d8001d101407030007021740b03420401100784040b6204c0c1c001c000385e5019040c00c1200f00011030864002110862406a4520f2464000303001005030541e1400c3d02c900c02150300c1e19102002e402c102004010b1480e50341061911000604082810003241c0e5045841300c100b40202d080c124028011007142c000350b641c20420303001c100d03000015002c045544650842e19020b031204284070044905030b650703994a92130400844c016243c0384c2c010348001d480c82e241c0b40781402c2141d488100300450b8442100324841d070000078800590b0880c0200840c186065a070702c1c0225142c40b030264240901c1c0e070400052508003801040c100105140e0340c2082c440001c0040c413 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 704668902 1250 704667652 704667673
    0xf100c030e061c15090e0304031709040509100f050c0906071b0807030507050105120103020919050c220e010308030709030f150c090807050f0415030b1b070c140111 72
    0x40051031214040100c0c2c02409a0008445c8490301501c1300b110500e40185041c5850b680e181d050f80351400305e40500d100d0381400058419125440782c144030380407201c000c0a03881c00324100349040780c049154645101f824101081a804125811900945029100c480e501c0045041c10ae40ca0080300e0310070409100c00441c00103a02c04000b0f4a2410359000c1d07416108456a50750046d2103620520411031000442c07000100007500e031003000180c1c480c1c070f2060028040d401040e0180200e0f0380c1110003034070413040420410040424150140100811000c00c000801e0804030803100c0c0300c4e01480020946c031030000000381c0540c4909080d000855000c46540100a00343c80e00d1021a03200007090f0804500d02200201003610646031002240e8002000d4003400c4c1c2408240a804140c0581d456001a121100d41000440c1da401c107200542c010701642c609400c00306441120039410590100b4241018400f01c0040b544440002045030b078220040b000d00c03002200140c0d442c0483c000d86a035903024410040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 704670152 1250 704668902 704668957
    0x1051008060c0c1f18060e0c0a0b190c15061716030206090d080f0703080c0307020304060c020a081c0806010f020a0f1b08010b0f100c030e06 62
    0x54401210644801d90385048415a19000380902c42803598420102d08141c0110300c2c140380b01500140d00003040c0400e4018808001c5410714404071600c17a9540000c00305014148104648404100c4241a101d46401e08124082c060402100c0d401050b1a80100b10b0901030080300005682c0003405c034801540c007201d070100a0001d40315000144080e40484411203001141d40c8841c0d840c003511501660703045809224070354003d205511b800c1080106208081164000641043e16159421a0f03858800e464010040305c030191501508a00a00a00240c1380d00070080e034042d201a843c00e0441c0409900004900320f0f080d40c040891030003062000d0b06801c42c0700f0b002491071581a120410507442e044011680500103030350f2480103810401c0074100003188440e1185066004144013016040701e550715a450070034036400703040141e641c1e20f540302d5a42042c03040200c0c08074040f05c2c058403104103002c020384040280d0100600f0003568009600c2c0030354076031041e2544221030000b40b0500b481c3d4910030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 704671402 1250 704670152 704670181
    0x40206030606070b15030114010302010c150b040f09020f180a050703110d091406010522020717040e01062331050a080601210c05060f1b1b0118080105 66
    0x11710300a500b0b02e101502e01c4410b00f0007080c100c0e503061b500d00844d0f140c3d6450fa80c411b02c0080e10301007240c0e61140d00d035013600d603558098241202400040002d0b16005481085540242c181060f03000c0d58116082780d04240c400e001140d404841c0f80300204055503610811801810076252084011b6404070702881d61801a80c0a0154284500500441c40d45042030481e6510001d2040302e510412000d11110300d07840030420300004060549001d401c2c88081d95400305643c00c03010540c0002c40001c0340030071104000c600765600402840c280f124100600404007005000700519011040100064803800c0111880030b95900f407010080500070740810070b02801600c1c000c0d109640c071956000310041030641020035654122030f0003110081080d01000090101024100740075034610040c3d440000d038a03101e1100a00461030425071140e581c20300b440c0510007455a032245003038075030300070002c5142c078150750742c01c052034040d007420030f5482d507100c045140c01c002006801005595080030240640244103600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 704672652 1250 704671402 704671441
    0x170c101d06010315020c0c03070e070207230418060501080309031014060d0203070f030b010e01090e0601061209050a0f050c1804030e0402071a0405070b040e040206030606070b 77
    0x240d190215003121045641c84600f0301015180b0100568001d0641d0500e40c020602d2400c050103581030001d104c00002c0c18500b0640c0302d214081201c900700840c545d414070000c0d0203084d044102080b80c00304021216180c02c004010310b0b01403503803600b04258580003139504110140d4404da041c84150307142e01c0b0841d03c80d0040804030340644181030019082c4040d6010303280e01e005680c00c0d441e801c2d41d02c070010041541c1649805907018040c0d88000700350401646e4904024501414005405500d41828480311220503407111080c01d2a141081ca00c103000483d0701c1d4110703022803400b481d01114040310407004060440b4010024400c0094410420801e4500044414015816111103892040c01c2c880440c51b1040807a0540500900041c000b07400345101400c0005c0280005080254541d18428045864003000c0000c64481c002c000400c40c2c10840b0402901540b01101e040c145171801c0200c1206001d00000d00c0317048040006081394840409491b11035070010095541400d0a003401704440e0302c10754 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 704673902 1250 704672652 704672681
    0x40228020f01060b160213140901020903070609050d120e03190b010501050405030601030605070c20030601150e09040f020315071106040c0302011809060b040f140d170c10 75
    0x15800540345261300142d0300e103a65000302803962440c10786d08004e0580120a880e244c031664907020352543e1003500000310b00c5051020700050340e418050040510702503c0c1d82c041010401d40b0ba00038006510b44206008610380d0000041c1b00500007484140c60b00c41c1551641030300b40c031030306e4082d0307a60b500440101d444a60043c424a41d060b600c6074011130303142c80b0740d0240341d825030b002400420001d00319503c142da0040d01ca04d48050116280e90318581c1030081041c050901d07012030b1890120b5494203015890050512900b81040894031520243c90288001d00b200d21540c0c114000406001149405d08410b65008050701c22215044821401e05401903c140b00000d0315807000d00301000000850309d0169070004405010b0034615401140c018140e010040001404090b0000b045100ca000d070f41c0151480700103480c2c940f82001c0e04e104007210954420080c80e00d540d40011508d40300c146142c402d85401c002041c031465210b40c1014114400c0d1071f0300c04420702c110395801d56103560b16409032050140f040f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 704675152 1250 704673902 704673911
    0x1231e0304030c120207051e030f01050f16020717030307020d0e0303070605040813091b1e053004060c03021c051b030406050a0b1c02040228020f01 65
    0x20a42945501085400401041152000c02c0201d205035211380388a9080c0c4c8125004107480d5008192800610140c110642c880c02c0d50541c00303032505006d00c0c40c0011040c0020032043c0741c001300300f100f0340e00090700d65650110300c0040301ca1014801c0c009000a8100c228000e40b544030001031a80e5207520403500380005015000c3d034540c049124109030985510010b004508151164488500800028008455030030003045421901c2540d4240100145000b110000b40001c10801040d40c50110007104001c00400d45054503084141d200d10840305200351924a442d4079030001070b03541c0000065000707803481c5641d28072241a03041f209940b512540c4541c01c140040382104400307034181d000b02006d02c41d8128243c2300203401d44401340e006030352140a01c02c01c0d107515404803541c2e4680e40d0090383c0a0301c0190322001080084000b034083c01c03040c880203840c110388191500381c494950703034000e240080c855900010100c0344140b5201c004a07600c8550f100c1c5104cc00341940000e542d40100c0e0903203000c15402e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 704676258 1106 704675152 704675197
    0x6040e4b06041709060f03130f05010b03210a030911040f050f0906010506030106030209061b2d0a0219030b04080705070e06010f0e0123 60
    0x4001e40580d04060401000c02058032802d02c40c40101080612842e80707914080324800e0003c0e240b403946030385905665095020510382c1c007500005d99280b10724184a010b501c06415484110304464880750700c01c26000002c0b81c06140010390300d000340110f0f20b0b000e0003500715400c068843c85501c814000000c002500301d510301208014619910000c0042c0e007606500c1c119000143c01000780392641c54440011503e10050240030101a00410042d110380c50f4207003556100f9040c0255201c0580f602488507564401c2c81c3d0f03d1641e0300035140706071450b500e0412155412203242034046e02e900d02031078090000c4080b140c081c407681c14210440c000041050200050302540c452202e403551100326003006031524000d03405c40000703d1900000d02c440d80c3e8000c05505001003484c00c00118160617040107031101a441c10388100c03c60350100d0200e01140c88c0000500741c07101c02d44002c0704086027 = true := by decide +kernel

theorem cover : BRFrame.Cov 704496402 704676258 := by
  have h0 := BRFrame.cov_init 704496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 704496402 ≤ n) (h2 : n < 704676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
