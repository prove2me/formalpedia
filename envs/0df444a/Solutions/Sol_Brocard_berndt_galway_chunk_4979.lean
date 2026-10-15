-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4979
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:20:46.605382+00:00
-- url     : https://prove2.me/submissions/de59e254-5b6e-44af-b8c3-9146a2f21ab0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 895323741 ≤ n < 895503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 895324991 1250 895323741 895323749
    0x903010219080609131110030b060403060501090501050d0f0b040c05090a090b0c18150403080403141902300601060201141303020721080d0605031516050c07 69
    0xa058000c200185600c070051a00c5910110b42d03581c140c0c1c81710312100c00311a03603442008102070a81c0c00034003040d24018840c480f48010074503004c603000c401180881c03480d402550040b204c06454600510800b100744c00350601500041c5c440b04070104168486982030360420b000540500340e010081428001351001140283c43c0280c1010424140004c4010060620074815520300e001403010a071a01c0c03003101200d40e940316094030455a030780402c1c1080700003100c1c6002100c4e0000c0403c8004000b44510010b000294041c0c140015100044201ca41c146034403d182103111022031048900144c2d01c1911501c0c1021014801c9004c0c03568999043c000300140c00c90642040c8035103000000c200d40d0541203450740b485955000a42d44e29600082070080d50fa804001340540c118100034048620031044260042e40381d003440d032000c1c8846895491382035228031030703001e41d003074030759909004a040c04c1009900d9003040c5210014546054038660074941040f00402c400c1000c006030f0300d891f810041046802030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 895326241 1250 895324991 895325017
    0x1704091e0504030503064b010207060504090e0a02030a060506010807020705061801020102090409110a170a08160b07030617031804050702010227091b0703080c040806092a0a030809030102 82
    0x112180304040c8402440301c0390841f080604040c0f801c41651010405000320340590711500e092905080b20700d0090824141401080d215090060740560f07800c1041e10903640c003075400007401d810084001007142c60018400015544108020130003500c2c6d00040f00c100300b00800d50501400346000040b0b01910500c524581e00c281090a03060612901c0100da11402c042240c403150069643e684007810010402409110b80c0c01502504c3c010920507001060310041070785094088101c540c0d918840c0003000d48502001a079910003c2c0b20150072105050b80007440c0c08021030074400880000c0c04088800000750303016517250004035400c18001d4041c0d030a403043c0581601c41442950341140b40c020000c02142d8800c045000c0400c5240910664a24290038801c0f403941c0340060945060f69030000207081414401420440010700c410306000c3d0500400d02c80001d0007a410070503a16440c0480c01d140d070418244041003200c00d080c0e944608035807c0f283c0c800b8880d0b0301e5811200c0000d0090086116044c12 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 895327491 1250 895326241 895326319
    0x90f0c071112032803090c140d0206071103100506100c17040e150604030c090b0a0b04060203071401151802040b040e04050f010506010c02010c1704091e050403050306 73
    0x1c0b1040f135241403907024071150000404c400031000890680c1c1c140a80a030803090404018405a4200303070a1145071007003d02028000600c030750210720940d2201c48181c0f040300548181202a203014002d106800c00b04010900450a200c0005402443d02024200500c0210703094101082041000c51482d07061602e6415103ca903541c0a003805080d0845215590040508600b200b5107812401c0d00c05a1390029019804182060905030041c9800004580e0101103400700007020054040200040c0c0000c0c0d01441d150b40040c0b81c03c0340e40e14520481194a641404150201000307151140c101702c0e0255600b02c4031110f00f0030345501c024451a084805420000240881e05040e26000349021714440d40403104920801c01030b043c00c0718070a40e407450000b20600c4c5010003542c4a0505440c1981c01100000c1c2c0100346000000c0e441e901c5940034081c40e60301c07075078031101c2641ca1042001c400c2203440003d020700c0c078080c0e0b8001d05602c4020002c0e032140790000c208100b145400b2011032030b900002004090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 895328741 1250 895327491 895327507
    0x1120c09090b03030408150c070204091103010f05010533191209050c0405190c2007120f1e0f02040606021506010f12050c09090f0c07111203 62
    0x10200e140d0380a4403200500300071280c009400c00008076800c95520602404c51201c51004a00c01548081c000340455441400700d500565958410040ca0610034100660005490b105050030b65014020340c40400d8a04401009141c450b4800804c14100b000d01c1c0990080316860a26590008a20203c848000105003c0a0300313041d600d2803100b510258807845482c0c800300c2400019161400d030005c01035006403c0e0300702c0d242041e400450300a040c401e044500401c1c041d0408085401444484001030308588142c18114904102c5019203008a009401104c1c18401c880c1c444d01161b0200034904089030307811800b800905042c031a505806145411242c10342401d2200c8500040c45090307125514010340061118000a80c40248054002a0b200f65a9420005545006480280400741710041001c124440d642c1d1081c3d500c20210700900f207440781040c8090181010004080010009040003031020306108001074030841c650000c40c540140d465980890070201010040c00e80b03510011500301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 895329991 1250 895328741 895328747
    0x702070906030b060f060a09120c35030f070f08040506030411180f13021207061d040b090408161e141b0108180610030303053301120c 59
    0x30307001311000c80e8085581c48800081244078032460078107501081c00e407802008200400c86101541d54002c90b05038501980c2c442d51402c80d407c2a900c80d40c200c8280b039040c3d40c01408084446000c000c0705400850038445660f0070141c0a21880001502c3d410186110000304600002190003a02e000b912080d10380c10240351200e01a509810503c5c4156a59009045c01648000000e40b02d5810481c0500898856450881d0308200c0e40700f0a0740c010305545a44d0543e008208090340003441281c0e120428030b000c40c00030f41c1e200d0801c088030b64411420f1900360302040e070b1010f1210350020b80004015503a0411428403a0000d5544040200701c868984640c2c01201205141c0c0111280581107407003e070040300700302c1c03500e5075440043d50202502050f0503941a5101c1c12980b58031100c3c500c1c80422502491380000d1408608980c451440c0d84030355800d10826038580509d5801c40d0750542d4802140d0f01c51038002e030f040f0861049082c14034811a0a00201c0d0b03100349500904030b101000700304441420780b6002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 895331241 1250 895329991 895330013
    0x7050a05031908150603150301180c15050f13030506040c1d0402100c14120a0f17130615030b0117060402030c0d1b0e011401030b0f040203070207090603 67
    0x41419076540007042a883c0a0903460703100300400503190083c452402c0c02c01402e5040a4000614880d029948840c151030034403d0292445085078411804081c61500103a0000c154104c007003021031042c10300380c102c1e030414151080700709200d80d81d580350038030521400b01e8421103606c081d02c28402d420502092000c001440002d80308070448010980b10750300d090240700c141c140d5000750020540407c8044d403e10608040c000f251040040707414011101115a150900180d52800c00000c000344c060407054000b181c2450380000b9040c003845915850008000d420700050940c8070044d8844202404c102c4c0c203a20104402c20fa03090342000c2592207041c6660391400900900d0701180307035038044c105158400607195206950040003405000310724014031109484181c011610044540d00142c284064078180f04060f04003c910310100d0741c90504c4c1010403074040c0f0525810b15241800081d0561612580070b11590b6098801580da51901d4070200c3c03800105502c01d106562034010040200001c072104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 895332491 1250 895331241 895331257
    0xc05101115180109050c061b0609060106080f070c110607050105070f0201290607021f0305100e07020a0f050f1915060513090203011107080309010c0509030a14010207050a0503 77
    0x80d040440003800070b40d422644441c0c1c0c060055444400034518505c1c2c0280249412007802070700c541c510784295940e07071070070909481c0100e603600710030018440d45034809205540103208103000301142c20700f10805083ca4100e03a0010b0480e9010052100840c0c0f9080121101c0c0b641c0400200500c2c81c001c0d200408074100945460b0055080c800b1042070300380740c8a0080ca442041242d401103012403002001941e03804120101d0700f01a035000b03850000004041880d4070501c5c81e8074086814640101e5104580400741c00051590b0420024882c245500190103000c03560300032802d000700e07000b609041c0d160440161844859108a181544040209030b100780c403da403090065480000e18880b02d101501c4d1140511500413203540361180e54800107400c004040340c009000040e41e008032011034000c5506c00700081d00d11000000c180801c0768000d2044442c0c5140c9454101e0510035100d0010391203046110000d450305a0140b0074800e020b4084d030485401d198030008a502041d0280b030002e4903a040800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 895333741 1250 895332491 895332511
    0x20306070906020c0108130605190b06070c050409030c06060f030b0f15150403120e1003062303120307020109050d030c2a140606100302070c05101115 66
    0x1080c0d94502a80a080540e501c0c3d030068080008a00c0044840176001050810450039105c15a0080382d102d100c3c1074010065003107242045001000703601d0540303010081c4030740030f40c07402c205801c04100340c1000b04e400c1d140300301c4002c507441050782011203180d074035024094405440d0440018800d0702152500b01182d01c0b9541e2000956600b5080c10800708040b605801c2401e884c0140702c1c038074a00804005860706071806201c1c00c050702d030f032120302010f1841d0050101140c04159144003030f2030a1003886010820520b024021035007050700352502d241c1102c01041e14149503440c5035880340c1d824004009410f100108180e00e032314190b50020f001e4100c0c0881600c59008020414140d948680501d11065a803503d81031440c0e1000346524000141d1001031710f0441200380043c1c0d00007030f4416050110303115010010100c0d41031a03400c00c4042400205d0324018103204100075000107005841c1d0104070340c02114140c1e21404803001c20f0b00c1c1410301d52088040b5010382c2000c5442c130319808903928001d80f2400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 895334991 1250 895333741 895333753
    0x2010c03020408060f0709030b070f0908011b0e06090909281703070e040203041103100b1c0c0506030405060a060b0a02340902030a0c1e08090102090a060c0203 70
    0x20000390102d104500410099030020400504844500c0301203d0f04050306203084402d84d0b55070380340c003c5401415035100c8001100030948088041d4081e050802038640700c4001c001d18001d0300509011001d40a4845043c007508503c00e08680d42c943c401d45411a00c0981425000d261103003440d038642031010184805a00f500c0e096010081c0d01c00c04040d447c84e880398184480c820f0304080f125207504014000320800c90f941d0440c0246403506d0000c0c600a038840d10700307031400d5140d40007014100703444c240070b03110801c4c9041c0c0c04028541c1e803c85002d407032890020045c030325044103040604500126800441d00030700004280020000700080c1e17544209000707902009000c1d01c40305c244250f40f184541010060381302c0740e010b04800110701403d21071b002e6500d260b24940140700a003059484c03415407080030480c1e404801c00000030a10700895a00810b146050440d20461208103125481d442c8240d10801040d480050b06000003507040700c5032031038010201484159918001040d2580c1884101c0c0240244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 895336241 1250 895334991 895335011
    0x190302040e06060306040b042105070b070e01050a030b0a150507060e0c1302090f1908011103070903080a02211c0509031b100c0921021e0d0c09020a0201 67
    0x2042e800c0c0540c40007000703021651600e8482a82c1e52401030020740300c2c1c203410001d41c940155003400828101c07403292a1142c651865003001160610014040010b2012505039501c1f2681e00001710b402907402818005441461480881d2194056802508415140c9041a00002e400ca4098064030b4801c0c0c209010a110440300591a5011080c5c0b01d80c22620340f40e142100614182c000d000c00030000b814192003800610005130701e07a031000c041005208000710381840b101800b8000c02904882d562030403807850401c2c88000349460b080384030203000b9100110300b820241d4403d20502d0000081e1490200d80c40c540002425010351040000e02c01c0d14410060441e8044c0160168074440c03160b0b40060750904410860190700c0c07007482d0798000740305c2c050310166158014042c49202d9500c104c40d84c8036490b20f42081d000c6a050500b0388410b0a6074800410400010713519007035030310305044d05654245100c4e001d85010600e0b03107035411001444404102004180181c1c15405881c600106078000d00503d070803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 895337491 1250 895336241 895336243
    0x501110919031a04260a0908070302090406050702030f0d06050f03150c090102070b030f0901141603200a020d14161707050a0f0c0b03280b190302040e 66
    0x1c0e510009094540740401d0a00caa03104000b02d5900c14000c10100d60000c48081d07409031244000401e803408044041905c0907026481801c09000d0001d0200519100c4d04607000900401c00007400280031517220000121401c0c401d2041c1c655440d071b06400c2c42d85407100c0303646420203403005001d005e003d1540305c900c0703242d249400140001801034440d0780311015103c5044401c45944900d2000d03040d44500040001d01120203c01117120b10300b0a040350205050100801c3c1c01d46241024415494000c1414410203120664680324816141e007070024500b542000070003028074000200c580f004101040c0c24440030b0b004604003449008903076a5044500c1d0342c010303840c1325010b480410003a25001520080002e1451116120108204d282243c10f102d510f42e034030303803402040f00d500311170600c01003c0c0300040145400e4400c001d45a1040a24203615080300e06102c40d5084201c0a4400909900031003504101540070041e07001c0081c088501040c0004d010903a022040e100403402a8508191030380c010300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 895338741 1250 895337491 895337539
    0x120c150b010c032307150515181b2209110702130f060f090506060708090108060a030203071d0c09060a0c0314030a1a040b09012105011109 61
    0x10584071840c804042c0e03181250840109960354076a400041c140344040c00c0070780e000c1e141280c402d0a072005030304100614101503039409084903825500c05400807805589409800d5003504140005d1a80f40d910040701080c40c111140b804000740c980000c0b050b84000c6030903c240030040c00d401c003a801039592102036504448046181c1c00c0358040500c0124018a0200156660707602c0c65a40420304000350070700d04c41110780b598810308401c0040c030010407030f503410b41c0580c40e40411700b241d460341489016240c20303030701d48641044030381006400c00c0042c40b1366031045000005035030050b003160000f54448400700380f00c0385000c50440603051403030f0006d501107000000315008030a000c0c1041d420700516074425074040166003411800e020b1401d01d0314480c80091409503100d01c100d41070100307200712418001c2c0c2040030550f18250042d03080c4512074002d44c941b0b01105044440143c02c2440150b244108001080141e4000038007650030710304180300e00b450281c040c1110806c21940325010036000510202164 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 895339991 1250 895338741 895338761
    0x207030314060108103302070f140105070602030604140a051b04030f0615090c020a1707020a0b0915040312022e050406270309080313031707120c15 65
    0x1101c1c01c0b041c0001c1b8602c81c80001040ba6000d8464520404d682079401d00070070b4012044010703030058008100300c0d0a0121044000c020718024005804602000282036114070320005e0003841d00000420090b4441d580410400d1680c1c1c1c0048007181410a4801d000d000c0945210701122120410b140103c0040c0c0116022a0303030141030398450820954618000e00f42d80da4582444030035103800012440340c40c0c0100d00781d1003195405006a20303124135120140c0600c80c0043c587d484070510040c00143c9072140c00c04151200600c40d15140d03003103880081c003080c2c840340301c58000c41e00200c1d00004010700d0340c80020b0910b07503c1d0203840200280440b0a0300c4001c1910008101843c000c2c82c005000409602603504a8050714000c2410180c003061031089000096426051248400890307090640c0b010158010301108400b40d403908031810305405e00e09406000242c201c4200f15800702094410004a038105980711074441032845e01160b015010000f0300c4426100d106404410541c25610343c0b16800e082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 895341241 1250 895339991 895340011
    0xc0f2f1002061303030917040312140a21021b07080a050307030e0136081204050114040801050f090f010501350f010e0c060906030609090102040302040207030314060108 74
    0x1d55520700c028001c1005200140c00389070380d03840f0080201c2c408000d40e00710680351040d00d2343e9692861070305051442d07c40012104110140c0529050440c0c8602110300c0c112651804070100080a24001004c1c0c501d0180c000e81345100041d1000b100011b076900c4104400c1c0101074400d0241d80312610790b00d030119028000c2280c2c004103c0d50000078040d1b40e04061454040c5071501c0c0c2c60702c0c00c0c0c500005a03200c140400c035000988554001c058510304003400d0203404500041c10040c030300c01040f51080c0c007840c00380c1410312100329222100300242205a0700100440070003400207007004071000d0000740060700c1d00c4945001d240f0616010310070500940e8126072100210400001d01c0034840c41000c81d090350484a0402804162134101200304036615500c1d03c07607400061030f60005400645880718041c01c2034050b101c01d01c041e48107036840d502aa54030074415541607007640e075a03590072402403050f500025401803011500106040d4158840c004000b14843e0554140c2c032100700554100b01d00702e50034548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 895342491 1250 895341241 895341253
    0x3210e1014011203090504050c0c0d0f090b09060717030f0a06240216062a110105030907090606020102181807050906040305011b03050c040e070c0f2f1002 68
    0x40083d8038400c40c3d60840c02850100301968451001400355001039a0030341c41d0301000315000049a80030b01403481c010100d820411066100250701501544041c41482594200400e802e03000381c40e2042295a0b05070b110000301411901c80d90201015041551070300120400e26000400d071040501c07030802503601010b4548120f0b040151100d089032090343c4104118018410500c1440364541c2c0a03070b01a08180d110099140c0440320041d2440801d5845440100051889440404e40700c0c070fa00c0920510130300e8240c0d03481da558400b15242504962140200c64075104c40000d4050381035026042c892200c80340701c080c01c48440c08102c2c000038909248010900500041014940100003c004c10100a808582000c0d40c9480f0182181c05508070b031245034094880c204030b03655061180700d5000072000c40d110304050500000b0203d60400504c2e40060100301080c0c041404103880000f440140d01c58403020540a196150300d00842e0f0542d00000740882c00e0340e13004018504031006020030749151303004142c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 895343741 1250 895342491 895342499
    0x1332160f1d06010318050f060606090108160512090708010501052e1b0308010810060324060b0406030b0a05010219060b060909070503040b130b04060903210e101401 72
    0x21000703801605942c181507403000e08000c444014031400c011980168060b00450036000186420310310014640c500c034402c2082024801d03a04120b0b6a501b0210a00356000501c010389001d071010312071200d41c280301c0501c4000700300c100d01c00090420162001c00c4024480c41e41d07205c040c010f601304041002a030503408034150f41d0007404040182a41c20581e0b1518580340049111a44202106100f041c0c00040b2804010b000e007600070021105070740855102000304a285840e00800d0f01403840e03010f50541c02d184a0f40126909941142000c0c240f104a0b4603621a07507281d01800901480d030100f030240c0502d81000030150300208941d0100d981c01b40360301c0c40404181e950308006000d2461461b62003401844242c0ca141c45041816100c1c00e0962601980da08144c14040d681e035100410010007880816a02000180420141303031b00a070307000718013041d460f00364501542c014003588000240b54040c030340da803900c1003078640000001e800f800051b20703401c60342480d29406440700c41c5c414492302ca25500c0104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 895344991 1250 895343741 895343789
    0xb03010b0c07090f09060b1e060729071b0b0105010f020109170304021c150b180f01090c181511100203100e1332160f 52
    0x20620316910540c0c40b140d03140c40d00d4908a5021031031141c009507690006100b04442486800d400c42c03001c541c22039a180c00c241030400203080120340039000b800c0c041400002c0200c1c041800303c010745040f01c24003c80844508181c0741807012624034000070704131600303250000002c5802c1203003180c00c00204103003603003810300558540d5404861581103643c0c42d0040300114410130804031002c000c80303025940d603003070a0041000556040c4c116403c160030901a8000140805184c007000841d851008100c2401500c00600307006002103110b19442112000c00007402051038840d41602c501800c1080b00b034210344401c590403103280540b0480700407411000d11040242031920080188286020200201184d40b51030a050204400018030341d00401404807541880e9540009400070b0a400030710340c07404ea1102501a000e240d00507003e546000090036418030f514200215070040d1001c06200c88202040565443c2800044828000070600010a005e142c40100c20200e92001030910b08081c4500184 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 895346241 1250 895344991 895344997
    0x17040c03120c0204110327030a030903092c09010b010c080906041a0712050703020a030806030111040b0c0607030605010203040312021c0509190f1e030803040510060e010b03010b 78
    0x8800d00070075015000c0140d80b94051801020850b42c5030a03103d08200342c0b5004055003031100705e206007107d00304401500c2c10020035a0342c8941503140101c3c0a041504003501c00c1e040075000b6034458030038a02d0020103200900150300b07081d40c94000e40d0381c05a44180307029080303604161405001400441e006004903101c80b01812082030000d015503d0582e0756070b0306140214401c0c0041d170401202040c10000d100c84148010b00718406410103900c1c1080503540251a407540040043c00e00c021403000c00e8154900f540449860b00700c181c560359655440f071000203101d802a410003505881040009400c0600c00d0040000700d54043e0002c500342410750303071400006030360014480d00b144161025030400f0424102180740a0b81d0a4455541e00c40c8020140107441003181c00003144c1d18142e50040003002c0301446000110340000c2e4440c10500e00b090521520926194009003d4880120511050080200300d41100d0310b8028401c00c00e240c0e0b1100d120130003c209204007941034800380300400103200b0900017 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 895347491 1250 895346241 895346273
    0x30912011803020a0c0f03080f0d0605031b040506060909040308041b0608010603140705040b1803030d0203270a1217070323060d1212021917040c03 65
    0x41048890305410740a0420101d0050300141e01c08070384401803081016204001e403541442c820500e600b99169596544104103101000d4107001403015105801d6900a4019040c018261212400000c07440c10514040701e1009108a00d49400310b0031600e8820300310b805544c0e004d090007080356540d07102034454200040007500c081e03000440813030510700229203840250800d6180d0680550401a00504a941901e1400701684100042c000304a82180641d011100280c1c50b141c1da48000000c12000403981130030054061202103040e0781d50700110b0b0040c5210711503a85000700381d030001c0f0151039000c3d486451a40c4442d0882648107001c99800340350038a5110312401c10406c0e1901d00c518900a410040703514100003907a42c01c0c400a80254038403aa040c0c5030400d1401c800300e08141c00022800b00c4029401010200303d683d1101101d0f00074081c0350324503021001c0c00c42d00c61000480c0a9140741ca900d1180703000585151030801e80b00c0c2c00410290159822548084d0324508542c1d81000e04543c00c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 895348741 1250 895347491 895347493
    0x30a1b0837080d020d230f010302240c011b0f0504090216080c010f0e070b0d0e120c0f0114010608040f0501020c030c0106090b100f050a0e040c050307020c040e030912 73
    0x2000d540b5040d0240018451002801400113803055807000310042d40205101c017100031111b000030f21032544aa80d6005054030340446401e4100c0706107000325101050142c0442a04990120b545409510190b211b0121203505031007280040080c45001c58040b44c00c0c00c0d01b800403401c1400248185000d55029003104003003880300e080d8070051030f10b943c240c1d5000381180c000d050303456115103961100d20b070280744052007101c0c0003009010300300b4008148038042d0108420b003c6c0c0c1d81d64a002210f0b0804c000c1031405a0384001d41030b80d211003900c0516121740c0c90221802c002d6003081c4005e0034003141c100c0014100c0303c0c648e80ea201940c80300d07a1000490740302d20f502a00c0940d000d000225100748284020050103000400000d4054030305a0010251511030392a18401c102240702c0310709103504083d000c06240506c2ca040c0390f030341030000740c20750b40da804049035260070615001044a16035001402140540d60075000c403014031107100d080005444007c0c022204607001400700c4090350801e030808641c0541c01340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 895349991 1250 895348741 895348747
    0xf030210020307051c05130b07022e0c020d021008092406190e0c041d07020c01082a12060f2b140c210d0c02030a1b083708 54
    0x51f0990b1030b42080d0f504400d800280014030001145440c00000e41d07040c1d46c441c00c0201d09410802076500c100345254041041c07090141e0500119501d000e0b1a40c58154000c0c201400c1e22250313800240a50000c503041b000c01d2048510540064038001c40c0e0074014401d20500d49110384d00c030382c2444a14106c8602d42d9100110030348001c940c00412400941c8a0311102981c00e440d01d00c0c1203c1c800c020036212581c4424100b1400600c00f60903800700341e20320081c0c82070920301c20607100c40c0741d001d0100c502042c0b50001c070901044600c052021804c020400c00c1403c81d41403581d0340360101006218a0040d41195200c00410581c0c01c0c0c1c1c1c0ca03080c031148d400500a02e04c0240603a03c9803a8001000f007010759255041d0014002d2441030b00d0b00039080d9200e1110882e81c9203030740c400710504503a1040034040d104103000300b000d00790045540c100514500194049400313030900d100e0307501609104400c2d005500030350289004a40007080c0004134645000e00f1420b050340d00104602410220f5000601e094039607040c20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 895351241 1250 895349991 895350007
    0x2180f01050c011b1818090f17030a0e06060a0608070207050402030405010e0105010e0106091a1b1e0c0303030420030d12050f061e03030904060f030210020307051c05 73
    0x138894150b0400e01c19018400c1030320f59510007010152440141c42d044440f8601c1132040c2d503800b06001400c84020840044c8440840c1407a091220007000f00410300d03e03e01c101c8480c1030404c1c9000d50b01a03084030200b4010060b014118a40743c5c40c0449041e41c0103040e415007000b041d4814607516070030220b6401582d04103500d070b5011405030f80c000c45003611969154a184403007680240304507030050070b61201c2079910317504084004000001c20f203d13104c4200130240d03117a81406100e10441d461a020303507400d03148014400f44811740303880c071910164201c01031603080d5100d01d840100300c81e0712040004002d5461030b03840303944400e481039071190407c17400012007507a9480c07510b0411007140c0c0201c0c152a0100c42c00450001d00090311001001c102103406220300344140790304c0700e80d88040d400807000c55442100c800c41010910398059415030940c001e007841000988082c0c072000d0310080c0e900a0710214805036803510142d81c2c0344280030b0000e0903607008060068007040201640c3d030144865203052403400d854 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 895352491 1250 895351241 895351243
    0xc03060904080c0a0c030c0603051627031a0a02040506070308250206041103030f0711010c06020409091412091002070521100603200109080303010b190302180f01050c 73
    0x7001400c4545d04601d00080c01401030206284008144500d014040c0307240021210031400400071644041c00b51052100329200c140c004a0308556020404081040e42c0d00e0614192000480342c1303065420740031030301050b00c400190084030309603540a8103082c45c04a15940031118050000c00f464500403010880c01c42c2202d43c5401602e20015580c0180118113007805c142e0340d183c001c03110041c0b01c0c0d84104100e00d0741c1e1100c141903503c29500040075401141c08100107a032480c0f4900f9009100038400035001c90031000d41d40c404240640105a403588400011490a40c0d90280d01d88010f0780f100180000c1d5081c0c5006d07044441b402c281481034442c1c4070341c1c52022442d903d00f00c23408a000c0392203102da2400d08010030000c210341c0d5a5401400c6c4001c6140d038983c00000d51141c5110481d0130391845001740c080c2d0182903154020b00d0100c04807540d940c0d5501e00701c9102e4000c40c800088011001c50740e600c0301403180c02030710405020443c0e08401c0030650001c00114080304018507044c40300500031070b050018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 895353741 1250 895352491 895352503
    0x70c0b0a03021b06010608040b19090804080f030f030424090501020706110304170f0c1c020c060c060c070f020907210c1403070c080307030b010909050c03060904080c 73
    0x805072000b68a9980031a6a103191107540ea4038880c480d44407200400c49194401c4000b600150003900e400c410b0341300d40e08030008200321170b031304001900e0401c1060810030000c20024030490381850240ca1142400c20310460f101d1007820320104100b6401e1001c076000ca19041c024400d001500c141c5a11140d0004e000201910400107050704c1c1030b540824010280300f207034010074005062805207030707107545001c0e0713500c2c004440212176060010002080540105200134101c40b104447c2c2022605543c0b21401e03801d1204520070341110040c01034140007129428007105480d19009600b020708841c0d51950004000b5400604041e11045c16141002c00541c440d03100d00ca00072003032543c0e0200c0d0425044901c5d11036558004545400b141350513580d044255000c0c0ca11007404400b04007042d90307600d03803440844810001000203000c02d00b0000602a0032609544001000b010a88030001840d035207900031011180c0c2100c06115034482080010501e182a98000b60720610039282e05061105040707640e407800f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 895354991 1250 895353741 895353757
    0x1202121506040315050f01050f010f0e0f1203040314010e0a11180a090201032403030e0a1a0a0311040f030305091908070503061311091e0f0a14041106070c0b 69
    0x185e40c2e506002c030226545400a024120039a820501e05140c103000038615007286002c90200728885650300c405594080007000c110310020701c88407a03600c009522946aa1082c4012940c00e04048000201c544c2c0c180904d03110900351501920f040c0100c1e4558610b0201045c05943d0f109607000e240d1011404201100303030007212110380001d1801441e1001504a5422140507920000c0380f00c024000d0704544100d010a499143c50003d445c100000013081c19500c8903001420521003074400b01201000340c6002d452071644564050008403450100e00d2042d101d14080c00d4206d007005e107002d0010901480042298200103044d0003a21000810301716000401c581000029070403903c401c1003249410002190421080107403144540d0302030303a0340988034103008842809002d8000025003503107664814401c80b100045110074152030b120070100e80ca11012038584549510741045203c804008010051040d030380000c00841d82d0401c4420001240c0000a080302c42d1a0780340804940d115000b0003070b003090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 895356241 1250 895354991 895355033
    0x12009120304080613120c0c090c02030f071406011403100506060c010c12060b04120b06130516090905040302121b01060b0301030204320406060302030a0b060112021215060403 77
    0x48019454003680e504070a00946e02000011344008021402402070b150807a80060760002c3c206082c01c0d030503800c500aa010b842c1c070303450703010400d1130502040c0042006001ca5038429210540e89508001c8040094420a503030513501c034880105907014150300c4590003e00c010048c03800c00c1000c0d5902030960307211201c3c000000305044108002008240a040007401080b80300c107040c1420310182c0c105a07815980080e2204c0300e03100100c0c4141d00c5020b18a000040c0100041c040c1d0711f40409400300c5800c000d170b4144000380f820240000c0c85100d510500380130f00d80c154080c01e145e401c2c2030354802807a04004e40f90a40c05800352001e8020321400d208440c01030400c03103502c540780d61460041100b10f170840c480383c0341c204411040a02032246201d0341d14142c0c950003030001d241e03230300c540c1003031402444150030003900b500c01c4d84104000d000b0503a2550b03109035030980e122105800740d4201030741607000d44a00398024030400c070007003007039030105043d0b208421001818150801d170741d0340c48062010f50321803800601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 895357491 1250 895356241 895356271
    0xd050a03031b02030c0a0f03031103040b010501091706040f05030c0a0606230d030305040c0b0f0c0f07060e09060613062114010501081003020907050c0120091203040806 74
    0x40d2101c074480b00c90042a49001075410203204110319925100345182c003c0c42001e21691440805009500000104030030003046502d030314081c03400c0c0440b0a0203024176070100d000050006400307080548640d007000c09502c060102515542d581d8081003c100d02d046415000c01e20500780811010400030001f0f84c09014003003941407404140007080d107078070381a58800d038084803481d65007500c405041c107004541c14076000030155110300301105d5442d01a0441621000000765082c110141440070f42404e012484c140d4100948260100760707214075511418011a020400707120140c03415492060b8070200291880c3e1030805c08005402c001030301c075001880894020100421000303601000c0303807542540d00100f00304400202081000800b414071540d4100b00b10b540000b803287c80c10700480c0005540c041e01d540460b00f01400054000c0d00800740002166103001d1400302d40e1a168060303004088000c80109281100310001e2110703804506000070103a1100300400a003119040001921509000440f240e03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 895358741 1250 895357491 895357511
    0x5250615060905090403021e03040f090b1305090d050a0e060a09030318030b06040c11010f02090103110708040b030606120c0a03230a0f09022d0108040f030309020d050a0303 76
    0x410ba034200e412081c021124201013100003a000580040d41e0b2104200420b410617454489614520031500920340754001003034000b03126040c0703400c0410300d50011121449428510707142c00c0700b143d208031090026a48041c0c44840050300881c01806030341901d260402c0b202240d2404a503503940301c60003070000501351040c10014503038010b07400303450807001c004400383c1c4a1842d2124900e14a01a04040c42640d031251100b4005006001176003070851140f0003406440c0021109000075001181c00f0f5012900f0f05000509c148019070403034000c158407000c1c0c241400c0c00c04940c3c0311103400041270182c021f0020010340704002030000300c0d28450996020456961b0707210420041c242c0750b00300d040441034044210b4a400b104012141d059100095010014900c0020b50501e4090005844080c1d0016034495044031100051075440c83c0448d400303960400d034500201c0c01102c100c4001c03680949415144208000081d1013600f01c50340041c00200301a440078244e0712024103094501004601107a5102d000380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895359991 1250 895358741 895358747
    0x20c0f0a050d080415050a0503060925030506190609030b18030f071205090d030e010504150e040c0813081309020a0e0f03010b0d081b0303180705030c010525061506 72
    0x1684104192410501f4003c0aa07000b40c81c602018210900c100c4803d4001506059949030f10351400300070001904189002c120040d0007840e0540d0003034050348007030b8460b132034103500c0080503000c844a070354400c4a070b180381d621140f000920152118807403260300801c4c4406540108040c001e02508103403003d070b5030001460400f00d16086844648240030003480010701540d80d40c0e00d44a9030039010f0074804030505030400102c03481e100b03d41004040e0a401c110041020b030b031083c1c900f5807080d4152401c0202c041d400100f0f40c0d003400e0440766018400c0f00740070721400190800300500064080c1c1c05100c40d03210741360050003041e030b0041c1c1d19080000780500800c01c26490000c003003007000360064000304001c0021401040c880745c007901c0c000c0c001d034a00145550703481821120146860a00c5001d40c0e80724101008050f801009a0004010343c1c4075220000c601843d010400140c9184143c4a02c0c1c900099011480301e40c03242e074000410750740d01c00c080701c401040c0d081c0030f9046c01951030000c110304c507401c1c00005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895361241 1250 895359991 895360019
    0xd240e1006030921020114010609030203060603011a0111030d06090c1707020c1002031909030302370f1506090e0129030f0d02071403060601020c0f0a050d0804 70
    0x5071042606240c8004089600301002580c01d0118502c044862090a0800e0740540a0044910034240c2c440300002449135101100c04280c1e072085055840544170031040500ba2440d105a841801c1c3d0a40321a00d11503000d074290340080d2440d4800d507401c0c04c4e2408150821103031709071b0050810310f86900906980683c049041c1038a00341c88101c0d0503042c148071500960341c9045403401e90050130449004003100d4000c0043d10412000310140c02c4041512002c020455500d52100310301500c5914034000c3d4526006d08400c1e0302c0420030700c40b02c0c41c00300d03507140191070501c01090a840c0406100c5002010412040c0c038200c1b000786440c0c0100d6002e1504030618120381e0340403443d4205902d402100d242040083c0702031192241e101003520b1501c2c0700500000d04100b400300d40720000e4440c00c5440390440da000f04803101110f0181015030880010001456101c680440310140143c04c6407000140500d811049801d01c114098a859040c3d034998020809000503014190303450700300072504006801041b481c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895362491 1250 895361241 895361249
    0x5010308090a0602160b03070912050f150403080403050706060e0a0506100512010b09040b0a120b0f1e09030d0905030711030a1a13060f0209030105100501050d240e10 73
    0x38170341500031640b0020007a0150168401d5003a00001042c1168401c490070780183c50382d00401c00068440349041942c40c803903000100340f03e0048800c114241540c115615110b19050b4403250b41c42c0e55150b50072500c40d404902c040b10747d65551000030502d000c0305440c0c0c2c3e100e40790402000400d424600108030700030007101e0124080120800000c2c0110040500c1641140c507030070760054460b081c0c2000103003d08500845540c03c01000d0000095104c60803803d00c12040c014940c0302195120f00d081d030001030741c08403244043d007800c440c01c2045110382c0d0100e5a80c814500380c2074070b04000508840c4001d8458241d004e59981d400850440b0600c034101074101c41c104012801048421240d030b440301100103404d8809242d030302c60300340015465265410811480d42c0c1c041800c01c15088440407000082d00071601c0035000b5860030700081c01205402d40d0082c141c0304161241402c0c540022001d06c040d0102107001d00c8412254030314480d101c0784101e12400603050080d44000d951030405041e4040742c5140d80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895363741 1250 895362491 895362493
    0xa0c060f12060815090705041e270b060109031e024207020307240c02030c0f1504060f0f02010504081b0c0901030503030a0605090906012705010308090a0602 69
    0x808200e003640000b5022220b01d00303059044d02c55501d002685040840c3c907400f01e03800c5810100300100c05200300035226105414140b003002040c038100385401c0740b0304498000001540440404902090f6000180317640300105141840810b500c954480c2c064041e45403180c480c0d00b120119540440c81d0008002d0704d10000d4500d640c507014110b043c1c1801c0030768280b18900590540c007050340030030318110b8100c1e14841d40140480340c2a6558840c0010200880c152901c03400240c3e0b10340c1500e480c07103210040101c1d0340013802010b1090400d41001900d00440c5c615990021010f0a80504004510060002005583c8540c11910054140907190010030b04502c0300316450141000000b0318030b0002d80d030507468038101100303a02c01c031640e4051070302503080b03800c981c080c241c440004100f0000000444c0702d82c071602001d06c0002d540e602484070096050b070320038844c4e800c10b1005010003868600b40c1804088481007015000002e89003100449000ba0016074412400082080450500d0b220f0380c4000c1c540c0344 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895364991 1250 895363741 895363751
    0x120b041e12020f061b0703020a120206010302011e021e07230406080a0f1709060313060b06090d15020910020106050102160308030a050622050411010504030510020c0a0c060f12 77
    0x1002030038011240c48405c2e5010701020030110285882000a03e0085138060510307040b0401c1d0706000307507640c0024441240040c91180b1561810398880b20910714070f40c0036070020715041212484100300000c086480c1c0d1000e100300d1000103070300700508440c10100e002d041c2c0d4a15950580200388000c1e60126000104c550f40180c0c1540c0003c1c0800220481094001107000781d04090305800c0c521600c84d40710b806034003c0000c0248020764001c0384620360603610a1108000380104001488580d000703901c038042d8002010310100c0d01080f440d074004848441020001480d098a21001610b4081850360200050b03545031001c0c0f18650701000b40d10300c2c006103040300398846417541c0d45105141c40001d00010400ba00d0f84042811501ca82d2141c020410107042d5005441800700c14480003000d00f124203884900445983c0361055003d1000c071001c0d02e800c0400ba0045c240b44554650180d8811001680240b00f00c1e003800f004103842e044003101411702c9940d017041000143c0d10091504103c00f4030300380c84500e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895366241 1250 895364991 895365001
    0x8130e0705160201050d11090a06030c0f030e0109020306010b07120804170703020f030c1b060306010905010c08130b07150b03030301090c0521010e10120b041e12020f06 74
    0x200c820356504882c4201c070782101c03001d2440102c2d0603000c0c0c0310703071035a0b46030070200b040144044200c0504038414064508150280c0d0311030702141900c1100b60034001043d551404090384a1090704051a4108424008507017821036502091800000743e00240380d040001c900c2600700140e0301c024005c0b00308245071241580c141600c6950703a66207554014500d0b83e00010343ca40c10903000f4402000602c2c0e111099a458811800c4219240d10701c000380c1c40440c0001860b004203030b24050040d60302a8406a5850f040c1604180054600040480c4c040e03c014030140414540300f059542c0010243c406030240350348038030003403400344030601500e403030010750600340150110716481c00420342c0d046400c01070011480403000c1509440c00e100720100140e16520180300d1b00b003500400d80c1c08a04035403c0c40d110402075540c001306442c21403414003a413460a9407040c901404142206625178005018441703003004520402e012081d1110307422402c50351507038255414200560103000325200403102c00c003d08018500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895367491 1250 895366241 895366247
    0xa0504032303030609040f14250b09040e070f08010b010f030c0c061509050c0a021606050406030b0a080f01050f01051c021e0a14090a1b0806041808130e07 68
    0x1801130703004103442c0b000142170000d110003980403181c000c030008840d000c0c2118900d4071121341211690700072172144106c0101040c0d80074024122502ca0401500b490786240c20000940090007141c9400d00c00c0d1000803458102c0041c286006102003800090350100442c00540a10400003d800906103010200c4080c3c540054a05034a1540401c00103101f000d0000205c0310640c20390060030a240c40c0000700159007038104001e001403184d03038007120560606003a031281d20300303102d00030000002c40510040000d1030294120509844004142c0d1075100e480f00415441e00740c0c845000b00c20342e9103035400c2c003148103403001050f40580425030f0000c1c4c4044400c4000e0743e64114501c4005e0003442414000801c040c12450a091100e400500d000d20b0340f82da40740c02c9090840300491052141d81105d01007410411248100c0b400412040b80840e4010040441501c0842d401000560007030b446072a205410201c1d00c1036004014442d24a1544905803071850104003452504186040108c0c10103008030340d60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895368741 1250 895367491 895367497
    0x5010315050319170706090c050402190503070905061204260f090f040603140f0c01090608090c040e101d061306150605040612050f15040905030a0504032303 69
    0x103c40c01034040c695800d40361149200303210b0140a00301040214071142042040d820400c0047e0250101005a540718401c000491268517992800d481029247e0900039000703201a661110303541c10840308042e41e4401040d00d40d80000c04c82c02a02105004010401c40b0404078070000240f0081840e850010180603400c2d6445100d056100e8540041000c081c56940c10841419005028001b4003000d562480e0600500d4072880d074110703c5014a142c600c1c5001d0700041c2410440005954032851180b815100740d0f520080607000080500079180c0606c00e50f243e034042c034141c0782540c0300200942a11402d0910441309403500d01e42d001c42c0701ca50b08170f4204000069590300585514a440305011035490100c0c000d02140d00d1010844402660003d01c1c25080809441100c60b0794440042044201900e041128021684178030b40481c4907011521041c00c04000b80d10f204009000000d042040780c544c54a0754000780929000035000141c24810000074a05200482d4201d14802c00c001c80b860452a03101c0c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895369991 1250 895368741 895368763
    0x10e0906070c3f050702010206010618051e0d0b06011b08040b0c0a05010c050703030b060c0d0806131407111b01180b0a090303080108070e0609090a021801050103150503 74
    0xa41c400310000d40801c08801e0032400403800d20090b2030040d1000f10090915080403100307901602544000281d25806250a06503161003801d060a00310705200400950b4200103100b0010840648001146500c9500340c1503d4903024124018440c9080c4000500791107101c01d1030a41180ea070030141000680000c10ba400340c4403221122503d44c0c2000081d50304d801c0e4414000341c465801c210840781c0712074214000344525070090380c0500542d184082840024810072902c040c156101040101d800361281d6540e5411880003400c901440c11205291410350720503010740482030000805020003103030001c00030010300f40304101610780b03190103003807940501030300c1114141841500d00b002c204a406162510001d403040c1c81d4055110240108010403040769030108501143c10500045074100000580e14100c60710182e000e816642d0700b4003031154100005d81f001c1e070903108407051040146d45100100b4016400403007001030343e624260004060301c1c070110035130501c54107011050010361800b0031030310524 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895371241 1250 895369991 895370033
    0x40501050318010e070303090806010918061512060203061e060a030b060f0c011e290a0906080609190c0506130b040609050301150521030909010e0906070c 68
    0x12030b2a101c8850140c45000c018807158040d610003c030070150080d04a2050300c1d40707602122142ea8a80c80c003c01151180c0ba0803606e9044116401070000e030007078000f9103102c0110f442c0510381a9684110401c1141949070844c1c20340d4010081040ca0304101c02031003600000140410f02c035103054404940d25101e4403810904040c2c9440c0c0c0a12984c403034000f01d0358104030300c0300c8441c0e40388031a1700b81c3c038001c00071007100019103103082104125030f10b464068405140c4030f8180c0100d01480c1354640502040300791283c2c680110744007a0002d8104524851200104410800303420b06140c8005030a0601c41490941e0041418085803203002c140074180e140c00380d17401541c0c40fa03620170700d0380044900440154003040c55140d0000c0c01240703859001a060007121000e90090214110319103042a88540c1d60003400d4200707010a04c1c6107616016092482d40e02c0c140349003038a261503650001718849e15403d03085400d000c80c0388403e100c5405410000c2a5006d41c89180c01505004940d41340c941e8024008032141132 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895372491 1250 895371241 895371271
    0xf0102180d0f02030307030c1109040818040b031605030d111b040e0610170a05151306051f0b03090c0f04060509100e070503150d03051611150405010503 67
    0xc125070001000040c640040849886d00d81a240040c214203008504403040f003810304041d401410050300351800f941c0d01003140360a01c3c01c0c1480008040030740351102c135403150b107a03d0001c00d40d8034140310f0030000c801410f00c8204014100340a041c903051405c0b24034030802c0320f2118092040c000108001145424011400902c080000f0018000e0f0070b40a030001e205015084c02d00005208882e02d1204440500c41c80080c84000052215100c088424001e405508444200c0c21000c0d8a040c560350b000c000d0040718111000d003525040101c4604444000d03004034425000741c40041540400ca0080510790701c80d44c83c500d81180c58903100c500c060110380c0195840340742001c0990712070704110b01510018003100b0061a21721320f03c080205280c4a69444090254045042584604100c80c455203800c0841640741241000b44021200010001e40c2001414443e01e80301c0450083d4004560780201c02c124050251101004a1030420610000580c002008100300503604035003620f51051204400c007803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895373741 1250 895372491 895372493
    0xc05060703121814010507020717060f1e01080c010e0406061d0609060703051809060a0e09031201080a050706020f1002030612071815030809130f1d0f0102180d 70
    0x708402d00d000f0000e04052050040c0818020158030240c840e00300383c0d08a86c0ba00340d80750740c050540b00c0f00d4928080d150304104000f82180d0909201107821032020b0707450707118481a856950110540a030080442608400040c1c0595a8440c41c40601c4100c211003c00100c1c4c60f0030030182104000541800c00001c9464003900c45640c1c6409940c0141d4001e4000b07079031400e40786002051540088020301c001607000980300301d1410940039040c420701c4041c0c120048141046e00402042000818690051004100080c00610003101c0b02d0b00810340c0d10010000703000e40b8940141800000d070000380c2154130008000841c8070000401c00c04180d140003005a80e070300d40001246403003201c19201e824038400d2a0b00000c203004046500303a1840140741040000441032545030280c00200d120103400d09005110300041850a08482c48022903890300000d02d01100c95444c1c1e0644105030f01c0c1c103035035034800c0f840e03011124005c2c840f86d6046821003000b1441c081c0d81d03040361900c4481e06004580500030000d0590 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895374991 1250 895373741 895373771
    0xf09020304320f0d1e0e0604120201030f0605060f1605030409051e0c03010b0703111b2b1e02090108030c070830040305070e040c061106160309140a0c0506070312 71
    0x6d0552006440d050341c2c0c0d502c4000c0f0010698103e80101d00083c58855100a0740d003040c45514242c406c0246a141380024181d802082c3e074000a0208504001045c8041d0000e201080248010700002030046158904040c0301403403800084c04840c03001d03400100b0805100310000c120b130305503a00c8134103198a8000608044454861a401c0c0040794441c0c2c4121100d003101c0c40c5e8802d26004011910309032001c0d0500d81214940d0701c0106505100212499098001040e521001703150b01101d4251141003040c540010328800c01c01e1740081441d400000c0e010000d000103004001c06040814002e11030380c110700500e0286000d115141d000e4031407034601d24500c034140c41f070111801580c21904070340b013007612010b01c0c0074480c3d004c0d10116030400c01201c001400900a0604022002d080005040c1c15500e40690000c00d801d00d180341e908250b030f142c000e031001544c1d1240c840c00584010008007210400c0f8981540c0407025078103c184142024000200041c0c0d010500380b140840c1c00c100812b007016016420b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895376241 1250 895374991 895375007
    0x4243e0102070c0510110609010e0c011115130602070b090d02070e1b070b0c041409190b0319110a05011e110102130303120c0302040f09020304320f0d1e 67
    0x9021f004080c18030400b030750150800c1000d0031294080ea00ca0094a10041d100c0c2e00c0f0065a00001d508501400742c0343c0c1c048406210760002d4018221880d164040e5165812a4032104007162071115280078810000f4003000384000008050000701503a6081035a1100c00c29001424002501d03032864007450368241d40c0c0d0940303007299403001110750a030400d1610108075410901444096061680d050409841c289d1403540c0100010012507054200610480000d0643d03642143e40502c56425400c0071200008403038003500c1d006501c1828420031600412991185c2a031080c2c0c1042403403101c2c80c020000e06c805207104081903081458583c00c116404a01900034108403100d00c100510002081c50780100c10300344c1e808400081000302d0000510705508034000c40c010f140c07100811290601041885500550700039015021881c0048400d007158040940300032680603030842c9802d1088442c034001c002c01d00c031000c0104050705c811420308000404000380c03004001c0d003080701c0d1a45403031080c0c021240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895377491 1250 895376241 895376267
    0x102130f08030d330e060d0305040e04171918050907050a021908031f180f14180d08011a160b04120e040204243e0102070c0510 56
    0x1019030006400c6a000039904c092040014184401c800504d0510702800c049017065030644032103007818207014a039801c01c64001c0007105d91040400c5900b40804d994000381c040d00c43d41419003942c066000000500700d02088564200c800501c1009008654403010110b80c400900c3ca04180c0350b2461607022440d01c0018601c4240041e4030741a21010f2048480045124900421f034051040c0a910003c6010105612444840740320500c4014035526803900080321401107807101142d40c1410010204114105542c035646280308c0d044007858202d001c0c480307502c03800100d01306000658948005c0d203d90700b120003c0d09038001c900003a0410480b5100c201d104950b074100d1145000c0c2c3c81c2c54500000002c00d060300f00c0d40810345220b1100c80700c1c9458000c450a403400070300d0074215400744a4070000301201407000302d030a0290410744c901c00710b80944100c100c2c01080c0c0030419220101d607443c040c1c94511190490b0300d2a401006005c0c0400c0b0089100d108507207003030310780041031008080c00f21820708602035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895378741 1250 895377491 895377551
    0xf1005130b0409060302120a1220100e010615050706050c0d0c0215010801090f02090c120907090c030b0f13021c020d05090d0c14010f0e0102130f08030d 67
    0x8002c02c403542c01c3ea118030161780c82a114100302c00f00e17844220360368060501004000003141400304c2042c45c42521580c202d205094041d04c9410340c072403940e60038207181c5159402401c1d0740d01030001c0b03248824024900101520f0f0049000000c1100001304144030300b42c405005540c0701c0e40855564000171040790001c0c84c090f0800c0144105c0454000d4560444003005181c1c1e0024a00101d03503210b0612900d01c8243d407003541d11071801302da642400481d80004040c2041d81c103041c07008000100301c3c106402d00c80c802a001800f5014100701140d030446034240c240f00308061a2240003441c6444041c646211814119002c0c650009507202c02400307486180c1c0700058100002c428662445010340151201d401c03802c17003e01c0140c0d1460700300e0360303650300300d604003400a5500c8141c80041340850060700320b41141d1600100300205082902c030141c9a440e180941d881c3e6001900f101301d80d50460a04014190b1180c684804034a003081c407942d0780c018485c030451072540e0303008000b10307551010070141c050302880c3d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895379991 1250 895378741 895378747
    0x90f0f06050a05160905040b030106030b1303090b040b0319060803210a0e0307023a110f0127052707030e19140709060501020c0f1005130b 61
    0x12926001038071050712011400e80c1484040b80450501d103105024040700e43da030b180d0080b0300d131008200107045400070b107641556a0b00c0f000f0000c9214014028481c0103e00301210080d0101c0c0341c02000c0c420503505c44600000f007484107200c2988540100da4000d03c0d609405050388100d001403800502d8268829140c0388800511000030310b00d844031003e101141c512a0101c00c1d0b0b10b401110f0f0948a448a1891050700100400c5005150040020310101d80340304840039081440750705811030f0b480000c0e5501c444440002c0c0b020400648001e410b10000040d0741d403103221984039001810320440d49005a107144d180c110744c1070100d5500d64071240145030060054001c407400c024141d030304000b000c0c2c03000c001d2420300c000202c07170301d00038080d524809030010001c1a4880c48500c0440000d00018412207441c5a502c1c41d89612440412100c0301800035000000b5a1310701e000000380c41d2078022042a4014001c0701041101517070340c0d5000038000e811504100e6a15120b1605200913044a03804c80c0c2c82411000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895381241 1250 895379991 895379993
    0x40807051005160b060423100503150f0c1b1b01031407120e070b0d0c302c010c020f2d0a05030d0f0203040210031a060a022508030d090f0f 61
    0x1f80132281e00616441340c40f404402d03111002c0c1500c410444210003030030034000c400300e80d0b09009150540e51000d200031040b406e100c2c0e09440c070710f4551140301880d103843d0700c541c1e000c00c90050310301035540c1d030940c09080410080b048510420f0411300c000745100d00b07005c00c05180b02c580c1d1036a41c002e04098034a5200fa02c0300e80e41c0b9903850341815080f100554035a0b40c82c0030415040706014000040c140030340804210748c0301c40c108103021038804400355a11016a201c2c0e11000042c5c240807071300000481c030303071401109258941c801c4508403420911145c0465001c000459031603500070404694050044030786240000141004903081801c9008801320340c45440380380028010040050040289181424001400515104800c2c1c0c001654040d520034050070104040c98042d91028845444161000d4103c1100d01c0010760150400b030302d007101503081002d490049131150304401440c2d11a0003485240d450402c41d05561b41e00906240c0f14400350f0b00c0c58020700380560b40d407060300c40c03076170040c80111403c0721 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895382491 1250 895381241 895381301
    0x1060f0f03060c03050702100902150318121602060c0118120305011e050906030c0a120201021504030c120203040f090e06060a0b091311040807051005160b0604 70
    0x440c07000350703841450301e95098002c1c0e12034001e8a00501c025802084d4111355144d42c040240b20551081740d01441d083c8504141120f40b001862040405241881c6400691100507062101d076820074801108100181101210035118020360603406956141c2c840494015090040040c1e20100540702d03419079404c410445500000c020b003c569503400c1c0020b90b61001c040d180703280c43c80145144080100f606200d80d00340007880c941d10485c0201200c1031501000041400505c10743c004c54003104c0036048150540d601000481c00901c5c00c01e1003c4143d1400d920f0042c011034030100700401c0c844404080c01010b910030020340700503109440d00b414459580d0700c41d000040111040b010080d0041100080fa2464030301c410b0702c21070b049001080d20b05110401040460b04640c94001004c560300c5021010260410b40548060400f503401070410b02d040408000a200d01583c0c04c0703080010400008100f00314546805000c568440785080c0341d5181c500026015041445107540c03040c50303c280c00c03002418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895383741 1250 895382491 895382519
    0x905040b090709051303031a0d050309180c18060d0c05130b0304020102060f070c080d0c1407050712020409050604060c0f020706081b190903061d06061201060f 70
    0x441e4408403900385580d524008180d42048171480c1c2e000c071040010f4000706e8043e030082c0040b5a5600034440c41d031540b40c0000b0300c070700349401c0050391581d0011584c0c1c401c0c1d0412615150340301901065841480ca8940c2e200301c2288640d11003a9445071211410b0066516400c00340d40c40d00070012828052007a58200003012500700300ea41800d5600040e100244003440c01080301c0c011034042e40035148035525428840d0024901800d9031003001b01d005a40c0340401d40d9600601440c4c81c90b4030700400e0740039940300001c2030f9800d080705180b003100003040454001200054600300f111200b0040800c4207003103000080082c0290800585103000710400c03c02004000d6018254034a50354070b0b007a40d01a08004101d03910b6240c1e000350300101f0b04050110310700c040c030b080c040900340c01c161050502c1c20003000056410b001080307800c400442c454000038400c0081038020b0703c1c54110340f114111280f0540005a070340d01e4038041c3c0072070f016000c401c04546407400300b0340024001d04042440b41103c039940781c1c11214098 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895384991 1250 895383741 895383751
    0x8030a0f0b030c0f0a1d09060601090503190f06091110050a300606050418020f120a290102100e07031211010501061d0109030c09150905040b 62
    0x145003000c0884058240d2140228008000c0c0040c442c441141061201800e0140303d0107900840304600000c141c091720103811440242e10740303080d04a040001d021480e010001d861581031000c0c0c0d00c1c0c24017180e200007603201101c04090f01c0c1485038608508001d1416491014080c00780c90400d04603905000c400241a0414903040c0d94410450347c400340e0460315400341c20031500000700f401c200102100341d8220505130340c08030042e8010741c00c0032041d41e03403080352310304d5100350082403012904004c0d410144882c44084a07c2000640c503080d081050580240f00d07000400300d4090703800300801d64206d65940181c114040d10301140b510703d611b403c0305000c10310344044040d005200d19200d4100100441c004c2064140005004210079806c550781ca0000c1c00c07506075484104a0040200081c810b424000c060003060151a80c1c1c000300344844000344209401e0583d42d051100321202000040c0d1f4403030306981164134441d00018484001c3c03140c0048134090ba8071070000c0728109810b00080c4402d41c0c103028092 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895386241 1250 895384991 895385011
    0xa150209101115070e12010f020d0c0207061e2a08032d060d080f130e0c03070905040f020d09060b090f1909020d061406011d03031c180803 61
    0x1102120840f000c041c64100c42580001c3d06940b216403580c01d18002150820f0300000010410b415241e0000d812a000f140e003c81c10980c035400303000c00a5405100c9030014003598075080560b0b90095070242e0801074003044180030803050b29080c0d01c03a061486044200f050190450101d0107020f4204013070150000d459070410380611085081030802e0340e4103100e0494204070702841503031b6035000400880040e1104103aa4000c8100f00278072201200ca402880d1100b80c40580f02070300b40c20302800e034498010081401c00f070550208103101000e80c000d500401221000c0341c0108904c1d28841206020b40034100741c69243c2402c042da0309c0200001504684104802034685044550f58074105051038107003660304131501c00c001031020b07071085456040b030a100c1740003500d045554078160740d4650032960803031038003da00f0040d40c0c2030040302d60340a0031007280d0300031104406000101000c0000c0e1070f4860f6940307003540410202424542140d25410485a890442c00c00360307440100380c00c0400d080e9100721400c80403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895387491 1250 895386241 895386253
    0x908011d0c04020c030f0f0c0c0f03061302030c0a03050309040c0203040f063c0806040c0f082a0a230313060b03030307200c01020a1502091011 63
    0x48206000c8120250501403030041003040303503410078400254001c01912900d80001c1022808142410000301001c0000d110640c1c6c1d6664041805400c080440c211039104180c01d590050856500180381a040b0a01489c4d072a003189141c80020700d0400d03054040c0380c1100c4582ca0020501c103011015007442c500580301405240da030340e4001c030384074492406201e1034102c03104d1082c01764522943c1d0303168000d144010510b80d106110b1014072481e000c01e502a10044100800350340c0119800160190420000ea07400e00010080700005464640032429010400603400006124854080c03502c0354000d0260050851902d0711180c0024241e215501282c045403910094034111025110010f907407003480700d0924215240d0f210032020000c400c086c16581c06403680340b00c420f07a68040c40154083c01c616291046114001d540034107121005103007140154000040b002c1740c903600455142000b507030017006003801030600503c20f0000d0189440864000a02c414042035198101f07031001842c801040c11180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895388741 1250 895387491 895387511
    0xa09091811150703050d0207021e032428050708040507080a080a0f172805040c06050a050408010606050a08090f070b0c100504150605090f0f1005060a090801 69
    0x104002c541202d2440c00001c108070b402080c0314002400748a200d00c040503241142503000070315520400c000403060321204807001d5140345030070000c5e403e046400c00c40c0665054404540c50a01401c01050049a60400c10356030140200521360b02400d042000420046410031010041100004860484480c802c003500440c01c0000060110482030380040b9680c645401518119a05450703440000709005d00904000c600507180c0000d14460140e025188141084042130010b00140b6010068015440c003c140302c0400c0d16402d1640c1641d016003401c0355510b65076a012129031007154000304913546010000701e46158000020402054190344103120340c1c4804180300c2c0c5401da003440350051688442c1e01000380d0103080c0f02401281460b0b0003500c41070001c00b12040c0980307034119002c03a80310140e0343c034102c81801103100d50b8016080a80e020341c43ca19000805403a41e68000c0e0800c0c5da10b540b410009141d5191043c2c141e4041c100152055440f000c1503100a8258071040c021044c080d406c060441d0307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895389991 1250 895388741 895388749
    0xf0705030a0e2d06070203100c03050c07020d080307090806040c03020102060c160b0a06080d09091d0d12020702060a0c02040b100e1504210501050604050c0f0a09091811 74
    0x10024040900450f24055140d110002d0121040083c540e0042c009004450150b0b809224900e02610211004286a00c06001c01403c6502c02800c3e450740550501110015031604508030803081d03400022141c3e41d840320f41007502c003410075601c84c0c10148103880c100020018042000c2048904c00e8007244c1107612007004803801c40c0250b0102c08003880c2080806030100d13110142194015072250760010340340f615400700d5410031100d40b900b03a012070070a5a080102c0d0f0703802d100d00c00e60744465401c071f008039420300100e082c0c9900c1c2c0b04542d1410041e0300070784460481540e904070b035200c0b90300504150f82c501050b1006040d030110004282d100c0e5192066800c4141052690104071140599549188000d02d50410801ca43e0604540004a400b448082580c0c042c20b15000c4400124040c0341550f5105403034a030703007500c4c00101802c1c003960a2009004580000e101a20b841d8640011600d8880a03c0b890403500c184165200c505e2039801c20004400c40301d60f02c0910644540542d01c0445000c0c03895040c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895391241 1250 895389991 895390009
    0x62a1e121403150127050a0503030406020c060a02010e010204030309091518020c070905040c0302090c090609130b100302040f08010e03090f01110303070206160c050a1103030f0705030a0e 82
    0xc000310709000c000284002c211142c0e8401111014148040542a581071941c0145103091a003211045050300a20007454a80e003050b0081508800545c9060309040d4029243c1e645a20344d50700600d0080794448416000390002284461b044000310b485990701d080080c400040b910400c0c0d0b00500c0c07c5c0780381d19481e103403800f01e00030303182080c1500b089413045015100082d801f010001031640110039022a442c070f01c1d0300440307004d10b0250301c404203024114010010b044078054070818001b4410414200141c0343e510030344407050002c42d010000f42081c900c4c10030103840354411007a4050085900038180a400da400340003a22007010840909076106d401c0706080b11182885c1521641c000c3c800c082c01403a01a01454009406141078007100b0810b8101d5440c40c0c2040d0751a1000d81c00800c1080485443c00860300840000e5280050f604201381d2100e61301e8044403080503180003a120240507243d10304100f112804284460304954a4001e424a580c4075007000a2080c002082d812002d0f200e40740910304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895392491 1250 895391241 895391267
    0x6090a0c090b090f0a0b041a0403050d1407060f0603030e06090105041809050709020a0e15030f07031808071703060a1404320709062a1e12 61
    0x801c01c02a0411450342025004000d04590110903000c1a00e035684800700d045000306494008280c44600b82480c0396850304000a6030f95800b8005d100400100e080090b08800028050901f100c480d00c0d0300402110600c20300d1070250a050400007180c030a81e840b42d2000040b02e001c1c0e41c274201a034080c2001c00c061441524070381400180240024402c0198044191071a01e0ba0110006014085680d07017900f8104103600c25440c55502064a55040f90010031259003e007044900b500004c04040a4080e1404040c00c003083c1000c8810000d203819029074440c178a0b683c1d207000160213070340852601c107200e40d01008080300c04402484201e1003540d81001600c2c000c40004001411007414001c0e0140780082688800e40c3c01501c0303140541c1c0b80c401e8501d03682851002e845180702c000300a800000c40703190f4051301d038404212201804000466004009d4408520311202480b12001482850500e40411800103800303885240e601420061098a80044a6104480041c2c3c000c451075400d942400c41d0b109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895393741 1250 895392491 895392497
    0xf050718080726070906060203180301060b0f070c08072c07020a02100516031e09180f06080f160e04020f010309050102071a0601020f060408090f240306090a0c 70
    0x56076050f81894500d0072441c0407500300301e40314259036080300d40507034446a012001507040002c03841078484044564008030f5000790000e200c5e141c98220380c4c400c1c030302c01e16034043e0038010b0101d0424100440c2184a50062400c0411182c00c00c1e111210000000d00089060300d84034809c03106012100188591240308282c660064a0202c1d0140c00341303c03d010284250b441000003c01401c4c4038016400c4410000c94040e030794a111090001c01090303c2400c0307450030072050080c2010b0802041c01240f81100d819604510040349100982c00b18002500050304006800e001c0d0010030580d41c0342c005130103d2043d00c0f400c01000055503a118082c0410415500030303411000b410389004081d40a5000451182d108100051502001d501e9404060b81108241c01baa0740c03801e0140480c40d03038100545541011007401611060074155103012003031080600070b82c060740d1018a0b05032103035a40d40d1255000030840340440010020700f05072241c658404c5441510400076040400c0e455103162066203004006c0351 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895394991 1250 895393741 895393769
    0xc0f090f030f020d060c0807090501450b0a02010b15031b19020d0909020f1206011b0606050a120201081515120a051f090b040f0507180807 61
    0x28032940b40b1001026030603608071044489a00006015109500c442e070600d96401e6450f0601420040100c8038507403100381044403120780803540303221050815101c0d00459000c45c00456440c00031403040000211074075541d00001100290715054040101140420381e40200009450317030040006101c54400101c454000c103200040561196140c008000450301681c1410300d5a80e072039000c01c3c0820340d6480c2c2c005821402d00320400d10f400c140304501a144c010015800c0a622011401d4207015510b6090700c04000c5001140ca580d0013110f04005074401504003030309500984c01c066014084502c81e45008404d010400615001001c07210300ca2142d050303540c41c09a886c1c60592101c12100f800c617040d400602d545400240801080c004e15100503100c4d100d07800c40c98a03d0481042b01e070024038130042c010044e0510107524100305d00c110103580001d00c001036286000c00105000704042d01c106501c091401c014010300740e4004403a450711003d0890480380c525111203090792540118481c6141d250301e61 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895396241 1250 895394991 895394993
    0x31e1b030a021312060c020106080a06180b0f090c01230904060b0c0708070b0a141c14062814030a06050403051e04030b0109050a0209030a03030c0f090f03 68
    0xa5002140c000580301800340c200240e0001003e603140155001007502c500c03012940c1c00304110f601400c4c48042c4c0e180003c000041c6010b403001d80301c414480c0010909991092418501050039100b240500e03003140c5a00308a15001b1000f84082506941d20f8280d40704010400556620517100e0007100c264820841402c04101c4604210301d81150201c02c0d1b001c0d45405000c00e50802030800307440c82d4910711008104186c0740106032410109960400050807400b0482c1c25043c0b90801d00341d028a00410350455940d2060166200300c4800b6000000c1c405402c01c05400032640c5800d83c100c0c00740c502244d051780f60341ca0380080481c1021480003020b08188081030100098500104014003240c805400c0d02e00100e80b9541d0b100885d5003c80b0b08a0226a010031422032105030010804401044d64000c04d14050443e01c80740c0c0c0b5078005116488456403201e00180d80034005405680e01030174058116510462240f401402810401101d0703000200045004117249224401220844800549001c815415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895397491 1250 895396241 895396291
    0x1020c0106090920060403060506220b04060603090c1502032b0534031d0a03030501060521180102120402030120090f15070b22030806010c02031c05031e 67
    0x52006e2f078400b8491810048403410700c442481d8911100c0000110b0156001c100412079106800030000c052404042c2c100041104040f0010f9640e1080e640c850151001d600300d1451041c02c2c1911000c040d1a5140c1d000320884102041c008074410105000310382d5130a03101403000ba00300343d0144892546041000000307481001542480c5020700d0040b900201618034240c0c8c9503a08040400d4642c880c01c10072050581c148940c2d405000c241c544946840c10061190780700e4484180310341d400455603030128403103d0403125945030701414400295201ca40741400d043c0c40c4030f41101c0a900075401c00121003040b861004804000b00c00400f549401c2c02d116030203004040c4e070418800b64100c111040352880d8604c012000d090414802d0720b03030704102d02e030541007003c04604c240c88070025402d010342c0c0c030400640c129022a500c183c080c80c040f08454000d00000f85440d965100c05001d0859001758102c1140e0700000030741c411a900021414007021009201a0300001181c0c65200c000301000700e02140e5407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895398741 1250 895397491 895397501
    0x60806010f0f050d0903050306030f01020301031709040b09161d0a030f020f06220602150f090a170c060112022b02031902010f0c02091302010201020c010609092006040306 75
    0xb00c1c3c0f5000c1e00701201200f010003100c4c0503440940202d8004003c0101504d0304005002c44615503100030b41c195451035541c40254a000310500700040004a0100000c0e02d40354410305c1c0d90b840090000e02c090401c4001540404500c0d140e44c0e00041c0c00220000010900c00c03100801d1840140c181c8200b40e1640d1292241c02c1000d00c0c0499201144480c00e40b25951010003504035000c031292040c0301e000f40300c0e0f0f42022100d810791008080d504800a00e20072055010300c143ea01c10840c17060200103940382c031330150a1441c0c0010040c000c8924102d01d07a081c1304444060040f40e001d80c4126446640c031410105040c1c0400c41e4001d40c81180c8911503071450582c890081c114040c841000c0d0150180e50703001074103103208507041d03503801551508101c0c203660f0310407220304c20b512141c18484800b0016070081003c1400041440521105120080301164406d50446403240c44480080024a888015103405014100b8095405510728141000b1400b62811801b122541c010180d51500d031459440601400e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895399991 1250 895398741 895398767
    0x21809070f1b1b060329060405060c01020d0f050105030c120a1b1701020304020f0f09012108070c17030c071413021306121a04090c031b050901060806010f 68
    0x203d0620030340c030726010f14031242d40d02a18064a02141066440525400f140c20342c103040d000c40416011136071482d490b5002200d040e00d8080e0f401d190789425040c2030380d003e071040c005c0c2c010030f081c0f500c03240e92003100c0140e00c01810ba540031130030741d420700380120b0400c540790549181e22540c40c0c201440751400503495580d46000d40c1c4502d40e1040340240d6490800040134110501b0900b01d0750000200411854210440310070500704640c2490f6038140c1d000030801c401c405010314021860105036a41841c440c0c50125000c195001c040e4540d42c0c0c04900c0e02104010051140304035000359408910b4401001009450811030540010245189400313039a14003020000e15140d0006101d00006d020485140024800d01c001603031a1b2421524211000b404580a24840020780307141903240e442d4514201030381a50610101d5001c903034980c06050081d41200d05900060508921881c1c00c01c11800d00340404c021500121100d0324a6070783c40f4000c1d1001b220445100d80001c19001403044124041d080040310a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895401241 1250 895399991 895400003
    0x24030305090d140708010c0810081e120c010b030609030c0a06090312060b0a020c0f0612041e0f030816090312090906060905030f01022109030d021809070f1b 69
    0x400004181d8130f051030081d400c003078416512081d440c56103a4020900d81d030041c020076056000311340ba00356825200d100c1c10300c0c201d014030f030401c40c1a0116181084411520300c0b03211142c96440600c02e007520b00911160780d01178024090000025002d010100c195507800c1c480c0000760180904640d5181d00401c00d03418120b043c03103504d0b148071240a0300c500c41d600c003511101085955a8100c0200039141242481a81d40b05404000f0140783c0d076116541525980040d0302d05a41013500c907460551107440c46001400c0980440317081d141c091103544102d0041440c0640c5940c10280c403801c0d0f048485030102041708000c100451800c0000031912041d0a900032801e00e0302189103070310b809900c0b06445082c0e000c040082c00190082c00280707030600c010b050004514008500d0b04c00443c1002c100b41d007131111a455520301000002e000c54405104072458589001c00841d0f88501c9001c06080b8040201c1005015600000009800302e0140c0340043c00c22449868500c4282c0b0041d10441160000007001c543d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895402491 1250 895401241 895401263
    0x309030c1905152b1a1f05070f081306170403050306010c061b0906091a2a010f0f1e1113290a140f09031024030305090d 53
    0x3120011812100c90030061040711080c076115010f50242c514003950711a4a04150509203a01e5450400d6407001446d01c0109a40d2020451011785483c056090098410440e82043c001041152002010030420303c0050a00d610380791481211502410710301d0500ca1525140410046030050000d1944444145000c44000c010742e0355a0f0281d5020720725a02e800503582c10600d40f500e401c08441c402604451400b10241498900130ba8040080f5401c40d024111001a5040c080c801c200c002a04815001102c88004034062240a000b00b5241c074402006914040c0c855151140c503001d00036180039800d40400310203001c00030180082c5240410f09103401d40411500f190001c161141800600900b12580006000c007503440300c024621a0940c0359640c000c024030540250019085180070380b46071000e9803114042401c0760142d01c61045461350510034405c46000403010350b0004030608004514107401c83c6a081542d03200950f60780002000f16030305000c82040303403e10561001c1018014807031503030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895403741 1250 895402491 895402507
    0x20d0e04021c0603141906092a0e0c0f1c02040f14030d030507090b0310031410140108070303030905070306020304210905010c061e0501080309030c190515 68
    0x1181a8180440b9072016440d40c0c010070520041ca030184184144003406803080c0012034202451100e1009801418103a80d040381100b408000900300300080706102380207030384401082034011100d0441c451030307120b00c0068001409011181094440c07003500d91040e2810025108080c64031000030b039030340c1443c940e8207010000d180c0e2103d4046c03500401c52a501a040c86031180f0615090210000c0708006040c1820144078200340d0001140e1308444d0501001600e0b901c6440114001d6441d40d44081c03c0200070042101c8022000b14100038000000b2004100318035801e005056a85002d104d8080190800c0c2020000b0901a800c6411214400c03000c2d0b820a030344a41d2070784220b030000c1d1002e03981050131f5900003401c0d141c0c1074800384811802e400c08070200740c0783c20f000030319403108100001e20301c0361110784285c01300700303070740c0c2c64024100b05044284901d6846248003035494011452051281c031540b03480328031505025440001c0080c1100004c41030380c1c24202401400d05605401e0000c41004000c00c02e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895404991 1250 895403741 895403767
    0x30a180c150e04020306060301050d051014010e0f07020c121e031201320d050f101a030d030b0102120a030b0f01030c0c03030c0311160302120703020d0e0402 69
    0x642861000352511030510540148100d00b209902805103104000f400296602d81040d00d044038001c40f803442e00b200091920504240038280e03101012801c00c0d401058900c40c00f418541a83e0928058084a82d10b1080303032946803d0544d80b0350b0142c0c01909032010781c0c1c140301c09607544c4200d030901110000f080130812000740c0440980d0282e010713000031030510254043c5115150052125003c41e2f8a100b00b001c291680d00d4440d83e5007482e80d81510040c4050a40711820380740d0301d068109090350031069440c0300032a2145c888100808006141c0000040c1102c0a901402c06c106000341c0280324505070030400354028071104082a0641c8a035a401500105000c80186202c200568021030428032035018005a980181a03543c145801e044500701c0855220075032280c07190309450045290359044409800800c440100d070441c821000402004540880d000104114403d90843c2c03290062255009480d00907840001c00580108400303080c900d204000d00090b41c280200018070700720040c4600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895406241 1250 895404991 895405013
    0x360705070c14031c020606040f0e100e0c191503020c06070f020d05030618100906060e0f0301050112330f0605010810210b07050301090e030f030a18 65
    0x62001c80700986401c4030b103801c041c013884404454071030441c1c010490342c2001a48030700e40100f4090140756207035a03080d0042c2007508040040e807540c03800d84000701d9a80001c00041d080c04c0c3d0125901e8070412010043c1400c03c01c100480c1c2013416003440645138240503a00d8601000f1071404800c15400f0300000342c40680c1840058042d504640700d264010600e000040d080900351100982445014805c02c81203803905010740d082c0c200c02000070300295465242183d0040c2c02502b01380039a030700e4400085034654000c40310394201d0703500321121040016060300301401e1710024040d41c00400319802c0c10f1400241403501c4d6a5500034150700701d0301c0040b0054201c0d00c039100440e0160940b01d8035a44208a07032122449400081d080a02c2c14186030700d0014806c142440581c400c45d921040008013581c000b2440311142501c075680140e003006c03142411031004186030802e01441c40740324a1f0180000c9e1501c40081101e840e518040071003411070341d608034907600400400110100c1c8052209820000900920354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895407491 1250 895406241 895406249
    0x9120f0313080c04090819090e07020a02012c060304080d140604050906060901060c030306080330160302030402310b04061206110d0603050705360705070c 68
    0x55800040c80d152140f03241107094040c15000301d2402c50f40d000862205012100901205811a405103180b100d041341e2081d11035024030320b103460120a2000596000ca0300314403c42c001d07607170000611000b02c1c601da41a02011090101158244d100d46101e080a00c00786130300900400c090b50030840545241c0e419600c6689240200520000801c8002e00d050700c0b609410403003101c02004207107403010100e000d124040c001e80c0103111a09401808043c480c0d001840a4000c0c802901d4407200105039050003070b2690140b0944020780924404610100340d80c00074498000721038035180b55074008009400a500140050341c11241c044030080508842c00b0006081c0c01c0101e00203071100149410180c01c032015400c4852040d0305155080000c2e80346007142401c4140c001d00c000480952102e000f500030b10074400c2e8800000d0030454004240800450024110f90058038440005107240000c2c80e414403128844144884020211051b681d2090516583c48815820058074116003500d03006d20120160340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895408741 1250 895407491 895407517
    0x91e0c080115020d0c081c0e0705011e090b072d1101020f030d0e011404111c0b0a0c0302091201091a0106050f0f09060403201509120f03 60
    0x1004000c003518005014082c000144007400030a1402c000c010007803c00c464000c1d040c0c503004114500741425019134001c00c410301c80410854413140c0941c413920703108688903c90210782010700d245d10901800f00e0010001e0901c1d542c50749000d04003d442c07070380c64100c1041030744c90340d940940240d0315101e407140c400011004403015035800c14540c40c001c3c9101c0025040c050454001548100c0802d030008140c801d642003c10380403032047c0e080a00640140040b010030351420264006000c00d001c41400d139a9042d0109a901344455490360840c42d02e199000d81004160a00c1c0800155203001541e0000e403071980d03286800341c6003480000000c1c40001440010307900c240d41d5070385c4a908208000c81075403e82c11003a0078030440e662501002401c64000c24030301c04400301001a00142c451811800c5841c0d55070001c20b065100c54480c10320003801c400c901040c1b508030480004558445c45d088082d01208000c1000c0d0518050507034003400340300c940540710341019110710f9400d80c0c0120301c14005041020440c0f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895409991 1250 895408741 895408757
    0xb2b090506060a2c0612071706071404090209040b031605130501080c330a030f09021c03021207061e05060109090c180905060102070618091e0c 63
    0x400542e10000d070712501400e500304101444e41054082c0280c0b002c01c940061015a6484401140b0802c040400b280340902508030081102c004c28103041210844220458a180c0e1700d800040d03e140d1810314100400c400c0600c801c112085454004280c80d00005d840030404a5281022170b05d0600c14490307051b60500020802d1040c1c0c200003a8a80748007001e00ca050116515203503105465085410506005000103840c0020100b52100040070312035411001804001c204481c44000390800d690300c00000c3d082c4401048202c071140914904140c0051500b85104500c90407154130080040048042d800359505483c0d102590f08080c01c0000c0c0200710200b1200c1d0030300045071035071107500c4491104500d0720043c032401d039912159140c01e458543e4030008441c802e141061301d5103403507581d2040003101c816101107002096500035600807030b1700ba000c031400b268440005558400340741524801c0406200c1c010094504281c0002010310f416981900446902c0f046074020b03140380b0356130440480d10300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895411241 1250 895409991 895410001
    0xf0c0c062502030702210f0a03081008011a01030c1103220602062a0702090435180f0a0308030115050f270d03021e0105010b2b090506 59
    0x400c0e8054400740301d88083c600d400d030f8170740c00907070124801d01c0d0f00c000300720000c20034840703100c02000300c0040c203241d2008a60b080070503454014031000d402c07200d0000d038411000c000a012a0140a844006052065030b034000e485540c00443c000c3c0060340004080040308203080c055041c00b4002444086801d10180390071054495010300440d546e0b5001c04110740c040c0741004540e02c0c901307810034000000940103121740c1e4030f4246648a103009090001e503008880100344420449105080300c6000c0914000d50039242d01540050358111812281044000702041780c8210b4404903011060f1416006115180d880740f1031012030040350301034008403a1113100100500031885242007440184e0043d25013203181c020548211444c601440321915160440c0074600310044440400d00310310060090030014030340c8081d0500955441c2d00c188130207000c1c2c0ca5040d08001402c0180241c5050319000e100c000e240100c454104c002c1c5030a12007603100032540b0051001d410601ca809a80310403802000140114205 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895412491 1250 895411241 895411291
    0x9150305150702061b0910110d080613052d04061103010b07080c2107061109030307030f090909080406110f07060e0103180c0303081602060f0c0c06 65
    0x8142040c1c9410300001c200c0441d50008010b44d000300c44078070050031100a0190750080f0f0285590007a4011902400d6021503070780001140c1400030400d040301c8909139410f206480e100019030380c0e990400171741d13940084441405d1b044030703800c10803d5026015808031030b04150350501046080c19401c0011a0502c420311079103005050b50035001c0c858280c955454251410050701c14180d00901c60080030851041440301072201c000074546410030345800c4001c4001c5002142e0150340100d0300d036860705007040e01000e003200a070781358120054001c501e407003200c4e14140e40e080120605401000720300200820800032500481e049540702d20902a196401d20364040c0040700c11914400c015880b0b1b608031030200d08002440c4007140e2190400448010420004038080e01001c1d690719401c40b8080c1c1c01c2c1080144403c10103084a019a55441c03568481c0780d03840c811252048801d800580c4241c02003410a00294160750308031a13249541460300709155103880c1420070031a9200c0c0800481090580b414407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895413741 1250 895412491 895412503
    0xa03020c010824041a0d082d0f091c03030b0a050d020d140109020a030b01030210090803040504050a090b0f07093002011403010806060a1a07020d02010909150305 71
    0x46030740d0440d550418244100e0f40c0c001c1c41d014280d0701c180e440c0c08111142042d40403218580300c8018040201803402800c103500591710140000818a0103540c04604040700d4101c4032102c0c501421315140303403140794030b000480b60300040c031001e52200c00403000103080508142611111803003510003041812040e0100403500300560311117806036a0000440e030041e0360700c1400c0265694000740079003550450a0f500c90044c901403800940041024202000340007006a555040f6803007101d0401700c0101120048603807075100d00c03d90281d0b61080c0400e100380e18051300110b5100305143e00c00205505140c0790907007408429601c0f0012040500d0031700100b56884010030000c1c1c010300c0d00050300442c094001849000c000c0c06110200c015010a00085a1160b54151072080110940c03644958541202a13100d0308103944441c82001c02c03510014914032120905400c03032000e41460b606101d110303020b10502000150741241002400580811082100e200361603010080c3c4000140d01402c40c600545000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895414991 1250 895413741 895413751
    0x306070503010602060a0509010b0d0b010e0a0e030a030b010212180307050f06040611030c011b0305011d0604090246030b01031b0807090203090138060c0a03020c0108 73
    0x31104100600006400003011500100600c8000031246d41d0710b03012500414440d00701039404886110020240403110703513414181d410492500e407090f01da20820004075201241c000b1100c0d0414094024028060b600c500901403040c0140d84641445600140b05a800003d6410b03e400d081c400c43e44407800d007000f003203019010603242c07400e10a042e440020402d0041d44160320811102000114803c101403080d201600e0780300009202c420b513286601d241981400041800191601c0d0002458100d0748404031040c44104002d001c07503403a200c0500001d03054040050380c2248005000182018803007200030b100da42403070099228408211681c0c02684101412001900c051103c184041894003d1041c1101da100403064083c94400700181117414041c6d00c111103501503404009007400540d0015441843c80f1030003003010b002c0c1e811000701802da5402800c89500d28580c62516a070504150844064000500c01414540054000b5190900212040700140c001c81038284203560400c40d00384d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895416241 1250 895414991 895414997
    0x4180e0109020121020f0d06170c010906031d0706021b01080124021609060303090e0f070e03152a190807120c08010501020708161e23030607 62
    0xa01c982e8000810082c104600a100741120a0303425500d040c0d507a04850560301c40701308441d00c6d015410b07900c0307005040d14401d6500e0b82000b0a81c4032a108804182c044646005840354100142000001c030010000d03914400c80004540c01008481f410401040d001448160700900300b500591422000c070640102080c1e0501c102800180036480100c907140a2101e038406080c10785000310741049181c004104d0782800304a0507000c011401c005a90451804d6900070340300c1d040b08540e140c1100310b8144041300c03110701116920003c12542807103428105000c880c01021075840302009812110b03404016a640b4034500c1001c203d804241d460301e6642c0025490000c083c908044440500070804901204000c0420080c44000b5041c20701402590b07140c044000001c00400c100540c003c1d181002c20700416000d407165500c0094034020008015080c0c8103c2035100c8010317031405004485800300c0d100f550712924450711020440f4801b401d44880c0c0100c0003400742e40b81d01a103105050038218090800410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895417491 1250 895416241 895416251
    0x30e0a0f140706050f0906070219050405070804051011090a090203220c06051e071128140d081309061208030f1b0f121003052a0604180e01 61
    0xa0b003a0403005807205d19100354003055a0f044046c000402c240301c0c0303580096101007580d5482910000041003103042d50010b540800c00d40c0c40e800750a490540040f5001401540302c481040f403055020303007090005811079a400341c1030070134100006e4048552500305100c01a0f02008002e8583d09a4050b00da800030b03440380412003614540c991740304c006914040d030b904cc0000007a80c1d0300f030840044800d00d202200c61000588842e2986400100070640d280d0192090400d562100b00800b440d00e420810410100c8039044140c7c94150b000012403041a001030340075201440400201d003580300280451104400c0305404907042883c000211150b5400078075469040004070f50000e21a4000c0b2074004010300907843d40c580e54218000380303900b08064144620701d4041080d01080388210050040c026423010004540d5581c50b6030064a0081031101070600d600c80800c0c420552040c240b10241d0725800140340c1d29218607200401d40703c4c4d22580c8074000503940500540103820351481110200c108640091203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895418741 1250 895417491 895417499
    0x60f03060403110f12090103050604060b1b151e07050703090b09040e100b1302030606090402090111061302010807020c150a1803080306030c09040f08070201030e0a0f1407 75
    0xa51403000410040510102c01103100900c10b04120800510500404440b00b80401d001020080e401c0103d246001c20304203008a0400c0c0350034002d041c1610001d00c00241449503680c40071030405514021b8203641d01600c0d81200e90000a08000740c410700d000035800c10f0303003a2151142403240200030079010800005010000003c1d81c004103800440d1400415151100150310008009018000b003515040c862080290b0702f840e096004902460b0048030810705000001c0c0480040c0d2000321010755120004110880c850300d0130b640a00090041850070706110005203022a25019003502c3c0109521480d8180d02e00319a40545d203280d1210b5107202808101031600c02082c01c00c0c4d1049961400441d012600c82c0005115080f15203202c40c11403910490075030b4030f0a0641056200b51030040c020b000e1081030540c05d0600d8800d6601580e4082060030952946403901d440380c0e000700c40d00f281055101c0d407500700d04010070880003654601921041d1840f24944c1b410a1444c01211003171a0305070041e600c100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895419991 1250 895418741 895418743
    0xa0c0318030c03300504151407060c180e0604020706020403120804050d0e3d0801031a01030503030f13060504080a0908161e05150a02010b0d150b0103141509060f03 72
    0x9040343d48141c050030300c0c80ca407450143c0b0300c04501c230031102a1000c08035a000901c103458101c00b000b0f2050340c5508101704411101c00c100b40704240902d800302c81c40c000116407141820f60003811304070301401c0018280b903141c2d40c03602004012071110710005128501030105000b4280844403001c2c03020f0805030000c481040104566078124000b0070a07030503440f140c1e10320070b0021440741170846500c080a0a0503000c03a61024141540030f02058826070303a6420070540d0010300840d141e0581342c000c0011401c40e075500b01c2d80c1c025860018922403441d0301c440c4c08080000e480b40180d50140b84500030715078035404d100b64000d181d0b070540c4e0311070310399030b0f02038100002030511031032400050f25100e0712032141e4419040041c0b038008601d64486a0050301400a00c10402e042c68058042164640c0c0244003403100070b410400c400d461500d001c3e0050281d1161b61202140039803006024200c1810007007018450320004888010b01104c1c0321511200c81d44000340185080004075600400485211000e40c1005000c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895421241 1250 895419991 895419997
    0xf060509040f0f06060603062408010509040809090a061d150607061b08040210090b03150103090c0b13050916080603071503090c09020a0c0318030c033005 68
    0x1030105611441400b040c00200c041103000380e40c0080d410300c406035a840c00140140314078401d0321525058283c510070b16030f0078071801292213840b0b50744903041d990805003008100c40024204491302c40081100b107039962100d25049204001070040000c442c1d160241401852003108000e520260070001000702d40b120030110a4010740096032881c3c2c0351001c40c5080301c004c191084607181300d000c00714591003516504c04016841903100350350341c41c40c104003050148c03041c501e00d000c2c0c2b43e4030035000d000146110840a84c0c0740d104040525003c100e4500b0f03503c606140f40e0068000920311030001401c00544201e82020500800c03054030f03609190300c0e111256070320f00340808804c641048080c80102c3c41c280d5003080b401000d00449201801a0743c4481e601130000c288014080301d800701040b4002440ca201842a0703600034103140c89082c020135880d981110402030b0140085080c0c54880701c0400420011200c030809035108030010300c185940c18050580081d10401410306400880c40c16400e600d920000b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895422491 1250 895421241 895421243
    0xe03010e060a1d0105040501020301060e0607050d23131502070605120a0b121b040b01120504150914011b0507120311190f1e050903010b03010905100f06050904 70
    0x5403c0001c00d080b0700300300c1001d2910b080300398284402d10003030080c10350085049541c5030726060003c09100b001d101b8507000307218014003036400c5242c0a60485000362141e20648404051720072140b003c91708407400b40d4002c0c00d92280c00704280c0c1c60520a4a00710000d80c07001480e10b00040460518180d401051413042c112404411340c030100c04a03289080d070b500041da00c0c5030000c0580a442001c80100c50b0394588a200000c21355100790f0411466091910540c1d00884069440c100807101c0103c0381c0c030150a001c1d0040b1406420029441d0310585140b20700c02440388250040d683e041e640d14212400d4410710002032528012a405d2414a81d0300a0201c1c1e0700598412130300b44900c1c0703100e00240c008010070102402580000240032442c0f84606200fa10410f005440b40d80c0000100b502c100c5410443c03c101e00418003804070444c110364000d01c083d0510800080021420303a1080700400c0c2554003c0c0c800301c0d010380c015100000a9031160060034244c4101040c100146c0b0724100000f40c8214021384 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895423741 1250 895422491 895422511
    0x712051e1f050d0204060302060708030a0f0b0607080c0c040c050702090f102108130518040308220503040b1c09020d0201030c020313140a050429031e0d0e03010e06 72
    0x14402c3c085440304d8024000a40c0c0007001aa00c0d041c044c100100107902c01c441c6410040d140200b190021880e503c109200020050007490800085a403050b00e039030f0002008003200c0c07055800c21202e42d6030380e02813180d45c503015680b41c82c1c541d00e80f803040c400405405004141601c0000080060808001d941c56085490034803c481d100300c14100410840141000040e0664400142080081560040306401c03030f01e05884d010304121a510840300240003d640040015840c1404510b128165100815400c0700d910b035611181c071466514a451503205a20091001c500801c202c021303041010600b0035100c9410500340302340603030356001501c000c86880001f0705144da00c0b281545914802c100340d0302c3c1080030000b1081d110342c07030301c11804109010b00000f41c0300315580040030915080a000e0100c507440b0310100311000410400e00c1000d0403c403102d44a030140725010f20b5020b203804250142100e820381d02c1c050403948072811402000c3c00003082029009070b0406035400010200010403592024a0071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895424991 1250 895423741 895423759
    0x8071a0c15041a090604030909090b04020f0a080106090c030b010206070f0302030717070c1103120f032d01030c21060b031603050609160b0a080712051e1f05 69
    0x203d0301d10b40b004024070314129280780840402030a18000036103240a03500980350310b1101c1c2d664940e2a0195a003a280c02010b11704404003140060401e50801304951320010318018200d41c40d900100e00319491927101a0445d0340b0355101c0c10300d217609407103501a040402c0c80500b01919000901624045aa01811041550000c00903030354070710884d81c0d202141d4500500b0303200c608202070020a9400e000c901030b56140c0c003500b81003105142c001442107100400500382c50600508051025281d0402003081c054443c038421201d01801504612100c24042005045015411030400306000c0241790495200181e10742c95200c580c3e03c2c0241400005a84090080b803120021030101c2c3c2003040705241c03102c00755030503000441000b0b0045a01c0e40701c3c100714401c81303c2c556203c1100d5003105d4800d110304122980b041041c02c4036644940c60065006281741052140020604082e40c222241241d124444e1440001003104510741250000e410141c5d0b0303018401c45444051080314248170314402d46120342081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895426241 1250 895424991 895424993
    0x40311030606090417120c0a02060109020a120b060d09201509060705010605100c11030d0c080a0311030406060e1e0105010e030703020603040c1a18270108071a0c1504 73
    0x603004860104046c110303034580350708000c0706032419500700184460242c000e041c008a241200340c803c4c2c0b40e01400c0303681c0d104128441c41004000421050034559041903040040c1d03041030761503004a9002a01c1034030f00b1003603100504c150509218400e40054032565116020442503584942503030032000301102c242e540c400a83c0b030428010a207030703840107800200302c58840b0611500100a8400c8030300500807240505030b420201074403400c0d0f05182d04c010031a100e103c0d07004240c0000207000f2045d15030400194500c00031880400b2508202c900701c68032a10340d002404180c0800c0300c4640c006283d1580780300026255840c80d624a030050245d541001520031201100c0c2e40d04120134001541c01414156481c1041e040900351000f203402080201d0031036084c1000702000b034030100ca0303003072001c0700850305000c41900401c5140e43c0140c0c50f007440f074841d10712040c0c0201c0001c01682d0003021444001c1c0100c92510f410001180000c00c0c2c6800e5200782800301e00d86191011071204d00040201018170056621 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895427491 1250 895426241 895426283
    0x60504030b18010e01020d0b0f0306040b040c080625080601140a020c30060103170906041508010618031a04050f03040f0e180c1504080a05030403110306060904 70
    0x1c25040300e600f804c01c03244540b0340650060070ba10120940601c50040c0c0c1c04140610394400403034030754055106200040120b00b2910b0040c1c0c000c0d119910072092250b81d1001c0c14030345807060b641240500c0d0340320441220340e00340807602d4081046505045002c2e10346900080c0172103d9162410000400010703000104074428041c5c04220340004042d040725264008500103018003016516048400070380748010040c0f00040c906040781c0d4001c0d04504c8042070101040380e07a07046286c0c6690449400d02000c03036100c00c5c0864450160342e10341c0e2091010b6142c040c0090001a042005400f00c0780416410b0002c42c0b61400b0749403114400011050703c5481d03d14003d8507250282c005244103010104001c0342c10443c021819040f904070042d01e83c480d440e580320b403401810180d122414158060b42c4100040c2c00c00681c1c026241c0d8400301850b0610741e503181060f050046151084810390400034051003000020307444500740040540c01044d5070702d01f1402003000c0c10009403001d042c2441c0c0004240d10154 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895428741 1250 895427491 895427521
    0x6030b1c0302160e0a05071b1e0f0302030a181214120408060f0105030d1d0d0b0a14090a111306050d08190c05060601051b1b0118060504030b 62
    0x40004035210594030131080d00c000c0b109503030004a45080002103164203101d1400e100d032000c1001c003035040610065803009001a1500c5043d911083d0780450b101c0072440403568441414080c3d006150385840109008001e14440c515010754451001028030400d10b0041070001d015070321018404c0f080b503c072034105282188070b00c41100c0903140094003280c00c1d6000310781c05001d688480b4941d120369894908141d191704a09a0250009489080f0003101d400c2c5005401030044019107080c3c0010740342c0e140c4d40d407481c2048940f01c41454130380110b60080c4819402d1660300c0b40b0031030084c00840d00103598001c242c580c200b4619215080d0081c0202d4482103070340c45030008040c018a100d008000a2400c10031a8104c01d986032982100c402024405a009911140c0919030080280c4080d43d41e001c01900d00d0f4012111207101948141d120040908003003105590703003007030b074543c90381110030300780006100441c4018000c242d0003180350100900c4c0c0d0040140c0f020b69611400b1904680e0b41c048030705403098 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895429991 1250 895428741 895428763
    0x8090604050d050703030b0306100e0702010b150a03090b0a020a0f0c021e2b0221070e0c13230315150d1208010504110702010c1407120305120106030b1c0302 69
    0x8041ca00c248800807280070b10340b6040303c2f01e0b040040c01303035507901d24181c7c200d80d01000740d00e03007045005082d0b0389403c41c0400181500461810b0002d04510b540d01c1700c02b008030044a1414880743c0c001070314100da58010aa080540f0028078207002da01d8a5603010805842c40c1080c4600030100304250f18806540760000c1340410407207110140340315401c0c0311000600e01d04044060b4004d611441e100e0811003102c0003070f05207010b04040104a00c91070440002d000b64401003c5070900030080c40720015010380030b000d800081140c428541001c000c19000c0c0010f0b100c030300950f2880f95011a072100075503110f4a5005038400c00072003a844000d0443c9022600291003818000e0185075040340b0150080d40010702c140c180c03001903e0410101240c00d1010145204403400a8042810302100d000000c00e042c1000c2c0307502c590745060f41c0b4030355510340410810b007440d444210081440402d072108410303030461650740100280c7c80c0601103d040e22002c40c0c802c200e01e07103030607000003e10030011080c58000c02c4114244 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895431241 1250 895429991 895429993
    0x6060b0a0909051b19110f1501060801032001230c06070e01020a030f0c0606060513092304020a0f0b220501080606090a0e0108070302010207140901050d26090108090604050d050703030b03 82
    0x3034941e1007c46500c1f452942501d0010311440b10010828030701c01d1006030706880e80440f04030341446486c90900320f0391014150103810000340640900c42e80d8403a094011803480305051050301c1d01e044c00c001c01d08110000f811b40040040d801d94869a130380c2d00103200280c0d41d4160400e034103607000d038441c00c80e40c08100e6440038010b281010000503890b80e001c4000c06d58110400080108140c443c61050103075102e050846121060031135030202c0d000301c01c1001e0b5400a10040c104250710b40c0da035000800031150b940c480700b682540859081900740484071519803019002c0c1007548098285000681410701c00350100d40500c0b004958007903d501d40580c0040903202c968692817031981c0d61817400385d540030a80000c034010b014078180002e00d290180d4912150860040c081a101d81c207002c2804054020325005903400d00c0505070950031140451124984e1000000c88190b8500f101c0c0300251000740060040c450030b6010f4800c205c00308001003044030200c0054a80700c0d41c1d4101070700b012005401030244440d49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895432491 1250 895431241 895431253
    0x1d010c14070e0c07061506021b040216050102030609010b09030a060f0902120f0c030601030c05040b0d080d02130b0c15100503010e060610050f040b0706060b0a0909051b1911 76
    0x802d2011034044c10359a88900018404031240340200284880203108210141e4007002e00380307030440750054611342d800c5000352006007414186441002400b102e6242a038069600106018580c10301854090141549207a1540f61400d03a4011031360700c1b040d00b02c010384a10750b28031090300c820705260003594600e0b40044c1400150354600b8400381d25042c0b21384043c0441e12840301c40080500300800e0381412a030308044c45d80ca0183c0740501b070001926224032074ae5400740460820300001902480a08500c84240b031005072607035107803e11440b44c042281c000c0b0b1a40402402420781e1000001128402203182580d8020346490300010700025411580140b9070550034642e03044440800007a0841c82040215030100300c8440e0b01d001030362907206200f9030058040c0108000d0141040850060510074425400051480c0d80e815110540341c000f0180b100c000782e0070450402406003680034842d00407041c2c0b05040d000036655a806070642c0b00303102c03440a62449041250b24003501034079200300e9040c840c0050b030707807 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895433741 1250 895432491 895432501
    0x90405070e041e0b012a02151810050c0303070e130e0a05010c0c0209010e190c020c0a051e120c150c010f1b031d030a030b011d010c14070e 61
    0x8518401160302100070f44c9860b0010900b5846219003c0c80d58410380b216501007644061003258050075074000780e8101010034849404d00601074010320401e84595070800c0324001c00001c100c4e10500428815080000c140b006030082ca20100880c4d41001d501d061001c4400d8590010070b010030150403114004600e0003032001140c03600855000145846070b4001c00c9002c50303007d42654440082c08003e50424105801400050100c03007916070402c43c2441c0e008062080203000d507054613410050400160071401c1d1124881c103012082c1406070000b120108103601c1c03154000701070030310040e280520444414415072002c040030b0140d1000450050801140c85035040e80c04a401e43c04030600e45c0b12503103480640040c00c0d40c81e1045640c12040ea8507981c255842c8841c0441c00380010001c41000c1d40948031910280311400c10003080991507070f840101e1456113580000d090b80355a4901d44883d480c20300d1b0a46001d0703038040510811719510001d441c08019807280311901e03003610740c1c0107084840c0360501440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895434991 1250 895433741 895433771
    0xc090406150203040801050a0216170c0616020d020f10110909010303030b0a0e01030519030e04140702010e0309030a1214030a15080c0f090703140a0603030306080a08090405070e04 79
    0x100c01d45e20240d000303000c1da0715080d41c0b03041203101c0e02c812043c0c101c0302142c110001038400030010500684005440b03061041c501c00c40b604042d0161800c511210030009400d040e107805108200901c01d00b80040c15482d04c2e0602446d41340c0c5413030807a05140c83d0355900c00040c01c41c01c10080e5515080d005d40416a15a100c1c60301070000e01841c4a403904c1600c806e41d00003010300d4101c3e10746060300c2d40b107006007172120105066040d4035810039a04405000d001346404050351924814500c0d0405810000c0103941404100682101d090482105c0d0350b030410040e0032543e89001600b000801c0c1d0121003004a1440580100c0381550342e44800820400000184986003909410186090301c0d880300050500384d4543c1280c0e070711104660150f401a02c03040d0480010300d007015060b60302107580d04000c158501c00c0e00010510101c00c540c1402030030369034001030041c541c3c1880f42501400e500307401003a001c51241c0301e029090041c080c450b4401d42e21000010006840760001410084010704240180030b0083d01030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895436241 1250 895434991 895434997
    0x40509210c0610052b08090402070b1e07030b0a03020f120d08010609060f17041403040b030a0e0c1807031b0221031b0708071a010317070b0c090406150203 68
    0x91807254942d02100d0009078a0344031491113040625031282117000c00c998512074103030000b01c03106900c941d00b4801c5602241100389901d1250640c0c00194415201c070900c400c00c0c2950140c900030805242020303520998407036170f800c0c90640307804071642a001c2c0400c40020b00d250300303000c03643e01407030244400c84041c058201b445103042c0c0340161909550b0548401c0126038400c500748131729001604550b49100c85102264010303810074054a110880c00c18148103661543c0c3c41503010151502001003003041d01d005500c0340c0c03020380c40030706c014110601d0400001843c982200340c95800038040d500c0403800d0a0b0081c0e000c200214980c040212109584460294a95459078a2028a150140d2009005000042c11240300d10803118603411804501c0d100711406030800702085070010010402c41003c211821a04920004000000040b56065207031922401103208922441d58505000000000e1040f0902c10b0303009207405410380c0c85410403000070b4064040b0358000c41c0030080700840300c510180e0202c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895437491 1250 895436241 895436249
    0xd1e020a030c080705090408090607060f02041512050426070c121202070609150c020901260601080d03090f0b0c030a1a130509100204080318040509210c0610 69
    0x981c0c0c0d544d0342c1c400c00e000e2204170890b0010400002001199070a261030800b42105601640d0005155960069030404984c016084030501545451080c40e40b15404405517a1f100c0021005000354201341c0d9802c800441d05c58511800d1051388646c08410080040039201c0498200300102101036640b03e00044144101106441e0182440b6945035201e0001440b04100d81d681c1e6202c0c140c2d02d00c1c100300900c40c04a11480c0d9020840e240c103119016940e1241c40601038018401031118401c62101d45584501d03160310317040040d4220707d004110456010481d00742648090401040702d45891170140c1420240750740c020005002c480c1405420401d460107140b1901d0030300b4040001011031501d4142e4001d0040e10340e03900c00c001c0034451020042c0340d04243c1e00002440c00704d4a0100a170000d180603070304180c00c0291250b1000c41c110b0f5280003401000c2507444001e032000c00c05420201c0b00c013030312402d04040d40608201d0740041e2800d512020001c0f91080704000b400d50302c450030100c8400f032081c081d40c4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895438741 1250 895437491 895437493
    0x60f09330608070302090a030b060a030c0801050a1b1409120a050604050f01090b0a0903090f060e0301060906062c030318030d0f1d010905100f09090203060d1e020a030c08 75
    0xc005143c5501a108641403c1c8000b024110700d40d02d580d680a0545600a103295040350880600000151a010020024140900c00850307a07140003600501216001c00c03500c9400b458240e0301d00b02107134009469229441c801f0a906985020a9010a011200c0c050090503a0720403034104200b40140410102e005503c01d10940e1078900018102e9826505500d6028207222004e1000c185440219030054011074828104843c14aa9491212070640c0c2282d0004010070110101504103150078481d0101800c03060b1000c04c4554104038006160180a0481801c540b80c0b40c0d08200a42c000000780311401c090003001c07280d599010001030b202c0580806a00c501a11880410441280c050000300700300b28501d0b40c410351003c0307105100c5c0a141c030041480c40d05100000101140720784030303c03261301e032000e042d81c50721011440e0440005251040c640c0c03004080910520900030b03d40c8d100b918881001e5084000b4800c444041e40002c951a0840107009612041c500000810082d980540d802101d00f414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895439991 1250 895438741 895438757
    0x60f152a140715050705011803080103120f08010504022b0b030705040b030309091503060c0a1803050c0d1502040305070503150f061e130b1201060f093306 68
    0x21411580d0b0700d510301608070700a000d001c24680a81c8034902501c0300500071000412003c040182514686001c10005e40000340898014404d200c90441c2c845003150721480d04508560403400c1c0108290810b0217442d210741e40016a5940481491045000300006d000400e284201044180d20080540715901c5001c4c0c0107595001615281034401c40060540140c055490702d4450b800300302004074007c2440c00007124016043c40a40c904011082c81f400240c000c4030368921b095000603051a108070307110100c2041d038200600000d000804d01e80030010080d140c44924086500e8000482d000880c40d85030041d20200e0000140900010384604403103003a0151900f01c408815480300710402212660f030241284c0700442c41a0901c1003d410341901742000d82c640b440f0038000065102c030110760400c0c1901e500c1d420000d08502c2c00765007001c440b20600d0000c102d6549000c000900356903840c401c1c8500580d440e14454002402d8106d01d04001c401d8860f2200500006400906112030702d006180000e076041c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895441241 1250 895439991 895440023
    0x2f0102130803040302240d02030903031014010f0302030703060816060905030730020405160906020703210519050c10020301140f03100903020a02090604060f152a 71
    0x2104440070707250090300e1036211b1a04d00c100764049049404000c0c000102c1002130031801c10180c4040c0d4015407040014507500e0401520900070240c1d81d0300000701400702000d1101041e82c0010010740002c070142405070301c80e6070b4008164010701d40c5610a00282c098056040c0c1040105400e0600b0b8a0301038a444540039180e005041d034401842c09040c442c03002188d4a60142030310000c0c0b01c8042c4c59008280c407045041030340800d054400035180b505e41e401031010300386201074003c6003010181c043c85c4000c1c0081c52031130321101e484c0c010241280603c1046d011607845060f12174800c4440403024941c03980d11031401c20340003e05681c04003a8840c0d80340a0000012940120f5000700c904072212648034182d0075041100704466070b00350000e00e036850b00c079146201252440b80c1c0201c828050098018018203142c80c01030100c0c1010050a1911440c540001400005404861401602d000d111942d440254171003040c0c81c202e0160b10b0042c0e0300c0161001c07081c01101e0240b200039505100311410100f403860 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895442491 1250 895441241 895441243
    0xe0a08061b07080d140405010c050f0715090c030c06020d030b011d03161d011409130503040911270109060c03200105010602060c03070f2f01021308 65
    0x106480d00d020000560318101d000741803010103030120b5030054030001d180c004041010001c0b40d20303c007000c402c0290043d04000c00e0280a1040344540512810030300c3c6441c52010003194240710b81d00d0001e1402d940509184401407041d480300d500c50f60f100c3e10f480041903c3e0f003843c000701280d40c860300300144104070701c1d040b50522a002d140c51808040e10b07142580560141105a2001c041c1e18494041c4100580415404902d441450007009040e59603c0c0600c1070003460009000140c1102c421150424a4180c0a031101400103501c0005049070400d2103da514085003140f00d40c3c1d00a990784c45c00d0254000c1003595440c0100039612030000a4001c1c98448004655030382c3c0c10303040460219452074010000e40e402038144103003851007841c101028001b161180c01c00c1c0c441c045042100750b075562006118131901040101e030001141120a0f08502d461a001015905004c1481c805c10124100c481c04401c044000002005008800080011000c900041c000d4001e05560001d00703402c0f01c0c00188000c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895443741 1250 895442491 895442503
    0x4050109230604141005010605090f030312010308161a0f1303021f0216080c01110408100c360b120a020906070807032c06030a09140d0e0a08 62
    0x49a01c0140c02155203a843d050074106106090312620300400410721001c6a003403003803901908841d12042d4642642070203108100304c3d5220498002d07401000304030f095050246000f411250f0052105942d8501100543d007412900350b4014000c0e48940701540f030f136000340710050344181e0710800c44440e07a55a60680d103450310452680a030140c3c01c854040141c0e0151022020f800108000000d4601400f0314054110004038a00036104a10085541d00c2401400e010b03040850310031388550341c10241405030040d00c0780c0a2000071101103540d48520b0230114043d1029902043c1200444038040d40c0400d402c8011040c3d030811103040031040100822802c0c07061341070318400e010b0528245426aa1000d07010020350004d800d2541c402c006110a20019040710014a0034500c07946e102800404010700380801e51091440c00802044585404041d54480c00d065941c0300300401c5012807060303401d042c58140b8203501103618015001d8090000e01503074201001d04416101965400039007030faa0054507480e01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895444991 1250 895443741 895443803
    0x4091401050936011a030c03030409020a0306090608010506040606020d0e011b020603040503040e010f0e131115041403030c0a080c030f030a061d090706140f0304050109 74
    0x200e0420003143c5803616506084041000c004002042c540c400c55030b44010442c0f51100d014969140c45454100c00703d92421880c00c51016001045142a08400a80c0780d00446c0070740d106056010844400491090300048010080b100d01001620340f600700c154083c09080700c095020f40d09007280014050301c009480e00801c1c10a40da00581c2c0850900111880241020724499024812a011000d69554401540140e00c2000110354640c500080aa80220140d00080e000b03809941c00b0490741c02540643c41e84104444c0c3c40e080c0132042d0340f031300c070611098000290303400100040d900c8155411050040c815035441646120f501d402900803d43d40e4440c40381c000c00290440c100590020b00b0700c102500542c550401a40e0078000c400400509903003088505171015500e608040002c0b0308001d241151130550809014014640f00552a5640006100d440d08100c5081c071b0690f9010704039010744031142c03034104e0f0f42c55807401c0c10304155002c1c2000e04020ba540000381c1a949504040485500d80c401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895446241 1250 895444991 895444999
    0x6021911060906042121050f030702031606050603100b13090f060f050f01091401060503070c15060e10030b04111309030c12090b1b01110f0409140105 66
    0x440d40c00c10078008141c1003140102d4002400780000318010200c802c0407610403040c4034044541d40c0440c100f0b00d13650000d0b040d03a0700f00b5000340c0a105444c41c1e030110440360003004540d00d103950b80d29094030492a6200b80c6050a400b40d158083c0701003000240e800444c01920100e007241d8050b8100c03601d200480b901c03080b400b54040841c02c207012070014980c100448007030040c60031007800e40d00d90321404182c603130041203c0c151580c4d07401003004000304040d0150142080030020000009071004807280c100060007441d003404001302c00648224881c0380030500d42c5a00030707a11a0303100004040c0c500981028051803d5413006034000410348050700c04c09500701c4c2d41100c401441a1241d850358035030042c0c440d00058210700d4160701a0f060002500407020058484d54501040c0b521074280900c5030480c1c2e0618800300a0040e074104481d800300b40554a0038940350b0492903201c60003050983c01441d9201c03400000700c03008900400094525005082143d0806c00c0c2030221545d5411201c086000034040d031680 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895447491 1250 895446241 895446263
    0x6020d111c0201090b04050109060f02120403030504210909050c1303080304031e0f0e060a09030209090a050106120c0602030f16051501090c020c12072306070606060219 74
    0x20094440305071500c012800006080c8107642c03a141540c260803902640c0ba40c0d15030301c6080400c030301031140381c840f6a2444000c6042c04250300e0480840500604003804058a0f1300c04102030000e0508603103000d0403100fa40a50b003000112000c1e1400d44240300380c502c094542030010325400403040449000c0c0b0074a2980a02d440e0640e0350380c0707106400c0030f08150204400c0190303203211003020046100c80200340d511440f8411400d2040201004102802c0500490050140d0a145c0b40c01007400700c00d0b00d83c1110825030f5581d07261400d81c5000707100b0102400e29070030240b00156070100704542d00005030144010048003903e03140c1c16a5280f280c03141c0c20402c8001081443c910203e00903650712030ba407183c0d040e100d0780daa441c0c0e8040b090210a030450381900d030ba50240c0c141025010000e5000405080c2e030884c0b0f90007242050240c446440d80b040707015040914200300c48451101585081d40c140091402e038880c10303241402c0008054038001c10002d44208d09100040c0c92441d00c101c110341d03600800b9802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895448741 1250 895447491 895447513
    0x100504051b0318070b0a0e2403070e030a020607030f021c022d010f0f0b120d031d06100504050702010506031f06080a0b040c060c05032205120706020d11 67
    0x60f8801c03602c1140b00c80c0b40103070203011610980400c010000d418141c3d403032140740d014481c03c109041881e201c01d011400e28805071079004440600559600c55100c3c10a40700d101d8040e008207040c4843c2440007588003c0c0020408109900100640c03655a840e40c01c441c075a80f0320f00c82031070800007041c00301005680001c03001110712005040600191800d410083c4042d201c2080c1d0300c0c01c0d150310802d07040741d60b03498080c030100c121103a108080000804807800e02010505c0002c07a5100d00c2840b001a007010b840d10b214004902802c0f40c1c0503000e620310400c41b995860240c1c0f135001092403038005c90f0310907414100440d03200703441402414080c440c000e018081060741c41e07a201c449050722035854030384607890700c03070000302d054040c4100d0110130300039002c2c00960f10b42403410310b046002c0d94001005014043c61a500414000415281604c210120425003c102030001d81c100342c2040d40700c140c0c00a000c1400b16011907020a80c138017141d88075000c55880c07581e48030b01a43c0c00c070b000c01d002c1410355200540180c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895449991 1250 895448741 895448761
    0x50105221109061c121b08160305160501020901080601050322151103180303010e0408030a02090901120605010602070612111213150902091815100504051b03 69
    0xd41c10030002011141039080803410900880c56420017901c01c0d0a641551450b031640054085825400d440206504003001c0e540d805a42d000385100741c11405044126402018090310403100040500c0100c03400380007051800e40c0c040c0d448100c03210f00140a081c0882c206501500940740180c00f81c0701c04450040c0b0308040e0545180500205403041c0c50624a0748080806070b201d0305100c803170000540d0b503070392800c0c2d40900c2d274060b00c40308070072025402000100211011201000c1d0000c1d4403803420b9582c0d850f5007180344040c1c040c2e41c01565005811000000d1480d015403e11404103224440500444c1c1c0d0701c000580c1c44554500c00c1c000418209007402d80d090380036901c450303003940c0c502001c0f9003401c18040105101c41d5040300e080c607801801d8000e031018490050070760f1004103e0700c1010b11148045078049240d180016000c4100750180504e6962584002c1c0441008a0b009080200300c51074003d02d9026000064400e05028502c0c0c00042664101a80760310118283d03045035840c42e40c0c0b202020f0b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895451241 1250 895449991 895450009
    0x30303020702031e1501050303031e0a0b060f2203020f060703091e08070906050607030c030c0506240306040506040f02031501030b010f050108040c030210030204120501052211 77
    0x2282e00d4012200710100c41054919004204c40d0460003c01090703680760064020504107810662003680140204002e4411403030000140d0942e2600700305070b83c0c442481201c094080031150036804100030494a10fa40c40400107000c41c0424030604884004184030200408460f500020790083c0c00c4102c02d05140c10210020710403c0d20a15000c2c40a1f543c8481ea030340181070341d40b074080100303844600810420314100f10b00000391418048c10001076181c6000911580b081d10700c010140065842000103050103400380014540c1c210301901e00a04d4117500110a40f80c0c0785072221484600441ea603041c03800c00055040c4120b603c8002412151666116400c1ca8000794408030b038103120365800d0b82800c4201980c903070b008601c1440c00d414254101034004803864101d41049041140e13020400011441100c18001100e805680580a188442c04101d000c1c0c46107030802c01c42008600054020040150301c0f940c402c0c3d65107d4140c8148544802e2402030150382603003d44480c00d42084600c84d841c00d280c403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895452491 1250 895451241 895451243
    0xf100804032105010b0c0d0801120b0403050f0d0b03070902041a090f0307060f080a0903051903180f1406190510050907050706060501020705061b010b040216120801030b010303030207 80
    0x20200628020420010543d03900360081c0e1800e02011510744401c0500700510904260f05003880c0015604102007281d05400d8114090400007505000c682454020710844d02039400311301c2c4450383e41b09111405c10290080500320350091240301000250242e1920948040d2891900203c2d0700c001c00d040c0c0c0a03a184c000115440d446160449440401c2e60100300c0c2c40010016070300c85200c4580d1000300540100002008030520038100014103002940c00000c607510103c60141e400c4840c00c1710042100184100d5400040140d010984401804090427020390030030301c660a00c0c8248100040d015032074100983d01c4094242c900003940d040f28650b03400c01a0301104034a42c02c0c401070b40d10700000d00b9680056800001103880028550184003060250001a00080c00104009898140843c0c0c2a1180034601d040050181204082c000001c1d002280454002002551210907000320700301110b0465608036814250421040c20050007900d6a904a0b84c2046a540c240d0303107540c0b001d030302941c00108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895453741 1250 895452491 895452527
    0x207060e060f040303050c03070e062107051b03040f0303110a0606060c1509033e011e0b031203130b010308130b07080a0f050c03030a05060f10080403 66
    0x11050030100e5082150510403a842001c0168a042c2420060121500907100a100c40810420448925044041c1080303481c8156a581e65a121004160640c3c00880c0c00c1c200000e2482d50920a103250b008000d030021088d48400e00c07040381441c2c3d4005580f07100758882ca030040c1ca01901c0820210b801500b514100b04640410b592003030100e50783d00422204d094000101240584000f4024081e50502c0d6044000b01e52400304030f01d409949000d80006515004070403495592010702003601c400401d8a040d50b50980c5070f1a100a8544250a000c0c000f20310008400c0507403600d02e00d403807084a00810326004d0f8040d000e40078206980c080c9403902d910052402d1f29220150080301e000424000c0158001d600030040c4580743c40d250740b18500040c0040d800311704010713814426507000c144500308448841519044c401040511301d4030a4640780214000f1003c54000841001580400b54012609c9403104440003030039100d110003041004143d0040b40c1c4001240c10000030b000a0149003001d800c0803050b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895454991 1250 895453741 895453751
    0x30a1a04050a2109060201020304020922060221061008010e10170a0201020c041a041a0603040501320415060b0c010f050a0e12220312090911040603020706 68
    0x7403584000f60156404203e410070b9000c0d04001c142e0340c0700c0642c0f00605064802507140d418240c0000f454401d01400c3e117084114038103031815211070380130b0400a84a90100d4207644540b88046001c80c2500d4041d04842540c5079500003c01c07515110050001100031768603000c0069007046d02d4403244500c0100140600c1c911b4910200e00790982c18603c01c0240c01000041c4240d41840c400207042031017030140030740124208030040030b4078486e05034600202001038800150080c401c03006448088120403109811000001c10b000512106420507e1021941d01c410b007454040d031441d40c0644141001010703401d080075008540040d09010500a42e0302c030080300842ca50703856114002095210610300003d6170f54500b02c8181c0403989000d40b40e40030a21a00c03c0002c900e00000ca69224851101032006031580000d982c04d03c642d0480d00d1501803414510b07001003694992511202001440e04c018000c41c03100d0800144040f114000c41e180131110440d100d040c0307844c0c01416000b94004640858482d500c070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895456241 1250 895454991 895454993
    0x301030b060a0914100918080c011803120c0e01140903011401080d0801081b060c190b043f0903020909160b0906090616060e0d020c030a1a04050a 64
    0x203801050086600a240a960303810010b030a24805c0d44107500c00c080d8942040c00580c8050802000b5148090700700c40e05503501d03540030042d6070040007407080640d100948401e4490600d85d2100031941c00442c41481040100c2000100740d8141e01c0850b03420b1b00040c0714150700f26080c0c030f030368002d460803040140010881e81d41e001e4140800078000d800140302644506803a00340d066100000d1801020300901400115002d8040c4610010001c0300b0070703000700800075440c2891082006024018201012078020403421450720f42070b105015201a0b40c040e184000e00c0504021540202c1d40c015070140014803c903c2c0c200c11040344e03095101d9280305108080c0000000358543c2107010f445007601c84068031400a030103031640340c1214031350030054400301c05100ba130f4001d84400027100c919400855030103880381d0007449441d41c1140e0b008801001d55061419a2540450008880c3c804d1140e50f026100030380c5540d401e0680d6540c410402900030880009643c0242500032010b64029010300700355882c806807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895457491 1250 895456241 895456259
    0xb1605010c1e091401080405100203070c060b061309050703180c0303090e040305120a090f0302011a18010308070f1406040b0f0c27120309120a080301030b060a 70
    0x185034a002140c202c2e1010b00e02c800c010512a040d00c1c0d4942004a80303207082c6680410345480480d00c40341401810300220b020301c2800c110303403800c0c1c1040790415592450640c4004003118150001141c600707040c5083c041140c5040750644001640c001c4440c040c90340b074015100c2c05040301800758010305590380150701030030492094094803203001c3c114100d03500d0302c0c600d030040444c940350b403003800341410440074440065070010403281c414064050b11442c0761294044000140412100141404030800e0840708040d019040902545040030300c90340b0010410f41401a4204005a03035081d000c0984010300c00140650080e091460040110102141c0681d454100d1506032201080c1e0030342c0260100b1041105d40502d4075031060349070312840e0310390034043d6100c00c0c0c2d405401c0f0320010b1085690007009084440700210305071344030001d0100d16403464405115840c1e5001c00f01c01805140c2d000440c103820070300003c4d010b00c1c070340d8003e9196203168a16120809401c50242002d940004040d20026001da9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895458741 1250 895457491 895457501
    0x1606021009110a03110f060406080a0c0e300607050d02071502040f0e01080d0903230d0504050301060b04050607030c030504090f0b030c030d0206152d18040803010b160501 75
    0x200c9601d951318078550501c20010b40303007003183c0310301e1003104104403c0c00100d900550ac2508040f00034000314440047c2201540e800100107040394100081c500c40b0814030701d03129140310340301c200d0804c840060240d9054254580c5d000320b40c4400454010407001e00e00c12103030750040c9001402980903070450114003072182d0036a031065102ea0001c1c1900c0c4014002c0c00303003c5a4242c01000c4c06802000456054103000d0400540e510010380060b1089104207000c0c0420209540030b643d481b000c0c0c46843d8040c00e4040c015401c6400750318041d6107088004103409800701c0c01c86050b140c00400603820654959011658100c600c18102c04204052100065445e86ca0284000460420034081140084582414601000c40c1c03e020301c02d9100030000380700b0580119010b504a034113154214018810070b00032031090b052460015040f1540403d4125800c40401180310b00d00380110390329100d5541504640c4a00d07881a240600156010001081460064001015165041039481e07402c45840d407a0182154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895459991 1250 895458741 895458743
    0x50f060f040e0103110910051e1c0506150906210a12082d07030203060d0f0b060117010f061b140607081f03021011070b0c1606021009110a03 62
    0xc14000d0000300c86c1c503203841c0740d551044050000200c080d01d0000011024000c402130400400d0a0a516142d41d03221070300004101800240102c00300c800615109503518803c40708040d009100d4045818586400e1000e240a05001044500000d00340341c1c5404a1440c0550080c0051042c40810700019402411141d80c21000d81c5030f1920078500395400c540d52204544e1004494414406084140f9400c1c282c0303e90007004600d0010f80369515000820000b64800c400038208494484003001000303405010540304032001c1e0b8840544044402c450042c1c4442070042c50305442440c6c0060000b40d108804032600c82c2803912101e09810115100e81944c1c40419081c40d005400110401c0035480c0c01142c0ca9800c440c22000c1040c20450100402c0201142c50200a01c036800071a042c03141c192003100c0c203024000b1a0710130b403001d0680d10b04081d00780d07074401c040d1030712640610b003040c0f101c0d2048440d1000840da11a00900302004020060702c0017445660300448a51f6000c1e010223019407548840d10000d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 895461241 1250 895459991 895460003
    0xb040f030306090b060a08070e060d020306040606030c12051b0703050306010917070911090a060c051b1008040204110409020c070834320a050f060f040e0103 69
    0x21055418000e082e030360035811155455041c29900020340d100d280c1140c000540ca1714090704143ca030303042c04440d80d014510b103031a80030a0105044c0d072881c031305030300a5001e1f1000311010803020b96644010b03801d41e5482003400d008140c008246111241322070300910380c04441c1c024140b00f42029001882d006400c00306041e00092408420003420356003100000001d420138020140b00c000040130556a0740040c1d008111210791586003003503400a282c0103a03254010000c001c0c0700103030b480b101c001340320203c22601540e0314030495030402c0003039226003403003280300e00041c4c40141c00c05503144059401d000054002c86c0c1103507035240207510310910741d030140021b882c48500159886141c40001d1303141401c03680242e44681c2010b0348440d4000240318114251030001f5865020b58102c0b03601c80c45c40210982e01411641c100541203501c0007038058041c540e410048081351100c40394100c04d03c10902428055281c01101c2100c003012685003d40181c61050820480c25143c07907203d013031030240c0001c2a4003c41d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 895462491 1250 895461241 895461263
    0x1b18180105030f0705060a030e10090803060a06080405031e1b061801020324010504090f2c2e0905060906071b1b230306060301061a0c0106030b04 64
    0x1c2c07806002c0c2c0e604140e8498018000d080c00e040002e15540302c0d820380003040c190b0300c12400410140c20300c40001d4805410303500304030b40009810500240d0703200306d8205210742107030f050201d501409070500741d000c0c40d0440000c608000d180c01031543c40c0c80d44503d4a07030002c4018007680c109400c1c14000c0d0b21484100c28040c0030700d420010f12420744829a40700c46005030740148108020282071000407895080f00610000c1e02465000050743c45205036000070740b54604003444003a002020703070881007410810030614544060440541049904018806285a0083c0b201d21600c5289000d4018005c00300002140907807007182e40003400c881680300b041f034154010a00300701881809000307095100b1058200503140d2a514501203086d51082c007002050100381103c0c02c0001e1200305048400b0f0600d020310a1008450310138040c0000403000b810920038860340740001c0140c201800b6203011102c40040e40029920505203010894101c031080b002659070350396000000c64980031605000380e00800c80b0007d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 895463741 1250 895462491 895462499
    0x307020f0d0b13170a02062a040f1a0a2708160e10060212071518150b01020c150d091209060201180b0406060510050d0b091b181801 58
    0x3c0c2c3c030032842e407001081c442840105c1d5081c0c0c01103a081d41c070241d100c40d00e0040308081d19000e018170514a43d01801a030010a0100b00307800e5442c1c0000075039250105540d11002d1080207018507100d461502d00006480d0f2032010380d5240460382041030040c8050b03030000090349885000c1d02d40507503107825000d04900003000308000c500001880d50419844c2c0031659805041420181d95601c009149442c00324000a041c018014110781841c1d4500d603421003031082c1041e0314001031140954400c1940e4411110b11031050304c88140c0b05100c124981a00900240c444481c10015040b09500c0010368215007004184501d40140c819a000c480c440c03c20159201800e103401410941150040001d582c03601801c81007206522003c000304a500c540740e4031056440d0320b001e401509030381d88400d401044900703c034081c440d0018058070003228550030170019003115100b0000700e048140c0e00309500b0402180c0e2060503e40705002861308650b41e100c0460598001808290f4894003095031801261761140180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 895464991 1250 895463741 895463753
    0xe030418050108060c07080f161119060c0303060f0603050709080606011e020c040504050f0123070c080f03070e040b100f0e0d051e0105070906020307020f0d0b13 71
    0x640c2500c09000100302560414071810360b502030140418a5002002ca000c0c000c0101c1c1000b01d0b4200c074401d000140e100e0030080c0c1d000701480d0712070104668100d000000025942090903140300100301510082d08403034601f080a4854540d5120141c04040c2c44903030200301801c90b910b40c14020000d0740d0700001c0908e0200d800400d035007099004244160460320038002030740e90081c44910148421456010028100e00c801d034917010420100d2508241050200418040041521007000030008024451143c580d86400d0444c11603030803003a080f01044c0c2c081090607114143e0119940c1c49502d102d071030181070210581030742d042150b41c800014111072560b01207003064010402c450205580b288004031201a01802260b000098403081001c155044d1160369200c0340c800c4600e40d00042500c044845031309141c0d410706040685000305600b08000300d05e441d41700381aa4402c40f11658042e5003042410b81c00c20072461240407516521076115083c0401041440800030b024a115505210004580385004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 895466241 1250 895464991 895465019
    0x5151902030c0307020f220b0411090306130606081501031511090f0a050a030b0604050105010207061e03020906030c0a0e06160b040c030b041a1005060d0e0a05010e0304 74
    0x44011074005000d100c484a81c00000c1d6010b4550440c0c1901502d4030400c0031400e4000050448464480001e00e401c1411071a6403200090440540b003d001c0041c2500031603055100c9c1e00c40d81901540301e5000610706d03041081c180041c1e54402c80000c109990345003101450701c2407081c8100250700d1104010808c0000311413940000314078004c0240034213544107603404500d000300783c100c5004105501e5848141d6594101c054050400101050740942e103a08000307540c2c200464155000b03a00c1c0c040003140c2d0f50300004001c3c00301d403010703540c100e803a40d045103541140d4080441c180c424035800f4132002c8141d55a582c00703148541c0c2d015021680350b0190f103030001c00d140b20003240c2c07a000d0103042125444400380001540f03a0f043c5c100c2c0c5804019143c41c9400d11b1805115840a0112404c8600788401c000d20482ca58001803e1000d060505803075002c103010030440c480c880d483c0c1c00b0008000405020300303e5080382502a641c03400381d4081d00002e031903050a4811048010300242c000003024003015041c4452 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 895467491 1250 895466241 895466287
    0x61b07090c0e0f03210703180803042c04111e012a0501020d021c0e060601080a1418010c1103070308040206212d0402190515 55
    0x62101e50032011018106041036814280074910740c11403102161410010f441c5080301d1a4141c042e40100513040403210f0b048901c0882c0043c1514103841c00b240d00b2105807105484124019600d0a468910f00f607100d15000a0400904016200500c610b1a407409840780b045004105005a62440d0030400c01200b400081c541d980c2c02c4036540800e66640c0c400f1000d00714009918120030102804105162203003043e00c2c1c02001ea600010341c0c0034805007240c0141941204031040360300b42006040d400743c02e4800c40030010100d9801040010140e41c0715078110758010791001c100003805414405a00340c640700407907914510350384003104030b07007000310911480307520910340c1c03510315a00304000308925164412004040c04000340c2d08081010f41d540e680803900e280351414001190300380f84051382465003808690000300201c0b03114101e040505a0b8003000007951110804120f180d580307500700302594203c0b03c0f0509201d01c501c4400304194a07072104049805070031014903601c801c08140165405400402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 895468741 1250 895467491 895467509
    0x30e0102071709040e060108330406150308070b070228080703210e06060f0d2010030b03120c0a03110307060f090c0f050a0314010b061b07 61
    0x7244501050000c0030a0114544074114140d039810140c0002d00603006404911301c180c000e8200000720340400042101c040d0510308418002050000c644042d0f401d11342e48040041504140018001100c65000c24040030102940110158aa40700e40941c0e4025a004481c0700c6902401d01542d990100101e006090b04040d6100c42c031140700400c042c0094101d42d00500d541c00105140e005c06003d01e10030741c3d682452000030151890400c0682c3c0140c100003501d05018059480421a50305044001e15085007028105401c025425a64003800035000030300c140144000f81d03151030030b540c2d0b400c00b1007480200907540401c0340c00c2904101410040101b845614644080042e0080000d01140100040d030b05030520503d0f501450134030906510844000804141c40c200346405442650350100d0b5545001d48424031f44540c407040b4042031400ea601400b03602111840d000c0001550141c0844000f41d44500042080aa2400843c400c2e4004240c2c085040d0b81d10b500e44101e0f150700700420700c01021301c44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 895469991 1250 895468741 895468747
    0x60c0f0403060c2d1b0c0e39090d0c1a07050c04050106081f0308040e0106020f01060506160f020405040c06120203070c0f02180a0203010f06020703080306012d020d030e0102 76
    0x41d03015288003038020075540000c4617034580030184102000328000400f5480e180d00030500d0300c0400c1d89124070408a07043c6200d00807249040e100c001d100140821100c1c20207003170b46042c500c801042100490110115071030004110041600700c603080720705480a4207008102e40f55141d500d4413900740303044800882d0240e07240c400104032982c0c0c0724416940090070b0728564a9000c0c020100000701c0c08413500050310307103000001c00082812514140904990b5a6400d1f2444000c1c1da181640c02c0c0c03482c1e03115032580420b00388203000042040b4105030103114444c5078440102101540070806581044074282c2d20280d00f0502004619080b00c4000b10660741d4840441c6145084800a0200521404082c1002448078096021500e544500300d0b0079864640b00000c0c03524244541030302941c801d003c0e80d000c03c2005803001503040c0c00002c9040c02d0b0307640540400e0540c3e43d502c0c011110042c030002d403101e0f6140ca2000c22800f007014501000f0f05281c03658064045880b860b54050252000108102440d0b8810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 895471241 1250 895469991 895470077
    0x212100f0e07090b060405061b19060b0d0b0c0a021e07060809191104020909040c03020a120308010308130b070606030326280212091005040302060c0f0403060c 70
    0x2a17007214180e40d0b0407211b41340c98101960ba40007000001c3c2ca1a03541c0d0f8070a54100c50b00551008504200c2c1030720076135050105500da2410300c10107010516000300805902c001044259003044064644101c02e07204850364804480c5000d0b0262a201440710303800c0d04070280174840c1a901040c102d034811003070301c014080401401408800010040700140c5824024507094009694035011118030300320041102c04a81401c0c1040396920007103101c101c0c85506411800242e201e85455040c482e980c0540b500c80c05a1b196403a51302c0158440080724105281041c800304024203040043c1c400e55000d1100040c00c6400d43c0740c090064030709402200701c1c444c001c5101628044070000182d41c8001e4015140d244078801c000c0aa4183c0c42140210180c1400800d0000c0459050384840303218102d4142120051032280348080704480003a2000380c01a0820740001e005600c22000602180003080c950307524141e9070f521685e0848030030402610006980200002c20311242d80c0329012101c0759118038100c0c041c51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 895472491 1250 895471241 895471249
    0x10206070c02010207030b1920070807050a020603040321110406031a091819120c050316060204090507111f0b030d080402031501050109030212100f0e07090b 69
    0x300100204144481d00c507085900c00e2000500541d4003030413200842c1062040c0962505100c40001c241910744150317040c0300320109c2007942003580581c0025183c0342c1903407600186a0711806040d200d522981d0b0030303240107840d4040118411400303a620f484840c3c40703020507030034a20180c0240c0c000003401c11003047e50351000181242c044850500700060745100368140c848195034440905a0710012443c100030007582e5005041c0c070500505d81c29215020b04020083c16030768124031014001d5450101607550035801007a44900d85401902102c5c24101c03018040f50042401840854540c3d80100b010010b07090180a45130b008204c40c14640c1009852000460b0384484440010f140b510017103040464051070b0760f100c0504480d025040d41d000040c001d0003e07101200a0381c08078081c0c80b4030401c1000c62505440c02e54141c0710145c0d50030604501e5a020059042c3d00024618620301038440d07000c0c0e0440441c0300c6c080c020b6460810114019501c4e072021800c0c420300c1c0e0b00c44140542011040b12151b91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 895473741 1250 895472491 895472503
    0x801020c162103020c030a060b01020d090e15120f151503060a11040b0d09020307121110110d020a030f020102040e06040908040302060409020d051003050d11030915270102 75
    0x5075000d40c0b401c1250290408134a4a00d44001c025018010020100305102e25508140b15000003a004c44a003a42c81820468920555124072260f030141c1c20007164004071940e48500020b41c000781000b50300000440e2035420a0909541c4282c507611681040c10481003025500303500c00e4409000030001c60481002c01e4072288024010a00d040d55100241a00114030050350003410340f407051350f03846108210b070350001041091421f81c07082c4601440041c015000400e4101c060340e00010000c181c10113402031003c10702890390401c09018464086c001e40403000c10408100c9002c0358001e10000c125800c0103441310a0702401c502c21a40100b000717104c4401340c4548113400500c1958001803070ba040d400c14280398029a00000e51040340086d0008151045801925114150800400c003580701d070b80d09040c03803401d144401003883c0c01812070025424002c011203080f0390032100641e0b01e0079503400002554641c80680c03150300d80001041307906152142100e074046000148041c06c901e103040c840041e580305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 895474991 1250 895473741 895473779
    0x1080a05060120070e0903030118090201091d060103050601050c0712020d12020d020f011808180a091409162108132117070f05070801020c16 62
    0x80e00c400210304a40d02c074207411003200030880100c0c0103500301040c483e9204d029511030305c400f089480e008a0502000030080f681212544000054188210024040509a50402a418000d500034000380c42c030030980d240181d20306508407454a03450008009002c840014101d54100030040c03102141440d40040c403031083c1c80c0116650704803110b45100040c0b8a50b5041030081400c40c065021075222600000d8410100030360b81c09031580600c0c00c1c40c5090807540a204c4a40840684000d408041240000100b6143c10407054a014201c0c2d03050104210b4001e036808500c00641d2110b8245031400001c3c080c2e40c2107a05407014019003000c40064100b1182203025000342240c110804100c008810312510f144d1551081003240c440c4800c41414010500700e2044000c40c2849001080b00c80d400d003170f841a021603000c080d0005016030704600300c400d9000488100d0322410030603000c07404600b041181c200100f0000001598440140202c0c81c1040040304000c003907004010b40911059010403d102e142c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 895476241 1250 895474991 895475011
    0x414010b160501060915080706020303090304030b07031d0601051815270a090b060909070905090307050f1b090f0a181b0905010b0c1b03010e0d080609150108 69
    0x881d00c039040c01801402c19511101d0010b24040524040855007414082110f5114065485541c0d80d59000d80c0c480c4401c54040c0030f0f40e081000300b0301c00119a03205a40d0840c8003440c0002e061021860300700c030702c1c0072102008079035903008000401c100d01d041000d0022a9500181c1d000741c500300451054044028192503612031131100c8100c021600f91040c0c0c0e4001d000c5071030b14024590501e002c0071002014804010360300700346080d0016080d800e00100b40d9000d070101c2c000038040075140c500f19074018038001e404000e541c041001410081581009100b10303800366580a000854603035901c000d0b0041042d81490302a455080800c604045014580c41d803000d07545a0128041c0d480801f41e41e40b0f0b0250754001003100c1003888003103540d203003030241d03d0042d5403004108000e10390b210b00c885091401001014031803a4880c44a00c041c0b805841c0078030071503000180020807080266140e541c201200d0001401c0000c0c050410000c0e1440c04a582540080101c0c24030340041c001c03480028400b0710010044058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 895477491 1250 895476241 895476277
    0x703050a27120e0d080d09080d1a04090b0a0510120305040e010602150403230c060411120a0f0c0e28050f0a0207050a0605090a0c1715041b090b0414010b 67
    0x2042511f80141001e00e0744814450f5407480c1c00240320009090614a101200100f5401c00a1a040c05e1203020001034003c03940c01c40c035603540300d540001b5000092103204000d42c03013400000c0b08d40e00d410007103010314484c0d00c409440343e08101b01c0c0781d00904140d00200c1158070980b0b02800706802a642c80e40c2040c4c040c540b190342002001611644250300308030105040d040042e004940d40404036945014621401010b110902c5120800200a1000d42d540b00c040c0c00144480000850411544500300e10501d0758800f0796030358155a0907442c2e82100c1407901c1e10102e0308800748884810b944800d01183e01401001182011700b8941d0912000400c0055240d40c0092944140030302003058507016540207401744103034a409180503445002c80c1808440f02c0242107008034030103140d080b10741c00c0c80700740400400512107505009640d0f84400380060341c2e4004c45420f442c0810302c040e411040604406080810b11941d40c1c02480304460940e82e210311181f4032032006001c3e6415140850b0340525401102d0b046d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 895478741 1250 895477491 895477507
    0x112b0809030c100506030c0108160e01140c061023060c0c100302130801051b070f05060f0f090c0904080c010f06030c030507050307030b0703050a27120e0d08 69
    0x4914400c145100b40c9034421581201000030745070b008039105500540c19249450a618015110a6400d80704410b20b82100792010750042d10881c881c2880c80340515210740c0c21000700c1591580c0390300802d4400d203140c00400400c070340002030003d014005c0580c0d04102c07920285105201064220b44240d0511608000a01011312501000802030061008000102482d59080c02170000d61145030004940f0000720b9002508000600c50b00d441196124030185840c54074950852250348140021240c0e80c1c48400000c1c0803800803c1040d1090b08118188503003400e000400d441900801000c0007030507808081d01f4000b60b100c021180307400961000c526510b0360b020540b6107000d40503110740042810b02c0c001d000014418082c8031402200c1c01082a80c0070703e030f107401c2410380b181c200d0300016010156000c0420a8039209a1240781e2051480c10700291402d013000741c040030600548050301010091020902c103005800091190790002d074100091110112008901c01c1601c60394050b12282c03010901c0303d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 895479991 1250 895478741 895478743
    0x3151228020303031014040603152f0a2a17190203090424120203070302040c0302090906090108150c0f0c160b1204060b04060b0a112b0809 61
    0x4540c010b040e40e8807450000d0845141d4643d600c00c1948501608080340820b0a0034810101941e8006c1d95440700d41440c8001c00d4081c021444060500301e10b041551480b0124500120b00e00d20403040000380c0c0c842e070640e40109412134980c80c02c0200720704504520341da111010f01461009620191413500c400d101548800b1a02030b810000c1c0321070f0300d0364107001c4c0c1c140d078040000c1802c41002c50b8200112110f691299800030104465424660342d6071100f4040c159031507944854071031000381111180e588a80c01b10341035824490440d00401c0d0041018540c5243c4107002550203001603501181d0356142c0204942e81d904c0100c4619111030b408804541c403c1010412070340700410440c1c50036030b031b603520380c0125a4626a100080c91b124040e10008610f4251a204590040410402407451a1950f03110300f0010504041200c0e8407581d10740e00011811017541c00703081d40c5282500d40401e0800c500b5100c504000c40c0d0001e00c000003260755914450f00c0b00015680111406c6407412000703a0b680d1450603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 895481241 1250 895479991 895480063
    0x30414010e0106090b09090601060e090a020f0403080306040b042c0106080f0c15030603030405060a1e031b21021e07051b01030e250509010803031512 66
    0x3240d09500380640420400c0064010144c204016184441c642e130b5501fa9481c0c40700401e000e00c80010f000091200d20901c0d088581c0c82d00140048801881c09205551035862039009620864a401012007084298505813082d0102d01708141c42c28004d0300030402c86840c2942c00e074407000521160110350301008110035404a80039200e01c00464101100c403401c0c4039901d00040c40b003a1300c00c645040e00907844034013900070b0700e001f200080d0041d030405003400704112503038121140b20750412821742d6035050b54109a41550451f00c1a5450004403442d032030403500c001175401c182c1c05c0d042c00003803884035001c01d04c08070711000408626200107032145e1101c0010180000c050008141400b0041140c800344807004c0350390302d025021102030f54183c088000064042d00d031190740c0d190250f0402d11000d42c034501d0f070703d030150703603c14660400159490312500010f40680003038200710690392001c0100280081031030b444805a0303070100c403511500341701d15594a66410f4001000100310300a803062024000d01c070445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 895482491 1250 895481241 895481261
    0x31c150504051e162f031201030c080f120304020f030a06050601170103030c1704050307030c0306060b041a0a021f02071101050301050a03110f041b0212090603041401 73
    0x144000d080c040000e070401c1c11030469540d11001c1c420f0106415050134441d407400743c041500c914004c000002010984d203c0c2c0d007842408003a030000d040c40c2c00ca000500050103a6408014104070325410740c146442410007036003000f026070b80104c00310b0840c1d89002a845043c845c240505541d25912407010a100c0c108103810290140b10b006050000c0140d40d400042c81030700c0a0303079038400c1c1540c9044925042d1b0407e00c40034000c107400540355008241154443c107509030b9614012454035940740e02282c9804034640c000e0301c0c0e2803c500e205100704601406a04001d104001c071031402c190810044414010381015409080075001401521030750084c03240c0000040c1640e026210000340d418450086c1d80840b004542d071543c03a250310340c000d60044040d07070305840001d01803100007811030b503c0558201e42010015842085084540c0072951640a10840c800c03a0148100c1ca4400c010000303407074603040c401d022400c01010f00c58138034180c035220b0a490340a40c1010400042042d40e690241c010700e4000b41e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 895483741 1250 895482491 895482499
    0x1d0d140d150b03070305062d040905060c04030312050105030705120f01150e070825110307080406080a05040f0f02010c02210c03010b090a0c090806010f05040509031c1505 75
    0x14000030b95034008409076100f4100303528140966a80c07201000f00b41080c4034031050600d40208c2c1b148550b1901c10190a5504001620010390a80c03a6240c9600d040301c1251308171206003001070144105640402c8003800030f003000b60180115418903001980700c185c203008a5006540d2411035101302401048030440805212001f080750004186088003805002c1c010511038040710310215030510310400c2c24510848808104449802910074001c2a4024071030b62203080105d48160305105e0203045c030040200503c109141942c892030f1040152500c0c600812480010b0700d00410040418110070b810300d400741c1d0118078401032451501c01650032142517a400382d0800750344901c61901074521071018105140b01400c84154014113020107007a030b501110040d0304114401c010940e054182c0c1c002e600d4501d00c0341084449951514007161506100b41d010000700c0d00080c50402903402c0c944621078001402074081c610304801c00e09005040c40160034100780440c0e03102e4110380c4500740c0e243c5250291900030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 895484991 1250 895483741 895483781
    0x150f1f0b0a2c0f060f13031101050a0e0103050c0f04080f0c09090d030c0302040b160c090b130209040b0d052b170a0b0301090501020c010609020304170d1e1d0d140d 72
    0x241c04001206c2c1c607000440700c04041080c0085c0b82c0d80603109a40c8038400c03959585082e64860f5004501030103000d0000c030703c050424800700c0030241409025002800130600146600d000705000507190424401c80d5a0240402600380003040c8000b09003003001620505011441c04c441c030741c049001b4420ba074000c030803040c0b010410003208903801c0c421002c21405100b48080c02902c42c1c80b6002221420071001c0c1c1d0007024140b03820740040742c9401030003012400802c00034a40360744101159691400340c0086071103400c00b20407602001b25901c0860700000c0524807444218507190320107080195820b40058a8450803400101d001603507070495240220003070001d00404003d0b19080b4081c0d004114048515400d003000450700b100d00384240d070b00c00c4d40c1181c41580d4885000655454650011034466a02c545910303002003101301e18030700b44010181d0030b82d0000741400303160034108003818808040c40243c0c004c5521040190f501411010070401e0400849a40d039a8405540f0006c0400814001040e00700c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 895486241 1250 895484991 895485007
    0xb0708090a1403010608030c0a031b05011104081207080904020309010b030f010f0501050607050c06031515030708090a031224030602040e0702150f1f0b0a2c0f060f 72
    0x22000c0da08101c02680241701d02c2c1d803074500240d03e80c024503070400450340c000e58120012a104034100046242502e9812039081410340310713507086d17907a104100c0700d00c00c000050800070b4400c02c1010303400a490f01c0c0d284505180140c1c0c1d031815180310f03a214140c4520340210208014802c20750103020f10755030080c1200c03100a07072240114081c0c03100d40752519030781d46468000103450514404a84130340303921602926071140100c040101c1c540003c0d00b0b030324107480c1d045102c007003944034580385901c2402c1034180c3e1070b1030b854525001807420b00014600b241d0754110000100009801c40c0c04071074900e5503030f1300218100e4941c401c8a24030f0124145020880c00c1e0001c0c00200740401c40c2d0050050300e500e048010003550b10440160303626182d0b8002200c0c00126003001910b00e0f000c2d000001c0d005070449240340106007489001141c0100c00340c004006059001810783c085c0383c0c00255404081d04250100d8100e8400c3d01d000c2100042c2c210190b0b80101c0010f40d10210996806007210504800780c0c551031703215440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 895487491 1250 895486241 895486259
    0x303080a2a030b01031a0f061b0a051b0409030e0402030615030f04030e060301320301020a180504090c0e060402070f0b060f01210b0a0513140612070b0708090a 70
    0x2403801c07440c1c0840c1c50060010310300ba034080c02041b1000c40107080d80d56801c55842c2441801c1d0f10015501071519000c000c21164600c0a1007034101080c0501d00519031842c05101c1c110300c2001d58400580700380d10381411440000d0304900500c450242c2102c3c01038981d40d58101044600c0c0320700f103070090200800070421883d100701142c0d042c00f50740a0b07594954a1807605040c05030520003801028880c03000c1c0791012070718401041d8010130420aa80013410784c0d110f81c901103801e9170808007003500030039099064054140e03200d010800c001c0c03208450510200000e41c4a00b0000d52003805010615964200012070700e13180c1c0d804179400d440c0d211340380c01040e68460070200116402a00c2c068030500004800781120740c8940c9039025100d80c205464804600500ba601008001986050750080701200d00010540d0382c020704203440344128840858001c0d0001040700340c1c28030080c08280b140c0402254141840d00004011080c3e41d01c012405a90391401c0c00c0403401c0e030251403480e5030b1200c1116800316481c15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 895488741 1250 895487491 895487501
    0x314041d090615130209030c120102070303050601022109041812021908090904021504060e0415060e090a020405040507030608060702070e1513020a030504030f08010303080a2a03 78
    0x201039040d1160383c1c5843c1c0301a8420400440d007035a001d98458240752a03c80681e00400c1c007184002c00f1990410954070200304906d00ca900a105941d40c04a010024940c150103400d88c0300303500b40b024000492040078601c80900c3c420480544c0c843c1c000c14400130680f5254400041030220100407045e0001c00c2c58180b009203450510080140210102d98240000351040c0144e000d030312048403400d040010040c031880748030041c42a40d001c1c44039284018a64406002000541201c3d43c41800640300c460278082501c0a210f0440381850b8220f03020000d995110100001e240000c80f488034650f10f40c80e210760068000c6401c550b5015281005001899425610113411540c2501c190340240d0784954090740c960030701f4400c407086501d200340040c1400d1240212000d401b200240400c207401685000d0f4806c90308040c03a044040790307076841800300303041d001425030790120018a803510301356045a4000f0014007010b041c4100c46511201c1740d1102e98200c04401c110fa403003a4101c0d00310b6400c1013070000c002d40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 895489991 1250 895488741 895488751
    0x3052a0412120f26040218040b06040617060f070504081002070b0f040f060506060c011802030c120c010e220906060b2106011803030905010f17040314041d 68
    0x360780031444a8203d004110381c050380b0101c1c034030b440d00d4203000b819201c1135094014002c03a4880104a20f0b80c10028011071460b0003503003c0c21030703102c0c0c078034140f03007071004841b4150451502c50f0581c10044d1440c1c1d0000071a16442990140e00c2c404130b84800320706035020f0140e0707001050742d0f0040c2092410282c1c45607020344048d0340a400100036035103a40a0f20701c8102d0083d06c0140120910303154090100d171140d0021504904040c115070310f8501c45401b00c0382102c00c50f41c0180c100d40c2d8a13a005400790302e0100300380d0300144c00072101d0212840f5080040c0707685156040215041c840280701c5290150b60300d01d10305082c242114400140d141003a88514000c0c130b880b55007240d10618040c030115000c0004002d03106412810324045900d81c41c1c84149104040c0000c080c1d50410598080441d203950582ca007110055101e0f403260860746003060009410b19820542d12800c1121220a00c01108000707040b40350403070340508000c82240c0c50703801c42c8040b9102e55005080e00c030340711308902c03080d084240100501c18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 895491241 1250 895489991 895489997
    0x2a021e01050712110702040915060f03020f04050c040e042f0a060905010f05071b15030b2b140313180c0f1101020d050f0f0703052a041212 61
    0x90800c8000000403503820000c82c00d8290805d01000c001402c160b0302200c075160103140c5150100410140382c8060700c0307031900107200102c2502d00c00c2045081000c0b045400d480110340c144964030b00071807642d13502e000d1440f640320b41c1e40e044004a814041d80c240001400210300441217074602d01031900140c0404032048281c0642228900098280e104194150503680140d403200c504064480d0200c40f90342111000352010315581e4010300081d821180ea510040220031440d40c0040c640c09000703412a00b0781400613002d003540c900e21401c10b80c2010500002c21124010b03600d21080c0e1070600176001d220b90310712903100c0d00c40054691041040401c4000864004115200c3c10990540e0074806448501c800180803070950341c2880480c41c003540815419040c01000181015040324030b40064403001d41d102c0c20000006800d00c27854000c00c2d40c5066002e10141818046418456004030b0301c0040c0400e0007184041a1110154040c0e00008a900615072000710349256112824020a84201d8007600c00c08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 895492491 1250 895491241 895491257
    0x51b062208150924070f09170a050d0306120201080c0d050a06051005040305100c0c051507120b0a1a1e030907150207050402090a09140a0f2a021e010507 67
    0x116141395106404203459512082c1e0140c44a0209960070340300c00310114240542c00e100400c814625009040584443d01c0c000c00b05007005003442ea0408026045050802d41008014000f070030007041802c00c401d6081c60411040da46802d4042c00f01d006001c4c40705012030500d4140946420302d600540c05070b4100b10f17013440101c0307070010b41614244210300c0004c150303400002c425000802e23540c0c003030340e00b810480c2800312600205944550902e04c600013018240003070750082c0222694000c1c240b02c104042408104040500072000403040c000601c0b482d4141461000307103d031500346000a0360400384070101e540c4040e114881c1d1100c1c842d04115041040c1c1d02c1000e00c002a074a41c10149216045038680241054604100c10300000e544000700e0f4903003000c51000000303211040e40c840c00146012110402c0c110341400c18082c4141c0f1611003030598401c3c140034035050242c482035251030003801c6460403500d050241180503404c04d8075100c1d8004044a060f0303504c0c072a0b0340064003d5442130920781d8a00b10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 895493741 1250 895492491 895492513
    0x81305090601022803021f0f0b012111040503161701020a210624022e050603120f1201120c06031d030313051b0622081509 54
    0x80d440307080b910304442491130380c00460365016203401d80e0301c03940f4041e10646031407100842c620860344080e103800c0744286640d44000c5101c91900e04ca03250a01c030003460701c20190100840801d40203540020900d02095844d0082850450140101c400071b2501406a6000c1ca00300c0c1c61052614030f0303503c01c452070001c180701350041031801842103445840c11a100c10301200d41503114041d80c140101e0201640541c3d801010882e4012045c2ea40000100b002c1150b4090103403030307002802c0403e00071050020202d1806400d5000c0c0500758010748412070000c0004955545030b0000340b503c040502001080303000024185c60210f501c0b002010192846650b81d01540d90f2826441e040c3d0901f414060300f4007001d10f1080c044144241c20a480c2d090f510401501c02d0810a0740440c11540251003140030443c107a50031108021061000c4425841541c030303002044045980810098840d0300c52004800880200101081010b14804005072051000311900020714000881c0311a00c291041c4400344100c04000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 895494991 1250 895493741 895493743
    0x2a12090b040803090a020d12110a110f010905061225050a0503040305091009090e0102190309020a080a080405121c03020a2003030a05070203130501140708130509060102 74
    0x14501560181030a111561107445503149030308060310302c0180c0d0280b4034401c00940e03510a030a0007003c0c000c140e41c1c0a921400d1401070034081c2000802040f94205d0414000402c0c041880c45048000c00c1ea044000d1509200040f46d513444a9080a50b000300081000003414603640c01e8240b040104000e0b0510051a00c111303503a903140401980400150304000310034000b8400c0d4091070f080340c481c1c28076608040d08600000e0002c6004019600081c00e081e50400c134030301c418000e1104107582c0ba00214605454400030020480c0701212500a0540701e9030550110345900841500505090007034541103061031502d90210361140c443d4611a429210403400038800110701603103498144402c4420021880c0e4042d000b0b900801646c00a000c00d10601010900b4208641c01141c0e40ea070b00a181e40385000b4a00c5411618090320300c00440d4410721102054042da80310700030665000b420209180308248640b02400d10074281300412144020803000c6210351040c1d000e1040d5101105e5104040d55440012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 895496241 1250 895494991 895495001
    0x31006030605030a0809241c0b010c050c0906010c143a0c0203011104080604050f0f0619060f060e0a0e0721060306020c070801180f060e012a12 63
    0x391100a0400800300945484004900c8054034070540d104101c4070705101f160726800000d1034109003001d04009100c070500741e100b008045c1c842400c0c00090011a40c8480343d990745082a414068400d241c003107190b0740e00400300035286951100341ca01032645290310160300c03034442e440b01d41140b000c0849090408040b58030304018800309882c448818a0b000306085501240d1100c0076a01956243d2113600ca0303045000082000c1c1c141d110041c80203007003924005280c80700c2201c0100c81600054040340c40060041400c80d000015034842c030310310900100c0311800504213940041c4004858440004a640c0c2000300641f080324111a00c2256665400c02c0204011040300c0010004100084210a5401103480924003080740c03d00003d031180c4a5403101300320790081c0b600920980c0400d1007048141c0742401010b016401840c00700000548a41e074880f085552040010400b90312640405043c883c00d42c00241c0c080040050080c14070500c03030f2003060550600000000140500040880b080b209000d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 895497491 1250 895496241 895496243
    0x9060d1b090f1823070201150f0e01060c1a01060908010f050601021027060b0a12020d06021b060708070e0603160e060409020415030b0904030e0f060d02031006030605030a 75
    0xb50020b000300303c1007800141003d070300e803800248591101081c2203240c0403209100308060b17000065013811504101c43c040311030754044403041d01750b11000e20018010354401d41c1180e03c18200034004418a00d00a008040403806503806480709000018606910441510031528800c000300320350044a2518001d5900c11200300b405a070000e9865010301e00e2a900902c020108181b0118101c140c43c402c2182080040406442c404d80352440f40d0001d00d004001a0002e041e10320030f14208a0099000c14280060b100d8007402041c0d002c070700046024414450400c1002010041d2030061034030782c030702900300e90081d1952800241c4100c600e030780b00c1c01c000c0d089074058801380034800351a8000c51811212080c0c511a1150042420f100000750f013072213400500081d02040703074090300711602a4001001c03100e012a1a9205031604424000441d400407611071080e00240c0f4184001d1240788045541d5114100703a42c50802d20010822100c28820b0307555038181c03a065070301480035542d1901015035490381450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 895498741 1250 895497491 895497509
    0x2030610080709140111060a0b030f0a0c03030e130c020f01051f03081e0a050c0c040504031b060e1b0a120302030a050309160b0304060c03060f0b09060d1b090f 70
    0xc18130400e89000e100120010052401c1061803d01d903034554140700042e86c000341203e0f00c0740114031441ca0f0500c0b02d00400584270000304041d10b4591203844102c040c80c8809800c0c020503a086550645500c0d0303415000c00c01c3c1c240140002c12260200039915684202c41da980784d40307002c0203e03110300980c0d003040c04080f981007d41500103040d03417200b0401e40e001050700e5004000f030080c6201c0e0110b820018001c034030750b241c60740e545813003821901a08090342002d220703200740d10b80820000060b07001103075102c00b00100711005210401d03d2a0903002070190b0a00d001c4a44141c000b075410100c8035074150a5401819102d1406942d980c0131036610303030420407074010056042408054071840c403880c041c6500100081c1116040d04404101c6c603050082c0303030070041044d400041004103004c1117001d0840002035030315041003000c0c41e207850121007005900500b0303030b120070004045030a40d0f070b104295030000d1103024040010a007820340401ba00c401c0348010002180c3c04102c00144510b0b800050422100c0e000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895499991 1250 895498741 895498757
    0xc020a050a0f03021e0301060e0106030f0b060d09030c0618060e030f190c021305240a0936021e09072a080405032a0609011202070501020306100807 65
    0x4c0c0c204100b50700d240c3c00d41c20560405029804582d074003405070400420468141e102c065040c04070040a4940c49031241206c10b040c010765089035103d203012a1456076030b150000420121170f160031140102031346000b80900f0304201300c4662988403808022030851045408004803080c10302030949900a44002c400ba6240a2264005c09030303c0600ca01440c6405260000d801810703a400940428101c1d8405480942e850b410495416407040241036032801d400d6161038500030b103d000074021a43c50044005450701d50050240e105400c51440301101001c2c510300020610007082e65003006410346080c0e101c1c10703004001d03e944025a100c0c41c84e101d036025040066a0b500e80b203040d07030030701003032030602c4070800341e051050440c001c1d00804031003071602c207414081c0e445190108051401d2102c0000030307150341003001c17841c0702000c1155a004001d601510600e071036240080040c0da03100a00b810007507940b8000541071082040650085104141c2101d00b5240140e00860481c1d08003421136240d0041200c2c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 895501241 1250 895499991 895499993
    0x60c080d090213020301090911030c0d02010323040501140f040b04020613080a0c091505180604060b0a08190902060904050405101401030c17120a02031303030c020a050a0f03 76
    0x3503006a06858005400c80c00030340340c280e14640490340264000030b489982c40c0103860400600724000c01c96803500310000d00b4448840c000040d040e40c4c030399400034145661507507581d0303901c0404038140541c4164075841c1e24907860700c2d0a109000c2c04d10300007903454a0400000250701c640d000400b00740110b4100c3d040c85003a0b075441d401d01803113500014550010000c0300c5400a006101042100e0419100b8201c242d0310f646400c017240c0070741c1c0341a0004206111540801d00c11a03d0b8552010140f150421410000d600d0f003002040007441d40f07800074880c1d983e0000c1c0032588150000f840c1c9005601c0d10b02d154541340d040d2030300c2008854441c140290312500170041c9a000703190607080aa003060180050300c5400e40c5207400401115034650021a9000e280f41c010400d2020b001e0500c0000d051413441e80040c0c0300c011062540b540c0b09103210402c40c901c0030a60900c641e1080044d1000052040301d07007251941c99040c0a0441c50108004034401e8400c10f44c040f4090502c2104481110350300b4854001203819 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 895502491 1250 895501241 895501267
    0x31512080910031512020604050406030303020705010b060c030901260f1006050a0903030c170c0a021e060412031209150e0d020706050f0c1203040201180518060d140c0a060c08 77
    0x5262170907079221b682400701064641e1680705482c011482500c0042e569281c5140075800d5907221034503a40314190900c4041301c51075000c01201c3e8640001d00c3c08100d44001c9030040075003000501104044103180000700030280300b0107190240205002000302d02c0d0a41d41d540200c031144902c2c1c41f070030000b5a0805040000901038a408122540300381210708940580c1c2c1101c01c200d0301300d0158030090780e025192103000c2d4103109a8005517982c0000b0800c1c90624000c001c40c4441c41988500c4062405400d0b404043c14485c642d4490b4941b00e5000600a10302c4c00d007424060710301e1140c8403440103482d0000c004000000010b1503d0354100a030003800015180820a440c03075040305030307499500d900400048260035000e11581e0a2810228007440c1c903814240001807518440c03a222921a46820405100a5682d9442c8002e214600307005a600b80c0e0b00c12000c80c4402050100003043c800d2804000b0b280c2100204190100305000e03107103007089580d10201240d0107044000c000d07191a400b0445c41e103c00070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 895503597 1106 895502491 895502519
    0xf0304150c0504170c090c1e030705031b13030b060307082a0109080705041e0504050f060a110f031302060408032206020606010315120809100315 64
    0x1c60340401c0c0e10402c040d04a8061071008110128060502c15180460342c2398101c950345c42e41040704014002d60026114540c10310800e8003a082c80390308110a03155024003e00f1803034142c0b8034545555803804005800d00e5014016000085a60034040145070314140f030881c01c205070407030301500808101d408030703803102d0412070f010608008075400040e401098234400c90300001c2c5042986003080e4100041001000b4090400d000c00c03007072000100340e0341103401040059564550b039094542d021250aa041c10051560500843c240d054503580510b03400030000001c0000c940d280d0700054600e400660080c00700c0e0748001001d240014582c5600c6d10344405e1454101251400c03d20065202c1400400003810980d8070760340e04010b40b2058048400504548000306005400d9040c800602d511071085140502221000c58214a01c68410441200c05206589014a0810102040d0301d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 895323741 895503597 := by
  have h0 := BRFrame.cov_init 895323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 895323741 ≤ n) (h2 : n < 895503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
