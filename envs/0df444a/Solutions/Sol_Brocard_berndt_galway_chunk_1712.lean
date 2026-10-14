-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1712
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:03.719833+00:00
-- url     : https://prove2.me/submissions/ac6a5234-f9b8-410b-938f-ed16740b18b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307733812 ≤ n < 307913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307735062 1250 307733812 307733849
    0xa0302011b09140f130b0306010617070822050a17161b0902031303020601050a08030f0c0102040909051b042307020a02040f14011a0a0c0503040f 64
    0x80c2035400340c0407026452404100c10908640c0c0c040005800c1e030b01c0d401e084000c0e42400c280010454480907094640c499240c0300400911022a40300509455068043c5c41d110703079a40102b0340304484240d00700c0515042050004c1c0f160b612030300034107902c80188800c02080441d012110005015001c000715040d0b48850980c43c18000102248402011000640b51500c88a800b11800351404c103440142043d00007004c11090030300c1820038101800c2165811512803a0540c0f030b505414080c0c03c0c0c03c2d0054081d94001152600303224104105680452008500d803e405032501e413031680c00340c0d130070001655003840040383c203290902650021a00a0004002c8041c00c5c0c4d50003040380c140029203500c00e5107402d272100100844142221550300f25902040d5160f51a464186d08094042e00005d600c0751801c0c14810391307040d00c0e5002e00502062841e080740160f80312950396090762280c0c4d9500c140f0010a008645013140320b8035081616a110b44141c80c00c040c1e461002c045a00070b560803000d01c1402660241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307736312 1250 307735062 307735067
    0x5070b0f07050403021002121317061b0703090510021f0e07030f050309180a0e0f07030b130f23010b010c0305130806010f06081e071214090a03 63
    0x1600314100c00d1003114103007400c00019020b8411480020f000e4620360018001c0c850090101c40880790b11024440d07030310b000c082c25074004181c0d50b0041c8417500c00044201481e0680015203107200c0c0c0c104900c0ca000d41b2040200711032594020407400c0301013140c60180820b154903941e20b01915280d182d002040b420724000070f2440399501507545100b09501e44159200359150001e80b64040783c2c0c001d408225040c24030f090041c1103100b01c0c0402900f01900b2061000110081c1100340d10500d88410304001c1080c0c6581c010340c072441c04012000c5030754400c03241030000c107220440403034101112044020700b400700e907541c00700f001618a20989188a2080704080045840f840d208401001c10000304030030075840340042c0080c2c03c2610003808020001c1200507011385140104805481200112031040d80d440031408241c5c100e031701404000803220780108041d20003411140c0d441e900031000c00c032501e0b65a42003c41d203240e182c0c075080b008c4503103030a072480c0b0442c00880e04a000c2c0307003007201400380c075580ca040c00b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307737562 1250 307736312 307736333
    0xc0403150e012007060f060e1006081e0609070c0203060f090105101d0a020903030403140c010e0a0611030d020c150c042108040902030f0103140105150f0d120507 71
    0x11110f11100c0300c1005500000038001c4540207580040c002070806810994440182030310b070450b54000c4049400d004280400000c0b903411141c0c00e540e480e01d503680f9190105000380301c0d11400517040074800042601454201c1c0c150b64824440d1421160741406a0000382c900b00e020f41e88036003041d041c80248152000d0030f01880d90f01100840025030b580e0719140740480c00800038259600d041800e0030124103400030580485030224030003400c5076215074890508000b2600c0301580c2806911885181c0b403225405890060134542c80101121822403030060241c0301c000c036107050100300d404100404880022907101608400304180d006011b140c003030b82141540e10001a08420144809020820000b4940d01d01200f1440200007590003c080c907181c898072a02842c2c101d40c5203031f40084100880e910240501034100c81c020b0a940203502c2044210608a80040d24407410310030006003a0300f1107003420140300d0521540a00848082540d5440d1080303080005440340300058000203c407010f209400c8003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307738812 1250 307737562 307737581
    0xb09010c09060e130b2d030d0f05031504110a0f1409010e060c0604050c01080a09050a0201031e0501060504060e060414100908070b1c05060a09050c0403150e01 70
    0x41c0300000d1802d0441c05010342e059101ea1610a0241100c1c0c10080903250704960351118000c0d28001030f2981c10001d040c804000003104180740b26070b001c1005c00c2440c000030100181c5040740c50742c6403040501c40003128640c0c402052101c110400381544001c075241c9200d501d032003e881c0d24000c0d480314540d2900504075181c0c98881001c1140c000109400d040055048640f001024201303903600b13105201c0410b0290103068001080790003007500b000705012000c80c00122640c0260b031a0241c0b0760f110403001040724042c2c0c5002d86a036010701c405100650203940080003070024441c5c0d00e0718648a4031403003c19500240c01010011700041004c10019400910f03c0079080d00c200c4201e41060709010510488240d802c02461081031205180710580380940303440409800c1240507039001c1d58031074a01403540c3d400044102c01c00c03400c02111403881201c6114807030184500500003c1e0503481c0260038000342c80060720052450100700b100200058001c440c0101c84224041b010500703100048030715007190409507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307740062 1250 307738812 307738817
    0x17010b041409190c0e0310020a02120406120b0409050a1109060105090618060f07061530051c0206010509090102120a0f0207020d150e120f0c01020d02070b09010c 71
    0x405000c403c40459404098199412100156000001100b1685100c041c2042a018042c4050329240710f038207038004204040e816000c0741d1440141e601d0f182d006200d2031090750009000c0c4503201105400d10f40056410000003032000c06c0703401e00750702d44a0420780c00e5101110001c282000f49400b90a00c001e050354000000d09015081c83c488401041051040c084182301200303503c1112060f995403030701500c4842c9503100100392100c21a141110052031010780518904a0b03102c00081c010b0400b001184481800b031008180c298103012040e809007810010440b118020f51886040f20718a2a800384503440117580100015403501d000d010501501810b00e5281ea401040b8211040001c1100990000c5080900003444049544030701c00900640000a40c020f004002c240c0a020007013400020400515400300600400941900e035140d16042421400303400500210180545000203000541556030000d0328000b543e0b0402022684580012540321003d40300f88000c00c3c04c02d03c9124000e44150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307741312 1250 307740062 307740079
    0x60f08031b0f0a031214010f0924031b08010c03140a0c0c020603040317040609060c020a051f02120108070303020f010507050405060325020c040b0904110103020a17010b0414 76
    0x2c6103070949600f4016009010b2210021002d08860510b9201c00c00903051a0394003403840d6103910034849095824447c0d864500d0501031402c0082801c3d41007100840c400608400d0100d00d1507551086032a0412150303588060300410004000500380a800401151540e000805c0d000740728003e0895a0043c1c100070045140619401805800c030f04c4100754140c04a41c41500c03581c481c541120000044905c40180e90801410300040060907000440070303503c204810b0160015420003241d580414a1000d086680101da0034038400c200c1c42c103944480210040b000d40340407901c5c03000400c0d590342a400400310354842c0c030040041c103a050003900e01c0c0002410007803041703003040000103100e4010303409214860900040440c0050612003040000260700d11144542c084016030003940359a060602c0c1c5e030196080c000780c000c081c42c26065542c41590700c98503001490b800306004400a4208442100c203005071800640e040902a50000d4001d2040d180d5255841e0b081503000100f503003511600a0241c190b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307742562 1250 307741312 307741333
    0x2070b0316081f0902090a0501080f0a0e0f03070507030b0f070801050907030b0d0303090b0108030a0909050403180f05100813033204050a050109080a030e04060f08031b 74
    0x55100e882142001c0d00d03000d8299160300c0c03054081c00701001042070320340c0d80401001a03100c0c060f40150250000450300e0508140d51800190b8011500300c42803070010107031200003095011390303502124031105d001044480c01e40303c42c00a20b01e140d0240d00c05030b0b810b9006010405c10003d1180084d94062a04400600c060400740d401911062060180302d101d01e000c0000901c8592190340b000000200083c16040b1540503420083c00070003000c102502c1c440301000004c50001d00000032148020880d50b202c20741d45140c505010000d00000e4011010402c01d0044d40003881103906041d4058858250f04040161400e4100600000d5207140042841100e808004200061a80c12406030b90107041070b074082c1000040c05481020303020040309421010941c16100f440c98240034201ba6034007512804013407625000150760f074a60700d00c50b01215030f0243d0001c0b0000380c45412061482100500003040e85515270302d0007008011650854040c5510200d11158684114803e0310303013102d2800c01500880300b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307743812 1250 307742562 307742581
    0x60b040e0906072a030e090a0c030b0406062a0501020f03090f0109030e010f03060801050709060306080c0604120f050a030302090915061e04080f0f06150105090d0227060102070b03 79
    0x1203211021000700a440e031400c00e241c05106c1c01e02c0e02400081c010b03d004d203407400c004002040301d0040c200020b8501800075800d030606124180540c1c11030340b1840000041010ba40807111104008400840420b8402e000029004d00181501c00140709003230352a86030080c94545400180310b0402007682c100074800011076003010002e4044c208c01e207005c0e850500c000000303a002d000680e00207e0329601e0001009070300d5600004030402d50382199010320a860f03032030b0344480c0d440c008220b615502c0001000300f042200000001c3c4601c1d1403094100380c1c1c8000080c2c40d82400c0051890007540807a80000342822146041001070303a10099076070013106901b16080c081056802211701d0701d0029a8143d0210520100190603580188800b04c1114820f6604400c41a160003445004030040d20803400841c030b10b6540c405540f001064180c0d03030281003140d480c0030015040c0300c040040c1d0300a0070720b0507000160950146422034480301e1240201e1142000340c002803800c646035100d00c0c8048014401d1050521 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307745062 1250 307743812 307743857
    0x10020a020c0907030204120611160b011805010b0d0203130512120c0c0d0806030307140304091521030e0d0b06090c0c100f330f051f0201060b040e090607 67
    0x7504598000380440d00160f440c020342c8180404c2142b05121803800d001000945190709050f942e0721001212102100c9803c01e040d40c20a028a110f0310009008040700d668a070f03409550b120508400195950007292659418145001540880c12500082c0304c0205115809000d03001366403402510300d800c910822540e112003031203d800003081404ac010a0659804009442e841c0fa040380c1c1c12065501d51355004c40d07981d403040c0705202c111410070120300b82030085203039001d044484030141c2c5124a1210a1500d0003406030354801ca060200c5019110101d445000c861044c29200c0c1d00640c9031814404c0401203e400000d00c0e100d00860100080b40100c3c80c007103014181004107000203d4602c405c1d100e030300050a08150f42c030024900044400384044880c0180c0f00842c0c61001020a070316440e541114941040ca004440d0008040300440403440c030000d0000211810901c000030310b0300d44032081c201c461350190b401180d1299802c02032124080c428070030030b40c0140e19400d207606010804402a081f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307746312 1250 307745062 307745099
    0xa0b0f0d110903121e0301081b03011d0109210e060f2104030e0306040c0302120708030412030305090a0f0b07051903020705010b191710020a020c0907030204 69
    0x41e8071100c0c00200e62100a0940d4500c0c1070041c1030b15050100038030305896030f410004110400541a0a510740c0715480182220b05a0b43c504010f00010b01000e500f81c6c01800d04070420f150150759a0403510944054500c01c008a085804008220ba19450402500e100007038a24285d02ea00e02200116040c0d8000f803140a140c6001e6519945070b114082d000c0300b80e40180c0000c001400c003900d08002034103c00b0408288103512940b103282804a0710014150345280440f8000d115030329a45052015103440b6410108086140701168081501c9040032801c4d40c0041d40440d03614103005040104068144c01590790011400c0e0044c1180d42a50b04e8141c180c0f0b051003c043d0034202e054000c1014130344203004540189802145c0f40c0300020380070b40020000d500060003502e071035180c521401c0551030140e07000c80c040100d61403541c1109090140f02c040e0842c844e02c0c1041c40780325100d100b00040419002a14070080c482d0091f021007130072401230000b2014003c000b4010180b040209105045840505100c072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307747562 1250 307746312 307746337
    0x6050301061d04141f03050303060f2409010908120403110a030605010b030f16080703180516170f19020a05091501110102090603010e040c03020d030e0a0b0f 69
    0x60200e406040c19040031402c42c1d950010b0800c40320804c800101e95201d8011680c04044070a219400002c40c889864240801084c81e001040070030410329041c0b007041c07001d910040984a41c0d159050910f44500a5966140070105003c074100f1104e6803c181c140313009110a401520031001044298940c40c4282c2c040286a50034294002815407580c0c0c0300840690742c40740c400c210300c0d40c548040181c240c1080350344010000e40240010080c03402c1a1140200001d1525440d0762610303201030550203841128032506513004c150b54000702103402002f204158114100c01d840713449040c0170401101c1400da60741804103a0041c03550703100c207080000380c02d125442680b004451054661000074203d006551001d5489640f89042c4001c00001c4090b550800d4026281c20012580b000c3d0200d00313034086c1c1c03968140e03c044142300401c2a09a4a020300da4802e05c03c0712410b0509451b603000a0030760380307d88000d81c0042c1d981507101015040c04d9407280702a00301c1860403410805000520b094038810070009404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307748812 1250 307747562 307747577
    0x150606021e150108103b1212041412040b2104050309090106090b09040906090602071b0b04230109050307140a440709060503160605030106 61
    0x11003100c28000480b4450361410240c40e01d50b03481d0f100c80e0f5994102d052001c1400c0c5000190711100c40345120b0000c1d00c84094010380c4082016880044040392421507411007170052100c0c020b02d204e0040c00419804402421070300e0305003041d01303040c425914002e00c44101c5611150030040030189840a03030742214030b104003840c1d8401e940d2503421810340320880c00341d03010f400c03a4060004000000c0013415101c0703400e480380c2015a9803440300300c44070aa10b1042d448092010080c90301c207418503801800c0b526005040200e82c2103042c1d0381d40802c0380d12a0b074003941c00485107285851503200368906580104442d01409080a040c005a041220340c610762941c0d9204071500b200410364040c0c801c0c10010103004066a01060341c0d07401d06480741c01d200380400c0c0300b040c007920f0101e000c0108800010bc1c0050303030740c4500c898084040380d40340310f03644a0121f810581c00b00c81808135003a00801c01d400c0507108121000c200c2034a01303002d0502c0c042d1a1010216800c0c44410b040c0402070f409030a40381181c04074548000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307750062 1250 307748812 307748863
    0x40f0303090b0103290613020d0908030106080f090c031005091501060203042111060c120403080702011b1208060d06060807050a06230f0c06090a15060602 68
    0x10010803180200804000c2c128000100348402c1070880c2010b0340391911400d0400084213407098903000201c441691000d03100c03013100c26148290707000c2d00102180480000e004000e5840b03c1a05070000d074080c03000108614104010a0858035040b500304101d24000e01c0c100406000103600e5800154006140558940000d80350b4a41001005901c0010403840c1d00c840d40c4074003000703489074001e0080e031603802d4032000c145021181c01d50384e040e889500060031024190003501008060b52000003445540d04c200742e042998000901b0080c0011881010708a55480c080e20025003480e80d69201600c07043c0b041c100420105550aa0a4042000e07a1400c8001980c0300000208000980703200940821310b0b0190204110b00001156015200102c1d83c4500390342c1c2d50384044032031001c00c10140e05001ca020300c000c5680455100502004d009502d4a10304000301d8940301da28004080700d010700c441c4e0042c207480041c8140140039031080700917008180151424018007940d6541d16241d8249030ba05403400c0e07003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307751312 1250 307750062 307750067
    0xe0a081b04140702010506211507030e03041d1303080a0c0306080f030301050f0604080304090e01020d110a090605040b04062a1406010509040b13020406090c050a030e030909040f03 79
    0x1c80202c07000418401c19070610200080c001e2400720382090140c5005104441d071110078040002000e840c1400600388201524011100040c000d000d0a00345900d80301c1c207201e965030600c0644050f1600034042c621207c41c80058482c40c0801070000300350844000b00d4680401e0f0700c6010b440c2e001010080124040c200710100310010141c55106401078061599108240100440198101c1e1012148024200603002c10001c1078420f0f807155601d1603004010400505102c0d0704404c071500c0c0d42030300042c00c03c0748600b01e400a9544442c00c2140381103001840d6120581c0041012010701020b103840c6007403500388140c00308144218003448080c4180f03455800c4c941c3c9560300301c00c0120340300744480c00c01c1c7c1190303840d0100c1e107641d00c4410207025008810000c615070801401c00d80c4540d40200341504562110074194a16498000c0d043e604030781c8680021891035064001d40201c43e03c265201c0b0359450323031071100408aa4480700c0c10f103143d400c10051504c1d5907072030310842d40c1c10a42060b40040042030920b003d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307752562 1250 307751312 307751321
    0x201061d0c0a020c09010b2d300c121f060513120b09060a090803150112060f140409020a03080f0d09080405041b0c0b1305010501090c0e0a081b04 64
    0x4d54018280300012660a56640c064180341d006203180d03d040c80910102120a9445100b8444c0160010300c9400362003401140d444811002c0380c44404c40302d0000d034240d103080843c1260040c140010000d54000f04001c40c601c03c6a200c2c0240d01d6114003c920102d088013110020701c180300801002080e20500071207a03082e0301000b0120003618070f00700125850854201d210031240c950041c00f0740d02c001fa10914140c0140b5120980c4040061300c1c50303589200071040801c5d0354104078108035040100030402825442800042c1c84203119442641d46490300d407402422034501080e002d46e007003d00002c01600c45c00325400c10b883d4803003101070b25810800b2404a0600501d8100203d581c1014401c00c14003002900510640c2d40542c1e052001e200c080111031014a40d000b8001d002038100c40b025000304148681032604140e40482d070015040c6280c03219408e480d820f8000a07c1c40f6030300c0d801c11410076002581e2024404080e200311300114039007021151241010508028018105d1403848030701e81e2294031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307753812 1250 307752562 307752583
    0xb0307030201030e03090d0501060f0e0f040b07030207020907021c020a02033004030c031b031a07031d0606100c031d040f0e010903033602061b0604030201061d0c0a02 73
    0x18001408545c1d081c8980684018401c40102f04d14010300401d61284a80b0890f1189455480b4000147c680342d48071404030000400000425038203005010046e951036007020300410881d40102818180166083d5101609205407010355002d8011600140c40108071040040c2c1510744043c18010031402c04060020a1031b140c1c80c0000c40024007100b000100c0b14000c0940e8002c03100710090781d032841843c2074032a03041e0002034103500c1c1d810403105400342049600c90f44812a480c01044070301c0710300503550040021040c0640260001da00b0840c26040802c1003601d8004280b82c0141030601544001e400502c5580c00c100780c503501d03900700c4240c5446542007110008002c540400800c610024894024413602108074000787c1020302c40001840720380801c84c1c540b002c05008001075202c400e0409040400f105040b40c11280a0001141071080d11502d01c2c888813405c0058140c900d091718009084030542c0c0c001080c1c01c0134039402142800c00d060b0340540d0041011006542e16a007100c0d051303250501c20320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307755062 1250 307753812 307753819
    0x313140312070201050606090904060f02160215070201050919030203120307020f0705010f0f120203040f0201140301060c03050c0f01051018020f03130f06020a021605040b0307030201030e0309 84
    0x1506445a19001008041042400c180c00c1c00c1521400c00072400d80304c0039910b2a0380314000307004007403861600f210b103d900184144000034443c00e20741000300c1a6045102024004204e40e0314000940c140104500103044403840700c1d91800005d50b0010700b1a00900e0003607405102e9414000d208082c20001e45009140c004048031a843d143c00c0c85804a41d20880d108401800791001c0012299800a480710965505840b460035035020990111111101c0e5a0303131408200a00d0648500c0301042e1000b140500e0058055502c2c0d82210b0002614040c0544110030042d101007004000e2141d004172406100c81d85031422a9458170411191460400400501c8105500c3c5c10144984013140b404400121440c3c02400401100c102054008900401c91500c01c203203401c00018100444500c648214940300380100300c81030030562942c404a800a11041000d43d100083c0c0058290800039080014901250103008048103407002ca45c56444501c00241456260290545c1144082c03065850f8540040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307756312 1250 307755062 307755083
    0x90b0102071a071109040b0f070c0c08060a0b0604030f080f07060c1d01020a11040216051501030c09090515091c0203070c090212070f0905180603060114010e01050313 73
    0x780d5407040c02d40c480b100841382848075003016041c80c2440c8040c2d9105a03048850074003655200e81d1852a00380000b0400c00c100702c00e99202d04002103c00c0e02201c06400b00d40001c120929040e00000100d030180d4064520038102448100f0028080c403100382c0da0070703910108035a03d41d100b42c0c220116900603810028480c40c2440000050150721000d5107041c00c2d080ba4540b0691003c04005a80b40c24600c00090006d080740b0583c560b01e401d040c0c00800640810000c8900c500d403a50316100d041800105107002c14007007400c01002880b03400143c1c400500021035081107100780682d185070391146a51055100e0f070701c400000520301d10051100c40d002e03050310302060340541c0005500075181d5200d07081c00c83c0d40001c0444041404070b120310a803120100316602c1078400740c44410090fa84440c83d20045001c00060980c086181c1d00c3d80b21720b00c0c81012030094500214101042014100351058000381d58041d026034140140d680d0190f0041c024030800e09019940351560420b0109452461801500c4018403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307757562 1250 307756312 307756349
    0x406060f08072c180d031b030b0307051908060703110a0c031107090608280b0a060f1401030b15041404020409050403080702070609150305190f0b01170f01090b010207 73
    0x682e01380360300c2c1c12132441c103170307408154030100540481d18981d0750782c00441e8045035285461402580000000e4100504881d00342d0341e00d500203048814102c4144e0040150030750200102d510400400760826501c0c1400d000c40c16a22006504c0d60240b05d119100b00003400304908141400f941481d40f919210b50207466461703899200381e03400703042c0754030960a0601c0f4020f0900942c040d04941c181d61281010a909840c50054441101c2003202800990425517912000900b03540c0d041d19110041000c0d0400041e0f200e2848005411604208942402800c041a1000d0164045800c0b141a200c140c000d4030500c0201c01c0c0803030b0090080c0d030841c0342c00350310701400d01c0245030f040742c1d8092254038070b5421a4000303600e030882124a04803d102e55200300c00c41400c0400210300941241b80d00100700098504003106410300c0b14146c940030549a0304543d925551040704d56400140000714000c0001880840e00300b140040304800814814260031a03610300207139840d80c1c8240842001451440c055420102c0c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307758812 1250 307757562 307757581
    0x80901050d0e1f09081b1515090903120c0a09030c0905010314070609050d11030109140f010e030904090302010209150d0605090f061905060a080406060f08072c 70
    0x151107110008000c458903c0300d40c3c3c003000d8014581c60300c0e4800900f9090000d0403541c44280300140d00350b01c9039401074280f290032041007400300510403402c043c03480081c071084c801800301c0c0c030b0f00c054001811a041001085c01c030112800130243c02080742010240c0d10464108200c0c0c1112260b040100a02c4000d40002490000c81c1c00c000e051b04d000e00110070440596034000e0755141d000740300390400300302c0c41c0508000307500d4002040c0c007045020b45c602088007c0f56074002400c459000700101c4a1455450248010030001c05c9840c0c24036200b03a00070800c102c0b450000590303e0280c074511500c2039803244410400c06100b034050b075001504c00303014080940c0c03110f0304e0f280341900616504288030789403440025035854603040c050b0091807082c010500e42e440365014000b8070352034402800c42c000504840040d83c3d4403030400078403d41d042c0303654004c140d0509140a00039601c0c1c03035000e14070105011600380b2250b040464802c086504c0e01f81100150710030b00d0070000c1c204202801091a25230390a0401c0711502 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307760062 1250 307758812 307758823
    0xf010c0503090f0c0a14041503080c060f0114211219020607050a030b1504080307030801090c140d14010b1206090f011a0d02030403022104050d080901050d0e 69
    0x31200b0050302c0000c501c0000d0b05607190758114100d03078031190080003081825000340b41000060b9014001045005280000504441c40f40d4401c64645800003440c06101506102294118929414100d09545071900303c54242c5d80554916105020030658488407070b2070b103e05012444002c0701a0303446440c07a00600c10254200c10300614480b20308014941c1751300c3c03002c0781903407144050317442c0c41e03081c411401c10032401028595070030364211107040d00301000040c440028000a015030001035690b20000d01c0c00600f8443c0680c46004454181101850000e81100000c44402c04460709135807540300d905122340103050b007005421180440d410012650301044002000c1c0c00c0407048000c5604e84401c000c9c4488904219901015062001d00511160030b40004107c0600d0a540790182401e0002c0380000c12640140c8003200275a10408441c02d0441460070244144a0040281e90a180c0341c400803c603868490103000380105000101003034140c1c015002d403000d92002071420040c0100fa00344040e40c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307761312 1250 307760062 307760071
    0x100f14090105070908060106051603050c010e0606040f0203130b060109170a0201200703171309060e0105090c070b101d011a041206022511040b010c11090402030f010c0503 75
    0x4d0041a8013180031540002e0460407148159655440c1880740d0440850546106008504002d001c01c07e031400480240a00362070540c501001c1c002c242070040c2000201c40050320071645250060080200b020780c04840c4030300e9541c2007140e10b400b5560750001254644499040946810950030241007064000908015034910070380700c108030303085404030072028840410540305507544043e6044c00040c1e0046405150305c05007040003400e1140e000c0304180c1082c4190083e10319941c0d80c21081280d803407101303007180c010201034550500600303010340011814402c0c044054820302c03602c800301d40c0f05041a05c190004059000d010441d45070f003602005021603080c481c40d002c0010f9000c041041c49055801c550446281c001344c8100d50a1503a076900107500810032420300259003080f0003070420b000541143c5020720031002e000541603c4c4003004201c03412907410754100009800aa800945c0803404003052080850300045140d82c1e6100213071400008242d0307043c095007041844c2102c00c2d00030b00514000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307762562 1250 307761312 307761317
    0xa030512130b0a0b2e0e13060902031e010e041407090504081c06122301020a0c033018080c03130509160f050405041406090703050603100f1409010507 66
    0x603542c1c40b48105c0242d642d81e07164120348a07102085a0110746c040c81620b00c5040018200c2c0003180d10201000b000c444180d0305c104100c0f600041080a0840658091000200c2d03100c0e92481550400240c00500c43c00100002c00b034060681c49025043c5041040f10000c1c9044042400a85454a4081090381042c1403507100c281c40494501c1c5006664080d24041d03900700740303c3c0c1414500689441c1d0100019201c428030820201103201034600c0f083c00200703580ba14588914589100d2842e00a00c4c444072030003c4080c280c3d03540d8241040c100b1194201040e5802020b02090340010f01018004030420b07820020302c0344d400000c0c1c410714401c02001504207042d141c1d4420715415510002d00402c46000c40d00e00801100c06600d509245028084011075451245451814152140c020804032511216483c02d180c00c0601044010f240c544e202c0c5030301010518040c0410306055010960301d9409200412009455000c06100f07005540e0041d4a504c0c2006000728890130506605c0c0e00a0005036202c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307763812 1250 307762562 307762579
    0x10090506191707080c09011101090308010608010803030105090403141c200301030f06091e03020a15090203070504050a1401030809151c0b1203030a0c0e01020a030512130b0a0b 77
    0x1844512200b8851080f0002e454000c0160342d11308a524580d44601411414090421750381620740c0401d11840014500c40e885a81c02075041a074041c0841a0580c0500a19801000103000c40e468211890b0740059050801010301e10106200c8180ca00440300300c4501d0000da040a040400c0643e00940d100002154049000001d950441c1495210034003024190752040c4012000051807940040c024500900700c001040c02000042c02e030f2484040c005600503480001c0c980280241e500300c2e0440d00b000c0d0b000810207003d00d9404640ca034191441024861583d4038002844002d0390703000343e00d501203800d403d0f000a40c1c4034500140143c01644190340070b103885c0110080380c030303003003d01321860b1100200510126019000041d006084c6041d41150003030080d48100080c11000c0001e50300480c03940c4404188100324242c02003945200d401c0309030441d03000d005d02001003a0030904690300c0c003130400001c0d10160780716604240211f000b0480200320741d51440800901907a2940f00720760040d070880e040da2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307765062 1250 307763812 307763837
    0xc210720011b0f090b0c0115060f030506010309120807020106090c09090b010516080f07080714010c1b03030203060d0f1202060601050909010b070312020a1d040c0e1009050619 77
    0x101d064503070100c0300c008a05813a1040c010b03100c281010b0844170022800100e0800124400c030203004a842c0e0081c40410041c2002c00f0400c2e405001e41c0e54811028681008401055281c0c0f604c269207940a23039040c860a40e01060755a031007904010b0142520110612102038000c00041526116200d40703c0400e140c540b07440115132007101140c86101c1480344003400e80c04940c40e4180b19a0000d40e0500c0d0380d140401c40c2c3c100141c18000600403240c0552100290740010a800c5421744120746005010840703001c9654200d070708055150020282c1500d40143c070b03a962480801d000e03005140018014241d10140c200410405044200150409500f618002c1e1514801501c441c0160503072141c0c4806484014001d0400c00009001014044d24201c400511100407000407a400791080b04001403912030402d0280310440c8040d240240241e404001c004079a1300028501044800c3d110701c144215600120320f035104494802c007030310000b05501da07100d0540c0c3c04800414604000304000c1341e000012030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307766312 1250 307765062 307765067
    0x6130212060c0901051326010b09070f030c02010e03070c06170603033115020c0306040213050c0403080309070906090b011e050409020711090c210720011b 68
    0x641c021110b20203450708141c5990015103040e0020b14072071035018065032001a24620003000b000d0100d8a0301140041202800e10240c29a154550b900303008061501c18001490b900c009420541c0205181c0080c4000c0709000481c0500b0340080c1e4880c1038400819000e007809101891502103032032588540460354901c0c2401510444200c843c00e0f03168006224141c088611007030030700f00c0250004074a00302c801100c68a2581d1200a400482c0f46401d06100c081b140b079010096504a00c1d0210001d0400d890540c2c002820310b400c45c0d189012076520307035002c5a0382d40c2c50030080c0d42c00b540c1d001e1203542e228600100c0040c2e842885200c1d001d41c03103041800001e080c419901c2081d04490040c3c1d500c0124070484460004c40c00c200d580b441040040c20000000c40000c28400780103c2441030790004a0300c0702d08402c022213020040c007015070420080102d041c02e117110250720081c1c4600500f0406940d91a40030030307510014140b9402d404500d601601d90380c0d000c41980540c207134686840389901d116003800402c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307767562 1250 307766312 307766323
    0x5030d02030403060c120507020109030806030a1e020f03300f031b13030303020d060605040b1b16080a0b0702030c0c040906091712160801031209030506130212 70
    0x249005608100403e2001c01c0054105030380060850500340400114072262104072101103400d2030050359220044010140d00120054000b00c048005040d684800d80714403a180711240c41e040d0700200d04a0811045482d20340740009a0b450040643c0c10070b0b000c500c12100746d10184c1c1e10101503640003150f04544a074207d41a0f075403003a00080341c581142e9070402241e003400110034008001000a00c00c02800b859400c02c01c030055842540e01584604100641805440007a0495400d200f0284003d000b940c0b001e00c01d8461980911100c0e0f041603040c002c115080c2500522440a90900070700c0202d01c14000091594950340304010780c468640d504402240c0300d00441e40503104503040751510700c2e11303854550405140c150180c000058441c4030f03542c80348008a08408084100711000c6428400d0341841a012903010080d0400c030000e070901309400801240707050200400c03ca078600880021103104115034806198840200c0308582045e102040c688038068900324410075600c1c410303c8511002044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307768812 1250 307767562 307767583
    0xc080d0207060e04090606030803010801020a0e03120702061305060409052706060d03020c030d090e0112080906071a091e071211030f0706080105040605030102070b0403140c120a090503 81
    0x443c000403e000400b080301908440c0400d8a015031510342c0400410800700085009002050006958816503200a0000050001894803a1708400041007110101104960100390b0403500c1340d0b80e403c00928141d82e00038840e0000c075003000d80410302040030212030b88020f004040104400c003503d1030f10003400d010481450714140c80c139000440401c00c0d508000c0003403e0340501c00c1c01035034841c0000d003000c28900f00580368600006003451108010004006881c5805840000c03090404c1055030340301c01c10280b04040301280181000111a003d000218100ca0702d2081c0010484c04130741008500540c1c2c0d400e040300c80605011065000c402101d00c0010100c0480c0e640900d140e085105070388070b90902c2e2248000840d058050014040e440180174400180074110507180c26546506080034001281d085401c401c0c060780c410060310740440d1907000c0e6a070f8041d51610300314882c0e03034024a4903003881c050204188001e01c507272201603802c003441c030020300100d81a5580c0d005106650380c080542d00c0a0600b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307770062 1250 307768812 307768817
    0x303051201081f0e030d020f040f0509010305030712030204180504020301060501030e0703020f0105130608190e0c090406060902161e1e060605100507060e0606010e041808070c080d020706 82
    0x740e040c42030745103039003100c4c00440d1440240c9040829060a55061342c0c030410701031400c804002400e2100d104241c0301d081c0030340002c1d81d06403c00e41c119960141e4912803071030041e11281c10341c00840c44052080c1c040350042d0000300440c0f0303d501e0032214200050902610124403d500300040424a54400d2160030701414540f0300600703191380f0b0341e000d00c400c41d20110b01c02ca040020400004240c4503201708840c00030003c581e00e42c800c030b00d040000300342a4102c800540c4481070400c01d80c0d80c0036060006050840b10000c413040300c40d0f9241c9240180c001c04031540300c0501d4134008900d1407541200205a0641240030b041d84070b951204081910010440c001001048401030800000803070400f62074405029100c1d96001030745a48a00c00030300c0001d0240038080009030b0004a401c108002c0d03015540c40b010700d62000304014103041c000a00203201c01445580599507820f0814001c01c1c5035842c050030307107411a0380350360740700e08604007040480780500814010b4440c40380340401040c03002506e40100c2c1d14a5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307771312 1250 307770062 307770103
    0x150c030709050d0c0902190f020d0c120905041b1b02011b030e0a0906050f180606070312060905040512041503022b020901180e010501050c03040906030305120108 71
    0x3403c0000004403408156488060448081078842a80c4010042d20002c201c440b00d80b4001004000e110364483d0740d01008542003948030f10107090b00500303c01809548034582c40c04105050070104c1c0c060890303a0202da03210b801d2001c1c10b404d0881110b180c008203500d81d40c40748001c0e100d5400724a07084106400090000b5070082c0721061200e991103141514034468130300b04a0078081807001a2034410107400c00b40d4007a55501c0100036901e40018095040305041e51841125015600c55010041c0000d201601918001464034201489808000c9800000740b40800100c1d4541480100070101110101c415101d042101c0c2180d0f0001d0081d03034121900340100211900360440118069002000c0980401960a550212800411004000c00d1b60f1501006813503c2020b000142038000005600a07031a00400081c060310900c2c08985040d5602030030141e41e80c03208034102034179601c0f941e13009403007092800001004160f84000100514880c0c7e80d00c4400310303603c49050b95200d80c00d81541001c82540d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307772562 1250 307771312 307771319
    0xa020106060c1a09070306110301090606031b0806030f15011406040b0d1d01180c120506010e06031905070603050106080609060f0a180e070e011505090a0b0a02150c030709 75
    0x2d0f100d000760702c4204101503a0240d5130380d68a000540705e00310745100c01e00c0e5001c4014000004a4880c040c02042c0515040c0800084203c0550007030104d0200c4104000a0070002100398038108030101400c966041110120036060484404e50380081c01040071310240c0070400f895600c0d103081034605032814681041d00c0c0c00c030702c0050352005120320500f101d81c0e98408107403070303841400c28410000c0500b280c80306c6406180303283c0381a2102c8407191b003140c1e40e203400d2200e250020400014406054515200844a0700d4840d04e002902e04030103000400288200315001d007041250100d2315104445950314144003d903250b4505541c126000c0710019008442c2c00005181e070b14044000c1ca981c2c5002a0142c1d034a691982c2104420000e52961100102e0319001c11040300d0ba01044043c004010381d13900001c0a5040034100a1103640c0300034094100301c070201e100841c580d140c980035002840a0146035540760100c3c1b4019403207142100c004d036441000302002600c43c4000c407003109d1040341181c1c2c0d161040d605 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307773812 1250 307772562 307772603
    0x50f07050318070509040b07120e0d0e04020d0501060f0e0a0e0403051c050a09171204080d0b03010204060806040e01050106020c060c0715020c030f07051f0c0f03050a020106060c 78
    0x480c0100010a100303c500010b00341d11204030003030040d40104010030b80d078600f08801600740042c0349805004a45400d4281030352000105100030351400368501410426604000180a400b800c113100d40201c0c0780c60000034650360011841c0005041a03118001004800d200701f08190526206120341d440300140000c0c0040e2007480240172603649100044401c0040901750320448108442176206950b68180400901203840140c40310f403400d241c1c906e1718100c00720311100710f5120081d0004210031000b0500d4010084a1380001404100107002151542c0da13460b80281900806d8401500880c0751150300040581e043c0070b0f25050316550340080920f610030320144031069104460b5030720345000d80b860104000c186586001d41c208007690041c90580120002c02d030400c08813880c11440b85e442803004008030703102c0400c410300c1c4a500100d6004805120801510030700a00c4500401680d500c54007001099000340141030400c01940c0204101900c41900307540300b0044050150484000b50285000d001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307775062 1250 307773812 307773841
    0x5150a0f110d0c0f0c0e0601020f0105090d03050402060c060a020315191502100603080705070803040f06051b190507050402041802071e150b0607030e010e0f22050f070503 75
    0x4d11608001010a400307803980f41d0442040e07041001042102c20030b1015943e8100030020110f21740100800c11401d001d003010f41d42c1e1034102408400d15844030001015580e5010945510000342c0068840c1c510b00f41540c00000c1d881219948a0719152400124490400c40036108420300b00280d15241b107824808a508200c0300650940c0452252491103203540e285406008015889425500d440304030074981242403580c2d5410442c070b2940306020030083c0400b41614681107640e41d0820036a81da046224114541059050349142803160030903c070003202c0300b0b42c500d40005005505450030740f0f0702c0300c007000f0691140e446074228100712103a031221107900c1035000f084258441c4804a507141c4a00210014404c005072090341c0d40450102c030782a5076200c0e401005207100d004c80b0000e241440e1550301407c41c1c01c0b10070780c0e60b0401c000062030200302c3e02c920596070181c04004141d5010b50361203081e189a000100034480900b03904240c003080c0c00c3c22500000500418aa40b2020300707582c2c0b80d580c80207140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307776312 1250 307775062 307775087
    0xb0a060f021005150d0c080c010c0c06050307120216030306050418080306030313081c090f09021309050a06030302012012092404050c0901080714030705150a0f110d 72
    0x40403a524800d12985c07040071524556209440c0240d690f8584003a0034240030340007c906040c000460341e8000040c1c3c024460f80e0039070b0700c14203000761282c0310342c2011a010408100b108012520000c2c0711180c0034010881820011b109a80c244101c40c0c844080c4405ea490410380e0040e52086140180001100c2801441e80004081c04590030b0140c183e111488030032840d808145583c02c03412655486c12190383c505d4891003064109000058a424131008002a10707105107400141d01180f01040c11004d003031044018181c0c103400384078038145503824000505003840104c0256107085120005d2441110401d00c2c2c2d00250030200303040051170108504003c00081076500740c0c0c000d000505185007403d01e108061500d54102c0c50045141c9480c000e40f41c00024030340144aa00160010400300900182410a54418400c16070800380341201003450204650041c5501c00074405c1401d40001c0c1c1e0030054603c501d407d03a16048004204902540d41c0904d0004451107904034200b0322041350302403039145441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307777562 1250 307776312 307776331
    0xe03031b0c010f0b1305010501020c09060418050c010f02071a0c0a060c03060e2211010e182719170304050d0201060602030903030306101e030b0a060f021005 69
    0x10721070391000c980e003160a40d5124401250743c41100c04c0843c20b051620f0700305c0a2001d141041a541132200103135581d14a416407600c41c0b243d00c00043c03150f880c0d9811019a40f2100c885c528003c40191070659198249244c0c4140040d1994402d201110302c001004400c0340e81c8036804121200d1181e4494086a104181c0702110380320743c0000100054451240f4015040c0c540e40c0090000e08010811082d800090681e003010854980725502c148dd45051402d10b0952144148140c40d41440c01600c3d081d150200f8030f81d102c405c2d55805074804007010340d82c6100350380d414041315503206c1e003541040407540742c0c9040a8075984500c8001c045003a41c25880380035203000303c140405030464661320281c1e43d84211070455043d0030540c0d0768580c841e024003805000c4c0050f07001440c1410200c1e004250360f40070041c0802c2c410104c9005100c0e42501030403060008a800544144004101da40c01401404c50030420314002c02241d040001c0f001c0c403411100c01300070f90380c3d8090840c95006c9200c0300003500002d0083d211 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307778812 1250 307777562 307777567
    0x10513020a12170f07030f0e090f0907050d0311061b0f0f090603070e130506061c0f0227010504060914010e100905011206031a07030239010e03031b 65
    0x403510b246000e049045619002d107584e6500f6407030018a1f95146200303078800e00c03444800c845034650741e010010340d01c050a00000c01e0326564a5600c145085c00b140d010f9a0050213484d0880103150340080782c000d40c1c02c0d203c03040b294541c4510240500130b00307400e0200009a14140302169202c8041d20090142035503002c011030a11130410005401540140c0e101000b25005d1416100e00d801c0841000c420104904001c1001d460044003182d48d510500c941704c255501c0e01e0800840004140d44a111507881e0307038400715140d60728a008010100304884c01c007104e044c444024070146610440448007038680950394032001c140b500b100f000c0e03c0c60b4003419580c1400041c00c100742440c0c507454890072208503103a85a402c40c0b8074120015003c916080202c2c0c02550134a5030038000710312000365414800c05c004c0c1d0039840555807080d00300c0c000e00030081e8008514202c680030a1100400c1143c40706000485448128512000c1100508076004201c001c2d1668005000107800b00254855410f80e90b840d9014132031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307780062 1250 307778812 307778843
    0x28050715090605160816050d150333020309100504050c032e051e070c0c1409180706030b0a0e09070f050102030705060109090303060801020d0509010513020a12 70
    0x5031601151201c1d0340362a41c4d046104001d0780810581d41000031815000311809a080008105100c0c00700041300498440d0803040c0b0b640b1007039050500550300041d801421411141003521892520380c1c0307105000150405000c4001030600c2264080d40452004105403012814040c01400c0028816151806001031346c04003614184410321210090000803c01250b4002c80104001c62100f03003800168030780010840c03d090341c9500311940440d403e070b444600d60b580c0c070011610034039141e90080c2424070a120000d20540d08107003030302c0d40391340840d02040d040e5140e03480700403080c0044003500800c0d0b022090404c0500c3c025480b023041c05501a1200d500300e0344414000070101419a4002c20302d9116110400405845242e2003000e02401d2000c0c1d072034a442612086d54801041c06180350707481e519003030001050b000e6400b0600a01d5024029034031042c0c00b801e4a40201021182d44050b5401c240010f0035402c080031044003829801882d00c900d2600300701c8068100703203460100f01d84e0b000064000c1c3c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307781312 1250 307780062 307780073
    0xa05030622110d031701090e06010528060201140a0c120506040b0d05060906060315150d060906090c05010e030d050706020f04030f12050a1220030a022805071509 71
    0x3d614180c042d4840c02ea908100c010f0800c800784050380034100188c0340a810030040c120218459044503400c036005120b00000519900240c4108418841d50805440d40060003580642003107240311038015005030396581d01c40c0000107491307101400d1030005024010300304501c001c5a019a40103800a8000107900c402c0e0b8002c200b01070484002134403140d002c40100070460380304010281d841601034000e081c007010f030720101004012015250000c1408a003105441c10b0b00c0300c1c07020088060300940d05000d9603000d410000024050640d080d2400e80b18000301288a50140d2542c00c1c070800043c004042d121142c203c120740503002400c00329525a000c02c1000c0d040890780c400361010b5409542210541582d0380740200912101c1400c1c0814080140300c2d140c0f209800030303017003204054402d03c0841d01100c0248a51070034000c2042440c000074020007070064921320f0b0743c0038000e2617001045010301c1990802e02002100b120140030000074000b0007280c1f001980c0c18910410f02810302202081042403580d03034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307782562 1250 307781312 307781329
    0x309050301050a1d0307020f1309021c0b280e031216020f01050f0411030a05010c0806040f0612060c140a0f0f0507170307020a080f0403020a0503062211 67
    0x14103d101d80750411000c2c000818080e40c04044009001141741800c2a0b001c11030341010036454512500040c03e040003018915004200200e0340200072107902c4000d03e1089960510500c01602c000000d0b43c0000d0191241300e10701c2250300107040d440c3d00c802408030394050250060261035040c9020510072000781005001550780149204600c4c501008101880289041054207441c0d81580c140014030401c100d0003c02c0e550056007015004100600d1140031070301e404c4200c0d0740200158a411800442c140c0e01500711402001c044405011a0005600090907130311203005443d00c0910b1080c1081c00900741c0e502950988181d403c02a5000740d41d0800e02196400118140001c9500101440f08035940215920300c0a407060038607900780080307520391030403802d03084211261081000000c184035a0007000302810f5154800012640c83c03044803102c40164015200403401411000c40c042000d14020907460300c40c40e0921039005000101d02c503841c1a20240d00001d4961400fa41911020f85e103441c0318 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307783812 1250 307782562 307782571
    0x506030c160602040824010b1b0d0305070f140d02090a150507050118080a360806060102120a18090204151103040503070612020c06191b0912030905030105 68
    0x40e15145010303e6203050401414403900e2151614080d808209502560303e41510302c0c040108c2e484403d5210305d5a00700c620081d81083c24032801c4c001c0d8007042e80c036402162240c0c005035a00c80c180c01c6138160690300703002c0c0902094002032060008110f2280c0300d6018108500f40203041500d4175980f84980b058140f0264410000140c0c001747d43c40501209000c0e880103031981d0070148204407103030349501b1618011080640108411030311008001000907540011012080041440f100c0d400502c115900e60b103840342e000340d030041c440000ca0640c004544604203000300881c0314a0101c2a400403540c2840783c444031000724095010100e610380480c800350010702141c0c804d100440d060750001901ca1440c1051103200f5600410061000c0e44010598508452680c01c2c60700b031285034205404003a01a01180022038031a2034204115204807051150842904802c1000341c0848040039034011110741c000e0a01140b08400d082004034980c020740020301e4082d140c4a600251914006401e458050302c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307785062 1250 307783812 307783823
    0x1401050d15031505010b03060f09090109020406090b01030506060a080402090c0c340303020304050409020f1002010203040210030b030a030503090f060a020a0906090807061808010509061509060a0506030c16 90
    0x4003e90358601184036090241014020003810361031b00400081080462009090044140d82e000c94030b58002504221040b5900800611803181c89500c120001d28100d03008600080c1844007144803800c00c0c1044598010150740c402503580c0c0d40c0d8082c099410f0001e00325902c100800c02040d58003030000c0c82090603815181c4030281506107803440d168010100d1401e00851600303400d5041002a400008440865a00f41c0703000c81c01c5001400021160008000e8240d042459280441d04440c0d040d030095114502c21203441d420400101d9048049030030881e00b240d00356026603905008240104080c50303000000204403840303000100525400c0403002c2d911096650340206035200e806070000b40c40c00141005113440c0c20b04c145048143c50781c0c1c0485100d0441882510b00d1605a42400302c505c0c0c01c0a0041000213000c1d0b0305020a03015030300d150489400380c0b100c40c036801008107403800c0e690440c0245030051049007158100410003801c0d61015006541c100001c021140c3c00c0d50b41011403098090040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307786312 1250 307785062 307785083
    0x8070302070315061502031204200310090209010e01030b060405060d1b050909010c021c050f0c0d080a050412080702030c190b07110316030311072603011401050d1503 73
    0x81448070205c07480d00300e810341d00180580c0340e203e102900c0c5280d10a41011407240c40d0801540b17840e510316044281c45805020b050303420182d0780c04d1034121022081c42500c17a050130361b0703a41161000c100340c01e010082c4183e002101142c12481d20f50089904848000c108040d106800d40c1c4006c0c140d80f0844942c4c8038103540c201e0820803450a0340b00194418881c400a00c01c00b5800c041c000d441d0900c2c0c00c4080480c6802d00c802400140c03140040d13410030440005100c1d82d6a20400c41941c0d10b14540d071020001070805000903101c45458041d00d4007655005d00611442c12900905031446500184103404503c424080e501030046e0070442c00e8a0610a41d41205841d401e13414891320285008203504244491030101380c80328a000001c85010600003010b00c84c041e10709180440160010200364001d02d540030400c0414003150300d000105507000c21115103039120202e00c895040d40401d100d0510740200c4403a0f15100b03540200b0003030008403604000007890003200d00e209500020190010351b040b4400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307787562 1250 307786312 307786319
    0x3090e061309060e0c040b030d18050307030302150a0c080105011211030a230402031f11030703020408010e010905070b07050304090203090c091302150705010b03070311010905011701030807030207031506 89
    0x1d2101201d0102e041c6c0e01405400340140100782e13a812903207421802c10a448060421501c00c423405000034000c0101505c08096480c10001e540d001544c800c0c580658081021034600301d481c2c8102042814141c441c1c40140e8a8900191041f56101000e60916505c80c800d440d135061800b00198030030b003203101c00090642200d00c403600e0b19101c0c9400007201c480c9520140f00269800040c04800c1182070400180b80c90291402500580002c0d84030400e000b40110a001e00a50903402520666003190f008200c01103031101528280d40910401400c2c2d608030032402d202c0c5151010060018078010421245425620b2850404a030f104a4205045421101c1c4e170481a1401c00314854101040d010480c1526409800223015102411060301c4119400548001042003e4220300d0401c607009040e12500d5503241404442c08918001c024001138200f00046030b190301400303910102e00d188014441e05a0300315950030060394401c02c02501544142c0000000049d2507151400103804440000309000740b6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307788812 1250 307787562 307787591
    0x2210c100f2004030f14030d0212041707030f1b150902010e030706020d050315040c0801062012090402042c01060504080a260a0503190903090e06130906 67
    0x14001d07031042c0c04100c100001c0021403400311400100d10340051850500d240d4102c40149180700d51403c410300075001142c03507080c0044031403103d40305602030b02031035140400c0060320000b244500c0300001d0101e20000c2e13036000600e00c1194906140d130b81840c40461552541e8868a0300c4400403000e01d00d480782c07030303132044000c5507440030345207150f0003082d4002e0215608040c170194a174030120740c2c62420800c001c80000e4407402e00822401c040400900b0030081c00c843c0c10740085c15032200b4000d640c089940c02482030002401000d0704003c0499101c0503005c01c504a21000030198000320070039511580a0002046068420032241111190f488103d804034400840745c0700c420034140c0c022800c0c44000d000402032a000450300202c620361207103001001c1174503103155601c010000c8420341c9c07100902107503d83c070b4280c10500450060b000d071b101c501c4010b05421280d03004e517201d114000380001e140300810003c071042d16400030341001004250344041059040888104c030680c2c90b013940d005454023200010042e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307790062 1250 307788812 307788851
    0x204090f02070b07030c120204080312060603061c05011409280c0501050d09120c1103060106020a030c050c090703140702010c0e0f03120307180602210c100f 69
    0xc212029410030480d40c54691112400401807400c1c96103802c24075890522401442d42c840307220038811522161500801940c1381c00035114407052003070610204900345041829203100b948014450203400c00d0208420401401d0701404a50564991165113106c1c642004001d10a4038044011310110052500e0f0041d85d04110000c10aa000a401c620010802c0018000f040e20401c1c2491952020807400da04010310211101901101014600507404e03a4407008100b00c80d4003600c41080740c0040070040585658080c401c4001590010310504006405258604821402002582c2e015081840030409000048510705c0000e640da200c0761030100c0c410f0340c1030350300711100b84001c10401400810240818050b00d104511039a160409904143d4040080f00c1ca00203102600c3c988a042c010703c00340103030300c18140d8040ca119a100011a40c42d1000948000391a0b0400e070941051241160407107142e88944140c0b641ca0040b070303560350300640d05800740c564031410000b800215207407024140c9a560 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307791312 1250 307790062 307790081
    0x806041e080f0a12141b030f04060b0109030f05150c0c060403120f1a10021b1c1a0901150311060307030b0a030f0203060106030203092d0a06020409 65
    0x1000049500d0080785410056540604846500c07560340c950000041d1550040c410020400e40d061180002501000c824a140a240c211544110312058403555183c94007045401b50403102c1c04100140229502c2e4107e01011941030420408164036a21449014801d02200f642d55a1080100541308143c86c0b8400e5800565003c40506040c401c2d01c00c0b85d1560009403000e0b00300b041038109800290120b41c406c02c0042d03001001040746c031210301e00c0d1100d05e4107001c998510400e14404003550050021424901407007441c0c0310000082518010480c0c1078070a0220103c1c0495005c1d400d10008801001908000c0380c0715007068024904460b5280c2510100413402140f41211a000c100040380600719500d524000c403412a00da55441904600415440203001d0740201ca0394400014451103c245091460007a01510b2140e0b0700c0b000190300380d1000b40c84990295101782001103100202000e0303441d110800c80c80b040300c06403801480c20f14011b0015001d49281c0d0f400502041a11494071451044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307792562 1250 307791312 307791353
    0x723180105030105100c0302121c11030912030a1404030c06060f0b0706240b071202010504030914010225080f071a130306020d06081902150a110106080604 68
    0x4641c1007101013005c0400101d80b40d011301003411402030426000f40300307401201e10031502440d00c4060004500e00d00001d0b40c10701c002c03445e1500622403405a042800c5904c82e48442009000c511800702000e42e182e07000506094865668107140700f203892415142c0b070b0050340a5501c08100120600b492021aa030b164000c44161909060401c24551240c1c160380f10745030003000015500d403031105078074100303000d0249070414024200d40100c3c0800300381000c8c08005008125414440c020460103070300300c805c19a006008291460f208003c0b8100d6641070310b10100f818416500f03451f030510030b44c04c08001c180001c0708110400f944144410b007810040c0e1118080c031b003001014a946058000c2ea10841d89440e4144440c0c000140c143d084e001030f40d0400000c60b0302003c215500e1500c0d42080b07004001c1c0340144480303030141042e040f031401d01444582901e03d0300104905d070783c156900304400c12540614180c005200c9441507420a020342071194000815003035014102501e8a85402d16010304c800070703419075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307793812 1250 307792562 307792567
    0x3071205090d0c1a1303080708060303040302120f070905180a0f060504020a030b0c0406030b04020c1f0906020c0a11060f190e030313050f180f0723180105 68
    0x780000d000601800804081c102400d2030492401c0c1402d56000b00c04d8686a0309040005115118840401d070808090107a07903014074a40390b0240482c1c0c00c5c10180c41d80c2d6819171061100340098039004000340544a1100c040301d440c12480c4840d01d0800e100343c0c1c03103414801c3e40d0b40c04001d002400018a9009000001d01414845d8a903035914400c94014910240c01c00d42c0e140005001c64039208110809150004000038107407600100100c40c0350700c0790042c04c000038100604580c49041500030344c0c8580e003000010309000c00200100c499007120052252400540b03810442c008110707948000c001892800000d80707131842e03042c2002074900036081c0546000c1c00c4100807146104c41e02606886201c2080c541801c42d1507006403044518074100f54a20358540400101e0f942d415403602c003140201d038010f03980c6c07012521428007000b912010303080c401400c81a540740002c0410081c0402c0950040301420300340c052007101c030521400100c203407001c54a805800100301c02d40342440382c4204004002445c0961 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307795062 1250 307793812 307793821
    0x60109120209040816050a050105041509030509010c0c0909050c030c0a03020112020d02121905090303101e0f060c0507140f06070213020a030b01090509010e0f1305030f03071205 78
    0xc50700b035402000a0f140b84070108a24950000c1c195403d19019000001c8401c5c14a403810814020841500c00b10b4005092810304601058607004465800360962070b0541441c041500541e203041124008586090105901040c00107451140150680c010801003800b0800b031300a151509004a58480c070503400da00701040143e0780101001c03c01c0c402d010300961a40001070b864000b81c014008203081b4006180d040007612540910001c440d101e0186040c410313511540102912071205840c0c004110380c5e81b00701401010398212030706017003403180152045050350b00c0199034180146500090002380c42e81c2c803020705118003000810050300304a00c50701d0f1007007104000164080c1c0134036500c40c0511030105080b019541c602d000c0c01c4540148000641d41c0d004500380080c01002403105290104440d190b020885040510343d41d81030394182416030941e40c40c3d001c22047d10000040080b001e50300400e000314000f800c240050184544100f42681d01c904000f04050105516024129506840e000c03c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307796312 1250 307795062 307795069
    0xa0f081506060a0c030908010906090605100311060717040e0708010e010f0909030c0204060b0901021b0a050f06040801090320010e0715050705010513060506030a03021b180f0601091202 81
    0x443c940e40c141d040c0307030b0741c1c3c2ea420b441c1c15190300e8525400200c95518000e40b10050041c0d9130031028140344680340400050f40c401c881070720750030240d00001d000d540310030601d4011424240003e19129026400060028400d0b150b6171034541d0054101c0131001290006010a0540001580d40174000c8038042e0a041d6050145c1100188040d100e05000d0a0f1611881001d060041208142694001d0030a102003a16080f455445030311605183d030040c400e20fa850b0004c070351884084100c901c801054180030320329103000c121308580318a51083c0c0c000000c0100144601c03092007882c41280c0b00c0d8445000306070001e480c90100f05240d032001312280e4141100030343c0d8100c01180d0b02090f1900c401c2014078080b0380b9a022a032500030520010095840c1c6400d020143c044c01004001191040005001c0e03580c0d4042890745036004500010056800000e00401c4200700c4150109400c2001d061041d04204007490359916580c161040e080708120b00f418400e080d6030150184d0090030030407000c01581c5040381e010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307797562 1250 307796312 307796317
    0x50607030507050c010c020a02010206091b0d02280504050c03010e16020709060b04230a03120203090913110402041d040c08160e101203031a0a0f08150606 68
    0x4104040c0d4401c00075a039640074070165603c40320301c035008001c440c0548001035901c5150002c10ba015106000000310340e02c0300001c3e40c02c024202030310111b0104050790180604a440c0d2101203900114654002d8082507151340300c240050307118442d56500c0c91414060000302c802c05042020059000c00052142c0d10f40180055001480e4440303203c8801480c0404a081039429084200400d0801c1c000141c07000340c110107801616514090200701c408d43c00300040040d841081e0a50300a024500100b0200e1000e4681018503d41c60058038642480d040000314003040072910814030312300040c12201800050420244106015a4114905410101da800504a20386071030b0100b00c9940d4001000c00590440c490000d20414044899103c0c80900b941c0340c20341c1c10f0141c800e050080c0303c0090081c04201600e90100c0d0380d07080000303403803a2260710201c01070441070350301c0c4403941c0c40d14004503420340312a21200000c00c400e00f2600e0640c1e09241a13182489481040494114219010701c801d640da440f04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307798812 1250 307797562 307797571
    0x9060708041b0302060f131202030c1504180507110a031e120606020616050a140d0213060509030f0a0b0f0615032a0310030204150803071203060f030506 67
    0x5600040d12002025014510b141d0300003d400c5400425443d111041510141c10003038200140c0c0c641c140d4480323200c0d13024034050b26400b950580c80700d42c54098606000c020700401580320070f1150f04d041e444403140c3c5d000c5038503824600c0707140c2e9449080040c51a441f80003004a0034500d0082c000c008815180140503855416042c0b4140c1c10f81c1150f5620305004420a040707203040c18000340030340c1d030740e450b0043d458443c1140d99690440e0f0f51a07160741d510b031080045522000d21510b80304141d100580000345290000e0017216840c560030003040c0a0410300442c02030040605a44480c2e0300c00d508010b16003131007c000c616503040c0c2e0050742d4480c005582551400c0e4029071805004480d607480c1000074040454003002d0151a100c00000d200b140000c802004206101c9402c05506540f600f8031303007e070181b10440300c404160758459400d00040c6002d17003150500c003080500106119403203100c0c41313095900c070640c100c03201c4661403410103c0700e4041c010301c001410102070381c0807241d19540795652213450091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307800062 1250 307798812 307798823
    0x1315052b061d07020d050a050d020d060801020d050603100603111513090605100804030f1d03031c0501080d1b0602160b0a0509030c07030201051b01050705030f0906070804 75
    0x4808055206065200c60000d02d003070007180c80c1d00c80011066040900307040d41e5060044c000e4204d42c507100d0b13000b00101c4000301580c0d0b445601d081d50303217041480250841c2802e05030550f1192070000e81d4040c00d002420f462038101100041c0760900078105460005019180c0c0324441c10103208001042c0341e800560708103041030790400e80d2907180c070002160030f1003040391941080840c984040342ea041d10754000c8080e00c0342510029400c134031002e0140d07a0880121401000261195601c006e118858683c2c070f22040420684621802c00c4180042c0c1147c11180421412086448070403403100b10702e001c1c00d40101501406404c020020020003409c1c2e0780d44240d41900c3c031200b00d0842c002c20070f0707550494071341c0300e600003100c0c2d1a074a031894601c00c0d4250581d0b02088890811021800030000441202d58504500004108a0b4a50350040d42e582c0c0007040d03c040204082100110500e03c28010700b441150650344143d580c1c030b804055002e4621014003076000702d070f0001040200740c40c3c000030800d82240e00718 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307801312 1250 307800062 307800127
    0x906030408091c06180803070f02120a02030c01051501141806030f040311010b010f0e01030609020a0302072102030d090f15020306040f0b03060406091502131505 71
    0x14102101144190754695821a83c44840328442d41c02c588101461244144414080110390140b41c410100c2ca00360042c1240000300040b6021a001c2e040f0352520844038010741d8440030000c210403582d03130401003136003001d6000041d0607400c0003c28490386601100c000b07543c0c0311820f21900001d09040d040c5005616144000440e0b0b80d2402d207202d039400384200c0042101d5600d00c0c140c0c1c10051002004d031011400718500c0040200c48003010b0007948203440c410f0b5100c40c040c0c42810380c12101c0b16075103845541415625027010402d4070842c0000c1190961588016070742d00725034900700417920955048a0341c0c40c003098104100c2964040225100001c5006010030541c04500701144160720f40780000b01090380020010001c0c41c40350700a5403180408440803c01c3c0c442000755141950001c51401c0c2d81500608002000035070310f030b800000043d00407243e09583c5a5a200910100d80c000c62490031404280c01c8100f015485001d00036a64111038070b415410300d5840c500c901d1184141e03490100c80307101d91 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307802562 1250 307801312 307801321
    0x1807030b0102100c05093c0609130504031e02120d271401090c03380105102109050c030a0b060307060201050f1302030a0803010801050f0906010803090603 68
    0x30040707110045000c0408215113440014090b0545d0300240c5202d0103090b2200a0a4842040c0302c1d8a01d211041a801c494001f00701c0448100000800c140050f807129040c4160082500d400d01001c07038640301148001028101800d02801046890001050401400b00030701c21607039010a51690380c84030003824035200e0303200190b810090141484040d42d503442061026258200314204c002115002c1c0f0300c000104000304805500383ca25050001d403008003024004c00024030f4070500e0040808a1601e0600d400328000724040d03e004070b90303006400c1c402c0700c140180403030720700760000d80780a460604040303022000b1610a007141001c9100700c1541146d4540e2a10248203060012003820301000301036039428007881c68584022003040c4c031058082d01c15410b012a0301401440307005d0007014064400495a915030864040d400400c020480e094011b00307008000186a40002e140602080310000c20a440c02d0065000c266000500d41007681d48840c004102021011044402345281038607241d540740d80307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307803812 1250 307802562 307802567
    0x10812131203090b071101030522171318050a020a0f0825030903120504050c0d0c080d030f0b010e243c0a0905040f1d03030106030b1807030b01 63
    0x1c003030340554044c0d0000100700d401c0101191501039016001d0320704215549549045d040041510b011131090100d604607013078082003e18490071034050052200a18160240301c103202c0720803443d401802003a21003c4101e201e44803500031540c2c070402855045041001d042d00042000022030301800078004901c0200d030f10300d0110304804a08a1a00c101030000030924000107000b82582901500051a40c0340d1140280b6004d01400e4003c0d84c0150040200c032001d1410030403900071541007110401200f0a00180c0c0322401c0c00340381800e001680700060700c17000342941d070015165903641d51410070000038240021560343c850000c3e0380340f504d0030840a640038504c1c1050450700c00c0d0008500c010218896100d07000f180c02000e601d12048000030400790700c540b40d110030410b01401803828041001048188240d0420f43e201202041c8480d1020030312085011110f2074219209030001100d402c0040148201ca4250050740310158055405c000080b101e01456240c8030030140540040640341e480c01c0030070f41c1c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307805062 1250 307803812 307803827
    0xb0c060105010e0d0f051b010504080c0616051c0e0402070201020d1107210314040e0a0f18060603060e12030a0c0c02090708010806010501050304110f0402160506010812131203 77
    0xd600c64042c01e41054141807441d900d000a0907a84d85d03107c0c206491071600e521074002c2d201100d2030000140300f809010030030810300e508511007180c005c50000d24290041842007203c104812944100c0c83c28003280c910f0000d040f188075180c0d9034001d500422a141c010b036400a08464040214902152440800706c1260700306001c1e6440701860800903036903013003080c040c00c0039031103403510949031070701c90500741d94928100b8000e510440425400b01000180460202c0d00328186d10f11881000164180c405d0858461041c20340c0811703188aa0740301414410041c440c850f80401c140010300070030301c50045589146191000402210149031030700381640c04d2a00911070214050750080c4410a285007140c00209442002d01c1810305078070a0301d00001d292750103001124010781d080425052090000018070000301e80111606822503401c0055468500c0955500040a84504064000ca503d0070f81e0503450030403504000f42614004124405415100040d0082125201044501900f80ea030400303a4196 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307806312 1250 307805062 307805089
    0xf121112030c0c030d17040821010b07030f05180103090816150b04090b01030308070216060507140606061606061d0103051506090a1802190806010b0c060105010e 71
    0xc0c03002141e8280380b0500031400410741d140940c1110303220405014100c4501c070310009030ba61602c2c1c0850114000c1800f03c0000c0040b080085405201c0c0c100f188074806442da0f0076880848034040200c0c03260105580032082031225001494014100000b0040710403025101036441d606140c0d480d00c16108100740101650b0b5070750a050724012008005040040154180203401200240740c808502694600b0f40700fa45045600400c0801540c0c1c29550140c80d52074000d0300c02c40a520520a03500d03810554150101d020b1b01695645940b610041d140251402c1c441c0e69070b400132504440104852500c0328000e0351a40080072095a0710020942054401450140c105220038003004c040341c0d0000e441c2000c0c1c0c0b4102da100710100c82c904d940c44428040c1c0c124090381c0e8a0350040d50040440e0070080241c101840b00c20540c21242503010b21580040c5d81c40031151207004060112440c1000040400d005c41c900410280300c10720b01d483c1400d05440d48450b0140107150501804e465400441d48070024004110b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307807562 1250 307806312 307806349
    0x11070b0313140601080607050a1707050c0f01110a18180b100c020f090718031b08030705030915270f0612150303090d03050a03060f1211 60
    0x503401c204032000a40503009000782d60640c120000c080081000060a9040325035640150a00303031210407045545ea07100075900710402c40280c000100380500c00b11300e00d01a42c0701d5110907503107007642c800315420180340d5046010241d242c1018446000d0201080300c08003101f5182104003e84901700c03600180c03174140c00000c090b42406803800c95400301c81d030207611442c90886000000007502403003100c64445002000350005241c8145001904010f0905c6821044909140c86610500082042c5d0343c0456401981d42c420341c4140320b404020101c2031000030f49040740c00b551422400da19a2940c0f0712800500038095407030550084a80622030080d201d009185030102c040d49070106400f40d20080111841794800d80c0c045141841c0d41c6801c0c0704031400a02d040242180d21384d01c0907500210100b40e09242509800100304a4405545d0500c0e00f05c1c1e441d100713454181d12010310500c01001c4903429045281404460541400202d030280040c5040c80d511101035042000341c007006c1491100b4400a9030038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307808812 1250 307807562 307807567
    0x603010204031a2a1c110703031401051903080a090e0c0c010e010b2803050111030f060d0201080a051b18240403080a0509030d0f1101091211070b 64
    0x10000c3c425650a00071054500e8590850302605101250b103000c200b803550102e942000514072000f8040c40c0d038490400da41c1c10000744116803403007410b841d90003403c0032800a41e490301c9100e6440000034205024020a460000480b2404c100f03007841440140006000c000d0045000c820951080d40503601400c00100c440515081c100030072507041e00401c50524282d42011852070781c083c01440780c2180e14000510310146442501503e5403001c0d0850428109802c440d000030001c92400d0023415050a07104442e50341e607103030250101c8101c1c100580107a2044180f50040c00140c0e0344511481d0b00091034210019207030726031b81d10403000810b040160312100c40300800d280c0013921107405183c2c00300c40c040e02c520b880780d0103801c020707003420004104484031907070144002d00220390100050b04c0042c60b18103025150102460000c0d140c10510a00388001800303a80c4454070059100555607050b07040f6400178000f5808540c0e030703040080000a0301c401048044108050311203001c201c20f07001001a40040c0d903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307810062 1250 307808812 307808843
    0x3020901061d0418051b010e040c05090604030819030c020616170a0e0d03090c171006080a0c090b13050601090e0a06080f0714090a02041e09050c040f0e060301020403 73
    0x1001c440031600156014003a00c2d0052014410008480031220b005030340341034640c909076040100502b42140c040c01041000d000310103a03038460380c00070030242d805410300503241d400740354101c09210038001040b401c041c1030a140111817500007030740f01e810146071f003991100a204c0d1030341102c0d40d600c0c41c05039018010a01c0f051264852240c2e02c16181c0103510001d5808010184401340c082c1c4d451140000e0045440003010422003101642c2c0318000c0c4020025104844906000c980984529170000d9409030000300d40c800c1000b0946003030341c00070503084a084c070844200100160641d01032411507840c95881300c000030707000ea100d420404050320101c44910341c5420890502001400c0c64015035a9a10400980c000794850009030b0b00704a5014000f54440b130070f2140280200e03508050710b07618000f03400740000f05490020595104451000f9080c184105d4039207101841079070030151010007500020801400b00c181095001d100b03440500c03095000684503540130a009209a0b07002400c070140307100407071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307811312 1250 307810062 307810091
    0x70204020a0c0606050f0a3005010c090e041a060103110a0e0411040e011701181b050105090612092b0e01091d0612010507090512030403020901061d04 66
    0x82c001940100c4041040070340310001c0c001c0040038410815805006000208400c2d030122140120524196000846403540307846002c480c50130031102212140d4403160013030f11240c0e004041d8001040390307984240c001e042944811041004440d806641c00f6032010020784240d01a421080d00d44521404c11640c441e120200104500c0d00303c0100c0c1d03c5142062040c40082c0c071503006680a85091a100140c26460030a0115460444200010155484d0680d402c984458082d01c07841e543e0291700c0050142c460b00c00c403000015038540005061100030f02c41d40440f5225002500d40d00780c842000644a9100d241900c3d1400800e50b1648a0108500c00c41e0901d4030481709002248040585808c011000000b0066611aa0900803101c0b8094441b04402482009000c41ca400c401e002e8400c0f0b5051803070a40c00c0e03003921402c070b5811010072821a030411480c00c01450300400e81032240e000e117050508660000752501e0701880b0b9007041200c0002c07450002d481c02d80ca500703415040104100700902410998 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307812562 1250 307811312 307811327
    0x140304060504090b090405030306091b0703030e150c1606061a2511040513050a0b150114040909081b06070305070206060d02121216020f101d06070204020a 68
    0x44032103060901e1031010b145d003400400b190045600001542c1541c0d40d020030b0125002d4010034890204030003007100c5018850010007002010300039580411031201c28401140307020b59548803641d0300c40440c000c0144070804c00d816180344c0c02942813a0180100c0c00d040c80c0f0040d24040d04940301e0b041102c0024419441000020041c0310581e05514411440c00e80155034900740c1030001601c80784000c05050310324681944140da000b4400c4130801d100b664141c41c1d95190660701002100d5030b141d040240045c81c611141d211002c03160034607056003040d040303901080c081c1c001d91244840d229180c401c02020000c0150070b940810b03009400455003640c08020607640d0780b00035944072000c207240c50702049180d48082541d030f108a07409440c000024945500f800a80000758004698074065810850304124892006000382d0380a03000781151582c007801005107079000c000b90584200400074481900d0758020b088901510304408600f080f00404402041c503900c608200294420720000c2d03848101c0341c01004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307813812 1250 307812562 307812569
    0x30e010203100915300f060e3306030c060c0a110405130f0503161a0c0301030302060c07020f090106020a0b010f0f051302120709032901050d140304060504 68
    0x1801d10155402c100404081005405007484540c891045c0320300800340f90f452000c54107002401e04643c2c1d00a40c41d60b40461441150444034580c40f9034400514500400440301c000349002c0e01d0031880d03600c01251180300b01145614405401d010000100c0e40d5a00f40302918082c60094000c50780d40300c002c40980d440f0701e88a901160802c1c00c0d00e280e15864123091003010b10545506a440801d220545c83e441e40c52800071404584601c0204164410302e141d15400c0f140143c4144042c1c6881c801420881d0000318008040c0b00b250382e024001040402c0c0c1c00200703550010142051265148100c1c004074885070740c950f901a41291102c800011219400102e041240d070181e509118103036242c0031801ca10885500c6010180b105850040c801da1621110030726003d1007000005181a41c842c42c005031010088030340310301140c824007042041c00324550b6440f40b881240c03007000d5034a400202c08548c0000040c0241b83c0100ca95028400800007010445ca60045107a130481e1f880b650741d1180140140d00500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307815062 1250 307813812 307813829
    0x3072a0b0d1b0504050409111512010806040b0412021912020606220b0f03060408090108090601050d0f060207150510090b0d0609022202130501021912030e01020310 72
    0xb42007500c4545408800c5260541c1c42d03807110310709480d00e81000301600f0380c40d1058919070400960080c0d150f030754a8462250028110341261242d19019440c1503140c4140d0001125401282c20040029440350b40e00c0ea105921409003040d076040020128589820030522680f01d942401c944801c0c048144030076200c8284560803545d1541e50101030066028030000789224840c0c03101d4508041034056000219290009019803032198a0300001a28004054400303680555002840d0380c01c3c0d50344004900c1c2e014541c50000c2101d5403401000c140381e18403141025006c1018807140c0b10030020250100c8003016000a400c0503440800b42d4044002d100541d82810138080c0c40c8000221001a4018969440401440f003204400b5548561001c0d0081c40d500700da02c00403c4244641e491880441503003500301015006890701d45940c0b07002c403441e0144e00120706550181c20100301c0640080d10b05400240c1c46260b00340c056449100680140440c0e584580c00c030f5001100700225001c3c1082d4090131210044c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307816312 1250 307815062 307815071
    0x702010516020d200c03030f07170f030a0c0311070b100909030212030601020705060c03251110110703080306031e0d18050a0b070203010e070803072a0b0d 68
    0x14003042e40e40e640320303000c00b4011546810034556031040540c521054081404142c8451154420000303041d540054016158007402190305420701042c1c0038501422040902180d10b0405032010400071030000900c1c0380d4800d83c032410f42d00d40b858030030303000301c500c444049203560f032213442c0d40c5021001640225255407050010f2900041c0c0000240190302c84e40743c054001e8554901003c40490355503000030310181c1980b04480c4002180c1d04c42000074020003000e0b40c05962035550042d4403214403100715600700240d401703444880000c140214650b03141542c1c1103400d20064054058150780c40c0e55200030345107650040798070000902c1450700045208840450a036081081c1b00603d15915401d40d110122095001c55000442c01c0d010711010280d00f0f906d1800341c5e20b201d5035000054172404c0b1076000042c05020104c1d8900071070600340035401d5001c100d00b01174400c0382c2c10140c88550728054410040d05d09004400800584044039400001145e440c2e40d4260070281c40f140c40a010758002040c24500707030300d403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307817562 1250 307816312 307816351
    0x120406050912090f120708060f01060813030f03020703030f020d0b030606030102070309050105030432100e030a0e0a0f06030c08090d0923040e0d03060501020304030803060402031e07020105 83
    0xc201d03010404000c120300a00c82051040c017000d12500351a4640d03074400c922006c245c06070100451840303400e1821030b0548660501d07000828001d0081c01c002ca040740881910400250001040e04014160b03180042c0c4510705414200c014003160152900b00b2031000a94119000707064000c03c031426001e80c122000d80c0c0319001030500b01d200311078010b800030f84428400d01041d8490001550840d004034402255481300d00c296646220001504050380078807400085174450040c415010380189100f0304100346d0041078000e0b40c0707921826280608001600030090001c0d030380c41d0314020140001072280300b080c84e12103e01a00800506500c00c002c01c40071070001e11005400036030b800501c00e4a0742e624040c1c03460b1420f00340918030440700c020307051002c14080c80344640303451082801c000001802000c90990040001d001c0f43d200350446811900104014400f0814003401c4980158084d2801a6031ba500d40440150085804031651901104182400481e59054010b039001e11510f844407800c0c0b016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307818812 1250 307817562 307817593
    0xd0b10020304081905030703080601180914131104020a03060e010b030f100b0a0e0d12020c19050a14060903030706060509070905030a0f1704080a150506030a171204060509 75
    0x610840100395906c01c10603040060b1041c005103401c0103041c10620311039514220402c4030402150010f840c0c2c1a5180000203242c0d0b074840f103064008045440803104032009898000f0010640190b080c001c0703070001408501c07184207503c58401040980d4445085585500400300c941e8001e940c040b00100e80c4c240410341c8000c400041800311201309500f0391a102191005840110700c0c1a20258003504030b89061010524003030581b42400328590280c055080315404100700f084102150485014508d4024005600c9000856003541c1000c50703040210340300c440003c0d01911030a801c0c81d40500011801d0740420032a44c1011081e91400c80d41ca030016a2460030844400d1302038421281d16900107a40c1c540421520b00c1e00c0c101481c001c40d56042c03d030350000c4410300c2550181d4070184a56200700784200c20b0003410700240400501a40f0203006509104c00004e40d40c00385140f0140c641c0c0314000d41090100c0300c0d102108c48800e24a0301d00c0c882803900d400c2480052400b214003651a00580b45070000911 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307820062 1250 307818812 307818853
    0x14060405030303010603050a0906090305191803140a060213140405040209240406151101090506070518091801050f0601051801091706091c020d050d0b1002030408 71
    0xe1016000354116803030820100e014002c00380180e4202c640d105441401300d290b5000c1c0c21042806525656580c0c0c5007000c1c0700444400201040e0104410000c4034610030084241060031a03401c0f0f51404610903014985a0600d604a600144028400a412802d6104035800201120840f0354450701100d1010280800c0d96000c440c0254040444400a40f1120000400714903000110742e035103041c501c0010206044403459000400491074541c50300a40319880081020346001c03403802404252116038a45a896001800f041c00740704001c01c0140b0454044004071000c500d0003032129009042100070304c0404280d5030081c81d115402c0c0310005076400014680140165410b039562860300032180481c0464150441200d070410130f122a000a10300e4065208c560061030b0140503083d01d04040401c58070340b0000328a40500c110f45c1041071100c0395008074041000c1c21090422a1f51035910035a207400401d00d071207081e41c2c40034920168142650340000903109841ca50001c80b070640302a10201035804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 307821312 1250 307820062 307820069
    0xc071b090e0f0622050c09070909150b0703111011040f080d090b0a120504060b240703120603021008040308060114070f1a0103080901030f051e090c100306140604 71
    0xc01c10071841213401342003e04516540b406401690720310f02c01c0c00002070142205540ca880007800c010428461558244688020b00080454064105142c080011018081d801015042c0650010268a42c5c80203000c00854046074036010420f5001d0301990800130380144c0200c240140310010085a810b900241c5c004400742c090719904c1d8414603218665549a00004c0341008002890598003980e114070b01031b990003103108440c00f003803e680000502c00c0c60320b405074503c203030300003200c2c0381c14803004580003200c82094245c07901020380000340341e80b07002400c4160300007900801c6181000c404154070140c2c6601851080d81c51100030f80f90300004545031104565080b014440802c2540001409040101c003a039100741441c00c1d02c40107650702405600c40c01d900c240c403040000289141990b9151003441c03224168550100078500b044000221041d15004521340d6420414000c1080301500300a00d2403e110010a01800407044200c0100900070b01e2251070411103201480011624003442a9070a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 307822562 1250 307821312 307821331
    0x70b190212061005210402040b030109260f0c06100e1b0d0e0105010b0403050d081009050601030e0f03130807050312030c0f0412021011060c071b090e0f06 68
    0x11900d0b840d040014031120001c405050280400007240b002408881c0d141034482c00b0103001c0b005160038010712080d9580540d100340302c0e0345030500308400221196004540c0c480103a481c5160780c00b0309031a800c0148100c1102214441d0003288124008400003101807140f48550031030040150f40f00880704000500340c4688079040c0d038484031480c0e100700800240182a21203440070644c0c0102459203401c5980030b030883c1390340c52000181401403000401c4024404c1080745490340b15803401790042d030016075981c0906030145c1d84070400b01d211680320b82c200c0d0000b10091001d03101483d209054181c0d8951158807000c8208800c43d800144e44400420350341d0440304090050000e1b410b0b19203044900750700040503800c8140342400507100510340440038001500c0c900441c1d00004585004103c1d00305075400c06c40080003625807190a042c5000301d00f55401c0784c0070305141034075500545040b000d189541c03c0b10080c0302044040c002041165600309800740300c00c26040e2141c40c00381070300070354662000300c58841c3c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 307823812 1250 307822562 307822597
    0x2120601052107030f030e090903180f01030207051209130b090c09011103040905010f120309030303230906060405070c030f0f0c02030609011407030608060615070206070b1902 77
    0x2d51400860580101500c008259105141c69a07a28152903914540540000c0d44106480205003080a402c981142c0c0c510003c0d0700785150002d5060411441c2c6a8040c080c03903142c0e803040020390003501912000f980c00000d942c011000e04803e400107420101005100322820750008840c0f00607849000e1035044003905010007503403590720b601110f0f801a110315041249141101c8407031882440a04042c05289802060551429102c001030148a03000310408810080010700040c1c0c1145100c4100c0b941801c02090703d800400a2400314040d50607902040681e0100700b01d1512000b02e00719200c0d04044030100425107540c1c008540d0b400c0c020303000401003150002520500c038041c50418590f1400c1e403030010810f520a074080ba0a1410950b224405e50791102c0007400813542c040d240561111151a04010702840d100b840390380da20021701410302414070069019107680c202011604c0b520340181415907901403134640603c40480441c0e076a8107001000749070b02c054030346d54000c4800050741598081c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 307825062 1250 307823812 307823839
    0x2010e0705060a1403100e0106080405071703070303051005040218040f02031909021c030c0b06031621140307060b060306060a051602280e010b040b0309070f120212060105 75
    0x1079065201420700100c910f440e50001a187c00203d180a010b007050756214440c034141460303c035181c0006074010740380303a220510340981f404800009423000e0b240c2525010a0719240c03044d0000c07140c7c010360440b130f80250001031f0780b1403000044002038140c0207003940d00308000160840729200700d0209170303070b400024108405484c0300f01c582c503003210380d42600013000380443d4101c1c03140b00f06111501c080200c0c013050091000100380846400d116502c004c080d40600441740c5c07a10000c0080b42c19134016680002031100341c180003400440040307140152310101111a05500d404038582c2d035000940704851a604040e0521441c0c00e0404c1501e0203100c014000380d01702a5468402d60b010340080808007114140c0119200140e90381c080c03507100d03260001c0c1c81c5500b0000034000e5000b4948644d00942030080d104030040042c04144003c4030b041311030842c4456201e88600d15190f0030400280d000c0110085e40040c08948034400707098440020303100f00c88081c0c000d00102003494889100740704013a4000764101900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 307826312 1250 307825062 307825097
    0x21e07060209030a0c050f010804050d03200c071a0703020307061a040f0b0a0905042105040e1e3d080123090a0b150a09020a02010e0705060a 62
    0x10209248100009828103200e8408a494400038100555100c00650700030001420300000d4001000000c1ca84084286010f8039070950b81c04008558504140d41c0d00c1c0740d400010003c50718080c401440840f82c941d58030081e445a40c0c2c80741c0c140154015851855a5080304000203c1156005940342d0099404d151454880200810b1025124000003404032295900c6980d0340c400d5000c040c02c03011001481e10382c1c00050115040b59031b001025020318000038040815500c1e1404485e08111490340c59260070640000c4405006a03800301c81014001020301c515a2401007452515100d4404103217803d9565040b44600e1f6a0074031030320740c401c45d1464210814081041c030303110003024490307080300d413020f035070740c42c25421113604bd0b1040e039401c0320185100b080700c221588215001000c1000070709410040b5110150301c1c1c0000742284142e02100940b002e602c1d00c0e1030031840c00030101400c0841d210421102c01034003800031001c800149003e00700c0003249920b4094161507180ea01950780000f007160280709c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 307827562 1250 307826312 307826317
    0x80a03080718080a06060905060a06090e150907030504111008041202120c010e0c09091203060d020a03050c090c180f03010906061508090721150615020f01021e 70
    0x5003404582d0b0000c0c0425060700130040c010007184204800280a0b290001c020300700c601c090803440c400c5800c0304042000070b910190303120650f801c1521180c4107803603c45c001c2c0c950828003104160020171040400940d02d0305940315074402c0d801081c45d000e680041200300b003180843c880440001c2440d9502140101d11000e82000c104201d41c012286000c1850402e42601d802417000300001d69100d0b107210664a0302072100411480003910080c0311400e08051803619510701025182001102100041b4156602d50300c15900c5900a40f001902e00d0310307810f01984444030303449210b00414030300020400c0001081c040340c024065501408042c00010000c110b030134040800520380c90364072400c0c0328000c22414406d00c0000c2c0340903000d411440f001070102401000d002044030b44035070401407040040f141440c648031807200142c0c20307403200c282e00340c500080c49560140c00c1e500403038940744010070200c103000002180380d8101e40031140743d2044900020300340c3c80744d270008400c036401c000800040e05055802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 307828812 1250 307827562 307827587
    0x4021f02070f170c030601150f020a020a090e011d03160f050d050c0706020705010504050919092f0307060807110105070c17090a03150e0111030709080a030807 70
    0x66590440c0e840d21041c090342059000162200781d1036000f03c824600c00c114002e4043d5090b806800258504440c0c01c21201880c1c48403030520200c10742030030140d072013071222950702a40145040c102c141c036015120000e00409119050540c6440e07042040105840c042102a5659000031843c141d4181c1c0e2108484107401412210071403040c0040740020000d0040c035000115945d82c03d6252801081d12920b42100c0b6840b074801e54020709028406660310504171820344000742c03400e003d01d40310002e007115402d40741407426000e43c0c50701c100c6004004a211149003180d154050f652035001800d001030707200d580307128202507042d0300506013000583d0080040703a90044840c1001c80030205e00c000318509440040340c40b0300006a129500c41c00300f1507031640301c3c16503460700d0f1075440c1040000c8000c104c9410072404003429060002024079030303e18081d000140000480b41c02801035201c140d148801c250000d844000c0400c03400750020501d60400601c3c100c1150f0107643e414020740700d540060316041401c90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 307830062 1250 307828812 307828817
    0xd08071d120109021201140f0f04062a0e150f04180b120d0207060309050318030309030f07050a080c030616032007031206060f0e0a030b19060e04021f 66
    0xf80030800b40c1e441c110100e00382030440b00081074042c0b6007407112000090040209514001c0701d000c2c0902c44016009082d4840d6000200040d281c0c80d40040c0041c0d545103040904c0b05030252200c11907019400503150f1180340f0180e94450401480e00c0540d212401508899000d40340141700c200070522485010b0344011445000000706000c008000c110026102c500c0c44039568030123602c07141c1c0c60b94100315090040c0001d1808200035125039803419100c0c03003002e00340e050504100f4000308441d5400c5c4200c80c00003100400b120100800f58010540310480e40c82040d10403d010300c0001841100810401c44140b0000c003e0300381580d520356600a295203942204041594403054410401d11803114408104c03c1c3d42d2070360b51209003915004101c0804007e041e0025800d08004111480e0000d4000504c00c085003071903880511003202042107030006900140120703000c0810300460060042c81101d00d0a2080018003481c1d407225554940f103101660001d4202c02c0404031072100c51012040501d400c0c0c40d51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 307831312 1250 307830062 307830071
    0x70b0c040f080a0c150503240306070e01021e03070f38090a030905060d150b03090d1706060903031303050c1c02130507110102030103050d08071d1201 66
    0x441140da0301d15040c2d0001e080383e5120210103c140824042140014030300070b0851240e40e04c804000428030301000e002010300441c11480303114052146d02281401d0100501100c90078075250078010000f110910032140036024040340d071014422000c83c042e100c40c040100075441e00d11b00b561001c0c0500125402560f4842d0380714846c000341c074541030070b42c906503c1c20603048410b40d80c1941c0c6140d8600020742454215400034824000080d00456038030304440c001c88001743c0b900303400c400c003601401e00c402c20022424103924020804a140b075000e5802003003441c046070304440d000716055441c1c0c0030841c07440003072401c0e10000524038640300d0020038a07000040e050340c0c00c100882800442002d80c0c1c1c5c004840070b401c210300d4441581450003c0c030143c4008214812281c1000781c02280742e144902106481c41c1e500d0782c0015941600070880d0840b02c00c480d030002c650300c0d82c5d00d09040e91251034000c3c1041c001507000c2c0100c1c9850707108002c040c00800021541141040d1604100702510622402c41c54842d52903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 307832562 1250 307831312 307831319
    0x5011e030515220303020403061d060109020c0a0c1502070e011d06041803082a0f070501020c0607090e0a0b01051b0115030303060e090a0b07030507140409020d0e12070b0c04 76
    0x207041c50800c40f910070344025031074030b0840c035040f004d50340031001807800340030240b0300340300c584100080c0141180e981000060b41c07040580601030808448401c0641082030341c00700040c810f0041911105142400c1d800c0d90045034480e02c030115884800c1c401d242e030003801130007804011001d802940d41c0002e0020b02c006800010101503001080d00e4490640c04a100b803020400710b400c2d00084002d80c8645050040303880254191042c81b03d01030b00c0c000366400e800104520040100950444881103045001ca680c14604a140284580a03500032110b01e90f0000010505480c180c2c02903038030703911058640c02c0c180302e12524110301c0a0310240d1401212341d2150710500985e50741103e108051400b03980d0114041e810100340440f610786c00351200c0150b600106c1410003062480c1c08213900b1403028507000c9984d072a250350803a01c000001c50b1030812803000080008a40b02c00e9030080c112084245401d1000442d804130311a00c40c40348103d02800305004016080c001280d4480b039aa00c155514503085c1426207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 307833812 1250 307832562 307832611
    0x19240c0203181f0e04060807120f0f0206032509050d08090d0615030203010e1c0503090a061107030206090a0308070f020111040803131202010914130c0305011e030515 73
    0xc3c407100100341c0f08aa045103900f414042d0707101601001c00102449454030f1400d44583c01020000707003007a03803115002c004004140b00c03509240341d00100500d03124186082e4120904a4900b850f00785003003518130810b0000d0190034100229a00208241c0f0002a1515042c811b40c1c00360f00d0350382c0c2c003080003986000003412a1040404401381110301151349820351040c14219040d1342c400c1181a030041c8016100b0b19a40c1421506100141c603109481c0e03280c0d40d02c81c601d00511003800034015820042e010390440451005420f015000380d088481c5a254060702c15160f0b43d8401002c0c001890040c0081d090a0050851186200c0f052000040c1845036000d61440c54011703403c406080e800000702503401440e00d096680203072421141e03c1c00b04060903070000e0100c071158490400d48202110720148036070b07504070300e218000c6008541030100d0703520104014000d1509005a0850b0443c013490340999000e0700c020042540e138440001e01c00c49070300100a2450710001032031003400d413100070741c0d141d050345 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 307835062 1250 307833812 307833859
    0x11d0105090606073e0303030c0a0e0a0f090915020a080610050405090c03090f15071d10204b0304030506010e1905040519240c020318 59
    0x117084041c540004903c501034501c1014140c94000d1082d8400c0c014004d00040010844060031310358200746030748080e544003080c5440f110f5845118408030a0b800010304070580e82205007020701c40c6034010001d062041c4140124040e0b50350b40000544800000303021424890710100d200207042c1810b9080a58a9000642da100b08907680c84500c1e80210070301101c110200140f000b078586402c01b49c851100807103501c00000c6001000001007251240d01c140d000c1c04020100e00302c071400034124070b0380d008174098090030101c003106040002d500c1150050030048800b00702c3c1a404205440c08070601c4076040ea0752000009140c0603518030000c05c1c4c1c00c2d03001c5440d108101030704011029001d542c843d03140d82461820681c05070b0000c14400140e41c2001038074040c04001c0081000c1c00d5030001341e181c070760b818150310b0000e2221800381c00c14120b2035442c060080c02c0b18402c00b81c03218121450684805503034044185d40c4c05000810142c0d20500061400240710140d80c4540079000d041102000d4071041140d0000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 307836312 1250 307835062 307835123
    0x40803180a0f08010614030106210c031416060908030a2601180e0c0a0902180a1d15150a02010915020a0806030601050109090c05040504060806011d010509060607 71
    0x1c4e95240c0082050004042d074045a14400720020814185031800030b140c40100e45050318040300b04040d464040002e28801c0c070000d5070300844a030f40003510342c01c0c0241c2d03643c0400d030b808004241c10090029102e4810001c103001c4d100034034055802c15024640c140e85c005840e02074400c2c000080c101c1030b0f00007042d00700c2541c02440c2e0800c0110a424165002070200e445e441d043c2c41203078101006948e804c3e01d40224400442d0481c100040e502c21243c040100503110b451012640240f864200041c54044000c400702c81100c141c0160701591a0410000040d4548200d595002500300c552422090744400c040c0600421a000200e4804240d54a8650290140743e940101540c089040d040d050ba200c85600e83c03000090340209000d5040c030300041c24950740f40c401c62010f5501d4040c48084540b040003510020240900203104883e1a4401036884200074042c03880224682c0000b40002201482900c0c101e81c00504050714548400003444010b6000401c203445a82030002018091b5a15011005c0381 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 307837562 1250 307836312 307836329
    0x10b0a0f030216050115090209100c020d05011b2607050a261602030a021c09030b010b031503031806031023040b0f030318120f0304090b0105040803180a0f 68
    0x41c20030001b40b10340101c240d90400c10b955031050008012545031110681a4a0f03601d061000346a0501c1c400a0300c04151410010020b50900c0101c800c1c1c00303194855110f0101d400d445a43d40c1410b50880a401010701e001c51241c0705000c07401050700c02c0d024000030131001c0710340d1824042e11190751403028002001090030160b140406400c00c00c15412443c801509150284055468003e800d00020b5482c1600c4030450252480c51005445d664001e00ea404000d40d44018031070010760350b0b40c2e040d88181d00304844580c02d4000c945407000c554540401220410003041c440d41c0d107002d00c40e20a010b29a00020308081400c5860200850780410081203400801e942c4049103040b902d64500b48416120084905030290030301c205448001d907008001e44440b590102801441c0d20481400500400c108141030040cc0c000d040400c6903408002c0002d005440c41c0e86414001c0820740c03001110180728a20503d9401c2e042805110341d00c1c403641d01941e4641d41c00070490201a81c0f00d18910100b04003a44c48920f9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 307838812 1250 307837562 307837571
    0x2061210090c09050d110f0d1113060312030f02160602090109050103201303060903080403020c060304080307110a06060603060306061e1a0f070b0103020f030105010b0a0f0302160501 80
    0x80c1c080d01402520400030310346821410303e840c02007a22052880d000900d0000c0c90742e00c1d12200c3d00c0d25040181d00100081c049000301d807143c00c1c01d0344030200c0210402d0040416482030315140d00c8901032041281c0c0e00141e5402502980070b0110010403226048030007141e020007140ea942c40305a0100c940d079034000c140060783c0714000340003d0106c0d06d0703691040e030505050201000100c20f400c030100d10034040c08028695100700c001c418032405011600000c005c81d150082079418168401c0c5000d2080d80b01c1d400311031241514004014007030004a80040602e902000003c0000b0700c25406408100f2281c0111070030781969954100a4500d241c001c1000070b9a120301c208240a81c0d03000740001409641844280e050280d035584d07c801285001d203c00f06411181980d1030503503102d080b1201484580900354440700189040044c1d0417080c4020f0307202d080b29003541d0f0040d15041c0302d20303412609184480c40c5054642c910584000559039000c80501d0f41c02d11407a2250140014400b829170301c510000907 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 307840062 1250 307838812 307838819
    0x1401150501032306040c0c08040f0e010909020d020d030c0f05010c0207050f030a0f0c030b0109060f0e070804110a0b030a0606140f03060d022b120c0c050d02061210 72
    0x50032034541000c0001e401c1c1c44000d41e840c2c003454040c203581d080a41581c5c04250080703c0d030400e494100d51000020a1440c3c00140001e81d0040d1031142015141d18120000a07640d03185040401c2d02d11500b4013a502041c3d00351518014508000303134030841ca01c24288071000e54040c0d01e82c01101c561212f010f403a5a512294400e100aa05200940c00b501088500311110044a00400e43c1d840035030302c00502c1c00307840c081007009104940910100a50348003001074220341c0c48500d600d02803c07481c4103510860104520101b43c401000d08402e100341041da64003140c603522921903040c2c60203988503c0b0b4210380162004103140181c60300035031007224031150100700c04c0e2420314018050380e480030440001e40001d101d608035410079901120f40240d001c403420320000d01d02c0c0c0000382845207180c10700c3c104401c05400141080099500000020b80104001c1d10881c540e1241510402c807018801041080c00982c1441680382c1401c04821660001d4009410910925991902040150b40c0b900140701c0c43d05082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 307841312 1250 307840062 307840067
    0x9061407020d090e06060c01060b070807050601060914090a020f0d0506190b070311070b0a030e010c0801051311120403020601030c0f1a18041503140d020604020d1401150501 76
    0x4040c1d102e440e180010840d4540382448500b03140c0581664865803000514001c00782c401d40140700075048050807581e0300d80582c0343c2002d06030b04c500011a00c03400340200018030f00d07010b0300381a0700f150540c0d426004a23420a00800298007001400c4000a5500b4410782c4080c84c0e0780d030701030710100b690200001010304008080010800c0c500c003242c2c0d140514000c0070300110700c00784242d4803007540c1410907124085c0349820b076030305000264100c0c28000c480810759070250342d4181c002410817004000200110380022504540e800c0c0240034007500000124510a0308040b103a1090b000c0503050b8940c6400c024048203108903018080c0c80c2a070040e44490018410300000404900082025650400b14149811048500b07124984a010703400080400e882d01e00140108110100640040017000344400304081c40c040300c0c40d140000d6549960401201000c840001145a8500c0960f0000c0415a6503070342086080b1082107022104200f980c02e400351404c4007401258494028813800c40e0004c2e040c103000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 307842562 1250 307841312 307841323
    0xb0c04030b0a1a0909071221020a020a120203010b0603011512020a09030605220503040f08030c1c0522031406040c0b0c1609020a03060602030c1f0906140702 69
    0x340300b040c0ca49020b45a0f01d00b607000000f8400309040e50784081c03540e10700360a01e04002556010580e140303c5003080d0000c00100b04041d840060302c5950f40c4280245035503040342d0b40d5103081002500078407141c006100c1e8080214200c4212407004002003100603902000c036030603400a0380089444840390b54140d013240d420176030a4142c11045841141030951410006040c0da0051002810242d510404500b0552000207501040b4210703000c0354000842c0340ca4036070f549620a03ca044584040340d1004290180c0100407a98075080000027081140c03101103019a1140005003818103010080161411900826010104440801043c3d2a0030b030301c1e604044948480d00058114141c11050070032000881300038000c419241d552405a4842c018a0281da10b00301c04407080071140d0904000001d203080558005051401c0710759001d005c00c2d43d40e400141d1b5240142020b40403140c000641032a003601c4881c82c0312311200a0181c003c5620071080e11140110391142504e20140007400e0200880b1a03010404e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 307843812 1250 307842562 307842571
    0x1140c0111042301020307080f03070e0301022a0a05120a02030405150a03050703060506031302120f1b03070803040909050c0a090b090c030615090604030b01060807080c090105070f0501090b0c04030b 87
    0x103075250800035234030055a0b04c155072800762101000f00c04034216502c10040c604003040c021f8000c42d0f80d00001002c540c1e407100d141082540351100000348010004010130056241e980c000c2c02040c040b48400090b0341542c200340c094000b140320511000031107507162a0304240c00190242070030355a0405201c0102034400041052086c5414000b0402041d2501000c890340282d822050311031444c09413001401a5402e151414090300c26090000e9006a0110781c1c425899110301c0c0b8010070f0165032042c1500c2e0343c094898401c00780c000b80010001c0d400c3c10f03000059410702c51801d40720f00504103000900e540e03881d41c00c4600c3c0d15984500d0030340315092864902d508174480000c25415480c00000061540f0030540503481302c1034022070302c1070040d2650320039103014651110340030085603120350f8000c0014070115001070000d049e01010501e001c0140044039410311042e5945486c2c5209525884041d03648900125090f40d628070001010480300c1c21164025404c4444c42a5aa4614100291510380251 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 307845062 1250 307843812 307843817
    0x109020925020a0c0b0307090306051f08010b010c02011d030d0815040603150f060902030705190509010806010f110105360604020f181603060e0601140c0111042301 72
    0xf0000011548207480e440444150365a810f41e40e60303550804540302c00159000503d46414001488403c03500300d000c0801c075041401c01c0701800750b0780c0c0c40914240c4d03840780d14540c04106803030040009944584c00045100c0302ca01300e021481716140c8086480c11158070320300400503c40105010b901d28010110641c92101142c081c40250b06646501940310f480c10686005070360303140c0c180480c450007908600b000302008032045450b4078007c0c1c4080e02d154068040c8101c031a5010300000810346c06807003500c0d400302040e900c00000d6501d80f0010b407481e210100c1d051051200e500410082007a09005582c81160b1400030354494204010102021540c0d01003044103a5031542c14000007030b0b50000d0410390058040310621205011003000c11141c0b01c2180840030f100fa01c1c00d080000b001e01d180c121810001540c0e40c200704007076589009040c1013070142c80a034006103070541e0184240c4281805001c1c40c0c0c011400006581086018000565003c1e42c40781c240592484040000c0c024200219110ba450030f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 307846312 1250 307845062 307845073
    0x1e0c1e090118200c0601060801030507260307030903020102060c04060806040c030902090403020105040308010b04030809040507020313120501050705030c030106050f0405041a0f011b030809010902092502 89
    0x19400291540014001d98450540c031800002c1d40040a8002c9580501482005503440d03a8aa030051100d61000700d004130684a4800000b6110303102d4043d1078120f0b500f0502400c06d1300c7c01c0c41a42440d10b002d0308080c50002d90510092206440244000e045aa2081e210f040e419031a610019040000040c01600000c030184410030016401045042e03203c00201c030002020301003000c01741d00400e19404065003099540e8100010540c055000d240164000e44911219a036181c2846e242840b60740401880a0700901c00006a410550072694020880380181e0b414801c0c51907401d036001c8015849071014580960260307041c0502803054941207400b9260040c590300d008840764813288410301c42c0404009000a01800c003800502c1070701c015081c02001804a1120200c107080c1c01540001727614452501c0c0d07017540485600401c201440b590b100d0001501000790380e102600d1007038000f0b080c10090354956000c2d000590300d40815911079031503101c0c42041d1800421003261400e10f0b901d6000c0540d84817 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 307847562 1250 307846312 307846369
    0x91506081c05190305090a0803011805010504021620130f2304021005040b0f03041a06093c04030215010b19031503210509090a0e1e0c 59
    0xf150154245507680f03003030104030303600d81030050391030183d0100020f4070101021001242090034500702519107080040184142e9072036000700801c074441c0d0700d6028001c21010081500040c507030f05040c048100b03402c4182010000500100309401407001210490315602c488062594a0390710400603051042d01c42c80c10761414250011032403142c050000781c481c1600d20044440c0a1003141100c2c060b12102c0611038a445a06081000e16002a901101c80200500e00f800980200d644058402c15008003d42a0368035804030400d005c040c0f209500c0c4107800042d6150407004601e00075003a610700c1e410711741100d92506040003410a00d101c5024000360400200402100450701d00f56400311030308040520401000e450103070002c081c90074a0301d6500d44d00d11030000a100040f00860340100040c1c0520505404d5030a085400e441103082865110240c00040360b2086242ea100c0c108440082d0101d884880c00f0b50100c003442018052a40d140364024044043c0505005078000c0040d01c80e41c3c0d50b03200702040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 307848812 1250 307847562 307847587
    0x5030d0f020301081e03160b010e06041a010305071205040503210708011401030603050a03081f05030613020d02060d0e1203091b010201061d0420060d091506081c05 72
    0x50b0801d40c5440d51580c4080d40c6191805008447d1801c120702c0104450141c54544030340c07007090901c6020441c2d06120005001030800b8051040082c641124103440b00802c10010f4005210203002c01c001c11100792218801c1005520503140a503000c3e0008680303581d0610901682d42c141710142c01c1a4034000014411081d030070100260650710350f0600351a00f4040140102e00420a0b540090042d10901010707030305140d0040c2c0f105008000c00031007400a10301c103484031901c6000340c0c486c4503003542c04000080c08680666118002441c40240041800c52451300040c6950b000300c1d0348000c40c0d80c1d03101d10f16540120100030714103c69407031011003410b52a114084549908650300ca4142c80243c0c0300c0d4910440e03100303501c0000640300c01c104c8000d0410014001100e0740d2400c5030100c0e03100d0190484110b8504a4000d210a605002004280340c02e40000042018080301c4008451800003c0320741c0c000c8000d02d00901c0c1c0030300250802051801c1d0000b20b0312500710004c00c1c0d0030092203001c10044020f03d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 307850062 1250 307848812 307848823
    0xc031c09030f11060d0c030507020102181c05010c0f030605010306031a09012012060f03060105061b030406050d050a09030527061305010807020d08011401051605030d0f02030108 78
    0x240c1040080303201c05041d041520750f144102e90000c1d400000028510f0b41103040d0741c0b08501d01601c59400300800d699584e0164202d1044640c48880607e4a80480d00c0910f4000d11014900000c01d051302d03e40d00381592203900b9100000402c0c0c001c02d0b074191121510300c0c3d040c4216002440240303018030440c3d20310307142c0301c6032013481c6404841007400c2c40000814980094000810041d02c0c0001041c19100d20001c0c0000d58100400c0c210110302618007040c4907240400310a14000d2009018055a900e02801c10040e54891000c0b0102e0040050340f002c281d400a2018000422031a100c041d59807448908031000c50f80700030b00000384070b46015040c002080c0e100b02602d4810b0302d80f0601a149106100580e403002440714030301c59010000044201424911100180c12a2006e0301e80c425140c4070782c035090341c64075488030a0300000f440b5500100101c2c04511408280008103040007441d04401c1030b5102244412000203488650000492500e000001e00c41e0b51000c800e0104214110b5040030115900c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 307851312 1250 307850062 307850069
    0x203040308150d0c06030b0f03010203010b030106050a0909050408070b0a0507020a03030209010c02030303010311090c07081c0b1207060f0302040f12061409010e01060b16020405090705060403050c031c09 89
    0x15205030110b8010f4440100c51502c070b81d00080c206070325658a000050261404010240c050564a20000060704050003601c0c1030703071185c007151401c503801c024045074260408001c6404100c1144d80001d40100715101d00c501460080b42400d90b40c402074144002080070280401a1403844e141c20082d210790f001c030340c854007258145805683e80c40040012a08071400d90380282d40360100100020801c01c0ca440c1e40e0010707510035100d810381c51b9603c60000d05580070b8036401803c0c986042088a042203480707907520481c10440310340016452a114007080c812003440a00d0003850388a11024031030260030071a000134039095403a0540c07420b42407500c1c40b90300c100707144a115400c041d0701e05190104012508051a07940b43d07a1a610403e00d00b10101c2c7d13010f0324229441300c140703518210011860780007000c1100c02e01c04104100400704515682404010500103181402c140200240131035141e5545004100650007100200342840c00701c0101818111224541d80d0344c5200b10384070301c00e0b06402400c03c6088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 307852562 1250 307851312 307851331
    0x1206010c03120608010e0d05030603060a021c05090303180705010e041e330e0112020d0512040f15170a0b0301060608010e070801210219090e060702010203040308 71
    0x1021964034050b1448a2102501031000d4103120700440d12450550020f031020481004589031502c0704170044d0303150322094810940540000000500c3d2114940051021403030b0025070030b00d001c42220100048890540c8d1910349a00000280903008040c10030615905103224060041285081c00207060310701c1c0404000d02072511524000007250950b205030603018000001806902a0b1080128428261007170310460544603401d11020400e41741c6a08060300c9640164031103503420074920f849126000c43c02240e0102909100a001034000c0c440840200d8803c20460f440b1400c0c20402412034421350418101841078020b00d00f900c43d4800030b04500703105014100c503465140d40402c08042c240144a0f80d4042d820110001141a44882c0c9207048450483c042e040c2522021030880780510284244403c074641e440440014280030406108810310041050240e6001010254034001055000c2d945040c0d0790035403044040c6081c841c1030341c04503aa1000310300d580f40c1503038050405080500380e80e82c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 307853812 1250 307852562 307852577
    0x603070e06070506040302030405012703060207050307022107060c05030702040207020a270c030c021221010b030103060c1b0314070602030a0b0a080d050909061c0308060f06120601 79
    0xa98554000702e501d4160001c00f507864a00c0d160070060b603642d000b0301c2154001010021041c9a4009642d4050140c400d814a941c80c0d9a01d161202e20194120920a8415001c1001501d005a94080404c2c0c050022680c5505a070440c202c406e07410245254800824054009103a07400544080301302c2d110158112030042c0c80301c00c0c500100340c80c207005810111241e110001e4264a0f507600440342100d421688a041c01882c0311403004805031011b2292150160340580c80ba02024000c00700a0250300091022013062113100c410460011102039010350120800040184144901070245050b1044a41800304020580c01c000946202c40f0180103030401c0002034025803108030303000450384040c0d00f1000541d1071f400c1410f2104010801903484601c10500c59030300103900d43c6c000c28007900b031203410b407202400d0005080900011110081c0020f600500210003264081803940740c1e540600c0c042d94440300e980c9058010710040750307051620300e881190103201851a500c028400f081e0b00072401c0c6003912 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 307855062 1250 307853812 307853837
    0x11707141207080d0302030a05010603140f150301060b0436020c01020f0f030a0b101d0a050d0b041b051005090d05010c0f080a3b03030709170c060307 66
    0x2d007000e8080e048000ea42c0200100590255455005140200b244903010807850342c1c1c4450a400f02c484404100c0c0d154021140003c01c842c140781040350b4030804c02500c52600c044000002402c450403070b0060001e6050108090100341c0010f10044c4400684881024441a0061030191003401c200000601260005001104c44000b074065500d0020040c220f15160401d085900e04580c2080382c5c100c081c2440c015503180d1514081d0030701040ba01082e1510110704d81e44040e40c5602c6d450040c02c483c1c000c2300b0f2003000181c0380c0301c422032002c107140120703000d0b4144e0800d4540075500c02041086148210300103c402d10840c1d580c011640301139075403030410315a00c0a02d000030071102001c1c5840078045520342441c8002c1540c0000c2d000940385c040f565426120b95036410003008a81c241c01032040b040fa0001c490700e032452a503644040280c1d180b200301c071940742c140c0d50025181d58402c6034003400194004508000c03100e6042c88228100c181b50028160890300c22001c11018080140703540c080144468440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 307856312 1250 307855062 307855099
    0x306100309060603030e040b090106080c1303120207030302060a021801051c0608060702190b010e0711121206030d0815040b03100501140117040f080d1401170714 71
    0x20740c00e40d8001d0092024582e68100030300f1a66400c00b025000e00c2c10b1000c480141c0c6800c00b41c4a0680d119904e51390030740d07104d006d1810299040f084d49000e60090b22107001c404503030304440d00014500b041e40117280d00340c10351a0090406201814010b02e4a00500018900d0303040c2200d540007580c820b01c0e105440d02d0700641445100003030301c20564419440c20b2400b0840400119050748100310315001c0316001100780b450507105044100c80608440544801481070422545030720703810215910f02101070340703030000d10982000340c81d43c0c9074a8400700c0040e14100286401c030350303d07034008400c8002c0c003205ca42000001d041000c0c010304c40c000d24000003040f1182540d03240d010034800c001c080d084604000300c1c0b038005070081c0028010b0142e02c944101031100c4c2d5600c03a1100040c018820080711999441d69501c070540d0001e40c0c0e00481c0d014200740001b15a81e5184d1090408402640504141c55407400c442420b94107549103c041060b0411f40c0180315040350040b980900c0c00060719000e00109045040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 307857562 1250 307856312 307856321
    0x5070210090b13080f07050f10050c120a090501080f0403080c040f03030905030c06070503070803130204230c1e0c1e15130209270d050403170f03061003 67
    0x25010240007150803c02c20100b0224241580d94050407a400094614a0702d40e44803890b120b00c950040e6000000f80c0c1500304006040b01c0380c1c070f80b818654145114042c056041401ca00840b24003904041401640c06030b1200c1000d00910003820104210b040c00740d40d603c840c0100400c060103001d207a001144004040c8400c5034010003011070a050340c03d440345001421500c01380b01d202d200e4400c0301e102d00b4281c43d00d0011101c0213039000b0000c0d03260941c4c2e5a5100d070950001410106650a415070000158449004810000784601c1300d00104007400c107840e0300d0b207140103002c14011400500a2000c05102803640e041c1c481d01c10228070340c031030000c012480d182845a02e201c0c48511401024056003000016101007400f1b010a42c41c0c025548485108290101412010394452184004101d204841801c50543d600700c019950804a0000806034507224000c11040300041002400300203100078408650304500034661041c0c540600114080800d02000c0d108a100d080c00f0941800003078000d070311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 307858812 1250 307857562 307857569
    0x110a0e0f12010c020609190308091207060c081303020601050d02060408010e06090d05090f0d110a0303092615310c0b09090106140c06010801050411100507021009 71
    0x4050140e42008511070103000700307000080c05842040081001b02070302040811804201003541442000580c034101c6042030080c26007070650142d082c010200d405191b00a118050281d03101003079454055030020b00d806001441b20b1840c5074982800030001342d005c00c0c00f41c11144200c40c0c034480100c2c14000a0624404c550001d80a9807802c5050550904042021481080920141c0d0000e03503074000c0545e030714810f22080c0d550202542440d0003852401200d1092400d0041c50003510080145012412024950b00140d02068402d4400c1100402c2c40a0300841200107009142c003a0850080c01540c9446c440a030400c64000300e0009800390b407042c52040c40900749081101c100744280020326240c4030380b45406940c170801005020404480f0481110070030680642540c1c8907a281003000c40c1d101121f1070030b00f40035190030440925074001c1004480e029080e0600001014200352030300f280d02280b0b440c00310f03000742031000c1d40403015908081a2a84690140c0d542403800341e0141c8200e0b002540340c0c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 307860062 1250 307858812 307858819
    0x60906061b0102031e01150c060f091e02030115030f060b0607020a0f0503151603091b0605040e060d03120b06040f0608090f19020103020711030607050c010609110a0e0f 74
    0x170020880300600300b05403414422030401d82280d89882c1480c0580603213158050100c0c103070061a80000c1d00590000100c050380b04000600e41aa0b546c034810740fa4050704540c5204043d0700030840662038288200720b4000c46003205018094515500d2140d90594580d0240943e50707283c4d03030040c1c2600c4680c22a00f86e42c1d8028031921109499220180c1d80710440d00a0a00901c54256a14214800781c1085030046080c8007811800d000d425031304030701400e010700c021103080c00d44812501c90010304e01400780140c1401c4d00d42d00d454a05020159a581400802c3c681c800c00e118000c1a005c203401c5491518200c1401801041c0354130680301280313041c403903075000544411500301e00060803035000b080c080c00b80040c08150341d003400065041940e00d034948818045a88010000300c1c00541c0a9401411801d20902e000d031484072400c00003d081081c125410300108a001520320010b48003031040801518403204108a0032072034081385400d40c080d461128041c00558003002d0040d80e030320784030000c01c0980103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307861312 1250 307860062 307860067
    0x40908070c0e041401091a070c06020307030b03010e16060f1707090302040e0607021b040603080c06160807050301120f0c062012070609080f03130c0806060906061b0102 74
    0x6911501d02e2403030403101a2490350303110412498299044c041c0211098102285140500030501d07450704404000c3d010031b0510817110070300c900007907641c00a103225500d151070000f040c8503084241400e54070f40c1e00c80010b150300038003699481100c10216140c19a1854076001d03d5440f150103040d145e120100400140308101c20041008a0b64402405019030384250f4090206014002c101039507200c8c155001405608240c042c10b0038094103807611500184028400700710242c1d20307124101c0542c070594000d02150400b02c200404943c1502c4916002100c61501003820f241400c0f0003030650106001d0038030f401c49001200c900740310204c0c0241c040307240c1108400c41c5217a81c3d1a4060410148090a42d0403107200b509080110035003c10b03962140f5186d14182c61421219560b1100104495a800c4869090500c5a90000200003024610801009544c440c2002c07aa05204200c2d4030503611488441d40a001001600e4551003241e5800440c140c4c0c02a440c0c83c503180b00c42d064042e40c0c09110b070103513101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 307862562 1250 307861312 307861319
    0xc2105040803121b0702130203060103141f06080c040e070e040e0a0b0901020708030606071e050304081507200c030a1a070c03050304140c0901230402040f05040908070c 74
    0x807010b24a000300080c0d4607801d0002c00034062015103000d90171019502c042030785844401c0504540003190710030360515001848400314940040d0b91031f03042c0c6591130842000116010100f4818205c400602220706245141e1324121850008074800c5004040b0f14404000106a42ca402820010f13406203004000380404610141c2055a07604000000d480000e8608045005034506100305d45441d0b810044c010b20390b680710820702c01f250f8440c0c0c40480d44400028071150303a0405c190b81140f2950b01c00e10240d550381e4500300e8041d1401074403030090055a10b43e80b0034410070642084114841e030302c5c218800081c40310141409030a1044a0f9205a0140100c00840b010407101c440400fa00b103116480c07140c5075440c4c88c40c003202c4841561070001c01007602000400d0216240400c3c038141c0d041c4420403580d10042600c04101e4902d002e17400411701c0408010340038a811080c09500b0b228210544045043c280340c03102c400c081e00030300e105c0c0901555170341c0c079000103015451040762661138101c900f402c40d06a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 307863812 1250 307862562 307862587
    0x3170702060f060a060c0b13021512160f0e010201150b040602210a050c0a0204090f05010f0c08010b0d1506171e010b1c09050705010f0c2105040803 65
    0x100700c62a1401c440c0b1907000903902d15121544400342c850350303602d1580c90300e120b82c1e0b00d034001c2c0c101508403550039854020143c01a65540140350303090b80c0b101c41090b20703500e403a4200202000003034100f0035443c40000016005c41d5001d1159a1382c280c1d5803502c82c0c0c4100020740141c3c01003e006490701d01345080407002045410f441e00c018402ca40465007225035020403221850211281d4035542140c0503810000c50045910810251030003004030401d03038040010660004040340e0301c0000072103020020212a1060080070301c00e691100c5003052083c040401e00200080c040c07101402128591b00c008030300320079031080c1a132040a540100290000d242134940c60302030551201c22000c100781240c3d0400107070400300d001e81408001c4c00241168001c1d0303402c0004454844d04048050f2240e1401c01101e26903c0c1c0c400d000d10142d40780150b0140498500702000100800d58004407507090000360510301000a07801401c501900c40038894060302480005012a0244a9603004a80d10700c00490811102003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 307865062 1250 307863812 307863823
    0x6010e09041b060314150604080304060819020304260409090f02030d1b020f04020d05180106081518121210171504020a0902180418080d0903170702 65
    0x210b804000300c01c000d0340c548045060f07803140503a180e4041483c80101d402c0c40011490744484040c0200b1150034151902800703407031074110340c0c00380f00001c03815000c2c480c4140e4860380400401c400d801080d4510314040e10340c048650109004130b080e00000403004042c80c942c090070381d005803645007070501c2000000d0822030141e101d0081c09074401d0103524584016280942e8550502201c141c2480c0b41c5040703940c00b003010551400c58038913040381d000c10943c0003621f8244920b51080c0e030350110300030240c0d4030901010f08541d00e0390400303003d9a100351501203803000d043e26100d034490303160800ea4a440c400441100d0a000b00700403e16101e00000c1001d200c00800c88250318843c40e03040e101d1408155071200d10090109100c400007604e600049000c02210f00d1312024070350300c41c1c0013410803615996901d0b102c074102e90100c3d4004190034007002d40d64a40d4503080c0100c0945841c02201488011402d884d11919403050001c0c12680707540e01d100e020105400b8221540058032207003200d4000c0e24064502a4451 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 307866312 1250 307865062 307865093
    0x106081b0901150c0501020f0406110d1d12120f0d3207030b120a11060708030c0706090503070b010303031d032a19030219050606040506010e0904 64
    0x1900d040218114141410001d040750701012030038203401c40d150000d40301560816000d444139502080f03281c01f5146080c0003031006041d29622041c02040528025082104000e418410083d00044007400700f44600080750741154215921044959540703010343c41d25081000c001044d44000c2a841c0141c0d00e2080600070390b400028051180080c220344203142d08440030b4011111901400d0645c410030407000c0034561149042c20b00042e0706d0703030040026107840011041200141e100c4101780040094810300310803105c2d4160f40d89803c110059860f0185c5020013081140c11071004103005040c01010b07003083d240300e0340040940341d64030814100107020040900003540807a05110504440000e5210000c00390040703000554113000d8130510900400c0c6028045036212014110240380d80303030f414000030f4202c941000d0031210540907854041e0034148000d11038071913580084d140101107000805d41541c03001d03045500003003c0e5201401619520780300115141c0180da00c030100020001d442d041c0c901d80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 307867562 1250 307866312 307866343
    0x108010807061202030c090a0e01060f0809120a0c0b010905040c0b09100f0e0a0e0103030f0503041203020918090d11120702120304030f1b1418060a08010608 69
    0x1a038956204541d120464415080040d0b500400c000c02c140e40707a805160405d131091402c40c5044c03101c0001800848640e0051002415180c00421000381c10a10700141401c2c1d07800d0000b40b519004009030340700c51150244000304c070000106455858442d810171840c0340c1c0d002c45a1542941c4a9002000a1504a80444075441a0b200c042000c2c6000030649001d460000c141190f042141c0c0c070212582600c0729940c500b8842c0c00310508613942e031020114000b803da82d998000c481d43c5182001026024100c201405014042003132001151403000c110001b5030b12800e0240c2d0f11801036020032840052030007042c402001c51001d0000d88bd1012034000d491041c0c1e5640c0201c4c0c90146414191608a0b20084041d81d190801c610801410300240003010542480c05032420143d0340e448400e03000e01090000c0310300380d000912070040011305146500142c2814120a00384400b00e030301240400404c03020081d034810348440011748503541c8800319005000b01e00300038000750303a0f100580c40c1d0380d0745459024800e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 307868812 1250 307867562 307867577
    0xe0106090810020403020310150504020c010504060b09130303150509090a06050906061806040b0d03020a03260103080d1b02100f020c1905010207050d08191e110d0c030203010501 78
    0x540712a0360007904c0c00e494000f005002c0e481000d400400003042c0011501080e0b980c028800605c5680340c1c405410004210070021895152034503141088488045040b442009800e0901844c510444038950070694503080000740b4400a5030b202d184083c240c3c0c00242e0013100d80301008100a00815030088040c801c40043c009611441612511184100c0310f498001a131200200c0030308000240c810f80061029100083c1040008040380f15490036030426000f40e407082c545072007090f070b001014411144402855589403600031420000707103401840054500311006caa0740d4155105680843c0144000da03014000c100582c002c040d4480414000b110441c520300013455032442d580c0d00840d403620072403038090550300318034240444e05801010380a4500d5903080c0800800114100a1200c0c4044a51524500d42ca048818004840b8606000400b040d060400104446040c02c41c08010b01446640101d04444c0d27407440311650340035070680c500d01c44d801c1c410390b503100d1905030307000b903041e241c080e07880c50f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 307870062 1250 307868812 307868833
    0x5010f03051b06180d0803010906030c060215060f014406060714190606051005070506240a2310080f07030906020a03050106120c090b070302070e01060908 68
    0x22403102c041c0319094212008000000c1c0100000c100d280e503440c0001c01001c81d0366159102c01d0000c2e0400d8101000c800e03903481c428410f200c20b0110210051039188024880c50f0310800d106000e000028040c14096245600c145045a00913098614a035640086900d00410204642c0a0001c0d140380c4042ca4000040f0466282c2c03a084a200e52068801401c2d01d89015429076616640468090b124070290003840d2442d1b42807800c00883e0201903010b0040421510f04141c1003241304011010460240981040500d000607400b181c03160380880d0f240804a0542100c03405424444412401503511440d0340c0d80102d2001c02e101c100b0445140d108403103076888007481e01801301c80d00c4c091401e0f401040d4200c1c00112034030703d0300462a600914616010980490b0b55075034000340e03003200001001103912000184100c60381303d186190442211681801302906d400000b0b4286c1c1440d008101d20380d400015808141030080000400401c0005001c059540e5510030042c0200964002c50559010741d04520303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 307871312 1250 307870062 307870093
    0x1a0f0a0c05070f051903090603050604091e060b100903050f03090a030b07050904020c0f101a010809031b070e0702070b271f0e060403080912010f05010f0305 69
    0x80656010070380307800d4640005600c580c401071090f882c0444540c481d02100703030351110340700300814100f9219450700c2c1c440c1800c004028041c0d62000300700502480c603021213072010034800342c043c1c6000ca54a03080d00400080c5401c5c10380203065446d14a64000640c40100005075510200f5282142e00840540320004030300520a80c8034802d8080c4944c0c01407600c913007840444c10340302426800220608080340b80c810b59801007410380e00404135000c103e8214070380f0ba81400005115914400c903011004001c50043c1d4140c0101e000c18800241c0e04101003c4000b8030b0b01403007003044078080000340b40e000303440900c5041529911000c03806450383d4900c4410100e03d816000180c0c1c002901c2c508400c0f9810030002c42400c0b01100140c0885011480281c400e0800305e40350050041c441e40c20071030800100c81c65454025000d08841200300c0c1c05404100000c00220b50041d0a1f00c80d1820304981003107960082c1e40160b40034010414400451924120000840054807148075003141d1041d0182c4060351902c00c0384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 307872562 1250 307871312 307871321
    0x61e0412110a0602030a1b0b0c07031106010b19090b03040b0402010f0216030201030c120e0303100f05030a0201030c2721020f121e211c02161a0f0a 65
    0x803c00507034014040d03405c415004200424a0108590b07180030b000f00180ca409481c003030290346484d82040300142c11418180c0c002100030760714400030000c0030203500d800000d09041c480d4602401010f01050903602c0c2c00d620601e803940050540c40001c541ba414503042919140b00c00351422400b150364440c2d200030a0740041140c481c0301d03800118241c4114516001500078180d20b54100c020810086c0c19046440801e102c0d840802004200550316458920031902c00311459802212403130141000030090b07558000348062181c0e50a18010521001030342c42910140c0d100704110b200c115444100048204a101010088800307020414400100609081c1c3c007603640b2600294201c0680c103010780c260b0a095102d80c40300c0c140d10048802100c02c4d158880030145c5106042042600441200301c4600c82d015691401243e081e00c031145040ba80d08089003020f01c0581007201e440e6004076107480303d0410001040300aa1300041d074090400c200e10003000d03230040c0031151601c0d01e20262004c00c1c0e48401c00c1c4074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 307873812 1250 307872562 307872569
    0xc020d090513020904020c010504030806010509091f1d1f081e030d020a0809100623031f020307030e01061a0304050106360b010509061e0412110a 64
    0x2200c00d1990700304414000c511114140c00800b040e020030003004a500c03684000c04000c0c070028000207280c100fa2800a03c4054080c000604100c0c1c28001c0100b03581e540401c0d59045001c07031128070f5502a81400454042000e584460902d15001d118030000c000d011580e28810b106000c0040031089140807448104203860042c82460f80c8001428072150740c19001220365011407000316030514007899078104c2680e020b5040040051500c0050100000341008161868081200b05109181c01d04a9071042d00c402c0091010a0341c680042114260702c09000f200c055030301c4c9074594040b070484600c030040a0352041d0350390b60001749005c00640540d903061041400b940d04610403058602c000b03205425442c1c0001e08192280c0d540c3c2c103000030b450318684515194007001c00601441114040e00320701d880800012000702803e0414000e840c05a91247c219400b00c801198019140c05e840c031185a888206600c041c0346036400014041001a8442c01000c130365403107007189a010619800030b20856403410702c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 307875062 1250 307873812 307873817
    0x80a1401020a0c0305090102010b06190806100e01080403090b0d020405120c0609010e06040b04120b07090806010509090a0c060201050a060504020906030a02160c03030e090603060f24030a12030c020d 87
    0xf00307100020b0300c6080201130400c01480045104242403001559a51080c542c40e2200300c4414002c1260a400c6860030b075002c50200d50003142d40000c1da80c080c140d0303014000d42a04200c0301d00002002c0600480c4214090300007104c407540c40c0e40859240200a600901a00303220f2001c900e040d0307511010028848560000140c501e50400c6a041c005444102015281c01c0d0320601c180b1000c201003807000040c0005000d002081580074115080907240c51a0144c006020030060700402c2c8184980050044c5c112501581c0030307440307980c0c2c104515092400d044001403850340c1c10341000a40301c3c2d05401c82d5008000f54602000020343d0740040004a00c41c030800303503400050034000684403009039400740000d068130002c0080c2a002540e9100b40d4020250030403408903040115039815400c0288115500a0f1700703400901040c101011128030207a4024581d5814180044860b0142d0811004000011070050200c441028051422071800c2c2580070009000900e4140d0104410b031001664030399003400358 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 307876312 1250 307875062 307875077
    0x308040309051903062f041d010e24030102031014060703020c10090806130312020304030206060f010201021326030a120f06030b0705090a0b0906160c03050601080a1401020a 76
    0x42d40d0707000c094011003030401c0801c1611440c0c000041b018410115204201c0b6410964403401d20a40410301d02c00c2010a5804404210050242e2141e02c620940c01201101e02c0c0720200043c5a10441151098074144da0554008030500000404d20407104080e5000302e03e4000818511400f1320800d8000c002014005a00a03401a185401c0500a681c8012100c0c54404445a01c034150309181010a0f900d0108888110300c0160074135912140680e84c03048202c0c4207519500342903d00035699140500700522603095001c1c0c040443e8001d44c104c1d1301c80424002130a86490b61004007560f0700610b4410002c000c0100c01c00c94510030f40200495118140903200c43c01e1107040020014010140e000030202250ba44a6000c008103100c580780610426031641c8440d92240c0d43c200b40504001c407640310552012052200000070343c1e076501610b80c8099100c04201d0709101c0c2d82412204504580e04c0545140103800020800c9113010900300d01c89405429085140040c2e105070600301e01c03d03d0106000510b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 307877562 1250 307876312 307876319
    0x19020f0a140c06090f010c0c020d03081f080307050606031504033203010519060806010e0d0f0f210507030815030610061403041a13050a03080403090519 67
    0x11028031001d100010038042c2031050002c1507030b240000503100c0d802280d10180754514110404d0260003003403581850b01000c003804550114903040d001c803500a083c46007000000d80404a0a0503050240010305044100940d9940800352694807500c012341c0c40340500750002d41c10781000240c07a92031200d19140c9452540d0346480440b4402c2103106004075948a0801228000520101640d01243d10100b0720f80d49524090070007418601800203940d0080710321104100781034126070480da00081c2820480b103009503030800500c2c0c1136000e000050850000305440d42c00d010710040c042680a2084070403075a40780f42c414001c00d0344c004c100300800c0013420400041000074861564150019410005d0380102e0804000207401d000045682807000659464200056a800f186100d003c041a010351465414191501203290f41c20213800e2220b184080041455407001c0700c000d00040d1f4010041d12268960340c0340040c2201001d030fa013a00040d081002c045040d01e00003803501d80c0d200c200710103404441c0c42d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 307878812 1250 307877562 307877567
    0xc0d0e180c16030519020106150216090b0a0e04060c03060503210d0605100e0301051506040306020912070e04020f10020d03051506040b0705070b030103020d170d1419020f0a 76
    0x20a100440030041300380f00f1401c00303107140b8074120644c003400e030000b186282c00e01c2408050304c10030007420400c552048848150740c061510041040c0da0000601142c01c08540d0041040b8004690050b03500100c081d00b000280081640001604c031a00d175004d2144590320030415550310140c004c4140da000c000c1c3c00c041c1ca8108a14014062401807281c08910503a5603000907076480c18042d00030010074495040c0c51071a150a228a90748559900c18107914210a0808100d050040e4003004000e954001a902225031301c080104c00c0982999040746e212a480384000609003000b503604038001c03521004107185624021002500f4800c040e801054840340000e000c502902004d00860b418a0f403114050215803101c40051024284030505d00380d0314161460f00f949829111b03070200b810003105000600060392061441070b030098010200500d00024020502003910034040c00301c01c03c031f01d054070826944c08501c44e1903100b0008400705810302000381c0c004400b64400c00100340344020b01000070701c00a90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 307880062 1250 307878812 307878847
    0x1103011202180a0f0c030e070e0408040905010b04060e030303010e0f3319051c030302040803031003030e01021216080702090702210f0715020c0d0e180c 67
    0x14001050b1080b05121030665075600e00c1c05541c036440054481104001003490b9000c1c40c0c40041880c98208034580b022410b080d218000c81c0140100030075410003007014452040c095038042e10010b6030400455a42e000e0b15246c5a001d480350f2004180041180100c5140c04010307a0b0486280c9a114403140d03803103904481036240700030080301800c64800710021401c0050305218180881080c0754108182e2143d0030007000161407461120034001190050019840f002c0341241d030444e5a088100d901411840c0c20b03400380c091504080142d201c013004000e494190b04000004a81c001d0304d03502c080e035003c04012a1985414101400402401c0042d105602c03501100017800501900c29641401030a0740000d20008007a602c100c0144d1201030312036222020008003604100400c01410725208a1114807503103400351480c00341c41c01c1c5c0d040e000000740c0c0609404031410201c00c0070035615a204403101c06000102101c216a004004022001d40211400e0903894010f42641c0400c500b00b0180406407074100b0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 307881312 1250 307880062 307880099
    0x6010810030b0114042a031805150903160803061f08060105090409080d020c011512080306040615030e0c01090302030703111c0602030108060f040206090409110d080c010609110301 79
    0x40c3c0d9100300d101b074030103060304046c0d031583c170b551404000d10003002004041c0c90808038088005250400f80c40005200003c032141c0032351051490841c2560343d1302e241419800386e460444101d203400c0c140f110801c40e040c402503100d40003c44060480c25141d9034882d81180c007072002c01010034618000716403d0740c02140504001c950090010130041c1e92680c5014454000f020106411500801c1c200350b00c110a0040d40c40301c0c608142d13800c503d0784c64105039106411070307002d0103800d42c040000842c0303507074440d600708d00d000d40000745055011480c4480000c0040c02e600307555913203a0144131601c25071980700c0e204410071a0b80050080c02c00a08546645187c03040c5e003000c1d01c7d4460b014108040c40b80d5100e00c241c2c032005025900043c1c60358588101241050001001120002c51400c100701c01a6102d0081c2c5521100036100021500064503050400d940c41c0000103600104d110000e90410031000c004013059465007000340f00f09560ad56030141590f95141c66882d010b0801c1c001403080100740d41006485 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 307882562 1250 307881312 307881319
    0x510080a020f060c43180b0d050a0302060609010b0a050d0204080f0a0510090b01031e020915010201060e0105010207170120040306151401051810030506010810030b0114 74
    0x80c0840c0c1c8051034034000e070500403102401d5070900740c44501010141d9030107041091101045c2c50200060300150080201d00a084124444005403404031282c0d520400c16000c01502c89401c108281c10050b55611b680801240144180e000080711030501c10103040c100c46080c044241044001281918960044942524242d90900000441540070040030707080c0f42c2100301800702240a410200d040429001c01208042e0900b0046000200180300703044c110b070340283c0042c0005d569410300015800340440003035401000e010a000d80211940b031500c3d00748409030000c00c00d09596241156100c0b00034454940942c00260302005a8544039038000070710600388000244080c9803103a4607a0071500c0114407441c0e680081401d00802c0309500c1001c0410481e2003050807004d10703016107039504202c941121810098041005215001200400e450350440204a80d1821060420003030007001c0484550340001c0d10940031882a20b000007030001602d0700100c10000d180e00704182c1d90146440100c520380c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 307883812 1250 307882562 307882567
    0x32009070302090409171b0105090c06090111010603110f031902191203051908270a0804030818091302210f010f050c0c0c040b04060b0a030c02010510080a020f06 71
    0x1d004074220340c141c030503a00c01903840c0d4a00d00c60312031811615841f02640c1e07a1404040c04001e0320001511151030b901207030919601c4c112000100d0740c60504521440080d03081c40b1004c03040104112648100400944082c86288081410140d031110550104076480f8104c03c10b66001d03007003040181001e00005014021460303503604035100403900e01c40b42580010350108a150b01c4509107105040c03000b08900d858919400c141004820844200d0b1a0800c01540c0e418400c0d0644810300aa41005d5000030500340c5032a40c034100550a9400351000d03000402220707080040900c2c003540da00d80100c4c921025800d02d00c086600b44501e5001c1c014003c151034440c5028002d004d14200607445020f485800049800050003000c0c1e0150b41c405006099403803400e21450801400009005c0e03c08002101c010402d80802e0f400f1a00801503508402101540001d00050094041d00b210901081c154001c0005d40c0d1070401c91007101c249809040f1003500004154005803500d4000d082803100c00501076807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 307885062 1250 307883812 307883831
    0x120e0109080304030e040b090103120c0c1701091401150902090616060c080606030702032b021603090b0f0307050c0f0118112b05010917040320090703020904 69
    0x907560030480d01100001c203c11515030660a081c00398010031642541e901c401541190340700030f64074070320041d140c0401080e03041000c04c0c00f1032905c0d00c0000b03240d00c0e103070752081c0b0900c0e10b075403030103002505801d0751000000310100018040512604690600314182c40290341d0500e504034000e940300329103281e4808014082c40d82608030604043c651a0f218160000b00340c2014403000e04245801440c56103e920103004228900350080115048035110394100325404d8648251160003802c0710ba042e140e1a40f0109900400c00c1440d21412150344c000c0e11442903013692108034000d14490100114640d000034008551118043d80141c4130140700c0c00d007543d9a030800004190300310f980f440f58111303c0035a07000840c001d0040036041140b45803415564101c2010082d03004514481500301038003485121b00541d14240310742036200c56a074030360106174070b0380c010039030038454003190801e004c1512880c41300c00c0070300c00740795026204589000c4054110392459445d080e0940094001d40304164015445411a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 307886312 1250 307885062 307885073
    0x1104051018080d03092108070c0c0803030f07020f0705060d050a09020409051b01081608062e12020c120f040308071a0c030108070302060a120e010b030f0d120e0109 72
    0x280d024440c950360000d174041150a112003000902c59259445117a05010319104036800021207502103002c3c02c00800d0031040d440d00c010303007000c1644460400d01011081c001c0740054002520b003d018a85d081701d0b050410341c880c1548881441c0709496111000700305c0070ba804800c0390000740d8031070a00c240005000c203c9401007400d951070b0300300c11101c50f0040c0e10f6a4024981c0092070316103513402864840703a01c1c03400201e00c9008803140070242d005d0140b242e00041144c0c4d12403004d5400440c4070300e00780780c480074510102c02d5004d400203240008103000b41014154000d0b68401e446040e0880c0d8028110350100700c140c088240d000c409600d0f60070200b0440840861882c17001404180d10455481602d14464068128a441c000e0304013078551070100700400920400203000030076207804494481d41d40c0700c071520550f000d00c04440003111403403c090400390103e8041d030000c60000415001da07501505100d2149454102010020300401d016040156014109600000040c40010300004d96220142c994 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 307887562 1250 307886312 307886323
    0x3091e0d0c05090112020a120c0305030d05071d09040b061302040b09030c0603010302090a020a1707030c020c040509071a04050a0305160801060501050f0c1e0304030303110405101808 80
    0x6036001100240304100b02e0500a03005401000c1407000304803040c8840d030005100d0901031190321154041da980e09824800c1c200a000001c69004046030740c0c3c3d0080354004805408203c5401001c04c1c403503070344441007180301c585400030490014942d480c00d0703441e5a1112140072015046541080400005000003c0035200510241100301601c3e5101c0ca08036040500e42426000050301840c3d040c4010070058540030005508540b40d03400140e2622250282112008084c00745540c8406079803050007440d9805911090719510140c1c00c2e5070910310103000740019104c00b0380c0e881105074000340040044181d40810b050f1a10603c1600303900d401da03110001400300c18a608251403907002413101c003400101404011006201c080300070300c2003502d040c001a01034000c02c11065441d4100103405407248030148800b801e20341e104c005820748030001c0540c10f81c0d40d4005000843c040391415030000300141002c0b0035503084950080c101842c8004c004400c684c103204401c4011075903d410f1a0100702c00009201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 307888812 1250 307887562 307887589
    0x20d0c0f06090f0512070b0d0f020d0506040b0f100309020f030703080a0f110a02010305040816080301050f03070e01030206280806010f03020901020d0e060708070f0b01051203091e 79
    0x460701d14207400e140607850001e119610040c032a000300300810200c03500100e186411940c000070825290110f16000d41301404400401048276440052040040b80103a0310082c0552001d940070001004210240b183d40080200120b5020100d20700030202944a81c01181c01da620103032001d58541e0140340481c4c541880c41c0c0084591900200d0407902c49540010011a4003045261881c203203c0d40a60b43d94a4031042c0001a0415484000040a00c40c1c88421205da0784000007088a00b03030201e0500750f0340d6400c2802050702c6000e0700d84020159280000c0d910041e1800568552803503481c550030011246d104485161080304038160342c1e000b2608100351485024940e4072007030010700c2c11400060500303600c03c0004090510500607507600ba680018200310055850604450b243c4211001074803a000d200344c018401c40000451100b0800140099003507648107050181c0c450740c8400401c040d48468003a50034207a842032207400401d24144001544811040d40000f10b4650a100410200e440708071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 307890062 1250 307888812 307888817
    0x6060904021b0c180f0c13170a0c0b180906040e0307050105100608090c04091103030f21010b0a0f0309021e010206070f0c02040e070e01030c0f0f03030507020d0c0f06 73
    0x2020402c40703040c89070301d41140302c04440640c1c44e81c0c0752440c554400c07500040e0003803010b50300100d4910740c8218550020405440001c211141d90b80100d0070459480d822400120707140c202d1b00d10f0001d5841e1510b019100382d150541200504051131909101810600814540c0d100f42c498600e90302c040d0083c401000020b0060001250b6403034440c1d440300c120955a4132000070444101d04112207030102040305102104221400b041440300b908003410a565900300e0107a05000002c2d4410440c13440c0300003400e020003668444240314501444090768003100740b03e060101c44042000000e0f040c031030601a03411050501b00002c0702c020b150081948100c203000d042c0000d10320780c11600c0d040d43e0100700c0702e5480f1400740340120b824410248014041c0400f604003d008545400400d0080241805600090441030344034052969503428040d2680026205881b0701581c0a20007190300080e00301c05805481d01621080d103807405035030a2111800c100802626007440c01074000c02d884802c00301da04014500b65 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 307891312 1250 307890062 307890073
    0xa0b0708030906060d03090905090705030f1006150f0c08192c101b1403030412020102040509060d06021b0309040b1207060c0503040e01060f030f0b0906060904021b 72
    0x2004546080001381290380710b00c442c0313024100000c0d4441d043c0b40503100320721004140394a8a078205450951180c20240d0b050154280348900b4460001d0a2038400e41c01c50b50502540e07a4860440a8001e01ca281000024110090920405000d0012805154841c1310828138010101d6010204215108540c0e000200c460a40b018400401203244841c02c80320380300302945640c101c00081d080406182050f042c003016040820030050070240c003081c040e402080030a480d0300710038000f5440f60300484d07084a600c1942036100740c120340305100381c41c203491300503003081401c0c1c03103040c2000903d40300c81d4012101c1980070401403c85102031901c904601100340015034891500e8000c110594044540c1c03180100d00540c00c41282c0280000c08408580d5039050032100b508090900310f0944c85240c05c4241d000042c00b000256071036100c200384440c8020382e0381c10404030400850003c151901e900c186588004141d011500a150100042041c08401040180352982c155004421500a0183d400b006c3d0400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 307892562 1250 307891312 307891321
    0xb0703081509060a030204050702121603020d0c1502070609020622090c14161703041506140111030409060b0306100201020a050706090519050d020d111b0a0b070803 72
    0x1d0012688103500304039074403000c501c1c090000c00d0000e09070340300191180d41c0740c1d400326091500070300003004c0c06580c1401860740c5d00c03500100301d2800034803008114014030030718142200040c81005006d00c03050780704011400f5000c0c480c1c0e0b4400613421a0105903041c5039100340782c00040c0d0701e9000a0034180884802c4207500045804038100c011143d07800a205c890503c424034008030ba0003000010b60403000e035a215120300746260070f4006d900e441000204100c010040455030010034001440c4168461f00312900e5950441101c0c4055030740a1041885864010045106541c004c0c20702400894101080302d080c165200d801c807090365810391140f030352100e000040c0507050614000784001c2400a000941c074081820744018500d10a12070007034059070380c80440c1010414103000c0c040e241c5012440e0216207289909000307444501408404025118940078450300c00d02070407400c4010001035000e04180355125020f426000105280c6641c00083c15001051045910015004041c0034182136a2640391 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 307893812 1250 307892562 307892581
    0xa0e10050423010e0c01081f03232107031e030c031d060f04050307021509040f0504120c060f1107050735010e0a0605090705010503060a03110a0b070308 67
    0xc02c0369081c580e41020940b40c905540010520f02c1c0340401e20b00383c2400c1c0d88100c0a99012940003402c86411945100000b091100d1124032128501302c00e910326049102d85248241e40701101a9060020f515031010009802110000340190501030308082c80c030700d019082690303a602c455001c601e0202c1c0d40ca1b1006a44540d162080c00e01d850349645100e400609411034160f900c10006080169000380031001600f041028130941d50039541c090a0b1500c0001801c848a101e034100101550183d480c110b1203010302c1180d809024007031504004e6180ba0003042e13020440b030407400c50205035002c1d9119400c03500c00415601c101c41104200c0c4480680b10445894040d05010456014100040e8401c601481e1101040c4100d00c0c1203c2c0c2841042d14100072080c503c2c003411007a444070555009800d441e10a111054111502c00c402680c140d8201540311001034072580015075007030f078000400b2203003400040c80410544564420060220030700568030505003115600095003200001c1580742403016002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 307895062 1250 307893812 307893863
    0x1009060c1202120c09060f040602031b01091a0a090f0503120f010b0f1b030714070b0a1d030c130e012702130b0a1e05040b01080a0e100504 61
    0x4041c034015031030024481c2d8031540811020f00200c002000000300c42d0501d58a0b40119090603480640300740d1510b9079054069103c1e0002d42c1000c64003046908074030743c019010310900c5170040d07002c5421000c00c8a180d1207042c442100030000e52249548000d088040f07121038514840461150005503500c2c2c02150ba061903484000d4202c4081018150050000c042040d0540311051114107010340c03146484030520b0781d90078000c208004d06000c0007070000300b0710040744c1c2c40c0c00e41844e40340304032401d10365250f480c1c4803244110f807400c000003461018003000300d119100245038984001800c80740c40a51440c0014486403c080007004c1041c2d48081310b412a0fa028000c2c80e25110b11194a00f180c0440c404110f10107514540d40244140303075180356030b50b816400307600103040c1c0d420140855141e103032520130102081a5480386c090740100304480009140c0b0b820301542c1c03041801a9a09850786e01d502c5400b4029003030b102c15070186400342005040c0c24210341c2c82180d1040380180c80c2045500b11440c40d801114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 307896312 1250 307895062 307895087
    0x1206150303070309030f15060b03041a09030a05180303030c12130b040212100507110106140607080a02010605041415030d09230d060c0215011809051009060c 69
    0x303810520030301001c2600504041c00722038111180c121482020b10740000b84016420400032011b14003a0085180000309d8007840c40b07244603001c019100c607522034a444a809003103404400301d80c800c02c008100070303108501400c400103142000e00ca004103136500090454000304c4004004090201e184156200d60340741d0103800c5590383c5a91002e070329854503280c6401d000107001a01400c00b42000c00001c0c1c1c0104012124000c1101003001941840003008002c82071280c4482002e6003060800704038040040c0100c0c1c0f160f08010300710782c64101550303140003240d0450843c0b401955030320b03d0700007019111380c0030f120145201d08d0382c420442c0c03801c0c0504410f01d620b0850464041d80c0110585040d003a0413241c07076015690600702c821070b40d0210340c404030246d0700324420b240d41003802003202a0400045422107601403120360203031143d0800c0500ca100189000340714100410004122a12072980c0590110741c0c198001c8040e50f41c01e5007c6e5520f08240c41c003250b0122021aa05c031022081503a0294046544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 307897562 1250 307896312 307896319
    0x8120403020303040c440616031103090c010e01020709050109050109061202030606010e04090c0b0403170f1e07060207050601090605010c08040509060316140f061c0902010905120615 80
    0x7440744601c0c80c51000300180480712004000c4e070006c1d2009001c0c0c0c1c4012807481480b10840340d07246040f00c3c0700000301c2038440801010904040d146140c94020000366441041248010702c0d45107a00001124000184500d460660040d0314011817110500e010745806848054008121075141008001c122030884d440780b800800301074003d6005a0700440da8541058091a050304e1424032a40050001c01003050300610303048001e81d0018128100c00301078070440c0d02540c0020b90482160241d0721907445421803c0519003c2040302070708508420341c1e0314043c00c49104c00c0380e003030098554400040368004401500c4035803121004001d503c000f4010721015113000c1c0b070700e800a61200e90b1484d100c2d0107640221442940020000b800700d48040041041400003aa804080302c0da5518130180700c104d021303c03118016003403601520a282014801c84200c1c105d5642c0c0142c01c11543d0071040001d0444100803410806e520400281c20390311540100c0a1445007406040c10381084600b0609010903001403502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 307898812 1250 307897562 307897589
    0x1018090603110108161206090603050a1b0b07240e0a0b011e090203062403041e02090406020a2106050901090902030703031b06050a0c0e0405150d08120403020303040c 73
    0x44017201341c0e10390304c10060503092030104040d22011400c003501c40b0b9003202d09404e00c1c000000003070004c0010413820050040c001004d29000098603110300076100d0140c00c5000c44200301d40400190f04d81c00c03410b03066040d2055442e2500940780c170314060b40c0c0250900e8040384d000001003828001d006001074010040c0e0986074407150440907090301e44100921884210713641c00f00010b1403946648140c0d039810721009200c0d6650290070304030000e032900151010389005d030048507c1d0300042d00140e40c0781e900c0e50f0020410706942d07503540d071042c2c069404203641004000d01c1c6010004207201c00c0c090071000b50640c40d000708425061034107001001005a010707a42c03d07420300326114090b803004151f140540381c2518080040c55075547e070402a4982c1003c001704110f280008200700c15906600041e0918195500c11003000207420800043d80c1c03050300c149115222000095040c0c0c07800e00c403c800704030700c50711210f818041c40528404c1040004c40b000e80c00741c0c000104000801400e0305920002c2c0a01c03004094 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307900062 1250 307898812 307898821
    0x201031a01090909020d1e0c0b090303070f0302211b01022106012c010e0d0210030b0d080301030b060f030a17071401021603030e07030b061018090603110108 69
    0x2071804a440c842c3c085003c0d03442c40d070401551a446a283c00032900404100c2041c005080c0c0510440501c4005031483c401c100360108840844000300c40a41e00010011030074016186c948250310302c2c42074001c400754498050522504c510341108400031885504141c0c1e2902026030150020940c3c090400013242d2042101c0030322000c10388015680c0c001111081038040d0340da030300103941c01c4c09002054900d2000e00c00000385520054200c0c91081d610a0b07035068440001c0350140100404040c600942c0000c2280080401c24825030140b0400c9a00601c0800d03201b0050b19024207903402030308240d4800a145040040509048112441196041c3c00a0100300003645a145c0300205004c20f41c2e088900001c0e010302407040c5015003009250200f4001c551320b01c40c1010002103111039500c210003290802c003844c245094081201c0003100d80005e180782d1150349081c20410f8004c050a03042082c09050852014695080f1010704003400403604c000861505600301a03840b40001c41c46141000132a00410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307901312 1250 307900062 307900067
    0x601180b070602030a060503070f0501020106060e2202091002030309010c0507030c0b0702331012020105090301090b13031403041101110c090901020706060f0e0105010c0807020a060504030201031a01 87
    0x1e821468221100588984555808101510217580440c0e4148a00c0e0f00114a0700b11840c404812a0000d070002c0000d1b1f50380d00e100f079844a040705a01c0ba8420030300e13a0004c0340c243c1900100140d100d1111001850144034100155a404c04a0220001640040204843c81d0307024402d0080e02c03107507810301c42c1c240701260781c0c01003a00d01c210000601c5c95407030b1008108198020044c035078501c41a4884a080c41007c001d4403c0440440884494003042c0c070008190140e11546e04141034501c1a941488410312036001521a503004c0c941e8603802d5907036007002c0008108007070320340e0303024840b0003211007800f060906000b041a00d0381c0841035082c0000304180000601d03605810742ea0070000313081244407003c0e580080c1d810b00302040b00d4280c1001302030f070410040c620190f004026181c410b0104201030783d1610785100d45c00020340103050380d903a0f14200602032507001e050b502e441a44508001440c101465022484854082d845603010500100e814400c40d0b030503004a1143c1031107d00640ca0034403118000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307902562 1250 307901312 307901317
    0x90a0203090c01110a1707050d0f0e15210403021213090c11010c0302031f0e0105010e0a15170708060f090603120414040e061005091015080601180b 65
    0x201c2d81407001c1c503414000d199a061050f00e403da500310240580d03074408503141c208036074081d100c1240c0078014207c20000e62800348405100c2000b440d2758039484450468280542d80c4040260000c0d005401e02803040710050301d452851314105600d00600301d504013841c010385040a1100002c02041c014041c0180035111310b20403004a4524000c0414500001e010a840c500d0084010249031b50910f03015601d8207826400560103020b001c21448007600303813048417400d035121a00600c50110702a03401042550b200d1140c080d00200c1c01400708121560300c1c5c607480c4501400007480404600c0c4a4480380040401000c0d0550000c040d0030464442c2c600040080c2900305010f60b1079200f0145403002c00e0031034504000c50720842440310411542c56455110b04004080150102441036041c40d0001076002e0010641b41d00861590b42500d01b5641010304020358003c0c0106048011581c0c498000365400d20000701d800c074034440c1d032120f400908005000503c0c60322900300071002180348078000c02800207500308 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307903812 1250 307902562 307902583
    0x503011410031103090c120d0c0602030a02040503030a020f061302102703060510050d0305040603270b1807050102121b0a0c060908011b0318080d0b090a020309 70
    0x40754440410303501d40a8004100d610000707000c41001104026420100060501d001c130000c44910040032210300700b0560b541051900720000a02c400044000243c1503009075411040394140907003040c5d1100080f034615000f43d1603102c0180d0205020105406062040641061b00c3e420146140d000c0c2d030b0081403d481c4000148001c120400103030041001e581904809003004402042244950780d003064000f400c4280c2354550341d0f020003080015030303141618417002103c0d0705441e03190400345485000d50061206e039101d0102002101c50040031284a5404030310264840c81c03008000c0d0601e090490052000c44c0c3e055500c035408121706102030382c0c0010f0340d05603200d11100c4d4242d80340380314144a09102d49040295a45101e0002500c0402000e00c00801c2078403103554506a8aa668220641c21303620b41040d505d08410201583c41032681c441c0d0054100035105210300c0b4500301043d5260582c41c1d0000400c6480240d42e51038140c00351811000d40b42d04402c03011000e504500305524855260b121518 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307905062 1250 307903812 307903819
    0x60925050622180b0f03160317091519090503070b0d06080703050d08150f0d02181f0501020a050d210c08070905040c0905120c040f06060f05030114 65
    0x150201ca001e41ca02c1c00d14005003107061600240e260306006180040c11900760440c0c892a800121690f85040014096051961032004110403520395251210903030103070700400340c1400040103503010a8a4001c81006074948101d510382d40c440d0360741d110508582007503c0307030010030480c01c0d02049030790b800080703603000e0701c0e40002c100e690b400b64012a00014407180d0700c128403d000c0c0360800420b00101203107001c000d8106844500340c5907100d03501254908030b40c25103158424000c008124003820429a196140740c4080c25041c001001000d0600d24070104552001c02481e0040c500c580710500d8000321001440c0c00e0008108240265860745e49405405407140204072000140c000c01000450f04000800c100c98001c00c861088203400415a4004032401800300d1840c400010b0b03241400d00c03890740009050b6031840052030a2008001040802200366902d44c0b01c0d51106c0030460751f40b40314180c1c0020b417000000403034038034165018043d0424000e0300c0081c00000c0c0b00401200c20700d034680c0e151029044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307906312 1250 307905062 307905097
    0x10e0c1e03070c0204140604110708040e060f040510050102190b0c0706021207090e060d0305070b0c0c0d0512090c030307030c030c080a2106140f03010e0609250506 72
    0x418110f0340300480c600065406810003084415103114260308601500c4290b50038840306500b840ca01e1030f18854000020940002084204040e10001c22324540002c3c000b480001c2c41c40c020070008056803402d580542410b04281000c0099680400c080543d40b021040b1590551205440c3c844800c1002000410320080c001007000800c4003907070454421040740c200309101814020300c0189040e07603d00480800c041a8000f0500915100310300100940d4940c1e030b0341d80350442c3c81c1c2e1070300206040604800c0c4240414050014400c80c1072081c20700c1c002c0e02d42e840680b00c00080a561444403809869002a40c020341c1e080c2c03150351070110482e501179816040c255462440361500301c03045124240b000e0281c1c000440d00328201a8403a824444400780700c04401e441c641000310350710440d061440342c592001c070041c00038411410700c40300f01401d540c1700500028040c035901030902e041460444000c05140c0100038031410310302c649007902441c540a040d00000c00c90a04011528130301c965241d844903032101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307907562 1250 307906312 307906321
    0xd091406070203151b070f021908060a0b0103050a0e071e0b04270b010207060c0204020903010c0c1401090507230411040906120b011406160b010e0c1e03 67
    0x1903908458003a41d01400b1030782c00b42c0c0b04030078855003240180d46403058030300b00c44d1000e1005d00d20f880075191440c0d00040ca200c01c101c0a0b5003084980c814007020010f1683d60b80c240022800c07414042035220352000c01d0046400c100d048001021110014110f00b1540e1800c00030080114002800006541090080202c8241c1c50b00d180c800d02e440c1d5074480b20b40b8030700c00900030810401c3e02e20715140a219058030b45c007090100350040e1060300e041c42800c0380140e104450070894648038405c034624850001d04014540440c4c070740481e082d10043c901603004101888149420800b0441c00c8406c0d200c0d5107000ac100c0d84079155501501c54007070341b140d071503240b58031841c100103c50b5019544610440083c01049410790341100c071403150300319203e603800b5545003240001e0900c0c0c1400581c0c5409501c450107890a0382025200c40f001c1d030076201c442d500950140407080303140101e4850060054082c1d01c00000c0f0350701d06000d42043c180700401034440d6103004c3c405055800d00d0f0300300b200c444000341e410440d220340c2e5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307908812 1250 307907562 307907569
    0xc10080c0f0a021009050c18040302280606031118091b01120e07081605011b080405060406050d0c050a0c020f03010b0d060219080106020d050703021005090303090606030d0914 77
    0x4125602803010301e0b00054908000000902007d060000e90b0f803081402901145030188050864014009d600420b8000748100341651400d1901e00c00c0c250440c4c50301001d91581c3c802c8030001d0300101c61100780000e855040e45489030b03130220410025010000c071840d14030038203600c03402080d000c0d2014490144c6030f12000c0e1701072140c4550000e4104003c00070b000300640c20b141e8810700e0b44a0030840740900c41510352800880060541034400607140d1050004400c041c035281c0e9410103c0580d0554418400030807190341d00c0700104001c12055542d01c1c0c03120b0340c0c9003601d81120280b0751840c0a1140421200110a400180b00400c050301200c0420000504002080c09001541031045e44251500400710801c915a400b400c41c030070a402c00100003400c4103200b030b00c011000380580009607000b125960903a41c8198010601c2c54070a1050b03030713001c0307076880d1b02241540c40a443e20400da4001004001464004002d229031010045000b05401d0151075800b503d0b604450080c1c0401103107850b4500030544 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307910062 1250 307908812 307908823
    0xa1b1706010c02101709010b150c070819060e01060f050f031c03090605101208031509070f0e0a0e0105040c020f0303070f1b02031f090c080c10080c0f0a02 68
    0x182c0291100300001051a1300501c14903030514005600c2040c0b402095140f00c0c14800c802c503065010b0300c0720000c00c2c0c960154800a03082400500d81510450901240014040c80508001c5c1d958402914401e440743c03821900380c407904115229030340e16000b0204452004011031508903407003940c0c2d20176001c00d034801080c00c1c40700b10025503409186d0003251902e02680343d4810010306000b000c040055484800b03200401106900c11000100e2045c1c40300030226003402c0041d50810070411490030304200702404500111011502c240110300160340108200e42c011588417481d48007112507201140c14a0510100fa403818080d00740255a100755560640d402009904051260344048076268038182c40010801c0140e40000e000055150708940390440802101c42c02d034580c001c000d4146658002c07032460300c0311141c3c54052015502e6010072000700c1d40074018031028103021005401d900003a0300610884400c0a00050104140c00042008081c030320400d1302c0215000a1266580b81c0d8401400c0b031600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307911312 1250 307910062 307910087
    0x3020c04020d0906050c130e010305060a0b030a0b0405060106271514070f02030705010813030c1e0b0115050a020c091f17071a0a080603100c02060a1b170601 69
    0xb42e1829082c45200c0d0742140280c42903c0542001f0085940c84000340e0071007400a1000400c903500050214188814641008000306000b404a0781e4400c800d840e40078003030341c1c151000d6416030004030041c010280c1c400b10740d01c464841e54826500482e054040509071805500c100d8442d046401c11a68505200384c50001100c01080700b0310b44c46020b641002015080f81040882c4039208500d07000a09500071440c40c1c0c4511a5000c02030901070050703c044c1d442c8141e2540456281d81c41e4451980101d07020084140d145025001c1c000300356050074007002140d444210b181c02403002c14004044800da0008402da05003405490040d00340d260401c010000d20400d1407a0301e1608101c000c0070600b0040340c2d04158103482d21004980e0500c0c0e440000c0c203600c0d2452184261b10380c00420440c075209010700d01c0c0c160800c002a04488142454009060454030050f55035001a00103205002d0b03c2c0150340111202c800d25280807412000710700c10042c0c080c0402500710076464810000041c42caa0081c580740307408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307912562 1250 307911312 307911323
    0x24081c02010e07061d0415060305040f0606090c03050106090b040521010c021f05010605070f020109080f03090f06210711070f050103051b1608220f1203020c04020d09 73
    0x544a807000360208016030f0740c051520203e400c141145207460b0203032011011f40750205441c010305045d4100c014000052041d540c104006500100242c041d1040c0300040800d100c1c001088102060f000301030b104181d010030204000c0c442c042c810240308002306d0b02210400ca43c4104c3c08032002e03040a081e0440340c10400115440c010401d400e071134011501c0f0f000c070400701c03040600701c80312040040308540c1d080c000d1000103001446502c00091242d5501071900e801410603070511640c81d980d99207020b00c515506000c3e900041245c04141c10410010700b400c600403500d4901b00a51b0644440f01c49901d450310740704595520000c500304a0042060039640c003129006d440302d0a40360384080f003a400c4580300f400c0c00245000f0014400c140a070540c80301040d41150114036004000c062110122034515090300c8102040205034000f100403403408281404100311601200c2c0382100300d840c1c8110740d52000e00c510b008070569000080c0d0101e0082440c0508031001070301c0e0304010800e00e0041c51180c0c001000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307913669 1107 307912562 307912573
    0xc0611070302010c0501090b150f06120c13031403070b07110c091005090f0109050906070503061c060c08010e010f03030203040b03130c0924081c02010e 67
    0x7858011000451359131f449071034800003140d0641d0000c11000c04808010205e0400c0034941c20021422100d260a20944541048020a0092220b10600c400140c10314040d0282e4242a01564011514060100480c644103070f50b0381c080c020603901d080741400000c502c54805d81701003c1c44142d002c00b8012840e04102031180c424805054100c400f10400c40106141e1031b00d4190381d10a2a410100100340d516226007542150009040c08005070410010061070036040b100311380d0805000d8542c4410503582c0013412880c01030b9120002c03d0300d42044108440c40d90700c424224142d6000c684015100e9030380702e0044141000341e103c01009a08140010080c0c151031030007550b07002418000d078089036122580c0305804070741150408801c5547d40d49000c05225a502207801518640c1504c41d00c13018109004c4a68070450030350f02480c20300ea982c0c00b00e036910f80300790001100e48610408498 = true := by decide +kernel

theorem cover : BRFrame.Cov 307733812 307913669 := by
  have h0 := BRFrame.cov_init 307733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307733812 ≤ n) (h2 : n < 307913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
