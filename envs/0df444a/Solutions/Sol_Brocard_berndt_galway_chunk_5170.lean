-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:33.886837+00:00
-- url     : https://prove2.me/submissions/fca035cb-df48-4c02-b363-5cdff7357c2d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 929676258 ≤ n < 929856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 929677508 1250 929676258 929676269
    0xf150d02091005070515180102040e04030e1206014b06020f0c060d1413170306130b0f1903061103060a030f05032511061804020912030f0c010e0106 65
    0x40e41008003003012400c10540080d01c512100f0001c0302140401409c980c02030380b00b90b03100310a0310204028035400161001e0011001e440e41d000d004005600d2544a00b014003c0c801b880d06480c004201c2d10740a41411103000408511281c80c0c2036011030019028202010300094107c402d410210b800791001c12000b40c04000704004100c0605803204102007900311070103d5440c0b41d503840c2d810480c1461440c802c1d01a1480791008804a1003505228000c2c60022021240e0000c042003844131644407091181079040c2400700000320000c3c03860024107030400107482982e0149030400d165000c08201c3c080360040302d00c180c00400810f03188001b001114001164110340c00700b540d010030004030b2410401d190301a84204140d0380781c13180c00c143c01140c99010355180201480c810304020100014a080190325000031615030341805240516131030032088a4804d207000d660045510b00250b21384850303800c0b0f01c00c40302c020340b038907102c3e001140c030b01c9904031a0b5544019824203e000c0d18580c0c061107214162003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 929678758 1250 929677508 929677513
    0xe060f330319120e061e0306041d0c03010e160302130f1514010c0804050d0212060108060f070801030f020d081e090307060305150f150d020910050705 66
    0xc0c4004165620824a29400c6030540104103500300c0760782a201c0c45079912441038451182252450a008010380c4164103542d02070102040b0201c244203001090112808040c0d080c01d03925515500031601030a2a0304000c1003079405819403400c00d90300401c110902000c1a002040b004074100340c420303520200044164101450741d6002d0000d42080b06076042d03480f21201d40803c2d80280200300400b100d40031802100c5680e1030341000e020f84003004a0604108000b482c1070a00f020f019240c1261600c0760b881500e1040380c40604450031900c80c2a4071071520200201903070155a913030303284242c4561044402c00d990000440010720428040d00089058a400200d12602c5010036800e1013601c1400450558001c1d800340407800a04d1038080c05083c00503003d0003030a07101c604c50000d262070682d90750000c1040c03500f01400c11855060035078910100e0744044032101d02c2903c460300410401913a640042c1910400040c403036100801d1740c0c008107a0080250348182c00d411504600f19205e0140000090968 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 929680008 1250 929678758 929678821
    0x130605100314130503070f1b05191806030503070b0609010e040302030d05100503010513050d0e030a30080609010506030603101d0a050604110402041503021c0e060f 72
    0x40041c02954144e2040341100c0c940251034075426209052000c040ba0301e1045040ca075422040c006625500a105c02c0c0d031032208102203003891000d9a0554080c0b1140203564460721403460f006034000c00700a42d041000d036a580c40c0300b82044103689104449050160903908000034154001400003440f0320f81583c003071814021076041200c040c03d00a040b10040c0d02401c8070114480d5000e21406009486841c0300d091840702c903203040c5042c8004c03003070701d0000d0001d0001861101c0d1400314929684992141c080c010150303010344142120740780152000e159a940c01c000540302e5401c120118000c48081b212411541ea0f02c50130402079101c110b80360380d0550403030212440c840c0c86a4000300c005401d40103a001c4d05280c0c1090052800b8607007041a00d2662041042c00240102c058541b108128103480039450503080c600c40981803407010120004050b400580100001007030a1071020800c0c4c4200c0501c915403a445005e55151800e56406007944000c41c0481c4d400504501c64400d80b507041821400e14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 929681258 1250 929680008 929680021
    0x31e0212120709050a06050903010c0306080c0607080c0d0c0302070806060604290307050715060303210609150e060f09060d02150a020f0607180e06030c130605100314 73
    0x569030041c0401060041c03403c00030483d581d0b1000d06201400c1a0741c0ea241d00c4d280e51200705401e650005510b281403514101d030034801c061000c40c01c41640041642c5035940c900c491314111910b8440d007503110245004a001d021038040c0c2c004842101240240d00701d5043e00d40741e568140e1503950540e09190701c00001c00c000c116104204503020390002c451140040b00301b12100940c0b0441e4011503d801c001600020610100805100c662802d0aa106010081c490840d0340150150b99031000c0b000c1060010b501e9100c40d07a146402980203018058805c0c491012014819042548a405541000280d180004496040c901a607660381e0200402d41000380c0ca5100030b00081042ca05030a0307801603820980300c01694a4840100718603416540105100a2603590031410300c00042c1c002c80810044480c0100d4003282e20b068130080c1c940b450308043c0c09440e00e0300020300d0b242544420036002290742e4100f0360380c0d2605a00003411600d060307695440700d40d00c03408200e04480021541d0304410ba500d8000c241e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 929682508 1250 929681258 929681287
    0xa050c0301180b220e0303040c09181b060807030b030a02010302090f1503040501060506070302030901030c0c050f0d2a26030c091309050307060504031b031e0212 71
    0x108150b03040c1000615030a0f03500483c1101d07001c48580400c254001c0301200114000d0711a0181890020740a1411401c10b640e844094845034420011200d8643e14071054034011148909600c50340440180e01d001d0441680310882201d510035030300410804800180524028050500c105000401501c2c1c04d10350b560040d4001c0d04002e041e1504410300c0d2145242c00d4071080b0030032903250341c3c01224945a24062409609407034050f00440c0c05984140302100020750004107a81c0c00d000c00b420003140d1809843d0048840c100054009006031048079401540c400b40400e203190303070f8601aa15071088480c260481c1032010540340c019100c4208030004c507800725812011051095204030110300c035100051401603240d42050f909240c8502c40002e00f038503180360006110001e40392401050014031803a031552901c9006209000c1d0034103446000190815204281d02075100b15451968240c001c458100140051f9840c2c031134400b00010140b046110030f0002030202e28500002d0096407804080544141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 929683758 1250 929682508 929682539
    0x2010e0c062a121204050f070b18041509090606050f030a0605043f181206060e180c030f120f0f0a0e1e15070201181205060a050c0301 59
    0x7842c0c0e0040707540b00010040c02c0002050740d100701d5000300d034030707424141401814a040c03d240124560300846082100d07003502c81c2500c3c080c0700c402c00c0189c800807940001c40d0244c0f140c1d041c4243c90180e80c2d000410781151680c00800840e001303160401609456509021200c01d41140241c0d06078403030112000003c1c072130342240b0352041c80340020903d1400091074140a1150140c0d101040443c100c00c5a102e10ba2116074020b0711528501d0306502136908845900010700c04c501621701000c201040c03c4040c006d06800007001000f007007604074451f02d455a111b09002c01400d98011083c007800d2810211880d00140007200d40c0c1208010700040140c100501181c4d80c070005070803800358000d0000441c445200009002142c4144e120042c80c0000c40b410040c034a00300241140941d107655140040c203417107031101c07c0100300e080d00d58160b84100710700040e24034400707100c200700f005820000003081109880611100d4a44241c2c1100c80d80d0304c80088807004e40d2300407290054410820700c01040b412483d2045071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 929685008 1250 929683758 929683837
    0x31214150613091508060907050a03032007030308150607020603161701030b011730044a0a050615210702010608071203030b1002010e0c06 61
    0x40710100d50318581d10080d40d0740341035a2141350700000c00c108103184040c00341c90fa1204510b805003501c2802c1c50700241302c4c1c41c09800081e08003c105202d618203643c0358884107400c0c6075008203c565555680c5401420750300f045070360282e80391724074000c1d4401341441416500b5041e4000c0086096a440c1c0800046002010200e08104421402040b280100140c4550301a600603483c19603d5810111008284160507000ca40d45600003800882140c0f0203609121036440c06074071541c0d045000301c00006c0780340240d410444051008002805504ca6a4903880d08801c501d000707100522185103a20f0124460000641149c3d2295000000d0110b2410344c44107070b01c4000100103800d03402c4002c05105441c3c024450b0800f1000706601021410030b08600c01c240e102d02e4500c002c0c0152401e04c0d48158030303590b407032151050010001440d14100350003500055085c600c00b074400103203001120320080c00791048810400f60f40c02564942400c90603e90121046407612800d68030030a001200030a249144e40c0703049 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 929686258 1250 929685008 929685037
    0x3011b140f12010806060f0a060c03120608030a02031806070c03060b03210307170717270d0807050f2b15030c09090308160c0804030312141506 63
    0x42c01008502440c410b000c0e2052500a2113180f510f08203005469100850b501c0c070614201a0810410b0f030710020710801c941c0d05140403014111441000005451507070011480e0b0f00000c980c0201c141d07030010140ca000341c404010075140c4100402400858401d011000e0554202c2034405e00c08071341c4a0f0444030025102904668115070500c0da210b41c0098000024044a480082442a0a0750200780c41051000181c20a000c6003072203440688554990308050a404100000107000480c1c90242c0d80c5c00c11400501030b20203000c6141c5e00c0e0352220341100c4080040b0f0411404602602c1c8244180d9008c0015004041c1c075003071040f4007150102d0204402003c880110341640428408540200406914414001c143c07860440c6015010714030b15070841c8507910724000b021000710340d00c034400304c1e004804540c12007512502448100d40d152105c032006040303d040020b00100300342d40300028040d01212040300300443e40c081038070401640c0040d2201c0194104000001809103840c0c00108204444d600742d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 929687508 1250 929686258 929686267
    0x807050a0b0a0608010e010b1c0302120d14090f07090e1e070602010b061603110a0b070806040f0903080a0209010c1506061e0c080904020c150603011b140f 68
    0x140c08900c49001ca9441d100b858481c40200309540c024095030450424080013400342d819070002150b500150707600d0304480200b00301804c106150007072140d05074140c10009107a1380d800000041d2409084140c40c02c00c0c28000c5000010b00b070b070a01098000d210796440e00035005451400d06200d016040c0d0382e56400702401411aa80d482440400d402d440d0910240043c2042c540351a40203421180310081c584c0c002c58080240454150042481c5810240e060a00103441c003110f5400d07600e0300048c110002c1203081010184043c4a8200d420107209101c200c84c10b10071b88002400c200300307450010600602191010010401404e844d03000750176491410f26082000c1c505070b0300c91080703541100c10350608035035982800b80201540098184410b220503000b0b0b440a510f5041e004010090042024009200204103070802d40c0d15501111480c001100845241c07881c10030111084620036660a4861340c038190708000f000c0344102410b4070030000c50b110b0103414203035911000000e920094400b82009001c12 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 929688758 1250 929687508 929687513
    0x612090809030f0106090510060824030604051011070b0f070315030b0604141909150e011d01061d0c0d0501300b040807020d06050c07020a0e0105030a0807050a 70
    0x40741c0340414490f000460600d00d0070003110700312840600380b04000c4104034014130000350002d030a580c000c5540124010903145801c0c440c810050410f00481e41401100180000e2000010300d040041d2082c143c100500d6000d4084a80c0c2889416002403200003858001180f40d041502d10700e902000340d04000c00d44480402d9203011900c503d0b00216007030b00e001400e00c0094201441940218800c03000c1208071800c0c004c51401480c8070305400d60210940707404205041014540c072070404160650000c0c000d8410010625001c0d01c0c400340c6c10103170100c0c6901c465980700c505000f090304403800780403030040d04e5081c0705c01140c608030700400020101e03100300300914840781984941d500a001c180542c4070410000b00003117241d07000c070b115032141500c41e19001801040d8400c1030290820ba2200e4440ea803180c070b52011a0300911120409000070f8940700402000e00b05070002494690302c01c9543c55070b02e50302c136a80090800800c0c011b81da0954065610030000921513402840b01d00d001c0c404841c2001ca166 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 929690008 1250 929688758 929688763
    0xc110f030f060907031a01031e0303090204090803071d09010909052d0d09060f05030717010b1b06090c0d0507031203020406090605090907050d020d020f0a18061209080903 75
    0x6440341000341e440071a0410034481b03010105904020520203c0940e9451a00c44100303c1c807501e03a44070f08401c0e01900300d008150196001d203404950181c01808141800d0425804a0b00103c401d90081030b40324400d5030034010351401c5001c20020090140442e81d00309100b40c0018881040110392922510380b51a250140c4034280d0340003240604215034080c0300fa5040700b402c0080045c40c03102840311200b01400226000008503105a5003441c040b600c0b651148012200d905400d01410400b898100c004107510b404000284064201040c12402e404e68441c0044c0d940e890844407007040307400c0000101c0301d07450040d08040d07045028804483c80d06071a41c5448a5142c110032900001c2540050204005600060318100404c0b6030705144c0e0608071210085841844000c042c5c00801c6800560003a00f0f82c0c031a41502d16000c4c02980454075410030b00c0c010500c070b83c00b88011102183c4400030b5408280d4076452048140c890680d68001030400050140b0050019040f088a015100344662006038408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 929691258 1250 929690008 929690011
    0x1602031e071e030f031109100f030513050c040509120c0f0c041b0e04180305070204270b0a141f080c010c0201050904090f150c0c110f030f06 62
    0x385504660350821442c004901c1003101e00c04907048804003a160011903000401d0160611942c2400318a420721105142003c2c41400d40313540d4403030000d0400d00380240d44111000d00d00103668804200340c0c4c543c0607060b0a05403c001c00141a42d0101285100d281020340000b070708a0101411110055100c0711003c1441e000340c986000290301c8101c00c0342c2d0043c4200440707000c88138107844c06c200640405100480b0b44640580c0c40084c800720f41c0c0a001c882d00e4030f0780300c29072444006604500c403558518000b011980650800e900c41e504020081108030214603480e203440340308071096400280360356a030f0025840000d100c1c0c1d4000d9580e01c44071307454580035840c282c45042d003c01084081c40d685103d03000c8032042034210032059482440894026600004051070480e02404c0190316003460100240c054041c82c0801040d08003080c0b000300c104a0004c000790300505084600b80050440c2403c100c52140382da002c0a008081548400c2c00d00f0f00344000d001100c2c40020b03080e114400210301c5000d150010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 929692508 1250 929691258 929691307
    0x8031e1b1c0c0305120411030607030b131512080f040f090c0309110105160c06020625080f04020d1a071101050f01050103020f0409090c0603050603010c08160203 71
    0x60040c401da445440124a0211281070030710014403032454078004c080740140240c4e601c040e200000883c2c10700100000303401945200030112445494400710040140003044859405119144414807101c100e0f80146080780156040d621089841d0040e1045100408881511100d41c100052150aa81e110003400034021010f0040340a514001541d03040301c09000120081603d0010200300080150054150120003480c005443d00454060745280d0390b400c1c0b074010405103d000740003c049070080350a41c03150180081d05020700d0042c940c41d140d03041c4500050400180003900042c4220400076a0640282c0040c14400390020141e0303031480341460b0a441100c4a039041010040c80d15400b0005c000c01c4e160000c024801414503c0031060f07041010700449050503004203034920389100004c10380d0014003002100303000000360b904180351010003d018600000c0d080c840001c070942014001d40c03c00164035030701c80300c059550070303102302b0394000d035110090450004100c0b40e01c0301d0001d03003020f084656 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 929693758 1250 929692508 929692513
    0x6090910060e0f31180c05010305090a0201030e0c03060f01061806080106050322050a0c1e0e09030c160503060c0307020c0d03050c0115090506090601050f221d0105040608031e1b 78
    0x1405d42040402140d0f664031042c100342c02c110800c0150140440c0281ca031550a003004105540c065000505180b520411280c02d88648420890120164080c080c1215101d0711002c03041156000700c14000c449901903035003c501c4040c0104069482100156401041b280e03100308189144907500144030038044040e00c5552003140a90b0a03c0348001c40030004005400780741a18030429009448040f440d48125540251500700040c007202080c0110f5a9a6102c001510340e84074030041d115049081902400307020f031145c0780015000c0d01203102203078010030454004042401c419010480c14048049003201002414410b24000110900074600c140b8100056411105e040500d958112000101014032401080e01840100d0b40c01008032012041d11005166907000500e00b0140d19510194a0070030782c00382e41a0000c0e001000c040741c2401c00c2e82d1034486050071b0f40d88400300f209940e9075000d14045500200403201d80b1030403c861401c4050843c4450354101210050f5140103c40c8010200180382c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 929695008 1250 929693758 929693801
    0xa12050c06030c0a0f020c0d03031d16170c15220b0403031106070c0b1e040b0f06030a05030d0c03061e03030f0302040b030a020906090910060e0f31 65
    0x80350802c0721034101030170a1000300f04460001d0000740b10710080600c00340a2682e50000a55128100b140d91040c1c0c0500c1d0b001c48900007289003d02c540211503100304203400303e80400307a414078000862110610341000f44031484c08a5011a5041141c0c010b01a0b005d03903502010001040007a94100c490042202c410010307100c504e10700740500440051640009190403004c01c01881c0e5800a0484d0300058100d05440042c1d5140000c0c040a800d221150f050110307620000c02007009180b0303404904c5620015500300d00b42d02d03208140350b0b55031150070307005016030814040041e03056445e52041c41901c11519001c11420b035943c2c0c408440314011981c000d07480c10219024024581c01120616000c66103103401c41c902881d00c00032040d14040034050408454001544c080d9643e200340c140c900e00a401044020329042040400200b481b40384904c2020568003100030504d0310342445a042c1803c0040c101124450f00901060f0425107282c0705031041070500020505401414401c8540c5440680e0740031010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 929696258 1250 929695008 929695027
    0x150f040b1f260f0d03021b0a0c030c08010c0f050f07021507020a06091202010e0103060b0a270602031c09080307110c061602040b01120f020904060e060a12050c06030c 73
    0x3807041e61450b6481036400b4883c1003070100400030f50320107080414a40140c4420303010384011000d51f0f103d08424090700c50700d4041c005000c207200080c0c007203a1040d204804110703074514800782a5101a01c00c1c40c089044407a0003007181d4001d030024042403803c441802c0c41e007451640042d900460754410340444900220308942141000f4902002812290521500c5903280102d406200c1700a808003e0401c01004440300540e400382d0084005403c0741040306480d8010300000030483d002031001c0d000e601c20013080038110200280d02500a550495019602d8006070007414400c00e140040804440c03903940d25981c010610310005075010f0021561a0000b0500602a40f4680715201c1401e5103c2e2008004250590450502540343e8a5040c1c80100b584542200161410b48014843e405840c0c103143c1200102142a401000034000c00c0b0740c2003180036290715558400a00440b0b40076001801240280901a10b001e8032001d07851140c422240425842000701e65550005e45040741040808100c0180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 929697508 1250 929696258 929696309
    0x2040608031c0b0d0c15020723030705011812110d05030c0610050108010e0a0b0402040b13080d05031b07020607030c0b0f10260109050a05150f040b1f 66
    0x401c03c1c0200d554080c070f00c01d10340350185203201a20501d028203880c0082c08484078028000740300142030303000c80a400c2646c07003240d01560051000b1414401d01a1000118103980142080d045041111903800c200905000e0507600340f0f29004410343c2e010301090120b00c06680c5103a507400e50184500065500d070420f9042c0d076807900e14041c0c6000d05082c0965001e0200e640d0104e92035044038048203a5844503107810350084020024594199005400040c0125000b40050001d0580344000d0000d422455601c507001c0d03850310800a03003040054000c10200302038030018082020300f200e0018115160205560001e10907500c02c010442c080740300d455000c0240032940382c505174000d010b500102c150703244c0a62260f0030522580aa401280350100b240c070703007000b510440503000402030780c020000303a0f00605046e656118041030403955131192881c5209031451030314000780a990701c040401c0f5175132110b42e203140f50300f0b40003440e0050725810004134503608030014052600030310f0311200e44222805182c2940b40d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 929698758 1250 929697508 929697521
    0xe01020a05090a170d03090609020406060206190501080c2809060512013b030301090f1808070b041133070803060909030403052e0c0503040f02040608031c 68
    0x2a80300740305100c44d00b58043c0220702045030f5030031440c002440400c1031070840014005190069001461b103100410b0041e00041c000d80990f235903c0da492180a503110201c010ba503424001c40c0c485400401c107550f0141003215034011150401400c0c0c481000080e50301641c039080540c0200c0300147c50b10000c01c40d0b81804003007280141c0401000741f15806020280500520035503d00c45420640042001e0000400c403c3c0d023071401c0300e000c060705da5a5950710144409001e0101007098403230703e011000c0f03030110031172444c4281c1c841d442000a400c050b002d40b1690a4104010310a41c1c9000c454034034607a10382c1e03c1c2e02680c0c01800311160b82d00350020803848001c5003480003400018188000300205400b20304100700b40d940c04041190740094582c0e40c90021800c0d0301541e40003e2052240da805000e152030520004607002c051744110449051344042c045081e1001800f407130000c0791040004c1800704001002c800c12250004e80042121541c510003646140d0202c1c0c1801d21540e0302c41c2c01408111201d01a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 929700008 1250 929698758 929698769
    0x8210106120209010f120b0d030507150603020a0603230106031d2d01090203010513060b0a030222090c0602070e131a04140703030806090a0e0318040e01020a05090a 72
    0x31070030b20403504000b8001005c0e07290488144503202c800ca401100d56508140c07000d0902a0040d0b24040032890082c0c4544c00c4002c00701e6101a004658a41d07071354441c030400c001c42e600244403000441c43d1800507401000701b40056405045d82c0c000b16452002c03a006002e0007054a580c00040c441d10f503460021012010070035a80d450b411454094026034151039400407083c078415501032118030864940c2d0300414030b640000790154204800c006c3d98468080003d10464010b2070140041ca01d000200500c080c100d010081d400419841989030341403d031103240301045500f0700c00190784000f0f9125400c0e011125841400180d1281e0f4003800030102441881e41c000b0981d0080c0010030f0001d40c1c80031807001e0160b400e821400c0205001a06001ca40c84040c0040c00702041980c03206c03522401c006007101002c48115000b102c030940801e00030f2446103c1c41d141d440403400594100503039600804455540c4030070155015480d40d1818901c1c034021310051040d40b4164445039503d012510500005d194654042e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 929701258 1250 929700008 929700011
    0x90a0b280507140904092003070b0909070503150a030b09070f05030a080319020f03250c24050a05221e080c010903030603140f070e040821010612 64
    0x1446926a04461010f81000681c501e0b030780c0329400701c004207004114a61000e8145c116000001c4100c80030004e165010090071b40c25184803540ba200124501d2143d140d41c0d81d089101e840005031128443e001550300301100b806030007141005030300040c06100d459002a50140340900c18803038030b100204000b20040076500c0c0c0b0244c0051a181c0082d0b254800654080d20000f00000004c1c180103145440d0b4910041d00d650442d1a040c3e2030702003022581044520150703a07001440751001d44540c001d0000c644c0000c1d940c41507642d42095607101d580c2400c00c8100700e11202c087d00107004980300b40c09401e1042407040350024651420780048081d90425002208001d40c00e12608030204003c140d0720380042901e0303000101d035002c1a14140c0d00030b20814410001c694a0700da1860300700b581c15004401107a01401c1500c1e40c00400d070702c070039442c1d0046540c081c800703a02c100310400250034004e0703130345921900481c1c2d91801c0205c0901c4c9044001685100900e41c0200d20f0014031030340f1b0700800e9207280e0030002d407070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 929702508 1250 929701258 929701261
    0x308160c0812070509130902040f020f1902100c1205150102030a0f1404091a0109150c020f190611240a06090f06050f0d0506040b090a0b2805 62
    0xc1d94a01c030700c90070901d890840b201c00c00088441d40a5000c480c00340d0800350103000e040400444210017420080001c1748207904188000980c1540348c02503a9070b003a501900d852a001d07410565842d04900c042e2481c055004a082104c2403003143e00c01c0a020000c50740b5207002c040c8030b058004044440061002c0c502501401c0880110b9a0000545202e21a14141505a044841c20541d074005100000e5600c1c1c0c400000c02161000a640009100b210620281e0075184540c50040d11075041502030945020010b2040c0e81c44240309503420324000340080d1032101440e00c000080780e1110070050b008026501e680208011362035000001c0032280142c0c0014228048070b124070b4214481807125900d00380107038900420303209102a4040300041400031401c00134201303825180c070094621403099603c15000340b00e040a0500342516100310320781e80030015180c42c1c1c0c0e440e600c01862100c090913840c00e40c410b10a8501c00190080101c0340208550000141008880b08058003951400ca0b0200a0f0905080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 929703758 1250 929702508 929702513
    0x1d06040203070c030507050703050a060c021504170f0d1a01121b031e090309062606040c0c0b0705031902090d0b0c070b0f06120f06041506120308160c 66
    0xf129240541d89440e01c1e03580c4e64514103280340b820300d5a42010b8524001c4481d80020810300368040b107505c0364250256150010f088411004100c42260040e10300e0550f0305002441002c5a0010a424a00304d07085c00e00700781a4807801c10448a602242e01a20b0b42d00c1e01c1c96803150740e0410807107150414aa0401c0c400d01c2400543e407400500d000c05c00300141603c03011a40020219000c40d800c825800c1d2000f044000c440c0c1c10003d140450600ca46000320390780c0c107a003607107140c014405980140c9401d20502c003036849a03004e000091880e10003000404c0325114030400011071540e0510300640702950b5458032410500c108404000100d0030240c000307803040180485c81c0e102c0d91880c1c00ca1a412006500e00c0f03943d10010102030b40700e000c43c02000d103142c950411004035038818441707004402c140c41407052010540c9001d80e50f0b4002061004003a40944001400515506c1441e0f50901c00c50002041f0107664080011a00d030002c074013203000c105c0f4101044401c40c03100081074156201c52a18038210b88194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 929705008 1250 929703758 929703767
    0xc03040c0b0a110d170c090109030b1815070e041b030902010212040303110607080c1207053f06010f120b030f100501080c010e011b0c1d0604020307 65
    0x1e10800501c9035000c1488140180189105400c0c800e80109562040202d180020503107040c0c02614440c0e0000b10002c42c482c001090140e4000c024107843d030a0466085484100208500a1101d48017548407041003410400c00e0000d00704801e2011402405400e0210740903045501020301c444c05540b0301f11011046d0b081c80740f080c204510080c1000100c40401c0d0004074103100b1070300c01e00c1c3e043d403400003030000030181d00801141206110b60261503440d00c40400c126103404003a988640c040400740002801c0e0907002e280a40c01c0304150401034070300b80d072050100c042001031140f07030f22207280b14140c01136106009800c0b03c000303038a0032240560b1030310b02100082d102000042003076040000c5540e4880c07280e45140d1011300c0030000241141d501042e00c2508907034071012480003c1c1c7c514206070000400b00000a08281c200c0c405845c0c08201c07040c10f400449076403161110f0404820b0400040c600800c6c0012982000362441036020b624400c5482059040307a42d0107443d00340103034810800c2040d480da20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929706258 1250 929705008 929705033
    0x4151b1101090906120b0a151a04120c090b180a110f030405070312090815040609061b2c04090c090e101a0d2303070c0801050c0304 58
    0x48540311400800000040303503000390a8000c2620b0500d07150011560034240000d080480c1e11991840c802a40d4841d4100c0c141c9422180c081c407000b500680501c89500c414040b40607800c120340449003401d56a504100c0c1d100b0241030140c0d040020480140040c0403d4000d2a460355400c0d0784000b010f09540c074850204100040001f00c0007561406014101c01a160440e555261204100c17602c030b003024102030307848092a11040301c0289401009011140c01344405c0012a56850046c00c80c3e1101c516111891000007003089408540d150391080002c2c5242c4a80c2402015903401c180a80c8070620001c2d00004007188030300d90711080b0340001c2c00100d01030b04400600766015100464100355900e4210180b010640052600c5400c264622401c2d4000186039101c8141a484c140300110380310b0711000000d403850280d660401d0905403d80046074500800f180106100840c04003034410745a02c9a0039a0041d03101140d102c0d070300c00003c00c5450800d008041e040500c40c5291461800d0548d03910341428503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 929707508 1250 929706258 929706263
    0x603150a0f060317042c241309020f0a0305030306131b08040204050124270e0603070e09030304030c021903030806031c020a03080603070312020304151b 67
    0x8a60071000e8510380307950410001143d020a942c54101800b1220b40d41c59089405000c07010311142c0b07422960351414050340e0564004103074800780700b0f4441e14108044003244086201c0e5030065061502455112a40310480c4400350300c100007100003852040044074005003c0d00ba214088510052002c160088201e0360040c1c03040302c240ca040d542c110540c6001d004400c3c10314582010351824080526005030016220314421201080a6038968090044540d0701c030540d0301c40040b00700d10040000d801003c01000141e207420780401c101c0c901ca0154a01c03214241c000d400c82101c0b000070310005044c01c02000d8040c00300d40109840901d0107400c40e95880c0402440074041103900701c4081c0035515840342c44100782c0211590451195102d08010b03001081c180c0b00d00d4024400e15400039240004506002103001690707010303046054182e00d040b21303520009000d059040c00f03245000070006010a0b0864440001c0e42c02840c1c0b600e16041100204905291210045c00700740a103102410500940100c2200d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 929708758 1250 929707508 929707511
    0xb18091e04020a0305150f0c040b0307030c09090f0b120309240421020310050702061902040803070b070f140a20060411270406090302191a0603150a 65
    0xe0790307800000d04980e1030750710240c0f0601822440044061a00c074009110303405540c040d005948920000790710520580c4211559810244041030102d8403e41102a03140e28905c0c1640e40c040e03e1340c00c5441185c090b10200031060b988c0fa611850740e820003801002c906503291000e0350401c0f6136000807a111015032600440322141541c08829a441d054040d240076000455040400e141815005034640c850b1132010f81c400c0c4203110f800c010590702401407610400840c0d000d805e454880b910700b11803180c146480700074120703028400411903880410190407d01c0c080c581040e40d50505c8203018100d2441100804200403501740c01c010b2550040d41107400414091414844442d071036200100000544400e40d0b6181c003d020901040c8030b007003a0440705001c4100c410407441642d070140410005044c04600f102e1782070003400180450312071f80c4604141c2d03000f401907465601070011444e040304e00e6078804581094440c900d9620000980814907440001600106a1569507801c100f0450000078107100c00f80d0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 929710008 1250 929708758 929708761
    0x21602031b130911010f201612052505030a050c0a0e010e010b0702040b0d03080412090f0512071a0301030c0b0306180601020c030f1b01020a0f060c0e06040b18091e 72
    0x144a98114107c0e050700c0c102000c0da83e00d01e420b00a4a4080b0340010b007008194040c07002c50081c0c2103d485c421201e5000c0004c204000000c2c0e81491041c540d00b8523a040c08080d084d00280a441c1400350402035403082c0040c20040301c16208214810110750091700e0300c001e101c6d00600c10036000e89451070556060b079070f00c03d440c1c011034400600035194601200b5044100c00c1d05207020103401010b09801184100c4c075070702e4400311102044506104511602010840243c01080282040410b400c882c0c006072040c1d5402545442610001d40c5410500b013807800400401007041c84081e000d00c01c040c1c031034090354a1841c00c00c0000104801182e9251440d03088803180422084d0380200700c16a544140602540c0d902c458542000b0b4a46d840720240401c02d1304003d014212641c4042840c0348015071010003800c0380ca4454a4100080c401c0c244644284154403010310701641d174107800703130004040340400c1703581c0e0f6280601001131012500c2400e50041100b030050042480601803868404c00d08264040400d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 929711258 1250 929710008 929710037
    0x3070308130819050d0b09060d1401020c030406081006020102030f0402040e0705041d190f03050f09090103080d0b030d140d060317040f1203020a06021602031b13091101 74
    0x1d0f48960a0700c0010040d40684050079513400c070014003c08200d030785040003030141c001c082c41501d507400c50b0855800307004850620300086004c51008062082c84000504000c102c02520b483c40e885604050b01141d407000404c20800311031f502d002c0190540d44005d5046052034145a0030101c40500020f20071501c0f21051420791000300a000000c1000078002e1007400200b14541050103c1e540222845004000240030100026000c04000c56801582c240300d1800d41d49044030250003d003c540d010420800820341203075156459980610f000d595034603030398010f900303440d8125004950350a0094001c0394070852500c0c1c004e4008101603c4c21030f446641c407500038103880014007141c7c00007450009031142d00c24903034981c1b001420075a010000d41c030f283d0136191080040f003402c540b500100164400300703058000940540181c41d40e95030580910010f02459070000c0d08101c1ca01d100c1c02400c80360380f00513026a01d4481551640c2004040c1c0820110343c40b62115001c440e00070080505108014024462 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 929712508 1250 929711258 929711273
    0xc0c0d05010f111c020f03070f0c141c03052505070611090a0512030a030f0e101a1c020d020612040605040302062409060a09020706020405120307030813 67
    0x203940030542d81007108451052405010380c0241941c1030300030240304001c1c43c01d08624400c480300104c203d89a641590f0f9007040458000c0c595000792410010900744900015480250300c401c50301c0842c000d01b030000d4031200360318161003102007603008141c2002d050181b1040005070903a00c0b80d0844030500c8562942510503a041d01c5549401048146401821605c80340c41e2005840d450100300c44a150300350741c0e0410030807055120803c2451640040250b41034040c006e910121382004050000320790080c40074500303410954820042e06000341c449541040c000c10207054100000b400b287c4402c42c2400c11810030781c461f10b5610f4020301941841800c08103655400c1c05503408810104450007031894603240c003c002d02004d540480c05071045c2e00103c2c1015121480350f0382181c5181d0740f00041348031f0720010449400f9025103040d400a001c10400305071440355000401d441da000f40405a544ea18150038011320401034101c004940c1c100784900e100280e80724810b04e402a404130f15103050001c0c2400d2128 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 929713758 1250 929712508 929712521
    0xd02190b0f03040203120a0f030207020315090d08011707030b2502030c12040e063c010e060306180a060815040308060a050303250f05210c0c0d0501 65
    0x1120404500d00c4035910080c07000354032942c800d0f82580c0903041c468659142c6805080055404504010451306a070b501c281c1c080c01c190f90000342180c4c40705508040d80100080107445000d040c0e08800315003030b50103400240c86070050200c183d42004221002c07415544600150000801c02d030407040108501184044104c03c000180305003291000c840300768082d41d01e0f4000341d06201130b40203425601004021034815942101c0e10f840d80d400740d5656802c2001607000d900404100880e225180a460018002c840301e0740c006805480403052482c21000500104040040d40d48654820010030606485050000d040c500c0200e00900044c0c5409141d0409010f4540142210b03100c3d03003d01d00d1241980c0304100c1d014501940301c400c107580302e040500010600314080c01b41c00d54020880480003604c0c184000104880480055080c0d842c603507220840d500404c1402e07100c45e44119507a44401c401c0000000c4441c2c2007105d41d511b0301d00c842c020240c48004480c0300e244610255040707041406000c0d041103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 929715008 1250 929713758 929713769
    0x31b060e060708040201020d0e0f010c030c060507270308071b1701021e16020603070203120108010b030c190905190e060901050a020f04031101140c030c06070c020d0219 74
    0x1507069107440382d002000c208040b241a401881520b46844405003e00c0e025440b99030054401c0080c10200c0d80190740d41c10b50748204904100316681141d0101e4454424503024032440e82d101d28040c04408810011104002245c070500e0200030700800020340910300f1540026882010350025a41c40c90440c60406c0c5c041e84510f1038080300c10f56200920406500405101200d07c03c1e58160200c00c40f0b0380e0000e80035880c0c84a11007041c0c095500050b11b04075000c0c50b40905240304407440c1c1070302c801e00f4a1003580b0170b81c4a0200c0e6910381e040010300380307014801c43d00c85690a540c0000440400c0380020341000ca40c0c481c1c00001e6984034045656141952a011800c4100c140144000d0b40c0360003000e0f68417441182c800c80ca80d443e1901207528011607008944050100248080c18941981c452203904110b00c6182c03410f110102905041d8110384070b01411129104d00040d60301d6901e100a1141451002040d640c01c200349103504e071005070b4641d000c0b49052030b01621180b00246402010b0100140b0f41d8004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 929716258 1250 929715008 929715013
    0xa11040803070f0c0e070203030a0f06050a180605030c090a090c03060914060906100b0c010603020d1a071701090b0d0c090c020c0d080306150f0f03071b031b060e 71
    0x840107020384200380f140740074442c014005120b5a074000400e10168107451060044e00100080380500966400924400c1c40210001905a40d201d0001d81d2100d490f5010705565040d13107500001200c09481802c2c0105070680280000c6400003000800c201e50041a03010403c0d0754080713490602008000c04005980d01136420003c7d6000c1e030500700007680081810907420f02c100c5000502241000c81c20f20300034a40e19452041450400c00850715541064400d094150f58649000015a44031202d100c1518003400b00003000700321a00e03480d190504000d1041e01400f00d00c00041b009240c0c0c2d0905039046440c0c6410015800035940300281440c4200e2002a120701948400032800f42c0c500d90200f503140b600e54088a03844144c0b01c050100c0d10b20081d0029000e15004d00020b0103d0600021044041c030310541407900e405c560100c2042c058204401420801c00c1c00720400c1038503500445500000e0002c1c0d45c3c8840c10038a2544c1c01400d140c4680c900000055640c00420304101300390f0403c140c00d0444030103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 929717508 1250 929716258 929716267
    0x609151110060503060a0e12222916061113080102030601020708010b0a03140a05030304150f02160615080a120e0d0c06180e10090c03140a11040803 65
    0x41c0540034140314000ca61080c0038000104030b07020300760700c6400641500c03d80600104a90300c074203000346400c054040c4080c4881d003100c00a0960340032a948000c0c00317900c03041400019010031070030f040d079008100e444024401004070507004020844000403085e4040b401062042500804c0000e900990880c1c002d01049a0000306455006401a6109e02002e9089603025644c402c4801d00780c4851603c0e0982100b00d145042c030208188030750003000688034000b260f049024a544051840c0d2084409403110202c0c51003016031003881c2e00400c83d4580010405500b070503800140000590041e14004007803943c1c40c911108a44000b5203100010303c40c2e1010755618070000c3c100820401015003a220000748a041403030200e14180094840e03003500000200451402e158040c4ca01f034000225501e942010010005940d041d03d110844c40340c90700e1010706117210301c2c0003c3c000a58500d0035078042403604094422040c0e418078006594406d61444021480300e10070f00c122001842160441e0491b80800034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 929718758 1250 929717508 929717533
    0xf051b070f060f15090f0c120902150a0509150307021b15220905010b0417100204080a1104050108210403140312150108040605061f0e011806091511 65
    0x3440ba0304560b01741e0710500c180d001c030141e030030b080b81c003141542c60126644011a43c42c000607079200746109440030b07084005804402d05041d071550400c1e100c4070000750001a1000c0c407814250303081d051021612125508500788031001030b480307410007040d580c6000612038a040c4c1599981420701d4900c0f8190760640d54611060728007203990881e0071150501014065000108188a4403a00e81202c2c3e98081050401d4103208114070300000e0226079040300d10880d01e000c0d01e650081e1008100a2090308000c10010181d440c250080480c0103000c07038401c0c0d1910004001c00310002c01c0000141210002d05551303041c80f24442241d5000d00d0300064909003290114007113040000008042d40c8181d8808416182c1c0c0303d0a03008980f12145d202540021601000324002a100340c002c1ca400038002880704a91417454884803007084055044000051a101e14608441d43c000000d581e041d503440c03074150400c0e41055005019401c01344502425a024035440a480910407800b05000e99045e206441c940e90484 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929720008 1250 929718758 929718791
    0x6100201061a1e070809134512210c18150c1e0b240102011b0c03020a0506151206090d120905030c010f051b070f060f 52
    0x4444040540c1d41d90780d40300c050f8040724041d0b07800a80c1c08a206071821440360144400b003c40d10102d0301c29182c44051801180c0d48107400d50461001ea03580720186072140d02031104401400644601c0c0801e411241000494000d0304e1130b0201034001d0400a642e8010400c0003c003d031a0b0880c203e0340c081c034040644080710361003a1204c6e2800c1c401d0307003510303915074840090004250381c0a1103500810b0302c1c4451140025a03200340100264000c00610700c0c4c4950701c0e141da040c0490100c42002105081c102c1e0444c40c00300d00c00e600b483d004000e2000708550010112110368110032240c05406124803601031404240c0b00b00541c020480d44401694407d050076580307040c0900b10020354510503070784041d205c5c080c0d900005000e0f10803641c010040900c90b0b00e228054580d4a8600140e00503141c4603580c040100390100010b001620503000001580000407544500711500504148070131543c504602c030303e2408600540d41002d8001c100e003400700d0146d1030100000c00c81d03d5a0802c030309042c00c80140c0c40c0c8006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929721258 1250 929720008 929720017
    0xc0b0d060f180e0709050c0d0b0402121503190c05030d0f17071e080621061504091b080d1416080904090c05041802150901120e06100b0309120d1512170405010806100201061a 76
    0x2070b0201d441e12440c00744107a1303621242811032000600d83c1010401a0022485742540040583c24040c0e4018941b880a9550780603403040a40483c003804140019403c0c0000d4044801c484400c00b030301e06400d07015003581c176003c020f480030448071420440d0b04c840340d135113038003141200c0d912034440b141102d59060064044001071250420394002d01404685190041244207601c0500d02e44441c68000110101c00040742d031403100f0317501c150f030611124005407150301c280c0c2180c1d4081d030102050b80c1c0c41c00f004c0100344c4e0510790740455441030501003c40140ca83c2009241820094680991a80301403001203c03072a030301d031421031407490030b0400d400360105010500038000c6082e0150078910030740342d0201c40d84a00c41a6112089540114200305c886c00e010006090340c00c560403404074030555201041101480182c00482003480c882241508000060b00c4079840904464101d9040a241800203040d864000b07142034042d0450303c0c401c6901034802e40c02400500401d2980d07940c0c050341c2c0250744000b03411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929722508 1250 929721258 929721269
    0xd09111f03140f0103030c170d060504110702030c061b0a0f06051e13080708040801050717010608010b160c0b0d060f180e0709050c0d0b0402121503190c 67
    0x340489242c01100c01c42d00300b0b4070a40b4201c0c00b0f5070b4944d00e596011942901808402d60740c41c94009501d103280c4001d04014002c0c0311920704045040ca0411040001b01c880c0c40041118828013000300780d0058501040f0500005400c030b805035202c81402c1d0307000030307403007803000441446025580e0903404000c1c20003208640c0e140180c3c400c000666503654510300720040d00740010180e0140d40005071231141c070703800c5540f00580729004090500d00ba81d6181040d940058008c155180d4685081084269124050952003240d2002c180303410351420304007030b000e04410300501d91400c0c1d000410001010317a00361040800c0340d02409413000301d40d4036214810700350868608102e201e810154001041e140c64480e200c20b44005038050040c0010940c41d1400809c44403483d4a22030250384800078400c00716118681c800c00c1c0500700150b560514446c580d08480f030310321066204601c1030011628060640a003940e02c00e010610f25902c0010341c50000f03141c141c81024030700301d210380b91441030104111100000100c49 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929723758 1250 929722508 929722511
    0x8100506060c3009150d11031006080702030301030b0703020714030d1406060702060913150807030c0f1809080f0703091a04050607060b0a180903020601080c060d09111f03 75
    0x4145101c01a5a031280003429940816017201c076242c04002c010082c4422240b00d4000503020050125103455500212101c07000700300300a00802c401e40e0001441c561241c12131024601d15811641e40c1890440003900810800d40d000c1001c80800c190b48848600440d01e030022282c1780c500d2000c001000d0a07241d20560380c207000cac200124034070707040100c1039610742035004207075a0400c00b03200306104107252080350701100c2c1a1100e009043c00340801d400d45025002d1030018181e40b5043d4240781d0f180c00066030081908080d11001040610151503e400080d5081000455441401d090030943c03809851580801040c1c000713203640130141c1080c0320780c0c126078030303070201c4d124514100510f550b49020f00c1c464190841d100300708290008540740e01804400344018a10004c2549444504429442d54800603030003075684d080c01800e0680411049004100000003440e46c1030860010030b102c2c1c01000c1522a0a54030703000e200c0100070304040380103080003020300000280c3d0402019408400003601050011a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929725008 1250 929723758 929723833
    0x30203120606281103160b06040603021005030108010b01020c010f0813050607050c0c0f090105060d0609050406050604290d0606050d06140106170c07060e0a060506040e0708100506060c 81
    0x1c801009507072070301a081c0c00c0203054101b6603c445a114200030205540b0690b1110f000c00140d851708039008180c001940c0e9035071298180640c0d64211000c84862605560140c2403a154680e07025421144000552070010300c180c4076410b541310030045003440103010340034010030094241d03400030240203455860000c44050420480500104002c401032081d00025031400601c10350501d0f400600a0544040f130020303400b942ca60044040301c5060300d040365520384810911425141901941c41114030058805880394040202c0441003c1301c440d405004441440c050014400380c2d0f4800c43c0203007009803260011610307a01d0080c0040c54540b030300c04000d6025900100715248074066088000e9400c91444010ba01c2e00c046602080d00002070440f01c080e00c80d25400b0b500c0c6800d20002c0e0141d0303ca80008211424400c04010541d848800c041c41203070310070b2030108500d0720b001400141100350850001095269200418034510508000610f540308060b4100020711088005203000300800d0400e5242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929726258 1250 929725008 929725037
    0x80a201e10090f09020309120c01090218090a03080a41010b07020103090c05031006031403091822080406030f050106050a0305072304080705030a03020312060628 71
    0x9501d5580100f02c2c030404203070810b0210b11a5a4002d42d0480c072241d00300d89400000640c031b40010b41c0b00001d83c0000717035151006481141004a0883c0d02451070644807840b40c03608540e103656694100102a0800a003040400c0d402030b4161320440c960703c05041070b451000001024600034003070700b000ca0b0b43c10b803001c96021346120a10341c5802e07050750b0304a0780fa14901003030f43e00118050087d00c2e4054030b031504400320008141e40d041220360729698114001092107403070b42c10903001d40b41001d10704901c0d41c0c108003c0c5500581c1d405c554015031980d00f12401084c0e4403415410300c0c00f0180202040881c544228000061184020250040311910383c0c0c28444045800c0320003080c0c5d01c080c800c00340845d505200010155020740c228650003070303c51130044c4440f820642050203c01407403210381c10a11300040c040c0030a09040c403400000d04420740c0107241c640340958000350b80340b00d014240c0c80c82d01e0f099000305100780e58041c129508070300303070003030030449001c3e0045000d84507441807140102086600d1a007800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929727508 1250 929726258 929726267
    0x60703020a200114031b220905070203092205130b090d0c0b04050c060313020108060301060506040b0a140310090e06010602030307031104090e0d0216080a201e10 71
    0xc030b8038410b03552900d0310384608a58210903000a800842004003c00c00100080d06031000740802618806985035400e500d038410403401c245a0300b05e5010381c0c3c00c1800308646903800004440510301d09580b4a00c3c0014051903035007a00d0010640c2c5001c660412041c0301c241d8201c0003200710030500031301d10541240c0ba900b01c81075803000f80c0701550010400741c00080740443e0401c0c0d40140e020f4000c0040d00c110400313010026200e94001c442840070027404004031815541e2000c1e01680c0100140c000300000d9090000140c0280110320a5101082002074801c2c01c03070b449015401404064005056180e09280a601000701e00c0c501a6001c600c0c1352404450003a0800070300103041b1100c5030080e40c43c507100d20000b1000781850716034814440d04200030016002613070340706031401e40c3c0300c07000035100d00c00308154000c1c200594203024813521942e20509001c2d80d00082804610031754840700251706100301643c04000050095441d50340000025200c040c41c2035000681c00f1034042c02c035041038014000203016a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929728758 1250 929727508 929727563
    0x3040218010f1428180e210d020f03061f0e1003140109020c0607020d0504061209141b06270d0f050f06160c0f030905060703020a 57
    0x204001c24100d04020803060ba02c0070b5004018003925262035080c100c1078100c622200320703010600407000b088080010803030a0420305c03000d0010240c02e1200c0c441c81c07444956500030141e55255412002005084a030100204840a0040d0401c055483e000c0300c140742d40c00e54008440c401d02809400305030640c1c0e540c0d9400c1122424580c6e4844150f08113281d8140203655101c0c40300941030640d1615400b1030060110003040c003c06091101598480b40b0404250405202805840c1550700c008002212103407c80161800e03211249820031802c1c00b882c4002018000b505009002d00c4a1008090014100414441400b00540c81042c1c03281e4081020b01000380309003140c00078020b03da181c5c0e80700340b04241c40620446100082c03400e254000162140c1003042c000c00c0003110640e00800c3c82c4890810b040c0b0500d135200481c010450703070350f00c540740003e401c5a40301140202080b10600203441014012128a005081c0150545450786ca0503d4040e6680c8480003050750340d40c0114a02856500004010b076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929730008 1250 929728758 929728769
    0x71b090b060f030423010e010e01200f18060406020c040605010f0e270705030703051005150d110c15010512070515161a101406090609040f020304021801 67
    0x2a03d595520b0300d4600c80ca03404640e4000c01c14048115070329040c3c20034000d0340b40b02d103280000010302e0f00b80c02911508458444552003000c400d5402c80d8809010031606851005000703031601c41c0c1d0740c000a018100c2e007540c0982125801507010a021074501d1f4000b50800304050195400c0060315251001507541c041c0f1141c0c0c6200103024000034944a050651151401d284a80141c404002d125020b404103a00c003290140c0000300080304103c0c08641c54000e86030442038800c554100182001c01241c00f005c41c2da0003507126400001a411300c004499070010360f00c01780f407020301a207480301c85404644841c45c01481605684100001181900c0e000d003126000d00b1030346004020017460401442001804902441d041040a101c010f28a60010331070200c0e980c401c024a03e401c14495640090883c07002c3c0401064138601d0806001c50140380c0c11101045000700c40140d268400707100090340910845080c90740050820003821542900c58005c0c6010398400c0741c0c0c0185440380d801c1140c88801c801d00c1031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929731258 1250 929730008 929730037
    0x170903160b09100c06060603090c090c080a05070c020d0302010e0d05091c03050d050f041217041b121a0105011701060e01140a110c0d0f0b070203071b090b06 69
    0x10000c091030480400d04052550b4101350004d8100d5898100c111009a070001020036200c000c0032042004003000d013006030001b12810040c1c0710038000010009917004207528601c5903101c01103880d0038040e80801c860ba640c004d290f05020a00f0340f0b0020f01803c10051900001d218150034058030500900648a030a14090860b442102200c07031600c69a9200d800d065050003020440701d0701182c4076014040c464510b003404120142060b1800c64080c00ea2030300903104015120301741c207240e1061740e4060b03508960800c0180b04445483c2e6104035020746142c2c019604150400000000c0100a0032154000c01600b000b10401da80c0c1e03070700150b484c207403030301c00310b40d0060343c1040103011041c09801800356600e8103140461004c3e5222010000d154010003905001c00d50803108503041c0c000400052204d040c05561003110146140d5036041100d01c2000002d01e6292884002070185100700300b0b480b0b4480c2c219546030310a4a02c0c00802c20094a00c0c000d40000e98100987d04900c5d0520804440341054081d02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929732508 1250 929731258 929731267
    0x31903060f050f2b0c052b0f0c17240408071b03080c0105090d11031803030d050f150a0605040504020306010e0301050907180b03150406020403170903160b 68
    0x2c1040b00c0e516860700021841802c42d6551a01c54401303040d00c0c11610a03038603529030906040c10050b0303901040a0f442484102c14a014030743c0062008010303100d0381c1c0507440c1d03a0002058644990b484030b0a0300100b090868103102c41d200400d0000b201590345411001003141d4032a409040481d01c01d0468004d480504100724050014102c002882413503400e83d20413140e90354503540c5018083d88640100402070b9125001e015010100784046a2014801d0030800c1c03212511002041e12401200800000503003403a90380c50380ca440500071502a40c401ca0010841813602c001691040d00003910141000c50b080c071071204007820221281070546259866242c1468036082c100700c00f950005001904002c02c01c468403a03251800d000d514011568140a401d4050600111024010280c0c0407560410304203c2103100030740740420040038111940d0880c0704183d5031818803102074443c41c2d00c01441902e400c1e942c2c0038160440320242081090440a40d20403401d0710510750300301d0700e1030f01900710440010007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929733758 1250 929732508 929732539
    0xe01050102060619050916020c0301290102070905092112160c050f0607030b0102010207080d090f05101b181e0801060f0f0b0301060c060518031903060f05 68
    0x140b030010701c0100700075a07900d5645ca07500494a031401c10745000800c2d40c0792072400641a038050141003201c0c14164001c103c10002004103412648180d054094182c0c2807528115007a4401e20400c005410002d6090002e410720f48134180c2d99140014043c00c1030071015580001052141302203d1a4003a48441d0060603218100e84080030801d03d0010400c0c0841000302c02c00003601807180045003070000020701150720f1300d80e4001d015100ca0412582c1164410810400001c9604c0252203000a800070f0000380c80040c1d180c000d131108100a005007161245041107609040540c00500c010400c1ca180440340102515040d540b4019106503a01ea04900e080f003880101d454142e801c4841000c0603d000e41141d031121031500b152200c3d04410340c64480440140412074540d4515002440c03240600d0340f940d80351080c002c083e101d10300e20040c0030a441e07130081050380d8602042c480d10501e80a090325511890441440d4007070043d5480140400c1c00c0100004a4150b41c0344403904598010381014403261001e03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929735008 1250 929733758 929733769
    0x912100c050a050f0f04030f03021518120d0b120a1505190b040b06040905040c05091e10030c0e0a0b040506130b0414090706110102041404020706140c070b010e010501020606 76
    0x5e9050041050920002022034052000222070038026005030450006030080035240d000010000720001c190720b202040b9691001611406904036455680c2d211303002c00d0f102002911030308a16a51140c00403030622101240450309101461250f6001c42c070040c2443c0a0b001951000c032044218030008000c01c7c074061099800c1081e0b1410000c4c4005409600071000807050307041500b10540d0150307904102f0042105e0025100c0241200b215075101030328141c0424200500c050b00c40403014403031000441c94a002c4c00d00c501015641c040c52045455444010648001d90200e0304090b109042c4441903c1d0750500340314090044a01034400c070014014840020050005802e486400c25941d00c540c2800ca030309142024002c2121a0141050525000d00203210711507440c544d1045910400c0100b0019801d909500c25104040c0c5015071a100c49007400d00050200c14282c080c0d079a0303030b5010007010514150080403110320601c00881d080e603c0d00c07107845001009008641c050780c8581d01140c220710b020f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929736258 1250 929735008 929735017
    0x1006120f02060a0309080d0b01021b0f10110a0803061306030804060e0d060501060203092d28090e0d020102040b03040b100f0b090109051009090f020912100c050a050f 73
    0x440c21301007403641955840e070402d40d210042a0507815500c44d0b03011125a8140090400801c6e5144025142d04500340012950f400610301e45225654070034246503541e00030300720481c243c000d400c2070701d054403204e0500907201d0b07000301c503d54840e030380c034890400740b146c8180309807010350703401440319802c05007404010358010803210000d0768030407021441407001a845003e66406804e03590b000d1030f1200d2008003403001c00d060340ba0400820240c280c110000760780307000d0240d610303681d0b040310314404950782c0050034280c4140081031809003449030302c000f00341041903410428034480043d040782d040c0308112808908138010360080c89042c81c41003004c0380209605190280d000a4038815005080b99640d882c1005101c40341d02c01000e0102c0032400c643d00d176800070340c070400038902a9000800b4808d403100090240b41d03136004031003070f0031380c3e445280d1880081a030558034090382c05071195007840d000242c2c00342d0300d4800340d4a14240310b00300400304120902c60f500361071003116262503050500110710020460340e0031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929737508 1250 929736258 929736277
    0x70e03010b0316060f050715050a0e030c210408070938090c04120609141e100b100e31050615070f110a03051006120f0206 54
    0x48810080d20660b90034429020520034807850000300f00d1800c100900355a890500b00b81c140300f41800284003061041e41c020401031300c03883c4001910b6650900c248010b221840c4840703290721001c248030400f041c0c0095054801c0000c030300b0040400c1c0100c01030500034070440c0100d00c05a04004030411a801c4160410501310400500c415022014281400318400d280290380e50300b044c03085055456403c10004003074000e45221403c900d03041c10035150b4120b1409901009200683d207950ba6800d02140304040400c0604010540c2c1e10803108004143d04000e640c410303094240104e403044152030070749100c0c031a03440344040d0825284007940350090710f14010184115030490610101056142080e40082d40214030500c241400030030480102000c03100300030502d0f03006812007100c0c4e000031224103085da203146501001c185064041c500e407844070880100451a00110324034400710802201142c0483d180082280801c590795503035a0744609003a03040f501401d0001a00c0c00d0101601308113008040d11103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929738758 1250 929737508 929737511
    0xa020f1209090621150a0b060f13150504061b0302120a090305060a1a0a03020105042c0f180105040b0105010f050c06010b0a0f0c020616050a20040e15070e0301 70
    0x10429200e45030a07510b540d44c990701c2904580030b901c003c0785e40e0140c0c4c0c60b00040307a142c0400c07100d944107002c07640c42c0c8034051a007480300101141e070080d0912001a002c1c01b414000c107800c11000060807001e0f003590400d00079900824120000c045011110440c0a00034130b8265000300410344a01002e440140d021000b0601003206c20300d00071012803810054140280b40981002070040e502c0300d6180300d4a0b50071024184142c030440c0042015030fa02c1015281a60300c400354100404003010306904c0194204030380341d1181e0760350b4801c000040c00c11f003880304d07c20110301100004545403400307420308849007100d00615070650b84005008070b520076001e40d0905411400c0c598a4003840d208020310b4280e09070304c040c0d034505002428a043c00d5015410070422003031810700c02d1140c1180c0d4001809402040c10751154058504030030130a01c5030803c480d5100581207440440c44800700040580c500e907071030900c98012400c02218569203240020300484000e07861a40489548800000302c4040d543d900000f0b0b0700d503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929740008 1250 929738758 929738779
    0xa0b04031404080616050c060c0307020a060501080a1a0f01031b1e051512040228120204230f04051e0601230120070315020a020f12090906 61
    0xc40107000108040d2045000424051401e013106555019120b0302c1d4404010081c4a000300a82c00000c55136001450342100d181c40b559403100803890200a4a0b02404180c2070000004440c00040345007002c860149007078250445008814000680c0c064030320b030406100420040003c0390300166000b44c00c00101da0f91807e101c2d0b5a01050312402480c0d03c6c603020110510404115030700d0a513854808010503850301d141400c40219a0f0408100001d001a024089017046184810194021610710380d5180c100d0075482529a0101031408610003403c90240d031401c0038040703080382c24021000c900040001900200e50705e081040b07002e90030181003110b0600c00d01c0c58408903e50b4400c0b1100c46070420f60b0040c12150316141d161503130a02c0c1c80a400c0c00e0300002d250440d8050b40e12954040a82d140010b0002080c0311002c045458489150b002500c0921140d00000503c03406800606800440341c0c210303034440c85140d00050311201b102c03600440070741041040c0c44031b50410444441d801075005003030f960304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929741258 1250 929740008 929740037
    0x8060f060a09050f06040e0601050d0807140d0807030f0513060e07051005090405060901031211030405060703030f0b040501210809030d0201060e150a0911090301090b0105031203090a0b0403 83
    0x252032055500109810b440d0b010000e51b4105889449014600c0c400101503a500d40030104808030001070b0050402c0c0c0001400205002018901c200b401200000329151000c10a100416518040e100307440003a0800a4108500403280103590050f03800220702040348842d55506002095280c4042a2600075214001480e98078141001007117030454648594036043c032010481142d1004028a03c618020700040c008a042d00c442020b901e000c81c1172044603d052100c1052540c09181e10459102200150480c205a030581100c0540f403e20442880350255200c00c200a0341d40c24050b0780c80140c4001072110401b0586c2001030030f461f018203075552400030f2500110b81060709214290015039103a210411000e5003110519074081e060f41076801c0c42007903000004600001600c24503180fa5214100d410380b40402d04101c80c0e13590402002004010034929007401505070900c01e251007400345980d06208980604100c0b4450b40070383c00949100d130b0701d035a15020790b40340c060025020084a1784240e400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929742508 1250 929741258 929741261
    0x806010210060803090a080a210c0501050108100516120b010c35180f0a05030d1701080a02010504120c05180402041a010e22022106010908060f060a09 66
    0xb07410031601075940c9002201c24044810342c1ba92003203405a100a42d18401304540c5414864248103d0014407000c0500b8481110b00071786401780644194a01400040c40e0540040c6480c040500c0941c00d11982e03a828806c8920440e40183d079a0210b10411024100c64085d0707802020103020504144d490511240c66009002001182040484884101c0b000004901600390ba40207110604070501d042c07180f001c404440c0030300c41c6143d4000c500410314044e099840c1c64904001d00001350445502124402c4018446595040f01e0b56001080d1710002c9880c000101e800e050a42e0180c40701441c040c608035500340400d60100c3d0a6440300060003010410f991100c001140e80b003044195040e0314105401008122210010760307001e0141030350b00000850346c003d4104066044c00b102d09130440c2e007180303040707030b00680200030b105035194400202070780e041020050346421401c2940c50310740725a071400c0042d10b800006010703101042d8007a00c0001e19007040d10030075a9200300c028002e46025651005180d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929743758 1250 929742508 929742521
    0xa0215040521090a0e011503020d02040e0406050f01050a0503070614091203040303120504031d0f030d020d03050609040812101206060302010219020a0911090909010b09250806010210 80
    0x9800240006110380f03145400e0038080050240e4240d42a403551410b5010130781c1d0900d488480e02859000314804400003c00e40c1558000e003486404100903241901d0010002c0000712605440010400c0c004543c904002d101181030703c80c0a001401c09a007045000c0d214091941d02c0070b0020802004284001d03194661f222034929604401961500c0c11071074007900d08800480f075034081a190404010100380e0144501c0250010035446410710710106004c100c40401181910750103100d5848031080701c41d0700080c8684030482c6a5410001d540ba171804020f4021000e075800b40c00302206004007014420030034079541d000000b144081c1107071a0f0710012514030001819080da0204d9481400304250f50301030180848078072030340c0d10017886410982d001800301810ba000700040107686042841480200b04216981c0c0c210080100034546860740d40903002e4900d030110036002c0d0400c01c022840c14030b91022007140188a140407022982e2608500b00c5031900c00602d05c904510864101c030700226400c0c468130 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929745008 1250 929743758 929743813
    0x503010e150906090d030207020103020d14180a020907030c09080f070306050105061c0c03060b0c01060812161707060203040c2c04150e1f0c03020a02150405 69
    0x1c12041e400342185018607100141000359982021081010031040800d02d1071340620070b42001a111095400120005c0c05908803440055241c118000004084416460322410400040102e0b0f40d241ea0703400c41d19100061b1009420516160110700094043c0d085000d41118031b1401806a40e69030400d18500000d404800103203420201c414024007000d03005050140a040e50075602c0c0080513448070109542001c0d01d0480591341d40018010548680c0103d4000d04800130010344850003007448a0080c201442441d5051040c4440100300d04802d0003078801d202c2c00340025001c000200d40380c2c4c0032404d03030900c400d0102e00e0041000000003022407019501507800b505d00c0031b6400341000c550f11a156003102c250400324010114443d48200a4528540c0c0300d9032100607000f00401242104014101114030b4032414001e07284242a0f0b40b084c442c1d000b50448440d402403140200e4050180c040340724003880000181c00c481035401725061840c1c4030301d030014850422030381107000c0ca0303c524828910075a2074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929746258 1250 929745008 929745013
    0x7050d050109080a03150f141011010e0714040606080c03220303091101090b0406050d020c1c0929070f06020a020f0c0a35120421080d0e03040503010e 66
    0x50343c1b9900d0358106c805000d09040800c0c061040e05141441c010084100c0e0305038403403840074010310861440381542121800c03141009001030f9407040646500c6603601c0c0505488501c0b641c80c0b481c072a1800d4090101141c0403510744103490345600014204507070000300505e44001c552078104504a00022448508a0003a600016210a20301e1700e0010b4034000c07a4403d0400c5490b0209208c0c410f070a108607412502c1d5810000c1d92211501c442c0f030003174011a401d8a04500840840c4283c1c1c160030061144040001e0360b5280f070903a1a8101220030100d034410a40c00013040b500b500c40c0b1420b44200611015001b6840c410741120180e64010507a4865250340c0010707001011440c012440410004908410071284e10324282c4c00d0100b249080b403a4248502961030300c6940606981e0404000e681802c0d503402c082d68801c55011803513900e6640a0b100702c01c03029080d0f402d8481094420b007545d01c41203921803a410302d0020a14141005000c01c4540d0141901041000207040c4d68240f10742508800e01001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929747508 1250 929746258 929746271
    0x9032104170a0b0a06180b1011120301170d021b010c02040209090a0b01030612020f042706020301050114130302010806280302030c1807141c0b03120c07050d050109080a03 75
    0x200720641ba05c0414480b59000c1c01c144000d541a80d460514400010381860700f1190782c041c2d4141d2a1070486401210b0f0704406000001140c0c2458660001c41001c40c11811116000c2440104076650320041078075008080c11814020460f43c8101d812600700750004001508106194000683c0c1c0c020070790b0124000d9035150400499545c040c003d400080c01d1606c1804942d802c1a00824040504c42c0c8055104c0c0350346403925003865001c92072203900329960b8010001c04040c3c81c031301800250301c03c0c041c1c5804a0840c3d00e8000841e500181214442202c01c0100c0e4009403a5500565810038040c0119500c0406496003140c100c40c00521058401146880d030340116183d40107060902c0070b0394018a008080307601076002c0031401c200c045500040c040c50301401c0c181c24262012464001e90103510b008503282e1031400103004150304000f40b4808118242c5001010881c901c80081c4500d041d640440d8120800c100820300c1c4c140f200d0100c035806a400425002120360b5030807429803000f00300002099440700d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929748758 1250 929747508 929747519
    0xa030605010e101e090b0a0801030b01050a030203100c020c030a06051501050c0a030c11090117060c0c07050118090216030e061c0203060a0f060509032104170a0b0a06 73
    0x400d00e0322009503456505060443d0008001c0d5145a903120007aa22440b81c44800030b102e81c1d20640140100c411454980101c038200412800c803e100941750060810008a154500415040d044960080061031504a518002c60260810300b0640c0103600800300c5001c040d40b410b100d082940348c81040c0000300c91400030340c4840e0301100da070f00f1541009010f1003e200c42550018501c404da54150805400c040b905181c00c03410035040104d2141c20101d140c00006440c4042152030300c0e850300500684203d503881c200c0307086007030182000b126115031101008024650007078900312098024079001000303660325030714000c040c2c2c0d1003541c103844050b0045d070f209003d050740640034011402086442a00c2c01c3c5405507251b0b110742c0038441c0326a00c25400000b2800a9590300c22b220001d20780c000300907003419541c2c980606244c000441041c024000c06000c205c0a02e02d0444e0f00c241c9480c1261070030304050400c1003540d902d09005801040c1c51040d07080b088007003200030042c1d81c4a00042140402c085041c0b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929750008 1250 929748758 929748767
    0x110d0c1b06050702012304030c03050d0c1104150314030c2103040201050d18080309010b04090c1e0b0f1b031204021207030204020f030907060f0806091503030a03060501 74
    0x21a09544030040001090050950080442d51016024a0081c0c909140458803580d0308140341500320181a0025000027001580d00740e550450740100c040e1180003122640070744101d46e944034002c0c03100e0701c0b01e1840b41d0580740a51000d100110780710140c152080d140d0741d6130003210304441c51761055680f000c12240a031010400c00d0050003000403400c1c4116031100c0340c03110400c0c04040c10090601c1808546440c0002882c0d1005ca0f03a01e030408046441821030f802d140034903500507540d5800e5542800ba0301e070450f05060041044050344200b05030f00c072034a41482c21041000b000e54017107c1c7d000f0b0700300c0002d040e4070728400303404e8000078200340b03660f07510391210319110840709250010041c0d001803200c0034074400c40f091000e50158060381c1b29540402d17004c58079407c00700c450304000d502c04c4c4003103100095900001c000c0c610804482088030801519002c0c155044200950f8000c00542c03c2c0000038030500340741156513002107007010b58800c0d000c003080c0000d0030b40c0c20540400001990380c2104108a43e0710 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929751258 1250 929750008 929750033
    0x24020d02040f080327010e18070f030209030a1401020c07060906020c04060305030d050601050912060609150904061a10020a17030705040b220e0a060504020325110d0c 73
    0x5034000c5107890309000205032150945580c07602e01c0800326210789441d90040d40f80100e010801090701c0170602c90b00103211803039481960040c1c0001d2b500c201c4140103c1c064030032181ca04900500030035070b007400c07540d0780c22402050400d509825502484070000045c81004101d018000761b03160307481224144140245088003980d0440c6c8191308104003000441c001004580c0110265000400c2a80c3c03100016274142c419066000e40006030000c440d102610003281980c05403408540080207602c0303030302d0114400701c00c1050450380401c90801250004080ea4000c0041001d025140203e0581200020b0300c0210640541c0c0e000d80c122281c40020009044962070101782c044840d6815070408180041c0107000e0390050f0001010009104070b000020069004000c200c8104404041ca458491201200105031147c02103123080a4012466207003070b00940303104008880703802d1140a0460700a98208428a00007030130b001c245031122002d41018000c150310800c40307486150510b1040d14145c0103e461 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929752508 1250 929751258 929751269
    0x705121011180d020f06040b040603062c13050102160b0a1b0c0501060306020c07030c090b09061513151115060427200306040f24020d02040f 62
    0x700300441c2001c2d441ea0001e080c9075000c2928864114590307840440c9150740e0380b69410781d100201050001c2da4001c610010415507520795414000c29940c0d0364441c480c0d9074100014a10000c4150100080140c2a070f805540904600981c403110043c1b611030608a0f4820184d03802c0301c0301070340f240005108210381003c0d02b104c15044200103090076094010b5503041c03200d10720410020040704800510809400101c055030b00418119661b0303520301c01d02039403594140310455110078110700003e850211071191005081e00680101541d50301c40c010000710300f4551920f065250b01c00c1c8060032030f00d6000030194000e05904004409108003501018004a40301005111103a2040150003118402081c0b080c2d048201a1004102c0720f0307008460201c0001c4004e581da600c50400444401072000c0d03000c198940300c8103541c2c0301029a89200505884100c03c0350068a140c0103a030140f0300042000410421100e00369040c2d1040d035880c2c102141c01d036402820b2081c00590042014400071040a014100429 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929753758 1250 929752508 929752541
    0x1809020a0305010f06170a2310030212060c0f090a0306020703020a0b100f030821040b0f31021c0818010503130803131208070807181707051210 63
    0xc81b0110305802d074503001000641026141c2292103007800e85030703020303584d48464010380c41e820740740c1210601d100681d540b006a21540c1d100c00d41c0f0010381c0c4045050380c05400042400e901d0650b80c3c0b140001c10764000f41070550071000c0c0040010100e1002c0c0b0203404000e100354041e00b0144c030704d410403050340072014054075000840b81100b000007900c03e20f00c0d08116a030107240144c541e1a0301c01e080b00c1001e0b482c100d0f150b80b000103804000c10001d185822610805417045840c009032507481c022070304d800b5040113820503c1140c0c007510540041407086010420320040282d117007007040d201101d540c0100c8030b504440711070020a0140f246a100020028010740a10b859030540c5440240c111a4403202e540240092400001103100042c1c1d07400f008901503000480c0c013554181b040b000910015084034080300080c0c00d40c000c50312040c071415624107550400e9880c0310800b070070114000e0b04c0040310901c410151040e40c100080c0d68035021210304081d10000040c0040d0f00400594805464040c6194000301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929755008 1250 929753758 929753777
    0x15050109050604053d030e07210516060e12060408030f09010f061409090109050319020309030601123822051b03060609071809020a0305010f06 63
    0x15201c2c0c500ba202200d030201c4400c29403004d8520015507020500340080c48072214440354001c81c0954802c0159690000c0c0e07803c21072425400c282c1c80c0c0740d90047c064903501c2c80d003100c40c0112010741e40d001d50741d01c1e5010b907090303c0e4001d0510158565403004da6005002090010100b902e41e03240c800c1d103072904220280b0242c81c4a20b020b030b5420000d880024030745590340c5e04031030100f06800000d5100200e0107901003410400b05845240c00d00320302c409400d03a40d101e9072400c0b0001e04059410300442d080325a10a00450421016014500c0180b09150061046110a000814866608000c418002e00c580c0448110020315420070440ca0071403071030491380000c50107401880071114040140c02c645c5d007440c9050041e403135500d402c904594030500c01000c0170500c08607901c18000c001c140441c0a140d0f000c40304804088000505889850840d1807541c4808488001516940105240010f00d690000300408082e2a60b00c80320072070b0000688940041c4e5a100103104190350140000e01400d205e0501c503da1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929756258 1250 929755008 929755019
    0x22710050f0a0c0f0c080102030a0501233c030106060203040b0a0f0908060f060306060d0b040209150307030b19020403021309330b0d0c1203140d15050109 68
    0x2d114588465003008401c041403800d2288800a0900045e80f107a0000103584c4c1e01e502d80750103500241c0e217041c24185030500000310503905000c01025170403c450b410003140340d103070100b0107103904810300c1d141d1118002407650111001c090303010310344400000c100e59074042000c00385807c50340c181d0849030540d40308000a015011440c020303107081403414603202c044006055000c55014038603610021a5110b00c2042c05044403d204459100b403105a040312000c2e0f65100400c005880b0442000c0e269009035030200f07016003000d080d040d511861045a001140c2c10110110b440c1001d9070b0300030303203800c2d00c0a018818502401128664803c94284e025424581140c000506101071590711000840c0c2d1003030b401041005845034101e0740c108824110101c0c44141c511010820410917540d0503030340c0391100038142454205681030880e074002e50025005420110043c0d20458110403c3d000d121802c41980600c1c021000142121a403140e07002c28504c14100c50100740404c030341c101c1070500c00c9482040c4807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929757508 1250 929756258 929756287
    0x6150f03120309100c0c110a1502010504031e050d05041b080d030f05190e0c04110a140a0c120207080d03090201081b030c1602120c03120405030a06020a0302271005 72
    0x1d1260082c7c41c1304484030038800010040c07030269004015540c50b00084403c01c58041d40701d14840d900030303192210400081c14200600882078802e010201c1c0781403020090713620450748860761040c410784191407071841034100502070750000c0c1d00c41e40e4103074842004404829814014040041074124007804141052000751501514195500394a01d94035601c3c03407000c1d5810415100c1c5400003030010403542d4200c2c605a101075201d04907440215803e0410126080380c3c0000b01c8541c500d060350f401c49218403540da0700ca00302a800d602c90341144504840031904240c1070041400c1c0e855181c90028030b01e0744a01c005000050014a0510400445001a4404c449103002c0300d07800640314185030307590800d04180342d20034060b500000e034000420360481c85110500082d2640050070443c1210300c000042e1044444030301c0380b400340740d0701071b0000300114001413100d4014042c850843d0030058101b070a1030805d40c0c014461208011011041d402291085040402c1c642c03113082c41c0e074641940303044481d041c10318 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929758758 1250 929757508 929757527
    0x7121d070617091e0c10050307020714030d0509060d020d09060f0c21090503040f08061f060503060105040504050f0a0c0507031d061c05010e06010f0206150f03120309100c 75
    0x40d0140520384d8040d4000b4103000700c4e5076540005012403460344a4a10090030742d00f0440b04070015205a01c0003281c600d5001003280d03c1104001d00401000600c604219143e030003696041f50041030074010402c4040d840d0001d8001410010000a0f901d5032504140c425a0054140c42c003141d80b40110403003000e68403048080c080100554030301081c0d42d00013003600080042c1c802c003404501000c134012070315100341c20701c80c4100c400c07044c121343d00d41e00c0f6441101c207000400c8014107040014150704104c0e180c0148065980518141406401c00e6641c5001c141500e008441403840c181c040f808100c4142941c2c030802c04014001d290440c280f45840d0b40c00340003072055004020040070300003144141c6559a6084404404ad955607447c240030942d4202c0000c0d100078011070440701f800d40b0010781103500c10040c902c0c807004942d0084c021612441201b1842d031800858203074102800c2540054251003c118030441211002205581c0e07140c169040c5050003800c9600c0d81e029401c00c42d000c00d081e0b910a0052 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929760008 1250 929758758 929758783
    0x60906030503180609060708090a0f080319090e0901140108010b01120f02160b011508040c06081003060618060f0e0402012037030807121d07061709 65
    0x145076160000c030000b03105005600da078940c0060001350f014100402d23000905a03111098511202351034440d4240403c0004a0141900301d510500010320455403210410940d00130a0401c0c000c010384030f42c0d800250070170031a100c0d405a07460304c1c4441d4105c54200349a60040c500e11008202140222000810046480d0b00404003262561202105910b00b54100c9502c0300100340040031508a92405480350442481f03030510480c060800580094040c2400038440c07a03128842100031800c02400b91581a00078140c01e206241e003580110014031548507580250281182e2000c84004541d1540140c45858110000e000f508400400032521101c8800e81c1155090070100a030205101d2080c46801580c850100d46104011850000c11a101042251450000006011040031840d50303103000b4030b42d603401000a100e0303400240f0b000d4400d8524882ca4102c0c1da43c0420b45e001c2c80010000c1a021101c2d55207096000004100401034000c13590650744003003100808058548110402c0e00c0ba00341c00000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929761258 1250 929760008 929760037
    0x70f0806010906050901030e0a11031b0612150a03050610050d050a24050a09031103161b1815050a030308041b090507030515040902091603060e0a0e01060906030503 72
    0x2401c1c5d02e03800703500300e05810021802114800c040d17034201054041010004507010740504844000942d1103e40402d28200c80030744a10f150042460290190b100d00802052a003013456a210500e6034542e6002170046005030001d12080c10319030400b100301c001d20b40c0105c2c4035950501000c00040c00100d0b100041c60380010590304818031035032132901440919a0b45a01c0b2500e0003041107a402e200d640a2203405001e6035a41400810602038256240f00f0454800018000c0140a4000518032440c00021260003030704101d500c0d6981c0715070152251806a100324640e112003a51082c00c0683c0905401070800300c83c1c81c840c0070b10b15200074103070501c042c001408503081c0640000351000d030340c03500c0e000410440c0700070065450705020050050030240c034506a06079210903002200d14041c000d06a419800921030700480e00c0d01d51a1230f00e10010b0100c840c051603259a4002400c1c00311030a854825607041401190400c030201c401402c5801c01e420032102e1510300541480410350000950304402a000b45 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929762508 1250 929761258 929761267
    0x80a02010e060c030f030c130f12021306260607020610060503060616030c05160b0409091b0e1e0f01050d0c240909050132030105040b070f080601090605 67
    0x44071411031107494440348001c5000000c3c05421100347c0001c00c61074100300d44c03001c00302ea200c2c0703c803400d00d101d148914007070801c107102030078050b107001d086010110440750300000d41680d641104081580e00d403500b014800701114154980d0701401e100195018015201900d140d03d8482c0401c08006654002c50040000c0400024003d80b85c000440303215075100c0c0281c032003441591400070290409004111a1030246101602d0360100940815090301c4034100c0060406080c4000d000041121002c2521341f89038603000ea000601e10030011402511070104504c81d00c0c034280c20807080d20464050301e0380c1c031071a00108001c0c14805001040d41582c50456a4680c0c051050801000c1c80180750003801c4c1c141030004503403c6c5105002074400b00314000b40c5401018a54805862044075001d00c00c40d100902e90122415444840c0b448240600301e00e401d00e2014085120040f9003190380031207046480044240034800000c0c1c019006800b00281c502d0180c0e954505000001d040d03915521901051100214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929763758 1250 929762508 929762527
    0x70b01090b061b0f150a0f0501050a051005040b07050606011704020105071112011b140705030702150c010203010305060604110702010f050a0c05150402101103030705030a0e0f0c040501080a02010e06 87
    0x113100310045000e017258840b83ca04d441c211550802a504401c0b81890001060207000f118080c960403a030004008c051480d240005219000130700d055402c003005400c00000c40c40b0002d0102901c901350050004040d10700d4600005414051110044140100b401d8200b00060703a01c8004c50350095488595454412140710200d00c410120307240c0c00807130354244201c01e28441105682407a2441c0c40c0d60303c407001582c880c08440d15a10a900e005402500104200d00150420350080140344405007070705803519414144081c2242c02c02c0e001101e147e01f042003172007003516042c02044561084c010b0303010b10b0188190b0001cae1690400710a6041445404a1300f04a214090400c0c2c03528603030040299980c406070600c8000b400ca404440c102e100d400d00c1281013040dd88030381d502c5000c1454160043d440e6807280c55040c3e8090b08000c00c0d41940f1b544403054404a0f441c2880720401c2c4903010401040c40c41c01100801c003d1f2070b0141c000c40140d03030020315101e000d0b0ba40003109004a100985403da030300c04882 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929765008 1250 929763758 929763763
    0xe131703130809040f09120e0d05071a0910030c0801052209020609040c03090c080d1b26071104050c0906030a06030605010e07080a06060f0e03010e0111070b01090b061b 74
    0xe80760301803440c9440380c06c83c10f01940d900356808040140da178041c88402000c013085200d055000014005070300c2000b0901a02d4603100342d110500d42e40c452440c0c100507160001801c1d0805c003401d808000303502c60350040c41d016041110540505003c46030500340c69000016524842c1c07120b101c2600e603544400644007035440f440100d90701440b010b0000d0125800000740507024107091b51007220000d2400400051546011030415220030090f628050602c0061100b05102c03d10500d0035600000e06100140020002c411001c07941c12600141544a0015041122110994402d0680100c2c02c203402c100d0320922180403580c1080301140c01d1501c948480c0740b040c009103410b82001781114540b03c0042052110310080358403a8070340c0d82c1c48418642e40c0e0f800c0303101070f101544100004a2041c0c01c200da0041e0051008504144000d00001142c2c9140081c075401d45902214911903194000790a209000165660601402c4c110788288400015000404c0b0588a510a08010409840d0b540760483d0000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929766258 1250 929765008 929765021
    0xb0604240c021201021b01020306010233010f170705030c0d03090801020d14460c050a0e150d0e12120a061d0f100e13170313080904 58
    0xf07000103200641c0980780030b00075071015625128165200002181e5010140202d80c41000c0c10380c09040d98103e0030701c0c00c802c07403241c010210142d8012045440201c02c88204258001d1456017040b01d4181c0c5061145d00d40e10003048400c00e80b41d0002041803001c3c0d1000501c94107406029940403282045504040391149260f4001d41040d500000d80b4004080850f013100801c00140b4488454680b101c0080800d050141c01d24400c500d02e00900c05607207142644000030244111400d9030a84081b00c643d40300480e8480c0c0442408a00c012a1952920b41d1100040c80c0890042d02c08103039040c044201c801c0240603000b4102030031703610307903000a480110500086005442100401d601c0b0440089220f000c08030440310039000a24100c3c00040084120158541b41030045c03043d071416031200741d15480c4502c0000d0004a9100f207000000079440e0209103c14460741d01c0c0d00b2414414440c030300c1c0c000308406000100c0b03d4103c1080c800d20035080d4600104c202e0066100e0462540d8072081c00102d00a04030303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929767508 1250 929766258 929766263
    0x2121f211401050916030c0501140c0f1605040c05045f0d020d0318170709060f090213050406090e0c0a180e0109020a08100b0604240c 59
    0x7a65084010044150030041c00b8a4140080d22007940c10034030700d80c1c01d002e107511001d08000080341042049500030803400088110b00000c40d8900409613440c90301e841c0128820481c164007842002441503081c00d088800390a0850b4240108060080700030460300481c02103004548600d9410942e0721105860240c0100608007521911008600f080b51030f42015130201034a51103542d98a05406210500310000c0307a0000d04001541c140380d000e02c80d12014442c0110181320011020401e10b12001560100400540d103008070007090401d81c031801c00c6084c0c2d1020130142e003802800d10458940c580e41d5000c0d21400070f0010b0311048070384600c08d010030782c56001540240c84d14201060800303180d00098460850703081101e810f042e01d142448030b0241c541c4103100d01c903401403284a4840d00c040e0021418068650000328075000190002031048034a944405030660000171018002900c42c01a141d030800c0441e2110b0510386004c10680811400600c0e100320403000690302d9010a0140ca0311104064 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929768758 1250 929767508 929767523
    0x509011715031e0706020a0c0e150301020c0106172b1701090603020f03060610120b040e161208030c030702150a0b010212040506041e0312020102121f21 67
    0x2040c2030f0150300c1072158216112114014010302003480c500005641401d5503020450b4042c1d90314062507280340d84406044036000c0d000e200900e020720798003400035000a1285d03100019610703203018902401c0102c00404849282c10248541c3e01010450513400000c0d50b500c0085540c019000c5000c64240d07540003129041490901c0021942d105140d0004045d00d2082d0351110480c40d20008240d07031404e00701d030607551080900c10030120049c0f2a0034481041c2c0c801d04c07c003149811000e0006410341c4c1d50452808420341c0240907250b85442148100c1c0020201c030152a0b00108013034403048101d1100400aa0b41c881c070000120b600140308001d444a082d06203501402113041c00080e04004e407c00050003401440b441c010f8400902a40b4111400c54000500d0207140c18a400c102941a14500c0103603400e041d14800000f022510700d1210907500c0320240d0005a583d40b000040314800ea9000d418140710314200d40d82103046806002e011402da44100c40d00207070075021415200b04644904038000c00303d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929770008 1250 929768758 929768773
    0xc020f06030c0c07060f1209052d01060305012301030809010e0d1406090f1b0d0201090b0d0204082407080a1107030908010501060e011403100b040e06030607050901171503 75
    0x50346c06107600144040f655114031154420b48414030555192040203095600100004000321a81403521080540003040e402000e0400c44482421074645d540240c03426515202a4a5841d4484801365507424504101c01340550664554071002e02441c010b0728140300e0103465107d017503901c0388040070149034806d012100b5030813009112501c840301501d81954500c200503c0e00d482c01004140323a0018504442d50300307600d48400040240d244078400007641800396001020409203840401072610401e0020096601c502d0940c130140750800000d000c60b500d0318003240f0303e41c0b103c200c00700240d082030b500e2500d501580c40351440703400106400300782c00c010440001024030806800070384c0c51044a020100800c0030340c1e40c4600c150307454000030340c5aa001031038854000004c501c0c2d1202540d00044488000b40c0c069444800010240d44503411001d60080e1240030406a443c0400001f640705069141190403d510000080d007a0902103e0860001c4190310005500c0c0e0301c00103140e1103000d00101103070f008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929771258 1250 929770008 929770019
    0x9180403020d120b0d02150c15041104060b0d0e011b0e0906091303050a050d0203152d122410060804210e0d0b1005010c020f06030c0c07 60
    0x580390440074540220f902d480c55106100c0140c070411004a101800c6400009184d50800c0b400900e074054041100d0424000040c180508110380307113030030a50403034905040c105418501424045601d626118508164040c000c2460304401c1c0c0c0c041c81c0340c0d804040b65070108024a03d024001c0885483d080c081d03010349544503140c1c4501100d00101060704c1000e01901c985c1c00348081014101da07208822005070801c100064440c0c0010800041c0b03e00c0e0841c00d11441c107142809aa0040c3d40744e000131840714040400c0c5240404040d030302d240e58941c2c04850240c01584480c40c402c01e00800c180f086e6010034007070498003030611004405100c4800700416000c50803000c20141c0c40e09941c1551000707402e2030b01060490090801a000d0354112064400009182c0174a00401900008903410840c2d0600c1c0d0070060340340d090302030036054803401721000d1500d88128020041003155001604211080540700d0140e252907195100c1450155205a40e0fa91694580c00d468414400c21003414070401c00c00207403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929772508 1250 929771258 929771263
    0x100e1c0806010905030a020904240504030503180303070f030b0609060f040321021b220c020136020a240e0402030411010c03111b030606040908030406020918040302 72
    0x21031803090f01d400034000e49079014180d07605400103000b50025028000f02e00842c1c401c019030303082c5040000840c1c00c4a080108180156042964102c001c1100407042c000311594481c19000d890003010011400c1d031409590061205081300e40311014503030380344290034003503e54004845d241c1d503015003015070300c0103c481c80c1b2100745c3c407610050300c4ea060340c0e001c44401130004111254039041d0740d9008188081140456252121714600e407660701c101d003d660802c210000394183c140c002d0b104003002680650034480a400d4585020100c000f000100a60042c0382c2040085001c000c4264440c0e00d152510038400b00310381e0a00c0d41c00071000d01c0000144810428100c80200c840403c0030303a504d40195844600b480107a000940d00141462190020403900d54490080c00445030b000e461b0519111400410340350521049a00c840d49071400d9450344105400c080100340e070404800e0b5010000d681c0203483d00860713800042c10082ca40d41e00020410b51540c0c1d48040600c095030b0b080d03400400c07800d26140103903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929773758 1250 929772508 929772511
    0x2011206180b09070f050d02090d05030307020d02010b280e100609061b02040e010906020a0f0e030706020303040b070c02100809152205031207030b01080a050702100e1c08 75
    0x7401d0402e00d2080540c1403c5642d00e010780d250f85c0b40d40c1d010401070310301038078180c00900c0000c1d41c2a60900000c0002e545401c0b041c48164022405507039a424071035802800c01c40654000429607040c80f000001d645c880c00d2512149080482c040750400004104078846200300341d000e1b407111360940003800150714075800e641e401c440c0303191a1074402940c1d0304001d4500091381015403610807002c90742100541000d0304400075004d810000002c241c00300741d0b102d000300e0f00544840c400042d00034004c00b03009a04040b0070301013513204400800c0708615100d802941d0b440004d200518440740040401c500a00943c1c41551882e0300910100d03880288000c000c0036944200c0d0b2061030ba101d402001c030304171100188050b000e0390413180c0c01d0107840100d8024442d041201d4404840900c0100581d0f10941c1d0f07031241c8940101442e650124034092020b000601c003040203410520528908028080e90076000150f000341000240004106c1e1450281e40a081c07001d603203145030650018915280115078040c441c1c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929775008 1250 929773758 929773799
    0x180721060330050306010309050a0f03180602070e060f030a05061e0a05041a1f0902070b0f0c070b04031b1406150609060912070e0f0a0b0f0d02011206 66
    0x1842c038650300e6801e0b2406000c140340b03903802041c0100003240b0154400d802503408540208100d56410b047c030395848600303004d900d03003c1e00060001400c840c12042d158102000802052008003450f50501c9001002d20b407002d003501c0c0c41014074503883c41070740e203040c09001c40068000082d1800d614142c200301e0040c00d4038010311050407032400000b40d5611102c1c401c040c020394204240d030702080e5044400d41b101440103000f40112010f1408146403010418048001509100001580300c0f04607250034100c5800140070842c01c0e0006000300b222600d040e5041d00c1c6003136000b028181c140d4030b5a0606403030700c0d007a1040000701c843c1c00c7c11040e0144084c1c03d02c00c40740a01000221001507550141480f900c1401701812540701900f0040da495030724288001d48410000140b06000640070b0004403403030040c0d00d40c024400c0d903000c1010002103059001c00070f64428542042841180540c03400200e002101c501171922030140c840b00c904c00d5900c41c001120506000020412125847c3c0c0c84c118a84942001e05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929776258 1250 929775008 929775053
    0x8040b1e0301080d0905150a030f0b060c100f090b1b0d0207060c022118040b1f0212070f0303020d09020303160203060a09170d0b0a030c0608061807210603 68
    0x18650810301c1403a1001d940e1007d0719800c0002d18034046014019121040540a032030b200303040d03465036450f402004281d08840041c03144900300c0004000b500c41c01195606c42074907000e14800410400f00c081c0394003900391681ca07010503109031001c40c4140500648980d01c207101241641c200030711031344010b042120903000c684031075002c0c44105082e54141c0e5410110194280525404000401c0b0300d02c18115000748081002e21201c00450150080d400881c012200700b1418900900d405102111a0805032840145000c031a40c4410143c0e951150000301050350010f282c1c021140740342d014000701c0c2d038002c2c2520b03035032185840e964038070326010502a4464024400810380e17120442c4201130b01c2d103a002c07210322804082d00101c03400c83e410070000c5100041d1261403d0009907214a0860003451240384c104d540e880c100407005107014401010a80a1031401401c0c692070284e1074212a485841d610f800c000300300c080296880d4100f1000d18100849082c500c001c01000031100040c491719044416 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929777508 1250 929776258 929776277
    0x304090218030c060d0b040e190c0e0705250b1504060608091b03030408010603060f0507030903140915030112110d0c0e0705070b0f0603070b040308040b1e0301080d 72
    0x4054594080f4501664045000c000c50581150990859208644020000a40041c928000c141041c04a030b070100c950300d03803e100000401071a41600e00140c001241000341c00e150180c0c002d4040c4c03042c40709540c0450343d4070b403005094000540c05590000c0d070101d081026401c00008050388008102040c078821420980d01140480c482c0400d648108041802440c10030700111008050428105866030980400c0101207002c600034050300707004600c110000240044181407a0040340d8016007440105402c0072080c1d000f0950201942c05103021020095584494a0001580500d194a4008034150010000060364014040380086490150301c9003141c1039600e200b0051079030f20000300102075101c0a80140090111480401d9110b0001c0c10002c0c42c0c100c481c0c41d842076010044a6183c644800c040801046003028828480149004020340e0704003421607864038030a02a41c098000e082201090500051030040c00c40d1070301d00207455030203550396110382080b6280c550051104020902d000c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929778758 1250 929777508 929777557
    0x7170d0e0106080a0809060a02031908240904060b06040f0602010504060f02040803030c0c0307060501141f02151e100311090708070e030a0b2d070918090503040902 72
    0x100319a03c0c56101c4582446c01c9070190030016160081511142148414400042c7c18003280450040c1400281c68130b02081c42d01726090034411910701c103003d003440740c4580c10305a141c5820074003e410a07407042012a0848034040440c0e101c0c011760b071044c0c06c07081202100150b12038041d480300340600c0c01000e06101e04614100408264492131082441aa0082000501c1ea100403409031400c9021303801540e150103250f4403038500351902078001c0500c4038201000c0c0101c52a1008441c2d6440e1285001c0840180d5018006516604804031001182d880700c0c0000f000c4502000070f02e140a40190525450303401c00c1810f0454060700750100702c808a00c002c6501e03049152818000c1c2c801d8086540c1c1e51642ea684840c2203e5000088107002d4061051610000004020b00c01d418815403c074889400407403600400081603c0300b400b8103c880c1e00e502014050420b5000d0503c03c25a15900c16150050a1050602c001004d0a080203440c500011401164100340c035002400c0c0810712421104100c042d20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929780008 1250 929778758 929778763
    0x19080601270905150d0807030e0901140102060603010e030415021e0d0207060e06070f0f020907050309100204050a030209041401020406020705040605030313211a0f100e07030207170d0e010608 84
    0xc4d00100e0f801158000382e040000d541e071004100c2d0a11a2802052080405c4040f880381c0801f80c114404031141c0b101290309550b81000102d6121404030300a10028200445a039124401d0380641c09000c5c418040d515001402000b07120884011900d0594262090b11461910344000c800c140005000e00d04000410030b00c80c50058160b03100c0108185e00c2e2000da0740d00d0303594502d890041210481030a01c800805a40c0e81580c40f40716018588170300c0d550b403904008136800c1c9000c000c0101c0b86640306000500c00c2c0d88912065009a0340d0649080c40c030750300c49003000e600c0503c10700341c03820340da42c000607002c80c2040d40401d62404503502079500707201203500c607800c01d9200d00a80b651080c0c10580c01800f044282c0c0c0080c4a90348510355801003101c84103241d1594224001c04220882400b0b0481043c80740c80c19401413003a50021b0003010001402e800c000701514070b007102410800405070041160740c1404180040d0351008414141c2040e1344905101d404006007480381610013003546445000109407001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929781258 1250 929780008 929780041
    0x306091c080f160311070f030e18060d020409200a061d042403031709030a0512100906180f1e110f0319060b19080601270905 55
    0x3201c2546551601d00c0303150ba092510301c0030003c140e255854103030711600805c01051418051040007400401c5820b001d01049208404c00340604542a1043c407070043c80052141c22020881d011480c840443c000207000d40717030f80364000c4e224000ea50120058480340c0c1c03040001850065480041c155034401003526441040700444c500115016503c548500d0640e00121148042214041c40a440c1c0400c00c02070544c41c0d0000c60128401c0b10101c002511003140c2e4540c0b111940380150715113945040014000d004101081c0010302851001c15000c0d01990803041c003900521500b001590f50b0740301004403800f03000f4854000146001d074040300b050007501400440b240d40d41c403204103100080030050024140d00d400f10b40380710002c0c495100040200720045004a40a2041c4980d045005001e070007107030034940c42110b40316400c0103d502c0909000301d9400b00600203042008142e030f101030058800744032500004642c403002482e00e6090400610b0403030103036030b503030941000ba964803008040240881c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929782508 1250 929781258 929781271
    0x4061503052202120a12020328140f19031d071a0c010f0e0106030510090c030b0901090510020a0e0a0e04120219210f08060603150306091c08 62
    0xb030141e88400350070500c40c2000402c0890f02200c010b003803991a0710401201c14552200107800c001612034800c0100400b0300082e2180028005080764810320140403444544440002ea82011604818070805401554094200c1d5a011300904100c0c5070024010842030b20495030401029041059a4400180040c151031100d440e02000c41e202c9204004150809402c000302592500005030040c01e0354001d9414502900c80041540c0f4154607081e4240091444c2c0000c00c1450980500080f076419001c22040703035000a4594560f45490758400c2c054249010b010348103100f8000c0c528108280c03075000f070001500580d1400c08030b00c0750b1004c01640920034402c0081c4a0100000304000c26000010b82c58541c0c0c4600481e00c0c0c1c0b4149103040c460603600f0300016607407540080481c988502085e07400032074103990b03031a00c10120524540041c0140794040c107007a00504001c000a010566154617104903808010101c900034907020880d42d688014a6840100d14082c2442e41070120380540b000901801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929783758 1250 929782508 929782561
    0x31309060e15102109050604020f0904260910020d08061002070311060c060702070302090708250e040204030b01090f181b24080c030105030a020103050a09020406150305 74
    0x764210407200c000d45030704c000304040300240f611244602c4c648034801141c2d02c620090405032515004100c04042d480440a00841900c800c220018104024903211080c040b000d0f00108880c00e40d600c0b0315406801d03c0e80d9001402c100101e2021500000c10078001d2070b890b950140c4c6580c1d1744046c420303d40440c454030000760f4414001800003804145075200e5082003d05642e04002c01025582d2900b9010794984001d078102010a1043d41400304240c0c0c1e0007400e5081000403410500c81032004c03003c8041d075800035848660f4001c85078910071403003840d4199000700b05640751341d200e08001400c040284680600c440c1707080a1043c030b240e01c1d0b004a5585000c40040c5e4444403042c0c0c2c50703045907400030b12117010061809000105044410360f0b80300701040005215803040c4403260f20064244071001c8c0148074407a030113000422940d50002039222181d5420f00e4081031648800c00b80c42c01400100100951107420b00c40085103020341c10600318180d2400d07990500154607803040f24443c1e980e00001d140701d500e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929785008 1250 929783758 929783779
    0xc03030a05010b133b01170102071106090a15050a09050a0501050f1b0319121506050f090607080a080c12041112120901031d030a030e031309060e15 65
    0x1c200707003000b4076014451801010134031304500c40d00d20000141045c6203500310340b508014040044031082140210720750200840c5405032980b66591218412000305100d039100140ea0142900c80c42c04a00003014251903551140c0c05960001e002030700140b5400c4001100140006a90701e4100102c504a0744107844040c900110001c540000c0d5201c042d5903804076601804184041f40c00308010003031030030320884003000b44032070740c5000380115240256440c40d83c0c1044038240424001552050454001c2d041407940c0b14144102c816541c0100c094040e401030300800d154041c084e03540c00030060fa040d59a281c03000382d41c55018821171070044407108101003440000050000e010a084104616801030028070010404511203240c1205580d0402d401e00000c200b803841542c043c000c6c2c0030306000300c48241043c0ca0054500c1c65480c010110300300100343c0c8a00594100710303401d0040341d5030001449001d5240588400d0143c02030510340c0b00b568180380d5450005450b5038109083c03c13030820790043c42c401aa = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929786258 1250 929785008 929785019
    0x712021005180c0a2108070c030602030a0e030a2c0a0f0504050f1003120507061d060c18060306280f0501050c0a030809011d0f19120f050f0c03030a05010b13 69
    0x1005081c0b006c8542417020841c010204070103071200c40040d03202e5500980c0e280752862404065400b04814444a644148035170803510b0703017240c3c28940400d008a505001c024420744498002c9040e42d664a030001090080460f188040954031810b44074207980034040758452080b40c05030030700f040f242400b000030070510600008c0d241c030b110b40c900300074103240950401e10b0f01c0d203400d0101c8062010070f540c0c103481d20218030b030124818051603a01c84084103e03182880d030345580702441e40c5c400740011072003500c2c0000000e98683e2520035812150507842c0003511100310590641803120740901642e01240010301700028150700c1101200c900c03c45001c00707401500103684d0180c545043c05030030f0340b0280d526121581845011516105c0c20220320303500030f118000c000074180e4102030328a92040d5061004c1d07010b4502152105039032540f034110074135001221070402501201e89000320440002d80b2440000c000e8091500000554010041000304003c0e03070340d8502c807040315480342882c0204034282c4c14104011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929787508 1250 929786258 929786309
    0x15050f22020303040902030f1605041d0a1b021b030c100804110303030a0902040e0c15070804052706011701060e0111070b0703230712021005180c0a 65
    0x1507403000d41100c1c00c281d101c00c440b03000d0741c00440b680c4084020950401c0b6441581a85e40c03058030002e400d055181c50300b4071606107076001320001c3d40048501400c010428001d015807260651124811107501401c2a038140251030300070b91124400b800089071500200c0740390101d540035102c01d009004900b0788c0110318090f2410480108141d0301c1c0d00148842008644090001790b00c54183d03080006130061052040004594a10a0100301507200c22602155601c60b030825008100303101507001c0d1205900d02d420380c901e1207190003480e048000d001c100b21802c7c0c416100c00b91503c803c540111500d40d00c000044030603241c24013075842100b6500b40104100d5000c0c200001e02c0c5403043c50310460406607050321614040050b4004158044001512000e150780501002c0303090308aa95105011040d00032404158068010082c1403030b80c1c0c00100c450010300030044100000c0140d4010701c43d503c0c0022118005181882c1c642e07400f030185540c1d9040c40d141400b40d0005840c18081c0c2c1a95900b0b107001c8410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929788758 1250 929787508 929787571
    0x9180a0201081e0c0910050301080709020c030f040b1308060601020a1103011d030705010501051012020906070b0a0b031903020303010905150901170c150a1d0d15050f 73
    0x203004642030003001e900003107040020320503400c00300c130140e40f40b0411050107000e48050342141c00300801807005000d400c4001c20a0f40464407241c40251b15040000d4006056204000303411500401c0001c001070303468a108081c01003410768464020503e82e41d01d140b0742d280e1904994090050700300800c1880001c0e00030004c02d020031070240001901609410030b814414070203402c0b4050701d500208410080020900495002d03001c15181401c2e80340c000b4001030000c45c0c0340c0d400c902c440d9801040c00c20b155200d44007902c0ca025040014408981420b01d0301d40000c1919101da80e010b8020306a001c00a141404102c0400b65496170003146903a01c1c103440d010041c5009070010560712013503040d800d46c03942c40c81c4549028000d5204c0344800c42c41220350803441d04212550840c026188480c1840c00500c0b2107056420090072401c1400c50500c01c400380b00c001e407841140c4650700c10001c06040060112a04082585c04020403081240c1e0b215101e5071508040d003110311003800020a58450136540d80b001080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929790008 1250 929788758 929788771
    0x70e0c1e130909060c0908070303050f0d0c0c0516060e0402090f0d050303011e0f0905090c13090b0c130b07050312070f0806040c091412071409180a020108 68
    0x16400d041d1071540d1015012010b5120304900c03902c40c8144000e102c002c0c4281da02210301800d000e0b490603c0e0103a15030701c1e00c40f988009401d100d80800d155501c4501c1d2400c441d00f281d4a500c04000e080c4800340064200303001484151090b214448003030b0044110615034030161990b503216100c51501c56420040170b90302c982261500701451002c00e404e243c540302e18900089106502940d00c9604141c0340700d401d400c04602100702481d0041e801c110041d0103040010030b84105034000f00780c80c0c0e10040700500c0c15080700315058105512003100d5080ca021688016001c0f8030640144c4003944070100340480074020f012004820701c022001c100928103061004000700380c458801d423820051215060000894202c4481c03011901d02a41144501d602c514060b50281088808004c80040d10000420232002c0740039130100201180c1c0c400542d82c0e2550f4065a00d200c008007110074564940180c00390a088086941c4d010f9070700200441c0a880000699410710f00312440104901000ba4004403500300010300790 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929791258 1250 929790008 929790067
    0x70f08091216020a030c0e070c020603040f050a0203121c09050d180e041101030e03131520030409050106091a0a0c0b0f010812071e0215031008070e0c 66
    0x320b0050302e0b0000d155005502a1514106840c5000356410101030000d00350810060780c0d130342050059544c070742541e40241d0400c107071240240003490142d281400c00e03030000c0e41c0744c8502122002c0002800c1c0050142401800c402c40200c040d402d407840c180c0e110079100425a400845040410b0741c410812134144441070488400f0596543c91743d00f49004007954240d4440030520f05400701c0b560140590600c50368040d0017103142c182a41c00264091100740a0507040c448070701800072140d803052003011000d0a40c1c40003454545410003401f0395943c4244500c001c424142400000c8560103418410101e80f000100d40106045454040d20305502c400f8109041c0003400c9007880c003084203d1506445079902d002954000d50618010910700201c055074400c02403000c000f180009812076034030b506004c903251490400c0c50064800595146000c0000510504020082041194664510a040f60003c0d000d070f0f01401e440e41c4203400f09410840c1c3c00c1100b8102003003550b01461201d4691040410304910 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929792508 1250 929791258 929791297
    0xc0a0212040801020702010e1815040e011401090b100804060506060706020f0307090b130b030a0e01141009111602010c02041b110309010f0c08040815070f080912 71
    0x251406401580012000303070350101d001340c110f58004108c00c43c4644226180c81c01040720f03040891045100074031100091030a080c0c2c0540903116500a010305925100090101c103020001c0380103001424411000c07907500f05055145141405140b00d50418001d944c0d018003641c9036240e8502502002d084190003050170808400031844c40d201030f050300205089030564070b08118100500ca082035801c135032502003082028106085083da15841161a03509440d074582d92101c41100003440520043d441070b5081a25008070050344a082c64421aa81ca110b80c40a68840328900104c0b00000304084d95140d0802c9100e400c05400b09580d500148145003e001102459000c141582c1081401c08000b81c0e0f2000581e8445400004059001d42c000d4021800d103640c10340020f00194102c1c4101c020301011481d0101407000600c21100902601000c55226020041c0500c2c8150002c072a00f100080045030104030b800d204680741070180b00c0f06002412800d1010728800700c1544964040d0428a08206 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929793758 1250 929792508 929792533
    0x3305070b1819120807020304060c050705090a090c060e0901050d0f1a0709141305060109031707030f05161119090f0b2205040809180405011508060c0a02 67
    0x1452560390b00784500b094145402c1d20b0200b0074022450b055809200b6002c0c00c1007051603000054a04881d0380c0c0c544600c54070002d081240c1030421a82203030350008100d008000c6004116041840a0b81c465100010159a9082d0440d0014020108103600c5001c04004104901d000248440303860302407200810201c5c0c6940c1d4540c04040b401e110718500f01424410040180d40041100c0000d01d55800300403441d41000340010702d00c85001c0340c02e01e50076548201050540e4415031107000650340c0410f101d00d618800c110000000d403c50325041b00000c91b01080d98106078481d805580f2006421800e1014403034541e40c40c2520700d0b88004410350415200f10070b12241c02040c446280050100080c0090310300318a5000e0790540e4402910309006448402001c20310300900c0b40d03c0a0501904000040c00323807100d2a02c0c0919100340722201d640094543c50152011401d03020b002d0050b0303c00c070b0007040550344070940039407007400c6032040c00d001e604107070001403c1040c1100105403080c1944151840d81c00c081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929795008 1250 929793758 929793763
    0x120c030b04020c0c150a0c1b0302120c0a0909050a03030c05090406242d030207080c0d03050a1a060306191d0705040f060e04090c3305070b18 62
    0x1141c00c00c0c6964454201103807541020005c0d0403059800da00e5403881e0071003110014101d032040d81ca0042c20380b4022041c1e00701080d00e01c2e80c804059a4018a41031000920402c07160340e6149285500d44100131341c035000526040d09106014019070300502912000003d62800d400070840000c001060003000c1203400107030391b11889024040d080c40442010724000d4190011082c0010380261000e10228003411b8200400005403507111080c0301c0d204481d103040d036800071006400340141c0281710482c0850460030041c4040360403013401806580820845c0d0760316004c0b000340c558200300c0c010f0008191480000d05c0c1080703c0117603844040509005096081c100e1684100c003c66445543c0c0281c13080c4d2880040303803801881e030350002030b1440c1c1a0700b41342c2003195602d0386940e140308545c140700701031200260707986480d0442080e00b900110312641c0740f42d403034036011031650f182005400850070050060074a100711300100304041c0540d50354141003c0c81680c138002d8101e000380c14a41c110451441110500004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929796258 1250 929795008 929795017
    0x50d1a0a06061112040515040f0b09010f02010c0e13020c070f0e0a0b01020d05070516181410050f030f010204090902010f0206040201140f04050d05011d0607120c030b0402 75
    0x20980055102c0c64408010311000c600e00300302c000c40d080000d95100008111044e60190b0f181251040700c010f044035036140c82885290b0140c03071801c0c00004000380700070301c03000a005100c0c002e032034180f100b01e1245400c034225542d900410010941da4440341615003010b82c807519028003d0b200046c40d0640c1614203c1c0b91103165441003469003034900084c0a00540708641e140c0101c52901e0070b011b201c24000000c0d40b81e0380703c00c81050801070702140003010f10408000e412112410345000654480c2c95150710200901c51510b01034001e410422440c0d014030080610701c1c0b26210f045807007409141030804000c50341300d42400c00d943c5481520b6404011082c20700c020001883c64220010f0b900d0880d100161504030200304610a5400c803404010250342c0000000764450314035040503540e8041015911240e000c3c40d0041ca8003d40c412001004108055001180741030041400e4403550300002d00041d40c0f5082100c0d00f00c0003c0c0e40c40c1e0310000000b070540107250700307081070704000c540c8508010200382207800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929797508 1250 929796258 929796271
    0x1003080d1d07030501110f040b090f0907030e0606190506071a0702060a050c0a0206040204050601111e011b0912020105071e14070b121e01060801140607020a050d1a 72
    0xb0a0708004005091061220b031645001000d030401c1c0191034110b4060180c0e1140184084002038110250364480300200c80b5580c00811903c0d4030709200c440180140b00841000c455480f030440881d0003403400f600044080600700070382c42c80050801c070a1101a82240da000c0b600020311410707900c580c4101e208000c0c032034204e50b802080b2a24140c468203040d204050051203d03040304000142d0321560102c0c90a91094050381c0102d69a260b44004071008034025a070780010b80558201180440c8031800740074640d6020400900c14003050404010740146110010790204924a004100000780c0205115080340141007050400c001502c81000d0f0b04042c60a083c60b1244130400d41042100d2081030303014000052000340602424075000b04000c0c8904105a03106614006c009046090070f00340b55103000c0109103030b28042c0d5a4420018040344828040c000610340100c849001c5030501c0d506031058160010446012140303824144842c000300000199a800f050740c13013103540c890440805038003920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929798758 1250 929797508 929797513
    0x6120712140d020f10090b0a091b0f0e0f0106020618070915062712020a0b0c01050f370e1606020c0301060b071b030f051c081003080d1d 60
    0x40d01301d00628180b642204410700c1c440e107822001c201040100c103045a00c9200300300001002c03603e07410030038101c00b500034a00e030b41207180e9003010400702140140a803c44656280c0b10119840711000400907290901602c001a44003d0004644e814545440d5143c0c0c500c110a886001b6111040c2e407007510110f00c00d481c0210b0ba00351040040c3d0754000302c4043c00c40d600d041c01100001482400781e8941c8980c0c07103070803600c0b040f14603024190740e03900c038032100145900075009550340c171000301705406480c08450400c0e05841000015024140c8814070464034140880080142d01102b290503483c4402c0309240c04c0703031940d034006e60302c0014801c10101c2070f4940050f00064500c2c0c42c2250081c584481d032201c8500907410018200203026108040e503c1d4190b010b805200400000351304007a80180a41c4040e2a1080059800040c0f01002c29041d0865601e008514001442201c041e20400d0098031014031020504a003000450507175000740c40306103001c2c0b1010803c40c400b0ba040c40344885080c010f0407042e8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929800008 1250 929798758 929798773
    0x1c1a0606131517160e060f0c070504060f061202030a020d18120201180f02030c0d030504031b05090402120c220c080112110d080f1206120712140d02 65
    0x580c00080070003242d080d42e0254034441c500080034040c20b228040c07518052204403080219207685503004d031074280055007800c64032202d230000d100d5030f100584e1051074003030307841c4c00c038086007100d021390501c000c1d40c01d15119080722000d0340e2107040003940000c1c0904510795083c06224605003060051609070740c19008074807074650031401e18880150b01c0d04c585405583c54900c80746130f940083c2084481154000143c407406207180c1c00400d0604e440142150351012903448800304064108025005a90192250700c03131482e092030072a00207001900a15a2150441001030010314000082d541114140400d88600198040c00f01d020b440c80204180e10b084c0e108198142d08030100d20926601410502d00001e280d450b009292074a1603115102600a54411000c3c801549a4189004403039901440c16680c556268109a80d01c2c2c004000c2e13190305245401c003240d024034000d03202c9400f04980802910400c2c0c0341441440d0b1a15040800300c0314a00f1240d207003044c0740c20502c20340101c10402d4020302100e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929801258 1250 929800008 929800049
    0x21040c0b1815031b07020d05070f1505120a0b04060305011d060a060311010c0c05060a03060e060306010513020c0a0b0408030907080a08031b0d0f06051c1a060613 71
    0x20384510b801d42c6989400a00030000741c022550407443c034900d40e130916507540d001d880c004501d00881c2c2c844080d019100f0050005440300088400e9000c0302c0944020104407154004201d900e403085140d800741050102d00800c51888066100e80d01002005000181595481c2d50307403400e5940c5210000301d1114100202c600b001c105002e604e610402120041181508558a2640446071246d4690410030300100003c10410001c9401c0c0c050040188219155005000014085d02c403e015609042d841c03080429464100017504a0585030024a00ca610080c800c1c3d43c04001c2d0008140401b05100740450500440c05182d07030030307014601491005960b0701d0aa02c4a524082e01c90340003000e20760056140c1404a0554420382e038002181061040e4191415020f2810740e0103084000005c1c079140101c0303541d40c080c15034820001ca42c402c3da441d800c3c1d01108010704545010200026081040200b024890114621181d0340d010800810290034201580e00300e980500d101d802400c3d203244041012140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929802508 1250 929801258 929801269
    0x9010905280b010e101205060a02070f0c1203030e0d020705060a0314040b0a110c0a020108060a17060a0c0207180c0c17030709050d03020d180915050f010521040c0b18 73
    0x28100c0300b000074020800a0b1f40d080c1d51034500410880083e607001c1084000c00134003000e4000f11a030443c00d540d052548a141042ca24038080d901140401d252001e00203001d240427480281195250300034100040c40d1400740401503000001c05000c043d591515400c20315418840b0f0b9018500032040c103940b6283c004442d0045171a00d0201d4049920180104080440005041c0c5141903080c640b001e041d0701d540d4003084911940340c010038141400c640c0740880007400000c18921450307024900340b045201005003640c4401260013007580946202e1200321101000760400800594585001c841002103a100c1c5c903a070f00c184c3c80c12421010300000034410086d80c403014980c0544070031100402c3c16840d55030040c0d41c03407075101c0d840818040301c480511101540808a1001801a40005d004400224404042140e11409050710450744500e2080040d4420000c0d9141c02c0b0210964035a100c098540c07007090800000c1084915042250340410100360141c042c09510102d9034000d29041082000c108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929803758 1250 929802508 929802541
    0x20f090f01020f0601091a12010b090609100b0f0f03040c030507081f050a0e0615010917070e0a0e01020f0712140a030f0e032109010905280b010e 64
    0x41c1150320a002400514034003199080c111013219900050440301c28a9151860820007000d942c0000307148545a8510019001404640422944e80a00380d88030410004c0c0180184c641454440c25003c1c1031140c001140020413002c90f480e5000f9040015881005046a0003120100c0c0c50414004080007000420401840508002000751900315007101d91003004601c0098030004140c0c9840c0841d08000f55584901c0d03021190505a40b041e1138424150f0070103a140b44501307800500140d400084080f410008102800042e0707001d480c6030307498121030241d11800500304c21411a901c032900c001e401802d00c000c1c1000c91490304aa80c4803070b8181000840130808261000902026100c000080c9030510201d4500660500b00081c9072080c40d5150f9004100901c90b07224039102c0014520101402941d101080c68032600100c1c001d5503031000c000342a80c000701001000b507800301605419501d00b0201c01030351079090319110070f80401d246d142d40380d2500d000e0384684400444071090000c0783d54852031b1311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929805008 1250 929803758 929803789
    0xa080d0e130903091d0c0304060f090c1707332a1202010e07030611270a05030d02100b060d05100501021c09030803060111060103050105251b060f020f09 67
    0x88814541b101003041a440001c10013481c1d00d54600e0a00c2002030954443e208481c4c000d4000c03010303161030301c1401c01550842d1000150900c11120002441c101c0d5940b2515036a489200b507600b003501c14100240445c6c0107107000c43c01d12524066a4071405a00314800c002d110643c40381c0f08a1030805d0502e07081c10750413400041c0442e4180b10244810311000540441101e40c07121002914403411048040035008820103000005201d080b20159a40d2164040f49010070488101442940d250205991b80303560b00ca02d903002d6000b40d0b00050060310281d0181303050181c0030340400d1400c2d81c4505004100d600131130341c12101401292060025503410000e0b00813032481c01d01c0c400166103000d54090089981c0c0d1000400818000001800c540d108814031420710a118084a007556164503046000e440c04403001000182d1250b03c41400030041c6090b51010b038075585030480c20b402d0300120017490300754003202903030745a844038880d0750110028402013540162031902c0d61380b00c411078803c01401e414901c081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929806258 1250 929805008 929805059
    0x30307080708071e1202070303020c0c0604050a14310e0c01050d0f0b0d0b0405120909070f210603110303040608130c0302030d090905060a080d0e13090309 68
    0x100030103140c20041d00c1200081441000030603078600042241c40c45e41071586034000302e00206525013015099006000254003120503204840d0045081c8406401103104291348451450300400034229207004a80f440b49000e03140070b40301040680040020005d0041d580c8108540b840c20032020b602d40c2c4116140308503800060b04d030b011110000213040f8003e01c2c2102c0a0599201004a01100a42c1c0801d582e81d030064100c90302d104150a100c04005d5040710305841c90300a080d196986880b911046842ea024014000e07515511801011200c42d03081d110752100b40308085404510020f00c001c0b000f88070701c1280e28041101c0d419464444504014501c0c410300a9205100074410303603802442d202c0e40100c0b121044c3c15240c110b030400e41c0a407c110780c4003035090b001c6d00c803504860030350101c9650217484c074480044c00075444038404d2101d58074a034400c1d01c1c3c6c9500144100d8400d00d20940200d050100e000704001d981e074400c90403940885008801c22400b0031403903042013080502c7c0030503100c44c00b00d0b60442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929807508 1250 929806258 929806261
    0x20c060414011514062506062603161e080a0f0e09070305091005071e11070b131a041d09071406070506090a050c040b010c0816080c030307080708 64
    0x202a00e4001c1c25043c080e01c182000f05146c0340003d0700d4040112402e18101c031502d686261414900001c04403402800304410560281311000311a07880199090290140294608558100d250001094030a000c407450044800455000045e12007120000ca003d2010a503a0742e204e8440078141703101e100d0040c1c00b40034102c415400380350388602c0490b5028429050100300c6a9600c00102d041140c4410070690b124940f00078010b2450744520310000741600300102c04521194194262a0802c44880c041a51351101409020040707901c40034000c1d00410741c4441c2410740e256020004100e02000101c2c1c4405d50203e01000190300351401c2061045840062841c1800e00b11001b6481d04e070140903201e034142180c441e10701d81d511400c1c11203500c160002d042d140c03d81801c5011588914803c2c005948510540391980d24170f143c00d10500c4807419050f142c2c140200c1250341c403003210f6006002c01c5000e0328101d55084011610303080c010503440e4084000307140d03603290605025000b010050b00010402c510b140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929808758 1250 929807508 929807519
    0xa111c0f0c02010c060b030307020d0606060306050f0d110111030d020d0f0b03030316180e090607020f0c0103050c071704061805010e0d020301060f1d1f18020c0604140115 75
    0x44c921245681c1041e8040f601660040c0802d10350300c00d8080080d0010003586080c000e00030b40382c1c001420340b14169030522500341c0e118100518240e1101185a1200c0244413035000211004008102c2003018100303000d481051036401c1382190484206e0740051600018060400b224074420f0402240c1c0c2050304002c0f9201d0080800d0740c0b80001840c60714031402c142c5811410902400060081e010712361b06140340e098440500144060b001d41e0038020034489c1d5804030303403040d001003410140311400d00300410310102d401d0011409800c0141180900c40da0030003209000ca684601c0e41c0200500b05507415550b589003101c0103004642e042000546805c500c00180103a030ba10100001400004640c040007500c414000a801040164060545258100c0001611200840d01140c4d2040044808111585c611020f214041d1004c2d5801940801160301842140382d250701c041c00d8011440001800c00146d061094079200098400380c4a01e0780008030072000160034001d018000801002c04c8241c285444e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929810008 1250 929808758 929808767
    0xe2808070f1d0c040b030a0b040e1c0e010908060103051608070303080105090402190608010501021e0d0807121104090b01030b1305090f01110910020a08030c0a111c0f0c0201 76
    0xd480800112003600b020800e60004041030360041d082c0038007011b542e800c080c50007100401c000d180c52401107003031030740802080b40003154070480450407040002d40450b08200032100c5087c84060581440304030900420908000c22469000e144280000c10356200104038646d42010154002440ca51045200f0300002c0d5100151078110781c01034035101c0040c3c40302c0c800504c002e0b5910040e108056100c420000316603501c014824102d81d0280c0a480b120002ea11900b54007421011081d00c0c0c580c0aa40e00c894002e218010155004195151400c000342c510f21050701030b2130041c100d1410b25100443c06102482803407007800a005001d003400c1140d072050a001c50714140c1d0984403520350603640c030000303103d0000500c003201c4444000d5008010314940d901400c0c6c004d0b003144026a02aaa0400c515842076000242c01503034a44c00814442c2907a0b100c881302d0410341e02250f002000c00002d10844480c3e00030070410801c002d1945060022103110404008080b2072407400100308210085d0180c2c00540d820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929811258 1250 929810008 929810039
    0xe06091b09150a0e0f0d08070f020303130e070906030507120504080c100f050f041a0604140106080402120705131119050c0705030d0f0e2808070f 64
    0x10000466154403004000810302c40480150040c0c528000908000590748201c02e078003109421140b107010301800364103210207a89610b0700144080c03810004a00801c0c1600c500002d40c0c1d00c002d0450b86012045603400c00d0341916035102c0100b5245410a01070700c10340082091002c0c151030300d802c0100e840d0068000304415070803440040015520340200d400d00140c2c00c00c940c10103500d14115072200c080f20001c0001013034a00804c0603007624040120391004078040144e070042c2c2e0000c00d0070b101c608803682c40c1130b40c6041c00f0303120a0380075a9138500e14003030340c4181034100d00900f042e0700c0d038000070302e02401844025401e50841401e241c00203002401140d89001e8000c2c8240c04200e00080c815016034550f660a10580141140d072801002d03a141400f80d001c4020440c4c01040c0082d41c0320683d6078000c0c16503500d00000c03140c02003203402c041c140d4824403030040c406600600401080c011070f0051100d0f040700c11a0580002d081c01c0c00c400a0000800810507000105034541807121035a00e49015100040311 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929812508 1250 929811258 929811301
    0x6180c051f0e0109080706020304080c1206041b081204050f01020105042402070618021003181713081018080f0a0504090606030b090109051003020927070e0609 70
    0x2910451994243d1280b0000c0002c1c018885c103d0304a1070b00d920000c2c1d5031340c105104480c3d01e4411403441154608004140c2c1201324030403170007070101d07480c3d950300d500e0348032000c0c454011441c8212a00092001c2d0030403954160745814010310b680c0b01e05020500a20603c01c60707600e415a81400c0c18840080d1035440000080300c10320319405151602e020203100030744542200600542c0c2000c4901010b0b0062030040e50801d03100325441006d41001c5201941580c0706030314280e000110300088140800d071041d0a1004040d240c0072143d140460841d030140558115402ca01000c0e0700803444141400c0082c41b4030b81840c4e401d4141c68001090b19a6942c40c40d12540c50b071588034030b4012908a80860252007510701400c0d003481c1c280700031a124200100180068903401e8800d0023040700008400800713124842c09991010001030300c480c251780900440310000341000d01140d02030181d40f00c0c459500321703101c010180703040050021517242c150024007049000e04003074861080401844800c1088a80d440007000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929813758 1250 929812508 929812517
    0xb060f0d020306061309020603010306050f0f150405190c08180c06040302060903070518040308160e04110f3007021c09050a080618010203010513051306180c051f 71
    0x45e030040d8403c0540018840250445c0e404030003c42040b035250803940c4034001241c8a642681c2d281c448107040b0000c00e0740d201c081d20a46408040040c1007582015070322207092406040c0000d41d01c000b0908450498034241c00041c080014401407141e403040700307000441c2c0080223150040700b40380060a144140c2c8402031186400140c9000292814400ea5000300702c0280242154107001400c9031007050111401c800003030300035000031000200c602404014041650341d54030f003112003400344002002e100c1e00b81307911940f0600c40300340c4c0140a280200b000010b00b140000c81240c0d81882c605940c2001c4c000c52a880d0a038008200800f94000368440b1459403100c101018000454020f45005686420241d007020b480540455101400942e11b03000d0f215490043d40250a240d00c0f081c00c0380402e001d0254008507000c2040e07000c00e11390b00116000603041e9a03036950b820301d90f0b481c0380c122030744011084000e200b20407012042c0105411000c0052205aa00680c01c062071078040e011421068031304800d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929815008 1250 929813758 929813779
    0x901030f0b0402071208060d0c05013209030c0d0812040813120308060406080607050a0e090702010e0f01151205031c050115020a050a0311190b060f0d02030606 70
    0xc00c5a4010002a1101038001c568640d502d04141502040d006440000300704000045070702d0741042c805408482d0703080850f8825581c2044011a0b16400c4817610000d0503502c00500110203544010000ba1840540c0000b0b50ba28028400e040c100f640d0780b40d04d10311800a592640b13001c034100904072107000c40c10034003d1000fa5035910303011009004642c44070084403642d01020580d02c0203402c1c580d00c403d000e5103450040d40d40707010800c01500d000d806400c0598200102281c9124051409000a90a5401e14505605141000c42c2603804100c0d407860040c1c1d15004e901032081d03010301240c6003503d035100c0244580301162400380e0941c00c061003449100a803006050082c40030034010b880402c0c40440360100c0c250741944040d402f40074280607101e0721003000c03d081d400030380c000944a06d00d294000050b01503200542c40a40d50503c1d075245503071a500850880e03075004481b585101a0b483d01c0380007000e40b1030400d0000e003ca02c00014410500591100d8040c00150b500001c010342e02c65412140c0400c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929816258 1250 929815008 929815031
    0xd0e07140a2115020c100e030310051309051606111b0d030c06020d05040c0f05030c060a0c140a0303140105061603180320030319270303031509020a05090103 69
    0x507040391665440b10078408115414450170102d00d21010509500f402c0c0490072580c21100e0b00d81c40f0a403481c400740c0380c020301c041006080c1100c1c03010103202d40600001c0c50009540301c160801c50301140e0b1514a41c0011818485560061090b02407004041d00811034504500251044e403284d1240b081e124401c07401041c1d08061191021280850340283c081d5114105048018090101560101c50403034454201081c1c05800e180c004044036002002452843c00c500d0038406207501000521081013023608070600400e41c86d55100c0054495040140741ca0002414001c3c1161242102c82a0042c6501700402c440d038ac3d024140c031108031004418404141c0742c0e281c16142c15401c010012414040c1d4130002043c00f0002c0082e11030a20100038411008d81d000081503160700c20f06903100c2d285840c160090702d8051080318007041d1002c140f0403848a600480080042151156000b01c5c0041c0d102d03103030360080c281c0700d09015004010b01141075040040c0c14501500500500c80442d040665422081c0e95 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929817508 1250 929816258 929816273
    0x19051303111f051911190507210c0504050c0a11010e0d090609090603021c031407060b0f0f013f020403030906080f0703110d0e07140a21 60
    0x607004a05052514194100c074040c1c07098000c40b0301d11015415001d60804200d0080005c482440010400340c111080300c0d8005401e4456102d00568840c4280c000105000030b084200618014105405070301d8001d451800001401080e004140614184420b020380140c0d003800361480406542011005005040341080c0107240c9011041080d20a50303940050b604e80003102c07402924849c0d40c0700d81c1200d8841c807000041e00c20510000703401c825140340c01c0414400c2800044030003440b1b498a81080d1049100e15050f0fa00450000d488055403a14202c2052514880803601c880044d2101005101c1c0c440019005650404640f2040c0f800d400700502c0c80d00b60b0b400364451800624031600040320b25441d48400940150008401040c900417000c100786001c0c1108074403074044603034213280302e42d00d404084000d4021800c840c190200700380702c0d0741c0951005004a84d10031205e5402080c00600d000001d02e041d03802100e40c00e0051248002c00d00480b41018180095141d101c41441d400c40c5841c541200e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929818758 1250 929817508 929817529
    0x281a040b0f120f100e130303240605040509070807080a05153303100302010c030e060c0f06130c0311031c0905010e041103061909111905130311 63
    0xd03102d00640e07082103120042c0b2036605000340740c0c450200d42e40710340317510300003032804c1d01a510104800031040094002a02c070750000f60290002d5129414900300207980c3d010a89a0364001401160002ca4148a1400d0800d03c4640c0802ca40c9840e080d0b500303008002520b20315010342020030403600c500000d00c008000d04604081464040d2045041c1852002c4044180701d9000144121800b9034403120b0070a05c151003a6402244140c4001108a24540c01500d84070b44444044041c008040c07201140c95880d440640b00100b90000600080c206004443d82000b00081048099510700d2a0070004a02062904400d8139401241c104000d455040061300d80650705034029580c0307121038400414698021141002c0325000e88881003808050b208100685035260403224030441d081c000242c0700d250810503c80c1406031b42c42100035054840c170000d4151100607140c404c46003400121555183c100b036007101070b1450b083c070344607051190f04000103100e45540c0c88083c08120701c200d14001c03d83d89018801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929820008 1250 929818758 929818777
    0x50c180a1a0303071b060908030d0e2b030606050a1b050c09090f070608070f0f111002091c0f031d0613030201020d0305010e0112080702281a040b0f 65
    0x41391116800e14010042c1c10020289820801d0700000015009024140103403c2d504044080c5080251101544c4018569076110f894240b0a029008c4688214241c040c00300c01ba40707540c420066840c040c40a001d80700168040e804006081050360b00c01c651003030003000c0c882d001c400d01410b1a025400d00394603040f0b01346c40160b0310641070800d01030300443c0050300d00b1004803044251243c036603031000d00391410a01115402e000c01d038106191071045100381001c0c41400d583d070400820082208034524502520f40410010f038a500040e000b019103820030041e851040c4d07406160010021b80d540c1c2b600003400d0030000400f8441102106407034009000c1403280e80c0c5c000075080c1a201d25800a1000100d642c602c401e9000d805660001c03004188603010b260b050780c407043d42e0340320203902e03000341100d1858007441c0a540440d42404640010ba07500c0b010544400d800e4039440d04441045030654101c0c1410342e1100c5a10500c012071101801c2881081d01e040b5284400007070345940203049208211312421114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 929821258 1250 929820008 929820013
    0xd080610050904060b180901060e060304031214091b0d080f070c1e050406140d1209030c0b0a0207080d0206040b190e06040501050a060812130e07020307050c180a1a03 73
    0x2680c40f0032114246000245401f2a65030315540d90310703001941c982c44460b03811600540104001000b29004e409044a04108141c000690852082414924100648040c0d01c10340107001c02d200b807040d1071900705140c00e00445250a1640c503980d214104d0b0711903c541170302c040202007000b0003400f80450340c0500500790340004007018015080303c2004030f1910301646200f180b03030401c0032454101c403070244500c45801801003d021b03551502c41c00d1131400c0b031a1041c810030000000100009025503203c10052582a032459112000d81e40082d003004080d41003140b8550200040354042640020707002e401a4020800c0b018580750114a40490711507128403540043c00e04081940c0c0d2007001034200e00c2540914000c0200b5169032100c1e0054581c14440c1d20501e43c0580c02d074420065014004003600d030f03a51110440602d558003003071482c0b0a411292080944c10101e4180c0c2801010f2060201c407a000f26650711010b0001903018200840c0035002000b030541c1c0f0f61080204080c154140c00981c2d000904 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 929822508 1250 929821258 929821267
    0x405030706120612030c06050c19050405030d05160b070201020d020f0706111c020903010b0d0f0b060405010312050310031401150e040506040b040c09090803090d080610050904060b 79
    0x80a441c910055503001e0203180742807000118495600300c8a0402507065846c100c554200b51503400c090a805410080d80e988200030b00b18858078468030f861540400c4d900d0b0b15071640d02d401c04042c10f00341c0da03066541c01e0240801c0700000d50050400122400c590181481c2c01540b0761a10881c024040c505203402800c0c8000b941040d90000c80c0040d154a41c800c9400380310400f100080501136000742c0040d0b0070001242404403039107001503000b400074044050000925401100c00107400e04a204c0415983c1c40c0381c044a03081440f48400885610003070a86043c080d079491175441159850640e1010000c111011021030710801c0081c182100540e040840200e614070070040c01c0d0700810100c0485c2080714042c030000074010341c1c0b070f24000d8030450700000030b86250380d10740d1074503a641800148111001d4824507070200b8101b0f0b107841402e5406006248143c0c603442c25440f10382c42c16401002e0030043c04040010425959101c188540e00c20030280b60050700d442c45500490040c0c4803580014402010115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 929823758 1250 929822508 929822519
    0x20a0c02060d091a0a0b100f050d0f0504120215060f150c0f03041419030206070c0e0a09030806041a0f030102070b0c090a12050a0b1509130302060709240504050307 72
    0x410450044500031410002d01b4410030410042d42440d0101c2da02240c1d80c0c0c4007080c9a1030144020f0710140031070100c0803c0707860403046000102c0d034040b00c080b90f41c0c03420b0aa010801d5a41003064004406085409015904102000401403441005142e2040c3e050500440300b07030050034140c6091440c400104c82c890344820722440c2e140d81160003081000240e58030741164514151300c0c0094041c81103c03c600c040350841e001d104013a4800002580c000b19900c00004400c0e0819400300e205003581000000d060303550340b800038207101d0081d0141d4400c0d4106450740112400c02e030542c840300a4200e4a8400c910307500c00c046406402654005000759010000300f1103c80c4040b00201038000b000c0707410300d504589500458903100703402c01c800742a650110104100140440000c2504482c40c80200b0001d81e82c4803000500d18003040f1001407000c40d6074103490040540410405130004400d081c420001824072015119521030030803504124132044100c0030314180070b00111400390502070f0946d06120f0320b03034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 929825008 1250 929823758 929823803
    0xd1407051917040b1501090b0f0c0703020d030305010503011109100f14070f1e0c060c0c0e010b0702090f1302130e0109080408210307180e1801050109020a0c02060d09 73
    0x701e45401500345c81a6200b41e03158495444c1506951400c1203090405144040381212a00710481030b180e28414031802101590301c1c04e000944480c4a544e000c03d0030760421060500f59000d1702401040044180000c0005984800c030151000d4840d2400b20f04805605100304c0c0c0e126500c030780c0e510200e5000908201440b4000640b00416805007404040012000d00c4113055680f82c4600540280b0050b1018400e0a104c5c0102c1c0000d14050880350840e15210504074403014800e071301a107011180010080c085050042586174000c0f85021000a0307490500209420150641002840b4000c520070241700e8076181c3e8800300c4c0b6200c3c400003c10a4a61714500402c09078042d000d50582d0f4401c4669402e40401981051050319480b46251803c503162104190f803508201e0903040981c4140f80344c0800c2e0b02c1055a072044c800d0b407002640351281403032550360702c0c00c44106801c1601850f0040011004080d040340da404509941500c005503581c0034610b400008242100303005100d1580480d40e0010313610309 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 929826258 1250 929825008 929825011
    0xc0c0f0504200301030f050703080a031a0d080d1e062c0103031b02060d0e0601090c170408091206010905060f03011e021c09080d1407051917040b 64
    0x80d20104800004800c1080800000340400ca002d00020401400002d030040c1c4000c0c5201e21030000c89501c240c0f6692168680d4101900c0840080e680d1940c40c08030050340a4455002c8a00342c41c0c00380034824940780c418441c820240e0044003903407100d50750480302d500446246003170a44888208030b50340c1ca0340c96961580700341c15441108204041250356001602c24969030407130758140c80d542c0e10320a0441a1010741ca130401810380e80b02d0300c1406401020101030180d00e004501c0395010300290360600307071518100e41d1000c080700200306c444001070040500d200d9013140c2041c0c1210105032102d083c54002074940c584440725044030b00030440001076000b50740d007005000e100704641d499030f4907101100340b5088030000c0d0f41c02903d00c11a1104003500710340f41d6000700003403000403270021220401148082c05540d8014001c907035035a40000c401c0c4c41007186101d404081c802201c03d1040728144035030000d00f607008003665022191950b40768441c0c81e40c0207000001092461120903075641c646814071408a140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 929827508 1250 929826258 929826269
    0x3050c1e0a020a140604020114030c0301120618051f230405071a0703031a0609040c0203091c0204060602060601081b190512090316030e0301140c0301230f0906010c0c0f 74
    0x112400800e00c03825803527080d24031a00c0d401c8441400c6038a481d5007600e2054004030180c411582e1000002c210034007988004c40c041c0d001d04001e000704030198562210040c08180310380300c02c1d0718151582d551070b000f03c8402103411785500b0241c641c0b504c3ea03052003401d1608a0780442d101d00c1280c080d2041040710341c0e000d04881802038600f0061083d07540c0c2903807412802404060b6114808001050030303440d180c0c1c02901408203610403641044008404a04940214204d90a102d46039041990461411f40900c40140000d44007034416420140000391904001610300c62240c4004510800c5813240300c0c06a17241c2c0b01941ca1104a0b08030b0f170380d0014000ea8031100718524001a0140002c50780c440c00402c03907800c00d40300100101c1d42c000d1924206c42a81d01003074481d6265480f5090440440c81c515602e42c0078601d01d0300407e40c2c0c0e51401b0010602c4a00303000c841e984200d48000104d01d0b076615452000c020032020b80740d40d0059501d40700103e4800e8003600001700035080404000c1014040307002103206545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 929828758 1250 929827508 929827517
    0x120c0a06021e01090f1b090f0209030111070209010b0c101e1d0601060e04020c0d0f020f0c0f04050a0213090605100c0c0312121b03050c1e0a020a1406040201 69
    0x44081078a1403d0b50056031020309070a000785c0d008070008030302984503610444004401c440d044e4880c96080141e031018003035103014503004035800c1810301d020300c202161200a005e69a2800c1ca9590202d25840814456180c1c6680040351018851805012076a000707040000204407600d0200c02d4065852041200c0100321031400503152000c1e829180c1600d403400b0154020716080e0329151089503001c2c0800805034025409025602d0410420450207409144a072140b64280d082c5001c028548003421078000425441032081d01700580b1150310610000605460100d4159214580351001c2d215008584c0b0507001c02d00c000085144083d441601500c504986880068000da5030440f12a49500006070076030010070800c00001c3c240000800030a5914100034000840c0c01c1c140e5400c03a031100804030401060f40105001050f8984509a07000a08494950031300e640603c41c5240038140301c0d1400204580080d100d03202034000c0141006240d8001c00c00720358150301c161655113841043c0d07801c0313010a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 929830008 1250 929828758 929828803
    0x160507030c0806040c0e0c04120507090b060a050403030302090d051c020618061306060e010e060f040e0a020118080d09260d0c0204021e090306090105060d02120c0a0602 74
    0x525001c24014051354102c1c03502a41d0508114082044c101c020f001d0050403081003000040c00c0088108201072140140050700b0f001d8940460340d8140c40c021740c3c45510400081150a0402e0b070888140c40c01d0b00d030545001a12091010081030303c540c0301407406400ba01c510b03003d48075120100b03051701240f640350740d0950360181c568449000111040f9220704100d40c0101000400c5102c0041c85c40031020301640011506550b0380040307010400003071b000413502041600400c5082e090400c484440e00c0e406441c10055181000c2c0041d48034600c500c0c0082c104450124100211464100203034060000001503501700c0614100203800f03440c15218000c00c2d190b4602644015000c000001d245207a6200c016000a5520450403562500d010400f241c0c4140e0a000001d0b130800e142042140c22111103580030b80c0c0c0d000741c000b00340c58600010412002681884204501c40d00c5282c0b082e00745a078140c0f0044480b80c20400e15608010001d0701254001028190014940307a0000d0f001003101c04500b414000c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 929831258 1250 929830008 929830019
    0x50a12031808030a180f0b34110603151c080307020d03150b0906070c1a0c011404081903060b0c2b2c041409070f080601030b0c160507030c 61
    0x5100c0c2c6119000f40310407100c02c1040b1341070840006103003400d0340d523140300c2c540880120b451441c01601b05082c141d1041400c101001c10207401140c0c0000d14085554178118034083c50300b40c200003800807810380507136241800603901c010f042012142203070307001311007988034076043e07500941e00d1005070700110000703040c6962043d20111250b450400c0d01c0080c44007500e0204020306200c880d41c4809030445008a2503080020002e00c504000ca0804c07041030351f010780d02c0c8100c05800703081d83d4601517a48040b001d101e05020004074044112001c030070041d1840c4608240e181d000360300812041d402091901030001d00045c5a0702c001c07805048061201e800d0100f21800e500c01c004860019014400121300e180b45084884480d003400300c1a01c900d00c20001e58052031400114041d10380400401c200304074810b007407110041e02031244002500c070150200d81843c0c540b00e95141e46036418840030b051780c100040811007003408401240e5080380091818048415181750055482140744815075030010654000b080303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 929832508 1250 929831258 929831297
    0x60f0e06030c0a11070312020a0b01240e0109050306190c2102070221010606031a03100209010302120c04080c0d0308151c050114010609050a12031808030a 68
    0x24000050030141403c150420a4490b005020000d03102ca100b6060000005604138901041c14111035001d08014030562030108002003040c0c1121401080280c054030658a4401503140d01701d850f441c0c80100d40460a006035052545034104980602a0002b0001d100c6892021000b114513181c3e004c0221305900700e400c07204c00c0c80f41040c261032038603a25004520411990040d040060009254000d6100c0440095900315a16099144265110882004001d0f010300c0340e1084081001010a0f50061031b0740020f071220124000b0001881d404144002d199100e903042e620044201036030710642d801c20f050350303400d0b90f003107480b407844070384205102d87c825401c0038a841c00d0b4290303250721100c41c0ca448804c2464511107030200c0d45504608000b40400884150401034117005000b00000a01660044c5142c048000c058000c1c1c0305100060104104640350a110007080710410410354100c0d10403841c003190440301c070003000503100c0c184c1c00000c80c070340394044014030143c0c0b0307161911510400540c40d05070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 929833758 1250 929832508 929832511
    0x328020f0a031e050906040f0627060c09051008150901030f050c04150e0414030318011406030304260307082d040b0901050c0a03020105010f060206090c060a030f0501060f0e0603 78
    0x4001b40c010102183c009030741c035003060f10582d100744004525000c1e43d8110391a4402c111803400d0f0110441c3c600d800920526100e999450350703e034034003140032900b4100401d1008408a408008000c0c44c40000b034070104c01851051031101d00200049801d503500d040c26503030f241c0021001d8440e40a041c980011525103403041c0c4050340080c0350014125842d010320300c440101c005000380c540d090003051100d2007081c00d000442c441c0078000c00364601e0341034400c101401c40f0303980281c01a803088000d00f80b104941d800002c4d18101c0d0044140d0380b41250003503807100080d099140b084d01c4584804180d80c01001074210180855022034808603074207400e070000000c0211110340f20040c48800c200410300822009034010903109606042c403500d081d030b03445805480d00300c0c07001d02540141d49d60700040c402d5005540a5070f00134682d80c4020592405d12480c810f4580012079051441400001083c1d104c06010350010785081d04100700401196958100c042d00c1c3c44508000d1200098601c1140b0180785003060503203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 929835008 1250 929833758 929833771
    0xa0e0601030f06090606091e09050a1b0305060f220c03081e190318080306100c02041506020723060310030510140c0328020f0a031e05 59
    0x4194591071a01e6286419a91540c2620640e8039510441c000c04d0481c01244000e0000c0400010f8906007007007011248440000e40101e510b090044801c046000000c02481550708514085082c0c1458802007540b40465400240280140c070108500c0000e4100c21500c24614008007601009000b40f00c103e404828800042410300c2c041da0900115901340060071503a103804500c03c0c50107840324061403458226285001f825002204c040c0c001ca681406600404031144000e180321440a549207121070200500044c062401c644501c410284200d040c0001c841e000381041001d12a4201c4041e00100035014802c00340c8541e203000200d00c0c011104c10400284400415000041c0800c10040a030f4800381418000381d01c41c03140440407510900540b59007402c0003800048100a0301c552411580c401014940440303800e000700404046510907140d00c45411020020310300c00303c000d0000084c081c985a0a102d00004a007011045070940e004007041c2c40c0ca40e4031003c1b500c41c0070f03040c482920300c1240e50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 929836258 1250 929835008 929835013
    0xa080a0305010e0f070c03020c0301060b0c1207020a03060203102c07050a02030708090a051c203615090112030f0f0201020c0d080114040b030303011a070611070b0a0e 73
    0x45c0680c0d10450701c22020764400e2046e1030003102e6500010b0300350345407070b0060181c05d00d002510707102046c010004c1d01c07050b402c039800007400c1c4102500040c00c0c0c0d00341c070f01c4007515290f0004009142c003030002000c5000790001e0301070101e000d21f480d0714000704003540e41480c03a03045038104c02090f20300c1e00400685441040b140d000354900360311a030301c880580d08501940d41c1c00c61143d07400480c1654800d02191401d000074242d843c07400900742454808012005000c92000c55034141080740d94aa5200c01c0450104441034580e045040503010381c030300c0704010f0f0030046c41010002440302e04201c81c0d8000c00502c0c0100c0f184035181c2d0301d0707010284180d180054002c0108140701b0341e03034000703e0081040788010101400014240000c01040c2800c000e001d8010700005840d04005102040c171008207401c40760b200303440c1002124422000310303580c0d00c410b00411680da81c012041c0324141e15842d003103c040035030260041c00401c06285144401e134100d100c2c2103c0f01f1000600007048050b01d44505854542075800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 929837508 1250 929836258 929836261
    0xc07110a050312090d0206030c071506050609040903022e23040209100902070804090c02010e1015080a060506030c01080907120f0b070c03140a0c0b090f0a080a0305010e0f 75
    0x7103594840d8804c00c441130f0884200c82d450005643c075a0081e43c07049000f402c0f00b40d554052894190b0044004002c03080c21a407034007030f00b84020748802050b01d0017200c0903540090103410a0500b80c0c5088050403401e0802d40000c080458001d0f95a0903c2015800e8114203110050380700d2a494080d0b0070009a180303550f040c00d0300040140c540311203655088842100c60803001510341044070140d9004040c152550340e8002820010700c511440b401c0700300000707403008114000383c4200258844499110000d101d03038407500030110f410603903003a00009002e414100d03102e408491500a01402e42110014400d01421b4480401540104005c0b4410350820005d00b0f48141480c000241056441109640809020301c0200000311002a841c1c0981d0a685440c10004154a00101100c40d525078104900905004131140290410703c3d281050b54130040e0001d142d03441030981d42c6008402c404607030035881400c040d102440268402000142603d94041c0096a00c800582c0040c2d40192081400c1600480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 929838758 1250 929837508 929837533
    0x7030e061014011b08070305040509090a11010509100305150a090b13050115052b0b0a0503010c1b15050c130f061218050706110f010c05032d0c07110a0503 68
    0x40003400024408e090141c181500e4501240014204036003140c419441090f01320203011030326150701c0340b100c424a030440ca044c6501d00826503009244428a09054a580c0410150112211800c8005201414515030607503a00401c001916a4030403180c01100307070201c8000c1710a22400341d0387c181c032018400100c480b6811041150700da44800340350300010b40101501103400e00511448071040100c07940119885182908100f803044055200d58440d0789445001d1101a0b0890050032910030250100c80007400715090111500c0e180c0d081c5444503501c0c000030004c66041c0840905203000c405040750b43c000d0b44a88007c0e624100b1405044007060f000c14145501c00801d811942c152083d042468507102442e075545490145a60080c1c00820300400e0a41c0001004100b81410040590003d111044000c2c6c0043c0081c8000343c440c040444a400c680072070040d002c0f441032074140180b9134020746403401030702c449203d0b00500c1d000c60303d072a0f0800b02508645806029241038400c014046c0842c41c000c50b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 929840008 1250 929838758 929838773
    0xd08040605130506040e040302010c0c121d060403061d070f12030c020a09020a030b061204080c0a0b0108011b0e2d040f090203190308040b07030e061014011b 69
    0x442082d803840c100254045281d4484102400050600f44a080101c0c1868a4041d00f03403075069540c4810080b1150302c800104180c0200e90600c03c90794100520305880a001c29880c4103084407100e5088000003500104100a076030103d2030710a15544044501600c2408482d290401c620400d100420340710420300100d084207140c010400c3c401d0a01e807183d140320ba4086001c0880b2070303001c0302c1da450b8040f4411003029090301610107040000c4035418500107000c03034008a01280680040c0c0041c10110f00307500060010072a8009007034000420f46590760f95055490301800c0400c1c00c0070360f00102c401c220700c2154043c41c803041084500420361841070405807a0100c0c0407140c03034140051384040c0101d1200c552601d114020020190030000305021003130303006061a055841c11449a080141103410001c60751208640c0d070001c2e80488600f0180d10707081c0048016003000400c9080700c0c0100b00c06d01c1211004014000125420f0b50112458020084015121030010341034001100c002d0420107800107841 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 929841258 1250 929840008 929840017
    0x601060315081c03320a060f121b1211120c040b0604090f20040f030609050a21170606040b0f070f0308190b0d060c020c0303031608060d08040605 64
    0x141c42c00003035401010901405c00143c1c56000c0310510b5016035031209002c0c603111003e030300c482609010311409180548134034042d2103e11940c030444003000e40f01c0c01042180b00298a4000c00c081044403426110242025250b8550700200c400035030340c00c0104140d00340b004402d18240b189030050300c00100410140300281000c00100c69000c4420480030440300304074407400d648802c0030100041c001c0b45105003070804001010039210914024442001101030b1400c0c0e4801740d0354071501c0402c404080d890024031300100100021316a00d50070600359069801c0d80782c3c41807601b441e40c3d03a600c0000080c4981a020410039a80342c2d40001d001c0001317001d480300e00002483c1001c903542d03031a4a45030003520b51402c2c081100701e00720300090400d0107204400f100200307680c00404181710100054080c52000500c100c06040300205013076140c103401c940850080c85500004000582625500c0c5010344100c10010650340d01000859180c07404035000e801d245ea4420751040d170142ca424601414100c064626800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 929842508 1250 929841258 929841313
    0xf120c0803100806090c090402061309091505060a030b060d230c03151509090c040606030c032f1b01020703120c021b04050903090301020309060106031508 68
    0x1980141001a8280e4029441054401007040c81c050800b1101ca04002000d0300c1034503903034007065151025981da01038090700030741e04840044d87e551080b0310001c00a40c20f9800101500d1805d1500400d12401c80854140c0310303910241044244d90740300400c52034503024080500b0b40c020a1000502c1c50509030308011f0741c80d0041502c104812400c00420011400441c0d010b0625040354446035580c0c1000c000a004a401c5102118881e141c1460b60300c810620b0907010300c0c840d04400000c00e038100c105205101c40d0801c0079005210050311150042c01a10840142e480024034021040c00d10000c6100f07003444e44458008041c40d032040da000c001045800c01c454182c00044000070620701804244000d1000900ca501d605040c41c3c0d10102070b004642d0116030800035034010f91811601488801300400c030841c400c880000d082c2e11034501c20380c80d5020f582500b0350158400020b011081c1030001e8014101d6900b40d0301800b0400e41500300d038039402c12070300c5840303190b030b0141b0b920311030100700400c50011400703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 929843758 1250 929842508 929842517
    0x12020c0a17070605150a060f12090c0909050a0209100e0103200d0302150c0a050a200a061b0203070b0a0b191206050f13060f02090d080a0909090f12 65
    0x203443e00e070001103603000d8a440c80d40c0411003040c1c45283c01c00c1c10181005040f9070500e10b032040003446016240201c00081149901e603a40001000c0004034485072018026403041084000d842d840e06e180d554091420991041d00c0580005041408002d600d5041d070320700c8084183c03181d107190769068480200380880404852101c500307201c11b464030601080079601950060885001c2290005440000600f40e0140300604101420080d6084822150311300314502e0f080b1181c454409170a03424201051540c040c074003922102d04103214188e0010320032034000c1c8810087c1000341400c00d995034412940014070703d10b01c00c0001410258564030095901c0340281c5142c001c0d0000100c040c0d503184240d08012120004e043c044000c2c80368a101e501c0d0300c0030b80394894000728100700d081034081c80000e4000404c140d4403451a6100c03040c141d01510440380001d02030429030805840e118420f03030449030724900040c4c3c100c00001404d40040c003e038010190840c6540040c0b0946803106064099100306000500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 929845008 1250 929843758 929843767
    0x80901030b041a1c06110703030c02010506011b0609061505011101050108191a0c0307020f070503060a090305040b030403050a12020304150b211e06101401090f06090612020c0a17 78
    0x40c141d00410744030a0048411b2a41d45602e4500070342151f00d10100c007401c580c5490f080107002d90f0460118001a000d100b0b4403c1c0e40300c2249004006060500e000500d218180b844001c4031902110012050341c1c801d80f00d200c02d18600c190f00e5401c0743c000b449800ca06a001c0c5418040fa030820031b24041d00507014035000d81e4030b10a0115480707c1c052041d1013084201d05c0000c10004c0c500d60600030407119400d4400540f181e589050002643c40c0301c06007000c25540d82da1240242054000c200326002806030940854481c505421301a003d5040052540081030355001d1009142110740300700c0340304a9102c0445908880c800d0705d103030b0003001c8106009401070300043c9a00c80745000c01038078410b0443c0000003000507000c1140c80c00c40a070610440c1c000268494002c0c03114090703456152109540b031080341d008040030301c6801241c2c185400d0b40490080700d00300390081840ca81c000300260070ba94480d140c4c0050040c060800008034800c2980926541d000200503d000dc0c451070b90007111041c4034007485081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 929846258 1250 929845008 929845013
    0x31b04050c190f0e12060103030f0207031e1202070f090f0605030a061b05120a020304020102070b041502010c0c08070b15280501020d080a180807080901030b041a1c 72
    0x799000301c20040e0209a0301c010200c03c00350300480301c50a02000392003030008101d948003100c0e69213a06020080900c0084d500a040710340c0f007080b02600171034103c0d064520700529003510400b00351410500383c5150040303038807074a4500e00016001040740c044610f0140070394030f4020042e004004412849003003a17144c40c00001d481c0e4003040a01d01d5540220740005050401030350500810000168080038483c041c48810041d141d00804c555102401000159590ba21840101d003480c103103400500d40f0300d0703022038007260302d40c03000502e004541040c0c0c0007000017001100341503c0c000c01c01003005061000c104100e0300010300e003158640d0801d03c800c1040c64a030001c0000624280e6201c081280c41c1c81c2d500345040c078a002c5041c40500184420700140040c40f41a1400404040e002841d1801d5942c48804190349400c00c1c4120b448241d406c0540580c44501514000c2c0c100e5101030040c6001a0810000d11070034074251042440c200c00290a2504482c4158203025100c6450242e5030751480c00b24010001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 929847508 1250 929846258 929846287
    0x11010912031a04050c0901030506030c0d03052502061c1d0109030201050f3c0c0702090618160908030c031905040803030f0c071202011a031b04050c 65
    0x8000e2103900c012500c035641c440003112400c6100015072241d410101405010000030040751200c607030078030b0040780c242c0d14a40828500300c411139549811034848540c00c8181039001001c0d000c80c074560790501e0403107190124005405400514040c3d8400c004204441748940100c0d03254410790f08288000c5042c048003400c011030050704042d10966039440f20070903010554288103481d800642c180000f441401c100c034102506120f9800385c0c40c01d0343e020207800d006a1002c2c00c0204072101030008101c1036450a5414a007240c0c0180030200e0254055801054691900351411100704941c00c6002080e81c0d10100d28840504402e02204140507480902050014051008040c81094100119901e080c03070b04844000e406000d400c501000700a001c14001d1800c01f00880340c01000d9050121942d440d03803180b245180c0b1a07200004d014004030704a1182082d019000300d0b503610f1009070000c00000241f000c2c145c85140030008000540d80503002c0504502d0716900c025001501110b1090a201e2018102c08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 929848758 1250 929847508 929847533
    0x1807030f0c08160512010510050c0303100e0c0c0a03052d030f06030d1d010918060f06020d020c0d1e05060609130f021e041d120c0d110109 61
    0x1512250400107034040c01c103680101d003c9180703841842d04824813540c1c81407001c1170203554810b071800748034148984e10031420394507043c01c0f22080d0396981c140701c0b11100041d1707800c1c070400c00045851000108400b8400e001c0d100c3c50f25242000d407d80c0700c031561b01201e0540c4075482a01c50a03051000307041c1d2410390b030400401d80600c2c1e09036803540c0341044010044080f8001305124400d42c0b00d40940c50782e0b1544209031005818004940403500540d02c40182c5040340141c00c0f140d03142d1001e0140c0d10f01400c942e0401c100b1a00c04488965005803201b030704036201e60088071644050380c4038011400c05810b00d014800400c9000d90011280d87c9044003032509104c40100317041e0381da6070002040c45043d107031031000e90b50440182078000030300e44440e0303031249110354035060040c0c4510410301b45406010081d4481080762380004000b00f001c0072041c074454402c00f0b00012410030502c0b0b003038100012454008101c9143c0b0b584103008128102c6510000c81d50300401840f40c41080d500d5009410008030015000c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 929850008 1250 929848758 929848781
    0x607300209040b0301051003062a170a020901230c16030515010e0a0b150f0d110c03071e05010f230403050a1121120f01051807030f 58
    0xda030316408032041000b614003990102d0310a1341340a05214404040020b8901103a903c840040303080c40066490400030801013126a8410319002d4400c0d4003243d22440c0b461030b02d107014031021305070780f9400340c1d0000324005d0311a0702d4041590401c1c00c4802030075081d0343c101d07000d0708000b00301c0c58515161403913420400e140b50b192500d8100c0f81818010080240a01924000050319403a02585844900c000c42803000d81000c117210b51750300281e019621101d10802405c020507d226a0b5200d02403980f0f0900e1f4401c028003800070f8134140383c01e00c0d4403060600f20f6410f5010140250704100c210780722190950380a001d8060452142c85224001070310070701a110702d1103004100083c40c1b500708200c0b030911240001d54000008850420000000c2d007104c181c0e0101c030071610304007000349103d01650b89400002d40c209411038040309501444449980010280ea00185c20503680c1c5441d12001c405000000303008060348050a01d07558509020100002517000c151864045001144085000102c8046081d40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 929851258 1250 929850008 929850011
    0x20406030f1202010b0d111804200103020906190c0614041a1e100b070605010f06021b0609220b013e0a1203020306010e010c05060730 59
    0x200014081d402c4003204400c1018002400307000d83d41000a4621000381c480205440382030700503460305454120500d400008002002c038004d00b000c0c200300c0c10b84110101811480d83c240300b0b900c941ca500c40d0080e141c0c5050040c00640c184940d49803d00d0401c0e41c0780071040700700704884c060080401c0389401000c0d6044003420b443c84007800e0904100d11a100740050400c5e082c002402808186510340c900c5c45030b0300d28084505e50300c684071160a1540311403140d0041c2d202441c041428020701c42540d210f00d040b203203c005800307907180d60307000d040e81c49403406284c600d045142c503801412541091001130054801c000c0c20801c02680740e500e056240120352043c241500c0c0c0d50590220300c1d58101c000c148554412100900158604541e200c0c00b1002104012020101031440764141c60f408004501c5801c2d8406294494803987e03240c020002d4100b00c40031800922030782170001e915409010402100303a0814044c1140c4d544403107003030b5031a0707403001961010303507003620001800100c05060b40442e40d12204c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 929852508 1250 929851258 929851283
    0x307030c020d050307170601050c1501080c030724031503050615010509032802060c0d12051009090f050609030715110a110304080114160e0f0402070f02040603 70
    0x14000e02e030850070300d591818403c080051000d055040354400d0000802000715092640d90000120396a0240c0c441020700340c46881c8488040103044007072641a6200329080f56104e0214400705503030b0310014030821404903103080c41c000e421506502505581e44441c18085800465a543c0780e0840540d60700a440c83d420a0041c041a1450400c16840d096001d2822a04182c7d050000a0300e401c81e0304a40c0020003510030085028009074803c504d00260002c00d4036403911740000c03041c1e40350014441c0200024621003000d580001403449a14000c034040009045028200031071000100300104080e14a4a420442c102c00554100403039440b8a400b00080d548900041c03404c9414030010710a1450440d0408174101120052241907840300c0c0c03100c1c6410786031600c603012224118822904100071650801c004030141c4800a101d007400f8040820f503003c2d61a020581c1250140c1c080c02081d03031322211401d54801c0303919181d0045c0856030302410303554070003208503800078044a50541c800c48004441b0a07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 929853758 1250 929852508 929852531
    0x9070b0d0e010b030a0302070b0c0c120a03020d0216050108040f0c15020708030909040201030b13090f02010e040b0904080d0e03030108072903190603060e1510030b040f0611030703 79
    0x40c070002e403c401d8004041034011641d010b0f440e10564050a9800c18010502c0310240804100101503007070080d01701c2041d00b601310318040d2592034400064015209444028030030902c0045d8801c04c036507003081000013040c180001110410000b500541d01c281400ca2041c000c20703a40360a0000600c2c102d10403024142c40c2c000080c0c1072450b242d1001d11903802c01d002d000d50a885848484e45c1c06542480c0008021001c0c030000380c00264220b8071070081c00d21f4180d802041005094400700424001d80303800005040c1c3c0010082a100c1100031290064902000b0070000381d0701d20080c1900c00410301021595869481113507141d80c20076070003810740c0e6000040070084900a54000180d242444d000c031308800c3d00320090001c451101500110205109a0101c104680c031035001c103028543c402e20a1010b506101162540d40009016802e040001c14010501040102d0f09940c101d03940283e199155035200d894101011f17151351025141d803501e44201b04a1000d9020056104440d5602c00040500548 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 929855008 1250 929853758 929853761
    0x310060311010203070206190c200f0603250509030a0507030c061713060f1a130b030d0305040519050703060e0316111201110405191a0309070b0d0e01 66
    0x1d40345040d500100107240c00340e00e0f09411160326024450340c84660544006040381c6038050580080c0c441700c240b001150206c128149400d1084800322001070301190740a08100c00c5100036102008841221586500d810a41074103415036100d41d4280300b030a2401880210303040c404404070448082e08000e400b841008100076144010b0089444c02000c1020301900102d10071202a00143c006040d2800d1001042003035082000300c0c02c940350003440700c4000c10140015a01a8800b000d11400703007603a044d91940c07414411440c031030310020300500c2900c2094000741c0c020b181c0030308180e915008220351040c210f039000c00e40c2440744e840b44004000441c91401c000c0100d070284044000242c2007000400356500b040dc1b080c004403504040c1c600b2150300341d90001000b00301c01c0106680c40e9401c103040d00e204025190058400c5902c01d4908250500c0103a22041030400c00b409042e031151940144910314031200c4000d540e00002d03500855081544402008800c2d40200c1107040a43d9181c003801d4001c41c5c0207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 929856115 1107 929855008 929855033
    0x150206130524070f030902011d0a08070b07170712050309011d07061d130b132d090b01090c050904110a020706050f160c0503100603 58
    0xb04901c0d04094641162074002240020114a4400b4020300071a580f0380d50507903400350307100501c4000c48100c46400c4103090300140c0000700420b005804004d40d8000d4820042d0058031800c85203450f800003030f0b060702030032035214060000000003048000780151200c554180241c50b99266200d00740180300904802d0036490654110821880011941900752007181d070300c12a030078100081f00d04040e506000400e81210940045c180f00c040240c1c404180020014010921100d00c00c078403c0030344488010240030042800190700e0814a1260026241c8003280e0b400c2c031540321030f9120101007032414030407000c840782c6138010b081d10790344600210340e80d100c0000c10422010700810108985508001915805440380050200b10240980195801c1d00074840c880ca00d04500c02030112011036003820101e8104040143c049135583d0240040d162007651103100090711450b6080140b8000e11 = true := by decide +kernel

theorem cover : BRFrame.Cov 929676258 929856115 := by
  have h0 := BRFrame.cov_init 929676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 929676258 ≤ n) (h2 : n < 929856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
