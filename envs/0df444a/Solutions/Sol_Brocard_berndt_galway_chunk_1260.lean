-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:02:46.067122+00:00
-- url     : https://prove2.me/submissions/4099c166-bc52-4166-bb4f-4cd23aaee5ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226438848 ≤ n < 226618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226440098 1250 226438848 226438907
    0xc030e07050d03030b031c0923060a0302070501110a030b040203010e010b0f04031a0f011e0308390708190b07090803030f04050f0a0201020a110312120103030e0f0105090907 76
    0x40141e1f00603007000181c141a001442c1d0049122a101c140884c4003607501e0810751405009032a801140d034a400e15800700700400001d2000d10809280140f10401d0944642c0d10040003001e4400c50441070344500e0041c030042c000b00044e8001c4604441540d45116656014582402e0150185d40e00c0a812079000040685001c5a0820f200e40314141c1012a10800d03a2519a00750110702540c4ea00000207882010503c00035080d40001c004481c1c4200e80b41c15030401501910a00f05a64070000081140040103c5200e1500300010300c050030944c005400e000c80b510030003150410080501034989040790010a024030f029030340d060007034100d400581ba034074504165080c0e00103109036401c903010b00c00c0c42112141c10101040c2e1484072031341640502400c11043c3c8800113100212800298140514030f1f141c00840e030700700001c10606500d02c404414642c50341c100a04818111000c3d18001c0c0300040c001000c07070b0791040880c0c030b441400300d55019440e100c1c28411035246078601072440340c03c0c0840712916003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226441348 1250 226440098 226440133
    0x50a1809020f0a08010c030f06081507090f06030f0e030c1906180807050d020c0a09200a0207090c020636030319150b0304080a0203090406060c060c030e07050d03030b03 74
    0x10f86c03803030310f8406115a4803100c00c0402103401903c80d800740c2c1d401c043c6002d503c8074410510140c0004451a01032003140d102c441c2410b1000450b444180400c0c3d0b180c01e600001c80050050000b1400c42c1c00155007042d0b02d034420541c4410b101c0450348251030751401240108030b85540510050250105414001e10107490808819400f0800036030740c0d4030682004840701440090460302120020300b00b03c550515161500014000e82080102c0306060b540902850058080c06408610f00c03550081114520340441c002c01c95400c090b440d000c64104c1d400700aa4003110800301d190302100d8180707070444104924002d1224002d8589130148a020000c20300840000d807114002c507001d207061081003080d00c07000d4a25001c03800d0741b150340300707001081c40000c022840f13030000344c21403c90324015039252460308c3c00060b003203c0c10741c0c0100c40441c0402d45504c0c180a068442c001e80040da0382006c010804030400780c5c527981d00c000d101d81e6204141c01300303864041506c0ba03000900c0341200035003140c07900200c2152040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226442598 1250 226441348 226441361
    0x7020717190f020112091e060902151903020a0f0c020d1209210f06050907030f0302010903080601031a0922050102030624030403030507140c06060a050a1809020f0a0801 74
    0x7130004903201c541c406240b8151040030f0039147d015140703410403070440c0745052180c0d200d81c40a4a01c81d5a0300d00c2480903032107964221046000d0070140d20f07036481003070319070848070101000108109441030000ca00070b40e8001241140c0900c1754102441080114800203505450942d00100000810142221040c0d0080000c41c2603c0c101041d11014803010032042180362110103010b4007000d006d030349038008501076500441d00014000160744202d03271a500da6648041885c101200141c0d940c0520300b0a06521990103074004100b48bc0c18030202190f00c102c901020251010030388650f008102298983c4581802d40c054518500710100303c0400398100740b07001303420071214103008050f044662900504417108030303c03030309920001d1142961550349003140103010080c915001d021003d6100d21000c000f4401074011564034a0080203c0d141c09800c0c0604904954045801414241814854450303c078070f07942c0804100ba040000e140e002400003540000e060712526410001d442400700d038000c810340084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226443848 1250 226442598 226442603
    0x8010b07020a08191412030a0e01020702030a120206070306140103050702031303080904140f0f0c0f0c0606040608030a1d04020f04150201050f15040207060b0613051807020717190f 79
    0x2052003001801140d0341b544030030710300440c0d1303024200b000440c0404076134000355510a0750000142000300c10750202e8680710f01b44000740c484121402e82d00886960400110f83c0c08041440c0c10300c082440c0c101ca5010815007210004e0506885100151100f842081a0f8000310140c0101d41030303c690303d0814400350343c03000d64602d02807410b0601074140c2a041c41b101900510314481c076005503958490002c0d6944d40c000d03013060030705c2070f00304079070710060303c444029003040003031503015000509005d8100b00c22035209510801141d007081c052140c0440e040340e80718155041072405003800d868007000060080c8100604291009004603010600b071701d4140600043d0f020940003000341d52640d071503000c0e003080100c0f2000040c903c408100e68460a227074000c5c200ca603101d40381c041160792091001a205800c801241031450f0180042000b580c9010704412106a00f5801c0c2c006440c144807800030b48840c0140a1046425549001050129000c2002004c50f00c1c42038401c2400414518045040307642c0d60701f0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226445098 1250 226443848 226443863
    0x41121070905090604020105070f02041a03010e0f0d0f0912051f050103020f130b151801050f030105190305070303020c0a0b0a0804031b1a06011701030308010b07020a0819 75
    0x300308603140340300b180e025a07000340c000c00c074039907650b1300440307455010381c00031181c80404c860081e0040e11207018a00501210710343c4541800000018182124890000e45101390700848402e102214040b07440050840c8a00d000c1140c140c5640041d03c140c00f45a0090542c0d03007041003c0c10504c00003007132140528004000141444d148220400d0544400307000195010038000705107585071034034181950083d01115000f0132f155020b01c0005a4824164180c400d8100c8005501014150700e00c0c0d0700c000e0355a003402e01c142084001c140442481c0014040d05008008001c2e401900c0c40540c80303594025948141242e40a9440f450003c3d103e52030b12400300d0240403802c5010030342c0035090081c0c0d28500a02d0761034030700355610f5444c103c8041c1c90400901c84090f02800c0401e0204540d04592002000d0008401c1e07002c0c180f4a000520a140040100403416070310001800080d80c004512030440b0702d6204221748541050002805000352031344020464441c1060040c41d082a4100b0020402c0c00b0302c0301c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226446348 1250 226445098 226445113
    0x812030405011b0f08070e030604030e03070f0f050904051c0509040516050a03110c010606020703020f04110a08040501150e06030d021b0402030c040b0f22050603040605041121 77
    0x401400d0096100c9480c00868080400c4e0b40303030070b8842c4003025440100c03850959030404851010909041b0113850550000d01c1c450300c01400da040801c10705008250940b071454500e031820903440c2154125002c1d5500c102d207110003040610408110002120f0b040314090101810240c00180203036020585181c0154209000500c02040c82c04950640300c0d21625401d2501c180c18500300e00a1003010a0303004455401c1c8032084050009204010161400d6001410024103500420200300003008406100d14101318407004450114000c0d150307200500d041c5a0005c8d26985465409810143c4c5840c02554401d0780c001007107401006c0c0340d401040240c00b9100641c216000c00ca071940a0398031070055540c11600d400440c1e040030382c0150361003248800c0a604098030741c90624001e85c4403901028100d000070030b0112900c003035180e60380740c50300e0403d6855221501e001e010a0990000400161180b542d6500041c184414012501c00c0660000c00c002408180d8807000100928214056849841180c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226447598 1250 226446348 226446371
    0x7080d0c150917041a0909040f020d1b0801050906011d070509060f03010e0906160c170703030204061103120412030b0d06051605030618040515010b0714031305060310081203040501 79
    0x17400c6554180005d0444521a90765465125040f16031840c00c0703801c42d0121045a01082030424903e005000c4a5451030305c1500d094003041c01d4404c0900b0400e43d9800590040204614403828801120300c00c0074508296640c4a1054405014071074001d82c10610001c1c408002d401d04100560599401030150341c0117485001019564450898442052540c04505029050301503040345140621490400d40e540140d12100da032140c1020108602090300030130305001e100d4002c4071049508070101e000314144200001c46035898180580051705140122040c0382155100360001407030380318003400d00c2c10f0b001c41904d4000300800b02210580441039414a00810051040c001c4a008900041100e2070020001000c9400008003820444203442410004007a1042c0265164003c0c03542039400da40381c0030301f414030074407041482c0348a51f01d5400412450b44c21402ea02030410984906440d610303126510304840d81110402034014140500c26602c10400c0040c122000303520071885100207103c141d5008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226448848 1250 226447598 226447649
    0xc0102030a231003020609041d1c05031b181002100507091406090103090209070f0f05030c191101021303061401030b16031b08060307080d0c15091704 66
    0x1c3e12184007100e144102000540b8000d0058840b441000708000745c0325030404102500881e411040076910340120052450441084210b526401e8140c20a01e01d1441d141c10218414090070f003208041980224515a08403446280c5490103400501680c05004502c1806580c682c0f405140d90070150400c1d0002e210f051190419401b250039042007102d01c104010200702c05500b00c1d100742810182d88400c05e1025070784840c00300740500600c0d11001c600c3c6020000c0104110000c100050034080c040040c8404103030b80508450304440e00c42c04071250031031031500c03c60788588804030701c1511358004106c1603c90242c410042d41180d02c5001d0401c0f04105c0d503c0b03003681441c000d02c4084d080c00220400185d01108038255152810311030700c0c0000d40c0340c4115045070036981100c450100017030b0b441c104201150400300030000c040d2a040d8007c2c102c1400200307005000c407807010790003800e22503c5064001d81100580154500a070310aa1051111444015400c00ba40180c45030149101603000104000b480710f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226450098 1250 226448848 226448851
    0xf01060e0d02040222030c080c010e010c0609141212060f0105090d0c030213020301030201020115030c1208071a04021806030307020108060607150509010e0f061b0c0102030a23 77
    0x1034005214041c1e0750702044025000410300207451034198411a2410503003020b020013452144101d071640e5401c1c00c1e00d0380e04e443c0108001070705000300050401166a0403401072000c0c254049404502d034026450412003003510511010300d82d104268031006c11042800c0944041c4441c500b110b072150b6100010050030001242010380810401c10820041c2d04003031080d98041d80c080e2588856890b62907010074240b40484885c0301c5910740c00f000600441d82d0a006801840a0840c5c40c40e0300305003991545c051681c083d105184809030f007031420804000e085001d603561990800002072058a511000f1150f1850440703080384a818180b400c0950310301c5000714280921809002182020390a9005564014000e40481c0c0d0080c0148807100010300100c182c030440494050780800c203804c20440b20760940f0303030185130010f140d0411090f00005c0007000980c10703405001c42c0d00e085684051000c0400b818401e03080700400310350000081006880064102c00301d8982000c5814403503000308071145040510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226451348 1250 226450098 226450127
    0x3040b0a0302090114121504020c060601052101080a0b06010203030919080403050a0f1506030b0f06121207150b01050a03090206090d060b09090309150a090302060a080f0106 76
    0x101884600d040070721942c0584480d0b001030400d84000c4042c202120034a0300040c03065440802030348204481d000f02c00c02610302e440000e0f41c040d1704140c41c2c0c502a0b612040700405c0c0c54100710010600d0b0140d000e84001040740c04c4122240d466403940c5039561151501540c41c001d543d210400800308101d03501c0001160700c6280c144020341820075160301040031044c140c400540f40400180f0000c80890424000b0740010b91040c000c0e00000c03d250300d092014000c00180c4515207a103004000c01c08201c622902551204444e00c103042542d0b142c9002501520b0b00000c1d201c0584124489000d08150a800901505004401c186c91012401503140c3c03d48001400e040d0004074140490f050050098000400e440d2000340035030f00f84101140410380c01203000606641c0d0170703100c00b41121203062541c1100c1d04150b0035005585480e804401141d984e007030341040514129000603401c82641d108503a00c0014590080000d81e4926140c40c0c02403000e00181c3d070a006281c803581c00011410700603c000c0300b01d0306 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226452598 1250 226451348 226451369
    0x619030c080105460509030c0f0c06090103020702130504080c0c040203150f0a15050d0f020f07150f110703120c0212070c12050f190b0c0304151a01020c030304 70
    0x80d03446620304c403050384110440307040c1214110f10a4200000e1300581c0d10480c0042c0c0210f071950001d40401d40780032010440040d140e0003985040700503032250f130101e9100f50020b00f00580c6c0e44000d1301c08140c0211140c18202c2c406858941480100600030008000a148078070495100300e24541c1000201c1c841903910030b14150041000e42e07040d003424035906c1d81c0300c41f001f41810070700c56940540c00380d400842c0d0440b1000a00004551502d100144118252641482011070901c500a00922000e21503800c0150501a0540c0f2000d241d0342c8a1f00a108070f055580400e1101741094640032321550000070048010910004103849201528801ca410324031059004122400705500d03140d10517440600306482008c2d00c5500481c0c10001c3c035800085240c814001802c0c4125a00c8070302e400e004101c0d004050030498001000e0106060701e603c1c42d0800d0320f01c07000b1a5a503c65140c508001e642e00130b007282080e0b06240a010501201c405120b010031070030303000e4419161001c810591284940d01440c2c6401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226453848 1250 226452598 226452661
    0x310020c1504020303070b1f08030403110d08040f090c09080a0f03050a0e150d291309240c020a030c080304050705030709091101260619030c080105 65
    0x40401c01c6141c100d80090242c0c0d15140550310303111803401c0c0442d5510344d442c201092042ea1529410309401c01000c601c80994142800c540c2c80341407007140302900e00e100d000140603d200b40080c50085400a00b001c0b02c07890f5129548140040103403001050740c0011070f4030741c900000d91485c0030540c03403441907002e0070044000225603030aa030981c01c80035900702003102c91842a586034540e1106549000c0c001e0340c50a0704c91442c20075100c10f4a60062030f02c0342e178035028070850782d244150740c85590011004517907603030003074651552241c01041001c0c0003034152001c101325036000c0ba004113000c1d0703c240e0714a05c00740b0607056403120907070340d0b50107450f0010001081c5480c20310119480f04040d503007051160080d91003a5550b10002803510605401600c812559001d101e01000740480c80c04400365001c0c240040c050079080500040c010010200b81003085001000a880d6550800b900c00031204424282403901d07100d050010107104c250003405036540c6080c5c040760b42c245610501440070f403d032a0504424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226455098 1250 226453848 226453873
    0xb041b031a030102070305070605070c05120a120f050718061202070503040305030c030c251205011e020c121e0c0106050306070519090608071d0a140310020c 69
    0x20004420001d2848031a05040075141d42c0038001400e4640c001c0d80c0c2c1c1038844845081003070032106d01401801c10301104041d88800504d011400400804802a0868482d0712908080c0c1c0c041c0203005002c2c1c0c03003078504144030030054101d6000701d0080c20380365600108548040d40402c550240c5020303110208072001860802288550002d00c000340c80391b01aa410030b55a0359070f05155421090008000360408a02c121401e28100701d02106181b401807051380061410a40510361805400b9901c09981e68540c0041402800d4020184c0106a404ca41100e00540515a0000c0d0011220000f40b401805400d02c0800003240c16185034903489414035102218480d01c070140c80d8010400c6803425521808000b96960b401e2002c14400c80568035a1942da10380111007107024041200010244411108140403680d880002d99501c050300b8144420000190719031039606050070440380340c1c40701103400d011804201e41050005041002e0342140c6c456854240700070140d0181074850740c0a9032006030903d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226456348 1250 226455098 226455101
    0xb0f0601080709210b010e0414010c080a0506011106040b01080d210207021203040315050f1302040509070302060705010c17091209010c0b0a05042105121b07050d02010b041b03 77
    0x812800c00e185804c0c1401080d5940b01690009038440c03075075450301c90100700c14002214404842600e1010082009420318035016000b44005000555496910700015110b80d00801c14882c0054600301141c0032868203280c446022102401841c5484c02910400703140c1e14081d005010b92075054048242c400d03802c050814000b9000b2210613607100340c4103510a407186c50203100901c09540110400780208c214843da000039514050000c03174806d07001ca02003050303002240ba10310704490342c11500802d41d80c9515944a20741070300e41d08081e520150000b1103004100d01581305001e0601c0d2030700c440304180303541d100341665450100c0307100340ca17034014403461000505080300030b100f945014180017800008686611064203003c175441680307250b5480900040c4071030600c83c94404400044c550310b0a06400e40c0080082c000c1000001c3c00d03403a06004524804964070b80d48882c0085004840e4071403445040c550707a01c5820501c500059460030b1800341d654145801030902c2260595219850b20303058410032130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226457598 1250 226456348 226456379
    0x8030c040b0c0a032d0e0a0b0d09051c1b0804090905010b01030b031612150e100b06030c040b09040b040606210e0601050603040807050a0b0f0601080709 67
    0x11010100004110740a15201034050707885a80014181c030501c9203005801242404c0180c00c0104001c00e000d0013008004848107100504d52500e184102c083c2400b08096004039001882c14070340c081841007050529600c4038070076500540407103a42c0307055909004561450440c954002030010150b0b120103000207128101110305c0f4107000d40c0740c103948844890450309031410072201a5140d00540d00c40e981c2c03602035800784110407009412500b110180603041ca900604c41c068041c0340600034602806441c0859403a0400c00c81c40510614100f80d868503110980d080300c400015140640a09030742c1850010307a8813071098201114035080c213003e1000480d41084021951194030380c4d070032004507141c1e4040e0320020036054440c0024400c18428250344140c62101c40b0340c00524000707840e501214000762643c11100d090314000e0380c0380c1791380c28010a0382c0700c1d22002902070b01c281c0b07100e0700800201202c00c6114040380003020283e501c0308c00045a50704c2040e940080003412803c4244440d101074120325 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226458848 1250 226457598 226457611
    0x102070509041e030c060e1c0f0309020303040f0806090d05090f21030d0e0102090a0902070525140d030c061503060f0b04050c04030f060b010c05030c072301020601030803 75
    0x200445600344012003c442030b0400c02c50000350034141c2c503020410f10303021f80d80044001754060001c00083c00410740c4140201c4034141c0400030b0034850302050724049d5200010158006d02500d640d2a2514125186080c042c401c9507130b50300c1100005a0b8a120202d8488440c0f203041d901e551078002d80104101e0714000900003558005020980295000b0084040b0580c80c40d03150055a205d0480f0741d484030840700f0143c2390b10245d0340100858201546c403462008241ca01030100141c441106007000c3c0d1400c2402e5948909080380308001e024031020083d0694200c45400c954643c0007020340c02800000b810001e0000d0202d4000c0f00d11000088407074100401c00301c070a448030720000341d03203032100015100d09050f880d0000381e46400320b89140c2094007074550720040300c2c41b000703140c5455070351642164200340700c0140006a40c1d6005580581c41442c0801255030448216070321583c03071165040d291134407403040012004880d43c51000c10b42e4100c03406958190160080c0c02140e1940c1c50384c04541c0d1004090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226460098 1250 226458848 226458863
    0x8120304140a0f230303010e090102040f03050309030d03021809070210020d020306030613020a06080a0f0c1107050f030307080702030f0a0b1f031101051305030d0201140f06010207050904 82
    0x644114504101c2c05944500984600600c288103040c0003010000b056811041c0d8045002201e100400000c2103c1c1111603000c000c0101d541c6601003140240100c3c1c118282e400e42c090000018090000301818a0500440c1070b20b01412000e20103408911549100c160000c285c546000014a8829160342e445034a90064076491021030344160100da004440c400b003500d40c040180030780383c102000402d07072008440d034200304040450740014550b102607101d400c0400503071a0008403400b02640058802d00c3c0c1c000c4007407081200c03034480a81780d004a114003410781c1c420710000003081d1a0000644050700405406149440d4264503441c0681d80079040903a014881c0120000c0c540f00b040001e01c0145010341c1d0f10080070300701a200d10070500207414000560106c050024030115070502c10202d010b48090810a40d22041101c04c401058a80c1c0e100c181e040c0924411f49100b00e8064100205840902000b10f99540d102d0a045203040c40c165503041c0160b100320410702c20307810100d00c1c140d04076005411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 226461348 1250 226460098 226460123
    0x80706060b0f0c01050108060615210118050603010522020103090209040b160e130b031c090501031d06070305070c0618030311211003141608060108120304 68
    0x39a820960001e82042c10a15000680242000b8288030300c602428005001e44014200b0384000382620303212400400b480c24002800b0b00c00141100700d03401c010001d040d190070385580c0d01c00d50000f140340654100034015080170000b480d10314040c8101d500c0b0f09940290122000b4001c144440e08800d500e03400c1f414103a0b101c0990015030340d41002030b0302c80d0303204181d0401d461800b450301144104400040205000060305a034205075105445048000c80724240000e40403000800a031500230140390301e20070240da00100c0c1d04215401110101030710401e880600c20002000300da84244000644c20520036000040840c030240c1c407079044503411003600e00d0801c4000c2c0f13054032500c2c102c1d00300202c50242c0c50b1092042c030007015014002d00c840b041d40c0581003030821840ea000001080303000f010b4850a644140c00240c40c03ca045000c0601440e04100040380e1005200301d2a695481140210381009a2103080015100c000080c1641039038001c00181207440c62a4600702e00380c1d0005081169852403065 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 226462598 1250 226461348 226461359
    0x7080106081605030703171c0903030e010c050a05040905070521010f09050609060906030f0313050f0405070f0e0d080c0105040b01050901080c0111010209120303011a0301050a0308070606 82
    0x954406091003a020300180b400d4141110108003440d0702003806900000410004110380f02c0064201c008614100340c1e030780c3d42d002e0004658411002a45400a180caa800c500703256141e804120807011410080183c004182000d6405000748180324001a00400051044d210907801c40c075003044070b6040050800414007014140240071002243c0d0545982c0c004001b03900000003000c005202c070480410040c02c09002051030450000c003094003030000c0c0004a401c035201008400c00c000596001d890300c40310700c4801214402d20398415144140c0036a014046c551800b4420503014141075103489454011a8405039440d60507011110307401900e400301040400c1c0c0b0b9900070000e54844400010700c1c2c0c03520749807400c16940180c00c0140248942e03c0144070000c030000da07440e450042424458400200d030000a03000e445803aa90f150481e107160300003140344100102450603a003207000800c10b03107034a902c594034041c042481007541c00010202c003040401c13501002008a00c1c0140b801042c41030310786 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 226463848 1250 226462598 226462601
    0x201c050a0e060a180b2b0603230c060f040311031f0c110c2b020405010314010507020a0503040b0906070606060804033230060f0103150501031107050604050606040c181502070801 78
    0x3202c408841ca132703c6218a8800d001440018401c4908541440c2000d440d44052941405180002031040700400440503403a5030410609080341d11000c1c9145402d035112003c48041c0c5003040702280402c04e00c884281c194400815003811440c4040e1240155414205449a550b4400020305441c814010030140c00761f1207a000300b90185000742d203940190f040445006003120342c0144031004540104098000003070f408011501200c001240b02c0c0c1d20b801d01d900020700d840c42904801064585024000601d45030443e40540c425070203a15014003c0740b44d0404800f06600c00042102a40300d50444c1d0214000502c0c01707000d0200034420841000900342c0e045a588021408440040354250b00030410b052400d0040c0c011003a00a00c0c062180c01180d6010229040c1c042c0140350505403104003c010703010740340c41034810300d94100f402c50354141440d05146444c0d03202500c0c141c0c01a800c0240c9002e030302d4060f0100ca83da001449100c41c00b0580f40c801e0848540d0b070b40541c03500442c0500000020050000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 226465098 1250 226463848 226463873
    0x41e030503041a0f010314070906081617030403030f030912030b0310090b060922060606031a030a1407090c201c050a0e060a180b2b0603 60
    0xe49460307540382014140f205050360940d119102001c43d4204000c841e4809400c02411a64003018004078002d10711a00b81c1400d07410742100c04c00c00c0c80e0030400101e0000010740c2c0724101c000d00720840e605603103944144040140440003010203901c10002000028403604201e403031318041c0d140010307031f841c030655850341e50480480f081030019444245500444c54240150034208000007400c00c03040881d0750311450030314001040300d80300e07010700700020b440034005401a1007141c4000002100c141c0d201d1816800604c410302440e00001e1501e008120403030780003d800342c00280c0050041940103410341d0f0341d4030104074803010700507180034803040010641e40d41e000300c449000564852980301804c4107003503102071082c040401c000350300c060f41403030b041d00c2006401d85000d0194581242e6400318000b0a03245106149590b60f040800082c52031b60700d584c03028800c5800701c501078400717550707603039072680e0000c0385c005e00001215840041410021080b002c0303804816808504402054080e0b9944076503500468 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 226466348 1250 226465098 226465103
    0x3070e12160905060d020f0a03050d050a02061608060d060f02040b07020f0604060f0c0f0506010b0406030e120f180d0503030f010e01030c0b0d0b0a1512050c030f041e 73
    0x10900200204081e4a030141010382003042c82088685003000008095000200c0702034000c544610002c1c4070b680740e6008100145810400b1141d02c1c2040d40e000500036031201c181d410060080b8800310b442c02c3c50000546142c50119035030014651644000c005034941145c01c01c60301260395403105000c2802c140060002881440000f0b030300c4250a0050041001103800c1c0581715580803c01440f1183d04528043d60220152600c00c082c00400d2401c02030000b141400a0402d2040400020b08c07903041c0401002650364688c0d003405527022241c0343c1a61040d202600f510f60320717000d01c5510100c060500107041030710b2002541110b04400d00f000f250325500303150400e44840d0400010842d00004c89113030240106004408568298950344031018000d11901035041021000107005c0407007034076900100e400711401030804c2d080903920259089000f0b4020010070201d68503020043d0180c0c80352180500c1009803284042c503603940d101c10f925106000074401c40c0c0307070302e0000102400c01707013621000d6000e2403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 226467598 1250 226466348 226466353
    0xe0f03030601031a0a0b1b07030b1501030203070f0807051204061d0d09030f210206010509070201021810170f010f0e01050d060c02071a03010e0c0702060f03070e12 72
    0x3407201c0014292405012540f41c02101001e03070075075a0310784e01c0381141190f4041113165200c00c00c100d4007450084800b401e0101c00e11412102105109024400c10700542c0d03040d0410304145035020064080e4002240c0c40390100d030f0f00410415800b03005000c407980c4012103140071850700740c107a00102c1d00c0700e50588058a03051303a24840070701c071854201612046401003c0c000c020324102c00c03200070140c2101340030042c40c0246d040c0c2d0003000c000c5085010034241802410643c03100480d80c00080d030302c0c602481a54801c01d20b05010405c0d40c0d006208980c10400c00c1c03042c110070080c2c001c0601500c00d210602c4c04080044050207141440d00001c109800740041000220481d40b400100554501542e00400d01c0c1e180c90000410103030307032200c5248a06030f50040e0045440c286241c0140e086c440d040d80004443d0300c2c050038240d1040c4900c4000d50581c1d40171302c0302c00000d40310b16986070700500a2030002900721004000c00307200401490050342c0d00203140d28209040070800c10118035403100c004c1900d030a6a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 226468848 1250 226467598 226467601
    0x809040c020f0c040603151109120f0111160209130618030f05090105030f0603121b010f050c160606150f02010506012a0602040e0408130608070909020c010e0f0303 72
    0x2610500080304540804c07a0140035190031600d801048498072503071f590909903289400103600040e4001d0750f05521004028a0003d8541712449440d0710303d1070034401c10f0b540781110024101010038140c0c1e0503148a1f100c10300c0c0e505001d0f800e00540d0304001d4030034900342924400c1d20780001e070340703010f489400010145008074195944c82e010305107981103252482030000908c03034034401384d0713001042c0c9512820391080a07810761a00310111381040d040c2c1200803140c59000900c0c8032540c0c10b84c02400030300706804000700710201e008080d0741d08640c019100703c01c0d0360300101300c00c030012084030140f0f05505008100019400b036030385913000303a1902c007052800c001c1040f420440324001e4082c855603500c18800e0910a0b88600b070220310000315541184810200341035a00703484c09020040e819500640503108044000b800c09050801990f0801e42c00403a04050155010407450f10a80c0094001c403000c1d181c5505072424070740c1c81d00103900851400b051543d41c0341e94891810108110b0342c8424407203203014542c2ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 226470098 1250 226468848 226468873
    0x3010801140f0403020613060b03121c02030603070303200a0302061b160602160b0423030705030f0d09120914010306050d0f0302030f040312030f1a0d0809040c02 71
    0x180000034485802c0765185401c110202c0d0300400c41c96030016941600010400061608800620a1410443d0188101cac0c454803440c004580007081306400c01070744103a07030103468401c100503440103c1d41395030503400994003000028003681d600900241c4080c101114140b000e6031603454440d0509050380141d01580500810b01c0079441c0c1403000b20000e01c10341d03252201c81c422904401c007104800800e09580007a40d100300d108940d049000341c0b50312242c14400340c280703802c081044001260036030340d0b0312010522104418030000308035011154804099414601c10090001164004002e98a003040c0c031180420001045103d500070b580c035454640110107800e10584070700016044034003906240c0780039414002d0381d541900d0540d00540c03203001c040d40c0c10b000e417908904501a05200801c0e60001040200c00c01505804c0000740020316541002903482540c242401e544080c49036030196014002030310583e00340039140303000581c055019180b500b00c00720b020400700c40d0b080060000607040105808207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 226471348 1250 226470098 226470131
    0x61208070303150303020a0308070210020409090c05030601030c180b06040602010207050616051e0c0105161101060501090e06041d03040303090f03080406050d0609060e060906010810060f050d0203010801 89
    0x1107075220454410740f404d0559501035910640c051002d014884510700040e042c03031080201705811030301e0717240c250345807503544510f1070140c8002001144e031581c4c4010b0100d4207040008030507040f0b0f44c000071004070321480e112441c640c1c1d96038184515402c0380c0b02c2400c440c164903a40c00802c000c200f00e03800141d80700458200b0909108014000070180304c03c041d282d111096001c01070320030712080c0e100f2014130b0100c0b11001c1c140d01d22510045443c2c95003800e00f000102e159076455440051844c1d1100001545110720403422030f4202e0040074045040c1810501240303403030f62246a407104011340b00144009031400307903058508000141d4401030b40005418030800d60300418103c000c02600007411852421603942441a0160740901030404c90040741d2050000d901d03400c58402400c9401c410441c82e500e07044540c1200714200da01600a151100114510794410700000f0320540c103040b003c0c100d10782040000c039030f80c00c1031041c480100a418005507070f00031500d100440c02880351900014059002ca9032418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 226472598 1250 226471348 226471361
    0xf031207120c050a0e01030204030501140921031305030c060f0109060801050f040605092104032001120b0114030f042f090c0d092307080703060b04061208070303 71
    0x80c1250615059040c02c64009054810720016400e100c040c440080b00100c0085c0540d0780003800d130790300704018810400e0461018074001e4802d00c2c295078140c140342c0003034402540c9100d004100c690b0308100240340c44001c00c40800c40d0602c44c00950b403802c1c004044091800606681001d800d9442c20010450482148103920007010a10000c1c0101d250402c0401840480144040e010640307800005039004018482180301141b000c40803a5031250000d100341050b0014002290b4404081d07a0101b0122203040c0c3e49400400140d54407429000c0c4018040301034004000c14905210441560021060a240c051840b40f0040007511006140904141d0060480000031071020041130060b4061510440f80c001c0750740d1026244178480b521100e020070071900caa003c10b081c4441c075001030b45013001402118055003102c11400c00342e401e44d941c0c41c41512441d06100300c0065500891040002850b16000180e5042000b00002440c9549031b40300c80e40701841e041e0842d24007100250010801d40c01d8816030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 226473848 1250 226472598 226472627
    0x1050d11180f03010902012016031b050a0b0d0e030903030703020c0405010b030c120402010c0b07050c06330f1f02071212050c010b040e0f060a09230f031207 69
    0x20700c0054815000a4407140304081c41c018405e5087d20024408e510800009400e29042c003140a40b01380da034100942100d16200c40d06003500c880ca9000201881c014652000351003400c03404a15001c0c80c0700010b0001c1116072490341c8580401c0c04290182d540900c0508101e6010360054208140d405d81004102c607016088040c02c1d100900c20b0082c00d000301c0090b1801982410451417043d100c07030005840b508200d9100900030340c18002004000d550000180031400040c80854105807908910039000108035140f1204003520450250001034101c00741080300503024002c110178404020116400345112104242958610005101c10542c100401c0300184003004000c803504201d562100c00401c0048840401c019004c182c0c281c12007c207500c5180e0b0340b80020410400c820810300c082c0e0300c9a203080c8a1700540d009001c00201802840e02801520ba9440701d5459101001640400d40801c0c1c802c0071505588540c004603606104108024240e03070b406200702c1d616074a45035500400766400101e41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 226475098 1250 226473848 226473851
    0x10206010b1e0f0c0307150c021c1b020a03050601030b0c03071b020310140a11070c12080c07060512060616031d1305090607020f070501050d11180f0301 67
    0x19480c0d40c411582e000c0884468810560350394a15160a0004900035001000064000002d21200300680b9110410480d01c14503c01e105101c2c550b00c0a1343c0b250603041030054840b15400007905820320402c0c0d0010b03400c41443c4420615862900410805a410b030412940c5610a80061050140303040405a000d10341302201c4c0c1c50340ca024000103013803a40c4001d8011200046a20190441d40c042c040070201a1030b40c0b0381003028144840c411401c4060a59501d002e062401c0b03030300355890384d008040b0340391141c1043e01c101403a490001418414450810141c64401041c003c00c0c648082c04e02c40300e002060250745403a25001103042000d480c0f0f0025284520134030302040340708040c50540383d4440065416041140110001e203250303070203008078458040c2e0300c80c891601c280d410740590384c80107000c1c50202040f030700700d503540320f005036a50000032110b10600d81c40100d082140358420700c0201580300808030040760b6800700c1d0500b15250b8014803070002c1c031200b4448070500203040100301e80c034510104400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 226476348 1250 226475098 226475107
    0x80105010b0705150435031512150408070501091205040806062d0103060801140405010c0c0b040f060b120c1002030307090b0309030f031006030e010b0a0e1806011202010206010b 78
    0x210051034070705607842404080301d80d100038008800c01d01b245010802c00c4240641da02d1030300300800000b101869508030b105000700d20304414111000220600c086041e428030010300c0c3c070345490b82d4100ba008142e00321403a42d01ca0040f040011240e81c0e40c1c8805c01419100c1685460602d581503040035001400c01e4080d5104c0003100344001c441031940c0401070f045661907014019850700403400381c00e0941003110190309008940321181540701c0001c2c481e5000d400200020818070720102c03004844c60b400076241450380408074010450a103503080b030003480785030000340841c0d1010200307100415004c080710083d003204400170304c2c0c0c3c101a0818900200184055441c600c0e000c2805403501149001e100d40c100740100001300c82d0a803c00440c1c002d1102c664020b6264600254049102a0103004c1c850010b4207100c0e0901e070000301401500042d4070000d101c54503050a2091075803101c2001040780d056405450084820079a0900005010f00761101c1e40d240c102804d40006454080c2c107a02c0320889000030003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 226477598 1250 226476348 226476353
    0x2003070305070b07020708030f040f050901030f1203061a0c061302030d0c02011b050610120b130f1502180f03150c0c100605040b06070201080c0c0304080105010b07051504 75
    0x2044030b001c00d41c080f02c0c200e902e840340303203089140c40b15540001540380b000182e083c105840d400702500442d2014400035503960340303d070144910345200b8400103140740105880400051145468400c0c1e001c194030f03000444a540d01e2031241c5402c0410382c90f00d8140c000042ca000d83c00401c0c003025501800111001a4a26455000c0b030b0742c82043c1001e020030400304400d00411684038622132504500c1290080324161114180a40c031644107a9031016251500c001c00995292450407000343c068021100c040140d403603a143c407642c2d100c402c404848000d40b4081070000205d00340e51101102501500040e00c403289404413490ba01d030100c0c0c09500c04d91200204004a0b580044d56210041c64072804c9043d0781c48040041105004051040f4480d000e654108140a0082c0c0e0107141103410803a410322200a08000303100180c40f0f0068041e0004075507030000380540c09004010608035401800b12072400d662015840e003104c6081e000003422802c001400c01c203106041000c0001480b14107501182e6040c1035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 226478848 1250 226477598 226477607
    0x1080402010903230102070b070f0807050a05090a091a011d0f0409230105040312020304030f08190e0309090f0708040b090705120307051002040b0711190620030703 72
    0x41c8401052141c84c444d50b00080210b00320744504030409400255104e10f441d2400d09184002203030171300b00248006001c004540e10070006580070380d1050311014589250f0410483e40d90303105901341500a04c03854800102a081c0c0e2240b0070a4074803075804060040122800148081c004004040c00104c1d1010b0400265440e0803007059404002c8230000b0300400145001d0b9449080d180e00c811170f003030381c2030300e81130001c441900000e105920990743c3d980c00300c1100b09104120300054401500080c0c2c8a00c4200400d409500807a8109000301424075040ca103440000d01a58074501c01710b24603130030108640046091217104560012201c4008240c0e500d08440014600440140080c210940304070108402d088180564405007002a0912841c0301d1082e2240756a03170700800044900b40b05600750340d0400062842034038103407011040700514280032501c07000000048101e400350f0007008d5141c192000141d00d80000c00900254540118014001c0101511000d07070008814041d08100403080000758003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 226480098 1250 226478848 226478867
    0x9010b19050a0527040504050a050705090c030a05180601150305010f03020607170708270f030d0c0501060e07090f12020d080c0c030106030302010b030f0c0307030320030412020f0108040201 83
    0x50041c965082c012a9001c00b0013405400a0030f800500e00410300c410700c040407840020309070150302201c1d2240d0740d843c240254950100e80c50000c0250a001142903560b09801c403030b41084150149103070015141c8001420490700b03070712400c600350351000c0740c9280c0e6070140161401400d12000003070800f455a008a05c107486803840041c40d240c401c482c121502d400780c2c0140c540e003c0c1c1012281c6d4031918001c0c4001340d0000d284003000b410b0429210415010f103440c0c041381d2400a0b02601030500003d00110130344403000c08410881d0030b035407104808603022031480c0c0024480d00300350f03680c0c410661401c81c07402078046607170300700c503200b41c03404602000542c032a0b040c01019580d2041d22aa62142c0c100340c000d003052250000254994201100001072640c1500420880c1c0001c0b0103842d000f662070b09405546107503d90348190943c101310b008102107405101000319040020504141055030b000300c4a00f994000e40100082c20300045101c810b6042c4141c0700307003202c007080c02d00c00100d04050300064081c52030b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 226481348 1250 226480098 226480117
    0x3030406050f0d0f060f051210050a0f1a010810030b06010f0e03030a18140f090903070209190c0801080c0d02012109050c0a06080c0d06030209010b19050a05 69
    0x41c0020040d46103400e030400c48011400b094020004c0a407181804400780009100324001c2201e0880d01140c1450a20341042841030000c00a20000b007038281003001610000740f040707142c0c9a80c1c48410140746c81c540180041240d425091001143c9000009005c030b00014144d40b6811722080d0042c000542e144803c1d41e0030042c242403803901c1030303101801100c0f011400c854058142c0004555441c041c2c0c2c01802c0403240106126031010201d440b000c80c540d000d10050120b40d4843c10141c01380e101810400081c03500201c0c0c28003900e142c40005c0d0040341d59080d0960703801e4001a807100008000c10720500c82e00c44c16520170314210b5025450145220740e5414150782d618854107030940c0600031607000e102007900c4030b83c00a41c1d90300400040000ba100030310b90240191414003071102810480d1401032950008e6402644490442d610380c90001c4845401c240640004240d039440044050394800c16454020050f1100b4940e65015402c0d0313162003c840104007406200c001d11003c88080e0700711080c1c400010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 226482598 1250 226481348 226481357
    0x9050903070c090f0507030c020d0c0804081c11060103020a0e091015050a120c060c08070203060a020702011205040209060111010227100801030809060a05221a030603030406 76
    0x848082205045104030701c00200090300c1500300040749496604070340400ca000e01c8040166036207039a0280c0c05d850204402c0b90042c0c0081821404240c00740812000c0325020b03101041c14562914a0540741071140248002425034905104d80a540d201001c1c484110f80d18002e41941d502d942e0103c0c5440f44280141d032201002d1b0030005220341800c00c440810414001270a004600c43c01e4a80d20710700c041401040d002d080045008a9900c00b50140000d490b540700240e0412140350100031189004109000c81d44000c0801250016036010425a4016041d02c02d00590f503171220320000d081031400300020b1541605001c00c00c4050f980721b030440b0b0b030311403800e0030242400a030a14420380284104040c49650118404c81d4044100542050748d001c03074000c1d565044d0b2091205070a42e02e0101c00d1000400c3e81d8401c210000d943c1c20540013078020303180b05040c40707404d140384035800908034081f680341a264020a4070b4100681c0e00080c101034055008420018550f04018001c2500d9210710700a083c2481f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 226483848 1250 226482598 226482601
    0xf090b1e0a0b040222050a06020102030408040b0a02100c08010e092a0f03160303081008060c0927040b0604021206102a030206010e06132403051023010905 68
    0x15103d940454901e00980f19005003003908220440052903441d000311400f5000c42200421000e0051084030f0003140c00000e0326062524126800d4496840720703446604501032404030030300e50340c2c06010364425003410340c481e44801d6046c20507a4100f004014000e00c55684a81e0b0170f420301c03004042222008c000016610340700caa166401152400e0340c59041d0582521400500185040503444090140d070f110340da41a60603110f0031103035095504039000712002c907003082001caa4001d2540c4010b0a5800c0094900440b00142e032920707039018020310301c841c482c10010404110400000e903001d5a072240381100c04500b80882454a092000307402096140104e080030114092a8028950903030f0a080d0b04030380a980e01a090650704115070703584c80883c0035100f0600003040384a281080c142c4280e44c0508106450003040000740054000500c840103000c40e9000c43c11401103a158000001c1e60040d00204116003584208500b06d41181404014030b8952001c03032004081c201c1e0280341110b801e01801300c1c29 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226485098 1250 226483848 226483871
    0xc03080408041a03040b06040507091806030b090109060c050f09041107060204030f0b070801120204240801020705060606040f050d060b0d0309060f021516120f090b1e0a 74
    0x718851a0040c52190080c81c0c2e1020315003d6140c0114801c6200342d060262640382c15051209a0350103a80307540c0400c50a640621070712052030061407000d50360309030100340503940c3e4880c0080c0007802d5416903003d9465542410a2124a02415411345841e28056140c140a6100c001c7c45020b10811640f14503191065a803101700a0025a40e8243e0810804c56540395a484c0c520b421200c80902119407020040010f0002e600507118181211034006c6840604410f950800004104040441d01c46941c42003c408045010310b2011000d03206141c00140d661407141025450a58010100361059404010038054100070480130706c1258401d403a02400d00003145403442c090101c40480c19086a501e044100c141540460740300100e8815442c2d40340c404282c40d004a0f00c0d0781400419001d100d01e96008220405840340120b92800c1a91902400507800c08440a00780c400107070308411240e4940400e034050180042000f0340168103040788a007008800201d61422510007480c00035034a9884586240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 226486348 1250 226485098 226485113
    0x106051315030c08090c060d0e0f0615011106130809030f120d060b09031506040b03030304081306020a030e040f1d060a0501090b0a140312130806070c030c030804 71
    0x3038100351021101c1d850304440c0040c01069140100700c001951240811000f50001c10aa248004041c001e1442e0201444400e806005944103104242c0b0030b0745010401d040e03080c000304d0300074400221014404a011400141102c1c08003007403400c540c1042c020320106090780d0030b18012560340100d100c2c2d2600c1110000905041d04201c0d005035030302803131034200111102031009046241e40c11008111160f00c8003121006802814001ca0f0146d00200a01404507039444141da40400020008244000c0d4003010904580050303034201c40a120200754a001c2403c0c00d0000307005054a4030007000240240c0e1401849402038242807800380c0c1e5034400030341c0c00f2403480d08039040f030405040002601901c98030200d6038400e070845011000500d4800040342d0380d10103010310600003c2c001c11655085051540e406045ca40e00405140d1601c500d6244c407840d140c100020b0540d8a4540f03030807105580c81d0007405402c20400408200411601e100b403070b000640c100011500c02038041c50001c1059aa903c1c00303a6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 226487598 1250 226486348 226486387
    0x70512010c0c023c03150f04150e0a031d010807020316080d1802011805010509040b0f0d08040609060219060b0a0918030219020f1314040f0506060a0806010605 70
    0x1c5422213115003e41140d410b51000540240141c00301e500601c0d04a1940c0408032041e1054011111034401040108010b03a814080f40144940005610000016203604d4401141400c501044002500f00d0107101c0103800b0b0380301203000b802c00b0085482d002c50f00944034800c0204201204041c0c0c003504081c0003c0406494080c0400c00e0100040b90750544940e02e205402c1e44200e00161180302c000302c5404654014008541060319003906040d010b00400000d032034011442c5400044002030701040399586030314408164010110540c0d40d43c101503004045518a4203c102036500510400d00780321507441c0e10150311a0003034800250640e610001643c4014903500c60000305003410103d40905009002c4005214829001c6401e00c004003402d03903280360071a02c000395201e07034030190031486810115a600789030444140005464003c03ca0040c2014105480546491840760700801c20801c0c10030415421a0341220b100c0245840c102071607a84400500803902000004907180d0408408100c090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 226488848 1250 226487598 226487659
    0xb06121303030b100905100f050d0b010e091806090a08120a140108011d160b0306010507060218010914091f270b0d05030403030302130b030702070512010c0c02 70
    0x101c504d8513029100608914550141c140700e044804030034121075000b42420013500015441d101d08100101111030010640000c84030b0502c034500c6001000342d43c3e40b502c0303688101c0680b00444807076681040e000385007040082c9100307801ea10414240d4040713a030100583e03980c80070142005880d0361380d1145080140c103940d90291290b81030030001003408541034120300c1c5003103840c03288031203454005c2c10180c4d5181300881d2400d00c00010b04d0000d11810198400456120308181412407402c1425584c180407640305080c0c000c00c103011400c41c20200d40c1e0252245009065000b49040b00030b143c5000182410f00c003a15211080d444010342c0c684084c501c000e640010a2a40c0c0a0011402d0710301c1e42038203046482454803a10762400c0001d0301c41d4600380704010b000541100c020750130070b0b04541d03068000354020514481007a003402400200e294904008510401c129400380c0251464003040c411040030609501c96140d0402107240c2025900a5607044941e40440c4c941003c40c070b0140c83c2d007000140400c840b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 226490098 1250 226488848 226488859
    0x1e12060f02162a0509090f060a0207030807030203010e3c010e06010c0503030109020307020a02100e01020d1103090d0602120906010e0106020a15050417030702010605040b06121303030b 81
    0x1907024441258800520050164140c0004800c03e07984408140c60070741c1c01a140703060a12400c0c4600e0400500855003c0702e00c40c101e0340b403002c103400494500340d01110840b500710f40005a090400d81c1c0501056000026401d0540c01c41d414200e0003844000010200003281050151402c8145078801c006100707980700740484100284d1803000015468070034010940313042c030101c0c0401c02552245812040c01070700800911f00396420640c5010203036101030016411445001d242c0400340c1d90b4164800c440c0c03012503d801c0302c03861080001a040403505100321083c0030713410b500c40182101c0481203400941c4201c8940d440c025451034020003d0060313404001100ca41c0c2c00c104200c1c62000909139045c0e6191200c041d03126030340c41000700e0350750b142100c0040140d80022700070f18140205800c01070708203208918410340785c040c440c541c512541040381c80b600184e444d181c0401c040e080512811240c40300c19101c8a1500c22a45544445024040c144c07201e44062424100b090600c2503000380201c0400520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 226491348 1250 226490098 226490107
    0x60d03020c0a06091e05091602070305030f03070e090105031207150501090c020f0105370509030406140702100e1503040c05040507020f06011a0403150c02071e12060f02 74
    0x1001012500680904120841980c60300300c1c880e2901e02d050340491b0001004800369a0703403461444580c0c3c0d82c0701c1304502580305684c0003000180701480500030f040604104c06440e4900303800c2c01003075101c07204c0f201405502503200620068401040c107400c0042404200c654030003842c501401001d0740741440480040c40e0070008212101103410484108050f98200d401200c030005055088810507a50f00d5001030340c90740707000140030b080001d103041032603450000e004018401c90035400f943d0f030031a09440c0903040010280812500208240100d544200c50541000d8890b808650410244181d172400d10508484096559490074511400190302200c55a01c03030a2a00d00440007808600a01c0e1240f420310001800d440d01c001000124405a080281902d03441c10405444980c42017141d010142d0b01008048003040c4c101c0c1c0340220031000c1090014211071039400080c10075096401c0b0543c0000058452840203620210900682e040401504070020341d44c508030006203014065070800c9800440d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 226492598 1250 226491348 226491359
    0xf03071710061217031509070c141c020a03020a0605270f010c140a0c02043e04060203030703020903010204030c06170603010c1b050c0d0c08071d060d03020c0a 70
    0x50980d4000ca00c1140701d4080b04a48614144c841c0c0400c036410b4024034420850861ba074034024994540201040c00d00c034024410319118a08459408070f070310116680641c440884d02a03c3d200f454010325490310280c480300e510383d0381c001e49410203c2070141c252500c400c082604810304803918400300d0588001c030800309a8081d45d803911a4209012100e01d54030b0f04e03048045150080100e03440c010500d000403032402c01c504c031060781d01844100003643c226070344074181007400d64444079031808022180d2501e50150040e00040200d4040d42d2058034039a4024001001855000402d03290041c0f110f0a026880b000e1400c082402030269600c0607007890581200081d6054210950a030440e803039010507111a95020141030030303101402d141c480001c401040300d0340d518501e000012919807040d41030f07500d0080000001349100301c0380c000540b81c00103841001c1003603101c1003180382e0080909061144251030b50034104180f1201c01400d02d40030701c02651034042098130a12804200f003c00800074101f081c1c07aa03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 226493848 1250 226492598 226492619
    0xf0d0b120d020105010b040303050703230d1d010b090f0c070f060605010807210c050702031b09070e0108070804020402070614090d030e030a0c0215071a060f0307171006 74
    0x90780102552804001007001034480044805403505611502c2c601445640c04840c90720280c181200801c5440396405e1005011500400b000b400c0c45d00085840c0001200003040102041c201c5505e0340c1c0340c203007900c0c00350700c5003200f40d170f805065a903004102340c1d1001c034280301794800d0b540000c000700340f900000c0782080165400070066075820fa035600c00301d0391004029240d100601e02d54580420b08009203011002072500720340304188251034414140507080c0d000c86d140c0745c0003a80f04002103481103e00703402802d04a21440e4480614645000b0704480d000000c1c08121014120b10304003d0388400140a645450701110000c41d8000340c10440c541030320041c070941010940e05041d841c0240c0b000702d45064440e01507802104140000f46240c413008034803e803410701900008903048400d04100c5024001100301500b00703603000e200e10014464540d00300d0210000000c000a21130100c888a2100f5501c00066113416122007440d8260ad030420040d01390300c0d10415060700e01c881420a42c0124101509 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 226495098 1250 226493848 226493863
    0x712090306050f061f020c040e013e0313050a050c031903021209010e0a09020d06050414071812112b0609020d02040f0203060f090c0f0d0b12 62
    0x41c00301000a51900c2001882c030070320a40d00158420035070304004502a050720501100e01c40e49004070740300e207441e6402040903240c0c03600000300540d5642e04d400f060341010442d40c01060b0316007000c2c900c03a5450414119600c00010001c44001c0c18040005280d0f09034250068103080d40000c22a10080c4103850038680d118901e02400c1e000740200c4042040380e1040100c0c03c0140d99058016010158080e159040c468100c0311209040103180d2840174030700c0e241c180c2284060303c00075002582d41d2a00c20000030580754154000e41c055890030624220a8048514150704401c6501d0049000e00200c2550350f50307c04541c020747d600088038103120041003000c140d0036040c40c90540351100c2524042ca081c515000c4a00410b4a06172100039400c000a861540400d0103184010b00c8080b50889580203e03040381c801c90801c0d00071b650f00000307201442c40c06418410003003004442580f46498414030440081c0501c840d00c1c8100107004c00c200da05070782c29812a02c0014806450200c41400609856580f0364030f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 226496348 1250 226495098 226495103
    0x6030503030412260c07060e030a1806050304030804030905030d0207080c04090b130f0c1203030b040c091e15030b1023222c010e0a0b010507120903 65
    0x41460755420350f5801040aa0a442c1140114004440914050402d901e200030702404188404001c10800240644508625003408170015074079541001400350010740744082010b0f020400500c00c01c0603c0d81b01c81142d80c807070b6040c54280300b162910310f000d590301c0030603400c510b6060060750750300030750180e0004045003111160811200e08428500a10007151303e03025002e0710501903540000c0c4a0b00100d4414264140304000000c01d1100c1a12003a00400b45074000b0002d54080b51a85014135505001390920044111001c0095034100c50b4040c100005500c60403042c0b004064007107000314000c009000003052100fa42c0c0e1259244144002c2c000c0112400c0706108144c88031003844407510a00700601211f00c42080c2819410000c1921406038000b648036114078074030818100c4420f00390b060458014440102120640400c019006c80000c811200b00d2303004040900041109240e89207240340c101c4c05c0308800040701c81040c0012a07940c410340b1b5018080d00307002e05540d100030b0340c40700c000800c490 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 226497598 1250 226496348 226496363
    0x3011d0d200309010516080d0501031403210a06091b080f09030306040f06120c0305010f152309100509010509070f030c0207180608010e07181e060305030304 69
    0x10740040c04044450350a003800109901c248000c0c1280d50040d0001c2621510000d05420b00c84a95520203420303a0044240761391094480c4010004c1103450f000c00c00c10641c0d414040c60900e40c84a80c800e080f0300c001c22042c0c04814a13040480c246010070b902c100050000c0c1d22090002a005141200382c8c901030003024000038080d040005c418105c040c003424003815070440a0751450b00d90908200280410510f000c1215940300c50000780d802007508940359040c42281102540d615500f00702d42102c04030f00c070080d80d4904004080d41400302d0020400103548000d42e186091010102e030603961141898211a0440143c00078418105440c07c815812180d0860700c004050ba02e90b001d1084035141a111000441c08440043d1005400303608607064000e064811103c0e12982c034154210010402c00d121002280d8800090080c10428005e901c0e0b0307d15108001c0400f1481c29802c00b400841c1c4080781d0041c0c0c0e83c2c50602501c00b003d0743c800e030500000e4414062141c41e4590034803a40300e6000791011500c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 226498848 1250 226497598 226497617
    0x303050105030f240403050409020406030e1006080d12020706020f0c1b10120e060c09010305010503190b1807060509121501170102070f0c031406040b1503011d0d 71
    0x240c900162080050920f852801c5a26840c4c442070340391003501520440030b01205000100b02c03d8501e2000e00001c4c42199004140312400c0c9040c2802e2058a1001102d0346080c81000d00c545800020380802001551038842c1c003410b04070a02d1002405038001c02400f00d4000a161007030030b0604406001800c144405590741c1e100f04c040d0640f5003403100d001003078012140c0030b00010b10500031224900078260034030001c03d0f1798084080c504d040c01ca04076aa4090020045100c90040d40d16104007405001d042d0000e0500800228000e40044c41c20310000300540c1c02040000c3c0d80c0b012002007040380d00030480c102c49030940c49910247c021b4110f801020301441140041c0a2122800035490700c0300107940c050380304d0316420702e0365000b41d1000440b07031a90559020004440042e1000300810340e0107001d40300142a06003545001800712104000001c50384d4407001c01e11000ca102c1c86000c641101038880040041100e690129000d002c000150600b0900c40d45106140704c940480c00000e06901c40d968200342 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 226500098 1250 226498848 226498873
    0x6031203051605090f090703051e091207020105070c080a031418130605030a060e01050108150a2a030c0318080d1a1504090b103603030305010503 64
    0x101eaa0441d01c02621940c241d140030b01490003000144184000940201503d075061008524150026910080000d681d1010072100007140f0f0403100482c199491103001e1814140880c07070780c46840382c9181e030484130000b6840c2c045a018008030360f1102ea20454400080e41d8440c0d0040d240d8511060940c0494100410003a80c0714062040350354448034255903000003030501003880210b80751400a13044042d40c52034040342c15542003100c1c440444c4944000f007140d901d180c110600f50389040e40410742aa00510b8440c83e41d03180300048070f910540c80607000419030b0b843d01040400c0001c618207606031a084c804000003e0340e254000030702c84000ca8038140424814020102c401401c03401001d040100f0600c909002d40d089904140012000e40c46424075485840c800070300c110641c40180b08903180001410842030429010f50a016081140c481c20049015440503002c0f03503c0c980b90b0340380c0134010040380501c5c000e50100c040100740e00d2021640c0d61516890040c00500084c0141031203849808081d103503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 226501348 1250 226500098 226500101
    0x3020c0f120a1502040f09020306040606090b0d1814300909100510020f0601090204030c030204020a11100f1104050102030f180337121b0b040606031203 67
    0x6103007000300003002c14084a441c0c469201080804078030145401300400189101101030b00009840541401070740e07801c20b0350070002258150340c8154280511100100410b0706500207503a100e4a4080c404106c0030b404c03c4c010a0300b40c0b0340307550007801031010740d90807038002c9000034103403403d07080e056220308603042d105548036038004810710610102d0070304000100042c200842c5031604501c900c02080083da4030ac43c00250300d001e0f14401c010042e03100115451046104204e11401800d03030b418110b2400d800c646441501002e45d010190061380c000600c40c0b8046d100d03c00c04210301007101c06481007003840c3c00d1180054020034aa100102c0d0800400d90315041b50301080f1011148160025460042801d42d02d00c00f6401c1104c013541160700e5542080d4003a04c0c240051410b1341c840e0840303481400034954116403d401e400461000e1101c1c8102680b001500c02801051000640c0c18045050000b101e000d00c58020012030080c80e02e6648000c1c001004180d422902c1030f03078415091001d0b60002880c04031b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 226502598 1250 226501348 226501369
    0x7032703020f040b030708010e0c09070f050f0c0a050703061b08060603070e0a1701060e0708100e150409050c01020105010b13030209070e03030703020601051005091807030902090403020c0f 83
    0x25030000040c06820110301d01039104c1c420741580602620701903a51000a942181c3d070000c00107901c1d8006500e000400d02e000210558000715600b0b100001605003280102603009480451914600014a0025120040100c020340607400800c440c0078076164940500a0302141d40c0c028041e44480d20080e048a00443c5010301c642c9020f080d03242982eaa40d0300459050406c440e40d20782103800140e010036040d02c1282c001c7c50b4040303a8800030031607601c1c1c6082001150b400514040801c1450818449000b043e4030884045130804d41c1c0020182c1c5841c5034120b409440007814661091400c04140b0421a020420300606c0d1000d80080100c0d0383d90305c1001d88548166841ca009513840003105100500e8040b842c15000843c0385040c5d0400080040401d25583c0028030a03001350380050300401c00ea00c0c0c44c403041d100c4d1668924285040c0404c10011500340303400c580c002c1f08002d502c0c80004094901c20b0b40010712150b00249403420318205818041c0d00e070001c059a044c0240c100740d516050a08010303600d030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 226503848 1250 226502598 226502603
    0xb0712050307080c280c030318020906060f040f060c032003070f0302070b0703020c040e030a0c14011415040b06040b07030806030c030a0b04060f020301031220060106093312090807032703 82
    0x8402533030f035040410441707a11020f408100010140300201e0003c8000c5680c0000e011a0f40341c0701c10310081800d0280c440303011004914224280001d200031884400700c06d4075009584002100303a0502c0b1480c003641010390a40002a1074500030540c10705056001998001840d0b0a45d02040701401d0b12441c00e403030b4820603500c000071681081292001502407824100d19a0241e80000b44a201c40c083c40b000300d0300c0c250390380301e04074522402e10255481c052044800c06503003160400d181502d481c03c05117107030051043c040c0500901d20005210741d2000e000d400172001c00141980da18800074940b0307140000041e103041d0313a85450014400c100c8091361084130f05070798102030f400c3c4c0c0c10703a80e283c0110741403242c01c1401d40c8101b41004469089140401a85020f400030343c03500d03501c0f941845422401d013102e05010400b030003420800d6040b02e104200d1208010080381c60031841140c4c1030030400c8090880420700810340e4a0000d0303100c040c10f41c01481445202c0803014205d0b01c5000c07800120030081d0700c60001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 226505098 1250 226503848 226503859
    0x303030c0c030d18021002070812090307080a050a0b0106090506040306021c05010e01060f0e06160f05060703020a030b010c11060a11070b0712050307080c280c03031802 74
    0x1050016101402070084180c549007120300d440d031039501610544030f0440381507004410008202017140b4021880e020000440e20040086618020761a90745c0e42c490003009506000014056076941c03014001079016120300d204440080226140c151b0365694a060140d40300a030480010444500c03d800d80821600001d09442c10300f4250340702d00d0021b5026500316881840041d442c00c2c010720960080c54000c0a100c00101c000c1d43c0343c42401380100307000c40106010080801c410844641d1040b0a4900c046180c405145601d1418a050540b201e07841c040500244038400c1002515940741d0010302440c0c1480d6014026200c0001c015a804041c0f0072008044801440d00301c0b00c01c1c14400090200e0500910789045100101d160103410304082e9001000e94560010384c4009201280d5401c0032411003501c0c000703185180449000b07100000160a02e815210000b40b1681407003a4100202407086c0641815009040481005442c1410800080b004681004600043c0311081c50300301c208907802900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 226506348 1250 226505098 226505101
    0x9140f2a1b070e0f1918030201060b070c090c020106030803090604050c0109031a0a02040504060308040807330509040212060a060519050304060615020d08090c0a051c0b15130b030303 80
    0x910351035510700100b20007600800c9a0100300d4062050091403012410046c40350300b07100d0035040007400c1d0380d00c1c1d80283d034904400300b00038000900b4420605007180c004000004407002100c80481c01b50001e540094042140442440072000011488a006070320900c21190911040801510081d10780c1c4405811000304c6008640d822983ca804d5503405005054014940ba4441c0005000c60b21076800a441c059000708007440710580401500c0050003440e140c941c07401c0040c100024040c21003480a40c1d940d4a851a5050f440e4090400d5400d1440c00030700031340d140d074018100c800c03214404a40c2240310306d14074000024001c2c00340d0102ea03503000750f103115a9541c01090005680540c0b01901c100c3d0701550312140060328051880044a691070640e002d040580203000c0e00410102c8040d041803000c0c0c10006110b61b042d81c905a0900c115407043d03c085549440c400e5019107910703e4138001618900400c000c02803088548881016402c5040380e40100d580e100e0001d20003142d89444885415031700400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 226507598 1250 226506348 226506361
    0x4060203090f070f09060e10060f03020f030f04061802010912051e030a08100503191e0303050a140f04020d0c030614060a09140f2a1b070e 61
    0x2001941d005404004544041d098a000d8924000e610f034031004502882c3d0009010464160150700028840b1214000550070003102d41e144c0c11407140700d070105018141a181a0a41c0650156245201c15107001070b124607081451543c1c150f8102c5040310040c1c940f184880031045426004015280c060f96550070884c280072200780c1900103a2000d45841c800c09541c0e11101d20745540c148007891490700036507154070344103001424061b400b40001840800d0580c092007992000501c100102452015110820301c160038000b4500b4041c42c1e0141a21a80200c076405050b050f41045025250380d0b4003c01080d4107040742044410b505072016402d181c4518007240c094a00410f0140d420783c0118020fa521564030b03a0342c4e1048900c011000c0e5601e1402ca020800303e441c103988041d001b4032540b28240305101411050000230721004208490480091010035109920402095041c2034100729601c15070001b215407103020f401c9480700a03581000207040354502c1c40c02064060840700111204001511002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 226508848 1250 226507598 226507601
    0x1206080d0e100e0402031003060b0d052104030503070308090607030b0f21150709060f020c100216080105010f0b0901020d0806011b080909010603050108030a050c07080604150e070e0406 81
    0x1100d82c8400c00c810645040702507a294402180140e05004559003054074500d0110155100c40a400d07120f15640440500801c90201c1c0003454100407840c10b4914483c100411201c41c021500040c040c0c3c400421540d080680002d0403500492110040b1009076854440880c251445800c3e0241c100d22080c4007200035082c900041c000c22107002e0b1803181c8440c03c41c014680b40c0074080100b00d85001005c0140b04aa03900070440401070661f600c1c00302e04103c00d0200c0030b03541f00358008200d40610407c60003042942d20900c0000036101d40c2e44ca04001c3c3c996103019103800380001703001d5101071004007a03000400d01c2084080360407004040c3c000d000e040c00600d009441849004017040e043c043c3d148624010f6030010f1010a0b0041e10800a9070744a8491905201541034141c20940070305180c940148040c20001007074030702888441c9440c50ba0740c0d480920b06403c090569200c034500d48200c205210800280f6840703c0d203101c4942104100c0d101a00d04010343e0345030f540c4650503100c4404804075008c00d0b0113 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 226510098 1250 226508848 226508869
    0x2e030303090c170a0b06040c050301060e030c04020d020c1c02060412120203010608010608070201200708120f011d0c0702060c0a15050a0f061a0307140a1206080d0e 72
    0x140b00b400401940c0341c0420702e40c05184150b0f00500d0300150180c80030010070550543e04100b05039820090007203e40b0004d84035100600950041c811104507440c0e6580d410131000c034038501c1c0900203545031035903c180c9201a410a40300c0084502400c04148038844d5061502400c1c1c00c00d644c006d11058441e520359003180d044590302a810407910300594040351545000441c000d280039035400010f0b42c9814402007020a0140040701164101803000c4481d010100300d0480210311a991b282d0340324403d02d0100301c6032241101105510480104000c0422602c21029041341c0488102e01d6662104030241c03007101c0c030100c03440c030781200702440b02002505143c0060300e2845289011100c580b90140c80784016011a90340441c113442e100c80810201d030145001c0c0143c602d400c00c00503c45103042500071400c01940b082032000015010002072502c0e486900310042c4034280c0d0307161396999190104001c1c1040d403401903503442a03041080002e1040c00001d2400003200e00d41d40d481614000c01e80400801504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 226511348 1250 226510098 226510103
    0x327150b01020a050a030507060c1e03020313051603210207090f0e06040605010501031109010c0209040c1203090608180a1202010b0612010f120b0a020307021609052e03030309 77
    0x10f01c007180c80014000700042e049a6000342c0b100c3e500d440e00d40c03401006640030311500710100300710f60120740c191a4480104603080d1001b410050307140d81c2e640c806090b240c048000081c18038490006d550090b00e81d0044e0074001d0703030300610880d143c0100c00381500b141c02140382d1060005a122500400c851155079000755002c80c0c51000120300221100d04d61803400c40309450644025640d280100304039a0148681710311581c600d6070300707805e0070058000a4045140c41070042d0141c940040060204501da4075004040c042155007030b8004452410700805001c032a02036080070a848102055540e0f07001c140c80c0d9910f040000090101001581d51000c02c811421031010640d074035152242020740d07503180a024190344207401d84803107614003443d0750280136050f03100b4900d6100e502d5100c800304a0440006602501401e80940e42e81c503198001c03441c001c15041c040a2216103030b800851300308004d4000e68043c82c06640707551445046800741041081d034002e1034401c921044101080003a0283d04a910b0700d50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 226512598 1250 226511348 226511353
    0x4050411070f140c21010c0f02030d02030a0603060e0a061103040c2105011a011e020a020105182d012109080d180506090601030b01051c120327150b0102 67
    0x41940c0100380701040142d0345d202c045007070820000c40341400b4402c1e900c2d501040d14000c0504203845901030744a2060f1030321100d20b160004002a2840d5854000100469211108008807205100c04a80ba050301030412075005007080c08a4140311802c0c415a40100e80101007400010315220224001902000130a6182207044054201254003032142000c00302254001c1009980580001841490200101d015000c1942000110550f0000741c1c07030302040e4207091890b41c40e404100804081e08143e104150700c64101140810482102c100e5201031144811034411007552034001500d0b0890306120100d50b0140c0300748001500d041c107030040101c05001c1c00d0305928082c0e072000c100e82a04c035008226417001000c8039800d42008010820030750701c211400b014242b03550442e501d02030041d80611a480c403521a210110341c82030415100003010035402200c803441032180e000b01801600b0350300131403c0325040041000080c00c41e80280491000d5001401c203852205105040c030041909401c17860451 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 226513848 1250 226512598 226512613
    0x5070f0203161403070e0105040506130f0204050f0603040f1e2001020706170415020d15080c0a030302060406020a0306030c080601261504030e1504050411070f14 71
    0x50701c00b480040618004100e900d2403850401c01588191000c044a49000c0e03482100c0070800d010490380c800c0e041d95401c580c0420b003074903040c0000b5002d0807091243d00784540b4021000701401c54590041c0308695090782d4400490f81c844040120500044502a100229007005000021407041414000d8004d089110061000548030039144c020101e070304101107100d0155a0b8019a01004a01c00030003561402898840070031860340150040500021b00c0818003440303094008600c1d4058800c851410b100411089203148400c5948416600c500c400c180203150008080e4101070850a054a0305900100346540340d95440b0300080d07011074085030416595000100029902c21821001050364400030a41ca504014488221166004c5083c03511820310904440340c41d0040b0fa240c1b51550900790802030b507034440c103080d109410607464055200c0024514480c00c1d0803603401420071303074005039010030583c40a100540520b10500801500070740320354031001c0c00100780c102c0b5043c14011074419900c02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 226515098 1250 226513848 226513853
    0x105010f020a060b1c0b01050f0f0d110a0e13030e0111031c0b120f0d0206131511030c0717040308041a0910050a0f080609010b090d080703080415150605070f 69
    0x207643c2c41c2d10f41140c103c01c1500040088e8600001c0482000701c08441800000340d900d00019102e85016100504a200307258000b45a030380d604010100401041c00303112050324040c0300703550b80c0c9082100206d0119021080c20740840d441030480051503090070004610307140e940481c01c0c21002c01140a02d0a007074482034150456103643312400226405030004040710300c5840b5805050040c54024213045600c403800300200703444034044d65900c03d9040303103c2019000540c2c18a00241883c00000e4034400c00000501220600b04030050601c9070089885048007150540e05010328421444003810980f4103100506c50314002e4255020a844034540e003618142c04c0002083c070310801c00084001141020445003e070310b820684109604541d4545410740c4d2600c41c0010b492040b0600450b605100c001c1050034240e1280941103400a8000310200c0c4c41707262514004200680c02c9a04507044102510070002c41200c5e4000c0c501d1001c40c1720b80742c00109007071145c201d8607a004144243c54a18074019414003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 226516348 1250 226515098 226515139
    0x602091002070e01080a0305030f1909050d0320250501050a020315060c1c14040b0d1803020a0b040303091407090b120c0d050a02060406030e060105010f020a060b 71
    0x658080d50050031441e407501440b1590b2030416440501d1542120503002c00090340102120741c84480700d0366140040d21001c010002400718400c508070410b2800389180140940055410f0740c101c1295014000309400f25000c04030440342a50000f0380c0d00d018000e030000c2c004a510324187d5502805d00c0c4214030607803521224290368050319010302c50355000040c040c100f40c00c200084038030031055411a28203031a40001950390342140036003c00354020a142d00c0f284030b1080220b0301c01c0100d0b03034801a8545440b00448052640000101c1034181e141242c42c00b44441d90354052404240c061b005010750710f6503138a452018180081080302055940ca101c00c001a80e03803031548080d60754032401080b143e030030540140215401e11422501c02c070b03e01e00359106400d2000400c0c1d00c0c90041516543d1154043d450401d29000d07840c4002075001601040c046001d036070562010f41c2e514030340800c070b84090340da4400644d1001c0c000704504006070230a07a034440200d1400d4000501556015043e2004120003540351603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 226517598 1250 226516348 226516369
    0xa050d02091e190b0d0b040f081902010e0c030604150c02160b09010206061e060d0603080f0717160b07020a060606030204081005010803040303110a06140609100b0301050409060209 79
    0x200c3d5681074002801007150144030703510740e00c4415591072140d002e49868140c2c02d40740051005100340c481c5480801000341020942e03000b00110150038901034a8a90003070b000c3e0810110401c1941300d034610310301c003c0c90001202802243c000e000209118140c2d0810005441000740400940c8a1110701c100c0d0394104c00e22100080407071121480e20380301810700090134030304094003c903ca2480b0990041d140100191032089070f000403940c1690354912116054040c001c03a510283c10b0807400300d50750808420580040011070310881e4000c84000034603200810038010b8055580100c01c41382d00010000394002c8400340c002c00b141c012100c036035400c0d40d80c00f800da45603500460002a00840c040090400030450202d084004038810305c4150706101d003c551303900603484090b04002220b5048000610f043c40110200f0750804414031103028402240305481c42c0560f5000d010303150b000001007146200300701039026140c410201c02d1469103020104405070081e242d0560b50654200002c948699805c0c281c0d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 226518848 1250 226517598 226517611
    0x303140f0f0a0b03030406030c030908071a010f080606120a0203061609052202090604031505180109020108010312090509010f060810080d0302030c040510020c03010b0a050d02091e 79
    0x3000500e4a815050701880780600070064050500e07600100ca641c010050380c00f6941245400500000340318821406820541400783c41c0d602d000602205100540e20440b40c4090920003040f256641c598000005607840d00c00c2045a0b00300e407006c22503604c1d0424040c4031b1300103180308070703001d01036241c0000b030611200342c581a4000851310301c2c283c500c07601310484000621303048840541c000e40d1103403507441c1d6400710303a10300d4405540001c11a0050744c850003614007035908079400d0781f81104000c82d50402840191900c2803400040d6540204036001405184e1f1002c3d810394501065074615603c1d0030b488403512a840080c00320041c00231031652100c0b100c4600801c400102d90710030510341840034201917000760020741d01c04076203141449000b40000f4423050300d5443e8580103a4903960041c1024840c00740382c01459000c281e10b002c07210314550003d05110305070f070114001c02813021010100450010940328607034008040c5d21a81025160050003603920205042d920004096500c0e6046a0084211034a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 226520098 1250 226518848 226518871
    0xc020109021f05120703140702030a020654060f0c030903120c1902010c030c03020c070521071518031e03020c0405010b042408060607030314 62
    0x80c5015460702e86030340c2440700c81000110060307000714900180180310f9100f4404d101032040020540940c86640281c400c8182c2c0303588200c0608201c00c00940741da00c9602c0403801841404003084845128035103243c450b800043c00b480039413102d0150310b0001440301c1c07803103c100c0c40440b0309d0400056250801d821030709a080c028000b030b490b00c0c00c1d080d40c80032005400180381a8041c0200500960004100c2c5c0510b00300040340c902c1641e0b006400c0800f4030403e0080001c040881116400302501500020034004040e20180301a6404c20002c038104d000b441400001a80101e00401031402d00d00014000038031213440b40344c017091507400864074284456100072150503103001100003960303100c49140300c0c40b01d8562604016a00c5c41e00c404081842c0040c0c0c1800c924401c10002c810507008001c641d910560240c000d003c80d42c3e503031042001d107030410302c6100b100c01c1c07110040300681004440e07100090509900d4058258949605112880e004204200e05059450122403041d00c542080700c1e1080c000740c0c11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 226521348 1250 226520098 226520111
    0x933041205070e0108060f090c0a060302030915061e1302070c050306070309050601151e050309100b1e0a0308070b040311010e07030206130b040807060e030d0e010309060905010c0201 80
    0x3006450806164480c401c0000c9083c010301c0036410214900f0b8006104040c45080c40d101e00c81c00700e06249402c0c004980c00316003801c1c0003400d150903030099845114164141c45111401c03416015414500b141c80f0b661084403141428441019900d07034030340f10103029000c80e00140c038844c0e040c000c80c0d00501c004c0e42c4401101004000e03d00d0100140d90b40b00c0400d00c1c0900c184505a0307110b07a5112010301a070643c2c1d1031200b08104a0502c5448840c02c600304031200e031340d100c3c4000140509240e00688a086140c015481032800c2b880460117105c22241e405014240060309181076101c1c84804200c46c103610645003400000486d90000141084602410000740c0380d0a103440d003d00844158030320003800c0c1e4108014440020004108182103c2d010340c2c03116030700d103400301003200300c002c654001e00c444c02000301e0041600724000134541e0640e119030320341803440e101120406079500c0300410444c00040d00c01c02e075203e00e540300350090500d20744111004500100ea6907075250a4a21407160300340140c0d03640d41d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 226522598 1250 226521348 226521353
    0xe01030c03060f121b0b07020609041e0903030501050f01020615030102190201020316080606180f060c0114010b03091906090c090b0906120a06050613050c07060507030209330412 78
    0x145c00100004031030340840d000c1d074980000d03003545004001c1d001c1c0c45000b01089546698449800c0083d2640b0904444902e140260910000401a00d0429400245040300102e014180a80440c540181c160006c00d11607549842d9603400c9100002001d4041d5000c0c00040d0b081101945c520f00c00c60856000980c03240780070885500040a20100c3d01c04008102003403046c2d5803103407422290595484180811b40d00d4006c0080380482207001160351300039030001401c18200b078040d171001c0f4616950b500ea410850340d031040305140c140402c0c4e80070178982d00602c441e401c00d40070004007000e40e41d10610000c100b907045500c0d0b40c0032034000d9600c50491107886140d041c809150101d5200e5111804440710040e031001442e8640d40c8014010b0010b001d176a460f00410002d54891480c4400148100d0701032040d840c3c89001d90342c0940101d13034110b440d5030510000c2551940030b402520000b10001d0104010141c15043c0d038114001c40f103200341c40031860b425826402d690000b0080001c1c004a00b824400060b803031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 226523848 1250 226522598 226522613
    0x3080a08090d030507050f030403021513020307090e0c0d0f060c0906020f07080727062603091806011106010806060a05030708070611100212070e100e01030c03060f12 73
    0x2c1c507280401d403801c07040000d425046420354001c10b458010403512a41c840c40c00781e141003d4048925a122041020000c003e020040350800607842542911485a907458240d0300303035015485442e450303400000c40c10803141050b40b041c1818034014807624400010750344136142120340c0b064007000002c080c140c3c14401c03641c0400c00400e0300340c0704100a04209190040c51512001140165102c1c0c2101c0780440072003000e03142c00045c03807088020f020440655503d54000e010300211403845204e000b0180e00c50000030300441519512030002e060b0b0210002c5580c0240c1d43d8960081000d0b050101e042c04418461398100150750290041794000c2c001800e003842004900070003540101d200e9030240c01c05100480740410501c01300d96050400001c0708501e100424142640c02404461491010500002017240f4404081c014507480d1500d190310540318040c46284040003c100006c03542d0048541101c0d44641e01c070ad00c840180f4600095036540f502555082103006505c0781c1c04144810210900f03001d002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 226525098 1250 226523848 226523863
    0x605070306052b0809130e030d060e04051b0d0b07020c15070305040b0d06080d0c11040501060f110304080d090e0705040609170a170304050106091109091003080a0809 73
    0x50342441d454401c2041c07810815483c0000502c94400450b00c3da50945400c0c0c218504026008400d100d4208448a605e5883e00200d40d00d46581d4206840000c4144480050a0080350080003600c1c0c0504405110000701074034410454206074cc030200d140201e4501c0021030300541790f0b90301600d441040501001210a034503045059440f4081140100094005080342e04550019a14689804d40c0702405401440281c3c0300032814000c004c070032010f1a40c01454210018400c07103d0722418880c0c4414482210740900030790707022810071010114640e024401081420362040222131a0075103400320207003401d00b0380c864400800c01348001030040c81e140c0140f09512030348a19040c4d003002d10300440107046045510450304202e14511006424070f00c04d0040b416036035007010340425140c0d9030503600c41055100f16070a5406528040c804500403c5900414030f51207001984142032800e100104620040c0c080c00fa07101c04000000d000000070400b00c050401010340e6182c0341e80ca8a00f02544a0031f0205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 226526348 1250 226525098 226525129
    0x40b010e060d240305030a0908010b1507020a0503030f071707020a260d050d200901030b03010902040606020c0a060905010807050c0f0a0c140105030c03010b030c0403060507030605 79
    0x4a440e410140e2140c1003902c007460302030080452065100e090200d00f07500b8520a4142502d450b82c000300034844000010186c2860599415401c169a01c001c83c2c201c541d0010740c59449200340c03003131f1010300c4044009454000d00050103a020203588000003440d59204220440c4100800f1032484c0a120000d5441800e0300e0100c82d4603850440281c0c00100030000a029080c0c56440c0d140703040c0d0f05a412200b096413010b030001c0445940045000d406054ad0304000c440500301804d042e4850300311000c8081800720f0009074550301d4100b01ca804010f5020303000360805642c041d0f60b11482078000d0b9842d4000d080040c0840d170060131502d03505000340016003c4540181d014000c010a0801c1180d80c00101590701c4101d030319115442e410700c02990b41c02c140011036003040b0b034843c0f0071483c17040c4110701c10000e080300c0a00091b403100050b41c00c01034600d07010480740205007900502c010440324200710001e40e400000b40d01c14600d402d4507a611081210310540e9072000107541d90105100f503041154004400a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 226527598 1250 226526348 226526357
    0x11010306090902060d2a20160501110c060315090f07050f0306060702040e0d081008031b070503060a050907050108040b04060b0a08030403060f0c11120c101109040b01 73
    0x2c6280c01144803841502070001589076101000400d40e0b40300c5c03d4a01c1d0f5640c1c40c0d4040d0015000da4513008000000c0c0d4003a820504080f0072203010031002c00110b000030381e0300e4502898107039441d003001510480c1450b920380c2d580b80600c584a2006550780d40003584a0076940202c820714144080c02d0010030300740148070300860544881800080d03908601034444a410000300ca0359269221000b0801da400b441030001d400500303200091101441c04100701011903803d45c0c4842c9503686101c1250034030040e0b07100700200c1d90420810050b000c024518002800031204040b1000c0e907a0300d9001c40d2402e00b0813114114201d039648117005500d4800d00a01009010920f00401c05d400d01d601d641400c100e007c1c100500d030341d54030480000984c440d551f00000030700b0120140e070b80342d9969040520140001c010300b007090502d42a4201d0038076004609240d40e009070000140558002c1e481540e4103640601410480b510806a602d18641181e000761001004200d48080c1c40f281c0f03100c284416200c031100c155040c007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 226528848 1250 226527598 226527611
    0x2010e010c050a0c0b0c0d020d09020405150a05012006090709110a090506030a110c010903080f071b080d0f0e0d080f0a020a09120f0b0c03010503060406271101030609 73
    0x540c01139441040c281c0015000209448411801d12140704803281a0001d81c0041030200b0b801d501030b84a54101c80c0269000e1040d81d64603412104500c00303007440b10790300056502c02440f00754420841d0b0742c403402680210b201c040304802d4806190004c1216448101e82c0003080034440c1002d18001c9060381501c45107451704082c86010007802c001c9050080310b00403130010001592015050300035540800d109203481e030790381160390b100d01d02030840300105070003080060380480c1e01007105e50700f03491046c502c0d944c1d00381c10b5042801c440e0007c1d581e01b190686401205103c085030020041c480c04070404000c02001074168400c3c0c40305420702545d00c9901c420320429108101e00b8023401d09055601c58203040006a54460380d88082e611001d864011a88400700300105008000c0f01d040c0c82c0720300c6030062509c00001d96400769107403881d21003401015010b4000402140020b601c0303802040b0303120300e000352804416074100c42c5040013510104054070056024100a01c00356050310903100517010070303002803102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 226530098 1250 226528848 226528867
    0xc1101050c0306090c1204050c0a0f03020f0411070c0b090a170a15091502040918030f0c0f0503030a051f1a070204060b0f0705010501150f0c1106040602010e010c05 72
    0x34040284200e0040001c04001034840d00410304941c0b1b4050b4821074191103080030308081c1e03680d400314080f20b4040c103043c8102040b002d05146403c1c00701c1e40d000305005c80041240d401c0c04003a04400044820204051140e0302c006600426154043d05801b0062925068000300b00013207200d25500c80302070a041c0c461070881c803100101c2c1103201550082986ca0304031903055041001009801c8010340301c2c03035203140703000c41c0e201a5400610440313541703c03c14004201e9401c00e8040665554000a02042800d80341307103107075406210301c0c405280c01000510741d217669686446045500031140d03540e18070750354400c00c1001100800070110080a0021000b8034a040041d4901c504200140e00710041c900421520115640d940102d800303080e610141c240c44403121501d0b80c44e15041040300311140e501704000070a444440541820101e100381c1e5600c0c01c40b02c3c0801040d503004a440d501990031000340d2210112540700e00008100600c4207900000758000c083c0051401c540d0402414000c010f81045407030345 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 226531348 1250 226530098 226530121
    0x30903060a06031e0c0911031b090a030b060d0b07180801050610050c070503030c0327060403060203181b010914010c120c0f061a01030b09130204021c0c110105 70
    0x40e0401303503c03440c450032022800d01c284040001d6200e0264241414007803601c81c0308607000340d4050201c0302440416074401080714515400741c20b5102e50440c0f4048000c10104402e171030801c0d0446001740115036050516154080460400c458130004180c401d005841d044440c2c1504000800414000f082036040c071000162080c8a980120802c0110220305c01d80346042c10b109041c02040000c0071a99200000004247c60b900a100c100b0000c81c100f06e000030640f0b048040b0214440f00c000c0c0301030728050450b624a0025000940021040c6001761480781101008000c501d0044003015000ca0303c22001000060040906800081c110904001000c026980040fa03640070703588d1010b1200100040c202d800c40b0341c0c42481101404050121a0031030500185903c6013080640442c0710451060f90200190706490028503025080000d940010742042008021a400c852008001521700900840c0110042c2d201c41500c07060f040c6d451000900141d00015550b200d0f261f81c0000344103a16108008030b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 226532598 1250 226531348 226531373
    0x7021819020c07080a030804020108090c0102060a0e1606030f0605060405030a062d0f060501020c011d010c080705030408060f0c030105040c121d0d090b0904020a051308030903060a0603 81
    0x1641c010501415110090000002400000045032400748070f0b41001041d554054a00b81c0c0455440d8000c030b031241401203800f580014040c1c00808140d2034000344800140903400b8070301014010240c803420303100c0585800000424007640c003c51110252900c42c4d0440e9440d522151080c83c04000400854401142c0ba11603107800c008000741445449810340c40c40489200c4130030410b10340d492071850f401c82c0da03404aa1f01c2010120704200381500e95006907070382c50032200e419002c42d84244d101c451903400c05035804486c0030b040c0743c0702c2e405410303d6981750b20a030002c0714215960f03040400d05000740b0001b00b08041d0700118023802500c490419000d031210768801801140d0045445101e004112401400014480f12901c2c1c010000204030031000ba64494110801c50014005d503994080d030144154103140994001a101d01c0c0341041e9001000001e501a803040d0f001d00000344076406240004c40b208100500500028698880c90b00c400c1600b000750017403840c030026140a400f80045400002e00f071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 226533848 1250 226532598 226532641
    0x1020102090310050c0c0303010b07120e010813060f02070503071a0613020c03040302120d181802130b0406020a050c04141311090a0b010206010503060421170c070218 73
    0x281520740c1c01c1c2d81d520511610031b9040007031000000000c0c41c1c0d2008401403052074010501905403d5414408480034030640303035480e000649500c080350800548800a0b80131512a030400a40f0040c4e01584034280d801c2090240d503a9040817840105000400241c021020007060031096989005000940e01040c20b4040a160a5010420b0015100c0c20001c4401a640082041a0341c6688030300c10307941c07412942c80500008040d44040410300d000b02e075103c41940c5030403505540340980400e0500080d00b04103090700c10341803074a000007020085840180060682540680314200e040d09007940703003159840080d0300039440c00340381d5182895007071140307500241203030310743c441803107190900b0642e076910f051034280e00c42500024003102c509540d01100b1511002c0c5c0958500760380e940200368440c00d04842c05411100c665150810a0b00e501d948070b8003d07086420201c0c0344070380350071211003404003c46140c60240c10000c0c02405600e04281c0110703003542c00000700000780c41e0040032040510001a002c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 226535098 1250 226533848 226533851
    0x617071d040f030509190311090702030d02070c0528080a030e090a02130b041d090304062102030114040b0f0a090c0318060203070f0513031101170a05040c0501020102090310 76
    0x80003014404c00841c3c00030200200500c4400e0f0000c15443d200d01040d10007150050a0324403001300c0c03410178400161181d80f00b50003035402c001d0085000d10182d44010403c031240480c252020503d907031441a01c9212101d14049031800e203049030280c46600140750010300d103651100d10001c00003a231086880e820110280d0306160a030315941441e2001c6e02445610089252400e070300400ca02e0080030243c0301302d0b62440070316403034004d0503000d903010204140d0319144030390801c0000f80706103401512189800d07401d800a410740c01c078030000c0c1c08040f030700280c10440d08110b032603800e2010303440c00d4011656007010071104145030b00840c100083c05d58800740714032a82140c4640d4a0310072a4002d41c00300c0c11402c3ca00c000100d00300042d02c2c1c444020345c0f00311200c1c8040352180a10800003440ac20644202c4800440901a803074111b448000480680441240c10008081105071051100855990248241038000b1815042900d014082444a6007140341168418840386e181039070001003054050703041810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 226536348 1250 226535098 226535123
    0x4050a020d11060c0109051b090c070f0203030307030603050c01050c0307060c020106080312160504080a031202300105031b0d14030403121b0c0509090f010617071d04 73
    0x50880c00269410305550f4020000706043d60114010b410241c41188a0000c0c0d950f001034900312600541c00c11b0912a40004a4000042080d9214802025440c0c02181078104403000f550020b0f181d58000c48100000079150760040080083c1001303e05c50522003428594104000c7c0d101565580c09079400161a1b2501d6190442840c1c2c004e500003006010b404041d030b0781c0c0300707464600d94210f20402d440400415880d0541301f2030340c603c20b109a4054910640242490440c1c5850844031201c412195820596003003200c1c03095030031003140100c400240c0180040ca081515a10b041154905900c02c038041d400081c0340c2e0400e16000f9106458600080714802c06181c03181c10030017164070703501c00300c0e8465120002d0044244421081c134448a4030083d0b44550340048000820049039507010001043c0079030b030b00c805000518081c031311194001081802c41d03648150102501e400e60703150794051348001c802a07801c40702055007403140e803000d4150170768541c5100040e01c0c18041c2006c00100054290610000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 226537598 1250 226536348 226536353
    0x90105010303053001060c110301090309030b0a02040e1315050402090601180504050702060108060a090302060c0306060904060b040911070b041e0803071206080c0f0f0411070605041a04050a020d 85
    0xc040b0140007581c0c001c20704650703102c02d80030340041c47c00c00e81a0341e2072010000441c0503190500900300c1da07540c166581030009265030f0303907040b0602001e040c42007055000e00011610b5401101a02d205410049001410f1f4000741442e10405070807006841000303043c40100030241e1074401e07820307822402c04c5c68141940e542c90301c040780400c00690030040c0d01605207130134412500d5000514034143c40803001501c84a0312451808011a103135010010050b820030000036806403003c102660f0b105030003410542c034000802d000507040314107507000f0204003600400c0c1840000250700c40d000785100d5aa009500e00416603c911035140d4000344001c0c196588506d40c91420080307010503600096001d0690340d10390134107180c080c1000e400c00ca4010700052400d9000100c07650001600750080f0b1004d841802c2c200080000d00c0742c85560070301001d412a8650900142244d0184020007200e0b0140c0000601400d051078070f400a0300d019000c80c262481c0b248184404245c0101e030641071140d049850b5040440300d071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 226538848 1250 226537598 226537657
    0x62703010b040e06180a0c06030b061b070305120408030f03090c1f020c0103110306131b0e0f03060402061209070302040e210f1b01020909010b0d0509010501030305 72
    0x19005190090308000c6181030322480004d0040c01001200ca1400340d41c0700504001d43c3d00c500c000d50292000002d1141007000301e010798058810f203400600860300c4e1140d00c13000e00c691b80c10101107a114540c4607060400034041c040c00100300c185044052240b0303080c0303070101c56a9240640c08441c841d020f030000c041401c0760420000c0c0550101c01920580796220001032110354a850700c2480d50250042c070881c1400c030340c440d20429044001e9158240c0c1540c0765030091104c0c0701031035501690015900e400840807804041d010021410140d6502c020486d403007014410003040d540328813800f030f501c0042804010b0741c0381c00640320100b45400030020643d030f507540745a01c2c02025038400f9400030718249070a042e492002c02c0c0c0d1902c0c110204185400303032012000c02820b5110304603200d42c00300c2d011b006101c2d440030622054000022440005410b0007000c0c400910512020b138000410b0003c0007a070740c0d102002e03a002c1e40c1d40c040c00d054020880c03585181c4016000e0302c6070080c60f280c1e4020f41071485e990a01ca4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226540098 1250 226538848 226538861
    0xf06130e07170604030906050909070309030c02061306031a09161b1a07020d081501030f020415021603050a0201051b1b1e030a06050405030f07060c090506270301 71
    0x5050140c1d112102c4142544450040d03034203030000340e11800082a424090070881d00d0900c0064481a29903a402d84120010100701100314100040410f0301800751b5543d10203481e8001c08050044031003407400c44040c0c105e51810007031096019120101442940e40c05000f80c0d40842038024011125001c008102c0d040c0a4085040210414003c1c1090178061210304850981c600d4011155040d103034800241c1c1d44a100c10744500016901c8000160700d40b81680700341c0c0c90003106050104402607110110341c140d0300305401a460850f0303008400001c096040042d500c980102c1d20350701c00d00754219212180c98500021b0041d040c01800030305000d00c000f0503040740005550580540e4200d24450028283c10340a821410340b050000d200340c11400009200781c0b186520000700100307805515617035000040c00c3d0040082c1c58600043c0078a9545100d44030041220390303ca00c02c00070780b081244c440940491802e4000c2c5001da40c050050043c90354040c406450030000501803400c00c8034071900024050800d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226541348 1250 226540098 226540109
    0xa11030a020102030f0a15030201120e012a0801031110051b0706261803040302090702160902090f12030c1902040c03020702060f13030c0b030f0f06130e07 68
    0x400281403032055410b6010f503014213220020b461454891000e1801030318080310362101d00082c4244d00700019800383d51240e02940c035404022a00304110441d4508580d441d2a015180c464002030820700790380c5d190180b4041e2038850600414130b5045031510340c03000041030005405046080d40e40e0340742070301406c15580c0451001d580c00410314040020b0700d0b10350002d4407544000c145103507000740c600711a804460755800c00504104c0c8440da100c42100b040100e010603000c840b8001040040b0158a07100202481038189800502c904070200c07000945c0b9500380d502019810b803050054194558032000410010740c8221110140c0704948001c0038150f204040c24590b803481a16140d003044046d03a0000d046650088400b04550054110164180c0c0b0403010000c0d800324041103110b00301d01014010740b5000b0281e922807036816440390740e105202c040d560008078100d100401046142c03403103440b0459020100c100e810140c1e003050030105441052140030915459100d0505800304481009180c00504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226542598 1250 226541348 226541353
    0x1c020a0f1b06030b03060108030a0f05070c03020d0f0b0a150501050c1005090c1306120305031308030103081801030603030e150f03130b01081f180203010906060f05010c080f0a11 78
    0x2d5a80e030000e0002d08000119500901030b03200005012074000c802d64403a4640381d200d51340c150503034800440e9070b58401001181d140407524030100140e21918807082016204a00d02048142c5600f894034a8903c01850080914103040304400d040702620780800468200b82032007612501c035400402e040c140c1d060aa014070a1418080007600700002483c42282c42054401200802545880c1401c2e42c2d454050340000c07640400a02e000240300700d00440c0e119000040d040e040c2e68450343c07098400c0c4e10a80c0301740c0d023106020413602c41c149100d03400c00094180908080080c1803031590040c020452030320600e44070f580c01b00d0424808100c20000c030744003003041c1d021442d541d28082148502410f041d48090b201103180e0f2001080d422000190584902d020040d181620000a205c2e5009060742c024030a5840080442c60001601c090044c640c3d00c40c403a00d00403503018104049120036243c2940120b041143c0d441c040070210303120300210f5800030310150065550b584e11500564240c0303284521032903e072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226543848 1250 226542598 226542653
    0x4170337050702011506030213060c03050d290d05060406020a021615090b27010912030e03060a0b01080c071406010b030702100516030903090b0f0306031c020a0f 71
    0x1250f040d800801c2c01d20554041c00c4480d030b2203c46c04c0381240602205400e050703107a41c00c20702403540507a04d0900003070300c640361040c03503c1003d64000c000c0d600344880310001030f4aa40e03081c1c0c0110f44051031300c800440e02581e26408a807032640380c680c0d4804026001808960380010220017992003840300d101c41ca0400302c19000b00941e00c0d2030b000300301c0c064460080009a8514800b00740185004104c58031540102d8801584081000201c01c01c0044642d1150510000b4140025040507000d106482e680c020b4803140c581804140c20b050808400403c0c5102c0c16142503440d81c078903031b0001440c94200745000503aa403905c42c1860b140788107005000f030701100362142000000303040400500651144c00c141d402d4800c1ca0292425031000d03101c0a0314407038084040707610a5602c907840b96111034903403400392628150a0383d0791404060980c1c488842020a10000000c20000781420848039032140754807a103d040980307841e0380080d00c0d100800d20085c5208001e0600105204440e0326031030b400c8003420a02d5120 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226545098 1250 226543848 226543861
    0x307050f030a030e121504380601030204090e060a0e01020f160516032108010311042408070303021b01170702070503120c010b09010623040b0c01050417033705 70
    0x10f0800844e81180c20f02d2100c80510f418048910807034024450015100b891205199230b09403103401d000b0081410158203200015840e0399501075100400c08440241249007092044d400c10384560719540d05031a170042102452000d1903100301c90366070b4110400d5140100162034843d0070400401071550040c400c80d0310202c00e004292010440d40301c030541c030401461b1440131040d02d861100b444017401202e4415503811103403c054010407010600320111001d100000303010110440f695803c880d5041e80088410300804d501001003440c1824251b04013070074845243c0000300000312040d0381d034411144603008240c0b0780c1c5c001c000000c05410014155403100307200780b0303803014a500310a031508802d60030044040c9160800c102c0b024180c400541d521201030007203100e007200e031000c0380e0842d60300000104000508141000064400140040c1c0003048070309280c01c25035003000c0070500340503684d00f0800c00c2c0803188043c40044101c0071200c1c850300780030801c003101d40c200f0103810401000000f41400e042000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226546348 1250 226545098 226545133
    0x40e011409160e01030903030e01110307030f140103062a3b040515090414010b0901060509040b060708070f120201140a050c130807050307050f030a030e12 68
    0x186000d0300c40c0581603582e068420561100516584082070005100f0340b650b5100350030a12180d4040e0601040550301103602500b1140305103403000b0040d40101c00d2005583d85805082403000480409200102c00d6840340185601c040c0b00c001c00d0266500e0308044c031031000503d10101c0605061400c4040014248040c0101c0148460050250f0910000d5900b42d10502020019454150a0802d03484110802e00c0700405e03002c2c082e0000d81110088240e2642c2e40c010000c1d100c0d92040d0983d841e01c06102d24124255441c0000b001c0c410a4554014008076600a042d01c0c2d101c20201e0300031035500c2c03d06003c141e6070700c261000035014480000d0b0100c03d0041046034074413060301ca4803407501c049603000c03401c074225442000c1d02078400400c480490030841003608080d41004103518080d1405c0b140460960b540c5076150302c00d00040d040b24404010300d207001e001c040003d00e01695901c0e120700004000070746807091101c009007070040c40e2103441030715103c816102c2514a0042c04a901505270b9407503100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226547598 1250 226546348 226546379
    0x4050906270c03010f0b0408030706110d020c0313050913240504030c0210080105130905030910090f1505040b0a0306170c0a0b090303091e040c260403050405040f02040e01 75
    0x71040f174500c0000036600e0310007048034221256a0041d60801c1101da540c10050640d104180031411006e1050020021417880141000540748000b50b660754000e4001498030103159100700c2c401d446460810510301c0e090541c0a00c17041d402800c58400f000030b220024203420031619000200b51801003004201508203071110742441c000c80e0400003160300c0c8202110341e50001d020303441c2c00c001c09000201190107540c000100c1d09100300242d0f810080c0040c007140d0454030141d000310004465100800850360100030f094050140c0c14020985641184070140207807046100713080c22a60300060034035074940701e40d00c8440034206600300100c0b80300e020174180d999440c103040071512800500c5800200c8024074011a2081c80c00075001d1810640c0c1f80c0b0400c000041c4c5004120254a01c1800c4007030180d840344a20342032180c0d152950b401140d0b40421a211080c4040074000014101c20103001c08241c1142c291403c40d00100d4000c00c119100303a0104000e401250310411000071080c0c0040b5810f03100c0da00ca103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226548848 1250 226547598 226547609
    0x61814011e0219320d20030a03090c0b0708070305090d0b190c0c11060703020a060203240303070f0209061201020d0e010e160603050714030f010905070504050906270c0301 75
    0x40e0451580c55418071300d0003c200101c2500c5900014035a6905070042a11588890807045203801560074850f0b10f50444e448089400c0000341e40d80c09150400c40050085009010302d80c0142e401c013003240d62408000d200300c0308050144500800c40d030441e80c1d80e1078881e20400354060b45140250506184590307011080001104200d800c4c1140d0300500c0d0312500c070b49000c0f03641025008501003040b030140040c0b603000010540850140900c8003003c2a4a0300045015038040c400016118050307149460324030030fa5005a070f10030f03002041880c01056005046001c180e4044a41c9100c607119540022030f0042980408056540040355803e2a141c1c1584039464141050000384031903205811901e84071700c1d0211f405000d0030803090051141c640f1a5000c0d90344400b003402e009242005008403561903420484180c03503a83c0e03a481c014400140d0a001d8039070440d0050401d14207090812001600072480180204e00900742c02c1c4901c4000e400342c80c82c0c40c80207400c4103003020352820035905a1209038000d014030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226550098 1250 226548848 226548893
    0x40213120b19110d020a03020f13060f050909060f060d110702150406050307030c0219050c01030f180303020f071a1f0e010e090705040204061814011e0219 68
    0x11926410214002e9202c0303c1004000c051821314020380e500000c2d08000040c008141c1d0a1041d42100070b01100103000040c441e024901410745041d80080081c2100d540180400400b406000703903940302c84140d5a00154201c2c3d0100b0b5104048d00401c03052701849000704141c0c0d0624a040d031301c4400c81001001054003d40382c1c0d0350f407100900c241719400d2080744203000004000b00005400c0e24800d51201584110381c0c415582401c000c240e40464003810041d054039190000c041081583da094480d0808900c0208024489074801c4184d190298400400250038145c000607000c82000404048680d0320780d001d5500454400100540b03c103007035040b1150b01101c803680514036a00320a0f4446001103c4d10180703818426820038003034040c604d2000d04007012034420300c040401c02da43c650000d000541065581c002903880420200d001007001a4403400b114404d058903140c1d50313603118445041403d094101c907020745001c0c0f50100e18200504600c01207000c0742004100c100310b28000d5803d01e00c2581c101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226551348 1250 226550098 226550131
    0x1110c0705060711010f0215100e0708160302090307030c0801021c0207050703170903010f0507020d1d060901140409020a0f02030c070303080a06030804080a0629040213120b 76
    0x5002c0d45204140c40a031821010719603440c419842a010443e4800952068410303013108100e038007001c81c5082c0c441843d0b82503d03081c00c0c00315031a0010307900d42c080421318000380386081107890030301c0070780044498008054000a0401c0507442c100145001564000d0120380e400c2d07940c03c8035174001d400000e207c2c990480d0000c13142114070303118002c3e1400c0c690094042c028403840c50b80c1747d003003881c00781500d002c080e2014001d0110319902132190407900248050081303000c1c41d040c003000b401c04030b95200000502618a48421820040301c03440d42280d0780a035040c03940c456450380180c44c072041c410896104d4030000107000c00c0030400c5401804c0740d0140358031450300c0c40c4402c510982e103901815821940b00c1e8860301040010070f01c940003041d0004185403001444e96140d850341c600c2c03a44560041001a40403100e030bd4100f1941c1c1c0f0504040200f80008080d0034004400301c1c039028036687d46c070f44d40308039004910307505c116042e070031400b000b008009050ba861161034a081e9520000442c1d1103003407403c0409 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226552598 1250 226551348 226551359
    0x14010308030a0213031a1006171012050d1b08030a0c030207020d05010608010507170703050406020f040e09150108061503010b100206040b0619180204031a01030c1d180a0501110c07 79
    0x140e2003065032090303154902740584000c3c84501e90039004001d440d4400c0f51200014180040304440310305540510045c000d41d50a0b07034006070009034540034941032504220520300204484800340c9070049110540400e404031000030403000780c003800070003a60200d08280c54004200e0b055205000700e07500c100081c441c0ea5070307004041d650105c95051500c0c1c01c4145100103545507219500496009102d51001420000c2c0581c001595801c685c10406284440b40c003030104070402008005071400c0013000400c0d256060101d101d84605020301440701c0000e0503440405144c2c0c080d00310002807680540301c5440c062104000940d5107500760b5060f12100c0c00600461490b00b0400101e14001c601c00d800f10000501d0b1404174007610500f6585200507a6080c0004400a03400213000d075240d800356040034003654110b00380a1419207a41e4000d14928900c61410a0f80c1c440a400c100c0c0d0203480c1204003806464100d80083c2400d4107070340014040d5207092017215403902100c0141107140280011114080c0e101c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226553848 1250 226552598 226552621
    0x50f101b05030a080f1501090504050907270e0a0f0b0711010203040818010f080601051e0c0304050118050a050907021c0201020d0b0108010b07020625030e010e010314010308030a0213031a 82
    0x302c0f61b541c00a00c941c0c40030700240c00d041d080207030002c0050048804203580c803c0440000321900326030444c0300d0300305d03200b03815010200d0080119018020000d01180c030001c1da03a10922040901c801410300d07282000003058540200f580001503036001d0000e560360301e4a03103000542940000c0d015914000103498000582d4070074480c00e64080401d40320703005180c59200064a06170003c052094004184028550f11025100701400340c0380b61140080d51290f060100141c00c2d8890803020501c01c0742c1c1d242007001159240201e03082100d6055844e6600c07038440c40d00c1281040303044011a60210300480607960082d1b8154002c092a90038481d04003d028004c800440da889000c2c030032640c64010600c2a2005850510024000a003516074038804502130034844d4440c81441e0350003600460b0211070402d0b15543c1141c068140e0700400d20707040003501c480481c850ac1500041c080035201c40400300010b10458020b40c120380300300814000b000c5c625582c81c130b0514580116460688448a04540803070200308070b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226555098 1250 226553848 226553881
    0x60c0a140c07210602071104140405030f0703030f0515120f03031b071727182703040302040f0e1b0406180213050f101b05030a080f 58
    0x11180600b92080c5007a03d50800600004a084030041d4640742c002c0c00254244001d12205220b40c04e0030502e10404403c100849a15088626800c2a008100000140c1c08401c550480c2100b2540c00c1c0c1750300c50b0741001c82c0141650941172100134500010302000d00407c03034603c19072500032510244c1c00c600f4883c3d5541c03111001910f5202d2a40300388049544280d01c1070b194441800c0b6040000e0a01c00d440c0c5030102110310990700c00c041607100085200d410803513003c09a080300301001d442c480c010f00240200f00d0004465070142c4031150a2404911603402017036a01030408090002c00d40700c00c141c080310702e44951051104034402c0346441c52460003040980a0000b440c040c200c094500d410005d4450413a4440c25032116034001d80d125408161103040c100e400941015440d0b00503198116184401e5400c0007503040f0718459940709801c510640c2c2c4c1c05001b100e800c005494001e4003e0141c0660400b03000c400740c0d008040340000715240481551100509100e001d01400e07601c06620750740c030030841040d0f1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226556348 1250 226555098 226555117
    0xb040e0d0c0605130210050c0606060f03070e010c0c1715070f050d09080310050f0103050103120c020409060e030306090a05090303240411130e06130c0908060c0a14 72
    0x340d078501c0c0c60200d04107610440d40101691444040c214440e0300007034400e1012480c120206501048003032211504003d115400030050741c4032442c180107801064814000180001c0810142e00840180350f403141020040c52503009141c1c032002c039111480d040350041c26220210152040540f60340c001c0760560400c0b4000d212581751004418030140c0122441c1d40007a0341041c28036240c60440000a0342c0d8002103100d2444407009082040c01c0c0810005480d002500301f81c101420400180046840920104c0005105051480c440358852002c24041c01c4c00300001741c01c0c41c0c0342045101035100040004c41c4034407800c489240055841044020485000ba9000c03401c070391088c40080c0c2042c0c03400f0004031522001d120001e49001c540b00015082e03410401350b840144001080e104040c4c1c40007181c90014114680402c2c0041c030340040440c01c408402c42c20318040c2620b4000e1404901d01540030b01d40507100001c156210380c41c220b5401c20300c42d80002052800904803a1800c20707800e8030001a20390294 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226557598 1250 226556348 226556357
    0x60f2511010b0612180f0604050a0308090d081f0305030301090b120601140405040305040e13060606091a0f12100503150705090108060a050d03030f1b020a03081e04060b040e0d 77
    0x2119502a01700340307919414541c0c8244120101608540003c002c1d480c4928170650050500d1120b85c5001420b034500580400002d5100d1074040040581001106a001000d1800c1810f000d580a040b2024130115070300182150000000201e1000c0c0039400480c40403c040d41c51100c040d00c0c3c0780201303641c0c0d10244580c08001e00284030f031100324902904200c0d0494083d01d8030301d043c503482e1810940011401d0701d08206030007404002608221407402420002c00c864108001210b26200c520b1704031039000081ca460801c000100c0c103800c841070314141c1c3e030f100d05039007584207081ca410f83c158003082030240603142c403034800c020314003901e03040c42034a15204374003960300d1501740000ba00c01580c0d031400c0a8442c40d4451500d01010039a6104c92506036581130103580e02150300942d0300300b003034111800000d92400540070240100c40b9181c001030380500003545440e010078a5500e42c0081c8a1180d000e00311040704003284800d11041c40b0080d003100c0c003005000ca8081003040c4c02461840d64a110380104a004034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226558848 1250 226557598 226557601
    0x1050a030309180f02030a0f11091005030a110f031009180204020702040f050c0a030e16050d031107060f030b0405100510030605040e0604050717060f2511010b0612 72
    0x1000024180f200f141510300402c040300c2c16405003040e030b08111021403101d40c0e00c0e100da41802d042c50080d00c40c11451070b0449450040403070046001d4814001d2010300f4440008046410054140c0c803403194807094424a540303c0032084c0720104241d109690080e02e441d0030031800310b1f8981451007944a522420380c0008055034482d82440003a4220880030303039002c0d42c0d621040007841854001c16200b141d015100d903507a0002c800b4040c0480704a0070300c199107a803060307101c21741c1e826007105008140e80c012140071841c906c00c1e00e402c4070201008500751003940a540c0c40001d00580000074100ca40e03200f0b17203043c081030403000103110848804407040f035412025140c1c1000300c0c0c1840c008540074940d00307160120b21070782c50b200800c0a0320307503d800302e824581c00041000140403040c0045005881c00c510f0078980c001c051510310355102005060049020101c2c00841da5030010304100d07950f140d485141da801c10070141e2a01800c0080403402880540d400c03d0318207130f12403038020b04844440c400710100004a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226560098 1250 226558848 226558859
    0x20c010e070b0c0309040e0313030303020a1d09010512240f010603140c090d050303040c03021207060e0609041d0f1627060506040b040503150732070501021201050a030309 75
    0x241c00d1682c40c47d0382e40d020400a0508081003480280f01950007510050394500310045c005114210f120b540801800300b441c0c282c1d08542d242041e040c1104e00c02c5a003e4852200000d815003800410742e500500d03205082541e940b03110118003203601c100c0340011254a0390b070340c4107000c0e029154420313611322440e0250300004032050300c218050000d11030080c3c160720300d01050b9a165881d645c0151410750307a43e09010420002c40c5400d0340d00304100301d81e4102901e1058a071402c044c0c103090703103805405d108017004114843e043d1600e6221401c2202040c410119000c4107000c00341d00d8510000d00c00d00340340140c00400046598006c05201242d090111911075900162582c030075501c1208038910259031101400207440d0745502c0504003403c10001032a85e11440e1204041c6010103040c0380d101149100010015a80d0704440910a2100c5202c00f18080d02015000760411100e00300041035602c201040070300c14400158081d1072400985000500c1603600c03002005070f08101c03840003c00165000f00180038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226561348 1250 226560098 226560101
    0x60d0b04080c030a1e0509090403080402060910120f0b0112051905010f080d03061d0403090e070e031e1f11040315180206031315020c010e070b0c030904 67
    0x90060081d041581400c00c1c8000c12800c641c025500d00b070000b40c580d0b41401034a280840089145080c9040562801c801c02000c11802c8000810107401d0000060000d420340d15940112042400d000309203042240d54808050220303102031508003000d615084000c00400050700c512520040140c4560f101071004011550140500500710504107058058030620320340e250003403078003905894070300f24521030500b100c040c50504405440c0080604001e8208481d035008050070324500e41a4441d00d00d6135980703082c2a00d20b690a9805040001e050f0020403520743d5002000d0b4190311000c400741c400154000c2d60400c64102500c1050642d90000340006c902945c583c0c0b89642e50341441314011810308a03410305007040350055441500d080300305020170103404045204d114203503440b4043ca0385003042981c0100d0710500004211101d2603400750115400c0c00404600c41c50180c6441c1710035980c0b841e0214101d400782440c0e030309216080c49001c0b00070480418400c1a580b070311010074000e50606826608110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226562598 1250 226561348 226561351
    0x603010b0d060801050f06030f160308300907060306140907260703050109201602060304120e030604030509190504151502031602150f0d0b041103060d0b 67
    0x32981c603075800c40001c050000b0300a061080030081800344a03441c0c0b480a240c204200c0310300d250015000500c6014855440c40c407a2400c2e650421011500c41169041c40c10503103a48a01c21600b0420504000d04100c0707441600c14419080303001500c41c140d954000590540300c060080b0108204800c8049400781040705000d94400c1e5245054031518807541029101000f20084140300742c0512010486160b0301409003e004201c44c810801000c0c42d0840810a00900d0728200b810002c0c0010b02074421085a00c80c03000400e0300200020b58a0419141c00345008403841040e4002c6100004011700d5231402084282c1300380e0709a1a01850007480034200070150b0f03464070070a40704042140d000300b4291518481d09445140e003241002005080901c00e002215a001155003103500c204189031403610358500d03243d03005074195a1100038940300d10f590030541c02802d4400142d5480850708031102d5504da00404841402a00e00308406942050b03a02c48074802203500300d4004001500040001d0f0066103002d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226563848 1250 226562598 226562617
    0x4050f042c1005060a03030507020108041515080c01080712050907121a0c04050d03110304031a04150908030c18040e0a020f0603010e06060a0e0a0605031806060603010b 74
    0x200d200c004000100740500006503406040d960110100d51082d0755a485400d810100441d2803030121440c56900520307a01c180e0400038104a031110101d010485070030f0b03030010a240c0400040c0071000c45040c0c01203240380e8900c10422113104040344c1c08095400f42001030300030101652001401c1c0e010b00344140103400060010a1944110383d0700062026110003901003c0c1e215882c40c040b8070814595280c0c01c58801780c801c0d0304181003000108181d59540d0300e5000110740c1410075000788104103080368114000da50001e08581d41d900382e210311303001081001c0c903c1548503a0181c022002c4100b10582120b60200c401010120b082002c15869000c80d80913061101110b40c02c000c5150200340401c06880f50034000380060342c0700c50088011403608036120308080c04141d50680c04c640c500140c200044402a100354015000041d11905503485020006000c15001c0d240c0c0403140e80e1241c00801d6640300f152980511103800007103094005022502c44d0107194010855402c503403d0450801680e031250000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226565098 1250 226563848 226563881
    0x903040515070b1003020906030f19020406171c0f0203040e0402030307020a080c0301060602060c0a030b0a0e01060801150309020d080901030209090103080403060c0804210c140106180204050f04 85
    0x2d000c009481e062040f0300c60740c91140c03040c00007859803060090307440c4003501207031180d080300c48038000c01d00c400104090f81c886102e210745010742803800890002c00454103d0031003565011b189081c0d00c80d0004502e00d4107904112015001c42d141c1e14110355000342d4150f16001a041004104000d038440030314203812600040540e407406040c0e600060441600d40d011104540104200003000d28080c414040189198005820305140407080c4103214400d152100c0181980e03290689843e48480741400094000380d00b5056040d40c55480c040c11109091045100b181c2c0801c40d55000c81c0d11900030082540e50280010031300074400d40d5400e0b2150070a0009a0406030300b844912841d035260340000780214000d07031095951740d055080100994844000f680c0c1031050300c1c4140400589003140c040540e40005d082c001300c1d03d040100464042d9040358019200b04045000c0e0500f210341944140116240303e24000c0d2800d080d010b106e020703402580300d1207a009900321400b8080b400d0580025070419420803d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226566348 1250 226565098 226565107
    0x3040201050d0f09060e0d090e06090421080a150e0f15040f050402330c031306021c031a040b12160618050f0103020a09050a120501140903040515 64
    0x42440489402d418140c91203074840b2001d40d034101052140344601f410524107842039a0614580c030382419000791601e409040b0a4001800348080141400c411000d0103200006010640600400592041e5502803843c1e00e0441c20403c910280100b04045a15400c98010300c0e50358000c080d110010020141010360402500981143c1c4d910300c124902d21140602c001160308007401405a03081444425000b40c503ca410a0403030000d020b10882d0300d1071084a50742e50b0311550940c01a046004102959580042020012031050340100d00301c0140d40510065010305140420704406580307228107180502034003048010303443e08068012044040d40640600010205888000e1815400c041700a4074130100303000600029500a440030116414015091101420000040c00a060551016060680c0000ca0031041c602881c44007005040041070782144940d5001c45600c102c030940307401c0b5580d520700041e08180840118150340150000401107042904000a0100f02000f003900d40031119410310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226567598 1250 226566348 226566371
    0xc06110a020a06060e06011b030c171206030a0c05010f050712030509100212071d0a03140c04060e04121e020a0c0e04050c06160503040b0c0610030803040201050d 71
    0x8004050003900e90380148400e01c220304140b000c441c41a000112022100c02c180b28640c0c2c1d101c2001811002a40300f17040710220945416a1454000030000f441e1001c07407454411040182d40c05004124000c0180c26181e80e2131303030205912001e80d0000240007110713004040c041948a014900e4890656040c080c0c81e2a190313071102c5000c42060750010000076114400c11941240601050800915101d401d5040c1800d403003070b15444000041c503402c1040382c503404041c11400b00c540050004240a021240800d403030b8144000f00c0b143c0d150484c61148241d030751850041c2454841c11086941c01022015103480340c2e9205030031801d51220361003c00c820303a40d1070702d2158003034060247c0c90b161030b40040080b48042e02d45000c00e54071303650250000c2c51409040201060000c2030321400517008031000ca60f6100f104031003162881d1500c101800c6c922003c5404940c46070034034000c01c041d240c0c0340100d41156a50050105c504071a0340001412048240b0210340154090380180018203907400d1301055115107d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226568848 1250 226567598 226567631
    0xa030605041410171c1202070605150f060f09010509031902030c060f1902030c0313031419060207051005130606090507050702010c05010f0c090806100302010f0c06 72
    0x105440b1614882c0603041c00902d1519400c4400101501e4030002e001c107480448541c1c0b0f8000f5281006052804600d0305001c1c41d21442903110b2001c0101e00841d02d42000d4103052005103011680005040b108880c201024904200c51410009000301010714203c0030f41000192500602c1c0d0541c1486414405400340b9503080c42031084c44a511600b807100f0301d2079030040514041560f10b0039800345c0030404c024450b03c0301140869a21204a00300343d495105072020403440d62181d05c59190090002044031100711458060380d8080368003911028003420341c00d0680e540c81b010041c41c48608901f2010031000003843e00d4000d022691301030340940d40c080c0104002c190590f00100c403243c42d850014040402000b6151040002410200b40204150710f0700319005441c5118080c0302034180420342d14140d040007425044000c40500300c050a0101c020b00710809000c14a1602552000d800b804001a04000000f00d03600f04176a0165200785034150005000d032010003001e00141c6051361504104c88078140031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226570098 1250 226568848 226568861
    0x2a0c0c3312011205010c08100e0603100c0203041a0a08130c0308030a02070b0906220212030d0c09290c0f071401030c09080d05031807080706110a02090a020a03060504 73
    0x94003c5900803980c0746451401c491010203000d0034000310fa4280500d00c05413000c81070030382d012800a000980c40b8440041e1400e1440c405641b11a8180417180d04a81da003c0040c000320340d00003500f0310400740488480d1400c1d0140941c05c200103001c0d000000c41c1105600c080b50700f00c6026a131000010740e01c940710042c00c0d520841d43c94200540005510042000e200c4049a00c0508140034261070300304251000302a1074120780b0717800594052444003066550710300911003c2031030707903044955940d100607031907001d03040fa1b85240c07000c40c41c1c45100003460000e9469001e9485c5000d51202120078440c6801b59158020781044c00861144207051040c0d40c80070403040340900b1544040381460002d003400142561601d0120b0420089080c03420000900000784a802c941a076042864aa98031050850910301c2091412419445a4507001a010802081d110250b0301d03a6501c6007190814401c00d10340d154052038000350091041e100092801c2000e5019082e610f485290120b402076503240060296003d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226571348 1250 226570098 226570109
    0x304030303020a09122424030c080a121805060a031401090608120f090a030b091c05031306020d0609050a0c0c05060a052a0c0c331201 59
    0x9000860300c00f12a0002601001440390055030365002a159955980b240d40340380070080d0101031020006d91040a94101d404001c032444081301c0003800382101002e0221003440255014a8141c0021a1300c0f0300110311002101e8001541b04d000750411001201c0f1030700000d003000d001c080400c9003c100d5580302e80083c41004090395001c100340304c0b07580700701c0394003c0181c3c0041880313842c11404010b11840802c2031312002c40074030041d9840362806000c40c256482216519a0f12002c0f44030084100301c0000f072894000c0040a045541c803035095011080304440010140c40031400a00014589407015020402d1083c0304890250a090b450403618068410540201204540344c40c10001040440c0c4185480800e05190400c0660700c2500e404e6242c0e40f000e4070342552181c8070000105042855044101106070300242c40c9803d0b0701740c6480111a4014110070491030140031006c002505d003020b1050481010b12117100b0603200381c508514444840341001c1c00403d4014406480c09050302c00d0b91500816 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226572598 1250 226571348 226571351
    0x901080f1c02031c0f06062c18011512020901090e13050d050705010b09040c0308030c070209042003060105060d0c1103070c030203070b030f010302060d090f080405040b060405240c0304030303 84
    0x105e15200040d1401078006508021300ca15030b18406038501c1c04865014030034040280004106c50b0081910160383c0009040650601000011640da08440d021065401c03561185400406040a94280d100b02c1c80801c0c0040e00c070350014002da0031156003441d007110a184500d01a20b8490303481d14280710100005601103403003c221030041c010203014454256204407030000c1c00d0700d40399035200d4002081c0d0201034070f115400f00014099020080880e42801d4000301004440e01c7d0a1030318404010980062030360740340b90820480f1050400152071416180c00030f040600f0888000b4988000f440721117410301c20882850070302803441a09000800d907183c01400422080382c00d50050610300b900d02c0e4000809075500b0030400088020380848141540d0b4103c4401c1d81d80d09010343c01901410500d00094226028880072100700110100104122401600d051004071243c1c0c0c00c00110340183e1182c141c200c1d03101d42490404c0d0840782c5007c0340c0b10004248580c100b80400d4800b52943d04140c000700e0220303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226573848 1250 226572598 226572611
    0x60303020705011101060b03011412030d021c020705061b0909090d080f01210c0e070806040e01060803070f02150d05150f03150c09150301050901080f1c02031c 70
    0x1560b010701300440d10180b0030b000303016030f03131410181785042c0c841445207032400c01c887d10740d00c101544c6401700c10240894001c100c940340c00a030a1400c0c001c5d4460403190170ba03e80545100d007194003ca000340c611b4150010b01500709540d40c0e526140c00c401c108071003242e41d000104441c0001c0e95549510741d020311800b00081290400a1502070000c0700d025000c801038200b03200c010800c4e21000101b07045100440b00300d01000281e1850f081401c00c480341c01103071400300400c0c101301103030350b101c1082c61160740111010703c03031b40401c010240e08880301405036800329001005450701084051080c01080ca10180c5a88080d00c200a51230943e6001007001424451b103035414081000e0124900d08048a4111030300300704045450700095a40341200c07044070340a51080d0002e003541c0218404c1c5d90320740b84060722921404a454143c20a01e510034050188141b12440020a1114001891044051440700108404420402101018990884c0810031484200710204004c85540100042244048004983c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226575098 1250 226573848 226573859
    0x110f210609030405282601060e070f110c030106030f0501140c070318050402160605010e010f05061309110909090d050a0e06091f020601120804031103100603030207 72
    0x40035005048040654401e00c81480a540c0e01000a49104c1080c86906601c0040216a1804148507070005001d201881c0c420075003050b900411400340781890b4020042036446074261403c00805603490300005103c0020411039034090110200c03d1030300070084403c47c40481e00000c1c01c0d035840d500704580c0d4918502010081007001d002c0c54070105030240360a912403818081504050003219405400c0054032184c52040c5142ca2480340d02404001e4025540ca069a10b01c20a003a41358100444840346020000900502400d402c541070f94100400b240901c0e00d00020010660802d0b00d294249552030700c800250300380584220355195003100c03483c0b901ca04030745042141c80080203200c815070b6080800d00540440d03020080354840c0a86081940c0c49003140b02c0810051b00600e2617140c0c121b15407200020b000014400c6160199405034200c3e810340e82c1381d08410301c1d80301401c41c005080c2c1900340002e1002030040104048070f01c80c06402c440480c814482000e0a50306c06601c1a00981c00c03920007400f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226576348 1250 226575098 226575103
    0x8010f15170106020d170705070803040213060807062c060901090803030a0614010201021602010809150907082104060f03090f0c050f1009300b0601020607110a110f21 73
    0x2605c0c007038101210a1521f040007400078450580e004000020020005003190f444265141480034005d01c2000b01d55124950030340c0d00d9841d801000c011410700080071000840c80122049680303c150b20f628100c031005000d0081d40d41003040035a040c05406800440c1d141d004001452054105000204401d8540113071903100c1002c50004a04590040081e0362a28003070664141d021039080ca0030600b0f90752281246410000032500c0d1188408000f002d101c080d000c0040d6041c1907490200a0f81d50000d059100385a440189400100c94104140001c0011a0040e00b40d10000030b0a0f090210f9403d00940e9130741030035402490205c61040e03800d0700600081c00c00003000300420800761200018460201005400c0300d0041c41001038544038410170540307908240a0b400300100c0b4610031000c659002d85403a41d031101003250b10f18018480c400004034403d1103081c5102884a603940501045116615448a07218003402840c1c0c000b20303804810348494039201c0c10f908800c0c140c0d008288541042291813070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226577598 1250 226576348 226576367
    0x3140d1b03021b1309030c110a18090614130611090604031b0e07020f010e070302061804110408030703171b1e0d09050d08010f15170106020d 62
    0x8880640c1440c80000036000035190b22902c40e0280030768049005000028078240720f0071100c014031401d02010300c0425410010580d001d511610704030074501a018140140300e0303698803c4000c20404070440c0c0340684800d5111024607401000041424280c0c0140c00e090050b0541d0709110340b0b41014401c170306028003031241180c81103021200d580340c4500c050001d000c2d8000d07800082d11101c1d042661400308019100200010b0501680300000343c030b030180d0080d44030140442031512039400c11014000110300450b005003926402800e981c1004c20f004c2070020b4002d107102130b1580107551540c0b00699030902601a00040404200450362150180340042890303840592510301218520b09201d400c03100841c030f10410a8040300744503217030012441e500d5010100a240c401c1ca0400009090720143c3d0142c102c0c48005000d2003c407142403c4d40034080341c11441c01d2155000c1c210304a101404880321000103001c0c0ea0300245046007901030303616042c0c03050141c281d201c035001d640610300121300d0641207036060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226578848 1250 226577598 226577627
    0x160f060509060603030301053102030f07050304030219020f152a0a0b0c0d02040305030304060614010905010809070807140307050a0e04020d0804030f1113020c0c0d060603140d 77
    0x80c41c2c2410000c02081d6203001c180685d41c03252814002010401982c07103c006004079880442480380321615080b00002d600035500600034645a1340060341c142c1c0607c084070301465041d4014000d01e003401c5480c0b07003c107403001070486c1d1010078116210322079075070007010511203440006603580d291080c2e00c034a0a440000c00c0e1843c0c02000c0a6591211400e0215164130307015004442c21189a5544010411507c206075088808c01d1010a0100034881e00001440c4204e21a4904004090b03c400844c28902150418503002a80f111424011540724810707064000c20710390100c41a003510740c03149504000c0d0380e81100c040080000c02d411100e150030000503004000a42e4204021410510744a82018005001900542c0e4007000f1a040041245c111001180c01050032072461802c0c1c81c0402000000700a058480c049020001c814a05c1da4400c41e510700495200504c3c200c0c02690a000205440c0791007030b10002d0380d0310701c004003103005180200000e0300e14a01500c8144039040000e0988008035200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226580098 1250 226578848 226578853
    0xe060702011d1b0405040804151206060305131b09090b0f0c040612020c1c02100f0203010b04052b0302061602010527010b03101e0b030607080705160f060509 69
    0x940c04288840100c2011003c0151004516a901c42c10500d0b401c0c89550700040c0680200200b90b040c045d48a00e907041c143d0401101441060b60380c0c8030803026110b0644804079413408003060040000d0807031034002c50a1032a20316a09007642e84004030811665917800507140d071074088040110b115140e02c080e40d0300500e0b00072072506040c2000700c0200141c0070104ea400c1c806900059104607254200500c20b040c6545807414203140c68120002510303455603080d1480c45600744503402c82c2c0d0403041d00a0b24180d4021068950800e407403c01040020341c0113a4094200c0e03002c184c1040d045465503100a200140240c008200c0340c02c2104907642075203003000342d034030469141c481407100180c0c00c9211016554107c0d50b0940c41d070b400b45040d81c0c9c010103544120683c50700c45c09900030906100340d040b006605a80d078080c3c010981c820031601e4142c0742c4006105915411490000754500c4c01460090b801282d01c1c50080c0c10080c1d0b40310401000c2d0000780d019a01581c1c001049010801580074056020051502 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226581348 1250 226580098 226580113
    0x1270e0a0606020607320a02010e0109110103020d020403080d06030c06110a0308150a0314010c0c0c030807081303050312070c050c010f140d0c0e0612040602030a0e060702011d 77
    0x81d1102c001900c01400c101126a280c2c89011000206034a00c6c12003810800d0301c4400407461a400380d01030503110016500740402c403203010406105500d030154000c0c03c206c0a454031100118000d61014180d1043c440c0c0c2400003002181061002e40a42c0449900c0000d8050450030216103110b201c3d4054800c220041c480302c1e04400011910310070483d410f00b0580c080f42c80780c5c16040401448500003e4120040c610000240540d2107034007588501044020016888035142c101e5000c070740e40030094114031104900b0000503c0341030040403183c1c080d0044a017841c4000c40d05801d250120760050b144c65002040e03115101111226407500500b45091055516840750f4407140c45040c410b12890602c0703410001d042f21580281590021121a60004c41d5a161404442401030000e4541e03500065021545501e0a040141c220348601025516000071a9940c1c0d651502075480204186a016100c1d2041d40d0640780802c110b6000b58044d03000070541d403442078900c0004240c0520705610a40c0b0846 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226582598 1250 226581348 226581359
    0x2030406090506062b020402250201091205060c0a0c020d08040608060a05030d0e030c0d1a010e04031706010203070f060203040308090102030c1204061d0a120212090d0201270e0a06 79
    0x2060311582041c980e0b1805c85141507000140c0240100c01a50740b06920480a512015002080c0c1d9540326100b6216249196200c0c860030740b8100724260001c1c03481d48810042240000c805015100801e000d1510030030b070b040c40358045400c000c245103088a07174000105051082c240c1000d60240e0010007913552034031151a120020350355404618000040c403203542000d0845403800e00c080a030a0101031700301c0002410300d180034414200c8035034003c100c001c0c403400007080c60321800102501440c0c25035250b20403400100b00b01040d20750050207041c1588003c21550b00000d20fa0000c691015016810040e2a40b4140c107026128184c01028807105074410401c111034040340f40103807003042c0360101d5103071825039540c600b8500409200c8144400c180030307400708140380200001c190100c0b40c854812410600b103909002d0380e07100301e0400104c1c50031009020300002403c0c00301481004900524002040400e50344110303491802c03c09028079011480d6400388980c08415448503001060910100520351800303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226583848 1250 226582598 226582639
    0xa05030d0f05060a051903020618010e060a02030919080607091401030908031302060903070803190801063006290903100e0a0b07020114060405060907050a0504090203040609050606 79
    0x50042c00e2040180c595018a90703514060946c0c042c5030b0140c240c1d035868a007140010440c2c900703c0030080c0011f4601d0b02401080c141041034a58402041c1c00450521030900204a0311048841107102850090030002403000f03001c103d0140245442c0d29a82202401c0103a0b24521910350758016040c541440030981c0091403000c01c8940c03141504856620911081c0f00180c5240b03d40014103901d84910240818581404002800d1100003112807095030000c04a081d113000030248950350105051f2114040303291400111200e0114000c800c40c0c40a080010906084880d079400001d0024182d0311000000f011142c6c11403d101700d50113101d403d0619030800030359150b40c00098100c8954503020b0b4290808005c011000301f203940401d1030240313860310200090080c0210761050740c5040400000c15482e041c64803c1a02480014203200d03100d9458403025a1103912001c2c0d000c0c10444c08000014501020340b014600451090300085190081400d001d40303080e1003d0101032141c01001082c031181d0300308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226585098 1250 226583848 226583869
    0x90903071a1e0f0c3001060219080d05150d050f0601080f060105130908030a0203040b0a0b01020c01030509100608060420090a0b03070308040303032414060304060e0a05030d0f0506 79
    0x260300380f0030f540745170102e03490042d82280007042403003c0a02110100f86244441418140d450b00d508860000c95001c0141101c104c0b50341c0d010304205010490f0901001c1c1d00c1c3c0201da0301c0340c41c0320041180c9540040100724020b41310351082e40c5a13040403840710803162003440300a0041401314005e00c1c94078852081d180e103840042c800d061042070101d050340d00661594001c504007d402c69005c0b43c49251658491b006544100d40444482c0d070302e0000248900c404d4130a02550041c180d00503d2511510380c015801040013901c004c05c54400e132070a2820107180c900a40e0064504180a000700f4205840d282c900205100d01031015203030300078203050b15922058007469002d41202008204980490007280c00e1a600d90006401020001004014550580c00440d0599001c110304400401e0703030045220024818040c0512212a60594051502d4114080d503013050248100103060301c1e6186150740380c40c1c4105e8044036180c0001c51510549071040c4900030142018210512003071901d000040c0403d800c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226586348 1250 226585098 226585111
    0x5010c02010e07091d06010f0f060525020d0b070c021c02090423060a0501031a01061b0204020c060405010b01110601030b060d03020c100909060f050906090903071a1e0f 74
    0xa0741e1031062121710844002000174a200d80035210a941c6a0080d02c0d50501240203440d680c1d4200d01d00003480c0c6103d0790841d80a4840c49807011580ca8400c5010400160540c80a90b440904a01a18041500c0e082018020341d8640c8620312205264414001c2240b960060860540d219561000243c5c81e580d00d8590303c60303448410f102907200e6040e0b04180540c0346040c90400751145d84100018900306501c8a03040c0d0340986080311222464035001203800c0000d0042c00c2c00030f890785224040f078028562040c0c2c0040c2c401080941810504202646445401c0340c09030703180c1e0346425424486503081759000c2400b03980c003000360142e9811900e64142103040900440e0003078509001d080240340c400d0090300188800200a21110410b070300b0018206c89131780c058650200e2030403900141c110200e4070760340111203001d418582c3d980c1d258020086155401012641c450000300303d5a030004080c020b600e120389145403800c03034007814110750908403084031510345100d240d400014420b4114518192941c03201c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226587598 1250 226586348 226586351
    0x15031e0c091d0f061216140112020c070b090111030c03030601030b092a070f0f05010501090209010c060b010903080d05040b010e040503160303060b0a1e0c0f1101230705010c02010e0709 81
    0x2170030601d0b103000901d115000c0d0320064140d02090408a90441d10791860090b69241414400c20604000b203101c0c2c42551a690b51003401c08001c00b4000700b02911240c90141000901d41c449644400c0c00d6503c842c81d2400710350400802c00c0040d42e05480f5850a010301540d0101040c0f808106d15400912040034140c540901144801d04108400b000c0b106070b01da121000c00d4824001e807400c1da203e00d04400301100c06500788000452011740c0c503c00e5661001c41650759280b540e083d03465a40c0204042d11880341001448000400421500002400400520700000445241038207001c6c668010680192800b010003c041c080425000000c2d2140d40d9200b030704c00aa0001d1518050300140200d9101c05e500600200380404101d40081500c030444141101005034802201c00413a040c0b5050702c0c1c018a0245517003000c00200e91100a138105040c01810702940c42d03441052120360402110000c0381e80343c1c0c800200c00c01004004e02130444090030f0760000380000c484c0046890b8913042a4000d848416 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226588848 1250 226587598 226587619
    0x140607030e0a03020d0302010b01030b03010c0207060c020607050d120b0a051e040b270604090206070b090f03040312020d0f0e040b0604052e080115031e0c091d0f06 72
    0x9540b415144801554010910242244280340190182c4458804c4a000c039140c035100c202c8504041c041d022415071103a0151404e1800d01ca8282ca0080003054107030380001081c440400060f00400242d0000c42c0d003515461000400b00f911002650300d001c074224010701040c0000c01c041e490b02000403030300705004113803c04040040d0700400c0050840c2c645040d03116240c02c00008074070902080881003441050f041c41d1950360f03510180429900e0004000b5084101082548085104196110b8100d11084c00b03a0340b44070030b50725807945550050740040d2901c20300c0b10020b10b85d60781c040048445150311810090808210034201a04005040510600036030703c5040b01603039a9130384c000700ca001d000300419000300c09400d4200340265041450310480c805210131441c907021800780350082c0c1282e50307014851002c0020350304201d02620900e0b00301c01c00c0c04c10180b021090b1b00c2041c000c2402032143c079070383c624159160207a8101810301c6140c400840910304014000c1c42c1202809150388168282c88aa002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226590098 1250 226588848 226588877
    0x60a090303020c0a061d01060b04060810030b010329060310020c0705190e0708090d1b020603070c0b0a06180203040507050a0f08150f060d03110304090509010614060703 74
    0x80d00c42c0e6450f0142c180138a0481d00104000d5a000c5d600a070a64001c005c0c2500c41041224200d400c10b005112202405000412686100d82d441591006c0d40d4600b26900c240d40360b4450b4043c0c6000e030012642855511040301700322605014444200e0700c0346103c00054140340d0003080e19520144a4005180d030006010303501c180f41088094010240030b40360024070207442c11486250405030144c0241c0000d01c9001c034020901ca180c0e01c44c0140085400341c0802640d10700c042d515000c0041121700302d10f504903450b0001da600c407409184584007544031404103000038541448411030003041811194600320060020fa20789030300307600003034481000050f56911745d0704040c2c0c548907036a0b02056114260010114805220f501030340c040b07401d0b00c0c2c2110031204046403030300355202c401c54180ea0f510840300c0014aa61408120105800c0c0c02401c0440c01038122000d81030031a4016003150b90b400c2e44a40a020b800007092003554001d211203007081e8107005134500003910a02c1103400140402c94840b89642c2c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226591348 1250 226590098 226590101
    0x25030c0f081c060807080601080607180f0b0307030f180605100504021615060302060306040207060e030a18120201051207110102071212050603062205030318070b0c060a090303 77
    0x1c10894000d01030541a08100b407001e00303d58007403409180120038000415080006410717040e200790202800c016a1540d2044078018007481c43c1000d070300e580381400036000c07000d81046005886500d0b140ca50320714080034098140c4a8000251b02d0091401482c0a034082841c002903628583c07000000c50191100e1010b00034005103504195409032001841d5072080c0c3c10003503000342091083c0c030140c00e41194404160204d980724403011750816410000100a490079030b008000e010712038100040c0d011480c0301054590f030008007100c03001c03684001d00d09001c05407003a10400100075004a14940e440c00e80d00080c068081c1801391081c0a01c9880440e80c021300515001c141244080c000b151102c1603400c0902c2c100304503102c0c48001c50501c2070003004c50203103030180758031072500600185403076100d00c4051500d0141461010711010180314105001400a20040d405012040c0c05d400039010f4103100d05080c989594019000032504006800641c0d2000c604a903014484e80e400103603002490600b42c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226592598 1250 226591348 226591357
    0xf0a0e060405330718090605061c2c0f030c0c0607030c17041703031e1b0c060a06082b0908010c031407031401030f17070825030c0f08 59
    0x1a20403039014104450168000041011702c1c52984000100941d5030a000007247c286000f1190020020072420490581c1c50840780128441d003900003c820041601c850031103184030a01d00e4540da224240f02c14695000c2018050712078560b00914a40304015004640c2c03241c0d001a428000d143c040340010625008007554401590032202c00711241403c11192143d55006000f0b4108036440c0702101c0c10100c1300001542d124003c19000403002d0009001d0086080170010b00b04241c5c11200e081407200340c05090042c1c084641c40c0001000c40d0b0428081c03150036541c0d01d40043c10240d00211401500c0500b019904547c100c605245080855070000100d58036203464010134800d40c200074001003c3c0343d244c2e1080c0c2d0050b0040b10f10507050348858078120241d410610b115040d40301910010f01c040360103403009104a80c4100301506402460040015294000400580c0c03000c0300419001904052007101052128950300c040001c0c4e4119500540412051400038010240c810201001c1050540840303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226593848 1250 226592598 226592683
    0x406060504050a050d02040b13050709090b1804060609020c100e010b180406020f03070c11090c070303020c071205060a06052b03182d0303050a0809010609050f0a0e060405 75
    0x2611003127460f03190784010b82405d44140d0000f03040600002681c1c0414461070f4a0704800074541c0748101022500114082d01c00780050f1030301c0d603075503100007238258440c80142500c1d02c2c41e0300a800390704020b201250494030088400c1c0f03040c0e41441c506000c0c0790f0300c01001122024005950340543e460782e00b4401c0c001d019054101541580000c103020388190090081d0fa540340c030810220401400003001d02c401c3d128251001404000c0034801034000a000c0d402401c800d0b00e5070821144000c0c1c0c1c514052820078428181501c2c0368000c4410f1080c4502c0d540504030241106440200c05540c807a02a440c002d007007800c195030421010440c4104052049100755461085214850b00141e22040400948502c445031020802001480311000c10460403041c02281d0b0191a1603042c114928010b07280388400400b4034829550318000031444010034400d1601a5603152101d55007881e04206100450320041c405407a554071503010000003c3c000101004120246103240d541207280500d094000f00301c00030039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226595098 1250 226593848 226593859
    0x6050108130512040e061e013507090812090d14010b090c0306100806030601030f02061612110309030c010f2a051603050d08100e0f04020406060504050a050d02040b 72
    0x140c3d00210407501c9001b0242200c003650b03024101c032542c00010030840140d50224200d54100d00d00c40d0003250101c0130f02a00681d80343c1d00f02884c0516020303025011039206011a680a905100d166410400d2414024800168518100e404400520400e860320b500170514084412a2100702da001c0d04040c42801024203544c6841c10162804c1000c0c1c1c100305c4440e8010b0002001c8201494810900e4901034540503016208517401e50715010110f41954038280d8216104011b50072005820717425022016028504600600b0012400106503025120208445078020b01514a0070350b40840c2d060108102402c00501028079001c1c144c40b1800300c04507568044140b541380301142c036450498180050700c10307404e40d00c0e403580507000d500306552036000c0038001d6071188100b00801c5010380b440942012501040004803541c0d1407001904240884081c02c4207403415007840114202805000c0140c8001d00384a030030681018041800ca08081c840e0300d1042c01d6034218607080d5183c6910903145204003800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226596348 1250 226595098 226595107
    0xe04050c0d0f090201020c0a0303080103020d050109080a03020703081e070e0103060815010302280b210a0902011701230d170301141c021207081b011206050108130512 73
    0x1c810081020b110140d001d070040280c90003092402303141483c09e03070358107486045140e420368082c0082c050603c1d00488196680b00541004185020080e20300c030304443d600541e9032042131500411900016140c080d120003484a03c0302c90700c00740e10f0b65a038003c100d0301d42080c0e140c02c5d2a00490103020198480d4000b80141c211080a2100d0546403e05030313802a54011030030509214481c02c80e0402d810100c2c0340112129050000000340c00c000d004000c60161520402010400d6040c1000781c00d0b1140c4002540c1d40448404550b001b540061024002e01c140c41010340c9400301000b10741e2100001081c042003020b25441859075400c1d1544505500221500c1c0c0b1000c46550f00c07130f01d5500a026050040f909020050041d00e00b1041621003131518207030f004440302716075091008141c604040c256044c0603454010030f1210080008540411a00c4400c5401000c01c000141c940064560032905280c2004024845643c1040c40d0a402c4103101c0c2498a0380c5440d030608600b04074401c030a203040c6200018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226597598 1250 226596348 226596371
    0x60c120c0d03060803030405071815090603031e050a1b20032b081519090b030613080f040e0f04030906020a050601050f060c0a060e0c09070e04050c0d 66
    0x150724410103040c0e202080007603190fa6609a0fa80004c032001002c69229410038461406c505584c0c1c0c800118140006c80e005103d50700d01644d421094205110065803581c1c1042415413194003001c400102640c522211301c08107200070a00d100c2c204c511424000100e6094108130040c240b80b10400340c11000c2104107110340000c90746c403503034400880d62107881404c0010071560840aa949440c03007200e100e80b0307a080ca45245c180d0350120014400f001c504caa2210541d580c0d12800900c401c0c1010001d058207042e03040031800310855882800c103c0c041e41c008010001f110001600100c2100c0d00321005a0308c0b80c1d603121115180d40701b00e407c80c400d42c480c1c003014442222103d1140d603000e0f0b44603850ba9070b0604d440303007000c03603031454040380c0500b455201d01c2c0100070305d04241c003043c1452034002d00558940751100a1007850420a0407003240c2850303980007085800340b03003840030810b070100440340b0782e08900b440340c001024904c4002140c0e11460365000401c80e00d90300001240d00c1d521030340303109110038010007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226598848 1250 226597598 226597603
    0x5042303061e15040b1009030204050c16110d120e0901060309030e0904020307081902040f06030512210c03071101020f0409021606060308030907050402030402010509060c120c 77
    0x824601030300c600e00104400701000038405540003100d14501109607141660140b5401d04003050903000b90341e801605043d5240c1c40481240041c039619030071101032852061004841000f00b8205840d1000d000c40c0154881c0300552038a0300350011a000c00340500440003d402d10040040280500001c2c0841c1c0b120f95005041040d0458003140c0b030b0500c982c0e0340c5800f40c1c10b0340c031302ca10700a0000da2010450410b40c80c24019140c2c00070b001400700e50304c040d16038000518001d141c080040000043e81103540440c40c1c9401500c0d404a080d00040c00018959900c00c0c3d41c0e4103400004500e0b011003c502036280389035000065480b0400450400040d0400c40c8800000e6481501d6282c00a111034a07203e444440500880b1103800052101900c0c01f480c1626050080d00814510980050b04c0508000855500c1c000d03c0051030040304041e5903401d02039070407072410f0070581c81540540d0040c070800c40582e13000810703640001e8068600f180d071207122110150506000c2c41c046810700b100403c80345817a9030300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226600098 1250 226598848 226598909
    0xf03110702190b070c0f1a0a0c0c0f090e07081c120e1207021306050a06050a050c03121603060807090e0c030706050306030f070305071719060b0901060c0c03120504 72
    0x419120390b1306d0703544075800c1c2c006000d890265403000e101e003004210003043c480d500007041e40f8080c203540329481380c5a047d104800725840d03010041302e98440d010351501c2082484100c00500c4180000d122031403c2d940c0c04c2c46503601e940651020710a00c0c0c1e8a8004181d419000390301c0725140c0c502601c401009491000849800c02d5506070f000e154900c0070a482203000b4458282901e00040201b07049929003101201d0950040342d409003000340620080300d06100400140a410000608401c0d4925201141c0e001a40c400c522403c201801d1940401460800bc28003a054440740d08000c00c40220300914645000411082550903100c0c49a00084840d40f2002440c050601241034074040007022400654580c034070700024115400c40e00c020010f82400c0c201c1a40010005029102c60b80410303d9008040304011000380d54054a40e50709081a10788864002d002d410141007261005803180c0b01e0941c01c0b074103804002e00084001d0001c020081c068001d0318010800380d441c800d803007031007003545d55200203a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226601348 1250 226600098 226600109
    0x19020f0414061c0507030e0303090c100c0b060409020609090906010e10140f0a05100207050a06140a0e040b06070c090515010203071b030f03020d0f03110702190b070c 73
    0x92007a5005918002c030071119074141c0d20b08074021100c10000600c00400b0050320301c200345691264004400703042880503520981ba07000203450071380110010305c02c112851043c514104000c04a82200040000700d02540250b070035200094441640e1000c07460354860386283e60350100d80c15041150260340001c03078070f0584100001600321a00d9244081c1c0c1000403502641c07180b03429074812406c4078180b03140d010420242c002c002d95540e03a91400440c40201541d540c0c240180c02c5040107100758204000c003c80100210310f849917104540105060b00390080c1d40380101007203950111200c2035911608441c000c1c0100902040c1d85200c0f520b4050310400c02445805492070038500082c01850480f89032045100041c0c002cdc500d042134a0755800c4280c203a40040300c2c400d0201503004004194203047c56030b8058070a400400d200403005002030a644000d02c4204105410b000102c50150219420f035550998165810000a819030042d10041840d58010340c2e0300c240013240c0401400801001c2e0300032280c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226602598 1250 226601348 226601369
    0x90c090f03120a050306060d020f071208071403090f0708010b0406050406060512100906090b19030201050f0a021509160e06061c140702010b04060506030907090519020f04 75
    0x58010189611402c0002c500101c140c0d0074070101003014010001107030311410080040380390000607100c00c0102d0300803000c00000c101000c1021801c000a10142e281d1a001c50b00b05101e151030203000c000d28a0103880c0381520840ca0100118a5804040002c5a51071540d08107841100e5116500c00d0b000703007840c64203144114140b0b031001405040030301c00e490507241d280d554980340956020300c00c503020ba005064580300394031407800020100300602c140c0018181c1d901000c6040c400039000c00803c070345501c407520102258501c0800050380c0140856810540e0340e80304e1512500c1818042c0c3c1015070309180152442090360420542e041c0200d42503505809891010725040c3d100c241080d8110000c841443d00001d0400003801c58101c408010310404806c90381c01b140d40d2071655162a612102581c03c100036030344a80090820f40b900b03015040c0506819100e0354117500d0228101036030350003140300b42c6131074503690404500e562030041b01c25010009218000d5603581103102c00d4030215170142c4500010032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226603848 1250 226602598 226602619
    0x10915061416030c330209030705040c030e0618120c060402060d0f090c0806012c10080a031106070318030e0303130801020304050c0301020f0a0c02030c090c09 70
    0x218011254000ea081030a01e5460400e4051002da003508101401e040d41070140c642800c2000840c0c103180580001034850b80349004840506451134082d40c40d5003030190042c014018246c4036100003c01500700d4104603000f01e0b95010404050b4014001d0500205d110b003d00c070204110b44c1c41940354104050800030481d003d24040700c0303141c00c0074015000e03100015040071011601510b802005003640015203480001c4480201580400b1184c81035001c40d0341c2c9110107402c0004050a0022a00412100000e840301c40f0145074280c10b4400241c14403100744423801b001c9121070a81e844a14083c0009008861081e00349080c00342c5142138020603518140302710310014018900c6401648542e1000b1801817400075140c1e80c041d50210103042e00359406101c1400040700d08800708040c0c1e40180b10342c000060741c0e402c00d41805420000c8200c81c860281e0700421403a0204000e8a084450290081c900300c0c80c250000d2002a050a480c0441c85a00401c08020b103c020488c135401481882c0041b03d401008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226605098 1250 226603848 226603859
    0x61401050702150c030d051302130612060e120f03041b0b040b071412130806130b070507150c030b12060705130807030501020a08010e060a03080d020c06010915 70
    0x20301c00c044000390090f80c51076944020806410140c8a00b00240065078103002145165a0441c3d9003100c40308902c041c0b031403104e002d42c105014840a1105400024490141010580905070348464801410076a94552410500f0402c2c0111400b40711841d00b034a6941290103041e06054100f514280c50401084003006090350580b1a128119402028a14181443d0500d03c11176600487c40030340d0403140315140702e00c0da00000d01c54100402c61a81c919034403000c2c940303582c80526900760490041c5500c00d400744002034102529004040d80c0c04150180c0c0b0b580c4030340c0111018054070300014041014072481c0940806c0c1a08504d56401150380c0801c10120300b401042090111a640b203046600b0100101e0103041c0b06a000700180c802070b0304146141540d0b10740044c50000250700a070b60f265070110740c4981980d44401a1801030441c102c0d46005030a001000074505a0207103c01000100d00040f484504841038040d6200760358510280c070f40381d41e540c006000c050016640301003203400144802054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226606348 1250 226605098 226605107
    0x311010b130e0102071a01081e0c040b0d0605040305090f0108250c08160c0b0703020709091104050907050109080d02151f03081e042d08030d061401 65
    0x2411040100100c0708520651410402001c2c451030041c62550200204800300f203860701d10445034052003402800a40c50710441d1421301c201c11b280c016a00c9180040d20241c010000380326208000b04980001d0404941d00001c0d086003803111008010b5030a0204000c14990003030043c0c51003010944807420030000e10001144d50100c220b829080d110a5403001407084182001e2405580c1c195080141203071800780ca41000070b800a0140c69080c030301c1c508901040010350310383c0342c0c0249000c0042c01d0800315581e4003e0340351460b500565140b20380d0b621600c81400310159004007032200242003089a400c240c140e1944404e45405500d010505140e40040c4151001450041c458410740c0a09101240194010b1850401410209481041140000260705040a02c100851281c01e110b555403e0b58141c5000707800c1442849010301034103120400000010b070300200128801501420404000294003100c600c01507000b07132100e84000301300c00034480601d074006070988610501c40905204ea0100445 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226607598 1250 226606348 226606361
    0xb010906090602030307030f021b06060a050103050402090f0901021303210f14130504020a120506061303080319020c0304060e04090c0b0d020f0a0f0807030c0e060f04090513031101 79
    0x2c00590007000081c040c5842513101ca241e4030b040f8117016280101c0380c905010340140000c680580750b0010380c02d0000c5c030310b0025490700c0201020700b000c0c0003070320b002d80004942c10b4005140c002d03082010740028415201c2981110804502c01400e1494103440b420f0215008082e600c1c42ca116860300c21000d02030328051103072a466800d0a548004a101032280350051942000380d840b4483e0034181c17030100389c0b0343c0d40703002030101c03c0e5056407031403100e42d0b0b407600f840240c0300050000c0e4001d40040050403424000110b548003520b170800c42807a582d80314080c5410b4091081044020664400306180321805030100c01041103d01b281d039580e1521306902c0c100021a184204001d2a9140c40b410401c071085040000d0107030003141c40801410420100c40a610780d40c4002401d5000407081e141070f000d0183c20091160700052107141c100046004c22f079016000070b04240c9041c5c400d0001007107200c00e1800d400102c03006003550b10b000303202c00d0814000c1c60065154070b50048010521207040c03060f15040510484 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226608848 1250 226607598 226607609
    0x7030b06090d02061303030c1203050103080a0804050a0f03120b060c0a1101050d14010303110f06150a0f0b0a0e030f030409091104051003150608060411030a150b01090609 75
    0xd034a001000c00c100072200750008001c0fa0801d4090242054000740b0b80e864800a502a4079280740ca00c441d0324026254440e030b40c94030030a0510300001403002c42c8201c0180d48062400e4100f61021340c40d2428190b1030300560320401041d45102407260410560301c031200c003450114800d070510201f0300e010104841406000c1e1401c0c020f43c0a680560082004424861810f00703040c1040c030326000680d1a90401c0d80c03c1c80c0c50041c44017003a1001001056848031315400420700c0032003d40100418a9605038a8400152031100b02c501090b100c64156510500c0b10401402d10641c0d50301a02d40c2d0b0310384e1030707a141c02001e045030105103100b90b503c81c5424003044801c2c080c0da403c00514680350404000c10024080c40c01c1c1076509682c46d06010ae01901c50b44102c42c003e2030700c40441d1004510303600d049203001800b0b4070100f1143d0706101c0200b00d030b8800081c4058001e5400340103040b41c40d5982e00800c1c50012210009017141d103241d4658140300d101c0b03905c4454100f10030b030707111009503498440c1565070100d54880e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226610098 1250 226608848 226608859
    0xa0e060a0504080903060c0a231624050414030a0504030303020c03480d0e0609092401090b040902070c1701060906080622050106090c05030601020607030b 68
    0x40966100303500203588640f14414840c204007059000c079207010001c1f1a50340d040c2c240081d440c0b0300c6c260803c071900b259900b20566a03000b00710341c1c1e0aa00850140704029041d84c981203000c601007051085841d41d51903888201e0405850802000101401c8152000c0c0c4295010400c180c0140402100703d81c482e90840e00c407140b46c540b80d42da00300d000790300008103481140070500c01c1d5006007a40d602000c40140794032500000304064044042c1104001680e8204111000b0785100381e904004a20240c4c43d010381c0c00c0805c80c0c0c40d4a0004a803983c0f0a851120703a00949403001c01909481181045000320a0040f0a20702d5003043c1c0015105807195009484015405000420843d4115002070010511405c1035480e020343d282102c0071030003d181e440c12a5030351038890038455101b40e840745100606e0400001d00180c140000010301424110728601065404c42c49450148a030075086a002800081700401c100321170300000500d11342060300c20b58014020746003c11400d507c00d0056080d00b5400410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226611348 1250 226610098 226610101
    0x41103060f06070302120d0f1505030d0c030905060d05010e0a14010e07050c10060503011107080403020d0201050f0703020102070611030714030711070e040c1a04060c0c08240a0e06 79
    0x2c000060b004040d08900f184110000d0000441004000e0403081c058404040f81030210381014030152900d20250390310a1018070420020765400259070321001c100c034101a00301c0050307030401b2101c05010350010354201000140c9800100c10b140c1c4001d04840c0360274800c81d102e07226503c5444c29900114010b04803480070368018851540380c0c400040e040803040c10003a05d407402c01d040c0030b8200186900da07040360941d1280300b017025040a00901c815803a103d00310a05e054819603400c0c4003401035000281c0101c0c01c00c24a6401c59000d581103913440c00b080c4441580b9018107180c002e021307512124084582d103040c20012a20b06070f400c0d00392400303150316480c0c05000c1c081d4a81440c0365500010303c03132410840d0154814081c048203000010140c00c41561000c11441e080c2400c0d61010020740c0f0580e80c441040010310030b0015040243c400390f80311450100002003160030078191100c42c03900010440e003d4090941d00581c0b404604007100c8140420480c0550745203081d02c0116858401400f0b11600040e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226612598 1250 226611348 226611379
    0xd050708010f14041b0806030111041d10170a060c080103050c090c1620030d0f0e010c02041406040e010204050a1701060812040905241306032004110306 67
    0xf41d02281070042c0c00043e51440e004e4400b8401381141d50302030301150807441401518242030003039511400b1480e80103403401e8903009010782d0340c10140d003815005503214008503524404018a80e401080981840240421b4049403c1c0c1c42d140f90b14421070781142341039206403005005004090480c1e0b0004040d04030403c5401c1800300d4464001c010411401040280c4c400180c3d0001005811500a018a16a81041d20b003240710080034568140e1196001c52078100c0203d90155101c15051113034074000c1450100940180e9075460301e018020740c05410130120072030400c82108914840c010440341840401c2d12601420b080388107034011550420355882c0d061010510000007118035a038401c00000700b0300d6407000d04a003003480e02c0072000d40c4003000080c2003184549500a2a070004400005021801c041c94908001c2400c5580030078007c84a800c40e41d01c00404686c0300400450308400c4060b040600702004286036030040341c0c403134443d070b26104140301e4021407101503034400e080c080c18110351840b968 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226613848 1250 226612598 226612619
    0x90c0504020706060b0c0102041811030402011103070f060c0e040b0f01140d06060309230c13091202010b030f0a020a03060207020d050d050306090601030b13021c0603080d050708010f 80
    0x42e641914816114900010100d00e810000c181c4919100001600c40d400c19892418502d2650304121410b0304140301e0352030102039441140e03085642402c04031841540c0d074556900314040c900780502012101c12075002445401d4015010110b40340d514815003006038000c0000b1107000644194112030002d0341010554061100c504112241d4401c00d41040c2c04e41e1050010703141947c004400003a1509008400c000341030601c00030010f19801084071101c51003914680d900040940c05100700040c0d41d4070810252181d00900c400c0b6004808034200780105880a4044c10040d0365070350084c0f1408600d83c0b03421201080c04552254024007920301180f550325910081e402004c41030307902c1105030250f8800610b081001140c001070a13148c880d141c1c6046000c02c460300e0380041c501418075040c44901200c070350362450928041c103030050005032104c0c006d100725001c2134403081404015524102012041c071810102409048101c2801030126955178681220704c10380a01c146481a0303152035051210040300f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226615098 1250 226613848 226613857
    0x30c0b070504080a21050708030705030c0c0610050a0504021201090b0f09010f06080f0c030f0403030f090831061101150b03090c0102031e160f14060a090c050402 71
    0x45150082c00c15456000c06400c2c03079190907084610640740d200c0c6103102100c48085118000c96814520f0600720161900482c81c0b000500399004c1280000010381c0c540d458800361450804244d084441510f0000700740030000310b407405100e01c218519400003800345014002c40e8a07441c40b508250205919061070350b0080d00c0b103543e2007a404010a502c0341c100d034849044284c024880460488500d41c50300ba0098016200030b00f07a4520480340c102040b0380d65940c10210780c1c00540c002680d00465030380d800c0c01c80040110310a08040c1509000034281807124040c050885801a88820306440480c1e0240c169507800585152440c00540170301044072901514024004149000c000718180001c140c1ca03135281e0119801400303e0f040b0100c18459030746010041841d00c0d50003030000710314010070000c10000c0791220810110031500c0006c0c0040e442012140c104070754560100300f403560500603250080998556041c618114414400003a4000e0406d00940b003041342c014501915440c280030510000c4e500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226616348 1250 226615098 226615111
    0x50f0307091d0a0317090703020d12030e06011503140702060408070f051903180825050306090a120801030b0c03070219150606020102030c0904020c0f030c03030709060804030c0b 78
    0x40880e104420402d09101078402c41d0f00c25075410780b80c482d840030044000503000d4002c0740c460380000d00a00060b01e42c001420016904200103401102540c1421400350007540c0c05d071303940c5011320400014110300805481725050020703242485440748844040b141d100c0116000030040c1e0050004c20b0114107450014200280101d60302104600c1035103425140c10300102c00d5851003520340c01c0c1d00c01499889032000c506800503c0380091500c0c40e0040c0316940700e04100d40745080110f0a180794229011704401400101406016210035141640b840d68895404500580d20403445d550b06090142c45501c12905076a8440310035602030715000c000e007400d900300800a00a5104941e06c0002900c2072040e140081845506103103c4181900003100640b582a4808009d43e80144140300402c0d4110060fa03030464015100162203400380b1840e17628010441007c00a03502002400a05007400480218840c0040f5125084801da86140c01c50f01079030101c034040c0c00140911340ca07800140d500c2c21000e0f04510f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226617598 1250 226616348 226616381
    0x9050c07060c020c0a0902030708012d080a0c17070e070c0212100c02030412061a06030a02030103020f0f06030a0b04200c07050301060605040b0d02040909080304050601050f030709 79
    0x1503403540d03039004072a00e81184502580c09040303000b4080ca050b00e010030213040c10020035410b40c10700c1500074108031b9060041a55440010100c1c1c0408007070072130603100e18031150900010b070380c0d03407001003036211250004250b40c802088040402c000c1d004d0142c146464030303070030020140e584c074080038860660f60103000001000340307141d54400946da60f558401c61429410000c1e1007500d64a5480304111101d2030804000d5400a1004004407206c003c0d1000c10145c001d100411103030104402401c84c00c0420502c29800b6001105200c1400540d502a6050364401d98440d0268076079441000000c0041512a07035100c9010070020744040350f9600b18851400c2c000d0300210742810105e08002c2d00c002c5401c80380880b160b0100da0544d00e1482001403030f0080805500030085e00741014002480c520840c007030310b084104000388503101500f180c1e040b540108426007040104204602c0d0000a40e80706031016903662107080c001150a242110481c0c0c28400c00400814071240b414507008050000c1800194440d0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226618705 1107 226617598 226617607
    0x60a0c0c020f04020c0d0f0306050f09041e05030a020309012601030b07170a0605090a1a1203040819050d02030a120b030f0706090501020c010c02090109050c 69
    0x3403501503032484601124280810068400c0ea007000115204003000e0074000390f4131aa506404102c6913409124003075030f0301c040005944241140c41e41c01072000000c82c0003c3c041d0010303078240d900c24550484110304540c40351411904001e5010b80541c0001860903500d41e03000c1414034840b0390401c51100c80505a440c103080c00b0105010041001d08084003023021140036805030342c22108440b00464040c5032415205015240d00d2050b14010034a11011130f03422240c80c0255201001e502c07462404080c180b80403c84811012528101c1038001048042030b8034001b402803958002c801d0603019003410f070600e4890300d000801910380046400a01031035044550000c41c040070151440070109082e04007500090400e41e501c1d10150b003e128240c070028000e90042441400ca807000d8007514210046040103660500130760f600258400f00031401400300d20880d0740883c0d0410746034854142031 = true := by decide +kernel

theorem cover : BRFrame.Cov 226438848 226618705 := by
  have h0 := BRFrame.cov_init 226438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226438848 ≤ n) (h2 : n < 226618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
