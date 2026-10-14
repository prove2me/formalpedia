-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:18.185443+00:00
-- url     : https://prove2.me/submissions/0fc31a1e-3b15-4eaa-9eec-de7fdbe0456a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633453237 ≤ n < 633633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633454487 1250 633453237 633453259
    0x602130608010503120a03051005030f011407020127020402191e1106040209180d0c140609030a0c030e1201140c040513050c07021206100806040f0b07120218 69
    0x86130014050b0603141148158500d8400c0441701200038200082940121036a8401c00069a413401c010f00801c45414100000703c45000a1111190b017202420303000441e81807440401d281c40c1d045042900c1c1c014603d207814440c0440740702103400f900034500c4041405030080c88204c42c00d90031806008040483c0803076042c440a80003410f0b12040350281c14480c550740844001001410646001c542101403000285d90080400c0f200510300600000710400181040d00d5090030444444510300d10986814040c204915240c02c5955590003605e141d0710400c4240c2c1e001d01c00b45030040c9c0318415041ca010341000c0c1000041c000c0503020341200301502c03412414000010f101020980e00f40c50541d803000b42a4603107088400104000b416010b081c0811400e400c119480c0103079907111036a004211084042c19107840c008000702094045503000400c00d41007a02004009600700405504059100f4103103200780d154141c0441c1c81d030300c41040e04101c042c030018021403000807189d400000a0310860b403003000300d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633455737 1250 633454487 633454489
    0x219020c04050f0606070f061a150313080d0e06100501120c0f11070906060c0b0c2803140106020f0c0d0f022403010909031101051302040c02030706021306080105 71
    0x119800c6400d8001020343d0804140e1324030f000c81c000c0151902030042e294084030162203610841e07022002e84180d4075141840302c00d4509024406000d00c540c3c0a000301c3c1145019261411005903910000b00a00c6000941d0342c81c140c0c49500949110003c40d007150218a0310b00d180c03140d081c51324000c0c10b011618442c00d0815000703260043d20602d03031071aa6100201504010242ca003401c005607400020f0040240105150040c0d204500081049031350745070b4a075415082c1100c0245015008111003002084006100d100c24814040e882810201100030003081650890050950380d64444943c2c07403450002038125030000e41c0000c8000c0c10703810740e58540c0e5035000300b01404182d5040244902d068080030805481d2103500c0a81c00021910804d01a007044808040b413903000760004090f40365142d00c04028150b00841d403100d0064002c008000b030342013182c030100c032100144c1c00091003103032504c0c8940e044038030920603148042c0c1d1005043d515504082c0803140c0311440d0b40201800110100000101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633456987 1250 633455737 633455741
    0xb0a0e13391710090e2407020a0809121903030b1e100201020405060c070303090608130f1707210807050d0e07180905010b010905100e040f0219020c04 66
    0x1198654032401102d00d0400c02403202040000c0007a844000c007507800082001d1385010b542441700d030401c00b5040e076805851400104005156820311000386907010030114a80024882180390707000400c29803104403010000c0c008a0303508100307070007a000d100d04010b001129800400b1400d4803030744083c400c2211250512050001c4210342c10700407820b8624038003403801d1668200c2071103c0c2c40e2002601e0140c0f554041403081d440b500030078400c0c0e402110704005165100044402424a5140455030740c141082051506090018081c01c60040c1d49842c108024a1100c0d0840c0ca440b2484840d4444100c0c0c1002d12144041c030112003404020040d00726003403845910842d00c50100d03621800e007446100e10301c850081010100350310140c4a00c400104520304100146410401c3d80580440e071081903180c1582580c4c0000c5000341404280b1406110b40d41d6185980325042c00385103010000e0034080341c005005440c1c0080e980d402d50f413001a03034901c0608004840140c848550702102e0040b0f049000b4002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633458237 1250 633456987 633457091
    0xf05060f030303061e04152601181e020a090b120102071a1b0403060207140706020c13060308041e080a0809041d0607030506190b0a0e13 60
    0x42c1c802208984403005d004213000c86550b8a101a100190f40d55640900440d9410950800e070b0a0380d44009010912002c000e9441180810400080c40007104040e00800d540c250740e2401414060740385500c1c020308088440c004041c0d43c0040009060b255190b082e00000c000da5061a802082080b6000307100710014000c079021182c0c01031482504413440c0140750b20750300e400340c0000030070310418103081c14100b6081c0191000e94060240182d480d68039150480c00701801c481d0354011604400c90402c416034004c249101c5408041d280d0b084e01d0f0300754201020041c81d080d00300600014000c01c000c5076840c100b601205086145061090f4a2512a1092655843c0340103000f403081004104014550030640c010007181030031031011031030110301084e10a08111080f521180020317511002c001d51031900d0303910300596000f003940b600b48845c1000d500c6145440340d00035186c18010040d0b01c9400c592101802410300000280c020004411300003241415040c1c1e103140e95900b1400440e0f10112800e8109640c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633459487 1250 633458237 633458239
    0xd1d04090c09050c04151806020120031503100b0301060b0f16020103180605040b011e0b130302030d090503061503030a111e250303022107060f05060f03030306 70
    0x41d08079464980d028000d004001d0031500043d90600c40042c000e1072556540c41c1143c03c0d500c440f03242007140e152817501403045038000011607050200e5900d01d00b144500c07500610340080c540c08d03901d80d1441c400b0024804c80003034450305807084000c0300e24a0101c81d4070200f103000c0c04030024400656070381c03c807000d0740c040e0300c4030010401d108001011020100081b42001c0358810b040124071140040d030951818038000f00103442d0745498408000402034881c00c2580544518404001180070050144030020164001c0f440e03034400001340e00004000403401c80e030045038010211103190349040c1c402400700c42c883c4281c0b8047e205060205c1c070030302d48500d0b0701c55403084046e000b1410302070018001c60341240980806d82e00d0340104198280d40d54244400040501c1480703000704148030350b81425595a41411300f8040c6002d145803818400250b0101e0340103c1400744c280111100c10958644400901c600d0100800a40c503204901d441c13146e4a411851061000f101e4515a10381581d0906440340301c1241c8039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 633460737 1250 633459487 633459503
    0x305010b0d0b010c0f23031602060903070e011514030105011407150204090618050f01441902030c060a090305030c0a14030a090b070f050d1d0409 64
    0x100c81c220039900c034400d1520140741c0fa240da12020b8445d20958100400b09807041004800446000c0006c0c0c170a41810400c180002c40c03400000d00d0b4000108501c00348000e20a038000101856075a07000c00816001d4070700e8440b02c00c650750b03440f00d581e004d035040701c511744010645010020300407501e60381c00d4038120f61060b1100c0d20030080b0341c4080002d40d0320090f03003240d100c4084202c141c2520f40700d102600c098a00100e0004045040004c04c3c40c081074442c140e06602030402c01003007004040e0b441c039641100d11542c20134001190310780c1d5100040c5945c2d8002d841c801c07140b8601c001c00c0c00d200c019601d0201d01e440c064905850010402c1081082500c0002e9013540c002c02000903c0c0c100040200705150541c900300180a8980d9070b0390f821030b400104880c11551051080005100409424104802d04000150310b0050410b1002c1c04010540c401c4140600c0c011860310280000411141e4900351b100b002e4640c80c000c01d600291005076006080207d038400380240c2102d5007070a1141d40c010301c0e002101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 633461987 1250 633460737 633460747
    0x8090a030f0309150f0e0c04020310140114131d0906041b17031e03010e040b0415020a090e06121e03071208041e030e130b030a0317070305010b 63
    0xd030082c00d546081204c11544034881044054068420304015881d100c1c004950031038802c980740d01e0901c0529100d0311451040090100d51405075000504941044400510709030751100141c8000820252140100f54006400c0c5510394060728144140c40c00b0340d00c0b01120819840d204940d00304100e030b115116512000c0410f011030352000003803208c1089090101030041d00e03011203042c080e5000742c5a0015030b10100300d000b08440c41401c41806801440700482c15589400e4141759400c0d0007900c01b520360603040b0040b500b441400040101c407141448820355440036000d9006007000b4039441005180c1c07640e41c0125007540b400042e214540400c0400a03c810715440c0080040311045a65000a5100401039140090360307090782d030b00c5400c06e1500e980ca107518040c240030074482420056070018128074800400002d400c03c411550301d5100782d17030407100b800e1542d000b040107014a0040550500c5481c80410406034130900d0316403101140400c204040e2180b841c107509030703402030064014804017444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 633463237 1250 633461987 633462017
    0x210030203070f230a170c07050a060b151903050702030f0d2714010c0906090e27010e0c100906050a0c201f09180b0301020c01020a08090a03 62
    0x1081c44000f000a29044100b202c07034584c2040c10740c0210030403404039400341003040103020040720050340a03a80c01da803603290105950342c09440c1c442c0d80200412596a95130104401d8071900d0350240c980720044041d03503a0b4210a1003a0202d00354904007440040c1c1840d001030314452001c4203852242c15a50109400d003284180c600d0050043c0100032068a50f4502c031600c1c0d055003915209184502501401d501c0c1c00c89104440c1c04d4884030001a03080c410841c3e02004069804000c01d000c4400c510311001017502c4107800c0b050411a10b010303c10038894000c8030085c4560040d80110b0390340300d0810403034001d520486c003482540c14440340420b0126681c548200081c6000340d004264a880c1480c1ca0580141c0a541c1c5d40304011402c01c19084040e0b00c0384c0055810309180d888017a8903c2041089503501c1c1065000811144140c0114a6030900d64804c4034200a02500111802d9a00a009644075104240b4041c000c1d0440540c0e440080c01600c0400c503200b5003c50294080da402d13503208003017403000c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 633464487 1250 633463237 633463247
    0xc01140703050706240e01030b0414100c02060a0c08064009120c15020d02040305030301083405061c140a0501091a0f0604120605040210030203070f 65
    0x14038240c05005003040744000050b0036104035000004000188015081e50504044241500c0e40084000280c070500500100ba0803204081d032082c0c2c0488513070001e00d2031140507428002c0c12000303148401c2c1030820802149801040440c8240440c1d402000300528034171f8100c500340340680b10590040c00d0212804010701d41c0d080007080b2032685280e03c2a007090740c1070000703051006000c04820095540c00213801013091070700411604920514085052400c00d480e10206850109c02d40c9100356070005401e66105100d4054900442e0854180c03516981d40e00e8560f9121311041c1c501610541200c400300141c4081041c00640e0884410000f94510b400d20090028580c010002c03100100d00c10f03901e004142203280602241080d810580c5841410803d4007481504c1041e00300802050406040d0207180c02014032000c8058800c03100580301848510104da4584901e400800030303003146902071003d00103260802802a44256801c05030591030381c00c218102d0200f07541c640006032080704400700492140d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 633465737 1250 633464487 633464497
    0x2040902030c09010b03010e01060807022a100201050a0e0102070b130206090406090209012a020607081308030a0e01051905091302041706090706170a020432030c0114 73
    0x1600702c400005103800000d0f08100260301a002000d8008010f00451900c0341d00c1d00d0050185080002d21410403e43c0a5200c0000c0012400844529546050f08107501145481c00140190290402d5004200000c1c06810121489000c0c1d90400360406015801442281c02c403641100202b0219200d040045100a00561703059034055814005074003d07941e944943e0008010003c40144c0d40d1103460b00140c2540801c440040e90722220116111100604035207004181c1da0440c0c03516030f035420f640b50282150252000c80c4544d0312950401085aa400000500c040561500d940b140226908011905032059088501c0b00e90304800c9182038490040d400380c03000c80001000c00d0121102503c11000300c1c0c01c65400f0550700c01090a80000016040c0046e5422103140d101524086051141c060680014407030030f08004a8040e00042c07074100143c0c1234034040d007100c5400440d0707408581d10346900907111140c11440d294003103816031010f2800086d605a06001a120340c98100742520888030300d0b03000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 633466987 1250 633465737 633465739
    0x60319080a0207081506042306010f0c05070603090506280c021e1e03040b09010f02070e04240b090a0c050f040306060305192f0d0606080f0c0a0302040902 68
    0x38400d00858201d205024980c004032822820001764501003081009454080c83d462660000f0b000c90b000c100e45c032007008250700c408282402c02b0152080101251000d220b81005410350140003000314255615401000c0010f0058046440302d0300c801c1c90048419101c6610141d0f1665041c01c0171100e81404e82003071070011040c2c010783c0e50030781102c3c0400e21200585612005150005000d08010a8800040d5215900442c0043d0309190800c900c3e588240700d0b5151203418040c03101c2070400c15502c02c01181002c0d04070002085d20380c0c1040c1c9402e511251100300b4400d0030a59920411401340d10501c10950080c10060211380305849800310300009000020204040040801008240c848031b00000c03c01503110301c00005545295081c4641028030100b0b80442d240706811016012900400441c0c2d090240c455001903a030340389000d020398203140341c05000d801ca1580c140000034024250b000c5400c071075640058841091034100300c25101c440c085146c0f540803200304402e1016082c03640c080305034644 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 633468237 1250 633466987 633466993
    0x10501080c070b0916080c0114130302030307050708010b040522170f0c19030c0b0a0f06080c0307050f220e070f090f060b030a020c070b0c15060319080a02 68
    0x401500c81c801c40070811140e04c03c90780d0000c0030700c414513540c0600200050601c40e021b04914011500001c0810b41c189208031101030b0042200c1c4061452100c1c20070045a004040b00c0e600d001c0d500c2d0003522099548544482c5500e08112041281800d000381d40c400d8103540200144e894022000b00e104d400301010a0f81e5001c1c0c0d04044c100e007490140003c1010312001490300c3c0d20340002900052500302486c480c04c0c141d4031419558400280c02c5450140c0c42d99115020380301d0f507503400301a0002420b01d00c42e000420350a0500000c0d080f0404070303151040c0740c001c2c0c09591056071558184851300c007005410301c0d04090001c5040345225000965403d8035a904000410082031588806180440e83e80004862903100d40c0c0030002d03040c0611968102142003581401440e01d89181c006070b40c0002000400401c1d000565040010310500c103000c0580000c08031191a0540500d03165602c81a000b07200c6883c850080c080750240c5400551444203850711014215022400c0c0e60b124a150400850501944 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 633469487 1250 633468237 633468247
    0x100b0f0d061805060a060315060f0b0f091003020a110f12090310110c160608060d0203030706060603021908043f0201141f0308030c07020a09090b0c0f03010501080c 72
    0x3c00030f0140900522800e03a010402c1821818180c10342d15940c0840d0004500e454410015900300d13001000458101426481c0c8074104c1c0e80b5a10030a01c5002f8480c6d500029003105003650750303095400f8007203141e00c1d1b5584904d40f40a9580d041e40e1403c1544040c1d141e5403124441c5d46804015400034140800042c0a503921043c0041c0c3d203209450800f807080781d03554004903100080f5601000740700c205421014142c0c1015103064000340c00040090441c1d40684c0d1400421020343d01c0400865502c2d50303126904000c03250307485400500175000342c180e00400e40d40440301c3c884d045118045088c081c0d6008032840c412030340503800e0f4004076801c0c0075644540180d00e400c000075250a594a242d0242c0d03441d00003103986140c070360241480c40c2c0020b013002e440070fa000d105080000c65010800781540e9105000d00e50b6621707803030751006d2640106a802540310703002101c045490000c64000307076903041c402d4110007011340326010000903d00903805200340c6d8100900c01049550302c2050340a81129401d00898604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 633470737 1250 633469487 633469493
    0x6050730112205030d0f080c090406081005180102070201051b07030c060c0302060609070e09040501020f160c0b040b030c03040606030b090313080706020a110f12100b0f0d0618 77
    0xc408050810254040250400c0003035013028022018964050714049603010740d000c9020300040c80c040e00c03808101c40701064001042c1c0703039540041c000e0000f01085400c1a1000d11405018040c1140d00161850118030ba00c16840014020b07240c040b54140c407514107200c40c8a20005160303d040d10317810301e030b4072580030000042030740c0d07d08510252450f07503941d0802962f5802d0181c40c040bc09044907026a56240c2004100782e8410b40079641a00100d901071a1601d450428034003a01034259144c550410005420912068840408084c54810009284501d03030300c03a202d1506009520403584503900030800520b058881c0c000844d03100e44a100300060740b644070303240c06079002001c0390072403610703400010307555420030180c10341000624018000f07098980c02d2003402516103000a10046c51b29921150403c181c1d0350b94130b00032001c0350307010702170010107800842c001d03954183d41850310b0b40d02d07450007461041a09080854401804025000d04048050f40da910001402980344281e4041520310402c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 633471987 1250 633470737 633470767
    0x21b04090b07080a0605063a0c2d0c02060a090f090e100b01020c0f030c0607030302130801020403030912151103060406080129060c06040605073011 65
    0x780b005951080a40c0c50911080320441c0c60381d4014030300c5242d05002c920a00050b6002600c04e01320601c078100d80e0000c440c0c8481100c00c0c421705018038500c0c10704205150045c0c1c804810034442030910031000100c0301d4140c1c041030a071203040303250001607019858003002d428074000a060a074a149400d0001030303500e80301c1e000c218840307410200005480300c3c4410078500e001c2000c01c10151124504104003501400040c1d03940c8940b031035590084800c10844440781c0d60910000304088005000345a90700c031145401002540714548503500c0302c0c070301c3c0004501d412051003a42e040c2d0307915407034140c84241854850113180015a6085900070300c40004a8030182c00d901481080d00c90007403809403a0b0400d2030030441680c000d03400c14400307a071401c09580c0c0104491800e410b020b6412540d0459400440d5010901c4c81c803030304200304054800c4000f17100c104040f030350209215401c40e94800e07076500452261260f00c405140300307800c414595181a425015501d900030b81c00401c03008506d40c41c0103030140200c81 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 633473237 1250 633471987 633471991
    0x3040f09050105120c09041104020d06090e0f0d0c1502041205011401080318090901090f1a0f010e07110f0a0303270804030b070c020a27020a021b04090b 67
    0x1003161900010441c60520101c034107001150365010340060441080410301007900104044c100c00344288a144450304d4950482e12515007891301032040c1a02e520004001c1c2851080d805614810122410304148010070b0042c0740d601c2d65a05e861a0070041c0d101d401044a03690b82d0259859420400055075005a401c48a4024468000400d2851150228000b000700503404118103410410030388182d03091140e0780002c040003c498461003038440a8078036006146c0c90000410003c0001084424403510107079120800c1e01524640881e41e460140d05c041101080c40365034051210b01c80440ca40d54003070480329040000131022225000341c4148003e1806d440f20368103802080d62042403880302c80b814581f00003022500b441c0d668075a011565071004911541c40058401403019011074a41c900c20b600460895400404c1d5103101c07600c0300301c3c800701100c00003400407403030035429100e040c0c41980e03009a82d0b04000503009030581141c012a602c4035032030003054107940315603200798460000c5c40b120940e034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 633474487 1250 633473237 633473249
    0x803151f090902040f051302120423010c050a0e0111160303080c0a020a1502090901270c0207090e0a02030f0c1003110a030c1704050d2007060e010203040f 68
    0x14000c0540e403001c0c1c5066015002140102d0041000780b0443e601c11400400b1103005032202c9412032903141e504c8009014207a03501c1d59100300c2c10184018000d43d1113185070a0000300b40c0603a1724010808406003210030100701030004c00c105103e0200c200d40100e5034183c455006040540001c07008400340c60820040851000441c40005003c1c018140c1c4112039581c0300106c046514600000311501940d2400200c00041c425500207a8004c0c0c01d000b1038044c2c40f01c10002a00762001c65840300c00040e03980e10010724034007000904100d01c000f00100d9020380d08040c001c0b6005000c2190a180c003100c040c003104075458030148a03407558040140c80c1000748010301c10281016007083d41174441084181001041503804150610301c4d450a070002d070b5002c80b039280409040010303500c01012002d44410b01031541c034100c10182c00301040140f01d4045140100704c1c2c85682c0b54140600c9a00702c181d80410005040301f210b6020703e806022080c000c0d0754200080c070050040b20704242d034540d208400c17012680c00407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 633475737 1250 633474487 633474529
    0x5010809240702010c17010302150d060605040e0a09030903021203070807060212060d0317100b0a181d01030f02150c15131a07030e0a03180f12080315 66
    0x1002d15a420721170460312002d6403801c60030000054000518901041c000648a0b018a2600d603a140307a6820455514058040e401d100282d40c078a005007168009204080000c8145000121441d0086c482d41c0751242e03045e11030302403c0d800c44e028000d220180840a0ba5140300401c032000c00b160648010380780e4144110800369a03080000005001000098011801303000c0321000040040e8001141318118202004540b4190761220010320300c52650703500041c018440006d20002541d4401e076003188416100381d1001c2c0700e656580201c06288002084024210b036058014800110800c2101811500003003480700c0c0c0c0c1d84c500014030b9180e03121543c03080959202441c3d14070400821542070398081703284003e05418030000c1c1ca415003803048624100b52042070710000124410300076801114401100d10890303400240134500a00000010111796140c40900100000c00e01e5200910400380c60050400342c000c1c11785036803850301c6504080d20400300e0504010b0f8840d0035890781892030135012407118078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 633476987 1250 633475737 633475741
    0xa11010e2d0324040314030106120b030f03070b0c2101031412040302010806010207090e1b0a140d060902060a030501030312060f1502010e010c0801031a010f0501080924 74
    0x1840d1410350348101c0140690007144072038000d4220b030300d459801c1c090604981c11066407180750449039901c0c011214158032a0100022824550044100400c1142c0c0b50b010032030b4145460800d1780e21075a0051800c003a9000300030712400141200388607900038210300c402034144030550080300214401c030091031420325040c4c40100140000311113405020303440103001d01400c2d00090801c3e4024465800040d0500c108600421900e900c01c01211004180c64034081020450001d0f00caa00c50070b034815500680c0655606154451030044400c40484e00c034400e8008120010700300b88001250b40044c02e40742540e403092090b016880c1c400003420480140d40e4001b80c60360462030050100003550320080308040c546082845040e04914000c0c0c10703603e840e60807900014818030304034003400040c0004019542408034150031960440c1e00759044c0ea00c592030b205020180c4040785003051000744180e181c204000c1c0c60411043d402a41c449400060390710079204003000181400e4100320044d51048200450a82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 633478237 1250 633476987 633477049
    0x603030309030f0e0105030a090312050c0a02150903120c07080a18120b04110d0c08150916060302070f021c171c0c090312050a09170a11010e 62
    0x20b1a440f45509041039070190a501c00024a40d00000349021591940c541c021004c3c90b00070f000441888212400903c42407420700c90380c01c581d4110701e1480e800752150030001004007001300503180c4507414080045040841400503645451405003410350b0191041114001103040e4400900464030f280c0c8892030f2804030060142c3d50036002d40e04c6052843d4410002a000400380404580c2194020305450261180070000490300c84004e1300050100e140e60400142401e00410980f210341103510071081280d841e14050343d110510449850003c0d14100d6090003418040d50207400310900070042c8081d203204640c0495811140d14414006201c05481d00004102c00004024050481917410609180d90020070503850444411981074003078555140300006845051031400a58200ca03c480c4c684007500800303801940701c0d00c44440005d0704d0820108002d524407a103494a56000e000404501c60075817100d040003120010414108004a0401449551110210800b0054400300c81820f05000d071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 633479487 1250 633478237 633478247
    0x20a0206070306120201030c05090415030510050601050706050c0403080f09131b140c01180506070e0d0201050715050a020c01061502072904090509060709080727060303030903 77
    0x4041804260500c0d0b01800100c66100c1c10050817642800d020450010703100d801c3d215802403403d400d42041c41c2120a541d018080c0003480d040ba0701480030340b81e17101d840100100544000310b41c580c1c0860020018440000c0d065400b890f0f0010000342c0060030b05851781c0da04803403039001c4403882e807161a0115a10b2103501d0024128004100180410040c9000d0003680e42c140b080840e0f180002e010340c0e4646111000190740403100315458000081140007500104030714000300190069a59100d440e00080085001d406c44c00d00303a14008000b9400c00d81c0b640c1c01160700d9404032104403800400c15004140d4081107005182c0117501c1c800c000760722032581200f183e0840c0d081d03030b202250442200e0240c540203a008905101a100b0400c00201403410868a90065000d5107103d50707c815800030340000ca44000c1d900060240b03a101d000c1d1100c9403103464044460049902444402d900880000c21402c2c40b030400c0c1030b05500e9043d02144141c2240d8a14104848141c3c1c002e5001c240c0b58080c0c041015404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 633480737 1250 633479487 633479491
    0x40612020d11031506032506030209010203070503130608070908031c02071a01171204093306090905060f120c041404030f0f0f1b051605130605060702210a06020a0206 73
    0x1000000078120b45401f5154841c805030304c10b801c280f5a0004945c03189920a004644680780c100040b20740e552800ec403800246071003440740c1070020700c04102240d900381c030501410080313130004002903080c0141080c3c0300c5032190441050040c101da0070480b440018200c820321040c0150401c0c500c072010b41c903100d00c00722206042d0062204030b4119840b00000000c400e0180c0f0705441880700009074510801e0380d0a040900c9610b2034030240c4a0014241044004003050182940c0f010341c2d40440c0341c0d1703a071200501561025188580e000300100c0700c09660342041c1c042d100040380c9110880f5180d0520380089411111150035180c4c889041e04100000d01d9000b16282e800d880d0b2501d010a0007890100c4003c02012004600d041000703458514090b10080700f490345601d00342c0000540d00c00340024030080f10303080c0d00343c45128000c5001049541c01030b0a148124001c07684003a102c40d107090160303820003580401d02c100a00c1c9203031810290300b80e210410006030b100c2d544a0500180e41d403880642c043c0c900440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 633481987 1250 633480737 633480763
    0xa020405120601260a140a0804030516050f010516030509060a031a010203070b0c03100f06080610030506030a060f06080303091e010501322706040612020d1103150603 73
    0x4030f00d031525403a00c00040b4100c10a810240d03d1080488541c102d5062012070003014000048c042008401d000e00072603e440404004c1d00c104055660f10070034000c0507144045050b0104400344410050545c1c00014600841c0c42464800d180184080c00a4015004004543c0c0000e51302c0020550400140007400020002400254100340465507100c135240710091010542180100101c0e01c00702000b01c040000c0d11000c0d100f01c40caa40c403244014030010342250b000788200c0465003540c1081d40244202c2c1d010380c4028028041340e600949035840600720b1150079860740c0c0d60341c03500065411001c0c40514010800300f00a0300c140e80994010b1030030841c21030341e001510703450300004000f820074001030340e2501481407440c07100400c468030b00c0c104006203001d9001e0300322500c40d409901a200400c3e03960a5004d802d401d0351810b843e920140000c448403409101c0d03048110210384000751500c41003090000303109800201d014603005020a081c100c2092070515000b20107428080a0b240510000001440b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 633483237 1250 633481987 633482039
    0x1a070216060c05150c04061d040f050601020c0d080318071d0106081b030403080406091b150504351515010e15180a120c0501050301031205030a020405120601 69
    0x2850034030b03142644960f115890030f000c3d09000c1c07900545144040c041548e81d00030403c01c40700807915040005400d00711401c074018014031a01117442d14201c00407900444e001003c1078150750311885c6040410070035030810009803140391400220119011001c2800e1108010401906e5140a0020745030000c040d02c12001480c6144800d0710340c080c418103995000343c2514046009440f00d003046801040c0004029140307000c2800c00c172216040461050f07003251424410f4400c0500440c404403401d01407401101e8619107000890000d030304412680c5047c01c0306000800e09040f034182c0d03015180c484a4061410350a8003001048050b0901a40300c0c60310380710a007040c0d56078071500c80010300c2c0078041c1455a051404042034003175040711005c400400d00c034009800760070341980380d00501c040804c1000c02250042501900860154410710030383e8101d83e40040e1880c0040c0902d10300b903510740c200910442003140d09100005490765080c4a0111803440b507005400036504020b0480c00003446440d0052900c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 633484487 1250 633483237 633483241
    0xe19090b010c031e0504030f030c0506060f0a2d240e1309110303070303090506010504090f03080c12070c02090a2c100c09090b010c1a070216060c0515 66
    0x240c00904020120041c1c0c1218440710540b04c02c00d0b82c66009030341020300420702901001c410590400f0685480a0003542100c2072695100104100441c104580c0c03600721182d018100102c0d40101c0f60640204403040720f480c0618103d0003244242511503000c10b00030721945030130b0180c001d01c420940115001c2403902074600e680c1c3d100461400c1013130380400c2c0281c0c0c0d41c0b002a1400d00200c450191110340004055917550303003550030020041d01c1d50ba00292030354043ca0000062034076140c030450426580c040e02034000c50720192130a5604030710080c5481030007030041001c44c41038002034482034860341054a50340c01840190060000301e080040840907940d1800d400c0700011501d4402d0380d609118000c0d591811038203028041c90518003d007404d00c10741810f24100109403600711103e403050b5003941030b041103161352150044a9809148202400c00321940b440c141043c1d0700c0000305981b01090f401101e000f150545000340c10aa03459015000240940d1040c2c02002024000316841c1d031600900a01c241c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 633485737 1250 633484487 633484493
    0x51015030c0906110a02030303010b1201090504020a0612090203060112060509010e10090201091a0301150201230717042420031911030f091f0b010e19090b010c 70
    0x4001680108400e00c6481020b6500013501005002c0c0d2240e4081c06880d141d503035442c0e205880742c108001e00702c6219850400031544103114411a44155001402e0701c3d40c65160801c140d42200b48061401d461076226142100940c03410803c86000386040708046001d4440b07403c0190440300c000c0d0030f941c4a64140162955915400110503038141c4c640640041c1d0b1441500c01030310624855030001c41e132001003445080f503400034031001e141201d50f0321121078038044490508900b01e5041884040900c840d050013005407a104025042c0e100045081c9289017803180301900c60072010465040318070400340b0407949032411102d040c42d210072210a40c140004003080113440402a90044074070600c50020000601000c0d101500040c0320700d646038200025102d107070510b4500d50045580610f6024140045000e000000030481100100b0480c810082007034904544081e008007020a4100b00ca1200c00d10220395504400d84141a10310f940318079038516002e00074003a87c0d0044801414407164608203008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 633486987 1250 633485737 633485747
    0x7030b030f210c100905011b1407020a0503030c010b0a060f0503040204020f090d11030111090f040e010b120a060b060703120f060308121f050307052101051015030c 72
    0x10340c01e0602e81c2c42840495081c01c0c2605800b8450124160348a6a401c100c8410a0340c3d2118000c54020070013030080c5c1c101c4440d171007004210710030500002411a5140d0325840c0104000c0d03c0d10901c014000000c042d03940c80000e1030741c1c000b010440007996480c0310b840d43d10b140c0381143e50000c0c842c504190b0382101c2030740d40c0070f0200c3c0030040004c0d00654001516610000c42035003204c00b02c6034001c0460040c81400d081c05001656024101230181d0300e011004141415a8810b840703906100522000d000c80b0203a041c0005040360500070f100947d02c40c008508541d5446804a9200485400400050f216030808500355206e04a4150056030104800350110740d2120782c21602c0184c0120200e8801c1104601030024101548040d00c000008501040c03480b081552240c0108411400c8581002c844804625007d81c0c41c480c0300e03415031100c44100702c00d04018002500849040381c00ca00c000840005150a50703104441204003c0c00d46130003030181003011030111400a080f850200801200c8140c0a40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 633488237 1250 633486987 633487003
    0x20a0305012114070302030d02070f09020f04120203070302040c030f06091b0c050703050607051b0c010516020114070c0602120a020a0b090a060603080409110f16080f040e07030b030f 80
    0x11a0b0902d4001900480001304848402194041e0071140324076250180252100010300601d02007800c2e03624005602000c03402a100b105a0074807045103810b02d0100c8008100c000700c14200c1e01400b070b01c100000946e0726031089915a034916200030031001c484076071407004c5415580110130b4252510340c43c2641107080030120f860004141c00c0c0388000081034200f0b00e1500d11590310041c035510407a401c0224642e8860040c4c060f249440400941e44a03139111003e8544610101e041d00050042c4101c0c0a07001e5110550303440d850040c1442d104000c0c150515102039409000195607070188560b003000721036810031a41040c0896041c2070f0f400d0100b441002515914035400c0031f00f102c480d01000c03034284238041c00605131080d4088001c00c2820f56038a008402034010384521061079141010071406585000101c5421b01501a1400e02e00300d2420f11a02910f0340d900b0b02515084020b004000c12500e410f0028005005001107890b443e140c0060001d040d101c103030401c0d90094112982440203040c0000c1c81007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 633489487 1250 633488237 633488243
    0x609050a0b091203121329041b230a080706081501030f0207120912033207050705030d030905030901140c031602090a021e0c070302060c01020a03050121 67
    0x40020028502a03614601848840500b1001d4202c107101b801b803119503a0203040380c41042146404100107143d40c1d6600b1401e00001c848203503020004001aa02e00e41480d80305d5410040783d5485c50319150403003408990000c407544100040e00004c031182c035141c0301e26401080003000400030f05060410007490401c01402c041c00c405910252444103a000350084c00010a074803074115210344103800c10400075025440134401142068001168030488984401195901500e81c07600c200c0c1c4a8850300071145000a1700d42100c2002454000030082e000d0003004010b00450003002120704110805040008446000c82894a04218440042c0c00841582c0b01c203002400d0030100b00d041c840040c51184110b0301c001049002c0000c4d05000c19a034088500c1c42c240c002c0ea1052096514603090b032040707200b08009180580c12204c16006000c001c48002d00d0f42602210507191001da80343e0208080b6040240c10000594021070000c0200343e2510495004140458070b0408822640340211201e0b44d5650000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 633490737 1250 633489487 633489499
    0x1050c09030d050d0b060f070b0c0301080d0804061d060109060f051305190e030a020106151b2f03100614060d060317041e06080105010e0420040609050a0b09 69
    0x19000d001a61342c88170314a56805083e0035500d0420711a10201031340305035400c868110030400400c1c6008030110a8074180d845e00b80c02846040c024060650b20340d40001c100b01ca038280c54802280b007040860181050b5006498010301071541088041d0b01590b00071b4104005030910f01c0820445590350300c000c4200c40002d40d40000d00b54407180c1c081c4800c2054000499221803c00811460058000000f400080c40320b50080103401c0d101c0890710701054102c104080004d40c42030359144a000541c0c802e4601030b00c982c4280c50010003802c803000540e2180300000c51141b02e080072a480d2820103104034064205220004c2101c1418000114410a68600071314050f240c00302d43c1480d2403940ea4001030245070085c004142498110f2074925065115008940d000c0400c0104c10840e0b1841c9079402d82526501c0e26030700b1080e0708280046601c414403440344c551117a19110b4040b007010015052144a503104803480341d945050901c054502c080310f5003c1d074003644007200c08010f01441c550640328402412294 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 633491987 1250 633490737 633490747
    0x609041505092118210105070503040b0705090315070903060f0c020c0904050d0302030c0f03070c020306161e090e130218040b06040c030e07030f020301050c09030d05 73
    0x40011000250105000c040c5040148002400d0008501c41215a41e07940e1105510301e4100000150040d500104400300010203041c125140480301d107000710314810040401c50030780080c00c5007928016203130711012403000001c0c031090080110b40c1580c442c025042c0b0b1441c2c80c0c0c070300000c299190000c1910340c060030402404214400c1c4a070312600002c1d42c1203079051001d8886603600300024241d412078a805031180c0c0403140aa4185100c00314840c58000010303001481c10103005070043e600040c01c490350101c3c10000b0044030901c204c0038600400c06581c0306141c610413481403514042c0050300c80b880035007202ccd56148107194007207131607127410140e10102c04050020500655008003143c11007111101104204808080c0c1c11440c1c00c0d240d8002c55150840701181c00100000303410544020b0a1030b98080002229400c2030b4018481003000ca1400041c900b0a140e000350038005960070032103000c20f000c0e0070042980350034002c0580001182c086a85850101d000203070303a490780360202400740800030079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 633493237 1250 633491987 633491993
    0xf02041d1f06080f130203030706090302010f02041e05090c09012703150c0905010c230d0e03060c03010806010513020c1e0d0f0801090e0a1e05100e06060904 69
    0x120324000081d141c04480c0c401912407002810840003150415514503030413002400b00c0358481304000003a41c014000c1c6150500b5512504050014804194155034030303000d2852103a903442c40100024501c0017808085000072080008104c541350344050700c81c40701c9006001c40f80e41084c0c1141d000d8482401c0040f401c0d01441da01980c601c007402c000b440d044500200000034040145c00030541d003550104200104000310105565041076401a40e00140e041448800010101120701800b6142901c064450f04071070f84903a03207400c89448000000801c500c075410031506042000390313009a0365111040c1550304040b1199540c11051140781d100d604480032140d04c8804950440340e203041103000752040c4c25000c4481c520705008079030100500384240b04440c012203101d401440e07021045a235a541250b482e10a048019011040c5208070038084c5001020008100c981d1001c28918680341d0300001c4262400d1084c10041c0607481078414a0502d5901d4081c000c01083c1c0a904c001e0841d9841920b8990381 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 633494487 1250 633493237 633493261
    0x100c02041109030708070b0a080720010e010c052107050d050f10080d091a0906071a010f060f201f0c14040b1e03010e0105040f02041d 59
    0x100010303400514000d81c1040e0000a4001000b52030003e03000c0324045a034a82c036803581e5038a24441c414540c003050040c0034004d44100b8465810150500d02060b03a0000394545942e01c0b0484c95107110f16a640721000402c0c004e0038004c048640c3c0c510b0911a00700340e60f4000d0301d0301c3c6c455040071900a401c0c00000164825000c0c0782501d4429414240820003807078500c200d4000f101d0161250441840c403540c0000d0803c5000660349810b042c1a0746103104e10703181c009141d041c2281000134000d1b900090005550b2602c0308000342c00c4460003202115144180600280f01462040c1c1107400e81040d050001e2000541082000001803501c0c0707812900c017210024400c441072201211904240141d02c0d01c4029115403c02c504500b25204c1d00c100408002100f09030340700c9400c00c08010a08000707010400c4103c10040140c00c50444d6018250007011030b01d080030609d54800d070446880218100c0050125051034421000c0f0800280300031481c203030904201d401100401d07009607002d9104440080c980349800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 633495737 1250 633494487 633494507
    0x907020a0c080d0801090c02031905040911120c070f0f030302040e180c12150603030c030a12181709040e06070e041a01050a120209030604240b060910 66
    0x8040003503400d4032804900d0301c4840f11000100051240c0001040d084101d1040d402101c0f155001140707461121803507a07043d0703046500c2b1501841020721000601408034021080c204a4500c000f030f03962070903010182001c2c00064130b00c000009040c0000d0000402100078603d8940e00010b4400300c40d201c80c54210044c0c40307550040b0b0030007400c07842400703158410032840860403843c0c5c41c16900c40c1c20000b414451002c0c02401080840d500a442d095140851031442c682c10030703000307410303a49803017407040490746558018016240090b0b24900c100541030f0503440360402500f580603207814001c20b15104c51038403003000049012030039000204518603540d21b51169000202e6035080d9200b61a00c80c1c0054141c450b8045154041c82c104948060481e084268001e1002c0b8143c41d180e08004100310304913500c0388504040c0b1006a820002e80d103040d6400c101031840385121700b940805014084001d411000d071503440710f841503801d00f05543e01035035404050350b504450550742001d0f01100520126990155 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 633496987 1250 633495737 633495743
    0x303082203120b1302030910201b03120f091b01050904090c32090411011b08032d0106110c09040b1506040b0706020901091815090c0e0907020a 63
    0x31001407568840321900514452520031054482c402000008c400a44001000380e605a50144030302c0c0313203400881009008500000d41d51454150415100c0f40c0c40c0d640884244130070642001b080286042d9441045a070203c03086000d4500018400b083d10341408100100906005000c60343c40901d0f00c56502c0103000c642c102200b40c00750f030350700c4411288012039018101c1060034010b003441d04040c0f00340130b00364001801600c06549540d86456040f1003d02d0301c025181006404d944000b280d042c5040a40300450048810950760b00380050400e0b42d10b008011303010080c481c040da04a0031841c0300000c00b411a0703407a040400c0503280500c641c2d41401d2030080301aa1005045080c0014043c1341c031120380c421030129102d0228401a2400c0000900891283c945000d00421290740090410b8001c0c004a03003042c10f11440700c5484d40f101013540c0c14208c125031010f907503a030502c80f8140d18502c0050000c03d2880000c002c0902c0381c0750010302d1003c0000165028038909000300780076074400c01c6202c0e89650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 633498237 1250 633496987 633496999
    0xa090807020d260a1b060209060a090612091119080d120e071203030f140702030306010305060906010e0618061b0709050144070303082203120b 63
    0x401854074240d004440110000c1c0c3c03030f04407000005001082c03c12920400000c4d1a18420b4003000b10f080701d0020a00e00302140c8494090000410b2500c0e564068805580c103511941002428888011301c1d040c4c0203020301004505102c403010214000080000d00c002c400e54035005030702424803011280100755440003074948030b2070002d0104207900445030607210060100038804a00341c0e80003a60303546c0785409603405640c12814a9800207019034044c492a0206440206102800084030103440d6000c4440782e0140c2c0001040040710360b41841165408003088600f846982000300008003402d1031107075814000c1704001000700000a0030346c0c1150000310b00400940c1e550101e0300071079100344141c0712500c50f03a12038810041444400c034018241640d036480c4c0f041401c2c900d020104d960b178414440c0c05824600c15110103115551860340121920861074004100c43ca26528005021050090036401c0407614020f40048104104820400590300340c6420021300100ca142e9000034103030400c61641c03002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 633499487 1250 633498237 633498259
    0xa0203070309080c070807051002250308040308030402010e1f0e010221040f090e06133e04020306030c0118080a0605071215060318060204080c0420030a09080702 71
    0x80e0000341440580303041c6e00940c0c00f501d0f5540140240c980007040104c015820074800c100c00500744084c080c590140041e8550500c60352901d07410080e44c0941c00603218114004100415560080d6601c030000d2410703030b070208880f030280400c9441e07507200b07035418010008a428107406507807080001c036090300c004104040703141c500305490010740d61091240302c0110802d400c1c0050845e8140c458410145e104501400c840d5807a00c00c061a5031100f1082121204001c02001364000d091024500002020800d84181c200081007440850300700340d003804d48103034010010840c45440105400d6a03102e028200080d91400c500981c203070041e0340d904003052600ca44019407040c0310b11a001107000301c90a4039052021a0260500b2007074400c1034a100300302c07440c2c1d0142004210710990041642c0a1024041000c0e0a042c0d42c9031070a990165108507040c0d1301c0f4050403070744d910b8540b10305620717203138201030105403410440e01c10803290000800c1589441d0b541c04122003840405001c5071007146d4014200c1d2056 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 633500737 1250 633499487 633499507
    0x50706051003110d0f03050d140702060103050f0c0604171e03070c0e01030302031207140f19050405090a0c0c06050f0f0c21092b1d090a020307030908 66
    0x190010b48001d8030100c6044031140c00340d0400d410000303000d035044800e91141c003030350703807020b6889034031011504e440540c0d5280543c0070a40c1d18040b89015525640c090540340d4954280741c0d03e0034201d1050340c21580c12000d80d5a009a507013178100d40485000860354022507822007005420071660902000104688d140b449600607008401858840c1c0b05480f0b098195441c1e42c008500704500b4000180964020442107500c0e90300304001d10741c80011417170850002c1006411403c5507030400e141c0c151400030041650608042c20420081058540780391050034145042c0002d14444070151140c40984ea41d4a44a412680305500350000150490414000c0b030611001f2032075144011a240d0b02d034041d03020301140000b040c3c03c003110407290419052400d1100300c802800c0200d8000b8190b1038203031180104a42180120950700803000e42600700036050201e416502402e609a98028404181c40001840c142503403030006e00d540002034107200503100d0362141d030281e000303000058001c0c210090201c0d0024413 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 633501987 1250 633500737 633500761
    0xf051201090b09071802030c0d05090f0d02070503070911030711030705010501060509130501060509211203070206011e09020702061308030d061a0306010305040c090f0b0f060c0c1005070605 83
    0x111684290031900d17100c251701000b02240010740707c6142c503100800c0420719025081c2c02441e0440032840948034a150301800462501c5904183e00001d42c001c0c140c100580d140c1403042000908064809111060550b584540d461000070f2500d07003130211844c000d042051041007130b00c04069110008010030b5071560806085074011a404038820b42d000464940d0034840d038000c4074100e07007960300d801d424100741004024075464002c0b480049002010131b08469400100501952521280c0c1c00340c4d520b00302803d00904000051f0010600310003024a44030b071040311150f94400700e9a0500c00113841d1202480024410f2154040c0e80c0c028800b040004500c060b00030004106520f035007142040200c2c0e6408400100c40403c6502d000d5020341400084d200d94004e801195200748507502544185454441100880d42c402da000707075201d59103082e01c1516042108076189a00c4c0d084a2050400998100351640e68811805a42c0181808021410302c00d00510079a07540b1a1321003000c1c802481d004401840d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 633503237 1250 633501987 633501989
    0xa15020a120c2d08030c13030b04020a231005121510030b0114090a0305160e0f01050607030e0a0b0d0e0d0905060313150e010b030607020102040f051201090b0907 71
    0x2034040b00845034441d03d411458884200302035490461000070300142c4076901c0c04c2d003008006da01c0d030080410031a040301031500c0f41c4c1005580300c1c000401c0b880c2841d0060182c84100da03040038118090343c101081000c0418803e101980310116100c2445940d00c05044800d8000d10305c0c2ca0305e00d410f8010600203104d54202d15114140b50580f18500c0c800c40f619012810303141c4100341107000c80d086200612000950800510840a000d04865100ca580c0c2c2c0d1011319100c8070003181a1000c501d80e4041c03050f150809200c41c1c22242e001c1030388410703505200001c1d01074440d440e07004060020750000251f503920341d6072943c4010030301050b29580340d00c460305280020b4482410400c0b56802a0042002802d000b6604201a10030260a40b421599001c50f600309501c2d0701c03902038074140d601500c0786184030500d000311850415042c00203e201a42001414988280070300351600396401404180080d01c2c3c1c4039035000c01c841e000c4070884491040b0140c40350040030310441c00380c41d00e1140400c02c5030440c4006920340c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 633504487 1250 633503237 633503243
    0x414031603210201021c0e07030b042001020303041515051f02071a09010f03200a0f0e132414030714031903050d060905180303060a15020a120c 63
    0x34400c42c01c0480304074201c0c4180c10680c80c4038014503028801e42c41d499405103104242d488104c2d0700c85502e80d1210381102030304a5080341c14004002505544c11003814422a40001c20300086007142410369800700e01080355181140402d503204400e803d10905c00c022500104000b52800b0203c0f20a21080401c031554107100c0b80c00351044000015000c142c101c000310301d0429441d0140d040070f280d00011600c4040341400c40c001c1603200d4044a55109503c40800d81d0f80300760401710b03a0f94880c2e00c81c1c05041d0104000366401407000070704a10202d61109800042c0300400c1841c0010791b035500c0b1900c02c84208110300b00c60200641e08401044014031241d4800803403000303c00b210020303503841420452b621045020350790075030440c00300503034401020220000107501c2820002e080400049140c03044410310f500c0680d080d511042400065041490246103031120b20300074502c0d514004000c1200e001e00340c80313407098150f41300c02c4c500301d0b0a109200406a042e8406106100285511070003002000180c1082d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 633505737 1250 633504487 633504533
    0x10e1f05191416210203090109090506180901060308130806090316060c03060803120103020f1c0b0a020906030a0522031d042012010509010b0414031603 67
    0x4440d409004010b041521a1406480c524107034000144050750450904102c6000403100903156080c00641c1c40c0c1401400594020b6486541441c001010407209a010800303251428080c010f0743e0b2283d010300d030900c2482c14045100741d159030345160300620700d6074030141214101060004a007000c00c40e01034101c40c46030382200c4143d110410741039203900c03c0446000e80140701f82600e10000f12a60444038040c2418140000c0c0c803981ea004c81400d5078041c410341c070702d05085100144118948403a102d000113109a034494802d0325088041ea18222a069003d00400c050000141c0e4000d100d80460320114000f902064403030800300105805404282d40d8102e050241d035908c0d06505d00208a06c042c15605a510322600708000140c000e0034448507410f05070010340b01c0b00e0085d5040c0d56a480368640070304410540365034241c0034412540d60710341a00310034400c203403001c0100f03c280164826101660074182500b540c0b4488403001a18040780c514024090b0840c1c8000041401a0300f020061115081080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 633506987 1250 633505737 633505777
    0x301050306150f0411041a0301060f0f030b0603011203081b070807081303050a06060e0f01091805160e010b0703020c090c1309020a0305060d0308070c020d06020301080d021002030106080105010e1f05 87
    0x903501f0140005d008120020f044001040d60480c401c0310424951002410001100007103d0080760b0142d1090304181c840c0b0761500ca1070000c05034001507081d4482060f16000c210440310103014031841c0f041c040041e140d01004a00d603c00c0c0030b20a400c440c400031015503e001d08655a241c07060302d802110740b00ba290b2078501000080d4210149070413612030700c81c150414000f80e080600d10b10007407480250303c0210801441070800028820460b06d01d030400b0b004090581e280c54a01c1d0f00698000507000009001c005214000000c0d0b000107010350715001c01c8505a800341e4801c43c0340401c2e802240980351f554100c803100054101c00d07036801801480040d076024800c959608040c000c15051080d00140018842d40000e02c03041e1050705410030081c4002c00d5041e1701030003503c841060b60000e07000b44c103098011034030407541c6070f8042240c4031144100c280154155890614068501001441541e05000c209003040c1403664960502007900c000081c0c142c07500c001400c0c4003c060790070001000c8162504040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 633508237 1250 633506987 633507029
    0x61703040f17010b13020309010b1816110109060605090c070210030509190c050a06021b04020d0f0911011b020d1e05060705130b0301050306150f041104 67
    0x100e40036200c4410204400d5441c004503102e0700e01038115001e80d039541c2e40d01d2142c0341d43e540052012492020890242e168104010075900310740042d40498402c0c81184082581c40441c2d2060700d0780001184480703524624000c0c026a00b508465010a91035407904800104004855220314261181a00d100a030350b524111180c0441c401e00d0030181d444681d4050140e1714520940091385c2c4103548605488203400741008114400404000c12540f01050003c14000c40c00c14820341002441c0903c0240740c2d03107203181e0307080c0c4455800c0f0201c00c2c081d50300007074101015074083c3c2001981c0c071408030702002950110b04040285450040c1c0150020314504504102000107041c1d4150750303138000b041850001803554a042162802c0c0f0f80303010030311682282d50f0022030418030880748100c030070381c079915030314034050215a900b80d00a0300107900c0000140014130041e00d002480a9005480c103544401202031140012811545000680d0f0300c5410309880b0f098510210700900102e9407011160840d0f0182c800b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 633509487 1250 633508237 633508243
    0xb060c01050a1503151a120102070209072a0305040b18092503021e120405060c03070801030f0309091107020310090f20031e0f0a0c05040f0216060617 66
    0x1c4806480a40380340640d4170000d07150342c0609400100c0b05003040a008821012404d980884007540c40241d501142c04425402d040e40328030b0348021076142282c0c00f201c0c0c10408a114082c010190114510030444080030940a102220080c01c0702d11540c60f11882a0f00020300c80403201078805000e45004000309100030001c0e201010700c680b907280011104039060400b100250001e04403541451400001c0078084515400100506440c04810005030b2816043c0710f4a0b20300003403c0700444007001c10070071040d950700c5003446064a51052030701102d10302c00d0400721107010340ca82042605910b001000f103100701803d801414141d101750160340740c4180f001c56100c1103800940024005006034400c000000d11441040700d0a611007000301080788540801281ca04040c80e012100c40c140c80c07a11048106004008004008400034024a12281140c0d9010400802441820300882d12201101410b03010b94058800c01d40c40c6021200e6440a14202800944000d2080070b5480b845820303492108a804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 633510737 1250 633509487 633509489
    0x30c010e0109380a0212190c0219080d090807032607050613020406050603061807050702090408040f150507020f1302031005040605010207080c040c030b060c01050a15 73
    0x16180c0700c854901d400390158002510400e0508141c1d10700001220720000f4000040700400320524a5848191220000e0318061b440c0b24030442c0c02100f4403903181407034a8002c0c0031508400307901d85007040d50100d10224a611452941c5110720f8a801c4a0101c1ca642c00081c081c000c810803603488803559656068403a0702c2d045c1c2d0303020180004030080440c80c10071003045989880694903200d1395280440b0754071228240507042e100313440e106e0050b404e03440940c5042c0c000d04001e003100f2a075032840c60801d200021902980f01145a50f045803403c001290103016605545669401a1206840d0314240c904500640d000740030700400c1c00748602001c92542442d03420701800400580700e452070002c0a40030013030550024a1304590000d503201e9150035a1409001646c0900c02c0711101e045200d040c50100400da8400e90011030440d881b5460412064400062603c60451300f0342c1c0005200301c1180048000c0c0040c0358140d034000c01e0015a0b0742030f201c41540064031031420b6580c00c10540c0d80901c00f0b6110608a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 633511987 1250 633510737 633510739
    0x6030d0f020a0f050c0607060c02011109060711040213030308040510061d060d060c030e010c02011a010e060f04060815010309020603011725030b09012d02090301050411030c010e 78
    0xc1c061103000202101c1821107104d015a0460308020203d10003c0c03100c0d4400c202c1128600c0e101c04020381110340901590a40a09640310b0700d0400210001003000741c050413001a00307100e05208801e900352200d41c1101c461400081c3c041460320b8803806c015060040c140c600b190113208040d1444248800343c400d2205480e4103c80856074840302841d910001200a000b41c0c5e48800c02c102c0d4000065410700c5007c04080c00c0d510b021442940380b0200a0850301c4804021056904059504402494031519610074040900700f4081360481b00c00801c0c0c05004440002010140c0060301103a540e0b00800f8151099244a84500100e0304103001102541c56101c4000c0d0096401e00040c4240c101d04564044913803035800c201d0f140103c01883d28014070030345260692400c04103d1040c428084034a55080d400307080d1400a00c5103000800780300c40c01c0c40c402540d12034118515026024000c04079012107a0b0150300800901c22410181000364900320951422032092103600005811540034002100d48110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 633513237 1250 633511987 633511993
    0x21040b070807110301151401080c09041104031e0209010b0c06040b040503070215130f0f060f14070b0a0c08040308072a0f12051303020d02131406030d0f02 68
    0x40a6a621241c0d40100c0e900b00c076481000c1c84541c00e1034509114030040a207403403104a80084c03030030010250510801e01d0b51810010120104488180000215408050282c0380020000d00889903603280c0c3c0030300d03040240416491401030454081a145c8810710764000c4031203000690303880008103d0362103200c001414681020700002d0100c0d00c5d40c00700d164041e000380142c901d000001d500103500c0314072074100c0c89900040030031488000c000006030740c0c0250900314141c043e0355050000c003100c0c07030115104103010080701c0000f001a07030384291011400b1005e12501c0319281c84c10340c03070900401c40701191216030131454841d84a011030700c00d56070356000300c0e01526483c20300e441d030300760880e10003416044407414035000508011039103941003007502c1402e0060304140311001c2d01c0d00e4483d152416507075104040050501044c484402550081400c03240c0c101c0350701a00d100c151010515215900848a204915100c0e0100b0070908000603540f0034541241900d414400405013034400036082544600164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 633514487 1250 633513237 633513247
    0x406020610030b0705160204090507090f0e060c0906040f063209130b0307090209100314010b22080f0d0201020319050411030d02030703030e0d050304230f21040b 71
    0x74010001400b5080820400c01b00640320382e008a400d4640c10142280c86038044402080441030600c41d00c49507555806090104000c045d15865440c040034000000e202e0300052402503d561b00c00886005200aa1000d004a5554040075180d0500c070380031a500644000701d002524403801540d051480c620701c90f02400d04d00e00d04244166991846552810b480e07a6080801550380c0410010008001205015960710041c10074001480c080d03611440030f250030941183c414901501149043d60b08610405844440e04120322291401255405244048040c80420030240c0400c9000d500d003502d1003218540c4540c504120308034030048807000005480c08c5000c9010100300d4001036003050103101003c0003118441c00090912500d0000b61025030b00002c0c0600070543c043c0602e54a500c0404003500d51058429009000c0c2c1c07000602c000c080e42003101000800091f1078420202e07100f554000ca440c00148002005d6031051030414021100140c42290060f0860b21403c80d4203813081c00750322504007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 633515737 1250 633514487 633514501
    0x60108190b181f05060702090103120e15041d2e0506040f030b0c04030b15121f0b030109050c01030e120c01060f0b070b060f0d06110406020610030b 65
    0x2000300c0344101da484400315a03503121102460300b030180202d0901c1e10646503007a90160b111001c0029601060140390180700c4d410241e51104411070440344c00105a05c1c180001c003104a885042c603c8007540d20221208143c074a0481d40d0015000381c49000b5005a9440c003d80d2072480020030427604a007d07003a00344180070f0300c5841c000c1200c80794000d12546070b845503210380000303e0035081504042440d40d4400c07800c0091080d00c500e490303002041ca4004078682411901e89400c5808000d05080c40e007025001a00301548034402a460351500e01c4094514000d207e01d41c40354000500111007540f14101a100503a0349018030482c038146500c44c000344481d000d1a4015400b5110040e808610360003014510140d50240c4001405100e03121000081c0250504684100342a550b411641d003a0303405101240014000340c59441d0005011035644198002c3e610001e504101c3c1e907440140314905000000c22101c041601501c151040e0745c01b512840c3e1b03205485840c05400702e20000d407560000a000c0303045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 633516987 1250 633515737 633515741
    0xb01020f0d111204081c0807141b03160b0601020f030d1505090a0b100c0b04320f070e0702060106050f0708070b071715040f0b03150f06010819 63
    0x9520241001d40364007801243c503220058100781d1206106170080420603804455203910750750f412205050503c0079092545d001070540b0202020008c0742140041c807015061840d00c032440249107114203c030366401c0e94955100c140c0800c0a030880d480e4880201296aa600204140302c80500f5400107600708114544120040d046400c050641c840d100c20740482c580d01c2e100803162044145041c003090028880d82800b03500c868603101c2000300508412004002071034104201d4201d504200c600d0300103c03c101440420701d4a8440203410358034980d10100d201d080102c2d00c0c50b01003c102064400c030715660700740380b0310610b022035070500182c002d5401881040e000e02c0c060040c914000305524206a0542e4805095502c11076003a9074140d20f9a0802c11310035030000c0c0c03a6000c01e003030404001c028101100aa81c2d03405942c0c040510a6031105444003851160358008112041c0080464591613452240300101303d03001c2e1090f102d414095400117040d94000c269007401041091040c07a5003029101038100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 633518237 1250 633516987 633517007
    0xe030a0f0302162901091401062105070903021c170304050a0c0f090509120418110d05070f030504022407020d0c06110a020307060c0f0507080606040b01020f0d 70
    0x10300c0301d6000e082d04040745400c3d10951440c80301040c4d0652615a44841d01d440f444140c0c44140010704003290140c40c203107407181c02411100f9034100121041c90305412104c0301144007070109a520b103020300300700440c0e510450180407039000313a44000602c0b11404080d800344081d0900584a02280045c2a800401c00d81c01035a1003405142940c010700880e070788403000c1d04110f40c040c3d003001108983c18030078126036229150304070017000c0c014103656680c510300c0b500d140540c0c0300756400d140300a96540040e00c484c1e001101441915450281d0b90051581480d0003024203855902c00034480450401c18940a0300c251401180c006240302c0c6941c1654000010344903001c0402d00002400703128040c0161150354000f04501c2c0b00b00004020282404401001c412102d50700c030840d03501c41d40d28500580c07000304406090f078189280124010429041640e4240d8500e1001003243c03040c0100050801c0703020502e24095030084409120107001c18004a170340c0c3c1c04141c100681d5421a0007000946802802a00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 633519487 1250 633518237 633518257
    0x607030b12070b1b030d1535010b0d0c0f050a0608161407120806030304050a0b0d110d0204061205091005041b03060b120708060a090809060408100e030a0f0302 70
    0x7413101142c44112400c5801442004101584a06103511075500343c80240d00503100c01300b03490100c80031401009140c19111003014844000800c89201c0030346013900310031096000504036040001c69890b0006c1504818440d4900700400c88801040a00d404460301b0308851140d9940f202c20785906031b42032448200355400601b84642c08000d120520300b090090315080c0c3c00341600411308980701b0307006000410020000c1c0d2082d002004180515135403500001c1c00e9480c035440450706d6070707103114041005050040703510309010000b04d003110b919522900140f0a44400d0342d0b515084c010244400c0301a500180e60a40c0e407508080303d101f0000d0302d10780c000c1d1303030042c064032601403046c00c42058820420300c181c000b40c0701c1e1912071500440760f04250f540000c40030b03001c0c4000c000c0285800740300c80d1500400b820f180380080d15009206c050000700002d0b50100c4400602003a0754660718800035595114021071203030030504140300700300400350100a8524540143c1c83d2040c2851101900b1802540003003495 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 633520737 1250 633519487 633519517
    0xd0503090343091802030f06091e070518190603080a031e0213090b030a02011b080c120a020c040b0303030106030b04090b040302031c060f0b070609050f0607030b12070b 74
    0x2032246054000c848400c009484c00b07050b089058010315090404020400815501c000c0902c00421b60004600082040303440424598000955440741441000c0e03001079840100091003544881c0d00011560052842806104100700802511420781d801444083d1400009110141846019800084a1514001c5010560405405810201e03005039546c0c0c1205215040705000801091080100002045004004401e01580000c11004030400d1a212007c500c001080c1009409810b0780c801140e580183c903c000705451000e24250024900000184a00d8079103000509003803107501c3d46004060059072442c0e0030302c2403e40281c20b0348508241c005503178803851300100c0d082c040c517240124400d0f4061692800015000c030840350030170102e229098a000da04208500000c06c0807000c441608114a84811007410180020004090068040d0082030001e00c54000003060691094075152410041c0182450070b102543d002d402d140042540144011700c60220b100020304504e551500b04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 633521987 1250 633520737 633520739
    0x40504050c0d0e01060f060201020f2b020a0507020a052d0d050a0c1a16020427050f0d020102040b160c180510050d0b040f0606050d0503090343 63
    0xb0030320894600700f482c0c2c14140d66a803c01d02c95000804101c0d00140322500c001d50415444c20141c40f01c2c6c4c0b207405100f209400d03418501e051403070301040501001c0f002d00402103489000c2507401501980c000903080344504019a00424185864041110015000c95809141800d961400c00e155030040102c20b600400e15229000051401c0000c0481c0502c9030356098a110f140c4a6212441c5100210209440c3c10138800140c00302c05001c0d0320b200c055011100858a107000c40301c40550400540c2d4000303a4615441c1031981804000203182c850b03a420f400c1240c0482010301c4040b4200e005da8007400440040411458082d80421166800c0f036a001c1c4200700346c2c00d50b0756824410201c00400d4481503042c2c407a000c1024201e10040a100241000d840d1145091096a941002c02c403000f00018a400015903100303081c04019404031015090141c10343c1070b1040c2c0d504245540760011410f0511a200c4e0402c00030f40550450b01c2d0800c080e40e01d0035010b061094200122070080c200354040841c06840c940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 633523237 1250 633521987 633522007
    0x7030c090503071806050108160305130f06020705060c030c04051e060c0607020106050f0913060902030f01021e09090c0309010921180b0a26090f16030305040504050c 73
    0x4510401082c0f844c2c51a01140b0007004c9041c26503002d170303001c5030520840200b00f224004065001c86159182c40c540060b03a6078a0a9140812b0002c805001d02040002c407808030070064980e0040c010701740142d003160020364460b5465a070911046824014140c41400104a51301300041202c02456060607003007810000383c00400d0340354004070b0003007813650b0004051000031502842464003808041d07070310b206484201000b00d43c81e030b140540443c1078005c90300049014005961300860450341d009040e00d08001905408074040e4100d0f100c8108581103e444000001c1c07139190848094a0010b41020101d94481100c0340c1035801c0141298040c3d504c5140701000141c00c520758142c0291554500d13100e40340700c1240180705081100940708416081c45061000070242c900f80c540403441407a21903e4114029580c280303403048010740308410845502444101000414411401c40180c0101c410850989400c601c2103003262002401040d002c11090002d400d00b134012944c0f00c3c001b10801850016154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 633524487 1250 633523237 633523243
    0x23060f19050d11010f02030903070608130203010908130b0301180b061204060914031305040b1206130b0f162f06060306070207080705040b0111030a0e0901060f020607030c090503 78
    0x82c0c1c00c403505001d0100c0c810940d82c106981220f00031162005505011801000c40d40d50f82c05401100e040c0602c080c00039110181000082141580c003030000d112802c3e141c60302a120b900060191001c10342d0407074001c20b80c02021401d40e4103c03030700395080b00310305404410104010108080c0d403d4003c54100019020032000210390381c042c520404000400c000241003014045e0ba03004036080c580e4008112400110340110490004d65504903400074500220000041c441950141081854011201004054100480b02c400800c2c05020860f6290b650100c403a00c4e0038600300c483c0100b40002c0c01500308058031414040242001e00c900c4d82c070180660400c14190130034402140100303588240100310890905108180d00041540010a40d103070502c00c0807a140c0546021b50350240799542c0c0c1074801d6a22640f446035030000c020040c2e0369582e1491600408440c9440003540c0620107030000012414407900700c3c0182030409901410540c3c0b00c031503088001e000d140d940003003040b001d1003021a40390303418 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 633525737 1250 633524487 633524509
    0x3020a0807030b0a0c121a1801090b040606210207080c01020a020c01030501080706120207060c02071e05011b1704140103180506041b1823060f1905 65
    0x1440082039200d00c2d5180812400780c008011503d0b5a04090baa69401030b086060003e0300b150f000004207541c0095140c15034919861140c02d0390011a9510b0103400080050007207041c1c0b40b43d80c17030602621582c0f00c184015948188603540016184212682e091494a04960000d40d441640949880c0b03040e01e5585040e08030624900c3c0ca80d600140c001203168041000b02c1511301c0a003018071442d850000116203074000c51190740c007840007004030789208d48000ea048540003603000303404200c0d01240c988000c0da03c0125005060b8010040e03040044524036414a45d800c54805a685903040110b40340d070304e40d4129081d00100c0b8401d0341800e00c00e000b80c01340c00103400a070148018200700d40d1685000101555036140c0076a4041041d1011a008298040750050307104e0b420220420160585c1602114291055407008007090464000007c2000c07880e0032214186000708040900002e809012320f100c00f0003610481d07071203480c0c440710700c1c100d050000b4078059295884c1c180c0080c280d5604003040c284904 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 633526987 1250 633525737 633525749
    0x70c121115060306150103110d150812090402070f050601060e13090f060504020604080105163c0315030602070b090619020d0615020d020d261003020a 66
    0x80d80400c08040a003082801941c44030a1007001803414000040303503d4010281c8510105110090b0081c850390003a0003070002c420030010302d282e0301e1301c5485255000745000080098140e40c4079000041d0100000360344040c1e440404a0380d442c0050070410013001798031000040f18030003081003580d00454001d1280314000d09880d1100340b41c0d4403001c1c0801001802402e002a0341d94a044864400328416065050725240d20200000b440d8840340002403041c0110350105500358200300810030480380c04907041100c5402503caa02e0b0520a0280d4546e400d0000001e00091040c410a100600d00e42c04034612405502c2d4180082e00c40c0b0074a40b1503411180c15001507e140e03400140901c10403440210443e8080400001b5103411b0410303061a10798205400d00c0c020080b600440e1070380c02c46c1e103a80d104100802000000750181400410043d407120202645040940108040220341a005410b60080340f85e41304200c107001040540d84248680d40038200e600d50b0109290040010b840c0e1340000005015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 633528237 1250 633526987 633526997
    0x1e0b07060c03061508010302040b010c020d0302030903010b0a081c030609020f03060a0b04030302030304170f03250311090d050717030c06010b04050d0b1504020d020403061a0d0803070c12 82
    0x500c815000d002d5aa041d03000c81e0081d0858044c0e0890b1650101c40c0c5410349904803404078160413141e0048500b408036070800b80d800f1041a151000b0503800000404a0346001d40c001d200007a41c0c00c00300001400703603100700d899542025201541d140c940400205145c6c0440c140010311540340d0010b0700c100d0b0006002424501d00c00810300c01c451501d404048003c0101c1d5240b1803170035085d5540292203000140008010035004003c0d00301c000418000d8421120300350041689038504541e143e1030992607101c0c2040b0440c0c4000c030302458140319001d0380c00a81c80d291466442d0020040910215202100003034900d401070305804a000780014034200002a5110001e42d01c80c41c14020083c00c0450607482401c1940040004204a0711044550506280c11007081c280580d2040702500c2010811404198081c0c80010864408041035010340152409807408000c40740515013081d0000c91042c80f65070b4000c048404e408001111040103541c4044945002150140aa41c4a0309010082440365020807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 633529487 1250 633528237 633528251
    0x106080d08060a1d070903020d030309140c1e06091f020708011e0e2103181203040f0f08030408070624030204020c0102090a24050f041e0b0706 63
    0x207070703000000640110046500c0c6003424070303002c40e68941d0303110304111807564003002e4001740e03829004140d0310008540141945070b800c86107150041c0200304540044488809652003201e60042c001041c56201300064101c84194500400c58090a180f080800e85d200d0700400005c80aa01c40019840f8134507806c0c50f105110714403801e8041c0c1002c101b0303040505a680341021007076040301001c4211884d600c580900043e180e2501c140c0d141020240300d6142079503c411580702e44070219030700007103202c2c0260070402d000e200c1108004a88800550407010b907030200520118000c1803992481c0700b44c480c45500303040f00d2000e055548015a40088406486200c800304200042c0315482c003d04508246119244440b2903110f4402c50801c05035010190040ea400300c4d034180074000940c1103c60150b0020a8940070759600c0503000c4401451400502200840300c0100240500a006071400c0041e481c01c041e06281c2010001c402c600c0e13070444100e0155154110020704040040010640540580004513621f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 633530737 1250 633529487 633529513
    0xf020405060c030415020303040525030501021902100204080a0b0a0b0901090b09060d03020616020705030109140d02010204060c12170702010219080613020306030102190908120421050f010608 84
    0x82521031701a0a40d00100100000a40d02184050380f20f24002c008844003a5210100c003500880764200034880e40c40040c0d4424491109103c06020040690132074090700c28034032070b501c01c0c1d001c3c0d40b06440c0d40d41e022a40040000f000000d420364021129000020b1150000000665017242a44100c031016070341c541c1407546007170001416920941c260b031070100d03484059900a54803032006083d411404d03008810b0045191003849030f0300003040d000f0028040c0c500035050902035860524183d10301485003060100c031203030060090341e00f02c5405880d00a0f505469403035400b0180754070b0107043c0030002040805004414054042400307286150700068552051000d0840c5042c0200f0600c0c00b030010035420061644d44109401302c03500c000c41009600c9444480220780a8003c1031424a20f06000c10340700040c580d07018030518100c5214100f1070b1031b0381c000c06144409074070590007040c0355204001000c0c0c10410b00e4030702d0494a50321070700840d642d52400200550850b030b1320743c00901e880c0c0c104980300c400c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 633531987 1250 633530737 633530759
    0x105041506090c0e0105131a09190b031603150303050c0f01060e0c0c0a0f050303091b010c1403092206060503220203120a0305102301030f020405060c0304 68
    0x140456180403c001c02803103074054501c0700aa51900d04010b00007400e80c05620314004031b00c000f400c07a01240c8450005103411070b0099040b2040e0b060091300034400065410341c2000b04c680840b2004070407a4034580700c0003104600c081810181e0010301d0745a203c000600080420440001c6000f42d4605131145003014013130741001c0c084400547c0c10380c14008180500513124404581264142046969a0343c502d10b401f0b040204444e006464944125800e109228020006500c514207a130305540c2005412003070f5220030403c84001c54005511013001d9000103160000d0049000c64070f5003180d080000036000182d120007085410700110294a003250701140f041d0041c0f1002d03042a040441c210f20305000e215000400c0c603241c02000c9400d01040b001951000e0001041d683e11118420344d86a00d420f8024015080954840d207100c83d0b00440059081c0d0103072101c0001204c800800360141c04a8001140a814000402203e0943c00c03c03000a65640e60801040c2005014010b50b032a80e290170503c00ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 633533237 1250 633531987 633531989
    0x30a020705270c1b071719050d0f120c030b09060607081204060b09040501020316050f07061113080a290a02030405010b040c0216060f090b1b0105041506 67
    0x80c5000070340c1c0316044440c0c1c54168503076002804a4500b0b40343c2400f9441d44d07202c844a68203092640c0107585000c51038000c0c0c1e1620030700c3c0c042c007002104c10a0380012552003402c01d103000050400c0d04074101c2101c800c0d2041d05100741d80d450500d0b0091030201d0030904030084031041e002c10390120360385083d4107606050200040d07902040072910f05082080b1074841d04094850664000195448200000c040218a5018980010010780aa40b5501d4549001c9000794001d0312140d031020350401c1c20215281c0300e202280c04810910707102c2d034104210f503034030200504446030501e41c0000051080901d00703000d00c2c2704d000c001c00117480201300800044c1032a102c0c03000039082e901044200d00010740012580c0c3d101c0c0310340003005072900596070354440c108a40101072900c0c078298030500b040f515814403036000910310004e1807200f080800c880d81e100400d40351a1410020704005c00c1c905402007000614640241041c3c044510031180c2d0a0046060142154400c490848070f20345084400b015943e10380c0b00c0d0344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 633534487 1250 633533237 633533269
    0x9040b100c0b1b04050409021813060e030f09040b041b020a0c05040b06070b040606051801052e20030f1209010b0a0e0a1404050d1106010e040221030a020705 69
    0x8001001a074101d201c61041c5d010780341c001e5803036000620441d1a04074403000190621a55400603040c03071059018414510f01d07065503001c0c00c01404191345200803007280d251104040d411031503c24804184000b0300150324005030300c903603148074112441d0741c007000004501e401d41e80a00b01600880c5489803e1580380d401c69070240e1700c0c00c03480e11004d4480c401181e00142d0000b40380c0940da50b0340d19001010304020303003215400c038001075640d10b50289507200c41c90503a90120307502040440c1a003208440a0700714034004041d02c4000b070307074140701e0f902540001c251591034000c0901481b50710010140b0750350001e0b01040d00030b840040c0c40c2c409039160600b4990000c941100034800564020001401041140901c1c529208007801144210719030b944481e240c2201e46041e0081c5190908104c1c2c0c85030840e2a054004c10b00c40c421002600201040940c140d4911000d100900c0e11103400b40701c501540040e845602d4a850341c81014100020006040d420205900030900c0c0d0f8100000c1c4140000c0c042915 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 633535737 1250 633534487 633534511
    0x80d0e1806030f0a060b030d0c080a21151502012310030212100510080714040b030a03120609060f09201b070e0c160303060b0408060a111c0209040b100c0b 68
    0x1c400092044400c90b490041c0314605007583d840001c40014050f0340301c00761000200c3c581807100030481c0c0d0505d0090115903052020342c000307011050ec05e900741d86400045078550113103461500044201d403440c850b00620740071444c1081c152240d0114810703d210b40200f24846d440655070b0300c0d0340c03040c6000d10781d404182d40303c0128009103411901c980e80d01d21805440154040d5a004400d19213455008184e125001000c03116020b20504026200403289015094000c4c18a9000304600b1003d00406080354003c814100b021481c1041c11001880d0030005035a44181c0443c81c510340708800e80140800d4101d804d4000608410308000e685001d1182c2d11030b440555160081082400a1005803103480300280c6a41c1c1c81c4050740d00e011401050182c211229500003c0380120b030850000580071b01c1000e040004009440c0c110708943e11031f00504805688845891482d10108107454018102411016002113542c142440000e421001403131940342c00508c02451000500200811191708070003880c0c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 633536987 1250 633535737 633535757
    0x12030930070e070302030703140c07140d050f0c0316051606210b0307080d030f0e07030b01031704050603010b072108012715080d0e1806030f0a060b030d 67
    0x200b00440c0082012091590220009840c2ea000344c200560040d07100700c500c9698900002e004e0f025410495055030b1a0000600307440c0c0c401c00009415000028689a42c2d0a183e10340e030b20102141d0001554010500040c804448109011686004a030784124007400c40807103011400c1b05038844d20388c040800c10105402c41104061400018501c0c0460048003103402c2e0b8004002c41d02c5c140040e4004959840303480401d103c0c156143d8046280c0c2401d105c014460344661400d5155111028000548204000d800400001d0944407404640e41c09038191a42487c1d40c400c00103005800990040d0a12100040c4d04d00c10010346c00c040c154951102450052212250036004000c241d05000e50111308040a5400358030080071444a00d84402042091020805920200e0380b1220300c2d03c02ea80381449151154140c0600600b000c100f1402d015080c480041542450038054030400350a079905030140d640031001c0c01002b4000300031594020100030518800701424946410f440b490000300300050548 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 633538237 1250 633536987 633536999
    0x11041e0513020a0302071a0a0e0c10030c090909050313090203040c0303110c030f0d08060a150807200105060a1502070308210718060503010b091203093007 68
    0x300480c00c140d51581c00503102c88001000760028440c801001d000c000d05044020480681e00000701d01c80c0c0b41180c4240100210000c0050b81e0f8460290800e074414940035054540300d01c07a912207040d8440310310b404801c00b40d6800741c64040320205002a86d151300300080005121200c10031903002807032600011442c40c0392a442d200daa036400760000900300014204021134044081007020b2028400030103a5880424505480d5030384c1807c00000008109036030700041d0649000c025410864003500d400c00100301300094101c3d80f54800510f0b02c0e040c00f687c40742c4030200a070800414010002803100020f0075003403075001c100b002e1440340d010f40c40c101400c540c03100342036601003084000c41c0c0d400083e090300e482468541e101040f04052042c44080b2201c01081a096030180300c2241d92054582014081912180700315402e00c024020940180c2d0204200c410604200c40c01360380c42d82103603050340e040c1803000c40090210050604000c10b070786a45801610400d1601b081c0c244e0400b40b440c014200103181c41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 633539487 1250 633538237 633538249
    0x41401080313061b12260906060d030207060c0201210b0915060a05090a080a0b07080f06010c020609040f0213050f1905090c0c031606050f040b16030f11041e05 70
    0x84d00401c0d80d030300b1090080540e80034102c580a01d0004041119290311500300d441c060320b00803a480001d41c4103504c086100e508100c0d0305a111541c1550107825918100101a40d4a120441c2c0481c100510f03140d0341d03003c12191303290000388480c3c29100841c2d400421410488e901c03001501d0207144080c1100075034150f035903100458426850b5420071a07114201c0700c000422020317140c0d010310224025041c08000300102942114805e02c9962565100c0c0c1d102e000d0100c501c18011981a0302240c0441c00b2007025140c414098800110005e1011548883c2e80c981ca0042c0d800011941d242d48110032401d01040c03501c2c00d8032500707807502584d040c0201c80401081801e0856140710360f40c0034501c1c143c04101c003003000b8011200c0e4000e1782c2d000c0f00d5413402c01510401141d105a0f50030b0320900d00c2c100100d10007155012150380110741202c81c20b1825118120b100c03020b504403000540a059445540350540c0c840c4d80103039a00103244120440d141c52074402c01805841205440017113003a4411402d0019564034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633540737 1250 633539487 633539537
    0xb010906021e010b041404020306130c0303050903010b0310200732030406020a14031207050309190c03060c0207060903110d080d15090908030406050604140108031306 73
    0x40002050040042621401013020110642c2c01909244140c0e51303844a0030340050040744260202c44540d603454610789102828950001c08803119180c0800119101c1c502900ba00c0030020000280b40795000c2c0040c0c68159207c101d00035841c0c8400c010200c5446251196444140c82c071482803030200c0c0380c1c0e600c0082c8107030342c03100300c1002034541100065a0540800304070303c41000c9c4103d84e81e039a141c44002c1c0d40c03280310101c1164403110740c525003060a030b800b000f5600b810644440110054135516030a695a0b000189101564400c000d0f40ccd410703070301040c1c1100751518080c454001e1704030700b141040380568007035585200540d8064507040008c2d0764042c3c811021603400c00c0034000c601c81200d00152842d40d1910001d130420002150036103d500c1c66502101c00c441d42120003e844c95958845901552003181002c2d069000c240002004642d90740c00c039503881324000340009092889440c440841040c04c1c3c1003480b950f400807400d4041c260104101300b010701841e00f06040002c501000d0021002da803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633541987 1250 633540737 633540763
    0x11073b07140913050c0405060d0204150e030a023307050615030a03080a110307020c1305100b0c010902060309030c0c010801051f17070c0203012007140c0d0606030203010b01090602 79
    0xa282d00017104030303103141d0030388001d000010142952108110005004ae4005010b00a90000060750400300700f406000d0342900542c0207000350031501d080b902000310200040040440d25501c22101c441c064002107810f070401e4842c0144551158024103066262140c02402c051a050f0003142d081d8446e600001c010760074a5041c51b0018140d82c4401c404006400c0583c11404c41d28000300500c04d03116008203410440000c15184003103070180c00841300040c0e0714182d811802a20700d80784140500c09a040c01000090000030003c520090154040340b041c1e4402c503201480d0b130300040307a03801842c07509100f10f0384a0b02d02440d0031452541030400165120100009035684004410110881d450160710b038070b101e08a07820014981d9280c4076502030402040304000328465481c10503500c415000041c1ca09a00a4103501824284100313540d865452094000d5040d07800d01c640982c000c159a144044a99001d01c600d0000c1500d1f4030754814582034a8240080905000300e0707010601100c1d90014000d580804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633543237 1250 633541987 633541991
    0xf0e0c0c0a120513060306050f04050f1303021905160b040b0904240611010f021201060c0c0306090f2001080408160209010306050103050c0111073b07140913 69
    0x1c802e4000c0d201d6204644452062000c64800000c040f500b60344914120b80040e0380010015000008110813a803080701c5040e94501004081b500d81d080350342c055490b851080c012a10031a020b00002c00081d40a4081251580e200b800190803020004c00c00707a009103860f0f50424207241c20103400701203d004054400307014a680715401ca26400e8480380c282d500808981460090302c0c2c94580052032024224204c0881303608001741c0141c3e00302c444c0300320b42288241030200c0c456039007000000c540500c8021410340f0210200d00000c80401c07840c2c8900540148030b40d04d0803402101510300684004280c0100391603c2000c8004a0941e0740c01c85440341c1d01c02c0e4007500099996003468031620140542c1c000103908040c100c0d00100030480c10790700c600d060700d015004540c1c007c81035900465806825142551998002c0c02c41046100e151085040d40c010011200c20311740c00b5a0f8400d48040c07090000f103520501114403d00183d550840b9050449000311a40d103031400da15080402c4106481840e10181b842d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633544487 1250 633543237 633543263
    0xa0206030705160606030605090a02032125060b2209080d060b0306040b03070f0b03091905101104061d1f02030a0f0215010b0c0106030c0f0e0c0c0a 65
    0x41d1040b07046aa1480c0240e0040c410840c1a0614030004c3c02c0501084405600c0c4c0004105410000a20300041030750060045c50000c0c6280c210710b54013092070001c0c0110b2941031140c0d4600340030059181e04401c000c0000e42c410301c00c1034185401602c000395a039a009030400c0d009809450924041c40c0d442d400c42e01000309200e00145860702c2180700340000d0800300307458880f0100b107289040005501600040303e0610240d500300b003c0607110143c502c19001c802d001000104074114925000c0c5510102c10425a240c0320141ca140b2041d10100180455a42c1c00c010062000780d00f8a228281158450281c01400c0c6800c00300d01900e00621344a2030342e5148000249026039585070540c1c0001140810f5402d0782c01c188050011b90349030495180d140205089041d4242e5051000481003010742d1040402d205603482c04003110116480041100e015540b0360718084080340d1503011600017000c001076010004e82c0f81002882100101500c2d2103500d250410003035000803000a40480300c580c202c09648007403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633545737 1250 633544487 633544501
    0x30020603012309150402031b1801080a0c080615161104230109020d020903070b030f22030c02041b021e0601120b060d0f0c0e070302121f08070e06040b10020a020603 72
    0x231094000c00803807130280c0003611140003111000c580c5440d45081e202c141e8151107403012141a50171038100ca40004502ca00051594a00124010b00c51030380010554500900880c00c0c840900103144241c4070144110b041d84640e007400e01c40e81c540c1012a0b030402c0c199081d0202c0c514400c2406100c0c008415801064a10100030940d04072142501c00604881c007155407844981d5442c0c20840b01c401401c000f81000444001d400441c04450104e0060401e5400c180343d58159048045418243d1308103607205603000803551094410100014280c0041010885045102c009202003856a0f20160081c130010031005505104500010340c0c07000305214070b542c8807804a5894048103c02130640040c02841314240041191141e068641c20b010003105669600801e400303903c04c000340510681c0c610b00011307400202c0610b4001c060303030700b0888400c01c03207940c0c254043c90005950032800c0f4541c6454207000c5145014443d41140b00300c20307140000d80f000032060180d01c8601c010310181c00390000000040103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633546987 1250 633545737 633545761
    0x14060304020102251d0604110712140d020a0e09012304050a0b0603010603060305010c1b0213110c0106080607140a05030a061203020f163002060301230915040203 71
    0x500701900d4000e0792175603070070700e01c0d500740c4400c0d20040d01892401d6507080f03265504400712600141c01c50010401850f4840341164a1714514145038869941400078101c070500c64001811782249582e80e82070b04c40400700c204010284183d120140c240c2840301180010160b0450b210550842201c00003000d40d2030900020203410185c4101350b0100c00080040341c669015440b00c1c0a40c0d001d04020010b01c040224280c1d900252038110796a0840028141401032030075400c4e000108442c00c0e80400c4c20010142841c1184d00200c100c8640d507512030406000c094070070000c1c80c0d40131080c1d1130440039091280700000340301d124104000c42042000070000e171127060590401402401803a18a007000820740c02e0023500c8014641c0032131454041c24020407a518110b10300141950702e540c2196210f0440a00380103901303141407a40b0b9030b00c0c0c9052504100035a68810155000700791620303141c01c2c46100110003950b4400c07211140c1e4410f0f03da100c103000c0034100d14101d4400c00507050b2001a131300d485130005240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633548237 1250 633546987 633546989
    0x20306041506090e0c090604090b0a09020a03020714010c050a080907050303070b0702011401050f01030f1103161115041713091d03070b060f0604030515011406030402010225 76
    0x75905a50303060000ba480c0e8002c845808551060f05114429160301840c80c009120703502c0110392240050005221101c43e5a05c105400742008144149003541c3e40c03695416a000100000c01003030340442e1020520501c100e00c1113240d18400e000b0001d4600604c0084d00501400040e4400c2141ca840000c160030010460180580300040031243c440110b46044411060204e80b500010b508086d10600407865507045d032410b80d98020815640101500300450040080d030540c0c04417a0b803107000c50540c610b00f1100441c0940c2144202d03074118800381c1e40144c0307482444480c03e001a0321440303280e180c0b209256181904664881e0640f110080000d540c81c016005581c864003291000030000140c5c000658045400940c10b00c014071901564402e4041d10b900455001038035521011f00052583d217040e140304150340800a000d01e0800c2d841c1d80302d4a02c0d003001d030039021003503040e240300501900d01c02e45000303004904122091032851400e580000c1d00c821142c0342020714010001000da0403140f800300004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633549487 1250 633548237 633548261
    0xc080706180f0f06060e040506010501140405210609060f0a0c0c0b0a05010302041802150901021c03050a06051c0f05010e03070b04021305090d050c121603080f0108070902030604 78
    0x101c0c52036560900ca400083d00c1d1200b101e1003442c1c00400281031940c0325030b9502c00d94000e8090803042c0c3c80d041c015281d1800a040c85021024104000318199032000341c2c0407d40e070954001c401240c071080c080607160010140c0044007950084e000c00c550320000c18055075014449400c04280402030703040583d203000743c0c4080100f60003960010030800782c096500013412240221005d000040c01c000761f241c0c4440543e04041c8d04810f056000b149920080c10080c00086011b01c1210316165040c0000c12520044455040000341c0721000d0041340e40003030040d800a40710480360400c8003904055045000300b240c5d6801490b0360100400c0c2c0081c084294084a9001030300c00540e6900c03911440d01804420084800301e00c151041c008131041200c00740710742841188201c00800c0345480c81c1105440980141c2403450340351003442d100280840c00761014020072001d52666503d182c00301d240103094188020044070209002c10010480e628001610008903180c00b07d00580d00c3c3c44203404030b0081c0000720110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633550737 1250 633549487 633549503
    0x7170405120a2a143c06090d0308041e05030c070609060c030f02011d010606200c1507060617210f0a0e040c05041a031501080a0e0d1d010c08070618 65
    0x40444200c040c01d141080340f002c80108448500c0385d0b07041200d03602991101076085540d102101c0700080c050407481d5080f071b0044041c0d0a04601030240703041c0c00c40b40811f08980b9604007103881c0428510402410300540b00c5400c18001c0c0d1401c0c090f001300ba00a80a402400704145c4025502d5800d0007980841e8000b004601c000032594144c50400380a090244150400a44248040030303803040c2c442142100c440a09010340307040c40c0a1010060503e000b4801000b0300c510402207000086c040d4030231103000700140c1c2424008000c900c00c1550030500c0a101200f0002c985001d00c1c075a00740180100d50080511244054580040c2070013110b03480c034186412500f0a24041003510425000405001110390400c440b0889201d281150022400244d4031703c0284903a130b02d03a200081d07008070385085d8001124640011080a504007080c944100d00010304040b4850108003440300c4410f514803001e80700c003130800c01d510000650b2001a648503161000c0c00d1180e0f0396410301d07081c1c1c0c4203042500055401c1042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633551987 1250 633550737 633550789
    0xe040b07110a0c051e0901410a0b0705060109020a03060f1e1e090b01031b08070e061e0705211201050a0b07170405120a2a14 55
    0x80111070314030038001c2c14450707640744ca11030752005d2150741c656800f41c40c00f42004900d6441e0a0002c070f1015100f1500c000300700d0a598003405022401200e003a4081c1050482141d20300011052000810081e041184134000070440c5402090740001e2580c1101c1c2c00080c01a0744501c0c28034210010300190300003a26015442400003030340060421500d06c0300c0d00b07500440c0c0c1540d03680c1c0070b43c802d01510400c4005500303d03001d0040001b22003941c80718407030392418100803502113441000340418500104844012803111310a1141c40d0364400302c005440d96064482500d0071090600a914031501511505006240050b154040080034410701502840d04100e0500000d984500801710350030586c80d00402007003c800000d107524150031203034200d910110381207240524a0300c40c04030142a80408001900c030402002a80d03407107240c4081d8143c22100c0180000640c146002403018800e0541203917480300c06000c0d9020304046450f0341c402c80e030740c4100801c28820030030081040020405a50424106c132141c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633553237 1250 633551987 633551993
    0xf0b09190612060e070504050603120a0509091f0602010e1e100603050f0c06040b2508040b040e06030a0c05220617010b040905033025090e040b07110a 66
    0x1381e00c204d0180070350b0020f646403014402200c0007150442d070301d035200e400b4462600c000600205420f1b00d0354546140f030408444003042004500380c0d00e821b60845180c9c40b0b0a20311400070340c0348000c0c0080d480280300700e00c4429105030b520b01500c0c104050742c450001041255110800c000782038107100c11004c1c08680c7e0750b824820f0311001e0701d902d181e4843c01144600a0300d0726203041120181e65400008900349070361f1144160312010a240a95404a801075880c0086030000010300010300e4098403060799181400078040c410080075207654002d5200700c6040780014180c5060030140c0728299001140d4240840000c46070341d92400c00d0240c1140341100201c0c000c000d02c21601312140d003000007400300c0150041030200b110040503024209801c180508000310003c0c911001211103100026590020007085c807130090760307003507070512840480b0607001c1e1500441e00341600c0b0480e40e031341441d40d591441c141002c0b0200f00c004000a01078078018000610841c0101005520203641c50200c540c170b41d032189 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633554487 1250 633553237 633553241
    0x5040c080702060108030703200f10020910030e031b2b08061e010e1201140f0906040804030f020d12020a02190605091311120a0f0b0919061206 63
    0x1454040c014000d20f070012503410720000c211011580d060761101c05405c1031013101002402d1708842500707640561841408805800c1001d4072000c1002c090040e6148160010000110804c2c00c02c0c5061504107a84245c2914000c1b041d40c0b20051048429000e040319040e00c103080c40c1b1040321440190140000c00da42032000c500540c0d59401e00d0340c0f6101400d0301d55070100b203e440001044465942080c1c1c14203c600e500c0b0ba401c0740600440604256140c0611001442c256066409541e4003c5e15600420096440c0080c29503007084060000c0e140700d0925480f4158203110343d01000d00005c1a0540e901d0454440b10001d105403030300b000d8400740784520104002d40b00c0882e02002d911600350400d4034a600601c013405002201e1042e00ca061400b08036001380002c100c84049007103040369640b40091450420360004100d800d02545550256141c4005443c0803030301510381d200440c8d844c21030071800a0b00d807240740c150000d20900c00c420303c820310070b000c07000505269000340e1101210140d019080040503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633555737 1250 633554487 633554491
    0x120a080d0c0201060b0c0d0c03200c0301110f0301030f030e060c010e1005060d0f06020d18050f01061203030e0717030702030f0c030a170904060f090b040b090c0f0405040c08 76
    0x90b41c003e02030581d8a800f44185400b030038001e2001d5400542001c0c0080e400703186c03020040c51103414500a03002d6001d103100781f001000c0886d0100c5801501405005180030300c02d6900081c280090b6a00703200c030004454616000c1400001c041c40d50b031085000615001c0c40524030241c2c002040190340303196000d0040e01821204202c4100703841288030781c0340900e10902800b4420413018081d17040141d02615903901c200b24034030060ba030555081003401c2001c2c03024018501c480b10328400400b031500c0646027440c83c0940907040d80b10715924100050144031903100c40c0551b8580c041c90b010610840154540c0d061000541c4101d1810100c031980c21956080030000c6d00280d4021000d0307032540a03120038140e4550545c5e10039150f054010405a100040c111040c440f05c003c84500c0d100e080c021080d01003400c8400680003041d9501150004111401c46030086c00c0c00090140e80501c100092040030038005440940f4802201d000850300b203460460213425140106030080003804540c00e00d6101401052003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633556987 1250 633555737 633555761
    0xb030d030609051806161205130302071514030415060303120e071d1305060103150509030a020d03020a050c070e04060501050907080c0901031d011b020d0e120a080d 72
    0x4140c00900c1e1031074409401d00e07140301490080d00d20b5640e59011008014840046002840007403240707887d80a01c14410340740300380c400c00411404070510341001ba151070355a900419801c8450607500460740d9025100410013420a01c0160f26502e036450300350561034600e2240c0280e0b0789015800010f042e401442c0464841141408000e4840000a502d84401050180e260282040d03040040340741c0c40d10303004680c040c1040d03480140c6840280e880d5410700e4000c1c0d005940200c0ca541001890721900d1040d40d810602c8000290f19042480c200030f5110595401d041c0103059006c51080941c82c007036070448080350300c2c6c50705403140d00e502c40b1640c07402501c081d5410780d510340c500380c00440e00741440e0200030300500c480e8548141d166206461102c681e072108404a04142c0c41d440904000064040a42561503080b4000301d220b80032200000c88440f035520b41c000440d0b018a141c40031a0750007855841040d0800c1c2d8480041e1212014410b103040c03000e203001070903440b00241e060a070f0050390784002c0704a070b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633558237 1250 633556987 633556991
    0x20919050901091a0705090d031d0a210201020f120301031e03080109020702040612050d0e010905130509030c03072a030305030f040f140106050306010b030f0106050309010b030d030609 81
    0x8900040c80c2c200d0311003220081800480c1010310070700d002151242c980c401c05503d41246001e0859020580c0c0d0b05550030103e002c0340131410989a421078500881c2000b41040d149080790030b02c0c1802422140140340c3c401c1d21003150301e06410302075920038882c900612000c3d004640c48136103080e603a4074084d8000d120903622180c4035084001c01d0045003140d551240d4150350f940906908120144009501c202e02c108da000703aa81c030000a101c03e0112182200c18056405008400c0030080c01804008140030b28038100150070406101503179402c80c02c1560190300344e500265079950501c05d50315620030031503074460511002c102e07070041010b144007522a240351846500d00c080ca101080300d1120503e804001c1c0400d00c10300000b23780c090040c031040e0340305e801400c0444c90704d5015280e00c108645060166032082c4d4403001d0034402410f0230000d0710300502010410618501d403600c80c01008103010300511081044c00070118008a00c2500502200300d40141518025840d40f10094014019445440c9000e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633559487 1250 633558237 633558241
    0x60e0f071d010e0f1012030504092307031a030a081902011b030e0307020a031407050916050c15131103010902030703060203061311040302151c05060d02091905 70
    0xc60881e100d54100c640c0c00500014039102c3c1150030102d1600200f03890703560325008000182e0b101100c1103150206010342c40c0d50740d0b2142484c42e04403d4400d1943c0c40c04407907030302101d02840c8000781240c0c2c2d07500c00302d1860009140b1100b218804940d0990703042440e45403003030300c1100c0c040c0100080141944503030710300c5900040c0900e81069090720203010803810980c640d0308200c0320f0940030f81c000050510940c010b80e45071000e540d00045e45118250010b4400b00e82c2d0fa508e80c0701c2303100c0810a070701c00740c2403c035025441e138502002800e81c0b038450005841d04001e008942c404080701c1c2009900f00046007145503d4240c40e140000d00102c00c242c6406403100721080003041900d060600c1200d0a858010380500301e0303d411500d510020390300c040c14130354100043c2000f044900410b44a90014540074060b43c650b194910700401580f00000e55003d1036889040050000d0001d2014000c0d662a200d03040202d021fa0303407500015005081c42001942000141d800c12400008201421800d01503c0740d04101c2c0e9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633560737 1250 633559487 633559529
    0x30627030903022e18080102070c03141204030302060405060f01082d0d09030515010524040b0309030a350907030807080406080f0c040909060e0f07 65
    0x14185241014010a200840500c054200070350080d0401c0c919501900021000d00301c0c4e0b2005000c074800c0c0d9400964028140c00100c5220034804008080c00402035050603c640c0300d0300700e001300318417008100c11420041c4d042640d0051005604000e41304024940f00c1da6a81400394031110100e40403203c5000f040c001501941c00003854a042e69400c500800c0100d00700300600b10450204214001c0c0d60448641e4058007260800c2106400c15070740e650248c445246181803440c0c4010f00121072000b00a2a0041c420368441d50b000087c0c001a202410b007000507440c03104840c61045c0c3d00f0034450341d44008104400710600000030f02030300159507291015101da07406030700101c00c160a00b104030041a03d0100f050001207250903500140640c040e100c0f04da03620380c1c50a80580c801c450844041d40c0c0803c04009441e0095400e90744900440751198003490075030000d210504c5140039003050f560703458000000303001d1b00e030b4081074059801100301c441241001d0f0080d80d46a8a07407044404c0c5600098543d481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633561987 1250 633560737 633560801
    0x80a03060b0a14070224040513052e03080d230403051602010e0907030606080903031605210a06140d02030d08060d0b1f060e01020c040f0f02040306 65
    0xb140b100c2d585075044021000b08000241c0d220707000c1a6407000d00a5030001c40019040c003455501ea445a075000d640c1c80c60402404061204107901c10002842c0408014020400d03c40d12460702e01925540706031120001c2c0c001414503e5a00003500070f0707001207401000115960712491000c44499100c1d01c0800c60f2007184910008110340060014205200068208018501010410b80305062160002c401e000206100c840110798030030000e41c40c0d80c4d0030011640c1148585400c6101000954607601d0810810704200d0001c80440040000c00100d60222503036241c0f18075800c3d2013910f201c40c1c10b420800c0d0f558010305003500805240c030102c2c12480516241141c0c94030185a0301901800300e0700c15285060b81c4c1a0402001c05410859a00000b070014001c40d024078420f000c0c840c40d0350113124001400c2400c403150340d0003000500c08071405544940c2e800260214100d0000c540c0807580c045440da2020251034280d00a0041d140041008030030015103410858515505803d04c406484032540d102c1c4c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633563237 1250 633561987 633561997
    0xc080124050f0f0f0423040c0f081c050c1603060510050f0f03031204060f0506121506060c0a063c09020f0a0e2517180604080a03060b 59
    0x94815801540c481a40c00c0c1303a080308480590090002a02da03402e01c4000c2c0c1c2c0b0a00b00e02950700d5442643c0204030411181c0145003001d4183c103080368001c14140300040340d0310b190310f8550143c4043c5181891080074070620848007404100d40903030b03d0308440702482c801032602e1400221001030410000074004500c500100301100c00041107000f040c0001010302c04200c42252403540c06010400410140d50f0440385024003980c86140d0001d059200007090f40708490000e084148607440c039060483c0000e0000401c02042c084c480c08405607500c603180043c56603c265201d40d030309801713030130360307e40510400d68004c070f00c280c440500003910b10011071030590050980304681c00c80c0c1c0c07aa11038410741040481d8030180506101030a0316522440c0700c800901601869800b00d550490040108080c061186100292a82000c07410018a8032040b5014003c3e5250070908039503026400000342550509584160316840303040b050b15000c3c101410074070f8ae60341c0041d1003103011034244070000900340e04c0207007128 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633564487 1250 633563237 633563239
    0x9180b15060a03110903011d06150d03030b0d0b01151710030b041704090903030f05063d0504051e0a1a07061103060f030a0218040c080124050f 63
    0x34a00700d4941410f80c010169010240070040091110400907202449002008200c507040030030300e4000c0c205c207549007200007090006a41031071500941141c6800c03005c004099810708000c02c401200601040c0c1c0300a01000c060007008498000240c503032000c0c0403441c0300071000c2e600c1032a000065417080c2c1d0941c030f0640d590f800154001c1380c1000800c0e4481d0120360864410f51080b400d00e411503c030850560055002404510390b40c0d0056010141c1510500c054500380c6001400341c0e24144001401c0103c2c03807075400001d018115032649000d071041803110344414030080e081039050420400141513070003a001361030095050000c100c04641640318100d04c095001800443c1a0f030400302c41c1807a50360101c4140083c09424818240019200c4c09044000c40440c0c40003616403130030900300b200e0951011000c41c042e400c50910b4201607280e02e01b503845c3d8008860001b05140d15145054010030f41d29a0003a42e09519100300030310855100d000c0b4500d80c005141d030217002103498404002c16440888000d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633565737 1250 633564487 633564499
    0x1a10060206102606091c08040c05090a140a0906050919030311070203030d09060f1505090c13080708060a06060503150301060504020c031b07030305030f0c0409180b15 73
    0x40001c0045210000f031840c10303000c503c45400c1054040c4900d0440142c0b1403500c83c1e040342d050a18103081c4050030701d165824a15009689081984804401510b503006a03805041d802e00099100c5485070015035440e0300883c0d1042c194038102c40c11100515990904581c50f504200c0824289180000c0301f1544001351041c0c115402e10558080d4010503619070070000740700050112801503a02480030301440100b054002c904500d80e484d116081310740b9240c0700b2000c1442c00c2c42000507008503180c07142c1601c406403221a441c1e158042510342038000c50400003240c1240d403502285480c0007050020484021008440180d00c6240624050703076018017903840040c80900004940500c484401c0074514000380c00010925125004a01030340c1c400813400506510028282c003203440300c10404079000c0c0803c0f0103000320f1400c40c0c0c1c0c010041c0c0f04c060981c1c0428603040303000c90000034503982201c0041100150410056034080c0d5080c40b02000c10500756000c2000400240e00154500280000210000c2c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633566987 1250 633565737 633565739
    0x7030806041b1b05120f210903161502030c0a0206162703150e10021201050112180609060509010b012109050d110d020a15020d02071a1006020610 64
    0x203581201d422910940c1d00d03100e502410100002e0440052005104104a25580d0074500c0f4902c001501c7c54107040c10441c8481081065108022080c1c0e02e1100c0d0b0391060541b102c00a0400c1c4400a0398003403d111020310010034024040c48500050403043d580d5000e445188c0c1d90601c1c41c00d0190380c03901c40040420b40410024031010a1038004009154407049045803080d00c03a210841d03403c1041c00000000c540d2524100341c05482040700540101080600354586014020003400303400040c41801e0510036002c8001442d80826080354140d00f44d9403080d1407034900c540c10210041c15681c038058420502d03003000b00746002418001d800c40283c06840b421442012140a00840c004008500c0042a900c50142000400a00103024440d501c2d59440248004040c0ea490412002e41c01400c19507100400b4100050340025403043ea01c0809100180c85003200c00d10358001e403241420081c04401414105002041c04240780c1d40034420312900400d02c90345503c4142c1e031b120b105441079860581c040e14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633568237 1250 633566987 633567017
    0x106031407260a14011a09040f110619030504060c0e100e040b0d060507090b07170a2d08090a0807080d060f0f1509060f0c051207030806041b 62
    0x12004a140b6a0281202d08201064940314880c030541d080d41c558994403103082c03c6064031079107107040d860f04040303400006608003a03841d8048080e00000040404503000070702c0190741e03100c0e0140c8064443d20003910004906008004000303003000c69080313900914010603040720302e220312240c00002c00080e114005003020b04034140d820409002200d640a51100307085162900c134030038404a0380c0d21480010840d0f003803015026001007142e400000c1c20985c24400703034000c070301c200c03a08100001c000c14000391b941100d44401c56009190500404003030801404818407003046002c41c0c988901d455803542402d0711b9084595855080184000c0d0100c08203002050114194100400003000d50120008034559100c4005800d8a40380c4c3c0207a00c60141c0100c00c00441100a088944040652505800003410228054203151180c26945c00b0801d54003100003c0180c10452039500e40707400c3d05117549481c02c171b141c014420300c0200e4a45010340e0a03d410501c4503052100044000c4140761101b00d00c0bc181d0003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633569487 1250 633568237 633568289
    0x70309020609041e0f02070614060a1a09100e120f2a09131a04030f0507021513060e180f100e010e09010c090b0405040221090106031407 60
    0x105114144445110058010041902c030780100700d8206040582c480c0d049091220481d601c0c0002c0030842c1d00527804011083d5200c000010503101a06050841c0400b03540c42d42c1c817180100088545c001d01081030909003142c010111a4000c41e044500802c810b256208050710b1301840f00c100c0c7d180d1741c400c2140096903641e200d2660340000e04030b030044010058080020f841800260307003440d00c1d003c0c0d05455a007480402c14914124400f121030141003414103070750040001c08030f44d038807904014000c030359401150f4a01100015003070144001c0c903120036a4408400010095101f010040f480c00294615981070007103480344d000c402d206071445a41ea5103c07c0031118030b002482d150320302130082c10124400c109040100d0203480c0d00d880350a009d10305100482c1c00c66586e548050f081c4201505c0c1040100f0a42c8100d4007552015207025031038038420820110032407610484050507483d03142c2000030003036056000b0402c0764040c980d0103201c0c804690705951142c3c004c0c0600306080000c01d22510405201c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633570737 1250 633569487 633569501
    0x30203030316050f0708040e0726070c061a1908031902031c021309090c18020c0609030a08011d0a1104080d09180b06030a0905010e030c0f010507030902060904 70
    0x19003080303481e00a01030600c0581d40e000d04006c8603a80300102d010311200c04090b00d025400700007410000d400d030301c1d086006000000c1c0c01b40c4403a5491407400000b80c846209002d04242194042020300008030440b000101c08010f48000d40d00410040c501c010580e000948071074129002107000d1841c1241805445130b0301480850b00d2000d40c802001301004040c3c007070302c424619640f034940060329206500c42604280485030701c00e15540d41044451008101d80c01d40d982c0c2203d500c2c05078900301c0220304611802a01642d8188e030040d01940341003001640c4088018596907074582e5400440d680c0b6008035001d0020f9000304e800d0030720320310310000e8a101c040b80c1c40340d54040c000c10b001c0ca080c06e6841490030719040103080c101001690000c4100b10b454000003046140300304010b001d01c41213988201140540c04020950369915072901a8102402020f50001c0d032810190b0003070f25034036050b0b030502696881d14140091007544c41c02c0001010f0310721905c901c40b80143d008210900c0c0800d2101044042c0c201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633571987 1250 633570737 633570781
    0x120b1503150105092a09040c030623150a020f100608060c0c100507020a020a1401020c0409060b030f0d080108010b0f1e100f120b1f0e10030203041103070302030303 72
    0x104145109500c081381c5100b031783d200c0c0144e070b15a568101c030b803003403209580c00e9601da0404c1c182811f805208456955007075404e0402d80c02d00310311000c4100c100080d1800c42902c03207030112200010f200c25140307502151100c2c4c4000300740200c9000060017244003088914030310403142c00780c100c00e001ca400315000100520180151800b12007848041c8880c000c100ea2050f91190091381c007080c01801181019030b08003004000e070451520701700b403010001075110900c00950610850b581c903000760421a442e4807070141d0b85809400c4900068030100842c3d6a17040c01050140803c520b1000092800c50502a03001191b102403d4000b480341500140000100488000130020f851703a0650092034032000346d042541c29199480c1040c40d600006d0182c002401303185d400c240355042120810054075202201490910b84107024200241524070854030b01c0b944000880d440310004102caa6150303450703005140250b0040744402240703510a0100359440c48075101c0203405400920000b140540d51135081c3e202901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633573237 1250 633571987 633572011
    0x90304030b130c061706040e03031602030d021912050411041e0c0e01090608220302030705070b0706050a0506180a11120103050c010903080403060c09120b150315010509 74
    0x455a0301c0116140f080c0e001440055082244580e58200c0e0a8282d82c20500c2a1000c00482200310160307034491000a18821840d003601c096a05554030800c12a50441d00c040002c546800021000d16600e4001c054400000360401d5801c3c9105030842c40346500031076204a4054101841c60b081c80060183c4040ca1002c558081d0840600018640280e2100210b165510858040000000740c20301d540c94000c5402c00001c58100703d003034800551088080130000a0180c800e1725245000c0749144907405006000303000300c440014078004504003500400344110780030711042d517400006d0381c2240c00459035941e00110541403c1c0c280740c509298a6000082c8001c003140040715442d40391000c2c1d0250a8100e40b05440c1d80040003803080a000c40d00d5151003d00c0c0c0302034a07902d03540360700c0554020360102811007981c4400c4240c004e4040c180c10001402c040c0c035030b0005078002c1e0074801e0f444030003214050501d04038400a500c01d8540814034002c4503000f0000303407403d64205800c1c48a104002030000700c0c0c1503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633574487 1250 633573237 633573271
    0x50a0209030102072604050102060c3007120b01020d14040518060f0904030903080a0905090a14060402040f140307050603041203060501090b1b010f0606030b1503090304030b 76
    0x10710300380010000680180c010b400c0e028212421500840c02500d1000c00c1118240424070041e03901142d1f064101c0309008440d074030390044140480250000303d041c0341c14603030032105180f00c10a150115a10800d2180c4402c0ca0380c4031a02000000d80d0110342c0070b0b60068014840520172140104014900d01e00703030340510380c103058650000c1611a0301200401d4020f00d0f030740b41004030307034500322800f49100c11060319040041d003019900500740c4815400010907410b004611000e41c039100c0c002c0340c0c00516000b09144020704040149400401c010b8541c55142280d10340010003c5c1000d0013258100e03070f0901c85043c0060704e4141200d031821456132415506000d10800010507035900c0000d540034500610103020a4040700d1006007c980c0719034862410f012200f00100f0a01c4000e9041d102400c003804a103a03451454181003500505858480301101d03841c0040205000307601d0740c00342c2d0b0801010790b0780c62007149800c0c8100c1c41602045641d003065034401c00c0240009182c0045031038110301d40c0304404400c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633575737 1250 633574487 633574489
    0xe240a0e03010f06140a05010905010c05150411030d0906021e10140f071b0320060f0a0f090c0303210908090901140307060f0e13050901110f0d050a0209 67
    0x14908940d800b440190310f80314180308500c3c02d0003090021185c11112803400501c0c080010300980400d2007528140f2003015210301c03d1040500c07400040d1481420070605615152408511030740e903207045a0300912a9000b01c2c04001d00030170701801500d245400800d0034000c0350b204a58502c2a8400d042d826015541d10303c00041d1342d80c015141c0d44040345140e10b00a01c1c0c80c0c094019100c0004061034104080075076054a04d07039500c00c5901e9966011715004030018031100041549031940da41050040c07050b80104105411451042401185084814081651802e0607081503604a901c0030b401b012070444100b0020b40141481c10300b1059640c90503502a0b003010980045a81c821819151070303030300003803181440c07403d0b00806024120000034a9009d152101c040303692203055000302c0e400d000312002c0e55407050f40607400c05400154000e110700042841220b02c10b000d80350690300c1244540c20309002c20f2800f8840c4048d6240342d500500c507282000024807048000c1c01c0041e14070980716034200004415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633576987 1250 633575737 633575741
    0xc0b04080a0c050708010e150705120606090907021c0f080c030403031b0c0b010f03030c0b0604060902210606071502090d14030703021612060e031909060e240a0e0301 73
    0x17010010f00006001150403212410000c80510f0701c90504101420010700c16080815100c0424446c2903080d03440d43e4410225035140b08a0744110f0348149500c0420889550000d6034040c40d0307000002e1208158050a0300340d4040714442d006c20b010620007800039400d6011100a50f03800b03406844c001ca1950301040649843c03d112051601c00906050200c0c0300b8072050b4a02d060051019840805010303286031001003003800488801085880b09102041c0310f03aa41d40c100c0c501070f0004040071507840c10f030701c2d030301e100d10b82c204200320f1408452000000f2850b14024041da20b465800c0b5941d800d01d01c80092401000354031403850740d644038141c0180140460022440b102003d041c803c01542e954009060103481c00c41094040d09244030303503160500c100200241c0c2c03142a41d0344240c01040c5201c038124420305500884881c0a140c0549120415074241d100243d6421154a5191040c6246c1408188085650048005141c4240050300c241940d00ca060041002248070301e01601540c1210703000a013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633578237 1250 633576987 633576989
    0x90121050108060405060709050f3102070215030708060d0516150806030f030d020903150a060f211202030d060609140301060302030a020d0c08030c0714010c0b04080a0c0507 76
    0x940c803050803c0b00f040000c006d880c2e0400c495080c01d01c3c0c41c40ca00f000240d1740c18500101c56010f4214074500d03050880001043e819043d0b04510103c102d0003d0340c14410007500800c02c141c3c8180c0e22082c0207c04120420308076400381542d41d40d10b0084d03a4403c0d05000500302d05001c2107400c0d2280e01c41c103084900144000c0c50180c03842c114606298203110800505001e07000c1c0009110b03801c4044240ca43c000004100da05a4400d25005601c81d501040020b007003500d030f1400750154003c4102040b0140805034007a20039901003c40f503804040d10b0f44600303000c10303501c0880340521500396002c0700046440414800084c3d4881d204480c5061802803070310b416030789164420008568000c0f000d005010703c10008568804003030340200011031941e00042d0340c402c0b00010190203510f001c0c0900301446a09100c14001d480000120380e515031601810030b07640d803014890486d2200402c4c140e070a9540c0308040d10454a034001c01d50081c2e6132280c0d1200540c070742c024442d8406008040e0074200000d02c003400480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633579487 1250 633578237 633578249
    0x4090624090b0d0209091905060609010915170f0708010e190b2206140a050106050a050d201809060901030b450607080708070e2103030a1a060901210501 67
    0x109c10300b046002c2c01401e800c182c01c032402850401407120b00c00c002980d021421100c110215010a119001c5081c1c100309445010044500800b0804074100c5030540140b8500f4042204131450340c030414a01c50171001c1c00318401000f100b0898081032541c584207003017907284141b00c2168013078024240c0d1140102c803001c01a0144004032002004a450054440e66006112504120b86072000c0d03a040188140f003010f0180d100141e881c40300040210700030b03a5540c081c40c002500182e50701040300c113011407a004030244c5e0f8441e5400c48001140d0307003881140300b4102ca40c00344402e0159118041c0c2100003001c5440721000c102188003075080a080384540c0084202e0105241c810040d042180c0c80741420001040c0c8c8c818009944140626998880c00e050341c000760300c0c646034008803004800110050604c522115907242004445900401c01200030340c010561396504110f40c0d44401c0f04c010307402240d40d03402903004000303210151455000c0e480031004080641400c0c01d04941500300d4208032003081e00b2075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633580737 1250 633579487 633579493
    0x3111f0e0c04050903090d0c0506030108030705100204050109060f180f060e0409030905010f120203040605012402030a0c020a05040c08041202070e060f04090624090b0d0209091905 79
    0x440002401803191403650001502d0a002500c3c000000f00d980c0d1044401c4a800307245050981028403007851006400f8010040c038160b035a5a640c01d00b25601e4000102c1500c80740649a1907501900e803c6c800c80d8212141030715808441071400745c064480e110f00b044000280255006140c40c020194003403c0c0c05000f44a0041c6100341c01c2c40802040e41824010345800340340350007038030300100c8d822040c19000c40c1c1d02440c01c0045241e80c00001c0781d181c4904408158600c3c000b0091000f0013416030040d505a0b9490060110700119a20f10005a07501840400015810030422500e000e17114816600c031403030000d400003400940c7c840c0480e0484140c1b0004100144803030092000700700100030100070001507440100f07555030400c4d012a40024003d8650ba200e40c410b940e04003180e8840350000e4070881d80250040250100b448000b000050f50300f0261800444112804210000e1510442011000241c5821001c1c510b9a0901c03050b8003004d0042d14052040d80c0c401d0b60369013102c10441c801a407164010b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633581987 1250 633580737 633580751
    0xa0b0f010503150a0b1e030103080909040c230f0d0f0803130c03200901031e03120c0804023609150a0c03060905010806070c060219091701060b030403111f 68
    0x900362a030f4011103d01b00082400c1004001203580c0d801174600f4034000302d0701e6030140e0301c99282c8a000c003c229800b400301a0034842c0381038800e903070240104504103019a03241600220540c10003902030f00c295002440b95000c581810081108507001c0c50307000c1d94101c280d4002c0c4a194690021960250b40100c0d03c01c0346030f00e88180700e4418080303810f41e0000103440403003047d415943c0f028500a08140340c204012080c20144060510490000b10080007545040007040f00601d030081c131440c000c4406078090400748a807005c1c54204201402803050120700342002c1e400703d00d00420340400c4040d201c804035109400c0e18144540c20700c070040703008910400e000a504201290080e05981442e0300c1510b40c0307441c0000400c40c1307400206009902580394540009440c00701e1428000078000c88040f8164004a01c11107000c55800c681c2d15000c0e2aa060055400042c0c0c00144a01ba00c20900070b009a408003031000c107000900032050050712117070031b105907643e007208400e40c0130b070025002e04040341190302c0b104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633583237 1250 633581987 633582007
    0x180907050409020d030e04020d020f0a0e03033103140d080a1a04090c180e100218100c0501020f0a11060103020105040513090606030b0f0a0b0f010503150a0b 69
    0x102400003050140e40500810000f40c001a040c0400d00704058140b002680c5481e84940e141c0d4112903070030343e02540440d12041500c1c1001115000a4204000720740c140d16400c1c0c462a001090342c10f245a080c9400d50040c2c2c00820041d00d100b401114903001c280c404101100040748001040211010350006200525411100a10101e4040d0019030100e15051051090000c07510200f40c4510003a54041405089442d011100540d40d0b40800451201c0000681c0d00e69000c2d0415a0a2950074040b501c600e604036a40d00120310400c82c03540b1461026407990342c490700b8490b4854881e140765003000c000000040d112242a64810500440420000101c000c5502d4210011031107a042d541e005060541c19503001030264415806060300c0f0781450030084075141002d030492900240c2c81102448076591ba441d04089a4005440e03c03641500c0100001e4204902480340051f0300340001c06001c51142100010b542c90f80c0090a154103c1655000d65002922001c5800f00100444c0550640c0c83e02c01603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633584487 1250 633583237 633583243
    0xe06280e010f29030318030307050f100b180a090503070503190f02031903020c030c07030b06121c03020d06080d0e01080c13030213330f0e0f040302010b1809 69
    0x44803003091450140f4802d603240002903a10115503da004c540e50b40740000064658050b0010041c020304c5980889404004041441c41c0b111003800c0062088403091010407880842e804266150000f42d0000a101c4004540080d200c09029600341c1c0c1c54120390f42c07100d07415580258031107403900c04407003060b1000c20381c021340c10b5000e444280301030750804c2d10b0804c5074a404854010204209600841e811855043c10b100b1503030404c5a0310120343c0e01e6a500e15040340052802c40f0b030144110410341140319001c0d13000c91010455074040190740c07541c1d4000807050f0000d4100d1124041815514203012440d600100003016482c6119250380440015000c001802d04000514401c0b45000920100128021349002941540e504458603030035200d80d9600c4070010102080302005a007030148210391510801c0c01070140b14034252506054064a815030f404400e0001c1c846c4c08050600c100000e441070505038000c6030481e21905c00818494030500000300d881046203040340c03849182c0c0080c03281d000010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633585737 1250 633584487 633584531
    0xe13021c0e0c010309150e1614040c02030c0616031503030302120603030901091a0705060106050703030b010504030206040909140111130e041a0406140a06030201030e06280e010f 78
    0x2440c051104c05c0d625a1121030209504041030300f056182c00700000b4521042c1300d1036a00c0d003503407442984d6075503881103494007840002c0341150155140c100410b04103071012003110b9241151500511840d00c549011610003003c120108040507070303480620f0099a51845400020750090380c016032106540c2d00d403099406005055184243d2041104940b40e98000b0187c00851303000d102d500124030f1030051795040500c00c02100410303d00520340007060301504440500302c070601941d0100803441b030b80c1c40156a503100718000030398002e07020b0000f0841c0c01c1ba80d820880c480d0b841219949101c0b102c1080340c5080d903242c008991400301000c15103c05c0d078030762841040000c06800d515104507042c01c0c0c5504007003e000f460f00204005801001405205142e005803240c0d52103040030302410324180121b10002c00c0300e80801c0740040d08040355400380d1a00020004d0041da80c00410340c02404036001e00c145a500101c40340d00d0080d4a604000484440170321032f480b0081e050303540c0410040d4014008891407003074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633586987 1250 633585737 633585739
    0x328080709050913050c1002010e06130b13110409050d030b22022d030a140907090b0d0f0803060f06040e07050a110a03020d02060108010603030e13021c0e0c 69
    0x3524041066503107020000d5040441131180980c50b64190400604284090f074002d50046c6d0f21071030109a2540c158040480400c80303200342c8946840e14007401309032281c100b2000d0005941140800c0c00c94010f00c0902c17100c188181984650f1030712040100e81a1410b121013640d04c0d42061203500b08064060140b00ca0310078007140e0440b221420800d001203201048100340345566404542c0100d04001041c6103140b003007070030b55054054540380c40482400d0703100b110000740c81c0d03050800c03004650f0001c000184c01400703898042e000c0c2c1810051500c0003407100e4030f503132540304021402d040042000300c018600080e015a0300150741e494504c040c001c0790a05589254040d0004000811000c0690f4a506400403880e25001380c3c0d980d02c09108230b0303000405581c9110b16014410902c0d0815070001540c81c9840c116809607049680d850031070034222085444003401094851242218506d02030580c40601c480c041e50050400c1c074404d001c020071400c403030302121155541d2224094400b50400c05e120307030540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633588237 1250 633586987 633586997
    0x1110703020102071802090a0807091b08060f0604090f1505010908100b031c030e0705010807050a0302250c03060f0213050904050109051605040b0319080c03280807 72
    0x480c550000b543e40c141071082d0b6090510038a9101e84080aa40484405402c0107000c0d54a05840e00c032000d807a00d145115800740c0600d80309403c001c90300580041c3c1c0ca141c0e0140c549a0995a4000510070703406250034440340d010390200000318450b4014800d031010355a08900009007840d680c0c40452101c0d13115040305050010094081000040009020205040411011a859520001091410980c07014400800c0c1c5c0a10100090075456448203041c3d0302d0040454003200e50f11401034820f00026561040080c004104644401d4041d030010403904030111040c0c0c4100001c0012041e91a0821000711480305241c1000c105004035402824006c552468046180c45c50a249122512006204860049004200103010702c0000e6004907107003078102c1300751381c64500000100c100c0e0b20060f015144c07055240100c0001107040006000700a03060a40340e07140c16600b103403164525030f0801c0505ea41140b100300000142c108990240340103911a141c0d61036002c024160000d045010b00600d81e5007089 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633589487 1250 633588237 633588239
    0x4060e030c030721080c03040303080a050f0103080f0a0207030c0f0812090328060f05060406060c020d06150315050406110703020c10020c060c060402030d020d05071709090a0b011107 80
    0x41907001d441340c07802640300c24001001c4c3d80b45040e403014050344034100414000490000145504074076024412070800b1001c00a60b0f507008080c4070025020301020f03001c294140111440e000e00440100225111030049407041a80c2c5e42da03010003160f15412407800720000c0d05c8200410f01c0100803031043c2001d05d0f030b1140e080c0440607011036034071a807160341c001c1514000c59681d440d480440011008070b80d0000401d10045640000c40d2010b0f1000303485d1107000354584100080e9151041031120000c55000b880d0100e2030311542c8071180070b00140900c001820a04a1000002600c43c41511071611705483e4086030301e11f0316040c03600458035005070b40d40d51071404010141c0040d5004c030300000c1c101d5040303984501c0d802400c3e1040f85420002050240c001500080c0c0103000320300010501d20480c17003201250104c1c00500822a1a1036181d08208013003101030100100040c0c10700800c643d9020040903180c10180034800041c42c0d501c0544007450078a543d820224003d50b44113110603035440b04000202036807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633590737 1250 633589487 633589499
    0xc0602191815050f0c15091e07090906020f0a08040302010f050408031303020c0303040306020d05010515040e150d081e0f0418060f0803190e0d0311100204060e030c0307 74
    0x1420122882108003c00010b0b04030b001ca05440c20398880031074000455410303090b0440702518051040d41c8154140c403a01909440d0030425541c9412800c4c525400f81074610300c4c00e0080c00c0500807200084803015000c0c04a0800616020080c00784d4204568441d09107007071600300a1308503110400d54039182420000cc10000c18049021a90007100c0c2c528941001c10960400300e05003044201d09a9040c00001000410722806030003504441103160b1040000c1d0f640c81d401c0104084003807035102120701080c8000c104a180702c00360250b02501803445106244680e4002070301c09d40200404642c00341010803000056a01c2c810503603030046031060580e181900c0d40c4140c00030b9010754031a21040040c25030140b104400260050001401c0c00e05c8105859500e5000b11f0b41c41e0303004015030107404000c080b00194014801c180510740700703101400c100003078200c03514111401c00c02861003000c02e00c201d00c02c000805280344000c000402c1c0d590341d01d42280035840101820035402c0c4510601c2540001810309c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633591987 1250 633590737 633590759
    0x3140405060a0c0302012007060e07080a08070c08060f010305010c0c0830040305030f09030412151d0c0114190e030a05150610020f0615010c06021918 66
    0x5102e8060808038045501c07450124090076441d42c403c80407030800740380308040185803c0540741040c1324000c00c2c400c40001803403241e5250220320a581480e8030210310800891f048000502c0314038041c2410070850b585a03501c0e0340c50400c2c02e8071024242c040d84001041404028420210020010701c3c1010350900c19403503421060080c40c50082e0552203001c0a40f51907003a140c84400100184562254145000e08000e440c1d900100d5080b0005140c510005461041c04000c41d4103880c1076840d41488412982c50b460705c01c2d00301c100200c0440d5030b6450021444650602c040c810300680c0002485100c2e455000184031400f064400c02150b00d00703018a02c0302001d80e60482c2ea0441052429128040303006002170f1070240c465800ad400d500442003038800c48030120340420b12901081c0c65030788205045c203400301d03940e501055144031203402610201c3c0c0d14200716141690401030502d0701c4946003540782c5030725080340c1c01549481c0300003111035820050103420030007803c4694440c60a10070549d14000201c15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633593237 1250 633591987 633591997
    0x6040201050c03070b13051e0d0302030c0405040e07030606291e0309070f1a07030806010e06121b09030304210b090f0c0603090304170106150801030314040506 70
    0xc1445008035042c1c0c0c0300102001038840080c4c100341602118140078841050a0001100a65107409811048a1585406500700d01707120a00c800800340b0080b1610210001e40002d0032007002c0c040308100000b02541c0c1d90092204211454000c1c0c44650b2940c984101180d04a5011204014030f03000a44800d140a85251110401d2001c500d41c0c6c600391126140c0d64140c2e001a030b13a035505404828002020000906072051b9440c0074101407040303498066005000c02c42c4580a14042410410600041c0c42096402d4002d078040c1401c01540c403103d00000d04c070750003840710780039244080d40c20828554000a000c0351151104400a4030f450405400309840380b04034001c540c910b40001e120502e100701c0440420031480e0f0841031035049400d1000e0700c245c5815945810242610072814810380f02c0c90000200c90087c403580c0d009600c0d0900d0006000414908087c1d500210f55861400140c604171010320000255407559030821250f045107400b070100101d24400050715201400b05102c0740d1650b80c1180c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633594487 1250 633593237 633593239
    0x60909060c090d1502040f090c03050114040c090b0301181104060e0d052805060a1401060c03090305070b12090d050403020418150b131b08190c0c0303060b0903060402 73
    0x4100f00015040807001d034a0b5034400c201000b40300040c005041e956180b40740043e05c01da00313018451200540011025502c0a0140a001d00b145072414091487c003070748114400304071410440f0010781c1e9003045030b025420980c4051900c2c400e1100d4260003a809100d08561090992031090415040c640c006000d9a90061310502031300401040e001400000c001d100410501c0c0d4210119991007860070000c0c2e1a07030f1950494042c803806010030030340303165030140010619003420707240c0403a80381403411101c2e81c5060303030103409010f9588000700110300140a000302400b885019039503900002100740b802410000c0c1071039416000088003c024130342c0001103034201c3e601201c001c5000b5200b00710003c4204003001c1d0013848600003040d0000d10304101e40140f84110b02c1201c040c7c009079409000700007510811000c4841140c09140e040710700340d005d403000c0350b0040d00600c45618030088403d40da03001c0b9140791403d44003041000002c402095894080e21001c0d2140d40c185508102e40200880d40e1713083d002e4802 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633595737 1250 633594487 633594499
    0xd17090c060a14030c071221180f0b2d04080d0e100f06050a14040c020309030618100915110d0f0f060503030a08130515010806060909060c09 62
    0x107141d005104038040b10f500318a24048980e0303420110307016170103940205e404903000000140641d086500609040d0349010a4031100690781c514003a604005141e01c5c0d549410200348070f4481c001180c50050080461842010b0214007428910341090f140f03098514824403d180040464004211032080f1036041544041d210b602c1741660b42e141c1c005002d01c21095003c038414452003500100701500030300d41c4507940c4c800c20070406441c3e10500c1400766460080c14007800b20303601140000d003090740c0300c4412803155205032428801c410000900703008098030751404203181c03141c0200e40c200b014004100c4016051808128a10b0280d41e10454060f00da04a000f003643ea560780300300d11090300d07411203548600102c4100484100aa50440141b03a03005410403c00e00d40034021885040c000211500702c4000c0e02c4190070355032004408451a00f41110441c0c150285902082c1440309400c0b915000c1d2204402401d0145008401d004044030700a04500e5254007050900903c40e10090171524841025205 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633596987 1250 633595737 633595747
    0x150105040b0405010b070830070305060109050f06031906081522030809070e0a0621030c08030a020c151906030321091a04050706090503030421020904050d17090c06 72
    0x20b032600500120f0100000349400c2030180a08d0000c0050003072080c1d900340c500304026141e240045803441840d0090640080c2d000c1100c06007464102e01466101e07194480400000c1a003203004e206540c0d072640278625581c0100b1440403440d0014425a900a000e010b40b91080310010424401101d00c2003005010f02c01c22401190713a0900c140040c0c0c018004030a03038601c0342c1c24030004000080c80f90b03110b10050404210881039a8203095000000da09400d940c03044010990b540710406550320161200030441e900b04080048080148502c1004441e12400501c0701c1c600000300354000c3d498002100800b601d020014800030b60402c00c90200c0c1c00c1c1c0008030035000b10090344490000c00e004031014043c84c00644603140c45100c0440c800348030307030700c61070540345820380d50740c02030302c11150174010203505400c02d104c240308035002096010000081d10000c02140640d80c0c006c5151448152815113041d046100b07440002078219034040e050625000c2220014907001441c2a110707888948094451800003a0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633598237 1250 633596987 633597007
    0x2091503070302092101061e151e030209090c160314090a030b01031403040602070e060d0b0a14100311121c050418111b0f150105040b0405010b0708 65
    0x8142c5034103a00140260070607918a00e440344150a20320601700d41076003000c0020580d60071801c60f4441d1a0840074184118504102c1400000b8003440301c04010402e52880c0d0031a83c19210401701e112040640700142e07280c041205111860030002c0200440400410002000840da0204420304540600e8810600c600714620800e2600c20034200700c2c0c0c4507002030700c040b00b0700c9207201c9018100c030300c1014001e2017003001c154400d03201e0082e48180c1d40581c100300b404206174403101c500c0035070110300140b50203101c8405585880c0e00c03006c00e40752503102c5039651503002c101000080d01c19401040c800402810390345540d0b10702402e4440b40c98190300821210410310105203040186e006c05250800c85080740640b5900020708a0f04640b1900c03000407051480d80c3d0a802c3c0c00d20801280b0000c3c0520389141558036503900c406550180d0106c416441031303072458840c401042c03000070328041c0c0c00b01c030300607165142c84208030903941d20a900c03520036450880108452161601201d003026031281340d03140c40d03444ca00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633599487 1250 633598237 633598241
    0x2040b071b1a0309010b010206070215040809060a0e03010c05161704050d0b04110901210f0b0c0a030605030d08041412030a02122404111b1c0201020915030703 70
    0x98040300b040500d0301c00c2d0101c16650003014511452601e00200022805100120382d100c0003650070b1030158004c0700c4036110071829079080740e07841400746450620b0000102e000c0380081d4418074803040003620548280505240a026140070b49040b490310500303044280091048040c4640001000141e51004000400d011001994002e007401010340d80c200c0c110b4106000500012a4201c8000c210040c4209440c80d214031620305175400c4500d480628000d00d0ba0312058014a0750701510164008415080040c6000388054481c4aa000102e40c94154041c000780c15500d164101512a40004d40d007888225805010564004c0d00840224030120303045186034180a4070507514400020008104002107100742c0051001c40e501079121000b56586000c0031003030790703060040039041c5c021030000d042880ca480d80100b0f8100b10125086484c4c0900403154506c50015007410140c10b4102400300800101c1c9204010030b15901c1d80003d501e80040c040000300c1c259015000c50b900c0044c08004658078074466 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633600737 1250 633599487 633599489
    0x20105070f2c04060b071a041106090415090e070801021905090a12030201050601080f0f0a020a0201060f0806100b160f0c05040c0305010f1a0702100219060e060a02040b071b 76
    0xa841004000d07103654401000e54444281540c00c20781d0f41c810701f080f0740071011140b440745401c421031000003101403040109540c0504542c40d84243c80c4c0c0302c40c00c00f40c1c86644a400041c0310003d00000c4a2038100c1181d0b0404e100c2d9030044c14540d1045c020100e19201e01d000801140e0031518000d0303a0344809c0c01c00a0100070300c81c0c101403030000020208808141e0158405405241d00344ca034500f20f07543c0d01814160401c0f048800d40c150036a41c1d8081340c10050560054080d9411030300000c1103040e00c0710512801026240c0c003580745944901c080c441000541040c07c005041618040c0b841c05030400c540003008050a50000c24016480814006000c417500c07005014100c0100306000c2c0c3c1d000724000030003411081c041c5844100114100043d170004450300c01c1c80c41480305903214105040b0741c081011801c110134086040d800740e0f0104a10110a04090384d1420340325040008c0c003820141c80861404400401310030406104101c01d00020100006684007203502c40d80061100c443c90000600744d15039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633601987 1250 633600737 633600739
    0x120b0a110c0a080903060c0f071104180c030b060405090d0e0619120c08060109030212031224100c0b090f06070e09060d0206030414030408150403020105070f2c 70
    0xb82c0105000308242c6400601004000704d04a4503541c039051034003d0140f050a00c551b146003020403004001409000343c0a0158000070000140761400f03880c90000d038010000201c54110505038140204a088a44182c000700183d030200b1161900b00c00040e07554081c1e03811101072151035a01da41c640d64814044482544203404400d10f0001c058102828180403440f41d0f010b0907040c4a0700490452003003002510031113050b943c407040245160240401c4480a500c202d40758001000402e01c21505144510b000b03125100500403119014603000c60100451094140304201c00c1e407000b02c106070b126400c2c418007a007090440c01c0d180c8580110b907181803100502082035000350020460f80d1500002082c00382c08060700d5900180d500c030b10030801a4400c11034000d521050901c04200842c500f05055540c1c130307000c2000c9901c0d00e6154282d480c0b505040c2c100110010055404210030180e0a00405800480605140d095000c000c14094490707110100090205600d280c000640c071a900b00d810b0400ba00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633603237 1250 633601987 633601993
    0x204020a030515010c11150c1228021218031606030f050112080c030d0203010b0405101b1e0b0f0f090d050a03051902160606120b0a110c 60
    0x15040d00094054038084034848500b40e002401d0400075401142150507555205407000541c2c0802010402890b4112201009640c4180f091411341c0c0e03010403082c1c0d0140d05c0c58034002e80b0381212014501c4802030030702146454100390003402001036000102c40540302000c61010791212140503100c5642c000d2602c9403070f407610400d880325120014140140080d40c0d403959060002188014030710094400c2031003180001d02c500128440414040c8011309600c51401050b42d00c1d001d207214030f001c1039810a0b00554500107001408000d0703440c001d8031b0000d0b14101420621171290681950708403c4803414809445894804d00320048003085104031040603030320010003030f15402c100d44507100e4600101c0c3e503003407194070304004501400000107202242d40d4a5545407403030b02c202d5000490181c400580966202d000841c07a07120724880500290004080b640340c030050900090501c4d5080d121182d02424003401100fa4800110303034840c2e2400c0e4005003d501c080f0724a821210200854407542e0b1140366640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633604487 1250 633603237 633603247
    0x402070c0312020102040f0b2a1b04060608060f040f06090905210712030204090c0e012a021903050607020f010525030c1202042d050f1c020402 63
    0x824801614801c1c0c074041d41a05106a60403001070b402c03485140600744291418603400c0000f22804401401000941700805400100d4030800440300f2145680d01103651300a00002c2c80b040088081c49646000c0441c1c1c180102450003001802e501d0010f003000d030140c01e008032010300680312600040403ca03007444041040b903548446441c02000b1036041180c590042c102e040d00a03080301d000300241c003484505540d180894694034000180c0c06034103020b085c03680070301c40000d03003074428422107100f24826114111504840c034001040c08100c41d556107201010042d90825485100c840c0103a440d07030503541402c81c0295003002103003003d0300b0360000380184036107420401c940380d0205943d0003202c600d100920035070b00c071001c0094034442c180b2079040341c08043c80078140301c41c2d200740c00248410302542004403c800f80c010f4000d080c0e900a070410f00c8030383c040700c0d503184080249410306100c5001090440c0465401c200005207800d0811300c1051140319041022500031304041000110f15074010300440d80c5e5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633605737 1250 633604487 633604493
    0x1b031c08042109140405010e010e0a06080607050c1c050d0b04020708070c05090c09010212070f02030a0309060207080105090709050712050f010f0e0403020604032106030b0a1112040b040201030b040207 88
    0x528613030141004140780300340c160390281854065141a5000c2e0324006140e6802c2c441c08480c1070714020840c0d850b40d0740340d0300e0000341c14400f40103541c0a03110304d94507103036200800721a0030f01d00443d803502c2c4039031010140c420400701640481520b06640f10032401103100c2c01044c0018002c2d00807410041e1900500050f070404005030004201c0c1201d0003034961000c0c0e80c5e80d030010940c42d07000714035009015030007070603481d800d06c00c40d500106000b170b100303400034a0122030b0b5402103403525072942412000304140850500450741c04001c8007000f007200000a000d1450460340f05a16224180b05241007252600c010a5015000701000e10080031800010011440c001d2900d001c0c20030207105400c004581e103140030070b81c45000c0f03001620944d00740d0010800c5484659048454103012000000101ca02154824244ad5240a5100158003a142d04101418070b50001e0302111000354410030701075010880c001c541d1062511595105400410b2000c041d95280016405003d82440455020348009500ca0030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633606987 1250 633605737 633605747
    0x61207090614030d090e010303200109050a0c08010b06160602120901090c12021f0e100509190503061602010f090b040323160614091b031c080421 64
    0x1501d1040f022902e80205556040d81c02a1841c0145140501c0a00060000c00e02980180c400650140c0844410102e02182d0500310fa51006084615410001c500018070501400345000342c1304140003082030366014000030f240c9214084044400c08022503d500600a0543c1954030b100b55000800342c1c40d140c080f5005009200015040b58455946000410040429000038030455405442409070407410415043d402c8407641c0c944013007054064094000b45c03141c904460030030784142c80c1e00782c880c585201040142e20b0034444035404000092800c000230f59000a03402e03003015042100c80b5480340010000c0340940649800d80710242d05000055003040460185544141d009640d0403130182c500c0681ca822124a50082c1d01d2035042c148401c002e44e00c00b4030942c9910b54418840026400700e00c20b200000c039041102d54211a4004031580700410049481c4100181c50440180c891640000c440041820080103084100a41a0006030400000c1c8100c00e45401020084004090511500401f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633608237 1250 633606987 633607019
    0x20a03050d02210307030b0f03030d0914060c090d030e030d0c030f08010501140d06031b05090c120f130c03080310080a0209010b1612030615170612070906 68
    0x18803032528150340828645800380902c1d210890304074134580381c598046010f050385c1031806074030008800300729009607410070040040441c06100440e1984440c14800d808060310f9069201c1c0e031300003800704914010b15008990300c105041f80c85c61101c2c480c50504403045400e02d24400e40510034503014402c00d540001b001e0083d54441c1e07a800c03629001d81350b0119594402841206e000c82d95800d0061201c82c1001c000e410320140505002540320fa0b00e4862209919020440410303042e058402809a800e1200070740e41c0c400070483c8003500c0c0c800414180c4188020081c14039031600744c00b40104000764440014036a200c3d030442d5003c0c001c980c9a08141e40b01c0d86c82983d551020f030700c034580000b80f00c070004900001110740040103100103a02e4100401c909920000f224000789901d2503000300026200c941012181000340d03030000c2d5160414890b1039a0b49071000540040c02081050303000780d0500010300c0c661160060350089054071001e4000c41c40c02450350800e0b1140b40c1000307000b04c0c01344400d01d0415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633609487 1250 633608237 633608263
    0x50304031509141c030e190609020103060b120a1512050c03010b01090b030c0904060803180915060901140906120f130c12080f041805090303010f06030b0d020a0305 72
    0x8541c00628074195a50140c90340c29a10b020701c5400c1081081c0c5c0690300990074400100166405c8012850f6000d154a00c0c005044880550321030040055581c144101ca02901c0c500108903e060b0502041480d24480103203000c103465100d84160900c3c1d81030080c010028026003c0501541c00f203880c1c00390300c868210511501175031074a1030b1754100390312446c4509c0889942d480460301d5500e0700d1100100c42c0e4014403013503410030340f6550009801c00003000181541c0c0940140d80d10090046410400c074140060445d0001980185006c1c40302d50380e80302100e00c8400242011003014000d0029080240a640d80199020001040150b00d00748015182440ba00410f07a49040c6a0380e54040740100b40b091840c0038068001c40c00080c46484103000520180b50302401e041030130703c001c0001c3c0c215180e200b0f4005d1410b861548101500d000224000c15421480000c0a14119030400c1c0c08024180c5251056104042e2030360740b0121580c0b074490180e91310580203014443c50700c0c2c0b44c1c14166590384042c4541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633610737 1250 633609487 633609503
    0xb0c03090615130b0f0d0c15050307170601030603020a1214010c080105090c22050112090203030306010c030e03010903080402100203120402010807120e0c0a090209130207050304031509 81
    0x6400c150b4403025a04880c5008051a07002000007410f003000700400d4034000c3d006500c50134410000d50b200100e501029100d18004c02040d800c00510030780101c0740741c2c07054041c0310040c01480281a000815042c007040000c854002c0c40e030301d20300124080c001aa001039000f2001c0702020510307140401c492900580100103640400b0600c03d445822151854842d100040340c403030050209207000544203802c40107045000d03081003a180c0c1c4c5c01503115140030700c441030b002d0703070f08420031071943c211030030f42c140d100c0c1c0d52806c100c0c032111900440d44a11004100504010700500b920741014080c02c8032070110700c0050000c01c9900414980600b108a081e03406070b101d030803203100c8603135001c2c400400c03911a00b5607414208529125a80152150907002d4803400503c40000aa200c11503002e00c1100c030310700508001809242c003480c1c14001001c2d6190040d80300c807801001071400135100c41410040d030b040c0801c1c0050741c908441c28981d043d40200d410007440c0000032110781001c0c85c00c0381c2060f1032041c041c086d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633611987 1250 633610737 633610741
    0x318030303010515030405031209162c0714130918050d0302071a10051002010e070b0306040b1503010501140405091f0906030804030b090c0112020f070b0c030906 71
    0x20180d4034042441503551282d4113541080000400b5005960002d00c80c804490408400c143c10726210b0340b0455200700c040d03000d070300c1c00010b204000c03c1d078400808800001c4400c41400c040360519030303a042441807940754140808251010b100b181c080308580055211a6180d0032801c007030280c205c84601c0f0302e1050360304110803001e86144a901e86c2c5541c56200000781a07040d50184194040d4100443c02c1e40c2030b10304082e1181c1600c04120542d44100c248101d0600d101c0d04001c1007200501030403818100310fa16001c440303000b0050000c0e0130740c141d558001510780c0300d0340c6503400640980710301d08403d41c04c40d90f0044c141c024000800040e41c16a58240c841c2e400403400c101045a1500071440741c01c0e41707c1c01003004034292004504480e8040c4142e160f45100040c0c0340d004500540c1e013103a02c09c9035011000141042484040280d0581208004001c0e20001650000082011143d100240521070f4000703403081a10f8040d004942d0903c3d13001c101c1910a103007801102d00c40340c10480e440d000c0c034020400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633613237 1250 633611987 633611989
    0x212070821011512020f0c03070312020f12060a090e0d0206090a0f03050a0c021507051204270e101b231b0307060507021911010503090c040507020318 66
    0x290140c182c801010030100da00216003c100e8540302c003010fa40c0c041e00c0d404c103c840314203459440149100b11512000b980e41f002c0514000704114000303861146541c1c070501c0348030600008031701282c0240301003800d414060f032145000200d84180ca9842149910b02c0d051001d4038004000c0381140406010341c00b0340d646643d600b02061b44843d00c007540100784015264000300064082c0002e07041c11203552038466000302d500c1d0302051265008410b182d414102c0400c0000800104200c3c442e070788140e9500385800c09140040c002d88500ac00c05900d07411030760208480703072218001e6111240c0c0900749000c454461190180340300c01480c400c124240c0800c02c0131001c0d012180564801c2404480c102c00c0500d0002081c07555005540107214048082c216900542000b08400c01c013500301e2034002c40d40060342c0d09140002900c0c240c000100050461000c402440c0410015025401c01039405e00305141d603942d800d0203c40c280a6000300d07032984580750a09200685900001030700c15008601ca03004c0c0c07501c0c0408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633614487 1250 633613237 633613297
    0xc1203130b0106170a0f0e0d0203040819020307060507081c05160c11061303060504060c170f010e07050405030105090c01141804152601060e06030d03050702120708 72
    0x13418005124180000701d201c3d42c040794405100c44204c0b40c00042d005642c007008034107204e18501c180c40142e00c08074090048070014011503400c0148000c40802c241c2d0705601094580301d451007488103014020941c41c4c107020600044905600c0b068003c0401144500300e14001000255a650224900241700110041c00341e80e08801c0c0c0c80e0001540d030038041c120303400c100550f07010b031455004840d02407500100040440c041e850049110f2400425000c000c55401003498480f00403040b0340e10380440c1446581195001d02e90b0650388110041045039aa140081e512441964403498066191000304481c000c404900d280c040d2100360390b11218207014202ca04510701900b4045004401481d1519085181a50050100340041e000402c01c140d5202c0c11002c0980c42c0980c00903030b00d58440501d0610880c00c1c41008050a8804464044c40c10f0401c00300341e840b10304203000e400345559400801c48050003000300701d1003444070611071662140304d0300d082c11440d0440704035410a5030103000c2d000c402d03a080e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633615737 1250 633614487 633614507
    0xa050106150903060902061204152d0902030c040e0309040b010f0c0b0601170c030403080a051021050102221d010302090603100507030e0f0706020a0b10090603030c1b0612020c1203130b0106 83
    0xc0c1148125560510b110300340207004000cc1242c1c0340c410b04810f040d03540c4960150612405002001e50307182d909010604c400d071510002c0d0a410070060607040594980c2000d0003002c0b00d82c120228a22940d90700b40142e4007062040c50903280c081c40076040180e4003940800840c81180309075200b03804c5499840602040c0c3d00309030340150103100882c00500084516181102600d070364091401c0d90000c00d6100c1e103003240d010a1407041c2c1078000541e51078003410780c1610400101f60421041e401c00c24020400d00480c10f043c04000d10a41201011803e40d90b400c0140381d0803d030f0105410461400d04000c06001090301d03044c0d044650081402c01d424040c004103284049901c0c503006040c20b0700060352010000030000700b40c4221030840360340116584003d8803d00000d11304c2500d520380303240c555081078200d10b1a2800d070300016200c0c0000078041c0c0780e80480181454101c0640141e00ea0042c4030f08103050010760700428041d05400702c00c200c03a91202e541e188080314007407844019a40d0305c44200311950044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633616987 1250 633615737 633615791
    0xb040516031709030109211803032003070b07021e1501050d0807050a1109090f120a03110d2004081510080a050a05010615090306090206120415 63
    0x1c403000300c1c0704504800004102c543e80003800028440d42c02d03910022036103a16044490704451564101045603005000b43c2c10000606101d040581d01d1943c00030503105041c1d1a296465050089104460b8420401d03120416800300c1c0508042c608040000e658900c50783c7e104484100101034911031b84004134a00950f00d00f1030444000c241e003094188800d8203010030301201c0481c4200311002c0032810a00c403849145105403841540c414961081155454003d4000880b03a00720002c0200c803801c002036160900110381d52080e459221040060740103200340740320008801e20006030448031440c5588000040d174040c3c184a134220007035140102e580d020740d0250355a543c2c0011314a01c05141000390300e90f0300c00c1207001c0091072541c42d02d41c881c0c00c1c082402da049446511010004081000a005070006090030448042c00006c417110010031001c0c0310b200240c030056841036440159150350040302c0c0700700350b42d43c0180c0d01c40c01e092801243c51030f00c2290082e00d09250100e5078141d19201000c03d100c5141c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633618237 1250 633616987 633617003
    0x3021f14010b3105090630070807060206060414010b03070318020402040602030901080a050630060702030a031b0504050f2b0c0b07120f110a0b04051603 67
    0x800c1964030103540e4080300301c0d401c2c0c80070820032100000da1a10f0745007103000540d0702c80d0f0018502e0700052241003107004e01250702c28100210300781c088100707000049031102000c10401840303403c61003a02d800c004060700490001d016410001c200e40c5d4000449602402e41a10100b0400d040d14040840124082c011400858001c10104203840c0c402e800c41c0307600000703028001031040c0e91540040c04903441940045c01580010505088541e04034031801d41c0701074564000c3c08149042800a08041c1c1c00e20760709417030001002050b2080701900c10700320008428510481e4a2400d140c000a0741e42d40004002a00182c117081d0440c0024403410341d1035030200d19075102d190070141080200242200140310b000c4e08140d85958025607401480220341c0c03c2840a44a028810905e061668a280c0590061130300f50f602003010800045004406800c50602c500d0b041485100228045a2680a0030030703421151050554400900003d5018640518411000c5070b03810160310046c0d440241147c440500911 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633619487 1250 633618237 633618239
    0x3151c1a0912030717100e0a0b01021e010b1207050915031b0102030d0501030c080c180c0903070b19090905042001020c040509030403061103090a021e0d03021f1401 72
    0x94202c014580254107400e00e440365440d400c4071464034160454083c3e0000044042c03c2110a210080c3ca82c0c10100d0b109040c00312000140010b541ca821022029504003240f0f900c84034441d02c01e51100d083c4450003815509101c1d510f4504d20755070200c5000703070b600c44c090110202da8984c5a490054084c140003031b0181008001e540752141a400b101950300d81580020441c40500280a03c00c003070103180709030620250503040406007880c10200500032402200d10040c0c4100011941a807a58002c44075110f0554828406d0301080c100740c465448134954601c08a04032840e0105c1d00c800900e401d415603a403c4400366a19180301c1900e0003030364007a111601c5040644ea0802d449400040d04402c18011644000c01351000714044410484103024a034001080c00d204214480c06007003024680101501c0c1181071807405103403a01c0340e0090003880341e541d0a442e030f00003800c0c0c1d003510142c5840c020002e042400d210309020b510762604510042c0c0700c2c028131002003100d011078856030902005c00c0640340300c03603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633620737 1250 633619487 633619513
    0x601150f0309120f031803051e0c0a0b1e0c0d0c03021b010608010f0b01080a0c0905060705031305240c0a0203010c02030703090f0e0c03151c1a09 64
    0x42003416080c8030405031507900300004a10040b0b000c0603584840d07960440307060308107a0020115186002001071400c070411405002c43e9210055503020f032040c4001c9800029105102042c61098810100b01400340072424000d1020640c400e520945001c0300e400c5409154990404000c0303801c45200390300030004e005001c0741d01c40603401850021035506005280003601100100b82c40c40d41d0040d030410341e4542c5014000c40d1801c7c0901603048031501c80902001420000180c01b04100402500c0c03007580e100c161595280c07140150790020301d0041c100e03e5982210381811030b01e0b6405202c6240c07040e04590b00c0007a040c24500c00c4100c1440c44032441042481a40078003500590050a042400384034914507080965000c0c840c049200185030000d60323541d0a20b14014001440c10743c8500030920f0701b0142000b007001c2601c00594045000700c040c941c1c80e038840c04000d001c150a507502541114440125030442d40c982519410f4142c02110040b088800c0d00840e920200c0b811104e461380c58110840c01c4c3c40c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633621987 1250 633620737 633620747
    0xc0909010e09010f18021306050a060f051204080301080f0c06090d050703080a03021e0a020709050a0f0e070512120403140a20010e063f090c01030e060115 68
    0x1081002e400032520700c000f00100810741c2c4028201c06200508542403200318a481e86500e9903070310340e108040c000ca078a403c3c00903541c03240c1d900c40c0300188400340400038150362007941103a203901403541c00c20344a41028102841250800d0290b5803940c45040e03103682840070b000800e6528418010710003482d200170303c014000504c052840440b914425058044005805c0201400c4040074541d00180ca078440301d2000d24518490b000b00c441d18000401c1a69100c5d0703030101c0c4003026908210383c0030030242c60381c03a0440000e240d1640003903105071901003107176091400800c0e0403080b030f10200c1d21886c241c50740f290780c0303605c948400034080d2502504110403c000b4071400c00e1043c0c002d080038181c40e480b130b5082c0c44460029507881c2c26690f4840c5112504072980d03800c650798410800040e01c4850510400000b401b130002c440c0c030440941105881c86c41014641100410100d414000e484000c0a0414a890603940c0c01003924450101c0d040844030b900101000484904840e031404840e041004441c40a4030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633623237 1250 633621987 633621991
    0x503030c060114041e05070e090f01031b080a0c140f01050d0504080c10230108100f0f0f060810020306091302270403090602031305010305092806050c0909010e 70
    0x140090f114084e81d10500041010517601d02504100810750f89048503006200e40c0c072080d44280300c0c00c0c101c8144038660603045851415681c1c0480030071440c0032001040756000089511400052003280c4804041080740c0060070120303840201550500407502d410008405c0e00e02403401e0020b44148110030803840076400c07454005004a00044c030b0a411206141d042039403c009451a0341c0d00c8050380301d10245000340c441120410b002601c1c1182d41004841a11180e107c0c3c0421800d580b13401100002509a5100300154000141c0030001d101200a84002600701c5204030b0b40d030740c0140c40c107038804500319000700d034400c0c20018407145565075102da940c409403038050801e80c1c00814031000c1c4441c520001059a10108149640005134505858020301c3d4504540000045400c14010012840641b0f078111042e180309080c00300b5199120346840b46004201c0c001c4201600c11050750039801c0380b0f0300721381003030140c0184028051956200c0314a01e152280070ba80d5900030b50b44a00411055960180707041d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633624487 1250 633623237 633623239
    0xb0f0c0702060d090614040516031505150a120605160f140403080d02040e180c15070209010b0406090b18041a04050903040503011505090f04020d12050a090503030c060114 75
    0x9040d0003036252882290901420310349081040b03002d01023402002c1044e2080103441c0310303650b0f03900d5003140c1da5104200405100840c49a481e4804503c00c80d4107070303c04421540015104018250765400030101d1054405800e503441031900002c2400d9007240808644008116110014162402d10b022a900081c80b02168000c08040c0030120005400400626084000c11405030316503042501001c52100060f003405001c200b8290300d11083d80021926827203c00080301c40389809481004949024030454100a50002600c400415500e01500c0030f0800c2c0d558a560b1040300d41c1d10341c118003100d4801c1561004c0c10500c0001200d40c6480d00d03800c030010b04048140680c44841c03240340441c00351042910080c480750000b04080c001da003001d00c10389030600300060120944602e0440400d22000018082000194240700041c0654440c00072089120fa405104a02162249280244103410205848000981800c0000b8040c03800100f501c0305106500b0241c00982d00e412106c000d0701024103007807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633625737 1250 633624487 633624491
    0x12050d0f05220309080d0903030806101715060f071101050f121801020c011a04150e072c101d040504020102070b0c011512031b050c0d050a0b0f0c0702060d 68
    0x1017000242800104003000960303d4040100f429843c02800d060002415980201e0540100780c02560740071003d502402454078110206480b485241034000c5901c200311600504002007070402c2c01c040794002c10b103190103104001c0742c04044400441d018401d020030000000d0041c41502d08001c102c40c04242c025403a6140318644000c507203c89400da81010983d810143d5440b44081b03a450020518910241d000300e6041081c142c0e80b03100e022201480d801070103019070602c000100d0300c902a12070315001200b40c0307480303001c41c40140c1240000301c40942c030f115001c5d4034018080c0c24000d009001400300a030184a5450f00d81c0f55000c280b100400e8018016411442907010004812900000806025120000114805a92107c0044a40308560090b55210480c420b14008641c2c00303051a855900c0000d600703d103404d110b00b0000c4c6040e0442d40350540c0040c50f0034813401005400282c02042c3c0c0e1140b0350a04066851462100f201c51046a00854144041155000500d07000004100003601e500300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633626987 1250 633625737 633625739
    0x3130615030c1e0f18020f040509190f05070f0315050a060e0f0303090f130213090c0201050f060f011b0b0a020307020f0106051305060d12050d0f05220309 68
    0x380c00d030709403641e8803924209901102412500142c072040c100540750303503103007001e4071884e045c114280010300e05074684040b07601240307284445070850100e0303006100013003410050b410a840e49400d88016807919009180c034040d5962844025401078070302c100229142c4113082c0d0a0103000340c0103840114004c52100c20f80709400314140c0e48024404000c1c4c40103969161002c00701d8018005c401402c007410b50f1199206012840d0565101550005854026038a06100d800010030f084061700402449403030468810201140d50101580115158000c5900038003046c1c0300e041141e401d11a050300d82035048502e00c40c0301750382035008444000c0d682c0125a10b1a24102d00c6c0d03183e0300401d8509480c001203060b000414007500303030f50400a2205c10503508000f0080032346840001034020001d407251310b80d625181c60004101d95a20400e1640c801c0d003140a0745a46060f0341e000a14036400901d8070703003c1614142c00c591003429039101e2140b046600320814450740055882895010b1240740048082010000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633628237 1250 633626987 633626993
    0x1b120421060504140d0e0a15050706020a080403030b060c06160225081509100b0d06020d1e18421109010503130606080307030809060901020313061503 66
    0x4070740c80c032841c0500404a0548408044c1c281000880c03240032080140c41c2c00b2225450380d03003650960480d2a0a049404c00f04580031080c1c0311801b40c0f56010300010300c0400c0500310b0310340009121b0310440c46540c0c100714101000e020040103000d03244001e0b82079030103d0300080728000e41003000410308030240126850342100d50f5981e5000004a44110341a00a0740000c001d01e603010020314006812855000d009803a060300d407513613a0900d00c80c111221588a54018000e85c031962406003c0c1a0854002d40d030b01c010380800d90b400307801c4114810747d6842482c10b01d401162010b200314140d94046001c3c1c1492214a80c95807520684252030810217007590f0088003203180600c9204000920400207104480d200f00394040044a502c424040450f0100304001000d0f60703805003c41781d00c4000d01c81e040d856001d030ba051a000511464002032610f01c40010a081410b401244240c40f9074401003c940003903881d0995582070340425210b000354004130307000d400c001403402e03007013010b9a42c0c0d00d0f451610f040c1da60f42c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633629487 1250 633628237 633628241
    0xc021516050109051203160305070c020406060f11030405030a380f0c09360a060302030f0706020c0603130c0306090b0601030606020d050703030b0a08031b12042106 72
    0x1801100d86030340d80c2200d2004c0100a2003690303030901c022581d041c218a40001d00e10260842c042019040650300c9001982d001d00888102100715000740c000c00c0440d450f41e101510740e40d54029481d0129010700c4441070300d40380c000215026a1000b0f0003521101910395a0301c4c01e01c0d044d4541045010702b465140a01c03102d2002d0813071441e402c090039220b81c0b909200d0156505190050501c500c120801c020081042c0c8890f000b011700640030780d00c0d840d2030030a2824105264215903400f40d00b16902001480504074182d00300e102a40d0084040d41d600244104d0703180d507030381690702c030360009070704401910041c61800d030001e180d01c003880c00400c0111605545d10f0804803091134004582290740c1e01003030028488100c1003a64801e100307003010410705041c840042c0d600c05480c0b020408000000400302c041521942255030700c040e001e00780e10342a540790a4400c0d240e4015800858040e00b0b21051584141c100003071a8000f038039808210703403030107080181c0e02261a418000d20354042c810030380c611000451074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633630737 1250 633629487 633629527
    0x110d0e03030105010912020604050d02060d06030606060908010519050615030a06170a020d060203070201060911040302100504060e0607020109050310050417040e0a020c0a14070e06060301060c0215 86
    0x110003640e540c0d81020000740c032000702ca411002c0449415041c040c01a201c00701250207035071080b07500c48818a11480001e4440c415043d1400202e03052034000070400081da0000d105440007511101d03c11b07911040d00c10700300c4808540c05030101e0301d900d80d030003031007022684a540c01660140100750107a03080740100303d0b80e6005581410385242d5682d010010803850708407204102101001a2140404540004421994103400039001590005c0441d0b4031a0017540000c00400e2045010b004030741e1040b0b0b40703042c5a006840300341e0140fa0b8640030035442612500464068500c99214801154440424403109400c0703c6802c0b810300812610101d070b5950100104030040034108408a140d2130545005000c0c49450f0228807d010400d0006106807240c00701c1055002d81107500c0141c541c0016400a03243c41a0341d000504003040f48510b2165800003c6505001e4640713010940c0750070344400c42801580d21003403140f040001c6624001d00c0061800c61000811036040e26240c90805a40700030000402002c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633631987 1250 633630737 633630761
    0x1d072606010e010e07052b0e010e031e04271d0105090d0305010510080a020403080304120905011d0415050a1e050a030c1206110d02030f1602070603110d 67
    0x142e40c0c010401100d000b9001540000149040c40c1010907980da02c1113400d100b04c0348040d003c03904003d000100f11140e84021061b102d804001d100b02c1080c41120f0740c0ba9844081c0c41010401514080400e01c0d40382c204480444107030300905002c200c45070408083d940c3c502003030f0041640d01d940d48021201500d1410031000c04601340009201c2c203080300304628101c0000b14807810305d07050000400644d0b8444400a41c01000303420842c01655074000b804000f031043c3d8000400800010082c042801100c500c0040440080c3e11174203c2c0315281c80065600d00e0064000c6010211380b140103000701c0c1069005005d480034441d0010300b842c1e8803000041d0f10304400fa007044103a103c029000b0351203000446015801040182c882504150543c3c407014000d0741240140a0354941080c0858200000d59110824204d01c1000c4142c40341031a10483c0c010b544165404114a030004000c1000e00e80e004070001e09401e26a00140602c038a0035070b007503000d03141072003242c2007010050000c58008109805a01c5e02000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633633093 1106 633631987 633632009
    0x111003110403050c13110301062007082a03061b07060212040209010b190e0d0b010e1e0907050f0a0918061d07260601 52
    0x2958150225a000c0004000040c008003040040740d4080456000201e40000300200f820380f42c0503800300302c2e020001c00042000600401500007604001190030038031002d40460139045c038001c2e41c043c0741c00390003070740a086411072108124042c070460704000e08200030080700480d0f0741e404010000b174400d04107030101c1405c82103440300b564242684201e09565075541001c04111951003510102e028840c0000041685000c41060350144800c0903111030746c0071240c0b030381203607403040394040310340c101c0402c80045002c2138070503911901070300d4445403111003810600811210b500441981000c00d41c00441801400e801c0031500b10110b450454040100c4a40c2c41d0002e000040c0d00c0c1d0080048a1038045200100c82003244003148403406240104080d12640450820040c0804401c00081d080100c062111000a00d0320b00e260031219905201180c260320045854660281c204560400d = true := by decide +kernel

theorem cover : BRFrame.Cov 633453237 633633093 := by
  have h0 := BRFrame.cov_init 633453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633453237 ≤ n) (h2 : n < 633633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
