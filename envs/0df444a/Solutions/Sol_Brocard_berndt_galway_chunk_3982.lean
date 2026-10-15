-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3982
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:28.765378+00:00
-- url     : https://prove2.me/submissions/f94272a7-4d90-4288-a5d4-db30ad97daad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716007194 ≤ n < 716187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716008444 1250 716007194 716007199
    0x1140a1a090306010b03010503100b120f0703140d080a0f11031501080109090302030403030819060303050703032a0f02010e01020304080301030b01060c15020315090c18150d0203040c0b0c0c 83
    0x3c4a0381c0b9205a20340078042070203100d81562011661060001304c03640310328203140c4001c01601c5e40400100e8082c0c9801c58000c0c8003821078004020400402024900701d2184860340c1d03001e440541c20060004104140c001d204c81c00c05078a8914565582e000c40d8000c464890300b90403119aa86064903010144142c603207595070004080d10300014480441e442842c0d500759150303010f1444c00d4619142121385030005409950030501c960355075000c1d40820301c2132100441c0b081c0c50310764680c4020b0402500b1282049034555510050f000e0b107141401000c00084011001070a04120000000c50b040f0f004120f00001015070b1361001090006101035000a981207030310542c0c015421740e803504401c54241c101418000c0860302290881d04150300c0c04e8010f5130b80100440301c5002c144400000140011400b900c42c150a504008ad80f140100d0710410400d5443e2400c0d1244680390340741c42001001361140089010740540d000c40450100007803c19010000c005600000c0d45410309142d085440d11140800c662 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716009694 1250 716008444 716008453
    0x14060610020304050f0d0311030301180b030303090a02090a1508030d06050604142103032412030f131e0e0105010c02010519030618050a05100e01140a1a0903 69
    0xa1018400802c0354151134000c3e2050584441c003000340418001201d608500340192610000da1721034080010b54001c221110155520151302c0886c18101c1d200c0f6088103020b500700300704102a122000a50081003541070760041e500d542d03508440d000401d100031f80004005440d94000690300b40001c007a0103451342ca46020003400d82c5c0d9104210503840f9502c0794101d00c0c9400700003108145850040448108401c28507503c00403d80d991203410765004079800000189140c401845081174001403440c582029607506800c15207050500e55030340509150750282000c0041c1200065108080380c5000b402c80900304a0b0440c0d40203e80c3d0b002d400f45000d1a01903035104400010258403c81303120303502d00d030180c403020703c1d01d00c5d08407500b003008100060f00c8041c580c55050005071f848014a002032225480e0070001200c1c101010b00c00705030340d0040d01254804076200f04c04d00481401100660441d0306120107003c40030f48102c04100015101d600c4030000074452044526a800e40700c0003003034500422425503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716010944 1250 716009694 716009719
    0x3030d09110409200409120507030e040c02030909040c0f080a052803110a08030c0d0513030206181c0f0f020706050906070c0f03050304030c0608060d020f0d140606 72
    0x803c940a07254080e081005004400d04808034101c2a04019080600081507140850b00c41c0b44802590400240002e83e00203504802e040e400b590141e0040e001b01d0f428000e002e040d03407000f0340c0d070f014004806108100302004681085003208081e40200340f5040344110b81540d034150151582003860068459008410090380044071310f9051803c90705211140764004043da8404841441007003486842c40e10a0030090004200c422000e0340c4a070940b001c403031351b894029603404401d030790014008220308000e80381e0140002c2d40102c0e500c0d901103410171180500d0b26031f01217603a1070000908804800c00816903040c010080c0d10002c9024002015280c2801e015140380d0704070f81c2c90a4620940c400070f0014010361886103071400050800d14011120410550b84852822641c0c1c4208d51088640b5400020200108654452090004c0449060601403442c0003004200750300e0b10524005d2080d80160302903001d07556802d03000e040060b0441c1c00c0d041010180240c0c0d5544e8403094521038410314811560 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716012194 1250 716010944 716010949
    0x1021c060503061503031e03010f0e0610030b0a030605090c040515010903060e0102120a090c080a0c05040504030306081509011505012001020c100501030b010f03020f0f030c03030d0911 81
    0x10141100d201800a001503540c02d5135500707a1042c0b000d0240e605000801668004120101c00c1c11256041e80a045540e54505400420700b0706940c2d000c049010103420810020341d4520740f184d075044086003408034214003a200010319481d81500001c02452411b4141302100714000b54802064001351010030280d1100705014a40d00780c801c0c00c5500040300c0340b4042c00040e0391500300e505060454030016007002d2201804000d0488119071060080ba51041480c2c240003120004600500031a006444a03443d1a1990340c1c510300b81e400382ca07001e035495001182c1054480c0e84690300402c01901501c401c0044c2d00a0703084418001e45004401d0340c00c14070401000d41d00004800c0440d10141c54040c0000d1241d40c81d00c2c030100001e084200c507554288124501c0b500284445860100003420000d090741c1903261020800a060b0409070841745203c0041c40140c0345c58215101c00344041707a160403402010f000081c9040401892135415010100b10f070300010503250000e402c00f921518207030a104004100307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716013444 1250 716012194 716012201
    0x60b030f0601022e0b0d0b040204090201090f0314010609050702250306090b090114060105092b030504150305011802131a0901021911090c1e04090c0221090a030b070201021c 76
    0x100a81f0a12a01c8040380044c9806d9010118052060428801c6260340e1100b00c03444103007507401541c0301c445a402e01e030041c1c0d000b803180501400346403400f0041403e0851000395030f00d048258400f00d41c1809145050b5003101e8154410085034484000c2c04928070038900980084800d503030f160415804d025682d00d0300b0400b100340b240b1913072040c1d66103803c0c03144060030820960300f00c0c181600310100548800181d1000c0c2c500c19500c1e00c0c0030b40c903a01e0782d0b985021503031607907900742507918000c16190600512565101c94841402d01040300c1c1e02503125803040080d04c442c0d01d940e5101e400f502041080591134460107070301800300000c098080c3c400c01c4408101e040c02d80d9201503c014000001c0d04240e041c14544649100e41000c2426540c0b800c0200440b2581e5051764800414006c00401160800c08074086014014100011b0701c06007050103448070960222620031b03101a803002c400801c1044560303c0703644080307005503001554004c2170b0408182c081d0007584420306040b421030701e4428000075070060b0700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716014694 1250 716013444 716013469
    0x40303030e060f0a090f020a09021215131d011e060e010b032809110909030a0215060607020604030b01050906060c0d0f050706020d0509060604060b030f0601022e0b 72
    0xd00f0702e54143d44024035180182418481260b04507038101042d00540c4070485508003031700b00b41100503600c40002980642410006000fa15048034508203e5010307180c88114040380c2c5005000454000c03031480c1d552080d1648000c404000d5840c1c0031100421092029040e02e4000e1090003c000e81c60311001000c0108100f40500d182558041010a41e1014010320b070303000019480e01d045070320303a401441840684071a09026200c41c84641c0c41006107182400c01306d03030010380e030100451402201c000003a4940701295a580b050351215000580f0a4a426040b10407440c0d0080c031180d621603c0340ba0000c0000001c1c0209030164481ca40043c0d55030402030115040c0d40c41d07140060a001842102c100c55803440800a0010030100303000c030000080f42c9001a000c0b00c503601c072001c241458105c800c0380c82c1801c01408984240d040480c100b003030f007002c0403c41360400c20342c00300b04425544000060b454200c2e608241862542c10044945844010640501003411018002c1c05481c00802c1040092142003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716015944 1250 716014694 716014711
    0x2150a020601180e0d030e1225050f0a0f05060a021e0706021e070506061c110d020303030108070e06030313060804060608100617010203041e0312060b040303030e06 72
    0x1c014407003522074404265042039001004550700b110700400300c1c24280d50840702000f0903224081f000c620001480700148500002000900307141050b080e1026500700386203504043d0800c0030100d41440800e2011400c5030221800311071454429141c003058240107071806445070700920b000b189843d60039000301c4060003001a404010f020311110548656481044200d520075800c1001d851040350891201101c600c017090319584030000340c2016400c00400504141c4176103a0040b0f10080c05222005001c8030503000100c0c1c460048040c80420003056030048040c0d85880084000280c2072000a0340f54151901c03140184803039115038091542e207015442c4503002c0d98510900504c580d030312034000d103039100340a048042016030342d5602c00744c107007003c07007207504615521441c0034400a10b202d1011103c0100b0351008600d10f00e0300fa180d030301c031340328010861600c4011410003110074548590300c0069101250801081841e03134650090600c0e40c000d10003200400c1c200561503500c0786001c2501486020750 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716017194 1250 716015944 716015953
    0xc040b091f0e0406020d051b030a232a0a201c0201020c0c0108010518040f0515010302011101050907060f050d020c0705010801050d05120a0e190302150a02 68
    0x1071229990580c40c20800c0855410355030400011140581422640207901880300160340ba00e80ca50003009541d00100113070004050301110b07074050b4800204481c0d026201900015803600285014071385681150710302141950000b0602c60b00e0301244501d400d2245505ca00c040c3c0c0c00300a1000544240501384004011800b41030f440c030001c0d5130b1010018800c8165000303440b0490422018606c00051031404000182c0d80854111001d4008016a00c1030b54001d090030005989030038001590711802001c1c0c50086903c43c0045810892154075404120b60b00605840d101c03240039040203080e0000f480242e00160801e0720121a0742018030642d40107204080190072540d0070490291412141c800385207040180030015511408072601c05417410903206030240003254540741c0010006081038100354424000002c924001074800540c100e01240f00298080e2504c400f80c1050783d010300317070800442c1c0082c2c0510000803034484078804e44090724800c0f100c900c010115000f850300680181c071908000350f0300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716018444 1250 716017194 716017201
    0xd0b120a02010305040309150210060609030f02040e01021b010911090411100908030a020102030108010b0102030a09140a09050405060708090304060903080f04150c050705010c0210180f06110c040b09 87
    0x1107034006903405030180c18407a2100d81c2d501848230303d0100405004005070071404035200c081c0b58502580b0001e00552510b03400043c19500c03a03030452440711030003d1085640307a001d00722903c1c0a4040e2036003500002c0d002080c455021400e680030700303000a01103620007400c1d0360026651500e004524055500144101c480e04180030a202e4000c900640840c24800101c00c001201c00b020401481d000d1050b42c00961070307501d0410600e003900d01000c0108d065402c14440308a1080d0702c0b000e002d085500e1103c6c2e403802810300320003080501030a40c11084005d0f0803c010001400f40001d6440d01615a591392172205903a0703aa008c6407a40954058100000c02651080001c01c0e40d14001e000715154043c45245015a980f04000d03940345524150408143c1e501800400d0000900401c4020300c42801c00c028199001d50000c3d403915a0500c940040c40028403403100d051052a032400054251702d0b514503642c030388032070000d000e03444c404843c14114440c0c0c50003000701e404c00e4058001c1d00500504540318a45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716019694 1250 716018444 716018447
    0x30804020405090708060c09011e1e0e031c08060d020a120503121312091d1905040602040f09060b04090c0c12170c03060a0302060a1b080d0b120a0201 66
    0x74002e4611400f51141364400b04051400344a22401000b2010400e80c3d98441d810015000b074030065003821a07003031030542011850390403054410b01c29450b180712084400501d401640d110030030701c0c40550140324501074480366140200d8040030240c1651103880d4250b407040100314110390403900c000d4001da9401c00c10041c0c41201051581082c0c407e0003601d042101c44020125034001c1219036856a035203002420b810b00002044081c410700d6649041c0949a040280b00c4401079069000070032810079000001e400c4c2e0303074664070071040d02103080760a01c002e08042c20400041d401c503016507640e0303800d07800300041d43c00018401d10040300d1410b003043d800d25241c101000018107140400c0700611414003081b02c0001d150009034802c0a49585030000120700c0c2c2c05004050305030092101d0606002082809001d03640c0440c3c0a045070760465a056403414031a504540080701003405180b214203075102c4508200180000c0c240c1c4a41c3d01508000e000c40510402210011a144128a94014540450165 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716020944 1250 716019694 716019701
    0xe0a060f050f15161a060f030f0304030b191e05130b0a020a170a02032203170403090b0c1e010204030215090a0b0406081501021f0518060c0d0501080304030308040204 73
    0x81e620380e00307840880c1135030382c6844c0301c0350032944240803001e4855410403c040c50951260310b80c2c0380055001b44036150302d1113811a520b00c61804043c00380b20300c4100207545000141209181c038805a442070100a40e1526190001d104111586005c1410800020f08050f40c88540001054000343d0301c0d2401e4440c40b2400f8000d510080d00b080410180070980340828140030400784c0102d5002c1001030380e034503000180d0004614212555852000907408001c00f10398842032022820b40b481c216844141c94501d4295801d507007540c0102c0040001180c0428070510100c2d203940b16050488500820f131269a424500301d2096000080d8445503c80c0803c440d4410b000181003d50000303020310a880b80c40300030645164015a003c440040c0001003005800c0c440c0809080c660031081c0005d041210807034050018200030900b440100c9941c580c0055610300e1024a138019290113101900e0403800e000080d2891540494540000e003030a100c00007411200000c100c03002c0341d805550303110050b1216802c01010707 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716022194 1250 716020944 716020957
    0x30f03090109022205010501030203010f14012a0228150c081602120109030f030c03200304050708120d240f05040c030e0c010c05070e0a060f050f15 65
    0x35668078080c0a0040e203c5002c42c0204100e1a20013041050b0310400305019100141c21080c1018018001081021102442d09041d250452001540450345000486041a64445068800d00c030400c009004030180780034041020b000355000c840d02c6c040034100da44800c6810240d25141c0d00000401c1206450f000c03500310b680ca0083c64410210080d031349481c034164001c5601c0040115850341414210300c2e181c0504040c1c45c40e401c0c000c0c024060f40ea1005421909102c2c002c000740b60b10b488c111b64001e44607611850065004590420541000701c180800a8100b01e8085410f482501c0012465400c006102d124501564040900d03041d03a159040c0042c0449a8070306041030103100c0038581001075601e09030b02030322080c2c1442e0f000c036107003404010596052008640034141f400800040c0300102141610342da2a082c01d00001010143c640075103000100d40c06044448080b03004e00c0181d9840340c21103002c170391904420301c44280d00c1d001003041c050f81004100380d000200713550b800d80e84180300703003e845c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716023444 1250 716022194 716022211
    0x60b120117030d05010608070e0f0f040b010e0d080405010806030a050604020d020a0305061f150518180f0708010f12020d0c0506131d0c07080c1c11010c0809030f03 72
    0x5102800c0c5190084da0030a0700118040340407003040099550b44001d9010400100301c0c1e06548212004010400003410710300907a000c0c584514141c03100364002ca10544144e2006407050503200501e003460f483e5900f01c0d01a46001034104d1002c5065843c0004254040d1900304018012588503030b0b08200d4181c583c10b0302280c003c42c02100000c0824414802c461060151004c40442d0401c3c802104048210f50380004000186401c00c1d260300b140d00400392520392000c40f030402184820500003800803180b5030018022441094208030341d29522221850090495417140ca500d6621070301800031000b0580103000380301903284035a0303025142c10308114030481d02562b09212016204c10100303581c3d0340244038114030950880300400810b801c1401da0007042209003060f2040d410143c0780315005108121002d03110030408603102c1c007a9001480160100035180c070002111080c501c20240501004000403030b02946030801012002c1d00650403e8860403078000078514080784012420080e80000c0c20510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716024694 1250 716023444 716023447
    0x70c180902040c031a030d1d03010e030406180e160c02180c0702030601090b0a12050f01090c0e1501020303060112150915080706020a0b06240a03060b12011703 70
    0x40250b10780703110b50105541c0d2554003040843c0c1d801480f00c8040d9030100c80300d00179032058400c0842903600002c001c104495154003000c0c2440c20100190241000071080c0704980270006000684680020b001c0c2800112000343d1038889965051540422808440802014040302c00700166544202c80c1c19840920040004002c000000c0c2011861042101c128072106d41c0058014190310f420414140103103000c101c24000001510302150302a829840340d094013901c3c26411038104001480b200e0703500b29008000b0801440181030001182d0b015109031500c0e4032059002c1044882501641c404020060300103610b5900d42200450710407090806031809140d4620000548220081d00c40300240440c10707000c0b941d0b1802e25980401c403921a80030640d19030050a08100070f036008164002e015412a514161681e1280c02003a83e00049038500385840312415580085014200042c1000341140d0f0b0307007042074586810b54080a4483e0056409400c10148010070080701c070b0540314291915082e0989 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716025944 1250 716024694 716024711
    0x40f060521100515070f030806011103180f04092f030f0307031704030f080c09090a0914070b0702040902030f03070807020328060b0102032b11070c18 66
    0x481074076070162441c10068110721010426843e000d007150840e42c0d078440c0303620325181007651400000b5400c5040201404401c100041d16030b07000c0c03000303001c111140b102900e07900c01c901c03006489210f0070000098419008103d04184504143c0b1804603420703840308010a680101d03503145442400300404000852000040764002901c1c103100503000c003040d807401552140350740c1c0f601800180115407445445034440c001c101c0440d40c0400107005480d00f42c2820382c21134a590360550307400d22680c0c07600c5400181100038083c08407000c0d80207002d000e004a0042d0004980c00c01c0450301c0b0b00f00d030720400b40ea04d9024082c030340140c98241d000b2944640b0080072a010179204855903400e581100100baa98500085005415800c090007184a00c284445480c00f0725450407201c0c02801035003000140c80c20740d9481d240160b60340204226100c0750030900c5012820401d4003c282d80f4034460b207050810090600a611940c42c08400503580c2c4254400c0701400300d2820108810409100481d080c885183c0b1070785003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716027194 1250 716025944 716025997
    0x809150c07091508030c150a090605090307020901090b06180d0f0c0e060105041203030903090b0d0903030e07051f0905090f07020607020606031903050708040b09011103040f0605 78
    0x80001c041c01e86000c2403140b125030f08000e1070340381c5600101082e042000708610a5001144001c595818003d881c015501c41c2030000c1e0007001e1000000300040d24243c1400a003d00004c00b80c003400d407088079002d0f203e0303032aa400e40b01551118801c05400c07038414421a2031001c8207910840f10b401015080c0320100e00d280c2c8074000700801d1407005a400d000c0c1c2410070f01c40020103c404aa1042c020b0030428905440e040d40154501c24140001d4100741e07840e5601000c05110304107450007490101441911340103540c80708802843c07203a1701200031a00d001440e2843c440041400c800700c1e14000c10700c4d08a80c000105c078100d903410004d445030030000807060108180e0748880e00f16004800f40710514106160441c00a80b40c050050969020b540c0b0000820100b950005076048028030040e03100030700d040d41480c0903100d5000c3c42e040240001d001280100300c100420002c0c0420502c240e0b00c034405800c0c031980e596280d104030b0041e1b900c001c47c001c005010043c0200020407035001603803410f140c4214602134 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716028444 1250 716027194 716027203
    0x4080f0109030f500304020123160b06040f060503060105060a1101020a032313060b0a051e03210d3c0c1404210506091c0503040809150c 60
    0x4d800c201000d5070f5071010190708890300e0005a00f0742030203810b4074604098001804100d03140500c0d10840c0005802290844801070130343e2444007001542904141e56460b08484d40b400840d091800b0307601c0e044120408190902442c0112034000d4050700c1130740d080405108640d8007801c020310600c50f081e51800d440d004242f000b0b120284d17460750005981402c00c24041c082504590500e400c0365030144c140035070b100c030444080d200540e2105c000680200d80201042250380316920065008980c031000c1541c80382d566008003540304048061351600103030f500d01112501c620400d803001c04541805600c203001159813016541d074074050052281040e0480e01540d13400540d07000b01104100500e25000075240600800f000012a41440b2201c01c0c2000540143c074000c5100d6019440300601212043c2903c00d02c11074501c035040702c02c0e6074407407424420440d81c0d0341310743c0040030611401003040010340d40300d001520b02441d8040800d41ca003840c031108129942a0210542100490030081c003503207a9020003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716029694 1250 716028444 716028527
    0x307092d15020a120c03570b0f07020607050d020d060302100c0606081b01080a0f020c070e01050607030912150c02150c0a05070b0403050d06090204080f0109030f 71
    0x60310340700310554514000b064040b001400d01c00704249115a415506482841504c98a4004103c41242032160400c82103265a1107801894802410440c07c00c0c020403802d614402c0788088140101522803c00490f6501c80481c1c0c00e02c0024400d10509600658a07001400d00c4001a040490380c95101d40002d403401c0c8451000c03202082c403d040070420031180f400b44070010705100c4082c20310089589d18180500134070041c0f10b41004004800600c5076040b6620444590049010441d210389060030001d9840485001e810f143c040030f54000100352400000721180170364595148180e1078902100d050708400248002c46590307802010302041c0a0785807040c203901c0009540100001d0184010102030741c6009800848451020003944410a40220844120742e034414007100c03ca5995050440d80350042081e051241400c00d080003807180c2454020744190741103101504c40c00b580e01c0c1900c50807502d00d900f004021803140d1042850040c011400c91a4407642c04420903054180d80c00d88403250700201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716030944 1250 716029694 716029697
    0x30d0c240903030e010b030304091d030a05071a040c090504030203070b07020d0e120a032304090506040605010e0907030e0111040807082a19030204020307092d15020a12 74
    0x1c215000c24180e16001d9083c01100000c001c005040d29000465181e00c5a070040e0b042c02c2d502c1c2c0198903941c048020000b00300c00100010b8940320008848000d005a11503801911501c10500e00100e2018514981c5409282d0205080b164140360400b4035026000003003083d015070005002810101d00d5003100700d0310480702607003d0102d0f40a0800080d00c1d842005000d54015111450111041c100008031819041e0b014185120054880c00029181d12640c400545110801040010310048560083c4d40110000c440c2408207684807001129010801c3d840ca41d400390703002002c2075030076000350f00c80d00ca410740389400415040c2c01c80c2c01244841c0c0c0140c0c0250101e501030181000041c2050103091623a0544000300300c03007400c03004810410450404180da119000c031400c0101d50403d0b100c00c02c0000c50340900300355181d14001c94094612900c17407185007a400f5999040c000700320070280020340344c0940803e0b0360781d010b4280050040c000b04c0d9200220158843c0c80c0907140440c011910010b0380210341d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716032194 1250 716030944 716030951
    0x112b0e060a030e0f070e060d1b0305030301061706180a060902070b04150209030607030c0c200102070501140a08100801050f091903090506030406060f0b130b0306030d0c24 75
    0x40401c2c0500d0940c0003c00310b24960000d0406200780c021a10005407c044200e5080c41d0000003800c100001e0b42c924403404041c1900340400104011011000c6c504036619612082203c0e5042803800034103c01c200e5085512900340c3c0501300240c0860f03d00190094602c010001d2910344407444241240d1110f10709941213550f0008020411404404076007003240151403d50401c028a80400e40c1d8920250221050603203d141c41e0f1003651090154009032034102945114000740c2410320ba41c2039003894681d500601902c4404140c5500840691201020b022800740c9040c4800c2c4044504020140c0844120103070100e0000e82c1101c24018a4003840c0106405a0135040ca9440c180c6041080203030b030b03140e603030201c2c188601194020408004581d81a28140e0b500d6807140380c448010011600400980c20070144045500707941d0f00040c0010114018410000c0d946400c01180703240006c40701d00e5416030142c1c00c0040d04a200d06d0700304440310300c00d46c8608542501d4195009261010b29680031030f6583d17 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716033444 1250 716032194 716032211
    0xb0a0f0e010203070c06230c0c0a0f060f0b010f0801090c03091202010b03150405031614070608090d0c050705040e1e010b01090b090a050f03240403112b0e060a03 71
    0x118440c1507c9541c0384d0702250104420350a044020080c000d10b41c0c040d1680108091000703080a0140380d5499900401d01c841303075603151400320005c0695422486020785420715291840d405210b055941e0034046d1141c0404d80c0c60000c07444041e0002a40c01d901b00354542c02d507400010440d11003c1c00d42e004a80010a0143c0900c0034107180c41c809801700f201001c00715040c400450804000c03110f8102032008441d03d044860301f0201d104c1c0721031049060003841403c00000e2080c1d845802603008450000588001c418000001c07034180087c02c1e0043c000d5040710804001c070703103806e070302070407850303010b00c0c213440c0004400940400c83c0c1e940d5000c4000c142c0d45404031400b496034007800c61000341a03654101400c000080300861814000e0b4065507015480000d040721550350304228482da080301903d00d0030354040003180f40741d98814003138030f00718040340740000070380c03203140010840c0038440b00800404d410000a05658041800c21400740c0303804d020b0f41c404090303581e468803401404040342503200401c0800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716034694 1250 716033444 716033453
    0x120b040902193003260f0907050414010905060a0305030a1805102709060303120c0503090a12050708042301092706050901060206041209030b0a0f0e010203070c 70
    0x140d203110700c8001e01c40140f1072100303002c51100c1e07000e00d2505444e0440b0707640e00290a0f00310200300a0300200b04811210104a60400d02e1000b16110303c10384401d65a8042e620014001580d5801c1400105910107100601240050341d004940c03068005000c080410368036160b0b02c4c2168820000c042c001034041524000603d5034000c920028601960401c02c0b508034803800405001c498103041000350f05003100318103ca04010404000341c289140d04000080c1e69250103041d464500522141142c240355160b4140340c001c4060702d109800c05d80c042c6c810441c1ca640c4500841218007203450500c43c00380b1196000c6242d0710054405000e000c2401c544c3c10390460100460307424641c0078035041080c005002e010045500291094900c4c44000c000680f500c40c503904005003c40da045643c212846000004526070f0020b00c80340a0f5000d88043c087c0d000c0c010754100c400b19010301018201d404004040b4030211a203074800c08070310740c0080c8002501581e40e0003030703801d9900503030308200041c0300d620b420780a20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716035944 1250 716034694 716034719
    0x50705010b060325110322091a0d03050d0501270c05040b0d02090d0302060402190303050306060901120603080903160509010303111005011e0b0307120b04090219 71
    0x40d04550003429450001d1800d640fa103c807510450091135910f43c0401400d00500030102c01d507181034107481d01d8050758074200301d0300c07000b44400b810142e42007100082c122019200f01c1c0651a41d0000514015042a045c0402c4521600d012420004104042c06000b1813a2041501a00c40c01804d03411a52010b043c101c94030b0181c03800031007010300e0f0004099903203030441c0488003291026000e07036440f95983c0324000028020b2508498000c50b004440390704041c0d01080c100d104510031940450b2144854030b500d04100745030b000080100381c04001003245440d044010340f0703150205142880c0f105803842008001d480d41a1720440740d65001088079032440c50240700040050790143ca415080601e03040020786440410302c00034040c84039040c5204406c100602011910024850051185580d51400c080f000103020095040c2000752140100c0d606454a085038001e01180c0e40358280030810800810061416500075039201c1e035180340400c0140c450050595450b403c40e103600700340380e00e410070341182c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716037194 1250 716035944 716035961
    0xe0106180203060d030809070b120604320c043620030405121201050f040515010e061309020304050c04110412031202040803071a060f0f03190305070501 67
    0x280c0c0c1c014400c00c841c503242d5101981c10b10f0780620b40400717a81c5904901504080664001840c100d900003160302d40302103000c00790f03402494161010016480c0825103c7d0702c01040c003110f40800d000701990420401c041d24400d942000c14490802d190541da5500003200186100007050b05039242141280d401c03031382d1520007142d040d541c5802d001c0c0b2240d200d440051040309002111550b00c000c000308060010401c02461f405500f4814541e0f1800c00c0d6400303281e0441d0901c00c803482400d401311801d0450402e4003540c0d010340c0c03e050030740e80032040440040d41d0341c5c0d030b00324140c80d013010062081111582c543c40e0120018001c000d00180d59080900705181040400d0f00242d001e18180182c0741c102020000449045074030510126568213814075007101e14281c50560944802d00124012415040100c000c0246902c550304a80d08071600d020f130b4424103407080741e40c603602c041206200729280c18542c80303000e03c2c648000c040c0c82080c143c403c2d100110341c0c0d01311400e8000a002040400800c4002d00c2003265 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716038444 1250 716037194 716037239
    0x6030114060a061103071b081603230c1c06110703090b0d021e03091c02070b16060204030b0f100503100914120a0e0a080703060c0903060e0106 63
    0x8078940140400c1e800e224500c240340400c200700015400301c05051060300c0000358000d80c514a4249480702030407440180d030052540b140520980e07086d03040e10301910041104da0000070403203144c4106058a00c0124180345840d014001e15840010301d035106372505603112050303104126040320b43e05100c01103c600c01d103903114042c006c0003000042900180303000701f11840040d085070b40f8006201241c0190080c1e6a0031090049200e40c2c0201c482029000365106149020803a081c08284e00f400c01e510400c038507400d002603003141d602408400c0d090402000a6101e005440c6051003081c0e80e1002282c2c0645d000b51003410401c02400b5151750240b80d0b254001030b056030002c0300c03070b030500b0300181c1c8644410b10000d001f00c2d81e030b103501c20400c0070004840710351350945010355800b070100f10b190144075032003c11080006200905840c1c0e0300d00c0c0450f10103003034408007401003500d50b00350350ba84401022034030081410f119040340c00000140c450302400412010200c00400d01500d4006031100f015032140c541003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716039694 1250 716038444 716038481
    0x60203070b01030f080d02040b040603290111160b031006051c02031e04050109110a0e0c0705010204170f060106030c0806040c110d020604141c050f041706060301 71
    0x801c85052165040d00e401030f4140800307003580e281c0702c04607100d000000a8110b00100340007841d05103200141c001c40e8025101030059407554503107a455a0401112a000031086540c450582e5100d01c2c1e419407442403400880d83d20030319040e02d88440d4446640f000e030705000c0020400c0342c400001d1203850001d0115060003801c0182c5101004058500c0840781c013140d903404000601e0900c1420400b00d00364450120b10b60303c81c1440d06029010703240701c007025185407042c1c00c8184443d090010300d581c21554640580d0403141c440d11102c0d46681e00040044e1629034080c030010500d1000982c0c8030311180c10300002440e40ba03210f85d18840c2400d4050748440245442c04942082c00364000c2113183e8010011500011b030f4410240b002d50344e02005802142c0c02e4894105070440c05500024100d01503401541c000d2400500040010366a10b644c41c3c0d4003104580c10380b61445c0c0c190154026014210910381c01070301381a2281e8114682810210b138400c041e50200c1c007803000301e003400e11031841034440851109 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716040944 1250 716039694 716039707
    0x91e0b0114191406131d010f06051209010219050a080f13140a081606050a020408030a0810030f030306030308090c030c060901020c09041110020f153607060203 70
    0x1d11002e20a100d0700d2942c100e02c1403440820f0b542d01080720326001c0d5503051810170907110f011443c41ca00b0003807000e011002c01c402c0007042401d0f07003114005c00c45001d665058600b4034024582a04103501601680496400b0300a0742c074134529909081c00c0041403030340c90a84405042c00000c06078032000d440040c818507607900348481c8400354199140065005140c82e1030703900842c04003915046010001a181d440c010503000d0703d00c109040c460200502600044c0b1898903001d203a44100e01c50703440750134255841004440c4040d4000e00365250312001003881488513960726294040c415a4150003113000941d07865040c020160802c00e102e400220780b40c010211103e40320b001c80d40d9a0581c4c0103a51280700042140003140c0c0c420031207800ca15201500008090610703103084050792102c0b581c1e4038880d4100d112081d104605c00111406aa070070f40004101c0031300d000b200c0c0a04504064142c14820004a02c0c441a80304000621384241422108280041c4004980103040c00c107650003e0007190009c1194 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716042194 1250 716040944 716040979
    0x1c03020604030c05150c03091005090606090405030d11030a050109052e120609060b09040807060c0e090405070f060c02090a0e011d0f070501081306091e0b0114 70
    0xc107544507900d030a10740c542c2e14242c1401032030007000c58120740905604000300448601c144003d5801280350700c0071500b03564110381001043c0c410448115240344d020700300203000340c50981c0309260480e00a0054a140605060b508015a6816003400070445800024400710800a00c03a0718014000c242040140d4140301d14040c00e44034040c0303600b0354001a6084082d401c840b51050400c003c180c4071000072240300407882c0c0040070701240c041c2504c55038648840305045044c2490001e2241da4080d03500340c54140107a50f003000508407042d5040403c4405010440d45450f42c503082c80c01039000d00024071509103006c4a40500305030781c0d0084800c20583c01e039010016155410203540204c40e200c03000c11100982a0402d004001155415502d10b649251403125040c010449900400019054980254a410054503183e40660304004802d088035000000325030030742d10012070248034085100f00f100901d040054a0140d60f00107640881d5428010407001841c1341407020800411f90300e03142c103401034680707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716043444 1250 716042194 716042203
    0xc0f0503030d09050304080d020a02190510140906030f3c0411150a1812060902010e150405120a030215100e040c050f12071406120903091c0302 63
    0x1000b52010f4440310750710200f10040c0b06980c0504181400c442254901c240000d694106189059008038072060100d400c0389444190001921405050307034038203041a50040b00c8030316403d1851a0034140610011040d03659060003035024114030344c21009641011401003188120724540d401032030300406005848049404003e181e10700502c05680182c1c1e135241000d008207000d110345154000c001400c044460302602e400f912400850f0b030740f00d0f5007400c0060060100d000150141c015030320001c4d039451000078a650030218850380b040c501003180300007040c0415503050b001782d0707200130b0002c1c085410701c024108450445a038031034201c024440440079450294407010b4509107403091a0740080041c204078810b1101c8030040c20000d458800310724050600c02e80c4030340300b40036261159501ca0154451032502003034052003602548090448640351240d0a00354020880078650000f50030f0150300c11404840c13451610605000c4091540d0f082c01c001004001c0c0185041005030307001700c0d800b20011950024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716044694 1250 716043444 716043457
    0x60e0a150f0b030a1a070206041112010b04050a0c0e040b130e12070f0c05030604021509041e0c08071b060209010519021f230402010c0209010b03040c0f050303 70
    0x500014515a01c44940c1c018241400c02180c06201c0c0090f00300400540c0e866003002c0788025440b600d080d8642d07003001c0340c44082c140d07400707440c202c0308a418040d2403a1140c50799050601c1c5000000b04d5032030701c10205081d22403ca4280001560721207004a059800441d5209841400c03142004021a0701d000540420444600d0f501c0c0b05a844180e812108010800320000005403150940c9030941e61410f07030708141c810030084600c41c8000c4800540d60400245407400b82b81e0042041c1e181a50741980300b0350940000d441541d0090b107400780c14091710200140659501d2895601003020341300c84102404004000d40000c0030411032071440c14a60b020310b941e03105500c0d8414400f50380d821042c0c004803001e0144500220400038404600181e150300001c40c01c40e04c50070034001ca521900c0341d590403800c844a604408400e510040705500d001154015190b80c800c0c414100201160810f80115282d554240c00804103101d001050009003c1014a028004d00c0800b000f100d00c1410040400d480340030301c9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716045944 1250 716044694 716044733
    0x140609011d1b0604030b15031507020309010f032423060a0302070f0222050906060a06081801050408271315090c030c030b06040302010206070807020f120304060e0a 72
    0x1000c2c005075982e940301128029a0401c0f5400700c0780c18200755481800140c1d0716254801d11900310740381c44074200007120340e20850301ca030051405c05100100650704800c00c183d52a0416542d0409240100717904000c0c80d21680303000c1c804894007410883c03d00d0010400b03074075400c400006480703444144e03a14402143c80c84083ca240160301e49c3c00301d2a1032500c064201c2d1000b035204183d000c844805055420740312034182828501400903441d0742ca10a926050305450103170b044140e1160034807080740240d800680081051005803421014182c10908544080d0350032602c5107000030340014070500941e20b031001212031444400c849000040002c0d6000d52501034250201c1c1c503a0028520140c1d400422401000b11060910109400f0b0390001d0050125008140100b80780508250032030074850155070543e98181c000b4070103074880000c140c40c410002025117045200d403401c0400500010b100c03130001c0d440f03468140ca8480c1400d103418400e603450000402c4865021700024404a884074040c540441c688 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716047194 1250 716045944 716045983
    0x2280e060a061101110a1106100317180405040c061709070e09190506010f09140c0309030c0339060a0c02070806191b0507061107140609011d 62
    0x1800070f5603000d059100c880f142540030101d4400c2100e0b41126192100403807600544846680e040c03014021841c03d400040c0902503455601c21020114800600e03c1c010408960741d0003040303400000f0241c4600f21021180111000310400c00740b0f800071518081080520501d4160749010310005680744003e1154200d1601c45201142b4086814450207201c44861090000c0140d5a414034954824003071040c44c110b41c03244640002e0301482440b803044404221903003805161540c00401d60260809800c96070540030400030000300210410080900c0000da58a807012041a4031034082e00c070800e5800e00c0c4034401c0020f08500c0038000403c284d584003283e5500091a000e0405c07080340b4000307450308178140380e200e14818402086101088000c103d11140014001b00400600e00d070303048032503c1240c801255051048c2070000e86c40390000d00354850403180c142d01b8500140c8640440f8600001010300e903030000400d2001b00c800c02e000e88544080d0010350401c522054140059680040358007482400b40d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716048444 1250 716047194 716047217
    0x90614070c0b030f0123030a120e0a09090c270e0304270f0225060f0908070b0703231008060c0c010e120f130302280e060a06 55
    0xc0d4264004054908001080e8491400110a001044c0d0a01606000602100b1409001e030740208115115140c05805040e20105d990303511500c49030b8090105080c086100c1034150140c403098030b5000185072006005c60320402500301002c01d14015007043d0303d299650b912902c0c14810501082a601c05140d000103021012904241d0440c003480e00201068541a001c404d4895504030020340000c10040080010b2105018240101d20403005c480d00d407001da20481464500c1c1440c0c84424040c050480030079120b8541290030101c45200d901140c0710311000c2900d205000306212aa40e11001c00c0c00c0401684d803882e124034540c49265090340031003e051800107100407108218481c02804414121841410110f19600550b08601e500c500b5541c03030a07a08015102002071a070040355090240c2e00e03d050a4444000c0301940203075a0b50541c000219000001038a0300d680744403a10700b4071240c0400c051400800c100044180fa031080c40800106024048550341d8513020200320b1300c590800c2c941c07039103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716049694 1250 716048444 716048453
    0x120714070b0f031e070908121204080d0e0d030e060f06031b030a060c0309170406120507031803030203061c1e0519050c010807050a0806190902040f080d09061407 71
    0x100300042140d01c1344400341803003046a000340305a4140e80849040e01d80800f8a421486e5581c00b5420f03007204000c00003004680821203440c010400c0b00c045410118a04000d0902c09142102c8280710500295580c10343c592124070030b010003600102c180026216509011001070f5460240e0f8104010700400e000356001720b07a41c200700d0495015840031050040c400001c1c0058000c189904064603140c0002d009020300b0501c2c07408482c20388996483c0c04440904078405d1100a144c01042002803503600c40c00c40d9000c0c1c01c0071303e0300c0c4084ca119980159072481e11209124410702859502102d407410396168400044681c00400a03480da81e00140c8880c2016003429403402d41c20f40e051000c42c0321805083c10521001281000d4920400c1c1c0f0364261949802c2c8003180c0e207206400c102c6001840500200d5218031b0001985030100d00c0301502d03c0324154644042004030390181c1c0c8010314031030010b5820003c40341d003484002d00000c00c034100004007a14120700581900c64024040781a80d200141d80070411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716050944 1250 716049694 716049721
    0x3030f021b0703111516020d02040911100302130b031510020102030402010e010e030d0f020f030a020303060f09070c0308040c0f030f05100606020c01140408120714070b0f03 76
    0x45985600300c01007000e180034016141e101c030707000c151040040325488003405c4c140184805040031303144000c1ca16010500d500a40401da00c90f4007242d12001844403a405a82c450252268580c0101d1700400842464030800c07200144000c884000d260060080181c883d40b04c03e0600200d034102401d0540c1c0e0b41d9040401030040c4641d55800c4d83c0450f03040b81c8528055815806980305c3c5100b1780b00c100a2000e01c40040d40e8156402e150541d25901800000860910070302c40784a00b5038060044407003e481c808481415130300607089210050344040304000c1c80b0b2410b05d0320b6a00411050360300018908005a0003410751200d43c40c040c003800200008141086403030040317800148904c035a090742c1580c81c0e1400100624148a0aa419200744100300803488081d00c60441200c01580041810300c0c0840300640d0f400b900c04440440c074000034080000c1e602e8042c000a0211004100400d5482e90300b880c0404180c00001e021401c0b5038030011003030022440c0f000803500c012111a0030207840307a440c5000c48228 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716052194 1250 716050944 716050957
    0xb0c0405030a05070f0e0c0301050438010e0414071409040204140111070501022107062c0f1902060c0a060f060803090603040641061c03030f02 63
    0x94401d00d10340b0024480e012400324141d90781c10b10020222a41d4203080a11800c1c1076032000030344e0404100402407032500782d012000d80c44004100380c52402044540044110888405501100c1003070341200c12580e1149559403181c500721400c21010f400000344001c0c6c3d0744002e1105041c8044e10b040e102104540d00c090701c45100000340155130715902c506c031840030403100343c2c05140410800806190f00384000300c1c0c10b07015a9410380c0107010f000515001181d41003080d20120640c020208201d4020502c20f010700b1000d0510018a1040542c40506a50301e00440d2007880301150403203815080d01c4203000c82c10000c01e004010310001c500c6198000034038544500e08201c00c40307128140d500b41c01c10030560080c0c0c8003810413040410070141e86402c900d440780f140d003d0046e4005000c100040024010380d02204083b0b10f0500b9814542851b00103510326203001420040008071004a03c24004c88000305641c3d00c600151512076214491102e9580d0048101c14010145501d40201c3c1c2d1451400d40d05460743c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716053444 1250 716052194 716052199
    0x160f050106061d1c03030b0d060204090b032404151d07060f030e0606090912030f0402032413031101021309141b0309010b150d20070b0c0405 62
    0x144640e2108050070616003064840119102c3e419102c5580c6005201160f141d0182e2141d500b04034003d80e4114014142c0c20030007075100000c0a10080400d000303101030000b4029134000020320358407040415180c21004405083c10300d03016102101e603015600780d4290401e0380080141c41562090402c040689096800259070709006400da03542010001940d90840f0116140d500c107a40345010100d0964960b03414010040e80702001040482c1480c1341101d50140180d01623440d1615202190744269100780d84150b49565228103120035482c041c0182d40c03101c01a10070713101141019070400a82500018058618488410f04030710502d4092004244c030b02d40554000c6541d5802c200d020706c002d0403280149081c50f4030300030400f205070400d1003142c2e00849560240d024007000307000c42c00d441e40c3d200030105001c5540300c86090415455040d140082250a28140c6440340807841004080360842c150f480040c09400040c18054520041101d004981011060202d5a00d104c0000d240d8800ca900a94 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716054694 1250 716053444 716053451
    0x4081f090204050403170105031212040606050a031a0105030312273a1e0201020f070b0f06010c120e04180b180109150c021e1b0114160f0501 62
    0x8144c2d010400440d6070350307410086d01c03060b41c80b4028903580d2603400b603070150215810004004070002100c55940d000f4402c60000c2041516240417503041306c02c0f548110340300051003002080344100c1604c0300d405050b00390011418800804503000c22000081c2c6000d0b00498031848101c1d81d034459141441d4071100300d070100c52400e1b4002ca0040d44003500c003501e02c18003007402c20000c9100c10444c20288100320159585d541d410544014071044414900c2881096660800140d03401c40701c0c400c00b5240b941e000d20b1001a15140071000c4c0500c1e0034008210904218841701080c0004808076807552030a541d40c80d101c0c46482c60703400400c0c01070074102d50032010940d0203e1000c0c2000803c040642c41403030000c40151400c5100e031000c0313080ea1010040240350f00302100c40100602c03025840400441000c0c4121407074042c003a400c4c11a001e0340e00760741041a4103c68500210034810301c04400e6600004c0c80c2481d100cae400411148524050b5401c1803024101e40302404003480714580700c0c00402034022000b013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716055944 1250 716054694 716054701
    0x50d020f040c050c0c090f01050613033314010b0c070905010b091f022e0e0d0f02030a051801030b13050f0711060406111e1c0204081f09020405 63
    0xa070113500030f4080c003030b0148038404804c192801c000780c6450142054000c807030696420501001346d150025696201c80603141003000001c20100c4407110040158074040000c0e80c0c0300110300301a41e5185104140e1140e00b402d0410650001c0d07010441c1c1107482e02d416142e180c284080ea410304003e001d5000c0d184447c00c4c14008903000070307441c0041444e24402c40e66580105103084007040421844040000943c000030b88050382c61a5119028602d100d907401911000344118030400112010b048280c54240d101d001c10321151070b00b04513481248400c6000850800c0d05201c4010024414400700c511f9891400c1500310450b40a03420615a005008000d8080c3c1c880024100340181412580c0d1080358111201040105000f6002d04101651202c050040c075603441c1c1360701000c0d00b800001480907400c00c0003c01d07452031030710a0202070000d0b00703910540d9400103100010b042c605130144110300300303204001c2008023041c0050040c045009000401240c04000203045e0300900c03440202035080b41c100300c1007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716057194 1250 716055944 716055947
    0x80a0906020906121503010501060507080a0c020405150315010803041a0d050112060b010509090f0601021e030c070e090a020126180d0e1e0a03050a06020c25050d020f040c 75
    0x1079500c01c0ca0000035009090720305c44209401c0e9842881070001158003002004040307007010f801811762610504095080d50a154041001c4903400c80e00a540c81e03031000c0d1080e42d81d140c184a1109404880e00c030356540c039410325010585a00c80c510402a4400f545c9100c46a814207083c140c3d03040d048030b03200030046903964450800d00c0804800c2d088800e185400700c034401640c01a8155224038001500c4031060340d881c011321140300800544000d0541c8608110590350150085250034503103448000395803103081011443e46017a10940007802000742001c1003109055000602e1460030f502442e10726417651644441c0b20041c854a024481e480000c0f10400c444107910307407034003a001d9880c0700460f1510702c03a00d8030880398480e00c055041d5115070429907007041402c0e200d001200c5804020b0129103501d03501d946403407500c1a00c400841e1140d03000b03e1103201013103007440402c01044000420100ca800500044840400f280c0602c5110b18450000301041d92207402c2010154007001d0710411980c0c121200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716058444 1250 716057194 716057227
    0xc170a080c06060117041a04020d02040e1006081c05031b1615090b0f070212031003140601030f03080703020d0c08040512130e04060b0306070903170a080a0906020906 73
    0x1c1250104480e45e500710940103025281c68840ea07040070382c001c40d0203942401c503262078401034000c0c0da1110b42459080d015030754600c00c4003080d49080c3c004002640380e09040c041030f190950b001c840250411150504202510351006030005d10f50300d8140d50701d07038030640c3d0100a0500100d010703a0b010720108031050054108a0b04100c0e02d40107004154941174040b404030240c4000060052500d80d8140c0800d4113003401c01c0006070001c040b4010f1381c03080d036110800142c081d0021640d00b2003903401414100203105041002c0d440c0740300740c900600025819603c52a80c5484072550081c10807a00400040309580b2940c1907400701c2d11004802e008081c0b600c00020241001580e085d1818040c00307132000c0d2181c5500b01150010145071308000c1a091500003103031040728000340141c2e0300700d4880f00715155581c0c0611800e881400c09803a2501c01a00313500300052400b00342e8022080d100000c110603101c0c40d40094800d980b1611414022441c0b001c0b52803c100607000380f0349220741020020940c1000c2d4580d400303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716059694 1250 716058444 716058451
    0x605040504060b0306030c240f030f09030c1507031b2003130e09190c0303080a020702010c0b040c0801020423042a0c0203031603031401030c170a080c06 67
    0x81e0140542a2245049003c038402515001d1385580110404201c41c2000500313007048611500840c00b400040c0c5400100c554030240310341c400036000200304084114084003464010140c080218104003440c083c032a46c0345009001e01c2000c419a5001486152094014200000100106a00803a070048010309010598030780c03840c4400184090440803c0d002054440c840041030281c00507030303e800b03d901000364014061064a024a85007840a2006400c081e1019482495504001c0b45035041c014888803000d0032141c0701500400900000d030382d000001040e0719030813180e450300e00e4555140403031030340620340d005034019400880e001546d10b131138120508801c598070b0810750f02039880e0010081207810000b8001842100032450301256865492852081095410050003100ba9600000c0c910740001c4081c02007200c0c0000020105541405805124045849410030550440d996034402d80817900a00165103910000780c00f5450381000b0510403070341c200c03000c03d90b01d4412130241621030300210b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716060944 1250 716059694 716059699
    0x1501170c060a0f170f01060507081e07020108010801020f0f0307021f0b1011060a02090a2d09021606050705070c0807080c092401030f0c170c091e04090c06050405 71
    0x78060489035404c1003a0451041c0300a07000350809a00f010320a40b01508421403c0d01c0340c9205021000314002c090b400b00c1054030103c1510b44c2c07502001c0c8001000176078142c10400f041c3e4014010180010140c60a03100510b0065445940700d5032485412880c012410300c024042020010b65602d860b00160b001101000f810740d2504907500f4041c0f81550132100005400703200360300000001e21900c150b64003800000100515042d056079880c42c1404242541c499204480a003510201040c03149259000b40207000751002513040051003c020080d41040e18005849a506c45000610b00e600c100126004113038420200440701d500c402d20749503104150702405841c0d1080d203110703902500e4038100161050303000c03044d0080492448821000c0058403490114107150b10f55192560009aa000b150129082941d4441d0400f8401508044640d0302600044141c42c0c03c200c140f44a80f100c0341c00340f019420402d800400b4528800225006059400000d401c1c140101c41c08902e1561140082044407002c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716062194 1250 716060944 716060957
    0x60609040f023403020a1b050d0b0906070c050a02010c021516060b1203040314190302010c080703150306152103020c0906100f09150309141501170c060a0f 68
    0x151003026883e26030b00c003006005a0300c041c0c050b42c001030103400110411010004034540013640e440100d00d5080407254100d4031320750104c040100640f800c01080d58032482c50319040c08484481c0d21880d46034504584042d04104107660404259215440d001d200070809120341a981c04050003041082003d000d0112880c07800c3c010b8a100701e11b040003140aa840c8108081e40c64249555681c40007070b042d20716907001d039008180c940c44441401e01c0342c40325000c2c001c0e000440d055a0300a0014110a4000c003200285403402c00500250a0540c14910980e50320040021b000300c44070747d6507408020f0962144907005180184c01a07150002034810b00042c1c801e4003207031060350301c039801c001c2c000000711385940d040385508240c1d459991042c8010000c000d258204070401e00d031610152070980d00100940300200e916610100b08201c0341e0030010803080942005007851440f4400a12129141031141c492810711a2079044c0d5640303024844001e19510081c40190f541540000203030841e80940c0c510b0b0040741c84c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716063444 1250 716062194 716062267
    0x518090a14060406050105042106090803061804030503160207030203010e0109030216120b0421031e0501140d051005040b0103110301020c120f070f0b180f06060609040f02 75
    0x40a00a1005445c0141c68080c1414208820032901d40f18010a428220584401d1500404d880c0d00c00c56294a0141401c250740b4070300f50091020040d54644030400090090f030070400480c3c0c0c081d060301d400c40038440c0540194042c02c0c100700d28100494102075410f500c0c00300b011207103c0d0154440d1180078801d40033380303906084150307404405032000e125840c07101a4940061001403000440310740c2c13061180503403556001c241e04811010f030420308542008603940d501c0034030100c0c20601c0304914819502e07101384160346c10042820f01c00c299400c040750103920601580301c10004c1c01c1c011131460042d03030081000b90b4a41420203681d08a828170043d01e48040412564000341818021640c0d041008001817002102c80b80c203004440d0703c404020309114609003c07141c000303800a07819048503070049510070460b0418082c40c00424245000d203420030b40c00140c0554030b00d9004264550b00800881d00b4544840c0444003080143c0400c0e07800c0e8a2940c07000451503000800c0660740d078004205502c0d026034022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716064694 1250 716063444 716063449
    0xd0e01023c0a0c0308070f14010e0f03090f040c2601091d0303040f110a0e060909030a0804031101020d240902090a180609090302240c0306010518090a1406 68
    0x105240406425000f8000c8240086102d80c1c0040c98041d1142a5001496611740c8070112005803011510106945415100d1389501003040400c85a2110001a502e04244c400c0001c1c4c80984d030344400c0e80150744074125024207034054150080d003904c2d500c034807008811340320000d01c100c1842400303400d86041c5494158003c450f1081240002284460015450b6403501d860341e400d0080000c0302118401404201c41c5815185c3c1c0c4003220041061042c4c9032402e003481010050086001410a00207510600201c06419071100c2c03039070380250301410442c0741010403000c1d00d800b80c811601589203150a101d04022400800c4000040b0b02c074084404e80c0d09a901c0d01030703010581c4100300e540365224080340c10a108280c60901040ea21010700c0900090303641e91600014280d454141c000e8005d6040940e10103d41d0302002074460036644c00c07244050283c40d03c81c50074046400042c00d8581003200214070345418890712080d02840c0301e001850020f5524007982400083c04044050050040000002c40c4190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716065944 1250 716064694 716064703
    0x80702030313030513080106120c050f0d0b07020c1c11120c01110a02030106090617060c040e1503150115230a090b0304080d060e090d0e01023c 63
    0x31490b61199000c03074107894a04880642210f4107110a004608500065442003445240020030351050748410040c40c80c1040c968880b100c0d0301c100c3c0a44082c2c9a010701546d14000720601d4154003150b180c9498031440c004a24050306d481d000b82d040440c0d428110142c508040400224512400115a11800000610080c0c40d008804120940d1040713480350101d40c0210f16040750081e03880e08450491080d40c00090175a01903910060f030680c1da0341418804001d0b03035000324500e01500c90092106042c00300000c511440307240b0940c2d209600d440e001c04d0502c0880d0b10210140c0f907000302140d50f125080011112562420301c140041107101c14000101c850041c0d503808004229029036400006400703054001030b90107070a1000400c0010000070484c2641e100103540114000c4050342c2c4c480354492152821944c07940c01070415440e01134104032105100260050b5031104e0391922152404450700181e1501c007807013409460803058092017458000031031424103415840d001c4000d40000000214a448 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716067194 1250 716065944 716065951
    0x905040c15080703110c030706021e040f050d0c0504020703090501020607020106030c0509040203011d06060112050c2a0d0e030d03050f010b0c100606020c010f030513020f2106070807020303 83
    0x1c91400c000080303609000b07600c0345c05002c042c41c5181e4506201024480e0441d40209401c451540c1d0216420303070140c20346075040300d810740701d05101840c040c02d008214070760038540e12919101c1e070b02d070741076242c10000c03041c00c180010100948295100c1d10180703405050381c422802114018407480c0001465284140035035812a9000116103203081c0c10442801b0241c0d000620680c0c241d074036441200503181a442000301060ba90902524050401600044c0100c0520000461190411042c0095004c00b0340c12a1601d00c0079140c208048400c030f402145000c00c981903140413901685540078017564100c0440548039004a05451040403000c03001d07001ca850548400755814040030042c050181c94000a22480d0b81d00c0d000c0751290100f4280407030507544644c11500041c3c00507032a407a480d5030007a8020042070702d6401c003844146807900409101c440000c4011388501418030b82406940c455a82c00d50103801100310300b1602603024016150344020580760314000900e8280022009232010054030301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716068444 1250 716067194 716067197
    0xf01050a05060c1513052506030b01020f1603021c1101050c25030302100c02061f0e0711120306182701060612020702030d050c0a0b010905040c15 64
    0x140c1400c11040c0100d540140110094522514003a0701002e54030340c42d010310801520800c1503001c9014646141000d071003e03030350b070784000c200309101c1c0800c0a10380100e025070f2070a2034002400032402d00100d2030003151813140540da01620015414a030640b030189401d5038001e40b40384060328683d8008030305009003650058240441141e00703032015807040700141030340c540c44400c03a141c41d540c041913a0882200b020840040010f2010304000300740e0140603030400d00043d4401000500ca400d040a52561001400d0030845000d4003203c0c49540c00e1001020b014000c4a11901054640103c0c040c081c41d8512400d02e80c076120b0101c0c003455500c0440201c0e84212009003462106111480d0440c0040e400a0000503040f4829400708003034159604011200b490725400100e50a850405c001c1c082c540c1c0c2200301d0659600402621001d40c41c00158590f400d0243c0c036029035070301d01506006003408600e00d0b00910400189000080100c01c2d0b8000500417800303041600c1c0a2591011416070881142079100c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716069694 1250 716068444 716068459
    0xf070201030506190807140916052a0106080c3304030609061a0f090c0304051e0d0258180602060c0304060f0605150c060f0105 56
    0x401940319800c496001400944113081138a03a502c2488602e00c00c2da00325400f40c0d44203803030411043c06c885000e4000c4038801d450210b140d04028440381c41c0c000071030000d8000c1c001c0020309200c0100200381919908a15501c68124070000d22810b980130b415a4840c0100611445100720210b1422980c80249442d4078004c00c00801114611644143c1d8030118090008905100020206066004000815114610003d014151100402203149c544000d403030081c450300c40301c40781c01d0310350200d080d0300561964141c640729074442c9403035481c00b900c117a02c181e81c64440f400107403810400040e080182880c95020344900200c0b4031046070301c1580e09034911108190440c0c14845e401000c60711001c20285a142c1e60010a40c1a940c07805100401440600001c1035841c810f00e035140f0480300100039011501c09003002d82000400c07101e03e03000141010303094903176503a042c0410441550141004240c05411420311848001030146180c10184156009026050028100303130035190a043c1a110020000e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716070944 1250 716069694 716069707
    0xa090606120b2b0c0906081e0a020a0605040e011d040f050f0607090806240618031002030a050702010603030516110a0b070309080f0d0f050d0515030c01050f 69
    0x10000d0b15080305041d8000d140058400400545642c990034840702010450800102c10324004100c01e00c035501c100e80580c030f8500203110a600204580401c0315030b0200b111101e00c0b90002d550304014440d00300942c0007001020016040da0000060070440c2d4140c00c04d0582aa0b80e0304c00005a411003101d1a00121141000240094644401c000c51940600111101c010000310b07001d180100c140d42c00c0c0e01050043c8001c201c1c1d4030003000b0442c0e10040c040202260480c80244d048017400c81c428a0620910000c6108440c181500c4038070251070302e00504039844441046204002548142c0d0420700c500e04060000312000d00500407081180e80c1a6162440d080600c540b207031040402841c1144d005000d18040041c0d5610035000c04064890b4080450f543c03011031070060f1051016520005454110705034010605001140d003110350356081c101242c0104118404441c035100701141c401545140c241031060400c48020b46017240d05042c1d0851f0452442c100c015030300d502421001c0401c2d928104620b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716072194 1250 716070944 716070977
    0x3021b0a06110a0c230a03050a02060f1c02030a061d0a20040b09031c0c02040b01030216060e07050a1a0a0c17030901050c0403080307031a04060608060a090606 70
    0x10114002e40d9016074140c00c500d0f98070503105000990100c500c0f0710303104110341c0101450f0300e0550002d503402c441540d1441d14550729a921003400c0c0a005e0320030744001c1010404005610111580120a011110702d480781c4201010001d40050f102c5207082e5140c608085200d80da502901c0019030035881e0041500d555088010003d0170a4060300940d0b003400d0b80c040741c80d038881c1c1005840a402d00e4018562a2030164061501d4000c0d020744d4480c0000c001542c821601d034000003200301143d0140c2e40402e107401c198006802078411240e0145841020405070418400182c2c0050814a004e0040ea1405a9175608002030010701c7d00802c0600d4043c1d80e00c81106100c01d4005007031036841810000c8585686850310006222a58104c0403d842d002040065500c000e126181c0d0002030800c4c418103240c2142c41c6c8003190b000c010400000e0540d80c2480750341c0c1c40340f6003e400f045418010000e10000e074581e0700041c0a0703002603c0080c0100084500801c62030301d18000c003001c3e40e0f01c0395244892026608031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716073444 1250 716072194 716072207
    0x15050603100515030d0809061b030a0c0201060f090209130209130e0c12030301080c010507030f0e0420070510020702091b0c0a06060513060810020702181303021b0a06 73
    0x2121001001044901c43c1520180320404450429881d04080d80c034001103201c0c1421070081c071250f0b040c000200490b004a10030f105480d00105000800200c09403808420390040c00d03940c0000c0700b110442d10001494117000d400070110b05005560040c131007042c8410182c10781c0a24900580d01115244041d180c0f46410f91001201800c540202c40801c10044041400da080001d410041034000000510407040b040185030160a0280b0346146011740c1d98070300408100d46030429030100020720b08444055176480e00070000040c01001269517001115850403113680c407600302140da031300804240142c0e143c0c143c420365000307a80203003c0c10840c0d41c80340e002c4502100c0d403582c503078008003050003064080c2d00d00b04031880415219440c00a605414002003200b41c26071895004100e0703052520078040300502144244000608079405030b207440e0180300003070414000e804481d030602c04000400041c000c40e01c1308403081c9070094003a01d603c40d9954203600030120f05101500c3d000a048030003081810300c00c41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716074694 1250 716073444 716073451
    0xf0d050a020c1b0303090d1a0f040201081803030a0518120a0e0a03021e0109031506030209012103051309021306030c1805060d0f02070f0209010b1e03060604170109150506031005 78
    0x21500382e8648d284546100c0701010640d4407142c0c01c000b05081008558005039495040107060046020940c3c00014a5507244001444da216850305c41000c07410101c4030708903000c40402d5032015101011010b1042b18003030340156884400041c0d00480302826400c00d03150b01e009407600640801c020030102003d804150070540c28031410070100340800404108080c00759581d021440502090151450040101c4414103802c04c0140a0702c020002111a8039904d5980320a07525040042e00c03041f07942d0a104003032665038030481c1c0c0d050000458001d82e0002d80203034401d0f102c06403400c20410b0341204007180d0000350100104800d4550180c2441030346080c402508030440c4080002c200d40d444216a5016a00002c40449550711080a00c0c021460109000303405040c0340d01e40c2d1410241484017540328100070000ca81e40c1c0c200000003052807611480100c030090700c10506d411200e2640c40d9030f454020b102d2484261802019048042488074103801034078020940100140100600c01d1409002081c024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716075944 1250 716074694 716074703
    0xd020702011b0b090c090601021009110d0303060305011a180402030705040603050d0905030f070608040f0b09250b0307030b0d021002010c0e0916050f0d050a020c1b0303090d 76
    0x4061044100c00d0109451480500c103d058005505010340f00a10342420b9007940c80c424141182008076030390740001c2d0500481282d80011a08811600349001c407080c0b0000410b8200030440500c00505405820540440c1c1c8a64020000071941c0c255220744c26600d508011340c0607030410411045c098001718240e0300a400282580d984958500c00903084585540c011621074110800032507006810150f0000282810b8000d05101c0440c03069458803001c06001d14001e02100b000030074103001c1411b01e1001c1c030340d510040c0110b041c200011603603680c00f10380024000408034021031590000803012a542264855940d1605544030004180d001c5c004506006802c02c81060152000d0780c0e41280c1050300610980000030683c40c1c0300401003903072080701d01490003100040184403842e02040303002a031b2408a450030035202d1001880c0c0005521a06024a03c0d81e402c060038400c50410300e50040420002010071520038200e000d00c0403d0f80d0100100b040e80c10780080c020000582000c80502d070700300303206 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716077194 1250 716075944 716075957
    0x90c0812070213060e16020d0905090a271a070504030305032e0b0a0314010807141203040e0114101d032b0809070b0301030609110d050d0818030d02070201 68
    0x480400200705c4070222240c0c07665904a0300b103c2021501844451300714109850f0803001503050002080c51600c0207800c003025030390364068084c00314003002200011003010344040c414100241c02d10715022140300c50b40490b80c08440010810b800c1c000c10845049942c0f54407040d04503980c00c07900307000d0140107503040400c0d100028a401040030300c8030b818001901c0e20b428581d8039034105240c000c046070000c5001c070100a6110300140071100000886900306d9540d03a0000d040c5e184400041036007034902c0300ca0b07900a031001240c04034a501d134102da0348c2d040e00c84036404411440768100801c00101c100b0071540020900584a40360075600c00c84142c0351160f006070440344074490511810400c0c850284400d81c0400d000358412140543c0a01040d402441c510003d03e102803c00300401c1c0c00b880184401010650b0311141103042002c0720829418000000708182c05c1d0b4400d5042c010b0b01c031040350409500040000002400103190204079143c0051a03000850504880860482c025030040b1000d9060288 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716078444 1250 716077194 716077199
    0xc1a040c030f0c080c0d08070206030a111c0b01030b0607030e031204030507150f0f0f09030b0903070b06060c1509030d060f061b030e1e03070801090c081207021306 72
    0x480001d81c03800e600c1000c580f44001c2c074208055003044030000703409204a556110500110390854161132816030100ca80300c1c0d894441d00310301401800403245181250360040780d19000740e03042003000031440b0802803040c01082045401107044500c40900598007600c24050640440d01ca8440b085036413030301400315001881c0f441e054502d6a0460352044400c2e90000000b03111502454946c040513500c40c6c1080158200e80030005404410f841c03840708d00308040c0c0c03400c00717070494401d2802000468200181c5c07900b500b029080c450320b070760000000341d40105000010484500344001204c036414082d1010702407092803110700c2e0071451005802c0985511080c0b0400e0925005840780d98024081c050020a1b0f4920700107028080c10080311018480f018115100d0000c80d81003405038124a07806c94035240c9408400c203035030b01e141e10aa24070039058803e240001c83c1d000e00c150300c0444c0450290310f28281d4103a442c10700c284c4c0c032904401840c4079654188185001070030003942015101c04071040114440340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716079694 1250 716078444 716078453
    0x10522030c1e0302011d07030b150604090e011805060606090301020730030203010b09061b121e07051504050a050d020c09090309090105010e010210060306020301150c1a040c03 77
    0x402e9007010034981c01c03040d450b60800d90244203000007460141c18140540751000d05650301c4003580c0c48040c000c40c4241000a140740c400d503c2107182050003d088685441d103601800e4001d080c1c51040e0702040d0305c1c0424410006010204842d02c540d4004000d1595a41303000a1000700e80007014520b030990340910404000030b2501d0260009550000d0101c0900c1d4803d580c1c001d0900f51100b0008145481040140310008400003100d000b004240d900c0707030b6240040c225800300d0700c54407240b6140c00d00940b132181180074000401024800311030350706400340c1642100c0030f180c18070501200906507404544c0712000e40d8280d0004541c064003031402e0707800002d0300b07890301c40c03d0074900e0f043c2c04010380184c1c540700c2d020b00e020003207580c1208a40000b1428142014041a98110f041c06084d050101c9800945460b80c400c000383c0000408440c818440f0596a2a15801a400038050104030380d80550b0b94004030b611502407440305a4000460141080111084240913a00604180ea50458030343d800310220b07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716080944 1250 716079694 716079713
    0x30206030a02070302071d06090403050d05100602010c1125030203070b09130e0c0112060f090f0b030a0201020709020c070308030c07060501050906012f0a080a030509010522030c 78
    0x601401c0000740c2d45600603d402404c104898104244400c041c0c109004d41804041ca140da11203029108082942c8550805039600d0140e00725840b122820042040083c0f48000350203021101550028071100d0308060003a58100d00c00350303510920f80d104403d2030160000201146500f00c002d1899291103907120f8020034100302c00c0e50041c10003500001344035912828801c420131580f08100300c04000304d0009203c42c58441910025044c10003415a42e00355140e61642d01100090050751950841103607503c00710000350500e40701c64002d60b4a041c0c0900f580e0f041c0412030b00c50f0903078140d024182c41420242d10100a4000d21141d00c0144101d580c044000b4075135000540c040e16142040315110305041c5001d005840050304024021144182402126608011000e01c440e0301742d8141c085001c1d5140f00302180c5170940c9041d488500c1046261410320011900400e02131420380e0b0103120030798880a0040c00e031a02918410100c1c41d18800169050701c083d681a41c036a07100c0d20b0444c7e0070200320785078a0000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716082194 1250 716080944 716080951
    0x201151a091908031207080f0a0218040f0603050f060114060711060a0e0906040902130f0905150105030d0207080705010c03120f0e0c09060d1103070b0304030f090819140703020603 79
    0x141d04c002600c0c1c0b01412141c0c1600e0381701c600f41c03411000514111444890008000c2c01060046402141080f03100c40fa0290100d541c00c1c0161040042070b48503002400a003449100c1990b0764003d07641100f10a00f40820f0050584a941001c5032a10154905211a075445201c00341c440c00c60086000101e42d40700d00003400d081c8950359805c1d1160011204000018002500c154425032a103541040103031181004102c290192038000221103050108803005881400001461402001c01c6000200388500302075040c4c0702c090741110b0180900103802d0342d23551681d009241142e0300501d0104a25846030310300d401103600c00e151541c9000c04207500101a0341120300c8401d001e035203e041d8003510910800282c00d102c001150340d0251402c220001c00c20a20100c0c038050070b06410702e05031a001c0e80701084040003c00c45d41d00140d90324a00f50030001c00d50080448801c0005501c00c1c00060350388000203c0704070b090a01034110413518402c0c1e03075600c0301440c0c1c00c20030768860160040002c0940d40b0040603510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716083444 1250 716082194 716082209
    0x3011523120705130e0a0e01050412020c01021915060816060f021212040606080709020901030c1e0305090c060c0102190912061a060c010902010201151a0919 69
    0x48a0322040101000c4060040c081010450f0510100801c02c3d004885001240c00004180c00e40762280e035804805001c05400040040d0f00380310a1108004c51040040c0070641b2a9081d24120f03081c1c00c0049850b481d40540e103804010903c21440e010035200a8802074074081d4900008615940f5179445041040d000d030f0411100c1c5410070704025584d000030300c16200240740d201800803d00e94007524610b5024a54501c0c075800c03481742c00141048110741c8003c018201000445407095911a01c00c00a58829407043e80004e09103155407180c1c500034103544003c0340e8400d030404100c5030b00a400301c0007441f00611090441c400e01c0b0311018542c9401c03004006260325400050780e82c5080110080c424903c01a841080000b08031040101000d110240f1540d154011b401246105034824200e4840c081040d42c1944201e0000319104800703015840801100e00c00c1e002480102c01200a0701d90b003464038840d0088c2400705107503002c16a030f4034500a007040301c0d00a107030711a215004c3c5294404a06039421184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716084694 1250 716083444 716083447
    0xc1e0607021509070b07050c030a200409030801050d021315061d06030714070b011424030703021e040902070b0906090705100309060f052a03011523 65
    0x100c096050084207050302407210b4004003400c2c0b066420b66034460b240304141400030b010804200b000005c1c4001100441d0040480f030315248282002c2d94400a40f00d00054106440e107a43d4a00c0e013090300580c3e0f603258041d1140c02203686804184800d100c92036800701ea00c41d514441c1ea006201051296503101c0c8001110031241a040002c0a8094180e401070350200109000c64400d140c0c1d5420200c0384e0000f03940c03030034004405401c2d0303071400c4600540c500204004225400410020700c100c1c92010f0898044a840e00140680d402800180d40c18030404c441000d01000054040d038001e8005008060f05010303944500e01211318841c40d9074110b50040d1403010b80006010041c001d41c0f000058218034100c0162204c0e00f8900084c41c0d8503526841103601031101c506140040b02d000358000c0039400d03080402449154034003c4400c00401c070031215010800b5009050b0200848a03103119000b0300c1086c3c6000d0702d1a400e0050380440904800b20030010040c1421074001c1c0e680910110b01e442c1c018003000355 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716085944 1250 716084694 716084701
    0x7301a0c0c100630140a021005030907030605090309040e1005061801030b0a061701060303092304053301020d0f0f0e1c0c0509010603050610050c1e06 66
    0x160500c6035001d03110582d14208002400070038400d0401c02c24800341003001d81d10610307110f000c405a903075000708040c21562021040341104135010071540c01082c800c849024a00410032026107441c04151000f662a900042d81440042c0c1594007207074003c3d00d040220b17406e25565100140c2500d400851a10882c0c001841102022100d0300801d60450300480f1094a1080806503c407212401440041c180c03942500c041055104030f030b8804d0b00900103842202c0c101c1a1b40c10b500354003911452208a001078140c20000404000700c1550001130a028038680810f050f1400800010b0480904082e100c41903e07030100c0384000c0f12041040c0c2d402c8112407070b0b401c20012100060b00740b003603403e05903050090b0b030302d05040540c1d40b0014152101e6842d0030082085252980811000c1b00e0710161241e1442e64055844148031810141104645080702e48500076030325a041241940d0099030442d8000320124403400306a40180080c2c42240450f034211784001c1004450301c0f10f40c110124008a0a410800a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716087194 1250 716085944 716085967
    0xf01140132090a062102160308220515070302030606091e03030301030c0312020106181d03031e0108120a0804080f030c04030201120b060412020a090c0e010207301a0c 73
    0x350000094220411800c2c03035000401e882011045d01c030001c0400c40c0d41000501e46060b048ac101e01100d4440c8200c3c8001021441e2069030f911004404001603402000010350451080c000c41e44102405450107060071000c3701400760a4001e0040c40351000310700d02c0c1848003520200080c500070741c0075000b0301d02154030b14201100c00c2c80d20650340404590601d10f0a00ca280da000d80342c94643e060800c6c0024841003106001c048504c0a0000c104080c0000070921004040e10b00301110129840002d002c541c3c1d03038034041142d960308290302880700e010041c02081e11007402200a1640240240d803500e04e40f0b010076010400751341c41120312070600c20000c103050042d542d0084045c2484916082304106950042c8005801c501403441042c200c2e0400900e0481151140c4060800034845450148600c071142c040c0031f422910700181c0c583c010301c150f80001a0016000529803000d51402c104807141407603040d403002c66046420001d6403000040b04224005014007040c00d48101801c0c0780b2030fa00d800d6150311 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716088444 1250 716087194 716087237
    0x403080a180905010305070303050f090a272721051201050f090105041104170309120a0803071817070f0f0332060f01140132090a06 58
    0xb0040240c0341c1001480003c40c0024800241e80d05418511740742c100d00100010148651000203401c54007103c000100c00c0040342000702800110185180003810680c00f8030f00300ca004182403410b44085620f2064000030315102c038010345015450002c400c0500f00c100010210413600e9500c001400000c0c030094452001402501420040741c1c09030581c1e00c4500014000340301801664484d540e20119001841540c0e01200d00034420303601c1201d828221345003115101c1c0c000320a030302d0140e566051611031812000c07485030301e000d5214209504644136007100b243d800f0101c540301c0d10102100d05000c80c09400006e98114440303c000000c0c56620305101c0707011200c0426070301070081080118400c2c000280e00d1011664160b88500d511040d00074400340446a42840107250b103d18007a40b401e201111480005190503a1030207049441c000302e461004540d11801446244504142c1c0940b0560010061500016100071315081364203205942c1c00040e02079100b58030041c003080d40d011500011500802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716089694 1250 716088444 716088449
    0x50f0418110a0b1620041d150c0a0f023f0a050f090d0c0f0303170705070f11060c160f060e09180102040608040b06030607021e01020403080a18 63
    0x80792907040404c0c41d09401d9100d100202c0c018100324801c648402e58200700d50019100c1e5100400030300110556106603403d08070b04010088550003104442c06402026041c40d6008400503401c0c7c610b411034405044410f107e03144601011801802842c00e00c021074090318641440c00e00d5508011180444640c94803400384110742510903105210202c41035400500380c81002c9010481e03142e45080d000005801040d04002c02041c07801c2062001c00c41280c15020001928480d85581d20b840b988c000002182c4a8116070550000d44200403a070001416620400b2a1500c03882c424111300984034009492500105ca10100039400810510b801201e090311090007843d0001c65196040c0c10140018030034020725001c50700070010400461200d82c141c01a04e0784480084000b1500c07a40c0368a0700400c0080159425508165410041900d034074010640c14000c5a198000b4410707050840303a80b1000703262450351518955801c0c0400000f18400340300511450455a46264180100c01120760340188182c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716090944 1250 716089694 716089709
    0x80d05071d131d030c01140916050d0f06111809010503030f0c0717030715150315020f040f08061806070509130c080601030506100207050f0418110a 65
    0x304010754003900d445078025110541407001168000d200400200c000894440352002c0313101c00078000c4900724040d0301402e0304092a41000510b40c80e181c40043e5250908080b0000c0401944020492032070b1100c0115680d5108285440090015031650030072180380003449201140c0c00102d00080e0081c889030118181e000f00c503110f80c03650400d008a5581e005042c200d41250030300140e03500d40702c801040898014009a10003001c03103100090382903101c0d04070600844d80943c160705030320310300c140301e000300c04504101d00c2900c0b44c0b183c51520f812a1030300c3c1c403a611a80c801d508201c01000341d0f507440010b2014002c40d8100500c43c0d8944110300340303080d0340101012840042c407561241000b0700420126004101352600c0c2c2c0d128028080041c1302c2c900e104540307000c1e06190401c039088071900008000d11a03582601d04025a03a64801400a10703065444017400582100400340b040e481d00d001c004000c1d85000e000020141400c0140003204403842c14161960031450301d4240280c079181d10440040c2244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716092194 1250 716090944 716090987
    0x180b090703150b1206010902041409060102100f020d0e070815070507030e150d05060102010e010c0210110408070806150301020a080f04410703031416080d0507 70
    0x454407000c102d4103841081e02045030b00c07980c0000481e0b0303441c2c54000411049900b9140c40d0350752002c401c80290f0091040c0d011a00440028424a00d400030032036100c2c909c1170700a8a25650650f5218005040c0d00d01c00303034021b5a003070001d0081002c0340d1242404e4402240b008040050502641a02c0c10941c8100464020700841c2002070081d40704090302d84907545402c1c051141e100c40b40002d0f209141d1500c00c242100d1010071900040710407500214003440080c1c008006544242d9803da00741c070b0f42804244003503030090840e410154203070740c04140c0c0c090500d41054180340d107440c4130a040010035402034680e6805181404154140c4126007510030004070021881d082c410072000e0800100101031800030f0b0051390010f01400100d403089038421850010a054010441203e034200d81c1100019080000e010200200c0f061000111001500c0d007544a11400080340d1120110b02d52010520130001030710b0040c04400924050003400c14203d944101203101d00d49000f00910709182e40500300c45c808031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716093444 1250 716092194 716092199
    0x741010f020304030c02062b05011d040c0b0913060b03100b120105010c110d03111002070b1b07140606041109011d040921080705040f0b160501180b0907 67
    0x7007140d07040e440c0f140e050b181c890b165150714451040426004108d6a0500030b80f140c15034840e50035034001410380c1c07402210bd08940c6424039018010300c104403002801c0006070300c028444880d510001c2c0c80000d074020068413200148506030016940d0395030151541c0f10011043c84411005c03688060050040d14100310b00b00160181c054000d88010301c00c4c035045c0544a84610705001180c1404001e10380c02902d904004112850002e08041d0340c2d00400c1580d0158411442c1d242141e40221040307150044080c0c0a40c0d01da4004203001c110500c41c0521851008001c0c000002d454801c0341046507a01401600ca145452810302c02520200070f45600185003c200c40b074040da130480d1404281080707811601c0d43c2d402800011030002d0002240c041c2084c40d90a062020200000c400350020900390740c0c8038500c40d00c5010059a01d4040d5010302c56890707500084c1401074054840192012100780701460841070499214142120501c802d059907202500040400307200c08400703400c1d004805176005107115031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716094694 1250 716093444 716093447
    0xc01020f1b01030b1804030305010501050705030306211f18080a0807111e0d0c1a04021f05071109090703080304050c060a1e140741010f02030403 64
    0x469005003440c001d40071001410340d22a500c5000039000140000e20816180c0c2c1c50452820001c0301d003103000038109000820594850820754003010b60040041d8290784070310040250b00c141d0341c0700c00180d0f114182ca160002c140704010324401c60304100301d03a50310f49490741100c030b00341c401120a517420600c0390032035134000848613001c0740e000c46020b141540c140d41300d1030411100d040c410b140940d80307841100c10014080c885005050310b0404c500088404444e00643d00b0303900c0720070002c0f020740007480e0074140656042103088045e030701c144001c2035600f0707203040d003412403420001c140c508030002030012880d0000c01c154100c3c001110801240d4440c3c40b440c144608546e0396060b80002000200c002c401b007001c22070108200c41c0c8013600108003a4480746200001840035102204000020411125150000d40a01098401a03031401c071914504100e94540961111244210400340c03400501071070800f00a81d1040024020703c01010720000c074074004071a00b035580303115081d521144100300384000203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716095944 1250 716094694 716094703
    0x120305030a0e0709060902041805060603010e04080f0304060509101509020f0903060c13090e03031623090301060e010e0429010b04030c080a0201021f090804170c01020f 74
    0x10000c9000301e4107142c1108880d0425010ba80825079207420400046aa916a40c0140c000e440310016242d008041500806041d079105460303582d0805002c00c01800004019801d0382d034403d00584641c3d140c0803039844071078501c0d0b104407001d80e107581d40c07881405141c64041c0305145038501c9080042c04180c05180000307000c899288a12008540e000480156851f24282030307441245000b401e0303550901e029201c8000c6036000034001102d40d03450500101e207084081c403a2a100080600045040d0b65446047c02c0002050324065014040c2c10710b04206055507080e0b50074003600e070f803140d11519500036a05241c2900d2454100f010030032003020041c000200c00d41002580981c00040c8041081d81c41101680311000d8011900060b110910001c100400060014030480e40b04686004000750b6603500303136495148426000f401038010742c81c2c00e03140178000d2880071200801c4090000d000081c943c0c41100130b6006600c40340304080c0342808040c10100c14441c100b64072000380082d2004040b607800b1300b5240c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716097194 1250 716095944 716095951
    0xe01050d020a05120a0804030c0807083909040302070801050c160b040204140c0a18060e09040c05030706020609060708070f031104050405010b0c0d020d2307060c0c06050112030503 79
    0x1100700584c5040c442d6030400400802e160442055a6159100e0400c000e00c0c550b54041c0f18071902c510b510014480200050008100d440040401d40040c06103020414010503c041281258481c6060941a507140420140643e00ca80c00500c06249420482820745d5030051025100c01c10520138600701c00d07110001341070882e0b481855140c2c1d6950b2480028000d140d0340c02e502100703003020b00800007008840700c01071a440240d9160100c0748516801404007018450190b036001820786a14078809091040c000e6800a10942302441a0381d01c45003c2071402c852076008600503030141040c061a064144032144e0011600e192035426450070b0175015090b095003d6000081603914060654075989100981d005414014010301955941741c81c0c0718515001030445d9020360007808031305844540005485148441e841d140c01180710410321407070001101561a134407020600704038840c00075809114030076a446c400c3d01c9401c4c08140500b00001103543c140c104500c6503000a0440c0b01090304901135030f03403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716098444 1250 716097194 716097199
    0x61305060a0b030c0f04260120090d150207060f060b030408070503070b01060906080702070807050d05070503101e0e0a1101023a020102090d06090812040c0e01050d020a05 75
    0xc0c3d075180c440200d200307845140f8070a50590381c00709010441c0b400392003d00d1f880c3c1c3c2440d150784a86802460741c050807600685002c03014144200048800c0403025005040704090080004c01d44103402d40f0f40c030074801d02c54040042c0031940003036954100b200354440d01200d00b146420800c601800d040003614584400b0b0710241c011035000c03074040c0401c642001210f813a244c0c0700510003e613503500c01c009021201c0500444000c29400c2002450507403002078880c00f10341c200c0c0000d00c22146460300307100411804070000e507102e014480020641e51410401c00caa4000e075154002601c01d4946030202c11050a2300c010044070341000c1313072400c0748000010041b84032504003c84900020b41b440c0182d142c05002c04800401e4601001c521620070b21300003020624217024600340c0031004907001d04a08031f00c156010107034003510250420001c01d699920003009644201d01c00303071400e01031402c52600e442044408460020341c80704148070b4500c642c08454010003060b16103941c0e1088545c002820705889000c0e02c0d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716099694 1250 716098444 716098447
    0xc0a060504020d060c020606130c170606071a090d020d02071406040302100e0a0909020d080a020312010807080d1b141e0c040e0c09011401200105061305060a0b 70
    0x2030540d580c0f200b101c000c0560200081022a406240194841c1012903440348128803a2454642030300e900e0141a40136040d80ea02c40c0b80340c0d0f0907140c5040b00032101904075608200d050040d80c000850011248103400440040000c003444e00380041c501d03140e0800c1c4403508540114001c42825038001615106450170000101c10440e40320000c41e0413402a580081d602c60b00c10702c5d62607440b13608030211003058082aa020b505642c0c444070b215003528101d20780290803074141c03962035011442000c00707080360392114410f903031030908244210401140280c1100c403a0307811001c0b04001d8420104000112200182443c10b9038510100d01500727a01070140c009800d03581e11500861002e502407202d01c9100c40740482e000c0039030714007000083d07840030313034440700c1d802545401c000003844040010392030b1203154000c040c8882a828450040c509131003054980d4103000080c03403645421031034084840c0041540074000211071800d2010840c456640405001800e49444140041a01d620340fa80050324500160385 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 716100944 1250 716099694 716099701
    0x1403070507080d2c01360e070507030c050120030708090111071104110a0905090c090d0201050c150a0c02100504080427021801080c1306030b0f030a031e050c0a0605 72
    0x686a035030707146d403e60f01851080d40b100e00f0400a94840340810081c0c5014110346240c40b5040c2000c048000d0340d54102248041c81202c0c00288200d000345507140c810310000c6160000600d01941da47c1103070090a43c000808020003407400e038070911040d031080c070740402805032419080401c1041d00c916000a40710200c500d03400c19890b162904900c3d40700311420302d5544d07a800d07002c100411645050090501c02c408000110b242c1c0780c2503070152480d540c0c00500301c4038030550729030055542d580943c52252250003007041e209080e41c107501426101c0ea06c2e88001003a0800481d20080c10004200200103815107000144004900341030182d409442d81411b042c44544100382c0d165494050301e070401d500d10f5000046000f942621240490303490f03102a02d500240d5150001c61540c039010f9800c0b1900e0448040307004116003407280d040038000711800f500c820305c0004002c0c04030381882c000c03440c207601055412442e0358800303800c51001041c40c0d013140b03400360805c11010304090301da081070390380a4281615580031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 716102194 1250 716100944 716100947
    0x412050705060a020406030b010201050402060d0e071a070c0504051b0c5d090105041e2904140301020910020703030206100e0703091403070507080d2c01 67
    0x100c035100d03a0031204a03520703450700c021800301951040c05100b0000303081441c070701c240394014040c00307000303650042180e42070420000100006000390109501544540ca1001880d807a202014107101003510110b07503654503072810f00c40140d0b1829804240203624013820480017540c041511100301e087c0f1b0210907941e02c0030303104092901017120900d0180c0030244019204e02600805054002800e8084154234200c481e0582c221048140307801e01644412070454403082000d4000800c4400d00504015041903100d801c44080c001044445180055441e0400e003e034440c00c42c0c05040c0e803c100e10a52075429078007281d04096028920452544946000c06d400550f40d0070340641c2c00440d00544400800b03e10568000c0d42e40b44c07a4801a000360040d80c010400301c04034020404140c84014103845080c1c0caa85004500074903141d03c0640304101c01c015194134070141800100b00e042d004d40c00034000141080012402c044902480800380488101e90328203401d82c00d084945082e41202e074144840884400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 716103444 1250 716102194 716102197
    0xf0a080910060e040b07050906180a09050403030f110f090609030f0d0503040b01060813030e0d1e06050604141602030f041520070b16020a0803030f10030b041205 71
    0x1c2944600d0a003600403e120f2510450030344158003825500360030b503c84030790603105840740440242c0c200c1400c0202102d140036104c6040d5000c07602a2829580607a240003040c00c6940076242103000036101c220880080d44680925000300510882080c1740c12002a031001d0a40b2515140d240907032004503140009a40602c4414010810081502c490001070072008003154021103003100d40d492500d00114502e441040442c1c4182c0c0c184611104400c41500c0582d1090510000d00e17030301c01c0070107000d60000f90301c801c400082684d075441c00361707044003d03841c0010036a100280900d008518100140c200800400c510350f0b002221440480400141c62008034114030a01c0990100c0013000200002d9500d1201141c4c10520099034132440e0111914449205400404c81740d00d225074854001030005030800401000d0340d001d080840c16140400ba404a80262010760102a03143c001004100c50317010610710041c0d0181401051f0741c100e5042d65280510340c0d074040c101802d024600c405070000140a41c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 716104694 1250 716103444 716103463
    0x24290d0804080a050c030616023403110a06020a020a090510030b190501060503070212300105011413030809010e030604062708031b070212010902150f0a0809 69
    0x2c041c1d03003940905091880c1d88810352000caa00a1152070700040c1311201002944490a000b80c1c0907144400d805501e08011591110320b068090340c0c140c1c981003010766000c510000852090126059070307c8420100f14880700ca0303611040135500003664400044e55030f41c540d2400d13030340c15030b00003d178503103410310000b1441039990002440240440305020b0014088041d01d4400b49100006015a0b03032100d03011246800281d40d2040035170310048014048111070f0028124520f00707001010200780c0c1104c5242c0b1364190421400f06c801d410300c0b005010300d50340084810350026040120600e02200313400c801845004500c07014048020200d120061f070b0303208882040d4910001800ca0b1400e080609001c0b006000d0a58004500c0314100000e030045180c001000710700030b80080070541513903108000c11440444001141002190401c0780307200590f904160001444802c00c00040c0b210300c1841809040b84003103c0351000350005001c1906908141030072607880b8502da00e0012010307240e14036120320b02070216 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 716105944 1250 716104694 716104709
    0xa0e0f0619060e010611010b0411070f140d0306090e0a0507150e1f030506031b012102040f15050906030103060903121806140708040b0403020a24290d0804 68
    0x5100005003181d0201b14401a058031500801200030b05070100011580c0d002248998010203100d8038001c03c03a11540843ca04d4012000c00741e086005031b111701d090855400204010a03900e0070288a841c400740b2580b05c0110202d0010320340c00d08907441d00342d5500524412220380e40c1d9031164210071b45104e54181e030715866010380a25040040b0b0f02044840329205080d280c0041e140c140051000c0c90000b409102400424140301d07002c00c404401150350a032403160500d40702c0e8010354810340c03100082c0b0080c001803c0b9140107502036402d010780b007009080c0810801c3c0c02c00206101002c1c080d5aa041100e044035441000007806000320f14056030300816107985451094030707000c3d0341d4001e1000c210885200510640707040000100c81101c0004c886026604400042c181c980001d00144204c01c1ca80c0d0014000d00403038040d4416030f41c40f154040c10035510010700002119102148140328001e01c01545142c14448080041c83c00202d42e10582c108800c0340300e0380400da041001c0c0f03c2a1401c0b1400750000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 716107194 1250 716105944 716105969
    0x2c0703210306092307020d1b020307120c03021c03080f060f04110405010e010309080d0506030f010c0207060e041a1314040605060a0506030c07060c03060e0f0a0e0f061906 75
    0x203a40d455900385480c14103000000700700d4000690317070a02c003144d4518104401d8548034030410358400c81402c0c03602031711000c0341c06104076000864041c0c884100307481081e01c280701d4080207a0642c4180200402e04a0840403e11049454100001d40103120303280e2003132892003240c035955145400249500520074000c0c1d0820302d132180c0a0140c0c041c501c0104160358003a2034040600d40980c00440850b04ad104014243d5a1f0034400d40342107030720540000340c2020006044039000c501030f841c0503003116981082840983e1100c0302c100031080c2c000c05401c0300d018046504220040c04004100c01e21500c101440344031341d095021420400e442507002c6005840702031041d680c80d00d0b0a03d44140108030581c0d00f00c0c4100d031400c0f00002e081c60a0790489200c1c480c1c0c2c0451900340030480da00d134405070010002c03800526031201000700c0d040034903004151007110b981c150311800b418242c500c3c504440d5407071050046900060140b040a41d000682c2a40018411140504400340125800020302c465001401100714 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 716108444 1250 716107194 716107211
    0x60c030c020f150d0522020d080702010203070206030c13060e060a0e03030c0a051612170f0d02070b0f090c0f06071a01180e030313060b132c070321030609 68
    0x4a6a2181e4406d8000002c40101a02c0080070709552020300b5000a600640442c0f000700011000b20141001e10f1041c01100d0628038030303600103051500110760440c441c52001c81c0240b8080c056085203401881e031400d0030300d141c50040780440c10502c5030f402580280301b00c0c0c54850100d61020812520144105c4080d19161000340c030f81980ca4549101c50104e503191051310120780511006030702c08055904c00078026040c0b0542440c4040c540280e02c500808003000c0c0000180c95013180006c006180c80b811000510740342c118015200c40102512140055011088107a8681c44141c078148212000311800f60301d8400310702d0401021100710041c10006041b140c00010030520b101d801ca004051480c1040c0900c0f03041e41200c999a0004556144011121410031408101142d1040c8240500503203c107081c1c085220000302600c0120150b80c0b03410125141d02555030440d0741e10309035415200805401680e1554a80d103030204e54a020328180d0301d5955058026450084e40080c00410303c61000340302810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 716109694 1250 716108444 716108467
    0x905090a0212090c06121503010929040b01050d020f0604032102030f041703070b07090609082409071e060305070f121e05010f080106060c030c020f15 66
    0x1007102911140007020760001c01d40c0414041030351141c4a0015020340e00f0214503031b41c001c800140251104c00400030320094070140d40c800b0b0113440071050080d03a801052000400e10213845800421150108007406414840007c02001202d81191070441d4800c1d242405800003520301d0036003111580c0d0100001400208011013100c40029111241c81403800388084020241c0c1c49210762281c02092030703c200405c0c40b07618040c0702071300303207107084602100d0901d902a80e42042c0300d40c0aa8000c0c1c0032445002082200710790010042019080f41d2010704441c2d0010300310482070b209040500e4240301009800038005180400002e0300610b4140b0b04402e00c2118240c0c0355103140c1540c001c41d00007a09110000f80e04a006d0721912405100079507851140c0c0e02210203070001040c01040c2c66081c42d9001e40300103081540c80c00341c9806080032a0410580c0b51824409508450041e448801400501352030303140401d8001304c14101c62501030b03441103035200c00c2c50300040c0f00b074002c604003000c41071001c04c0c5c41d00c03c1c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 716110944 1250 716109694 716109697
    0x819020a03022808240d0c08100605030c01090602060f06061903050403031811121e0c03070f0e011a1c050412030b0f01121503050a060b0d0c0e06010905090a02 70
    0xc03c843e00e65a04907100d10b0410044000d04040d107240316044509181c06034205420301010a80c09000420301d0b49490b100310b18103120b44400d00d02c00154451300305001c54541488001154542420b02401f0107180c49400b9483c0c21004102c1c0360928040c000003030841d26541c04581d454216400360703842c08103d414001d402001d05840640019240c001744659580b050368400807002d8200c000d5140d408800010810100304084403101d0070b00070030500001c003002c520141201130356850094880000c002c0241441c02e0b050303a02010384900368030020400d0000c0600c83c11f040d58800017801042911086461200d031184c9200c1120f818081016940360030056403107a801680304503c0340c1d80c00c1d00800710403070a5422034050190b1006078103c00006940c0141900c0303000b403ca00f04003040000100d07a041c5c11071041ca910944083e0085045031040204511134100c00100c00c80c0c0c42d090300503450b142c1d000588140c3c0550381c415200000404c070343c3c0c0c0c0503000726001010014a01c07403080c034001c80341c00007a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 716112194 1250 716110944 716111017
    0x1203090f09092a190e0c03010308120702100203100e06060712200303040c170f100906180302062509050f031504060e070920130f1d070819020a0302 65
    0x5440d685c0020a140b03c034540200d0f0704a9820401c141d0601225550b01c4140f03541c068114001e5100b1140d003041e01051500103184901c603208105249246020780103c41c4400003400032384141d10400992000802d41941002c0c0713944203103014000c0c6190900607810b01040300060f448144004801c0100300511a515041070361084800700d40107100c400089603039203002000d1001c0d00d412a403a0301501c4841d9900041c80316010b0100894003002000304801c030598031a80c03d40041c3c000204010f40e00ca007110410b00d0100300040003110204410200400b22949801002e114086d0582d00400550341002207401c015000c4014101d141400e282c150000c0c110746240044500407840002010300c82c40c0300c1c12501001000344021140703075407000805564814260080061481c1c030002c80c003081c4401a000c003812202c401e40300d8040303a1080840070320b00010b01c404e0400208504005c841d0b9510103007076015051114000da1540d01c0304c801034011340212482d0816110f80d8807584001030f410b800301c1010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 716113444 1250 716112194 716112209
    0x1305030705101a0306040308070e040e06070f0c0c031b15030e072c25020c1806130504080c0a03051c023103021203090f09092a19 57
    0x400d1284481c1d542c03001c9043c0a00740c3c0c5604005c0c00a404039000b00b9000d071b031045c202e14025000c09040c0000904403010b8011103811035015a040040300740d0030650381085005135081100f01c1c2d611982d201c112030900f6010003052410840d420030b140c1141412608054601001902d0a0b1100d00300010000d15901c03610032558491180000b40d50246403000e144000c40b00703885480c907040290048a10400c0c00f40940d02401d0030125400030310075000010058014036940a409840031020400c58001040e0850340300c10103460007805034175942d030444130201d031803400400300c0c9507555420116030340d002e80d0305034070f03890300030440b40104240c0d120303009040703402090034190070003d94126040c00324019008500310103c0311405500b15036405000507081c040c94044a6516640c0304da01080301c44091148500e0350768804956a4641e2030a001c1d8052080c00c103942110040c0f404c80032140e5600c2c003c40f9090024000c2c040b1034450501440c215040909010f0880e600030320200d40d40c1a03803c3c500c0e100e0b20f803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 716114694 1250 716113444 716113451
    0x6070f05070b03010f140315190501081207031b02281a070f1407060917120901030b0f180708010902040803120c160506011503090c030605130503070510 67
    0x240000310300b01620305130b95080c01c07412036150604c2c500050a407004942e140d85849013540c41e48042d0b00c0250381d06d100300003030b88401030740103880a500803d540c01030f0810704a54100c02c40c03608011021100385d42d04a80c01d8984800c48600c076403041040340020903000b0750840700d9015003055008003540007590000320310401c050f80d590b58440c080c04415000c054030850748801c105000105005502101c645030180d40341204d514651500b440c03038048950b110102040d160328042216030301c00d014075602c3c2d030800f90207448007104942e40d4107000d10514000d541416560000c604160315200e5801010450282200d1543d240201c1c000040040c1100d0103000103070072400200c0e100b01d03a130090f2012150b20b03130029400c0c149042c1002d004028002e14140800740c05015141412221544030120b450184d0044d00701d55040840388000541f01c000c0c1f210605082501c80d000148a00d05030324202c1c0d800850000c1c29484490150900000603040500140300100346c050501c4804140c03025482000c11040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 716115944 1250 716114694 716114699
    0x10512010b0d020f03120309010504060f0b0a0306180602030f0414160b1e0d0c0206070216120c15030b03060601081303080a060906061115010302030a2006070f0507 72
    0x98241c62020071034640008840d90ba4800509004050458403100103040d00d003013200028002400c1d81041b619850141c0d160000d0205004a91203070304800320300b0761810b01c00c1303200c28400305550300f6240c80300a204640d60fa203c20749885a1007800124541d00610940d0b4034108040007a461400c04c1d5400d40c0c85c1507528582404c01c41e00040c0425848000c0d640c40420341e0f203054529121504241e070040b0272001c894500c0c9500301d0500c0b00408032500e91250016011000080003482c208008104034155403192191810b00381004850324112020b040c0d4000c0e581216142124003c04640c0c005c542c0342c4ea5542e00719041e150980c020000a5005804450b550f40d41d42c001190924001d951803d04080042d00d8540400d2040701c4041d40610007840210713660fa135504940088540340d502607000601545180543c003501071010740c0c9070b03a0007424a0341d0a03504540011f6103030455158000c15045144404d402d404020300c08280305a0310081055407180d903241080c54240044080c00c0350240144d0601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 716117194 1250 716115944 716115979
    0xc06100f03050a0f02030a0b070809070b130b0d061e081009030e010e03072601050c0403170d0f0906050a0e15180304030503072a030f030e010e1201050105 68
    0x10840e900705000300052007aa8841c2c650035500c051091b41c0601405080d0408205440304c000d000300c0b400c0d079072140c1c00e10300509074504000fa00d400102c01381074201301c105004081c8904010a868071101c6d100e69030303000c000b8a0b00c024032456010006608040d844c0e450455000c8105008481340442610690f4040c00c071042e0444010940040c00705403a000068019441a0549107081c20083e085074441a203d110104055500060300812540c40d4a8505c540010078018150003514102056003050f046a5900f844000d00001c0100d6521011801d08a01001c40d003020401d2502c03000c00300502c0c803142c2803403005040201c481c030312032a04140000003148000200114804200e044031185511010301a651800c039018035035105100038000400800c90600090410b1403040e10011002ea1641c4051100680e4040b105898102602d00400104203030752280400564546020300102514a0040c2c42c1d2203130424030703603412181085100150200540c0018180d44040b81c2d146880701d2060b18 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 716118444 1250 716117194 716117219
    0x916211a0a0e09030a05032a03180a0f060c02031e040509010e1905060109180606020f030f07030806130f0519020906090f0301091430091005040b0c0610 67
    0x2590f40c010f9008024020301640300700302864100310043e12000b2000c5012013080e040540f01036681180c0480003040c0a0201700f00f990ba8001c3c09841005040210300c0b40c4c6420511001948000c4c019035201c89825500c58401e2040780d60981508180b107440c01a482009580e42d0824017495015203140300011070b0045008002034031072110ac074008642c92810380e090310040d2101505103411302603030410110b50300e1014440000c241400c103e00064507490464004e10780880c0350360707205564108100c0341000821034000ca512441c0c05041040c9907450f0300001c1020700d01c0041200032024500074004080c070700700750003040c0513951030008481c1c990b034a00040c6049120b52501503602000810254086082c8038804031389100004000044083e13484e10340e840419442c03500d0015942103510003e11000b00d800c000103c1060500f004250809480b100174628424034414a1044010000e00e420303030383c460000c8401030f0495156085d100c802614100c1d503034450640304202d081000354404600d0700181c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 716119694 1250 716118444 716118451
    0x306030607030f0e030f070611030c030c07020a0509010902030702160b04060309020616211704020108040c1e06020606180118021306110105060916211a0a0e 69
    0x401811007500c41500560080039031000b6580b046407200803c0741c030b1a0090002d00703130381c910003411b865030f864071843c125048506191400b02405c0c410701c140100e002c6401d00743d80c0c1c0203a044051542d54207241c000140e00c1c0038a6801300764082c090000109081d02d5a4014500a03540e540844510000c0955651301640744e900800e00c01c1001440204151886500300c2c841c42b40c0041c100c2c1d49072030300740380e4241c04108428a06642d184980348040440101c81d580d01e03455000d00340307020070080d01d0a511415014170060406410015404c0214040c4650105075400411481c0ea403407010900236071851060105522a03440903000ea0f600181260803c010250703007045400141c0440384e824120b16181086190003c1e02415509010b03c40342030440185a401600c07681d200c0008040142c0c0c02142035032402008079024080c04410710400740c00301c62200f21400500d0038041c81da0816800c48010680480c0803e8011a0034007059075010611000d0044103200c0c255050f04145455140701040550280c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 716120944 1250 716119694 716119699
    0x515031c08191e02070b1608152809140f0a022b360b0901150306050403090506121f03020607121b02030c130204080d08010e07050306 59
    0x40e000480506a928420b42d00d4212900001100302d03402040c44800580041082050b81e0f00243d1002441203200c0740c0d0354405980341c00d4a00c00414504010050040600484a002c12540281401d517484140449002c0c81c0f8008100d8490f00341c030b40c0124051040d01c1000c140390b2800702c1d00079400c0058240e20b44070b0000d58111039629141c0f00300c154000e5210301d10900c01c040da010030842c580c1d1503450007480403100a1001048540601c0c04035180e200b0404600d50840310008001c0601401c0c1107480d40815401c410340100756901d42d501c00e03001d0900e0300034251507403901000110420402d984a10b010340d000340d4030300782080d4032141800803a100305003001004d03d0400300081c0000820070503107a45100c8010030701c0500360350fa9003c070b90342e80c0000070100d80c2d8030314081c0e4000700164881925425010407002c141074184064020903242c807100b038550390250000075014880418203070101c400424442e0120b50300e44048070302c01040c0900a0142120724828040070402c820f1044081c1c03801030000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 716122194 1250 716120944 716120957
    0x50f0f0304030c0c06090e0f061003090302031e04090c080709031106070f03121a0f0118050d12020f030304320d050703020f0601120b0a060302040515031c 68
    0x84184412040e00020700032410861085480d0000580f20035184c801000c607900e078004568200078030015000c0008184c2d07044095900c04010a5540d2402c1c81010042103050000f03015589060480c20340c495542c00c03281c0c010711280035080009504005004a400404c400c01008010407000c072604101692241e000501180051001c540c4507108508201070003480750f460400d0682d599021844e0110040c3c0214113009003107680d1130b83c0741c0a440b6890140c007094200303500f000e0002444400300c00419034100a00c2c5e80f0200341401c00440b80784080c10004111880003426842d0417140754901c09000d60060040410800a10b0000825240074540c411206400140d1244466011044c41010302945c0d480c01d08610610b40001c0c00402c100703c0503070350ba00e5503c80c11414080e10300202c099480c54598450001041030003e035001c07a03583c41d540440310055540300c0c50b0b20b00b00907044540000e03622624010500100a41d141111141c00342c050703013640c1050441103001000c00801200e24808601c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 716123444 1250 716122194 716122207
    0x51216140f1302040e040b0105090612030316030e0f010203060130020702040213091b020a11120a0b10030b060303090306010315020d060807050a1a0a14040302100e040c050f 76
    0x1071a40d501c1c0c2c00c04031074100c01424a5a00c810009034405e058800343c404c0c0c06c030f060060006042c0424090341c0072074151560032522905003541ea03038a120081c0412500700b81c141e5413035480741c03082e0012007042a68004a800300302c05043d00c18000d42c81540d0305400309411321118100c00d07003a14000542100c0501181e04850404042c40000e5400201d0072030380140d0801104c500b81c86500c110f80042c0215882c009002121000c0440440d207030000d401041d5805000e6141c0055602d041c1c10056020a480d0b50905883d41807a05280140422000300580a41d5080202d031088105589049034000e8032401d81c40d84410052540700d128800a140d090303044480188045102c44199030b0616804a800510b0310b445499084112070980e08078201c543c1012108104c9450b0250300c04014000c0101c0460200c00e041003400703200d01c5074000c034800b4000e40111103400d006200e402d840040d0b40103040d1408086003940c0080c4400001140180710f54078152150300340b607100b00141e41803d1003da00c0c203841c0c41c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 716124694 1250 716123444 716123449
    0xc02010c090803160f0b0f040c0812190c080c1515030a0f020f06040303030204090b0906090708090a0b0906091e1f0e0a050607093c051216140f 63
    0xd00307810240c03440d100424222000401b00241d00f4410010b00150b1301650400c0e06d42403043e10031a50008045612029551900103e03030411103180c070170000083d8024101000b4152004084604080e0500d40086900040900c000c034000060401e4030030001d00c0d9a80d10040728008070f83e90341740190580e104818103000120043c9140502a0004064108100b43c000000380305500039041280082d40100e401c00c6640c059005540c15031b0700031540c81c0315a16250010480d6000300800213400c1103280c00c0443e021a00030b002058105400181080c1a4030703207001c043d5964442503543e10294415115581d118031000e03600c00340e0401048026100e00d85880360070406c9070682c824082820750f40c1d00c10182e941401080031150051044000c0c0c01310b4030f40715001404ca00c01c03036440520211510320085401c0044003a024420342c0606140c080128804d403022501d4440c940c010507040016102e040150f40c0d4001882c81c100301492424070850b0f61900d103030107019620301c41601d070071850752800a1040d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 716125944 1250 716124694 716124727
    0x70606060f121517071406030c07021c061401030b06040603050c061c050103260307021c030e0706080a15260a0503040603020403020a06032a0e12010c02010c090803 72
    0x1481c10064032031085880b0940181001390b03802003101645e005050410000840343c09051040c2e40450303590f8210320b8844a031b1941c61007003e000031b1080841103140080102178081c5203030482d4029004004500780320481d0600d0ba0000e001c01d86a44041c540040c0251070540a5582581e520030301400e50148900148140744d08000e0b007103800c42c241102038554a44c15841140d000f036000c0c3d0102903407000d1104485101e81801360001b98440006c208100f002da4000500d059040c0300c003440e41c1c00100d00d101c401c90040031440e81d14400e60062160000300782e40d0212500c1e0080038040b0f000c00c0310704c900c203c1d04100d0312400d219038500c003103401c4814120000c8840300c401c0300642d6002900d040c0582c0369245070440c4c0c0a50044000300e80d020505006509126920b41c01500c13650070308001c4450707048000120b06544554070303004400b1070551101c50a101d401c08d00036001003c1c06c509a40c045149005000e000808980d400561800c045069054480e4a2000494110388051403901e121000c4c0c00518 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 716127194 1250 716125944 716125961
    0x6061309031d12010504051015062304030516030b0c040e06090604060f0b040f05060a051b03190305150103050609041407050907020a12020705151c11070606060f12 72
    0x418000c0140320903c400303000751440740e4428009000032089115410b411950442d0b4201c005901c11032003400440d4000340009014a110f80e10440f86804010380414107120743c0d003005001d805500e00100e49050303081040010b0300d11511040d00b1036542c0301d51102c41030040d841003180b5000013002240701410300380940c40d0001c8001d080450742d5602d446040001c803a040d40440442d80f00028204030a0500c00e115038060708003290b100346400889040200a40982511a062078003070505111644c13208200701c5100d101040c150080401d00f109000d40100022207118403a41800354032824136611a100340c0340300f008018104100b54555884034264a218200e02c200c10384101c0c20041480e581305034541d07201d004d150f801400006510324240c01c112911070008402d5501c40282800070741c1d90078440704e455800c0610081e8589640e8504644001004041d0210072403400842e60100c04010009100650242900340411955041e007110400c0c10071000350000342141d03140f03200560851b00800384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 716128444 1250 716127194 716127199
    0x3050907120f021002060916031203020c2505121603080f041d041401140c071106040306090506070f080a1a21070b0309030405100903080c06061309031d 67
    0x202d503050340c04110b40c64400d0b00c401c409680301404002104030108101c18520581c01d030241c4203145180da5042c80b85a80d032602c0000d250700440e1000568104100d000140084c0c0c5102e840f441c501c501440305900c2c2c00d0f00403035004d201005215140785200094044030090300b400200d6003035145482d988070f580c11500340403c60680401c400174030110704290707030302143d820b184500200d410b2a203465420360008020080c980d0b41800351100d05c000f03800d05416131041c00f62188a503135003003610789644114140e40055503c2640440d021061000350752105074554480c80c220b807d25182c0741c45c10f56100029a0155002610220006041d4092078008000c0c01d88403070f040c91240c0d006603000a8444166a00a0b1080e0075441e21030941c0c031108000580c010310301c04403590f24609016503c42d869104038080d050251134004404a04107200d41180c00045411136511525122a045075607201c0d40e054a505d803050207003100f03d4144502911807050300320340c1a1501f09111102011150b0308140c41e62032540d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 716129694 1250 716128444 716128463
    0x50702150304050705040b030616050f072f15030703021b0a0b10050a050604050405100807080f070b040e040b06011b1103061e0a18140d0f0305090712 66
    0x1058500c140095805544a030002d026820b041c04244800c980125422510a40c050002e04c9034148401060101090151030070b140c0d1a4651004c0400e10b100300c51009001d43c3d108141c0003000305a1001c01c2091401c60048d0844528845080220410f03150701170034145041000400c1103c1e010754000d116a034000c400310080300e50020405d40c100400350105580c140014030070014958040c004580250004660719008142010302140d500c1c000e0780915030117165241e0106402c0760000d2002c0c001032030842c080310303a1140c444030a00c2d02c54006900207805880742c114049540303500394003034800b40c44541804152076519901c0d0000c1001018000905200088455240458030309016101490044108981d181c601078181031806100400c0d104c105000c251042016503d0b4000c42c9801074440200402c01c031000061800251030b9065004042035201c1e03542c000c24000201c1c0c040d04000c07070394031610704441c02c186040d002da07407040300d04800030b4110310740a00501c00d100c1c18025129000e60a903c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 716130944 1250 716129694 716129719
    0xc0703021501031a0c030108070b0310031205040617071220040b120604020a050f03070201111c0b0d0503160606031e0c12030c02091e040c06090503070803070201050702 74
    0x18a100d07001c0e0003d6030400708142c1d10302c0c1400d4078181c4107900031228401e80c3d4070b19803602c2d8500e03840b41c45901412814100c00004500e00400d0140190007071500140707804294907008a0281c41c0d54001e10985010400c4881000380d44070001042510908088d1500100354524200840040800c840110700d41304481d118844c400d00030340064000b400740550110b56039184045200802d030401403d0603c6940100b10390305034154001e0139540b4014121488035220b4030b03070b000180d014081d400f165420580004c138400030003415803003035420181683c600c2000742540c00d02c14001031901c0d2600c05030072940204060684440d080c0f849840d140d0161000080c1152240d80300482e25808010312409420741201503c18420300d4101c0c2c2c4024024800d040c141401241d0300504400d18401010b07100c1c103001000940002c01c0d0300962006850f40038041340c020318051800c0040440d05004440000e6641100851141000181c48080d600140c000b1800e103100e40c1d0044407107502c09202242c01410704000d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 716132194 1250 716130944 716130973
    0x70e0d080c10020903161a071401050403050901030518071a160602040807120c051c0813030506090c010503180111043b13060e0d0201140a060605030c070302 69
    0x3604651a54560142c4d1300c1c04200105442e001d804224484c0c00c202d080f00420803024502500c0c2c2c210301070035608a448450324100f02e9690060500e0514442d42410204802c050b44100100483c05090301c08202d1616801d111002c282c122030307500c01d210b0340700c82004d100141480c0c0743c805e8500e4803541100d16003120380b440904501c02c520021a40349401050500040d8428024000034240f20309407201084100c0c6c81d100d03a1036032940306203805050042c4c40001c003602502c072804038040d000890340c1d50343c4081101002c030084540c4401e9881c2e000702004036079196000310b41c198500c00160f544a055803241e014120081040381c110848665a03290946d4440c0142e0002d00000c11070103038004604140c00300c034151107442c5040132182c0200846d1044d0455155940c4041d00708000031351032071008010b443c0810003062240034448182c031914420100c4180c0c15084603244800c0360371000c0150700d44140e40720a80c1e01c03601270b80000c1030060000540452100c000f4011950203841259204da001c07214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 716133444 1250 716132194 716132203
    0x6090315110a111e07030b09060f0c0703020106091112010f0812090307080a0b091b010c03051c02030c130e0601020c0907050f180f030c03060a110c01020a0f120203070e0d080c 77
    0x3113600d0700c3d4225440070018070240d003403500d510065023000380247e8a0f200444051038000244600b010348408140401498400d500c05e03005000c00003003c2050706148c6249801a8120036110601c1c01600320012855107281c01c0c040c0d049030080c0005000c15449640c40d1980e9400c102c1d0619014807443c1070002e042c6e4002c100101c40c00340200c00342c07001030600e0040e1508010404814100c4000d101c0b60340781c260f0740d0144102420350380510780607840d80d08441003943c140610000329203c050000c0280012a800440101011300107004100102a81c0e0450101c21400488100340503170401ca043e0305440c1842805903522854a203015840c0840e6048480156004103011511500c0e45c3c810401c514100208400c0603003a084000701451013481001a98520700145000e0b0000e80720740c105824405280c088c1e418494052000350f403910f01035a8010003414888a0f03010000b80515000d00c80c0d01110310850307019030403582d50100608000000c0c8280f11141c040300301d035250402c000351540e80320f0912 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 716134694 1250 716133444 716133493
    0x31603030b09010608060306040b0702150103080913050c0702100c05060c040609060e03120a090b21130807030c080706052a1218010b0a06090315110a11 67
    0x44000aa440385141801142e0340c058110b0340a1040440a221301c40d580002c3c1260301036440758800003590784a0700b040f0f0030a80512441c101ca14000d40000c010040503001400703002009946c510603072100800c03404261071050307034900c00f0780310100322800140c10000407848001040d810316405000ba83d81e5580c0c6004801c0315400c3ea01900410248402944842214000e081a24000b0032008040d000251981e00c07442c82e920403a64005050880307a07019500020082144041c10b649038408010803034002c1c5030729012050500350341d40004105200d10007113460741e80e4024403014280b009556050b40e0f21001c0800a95050100b4840c250000300c06008241c407800300e071101501b83e520103200521468182d401c1e040c0000005000224034a400520101d83c0300810640b4494a00c80f042e01050045c00007800c200e80014080700041007807034100316400101c03417040a5220141d410780040320103c0d14800c500068400041001c00415886454042c218010130026500180c0616400704011036141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 716135944 1250 716134694 716134697
    0x61409060c07030c03061503110d020a150504030b0f10030b041e05010c03050a0203150904020d0611130504090209010b0318011d1005040308040b0c0d06060e0f012f031603 75
    0xc1001740104100350060400021020000c0202582181d6580c42410b40e034003103a0f4040c05071000303034009556504c42420020442905810325030050b1410081c40b03035116010580700c810544000c1500341000d05445032043c03151644a08426003165625001c80002800c19100100d1300115440a19120040c480c0103500c68000000c40e40000300c00a401e0f2680148600e002c02d106008103c40b860580300b20090120b0304440c0e1645a079164800900e10f410040d00240c582c1d4601900700314074001070801403100c0045e88000e4003105503a0010070090b07c528a000940010445004005140012000d150018100300712519070210100b8090308480007404090400f10103841d110714168800c1c4070f00b15080c22590400d200e030340390a84006d4405d00002d04020a080305000002c2c10200c0783d00103541130310721104020f01ca02c41d40c4c0c2000503d01c1c0789040031380d4890380c80641920015800340008040021b5090384c0c804400e110052050500c6d011800d1545082c04208906d048116904c030003d10224880d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 716137194 1250 716135944 716135963
    0x51c060807060f0f0212090f031906060602070f080703060e0109060e1f0608061611030403030e0a0e19020a091d10080f0a0b19050f0105040e07061409060c0703 70
    0x26000c0c004d0140a4506a40c819900208400d0241045240803101d00201c01da0700315004c5100c84010a01d030040e03100c183d00c0f1102110403124201304183e04804101c80d00b81e0b00311400b031625413100004510b69071046442135880240300700006401500007014603a080000080c0e10480c2e511240305072119241040d040d134101e02d940030300c2c04004d60a6600c40500e01c210420003181040364407683d643c1c014000e07850700700c1d54502c449100c3d441003414025140955007501d4585550349005400c0c5d0b02045020b0b4411300c1c1c041d40101d00c003402010f45034400c008114202104941c0403c4c104025401444c1d04ac080004260000c28088030174001d5594103202140380307074010f00c4c2904010551404603001000e0316000100d49058070303400080c076005000d81014100d132480d180e0035803020801031102204507034981031008004070f00c190160564100c400a80d000c1c00b001400d44000b507110003680c080e02010800e103400d01c40100b0f803000046c1c01d80c00c002400d005d141446800205141108552080703c44002c0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 716138444 1250 716137194 716137217
    0x103090204231b1c05040804031403120705070f02090411030d08150409030816030f0903020a023a0f0507180e0606151602120c04051006051c06080706 66
    0x20700003d6014805a441c80260a108401d00e04500701d4038102c3e9940c00140e15000418180107009045038010b542c482143e405620f00d000c9459201c0e00103001c584c107031500110020b0742d014003410850b4450f075448030713481010461550800c9810300d0701070700544000f40b2040c403680d41502d0820114003071203c0c50700d82500034900440c2d1119650383c001d0b142c81c022403d085149000076004503560b46c00034020505480c0c400d00421044000b424004e040c11078103420003200d203050503004940381c98103500a0340d0348100e00c4007002c400301006404085126420340c1001c0c2c400200d240380c2c4500f16802340320b4a415840701c2d0454840500c1e001c1c0c260040c48443c00404135083d40400741d841014401810b68000d00046d14190b80029520350ba00341c01075070300050014820070b010540c882e00ca110030b07a0080200c04800354076454283d03943d07502c05c110b6008910b4503000c156179901c41780041c422141c00c0c3da074107403030100f0030441c01380000d900c480f03a03401207601c2d40c01c0800d4110b401c6c00f2805c0500820381c1d4a191052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 716139694 1250 716138444 716138461
    0x303060504230c1303080f09061b061003020a0501050906281815030e0a020a0b1803010b06071b0e0c091003020c0d0e0a030c0f08070f14010309020423 66
    0x50301420740c410300c400400500e135540460301c0480044a802203c11903c90380900174003860703840784400e501d9118400142c4a40141460084201443c40781403c03a4550b5541041140414100307010203503200d0300071481001950320490080500e80c801030181800c091016042c00b041180c02450b050068140340c580100696003c1900c225014500b480010f40f1480c043c8405050740ca072440404c20180c40d82c1000b00c681008114500c2c0e003039800b41009182664a02c01d13029140c200a2505101c0c00d00002007401c14038050003510741c01e40b8002d0440d40341c004150348100f020032450440000081c440c0d0300002c0c1e205901c02c4400d10810041004542c2e0700b0b12007081010300850b00006400741441840300c518941c070001115211081d0790708001040b291594001105035026900007400300702e81d0340000c42c109407440540d008640054044440c103581b1802062800e041c58014082d6405210440e40d02c250300ca80c2112000e9030000d8000181400710b013041c00915841c031031110040c0140c03c414856402c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 716140944 1250 716139694 716139761
    0x2040501030e062214030c010f05060f0f091308030f0906060901140906030709020a1806020d0c112704020907030e03040314030d18030e03010207031b0303060504 71
    0x403100043c0c01d4500d4200441d103010308441c030034001c40c2c260350700086042010901840c0c4690950b030b411030b5154105100d8460103440c194501800241c106400304209040c00071200b0050030f002086450714041a9041c0098010f00900c100071a000a0b64010040381401c4011401030700e480880707400900c1d101441e036140c020b01600c114056280c00300100001c00007050703014420300c0c0454904449481f1381000034a0700c0815004180035501c00103900402c0f0750030103820003c034003044000080041d5110004ea032210200c901110200d80081200310000b0114084400300070b10040081c0c0628848000f207440d045114501854141e401d00188415441d000595980c010418501030019404a0402c681c0b64040c0c0c3c40000c2c0040c0c3c2d8003a4440b00c4203030900c01d5506407107140404210056581e00104144c0380800d5060b400324080210175002420107000701c591013074240c0c40fa2075000c01d00840b0507840040b103c1041e003c1603603982000c0744c0c42d500c42c0942424080358a2454001804006030402e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 716142194 1250 716140944 716140961
    0x4050c1507030f030e0105151903170715060303080f101410090515090907032018040c4b230d0e06151203120a0204050103 54
    0x400000010314400d10030981100e641a6140c80c0100540030150300680140c240710154078190b500301000c006407621400c08904030a08102e40c941c0d03000068801c050740c0e0213810300000d040180d00c002400f4008a00d00001e1041600c01c0a07542d00014051800000f140c519400881c0005c040d2401d114403079902068040c0c00925109001c000c80e498400c800483e9506021513501034544444861000c90007040200014000606000b520803100c494402541e8054050140f0440000c00482c401521070b2207403543c1300200009c0894101d186140390f5000d600080e0010300d0504444109001da03071114050114150020b0b2a5070400c04000c0d0301d08001700d18907482e130030650001c900c40c1e0074840009250b0040d100d550b021072070f11801a4542c003101c0c10f05c44043e04070014072440e040c1c9004030001781c00074041c1840300c1c0c004020242e41e0024061321813005030703461424031455040c03041c11817070400b007a0b00f444603102c0226807802c1600c51441d00b600404554051003294040780c104161358050056003030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 716143444 1250 716142194 716142199
    0x2030f0a0c09090510090e0309030d05121302062703191a0408040302030d020a0c1a120c04150302120a060501051602031002030a1a0303041214190b04050c 68
    0x8820708403200240104034900c01e03051080d40b03c0010071854109500101c000c0c10501c0b42c1070118000225619030303030380c6c801e0001a00900c51011300216a07403054098a11840400c0070b401d00940b41d0b0701c080c494101c1090401e990250f010441007ca0700a40781e12040d800010150820306a151802054200007030762000340c1821980390280d4001035004010551410704040c000da071035441f941003001d00c600540e0002501032144220340e6022a400140010100703214419104d48540c40760044494601c55030346070451840144907080070728034410002d5901c81920084c42c0d04080e520300b00b20008400201c1d500020913800104140c000e0b0008038251b520a034103003000d202c8107240500080040c071030010140003801c008402d1504540c1d007840b005e1011115901c09640380d003442c19580b40146080e50503a5941003150a51071001d0502100392001c031404034082c0b443c800c000b5202c0c040c03040c00780048002039000324400984906030100300c000d586400f48415000c41d18151a003103284c188a01c44092 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 716144694 1250 716143444 716143451
    0xf0203070504060b1b030d02071b080c0a170c031c090801050f1f1505040905090105010b030a02130803210901200705010b0a08100c0c0809040c050d0603030302030f0a 73
    0x803e42c1e00c20464400c100c240d440008a17000004882d405d501440d8001c42086000149405c10300403141c203401903003848032100004099984050035514281b07450000d4120800c05810404034217110641c110242e0f03040d050314801d601c1040064100180600100c0d000c4003010b06000105074070050003c00b030b02c1d041c0000c2150b81842d10700c030740f64150010300c5011410400e4176032140e50284420340400070040712032404009040000007501c2500640291b900f0036182c08001541804140a8141224000c4c00594030f552111588103001e5805520104940600d10740e0004150208000030704580c070703c01c7c05401d40180303800713040c00750214054498080350307060120724120410a180d0081003804840c0400d07075200c103c1e2601902420740c401455a10102c4800c00040c0c0b00c00c080748101d103560302180e00304410b42500d04261051401c3d4070f03002d0454402803024000d0390500c0d5000440c800394a00303085013040b441061450551701a504200c00080d000f00500545005104013150048104402407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 716145944 1250 716144694 716144699
    0x10020306041e0c0f0e031b0a03080d06030201111c1404080303090c03070519182a02060a180209060d05030304031d01112a03012901030e03030a23040f020307050406 72
    0x6940e83c0041c00641c440d0701f420a14403071407030fa02c01c400c0c44000c5900c0840d180d1a10740040a0500030295480140d02007401e07a2200c084e06070010403c040f08217007c140350754040a20350000c65007640800c506480410003000003280707291080003c2e5104403c031714010f2411803502e03001c0c107042c60181e6000078029503415502140201250b1503080646004c8101c80c54850700200d0308401038400341d4291042601115524525091508881d84450000d0b800f1180e86888881101c0c2c00c0b50000140341001c07100c01c242000049c80c200d150903402180050800300301d10350341e844940c10b6500548007200803400884900e031458051f11500e018508007400d00c0c84010742c107918040c2d10f4104003003982c0204c034a41000c0100e291401d51070010b502030043c00800050102000b4442003059206025903103844040c0441072645c803e0141c2105c08042c90301450a40d203500050b2400350010f283c03104100b505110359007800b01c00c070b1444039110358050b1060068040441c0140b500302011600003a00850511009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 716147194 1250 716145944 716145949
    0x1061d10080309090f0402030c040516021203060d060b04061a03011406090120010e03040803180307050a17010b04091a0a0c020601121406010311010f090810020306041e0c0f0e 77
    0x60b56030004181d000030041d942c0f0780c0300003030500c10503d414032b074000e203094184444481d01e0070181b0b20000c019002c464929100080d40216400111101540704821142c1600042c0207074100d0400e0001c090004180076803201c605030f5014840c0c2d1032005404002200405c50740140e0024031078000820750f5050b191402240009101c1c6003208410b8109140340d4610100c2d0440961240e44000340c55002c0c0d0b61103d40300c0030f5181c2c9a51002d88011f00c403400c0f04e60815014540030500804070303240109081d11881c50200940d051000103501c1c0c0f03421303558031000c4108035151405a66041c900c980c41c2d84150147c150f4071092030b010301400544c100c52919070751964240d00091050305507805850306034400307080d6280a131420590480c2c886500d021301400041044403400084c8441c10090300c1d00302d0f04c0c10340b00104a440d159584212052a4003c4280000c11011a8000c54009002030000b080005400d44140011a10754110000842d61440100861130788100c1e506010301581c0f078503c1160040000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 716148444 1250 716147194 716147209
    0x50c0a200c120a120f09091406270a151e0b09150d140108030f07121202130906050d15020919140a15050a080402010201061d10080309 59
    0x18500e0150980366008841c0b036104100c2103a5040e40034460b1050100e00b004000e00103503440c40c001c0c010802e004408a0116898043e50070540e40072a200c5aa5698050402280d0a0000c00d04c4004241c203211048900001c012090721500c0c075400040740d4030380e0050b885507010180d944101026519400c8004a460021189074101c1d4800c0f00519243d01010000070720901c030002c000e0401000c0020341c68025140b540100010316014000304403183c0e698001e4548a1040007040320441d101040101d001a10b00c4000390042c4109241850760031050444010481c0d0050800d150700b8442c900003044000054003a100141500340c903d880c0400d000e5441401e01e903200d0503140007168020862081d543c03503a03a00c80054190214420200d142e40d2800542e00220040360180a452000340108000e0241c55151802c1c0d9455070340d00d03282000307003d41240d44840241089046548980000400c44101581d0340c0c060842c000c160f4641e418034401802400046a101428507001070083c54800c0d81c4008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 716149694 1250 716148444 716148463
    0x809030304030c060216111203040627030b070c050c0f10030b0402122505090a0608060a080f01061806050901050904031101021803160509151201050c0a20 68
    0x3c2c8040030104a250000180c0034010a009140d68000f40101c00d01045100c5c4c620418030503130341b8054030074103506401d49a1050303018480115541d05c90418100c8080618504030707a0702e010b14101c45603200c0d50350b4021400300f582c0800006090081280c14003034140140e4a1440003210210100030801011590040303007558100241550b0f12000030090701e440c3c0440f074040000b4036582c0c03603500c0d146201903031000c1c00c94100c0700c9020b811000e100015002e0000c542450030010000844507203040d404071006200100700d07a412040180c03000411284c1000b211650385906800030840d1340c14841410302c1314402d00c105000c03007820284200142e4a400d075a0074192201520000e40a0b5104e0600380c0b03084a0844a031103c0e5880000d01031407010b0000c1344060720382011010f50350151030b528101404030310207001e05d951110844020440c042440f03040d10040500c01384c016840c2c850629402c5085031412180c001680400082c44840d8a601c0000c4400464090001030a03280c00000050758901810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 716150944 1250 716149694 716149697
    0x603062a1e2106030308070e090402130b030a0c1409010f151103180a1403370609110d0c120303020705030a020c0103200909100e160f080903030403 65
    0xa00c0d20a044070322880c05102c94a4602008644110007580d5210003003031103100031750008081030082003000348100700780c1c2c074141401485c2c04072031384440e02008030000809218104250303446450921588080c450101f005016501c50400740346040c00307000083d00800b0b0702512419000700184504020902c002007910784040d000c82d481a22203206886030109101d2801d0309100c040307808042860f213482031036040c1c1c10540b140065a540c0750030710080d0b9010024a1945600f29281c2c00281d101c98840c0381e00c002e121400e400d5540b2601100c404040d080c0d403402034030800e032a00546002d20000003200134003907900b0b44115a010340c0940781c103c41c80b06503010702c10200c0b09520380001814882e406503078019070000c06883d0354003107200003e540c0b0040035610354003003404c04050349030064542c41d0030003125903000102d903d0083c1203410424140e0000700306400314080c06a0101e80d004106001e540f05011400402c0b04a0880c000094440c51700711030a8004c0001120403c10f000c40080700366500136606 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 716152194 1250 716150944 716150987
    0x20a030206040f1403030a0c02010b090601020312070504050409290c0712120608010f05060103150504020702131e05130f03120608060a150f0b040e09010209040603062a 74
    0x26458a414104098101c250f0303240300100911076601f84136440325080c028150000c00042100f5002e100804c0000c03200d06026030130501240808000880e0030640c40b016070b1604501c2c240e22400080c08440342040240c40034520300007003001e0203410311885034000c40302154a0403a40341a018074110382c840c50380002c2c0103809010344030031100e0048070010541c100300709040c803010b511104614002d000038800c150003641401c011550950107442200c001c0024105000c072607d0400b0203020280d0b2121000b00e8110303082e40883c810004a034800e5010007001d18142e49186440882c070f10080d00d10140c83c18404041c0031010314001030003059980780d4140c0c0340c00d12039020b6602c00c3d188030040410b0b6110034064050001004000c03030b4030341e2014240840280d0f00440441c0c40d000040381294550081c0320a2500400044c00304140000884d81e00091074000980b401d00c00c10046401c2d1352070b60384115411911802e0059807007424027035851a20b480110440100020403100a0880c4941000c00d2100d603070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 716153444 1250 716152194 716152223
    0x3010605030a0c2106050f0f10063906050f10080604020f1c051f110a050705070b0f030402090a09120305060613081623100c0f060b10020a03020604 65
    0x9420392a144d0750f5030001001c0245203050140c0a0b03410301e0440d0282002d03001800080d0018003051100b0303059030400e559880b5984055030040300c800d40c910005074a080034441e429404c680210469a08191041101058070700380b90b841f0106012000d0b1900c8041e49600100b8000d03c1d100280081c1d010b0b4046132403032070243c84003000c180101c1c20840c0243c0c0090800110b1000c0c800e0010319030020440c25010f040b00b070303108018403000321040190450340468042110011951150001d890782a001d44142d0f5841e984d10104550301d54445180d140c0c0c1c070075000c000c20042d0f14094030941d51002650206000c2c404466562140e0710038074000140c1030590f280c0c046950f5031100307410355205440d440c1c25290855100e521556031881c4100050b04201d07501031022800f06030803014652035a102c07042420a1699807404c0160035022104001d04100c860b04042d0082080700134503400c1540500800180043c02406005804825046007401c1d54080804240040d50004840303500ca038100c14000c215a2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 716154694 1250 716153444 716153489
    0xf091002070c051905030d0302090607170909160906030b0d060c090b040311040c030b0d030507020112050f0618010819170c250b0f0d06050a09020903010605030a0c 72
    0x142c0302c2e00f200c0d0300040861084d4404500c4054a581911402c41c12100140710505089050348201924641c00160500038000042d0b03221001c41a41c410081609040c40d442c0d501050300c2007001c03281c0c50202d000c0c041424000303e8125a01402501191600388516450500460011600008000c0c8a5581c404000e4452882224620b0140100441d2071356074503a40d00b0035a070245040600140300301e1501d446007420b58000d1003447c2c0ea00101502e000300f4070300c040d1002e031151b4010500076814400344500400306c1d8000d921480d486036600e000c1c044010700f402418060030044400f00500019000307801440301300000944000b51b80c149401c0f0282d1003d9500d440100c2c01002e4041106800e400b103034421610001145003c401140b0a042c1003a1a00c0d0340c00102c1400c03441d00c0341181509040020141801c85003005244500944c2c4021035429918004546244050f52140e0400c560101d810741480c0ba0a000302070080c04210000c01c2400c5030340d1640403688485100d811700c1ca1100041a16400307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 716155944 1250 716154694 716154713
    0xc031b09030708100902010305010f08060439031202011e0c030605030f070e09010b0904060507180b0a0908031e1b060c1201080316020922050102120f09100207 70
    0x2090f00c84195042d016035458608050549180b049010900707280022030810300c07002d03840007100e0f0301070010a01a21551568140f4201d010342000c525105444d614404c804445001d46215412080070030407a07155041084110480003041c10459040c011640e080c1c580b0451000c5215038002c6001441e954008010350042c400f5500445d054005c400d0344402c08007000c80e880c81205c0f8501c908000a0b919035814900b04da005180d0781d50b00403030b500045004982c0d298071081e4001920f01b05210008280342c91010807140700c0d8800003020000280c038a41443e4000000401419004000c60901940d01c045090800078086541800800400c0b800c1400c2c0403480a14442104001540c131503040007030a01c5900e5006000c1c0702024060032000142035100001210706000c20540e005240d85526401c00c42c4000c03000c0c240904c0301000400d51001808019426810107104200059031085500002005c803c801021046c20781c01c0a002c10100041c0482c1c42141100a0300300180e40c0c18484c41c112210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 716157194 1250 716155944 716155949
    0x70b06210a08030f010602030a0507120c140a1401020c061f03080a0327080304021201020c0102120906070801051302030703020d1d010f0c0c02121915050c031b090307 73
    0x891250010079014850910011030140c0e50901c1020007503078860070145d96034850603038003c000030b1040200d000403444c01e201800340c880e010314010341000201d4644414640001d0300407106500b06041d2001000b0002901403c18201c00d0f000b98100301c0f2810219840f00402090000400005183c120040e1284640d85002c0c3d03520000480d141d4802040060041905100700005907000c000c1548600c509055800b0b05c0b580e019202c1c6186079110b60a1020a6880381c880100c599020301c4121050b020a0001c5c0c54240010032030f0144a107130500c40c1c2d0307150103006461082400000c50050003180c8807801011000f4481e2000542e580e200c00b0400c40c0203102d84250a105140340c40412000020041000340c00d56103280003c0c4070b00c105142d1150100d0f400c1c00a6000441c240400d0079005050000c03110080c550a4000e9591440a065a52522600002044076000c02e141c01586c22000d640c81600d40142c2e403000581e0a525041d030b424522080340310210008100045030040311a81d080000c10003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 716158444 1250 716157194 716157259
    0xe0d1112030703020a11190501050706092004050a1b050a0e0a14180601021c0207030c090e100e1e0f0f10060e040f02100c0812040314070b06 62
    0xd48411a040085d15000c0a040840d0003150380200400503240c07042081115800e079840003900c02e0318160055810f40d004d104229040c90b00da01540d800b117260140c50000c0000521803038168006880100000c071000100307903482540c036021410700a10801d002c000e0403071840741450307507540d00d90080a981d0b507209105002d0380301c82821400308490030030f400c08000104080c0c4000d100d172a0f144621400f444c20860782c0900503030095104a10628440c0c1610621000c00d0058412407510fa0311145e00c85016900f1020049496080c0361801c4641004100107111800c00c1c00c100ea8a25007124503100e15210300c0c41a0703607001c4c80e4000100c0c00d009000030008603107407030b0895004403252603e49403111540c809641d40d4901e803840c00265103000c0800c442c0305503400200034104100c107034200103040501001d154100001e215040d000100d100008005000a0050390501841c161030002c1c00034192950320303096103005001039030000c5e02d40342e11703560801d4044490540e450310b89032a8079103403c403055550301c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 716159694 1250 716158444 716158447
    0x160f140f0a0803030a0209040f02091005130b0309060702070f12020607020f18040c060c08040b070c120312151d060102010b0316030b0f0c0d1a0604060203190e0d111203 74
    0x1901e035005107489841908c00b4001440c102840c4000c0b03000c1c41a00603082414001d02da130041d840341004082c90214021a000d5061300c032465070740e1076082100c0000075a808042800f5480d0f4040100400030403040ca0b0521a0604080c1851401e013601c9000074011000407400740219540c080c400c0c03d2110025112808910146100f0902c10f041a20159034101c0f0440001c622544221981c201c02900003801c0351400745480e1605e1659400700a0039118014140004202c0004428403c0940c0b4000c7c0d60740c0c810704441551040440310031041c1c0c0130842c410f0380d000308a1842c8052824400460700380341000e0994401c7c0040c0d000d42041102c080d814002c1d083c1418400d81c0c0d4420040035030f07001c1c1c8403e48981d5034004641320a01c07402c1c0c031060381011080c06480126401504a41c28203032401119800d00a003e10204007a50020b03040280540c00100342081d403280304100400043e002031801c071101041d4500031a080b000780c00c030081c05020003070400305442e844e1480d00369561601542143e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 716160944 1250 716159694 716159701
    0x60309110d03030c0e30071a04090c09060c022229090103081617040303080712360b100602060112020a09051512160f140f0a080303 58
    0x3001000301c1010000811403103220080503003084400c451007000c0d407250b481b03030035518201d60007030f49580014206180d108400c000310f001c150f040380d00407031604030103d401e8a1742d0400e00c2c0c441c15030303c0e02c003540001c000c1c030f92400304800d0743d226001c0e0a480350141d8440301c25171859000741d103200024603414a0000d0a001c07a003074200743c00d03c01c0b480c81d0518003694481080440c42c1000030381030080c480504401e90500a03400f41055003800103250074450100e00113940030740c0e0003068640d0802d601c198081200002084266074010005948101c5604010445440300340c004080c410100042a4101c00c1c9508280305c01114240c0c80740c500c1074020f4071580941c074000d000342c46018482c0c0208c0c1c0060180600000e0b240702c25030501c01340290300a00390300180307041508200040c00003c15881c10500260641ea100b92202000021080543e1018012140000101c1031a507052917100101c8100350650400803155144000d0720410307000c40303001100495080010758000c5960708142d440740000000d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 716162194 1250 716160944 716160947
    0x919090c170d0305040506060f03070e090d170405062e030c051206010b0f072406050306061009170328200a02010c03030f0f05040c05030d09060309110d03 68
    0x41000746074000301191100308928004500340c5505460041c11580070001061075032400da0034401480b01c2c054101d829803581c80070f507200400030503640c5240b25000524403481555001c0303032112a402d161a25984c80b800c01e9501c056070313254000c1c1000010100820003100665503560038902078241400c1e01b910b500e4480c100700040d0310040c800d00e4071410300001d010048480104540d03042b41e0048400740d04100a0081c106840c0d880400c1c11104500d0a0070b85414901130705141c1ea140c031700c0b17011000032031609040c01c0c1460305070b02514440c45810301e040c1080b0b065a0102c0301c0c00076a0150b801070718080a48046007880d6004031869074500d0702600800101102c0c0c462011b264106940c0e48480102c4a05076024441640c6080000b950380c0080da50711002d03502484007000c0c03040c86440c0001d0240b02103038050085072040c40110a000b034844051209010213001080003800c0100c0c05440001500c15000e0134460182c8114000d25444140140500c01e403050f90844680d00904131000f03900c01c5150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 716163444 1250 716162194 716162219
    0xc0a031205011a0f1620040c050405030d05090f03070305030d06120317070e060c07030507080309010e0d08041a040501080a0c02191410050412030b0919090c 69
    0xc021a14140001581007440c02c84540e60400780c1840502c1e007154a02150aa030780321981000d4590f00025544002562207a00314804001122182c4403400c20b040801c02a10b2041001d2810800e0610040c40b145e5800304500322040f0250400c195101d444002241c00c4441a0240940c1070190980001c28050301100404200c01d22100801656407070b440321031504141d001000d400549030b9140d80700c400c0e007a02c5916070411601d051019480c9481b100080081d80411002190340c0c00a04003081080740411403003001d0030318513014504081a034000203043c2c0038885541d0348030f101000915824000c801d42281c0184c001d11134010a01c50b14443c111003550f100d4402d00f40020414070008001c400c0f644a44880308075076074094442e007600d140301d00c2d0300c90445c10002c2d12032090800c043e0302001410400c102446060000224040c075090614040f19903003200f068080c1400c0290303180641d82d03003400c0c05070306c5080819041c1074410402e0710340c8000c254000004011000300342d0082948030b420f41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 716164694 1250 716163444 716163467
    0x20406090c0c050706180504050a0e06190609110d09080d020703180e04051e2802030111030405030a140904020703020f120a0206010924030b0f060d020603040201030902060c0a03 78
    0x103086501541c0c1c5c410b030032641d40b004000c04120000040c00e00b07215a1405401480c0c100381000740110f8612102c84e01c81e070501e002903038003007000104c020250244040901442008104098040001b2942c9200c0140306205d25411010070b159554012001c224102094400d82e0124000071902c2d44010705d000f412909402d40c2552440c01411800501c0c0030043c1540d41c821684800500342d20b0303048069900f242c080c000d00c000c40c1c80c054080c1444080d6200305808499003520f42030030a0f058118014142101c40e4251100d03608541041000701066000040315221007031480c2901000001c0d0115568600030320209540c003c1c0006540d0043c1640064869840e2000c9402e0342c0130b0b40d40040b2080080d115059244000d600498010043e0440a51101d071000c80b40c04078480d0068032901494030041c0c0250070480f15403520303005109080c01c0f0303c070304a54801d4041d1107048000e092030b00001c01d0360000810081c101500c8280c0300b403c41d01c80d427041d54411082c180441c0c94143c001c0c40e02400700230300c64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 716165944 1250 716164694 716164703
    0x80d0f0501090e0339100e0706020307030806060f0d0209030c04022109070906030309180204050d0b0604110316110c010c030804140d03020702030f1204050d020406090c0c 75
    0xc40045070303a1100e407003100d010800c208011403500b40320344240380a1100e0b08a108182c50205003d03800c41d03200c0c640c1c034a44000646070160039030740700550201c030450324043c5007901e00c0c2d03100b80720a2054a07000800c5a602680500746032001d0358035200080e00e84c1c82401c0f0300300006c0c080403501d81804c4016070040c0c21203c4085007552140c100301400d102c101c2c01200600c1c0e400d03040c84000380c1c90040c60900c09980081000095072811601c848020082e01e42d1507004800044c040700701044441210b0604240c6607591003015850146000d00090a40300f501002501c01025500416500d80e035983c0041010720300f8070710298403440c002141503d4440d07510201030114071004100354003110040b5051001c054161203803590f44120b0b4070101c40c0d48000420458030310315800c89125942408002128003442e49503005a038868041c41410f0400c6001c105200469004140c00b0b0740c0182ea190a403015070b0320545144484800500000e400380c08294000d48000386844000075000368011a040c000a005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 716167194 1250 716165944 716165951
    0xf032806150216140409060e0c031b01050a050c0c03010903030b1306300503030a090c05030f07050f0d02040e060414030301030c05060a09030b0f0403110f121303080d0f 74
    0x5564040e621284000c641d00c00e820f0510380148180300785041844001540500005071105d0035a4800f001c56640746880c006592000401c4001c1d898100540200d520821030031003a12000da4001034aa40030350202d1409000011130300c03035040b440401210f020f2000c0207000744404102410080c3c028a0020701b414009c0c0301015241e4500718a40c0125011100b030740d0344044102c00c0100003455101801881d02c041440c09807111008220300300b0185006550040c40040c2420482c03600041103500741d0700c04c0c3d010380c1207540d5a83d10100c01040c02011101d00361a020131140c144400030719501c8480b00c00940c050b2070401041540c0c4000208148507501c40c4500c0590001841d581c40c0d52400709201c0105400e0580c83d0510260910001a14804020741044a03003a520b9580700080520119030050760140340504000500d51720510300041d26040340003a010100708170018503161035910300c250300b041c031000860078181120b5003c0035008641005045440d440c0a192001c06807111400c03000b1138508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 716168444 1250 716167194 716167229
    0x30717070513050906030304051e0a060c020102060f0402031014010f0506070b0c090d021206062d0d0213050f1911070b1317070302060a110f032806 65
    0x7032411200800090141c25514a01c1c1608000d046140105143d4060106220008058860300c283c1d00300e04030340e010840d070485e207a141030000710003043d4803641c2000031b0b00b445000944d801080582d00105006111203a6503500d0007c60718019100d003181100c94030300b1155500044082100714181c1d9442580750101c1d42d61001000030138003411300042d0a0003080004a41d2a1001e940200180d48010708403070984c0156030005403118410002d8480250000800c121846c85c204102e111940448819042c241c82c00720940c01c0c408034803620540c040c4c0340440c00350040d940c03108208101d100c0304080510841c50720011021001d203003560202920040d0b41b54030504084c0901503000e810000503260360525595071250000740d02d01408803d4500c400060320404a80381c540b0140300624110440c581c2c40e0428034000f442d1010080c25007501515001c5504a41c800050480304244103a600050f160b482d03400c007400c003030740304001000150f01540c0003501c1c400c03040382c021908071403000390200c0c403070038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 716169694 1250 716168444 716168447
    0x3020c12070603320901060801112d0405041a061617120708040f02100810051c12090801050412090b0a2a020d060f2307081b03071707 59
    0x8400c0c0713442c0409404a41ca100c00518400090f45601464100002c60031941e04c0c1c410301e08440080d4541e6200c0000050a07515140c80e081c140207004c0b2501051810805c2220b0084805004500400d0701c40e0341c80e00028800c500391580390381c01407900240130580d603001c06c001d64211740c04003030801c07500310441004c0041404a80c40907038a4605c2c0a611481690b40c038044100ca0080c1c000704200d40d4000d00d90482005138880d016a9840c1c490706171610603c40c18140d950f182c0030391256000b288204074000000c00140b098100c140240ca80c082000d81c0c1030f02200109881040481d04003401640c6044104002e1108541c06609294038503180c100c030068940100c6521881180d11aa001c00c1c030000c8010403044c94042041241c007450b01d40500007060039030006074840c0b20b0742000d5a80c1a266241100c1c450264480d490030350750002d0310340c109025512501400541c000f0b0482c01803001410003e94100c0490820f9041c40350036800700f07a543e11380510b0291203082c98804502c80d01120000052156 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 716170944 1250 716169694 716169731
    0x6050a15020f03070c140109090e06060a08011107081612030218040606021b03031c05160201020a1b0501110304050a0b06010806061e040f060f120b130903020c12070603 74
    0x68101c0c0a42e100c0e0780c2490b0a404101b01068036043c1040035007240000c5070300341442400ca076403244501070040d5003000002c00c0f10070b0290380c004804c10391400c00342c50600c0440c8000c5525181e80002510748840307690a4102d030981c100c01001e848a4803d9400760300d0300d581903004064000303030f80c000c0944000940301800219003940c0180405644003840807071070070404000c5820224401001c0f03e142818440424082542d000d05800b0043c2d00c540c24000a0074581c21410340b650520300c021400d220915074002c040258200002d1180c1c070290141d142807010070b4100d88000d0000740d00d100ea40c0d003400e14003655981d880407420760313a0070400400b01e16298840d400c0300b4050603000300b64504106420b003034200f0000c07010075407142001302008001002c0c0c0007584100001c094540ba44071611500500184c0341110048900445a01c0e0407030131540e0317558207004140070040d5404c0008056819141c140d1034422440351003036208981848180e040d02c00022030f0b400b5508103542c14000500c4030704164564 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 716172194 1250 716170944 716170957
    0xb1c0c05180105031f15021509031e090a0e060f030c220b04090305040f0b161713030b0a060902160219120c03112d0406050a15020f03 59
    0x6480c1060781c50065841800655000b03a84000084400d0114011190340c0c0005940a02c00c070601750101a40e8aa070140050007681c05003404031000703840d20300481500e80c032604000580c2d03044490151041300c541c4100340e6550000180c01c2041442d1580800780550700c04403039191103401e02c021282a2030401041d582c50100001c0c210703d48800380c128900c0c1e80d07054040b510f145555500c0244100740d5896010703003600c06010307172261962141001e0f65481a22401d42017464284801c000c0f16500440c00010b00840e541c0000c00300780410000954081c4030302c03580f18880440c9000c00c5000c000d00c60641d100b180100140d0a0170040d0a507248924070a03802105240c0b20029640c150700c00c058100306003646909520b05004a40c22900d542d500301c4240001f240c16142c580d042c0205000708849030300c000203485411217030340004c40a040c01090040364a0100d9446041c40405550543d072500c1d00014003904000300504200f40c0c55060451051030000d40d40e80041c4170b078034900315072143e010044661 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 716173444 1250 716172194 716172217
    0xa0501020d0606031b03050727050103050f0f040305090d0b16110a0201081503010b0a090e0c0a080a060e1009060e070b0f0301030f0302101b0206010803161106040b1c0c05 75
    0x2603112100c0586c02440700500003001d116040101c1000c2181100b104910101100381841a0504007400103003202e1006006201c03030419801400b41d20001c9804055005615141585d5039100d40404141000d00c0004000c10b050300070b00c20700c00c0b11500541d16a40740c040c142d41d8468940c500e094503d035204030080010380404c040d080401d42c001c081e107111080c0c50502400115100050a01080d0001141d0748020403144d03588070500c81880c03060054101881c021152a60030900f012215504e80c1418080149a0fa940707030841022020240718840f01c04500603820007440c1c90341d0401c60080c2441c00048003d5000f000d40200b003203445541514000414405041d00b0341c0e080d41e496000c5149090070036030135449155000789820425014030310030303c20590902000070184000c080c3c540181a0003c0001d074000340070909a1002400d810a002d9800c1540403d0600d40c16000c2840e038882e0303810804180b180029401071021100a040035081b400f40303404c0200f000c280d54201d40710b02580c041c110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 716174694 1250 716173444 716173481
    0x2100810050906040b10180b070b0106121b020d0917073f02030c011103030c090103090b01060503011508010b07121701090e0c18010e070c050a0501020d060603 70
    0x1055082401c409584000d0184c000280300c40140002243d05502e0401e60002806995015804005803009000101040031015040035066a150a0360fa04140195010040020703044108c04589410030414103d00081408940c4802d180094441d4400e07024000402d0749800c000400801030302e08032a001590b000a48029420a046850b401511082002c00b01110100b1250504090b0040e00444c0c0c0840313145142c1c504441c41818100524410018103010540601e140d01d24000320850740e20121003080e4550304c0c1d018100607070040900c45400b60081ca82e4000211341942c002d00158183d40e0601500c5031404020842107401050900811005140511400300025843c032a0060348400500302a10762101405845000e90003d9008a04542c0c40b40b0400c84007010921881c80920410366040950f41460a054440f0505c184201544c100d910000688030610a812101a29501000b5188442e0703080c10702a020f50419142c0b9420203151100020b0101d000344214001c50542d1072401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 716175944 1250 716174694 716174699
    0xc04170c09041b0803180f061602120f030316031b020a060203070e0d060b09150d0b09010e03130e0c0405011e0504080a0501020316090b030a050606160f02100810 71
    0x785451440300f105510700001d00100890103030401c2c0058103280392101010340b030020b04002080305240301c0d1914580201803c01407145030501c0021010341150301940c010841080085e0b140d46091203042d01e07000680008424010102004203800116421950f4107000c407603a40c140220306804003445150141e400f9040e8440010303c45e0f00519441031541c2000d1500a41e424003203152001110421100507030344000984551611108007904103110341841080344280320080744180c520510301a19132a600700001d02e042100350400c07501c15800d001940d03110403100d08080380001c01c6010b03104071100040001921440c0c0c1c03e0035182160016550b00b040c1409000d05910301c0c4204404e59410008200b10104402804000003400c0740e105400059891800801c42c0105402d00c1981c40c040024081d401c002000009003901c0e0000050a800161900c80300c00050729071140700744406072030640c03c07e91001d1064141d5840c48040c0240d425481c0c0b007000350030071256054111207072404100010000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 716177194 1250 716175944 716175953
    0xf1a010807090b04022b0c050306210a08040308071a0f0f0411150a120b0303091521010602010b0411250501020f03091b03061501170c04170c0904 64
    0x703c1c0b40d0801074001860892490000c82a440841043d580ca40b8400c00040b080450302d84114000007010303145c01425400e0640006000e5500d81d0242c4124038000404c0c90f443c44014002d0042040c0d014071041d94a658070320f4460b0721030301302000507100300d41c41108690510408240c040e220340b4a032040c412960782c5190b075104001c1d030080d000b034410140e40184a80551508078880920300494403031991a0701c48994014248502c00c00d00781161070402c0300c203e9254600100b954002602240c400001200c001c894454600601c0744582020220482c800d020b03c0c5891180e5042c0c0b1038540c000d100d11050b0000f800180d40d00b4030070b101c40d1b00204000c07a032552032200004210414030000c0300b1055500b03540b80c0c41c1c20398020265501070a40001f040c0052050100180011003030314401c1041030445190000b500d07948000c09428070b090395043d030749103203a03c100e0711402014002800b01841d41003101039590349800034091026014100d981c40c041c042400226081040001000c203421a038a903900e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 716178444 1250 716177194 716177201
    0x160c0b0301060e280b030a0b0a0509040609080f0d020405040f1404060c03060801021809090f0a03080c1b0f0d14030c07030c0218091009230f0304030f1a01080709 71
    0x2400341e041440f0111081340000d5200304075006025030030352184c0301d0403d400031804645c3c40e0900980b1034866200e08004545802e038000da4890303080349000a90201304e06010070103216414070660b03410301c002862040c1e4501030b07004e042640c0058804015101d02100c1810446400c9010308080540300400140002c510b9045518801d0207031501141080c0d48024007801c2e80c000c01e00140355000042084d078500e0504c1d84a03264030000c0c0740014688445010a00ba4885107501805400c001c480f40006003914241021503071145100c852070350703a5600042846448802c9140c0910890080408655089100e00b10082c8080120800343e40355407600100c040940e030240b10b08500303001c0f8142035600560b64207120701c0700304801481605c84520b451001c11f030810040c414244102450b0003000c10114203080c002c507410105072049030305002824a801403034440c400d880e14109100008011042016903a242c0e13411038070420054500660102204604550074011820298066602004240103940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 716179694 1250 716178444 716178469
    0x403260d1a10030902032404030c06150608040b0106051e071104022b09031d22140606040e19140c0702010e0301050709050f0301020f160c0b0301060e 66
    0x58440700a49180004242180c030303107040c0d840100307a942c02110294101440708802d902c84400c811003016407000040c204101c005003002d03003042884901c2004001843e44844c200b80c02003c14452001d40c2c1c3e6000500400044804942501800000046150107041541c5000d07440b2141601711102c603c60100076500905010f440c1100101802da1180d25144000d00381c00340191040c0054100125078030030011500c14125034503524140281c00820340c0880308a4418445429682e485941c00000664029a0a0714100c0924080c14001b910740c90313680c007002c032054080500b07800b2643d0b44010440300e03009920441c0d0000d40420009010581d00500035010850070120000d901041c0c0c2c2c0c2519100c42d0200c845110703182000a81c04151742e000710440c071024404500038006850184001821304055101c0c8500890b00d4032040c0d40d8a6034290103581c0d200c5c3c6000341441d1112400410420013910521064504542c060703004a82407910f0400c8034161102910746402019010080c00395460203038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716180944 1250 716179694 716179721
    0x601060f0c060b0406080f0706020607142a0c040b06120f0907031a07090e04021e030c030328090e010605070201050409050f010311120a23120403260d 66
    0x60343c3c05001907540e07114030030140c1104030007400d10020085d03800e49440e4440e0410000d541c040002c12641a0f072110055854203690304c0101d4540b0702d4104031906a14812120301c1c4228100240072a0b00c40f400114022401421201440442900700511050344102418080303200c440000141031603440340084c503040903000080300d01a1b96252549503002c40700e101e5441e09030800310b0900c80c00613400f80c40701c3c018100d102c0d008003090800750700041c114800d0040d842e0320b1402e10b14a225455805101d03441148501409890751040040c41d5100c09c83c0c80c00340c034035502e611500080c0b0382e13582c413502c883d10139603818101300380710340c0d00707040040ea05608609400c90400034204000328242c44030740180c6001300104800d0700d205504610b40340160404403013146e809091210b50610203150000b07402414282c00c101e826a4040c88072042c074040600189a00415100d988805940c002110005000b100d0040419150000c6650300c0218049a18014484034120038404d0750b0840b003160380102e144131101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716182194 1250 716180944 716180951
    0x70f111c2a0807091416030e0c04140603061302091f030f03020f010506030d0509090a060803040308030412080103110105030a0f0609090203190302031b0f100c020f0601060f0c06 78
    0x1a03030540d1111105030000880d0f500915420031180b4042c1c018402c0401c4200710315040c0d4a80720640315103554030b00e03400390101030b141c08001c100701005000308103075440702a00c24000d0709071034401004408802d860141c0030f0321802c00003e00c003545d09174032180c0303070307a030041000b100c0741c03540032400c1800101c28034070340707090b5245680c00000113034905018040343c0d2007600070340002c80c1e03100350603400c598006043c075000c3c0d081500116592540a001c441900c3c004643d01116501d45040c000020702054100f04664480040c0200c18003090601643c4071318442c0b4041d1030341a44030141180d9421080c4070050001c506c03046260090b42c01440615070018150030700191346034034406158156074442c2c1c041c0c000356507680c0c580002e41c2828800c90500c1800d14542807a0b900380c0b40d8000f5607030310420381084181e0250280c000041d000501c03140c41448480c00031150340c201f000101074000d140460040c405031247c511411004000403500c83c1c121841d03034480c6070040b107a040c41540c502e60b40c09411076100e0303034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716183444 1250 716182194 716182253
    0x31906080105040309030201030c320d06270e0d030c020c0d03110705010228020604031a2202010906051b01090c0503010501170709110906070f111c 65
    0x3091003107900c107501030b65074040c041c0e00d180005011100128645010480300c040c90711800e403c400ca00e42440e50491181110080510340c06280b9030140800180810f400c000300001c504c3d1600d110718034500390703e1260b8000c2003100d00030b130400c84d002c44000200380e070024800840f4040c001d030f0000400c031040d40166446d462500000512441aa21040380410400035441446080c104112000b400c030078002811224800d850700d00404520800c01c031220002074050500b191a031000740d5000303680c000c4002d110703005d80031115561200d040b91855001241d42d40e83c1c807615003511207a075100b1034041c0c6071040d03601c0c02e02c1c00c01c641d1680824080c0c0c03404071440050350000b00303003413161001050040c000b00c42d4843c1080105800d5a130103a100440070302c034801305001800300101d01d42c001c80351204000a5200c0480c00a601c40303025560314a54003680c0842c0c04130074486901e50486100b4481d5410040c0c5601c0301042000c1c00d4100d240406c03090b8501e802c184002488502103c80e18803404458002a08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716184694 1250 716183444 716183459
    0x1703151e060706140a0209030307020f0109031718010309020d121b05010b10080108060106050a090e1503010c09061205100305120a0e09150d1505100602071a031906 72
    0xd01c1507800f00c51441da54104d00040d01c1d07002c0300080e00b14406060540c54055142c000039542d005030b950180c41401c005500100e540e00a1020f48002e681c401600b05905a00f2110030502e50040d041ca521501403c0440608540c8240f20f128046a40104000212516a2104120102c40388000e0741030129402541a004114842091986214400118940e4800740502480004209445043c092500010710621001145680c10769503103280c919181d4004500444554140d40d00c6030004850500900c02c042c00b40c0d2010020003002540240002e0141140c00c40e050409407040a00040942c81c00c0ea40340d240941245402522100c031140c2e2690b240c4c0c46080c1401c26401443c40d41810003d00e407008240c2001081c44d1580c0126001c0a503490701c0d0070080007400031010014030030f43c0c01105150400420b0301c24401c3c1040003410802c194600740f410903c861116000d40c50140c803840c1e200194199141000c049088071003482c02d8116110404225601050801d140d21000c0c0c650304042500e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716185944 1250 716184694 716184697
    0x120b0613020d0903090e040b06100201153804120c05040c2a110f1c050706031508030711060c0102030a0212010608060d0803060103090b131703151e06 66
    0xc2821940090342c520071340350181200307525030300052054800e101080046020001810b502c1007040d62a00603000c40941e00b00e00612031500c040007019035003140421901c60024180461140e10340540d44594081890525084080c450b00c0525810800c0207010607136040d050101424803413a4561000c548590000d001d84040013030040014043c28144024403400c04140a01454201200600d650080e190200c1810345074030490702039858103030480b60390b071118038010360300300c0a031019582101c0c200c1c503041d0344031407046c441c500000f8209908868090707840d200c10b104403401003004524101842c1d849200d000c68100040341c0c03000c81031110441d00c2c007084c00214031400c001a001130342c03050114076880e4410b4040c0c12100412040a081000315280d07112003e03a0a50424030054032aa5850700407005054580c07001029a0b25100070b00134104413813059141603a01c02e03010f03a0703000555060010040e0200312000705900140306151450341c14082e00c24100000b001d8103107800c0012000200f50a0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716187050 1106 716185944 716185957
    0x11e060e060405130f05220b2503020712030c0512040501020c0d030e010e060609040308090c0a030312050f1b030a02160510050c0301120b061302 64
    0x41d5504000c0e00c008200052601140403840d0b8512406840c0e150035140c3c1d03075030074580800e0f544110404600c0020860948032000d4800d26201c07081260805001543c8840c010501a40e204500c3c08501c04442c0058030050386d40c24032860140b0415055000100400d072074070b101248c420340e01108440150550744403241e03450303c850406c54024810a58161501d10900159510303640c3c01d5040040c07420f41d1080200060101c82a00e9511a03508a07441030f8031480e09000900040d0146490b9504041081c003290280b80304280460312026490b081503000c5604210b10009208441c0249948001500c00850351400d1121140002c2080c1c804114403082e004000101d01800c1e41d81034541e02c41c07185081840001c40750900649841c200e0042c0e1516500b00400240c1d07012215044a04859070701d1407603100e0500e0740d1a80741d00554003422040e0b02c030f6071109800c0813145880c00036200 = true := by decide +kernel

theorem cover : BRFrame.Cov 716007194 716187050 := by
  have h0 := BRFrame.cov_init 716007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716007194 ≤ n) (h2 : n < 716187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
