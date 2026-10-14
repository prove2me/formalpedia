-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:40.187779+00:00
-- url     : https://prove2.me/submissions/86cdd3ab-368b-40a3-9b01-dd7c79f76bf9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 604676258 ≤ n < 604856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 604677508 1250 604676258 604676269
    0x1061223040201050708091f080603010b01140703051308010b0102070b120c4005090126100204030f152c0c1c0303050f09060a050a0906020a0f0e0f 65
    0x140140d0902e13007156188450300d045010340c054440d1541d000f0844903041980b000e850700b603e17920188540e0f922000c51f81d07000c1c105801e80d100d01da941408650407003500d4020f803c8100003017400d14046c0c24410314048188170f80b403c42c2038203030307105050995491b90b420200b076a05104030002000f20842d0941040c042045050540c2c101820031110400c002858010411095201132412a81144100c0340d0344000d620109244005e21000c413602c0042d2080410b503850500c6255041e02c0b81000e40e000c404950845440001510200c04a00b0348a4030f0000c00c9194940c0c001040610b105016500b44200a40351040701c102d0040c0b000410746080000d9800800c201c1100c40e000c00e510008110a05182001400d09001c0e0883d10181c00c440d1030401101c248040074508120b003071090744c042285903a280e0709508103580c1134591a0750b541100002c04d01c031450307503085140c100c2504080080d05131041c0d650324040384d020541d5040480c4c18115100401504003034000c40c000000d8901d4016106498001703403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 604678758 1250 604677508 604677511
    0x170304110418050a05060105120304180b0109030b1509010e01060503070c03050c010c05030114010201090503120603010b09071806050c03250b0915010503030a0f0804110901061223 79
    0x34040e5540c0d031162404152400b10300c2030350541250544401d101d881c1011030301d030714090003168040c49004d800c0140e0100b0000032031f800c403840f8842100f000115880c184001c1d0842034002c50400808440210114600c0c1c0e821901541c3c043c4501050040d034002844a5050140d2210049a001000400110750084202e030789c05a220b140040d41c540d000c0c5000c0d85c040c011100f03081981d62a00f602d0f102c1c0c3c40d8105004506032244641ca501001c02c10100481c240c1b2100007000b0901c0d082441040101c40c0c2103002c158000b2402800419407496030b4012545000007114200c0010325a007515032a94032545100300041c1c021460083e00d441910f091450707481c070510170080408404500c01c40d0500448852501c0f440ba0700071401d070715a0501880c81660380340c0d00034a0f5403040c5001c030000201e80c600001100c40c0c04402e0744072070500301c0d220901541c41400090050b941842c1c48040344010307959040c00180070300300c1600d03500c8092000c1c4401e081220380d07051030b50003001c04810310108201c0c0e2410245 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 604680008 1250 604678758 604678793
    0x70309050d1704060906270b0c07081005070f0221070501060801020a031b090303081b070f06051803280212041517040c0b030a150305060103170304 65
    0x20a5818040c03800ca160100c40a00305010075001040c08600d0b02d51000103401100c810b9030354100e90540c7d11307143c05000300c02068143e50051080354100400700382000078282040f80801918031603942c82d00003d051058008031585c005a6903404c000740190014440984a89240700070010410b02c2c180c84074243e0084040006002d00110f502d0381005425041034001c2d012000080d500c4108810000c1e01a100c5059000c10804440b0700e0410382d40e1240c1100411250141e0782c401c05520782c0d00701c1c400206508181c49030008020069000401c90f195042450a40f09510001c1c2500d420181c4021102c0007004112803074104100c2151044000b10200c40340f0ba42030070b44000c0103520020709a107000040140008440c1d40450000750010380038004001c590119280c42c007122040095034814060f007260000e003846803241d420b01c0070218101c0070b16031002281400081841c601c40484003a001d1990088469500a400600801c2340c0d6440a403400384000d1801415424181d03120b031900403a86408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 604681258 1250 604680008 604680019
    0x28140129010c030e0604030c08160e160c020a0815010504060602030a05120a1b0c030314010521190503040305070b0a09090b0609120f011d1015031b091107030905 71
    0x1852510b60b05d86040b14002d6901818510803030f40d80303151103900e41c809140c5c0003400740b0b2034034000a04012100b617180d10602c801104480303080d20307003801500c04090011060380c11680d40100800d0a003810032240145140c02c0d10014034030761420080000f0740f6029040401103410900403030500ca80c000301640d001d5010329000c0b05850750360075480360040805038034450510020840900c0b03800d4021001d00d8015000c0c0d42e06007c00c007468100f05141074001c0c401c0e541c000086c1c10b00c020841c0c3d4492510b04c2c0d903081003420b4811a038a0210741c820707101e59010041e43c00e9040020b0810410400700899002003000300506824501c610601501440c6544140340c03c2a496048070a010742d200d00c211040341800500500c3c2c1744204000c0c0c180c0d07070b4080001c420141d62070000c9450b0010009080200307541c4d001c00087c200500740a4410000d040d1204958000e011544004030004007482102d07843c03081c110000c584003924042d402002c1d07940340716908c40000d0003046944082940600c400e019034105440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 604682508 1250 604681258 604681277
    0x110102012304060b0414070905100504090f0e010507021e010605090c030c04050306040807021207030803181609021306050301050f1002031606051006020105010828140129010c03 78
    0x800e00302504c250350f441588103280c032658500407440318502c24001c8009984125007151a00180000082c49240c05008200c05000804c10300301c064000001c100306100340424254070141126003519401e40346000542c1055041081d041c8003894010742c0521a44000c3c003e040c90403000c0b41c54040e0290404220380c600000185001601c041142d0041501404071515860681400034464100300f0049101e040b00c41c0360a214500d0000c0c0c0034003525000f0a000c2d2450319041207030700d84480d0001c01c0d0200da024a281600001c800c0c01250f00c0142044040980d6655558000c0e12503402d440d00007009004080c4014070240c0c031803070707605540170201b542c1d190080364039404103901c1c0d401a55044440d2040240490b01040b8064211038014a100315400d195552560701c168240d4000f40580c25065111a4035002141c00100550f000703459403e003000b4008089499603605502c50901c03c503101d0b912040401d905240d800107000720080090b400c00d01fa20500000241011002d030b00107070070003802c0c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 604683758 1250 604682508 604682513
    0x12060b01050408070e0a0507212003040c061e021b0607140705010207140904020f061207210e0a03030b01090b0d050108250e101809110102012304 64
    0x440b000791070200100d5034441d680700030582c10520300f2219000028240b0010540e80750145030300c000045030004950b80c0c2c030010072091000420806001d52480e95040031a8440003071580f00440c0654042d40fa502981030038404050000004151402c01ca0307001100d41c00c20860380424914000d0146041c4c02c58140408400a90307103028500b4003901100d50040c03080d08400c2c0004150044074030a800b641e1207a41d0303561303521040640909540e80c000d407030740e00044e00500e0884a4045002c00041c04107040120f04d4044040c040b00484082010420302103030510410850b20034100074504480080c010b600507150f0711921004c840f4070007024180c580c6005012607010340280d030090021702d03090755102e1a486440c040900310038403c0250354040c00080c03008884200384040c1c0b036044250454200d0900d841e80720b6a0b0b190300180400310500400380007064808a10003081d01c0d002000c0b00200340047c442c01d1094522022a0150b0305582c036200e04d03514110551545104201856140e8000c1d0307a4450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 604685008 1250 604683758 604683767
    0x12150c0a140d0906050703110d1119080a0e160b031008010f061409040c060c11030a030801050f180601051804020309031c1103040605130611210112060b01 68
    0x1070465809114000c01e503461200303581d40c8000501e80c007405040c0310586503039006070300b00d400807001f039945414200202030950000c1d0f0040007901d4100440c01d0724244410703004413800640600c4610005075010244003901440740140d17a4904445800fa004900442001d2200b0111341c0c420032040c1c050100029949005040c0d860008289100091182c900762442001c004c2080b8050349480c4c40b292940400d050800c00030180c032440c1e0283d0080348907810101c06440030348140740d085070090440400e1405d10b841c280802c283c0d040c482d407a0115203505010070040443c0d101d083d214017901d005680220700b020714080440d0410420309000c0d648d14400c880c0c0d103442c80d48200400741c0041c00001440400000007004240d40c0d071800703092481070040c07501c042043c0e94801d041015100400d001040c0403641c01d90103503800c0001600d0130030083c82c1030b41e0b80740c0c00c0c1d80d80700c4030180d108080414124080d01110800c0200e108944418480d558100b03034094001c1c034502e08000e0f000035542d0800100a9014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 604686258 1250 604685008 604685027
    0x3240102010b0d050f1209030304030206160807080d0e010b030c01031e05010b090108071b1e0510050714161403070b0109022203021c0507210212150c0a 67
    0x380c504044001d00d424069525110300c0c60452461086c4201c01e401c480c0800180c83c040303407000b005185024615001c00000743c209072888100c1900201540001903400d10040404030320800420342c031880d5824007032003100d0380100c040340715074100701400001341e4000c500900304013024240002d000720700d0b01140e10b80b03e01c2d40543d04501c514050000c24241204405000e20300e000760390307050446e0380c2c410084586003041d100740052401075903007a800044880c03030404080d8541400b40001916140c8919141442807818111226515814080659880011101c6a1880700d02032860b08421352403000d03c20b00e0403030000d400740890f41020700c503004c0180222003045030004c0e0042c0e40c5503103a614400c0250300184a2031034410680c03290304440340500c0220303030440b03400400e03510452002c0424cc0007541b5155034110340300c0c01a6a00440d01604c0030701c5003203009242c04101c4240c0c404a02c1407041d140e4801005504a900501b0b0020002040400e41540725000c40403d940b0f6001003c07040d101c0e40f50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 604687508 1250 604686258 604686281
    0xf090c0d0903030f11070f081606110702091b0406031a09011d06031c05222d080309130605031e010507030e12071103060a02130801020324010201 64
    0x41c691031400b0300d82e25401580c10302e0010141040410903503100011144070785903004050740d150300f143c0c0d80801c2088000e0680c0003c807a2150303031154400d603038290881d84841a640d02e00440800d0071000c0d03040052241d540705018004454180c002040012091b002d140300d0300702010b4032080426440c0d07005415000d0554800390070346046503113034088074805941503941c005100a001c070025035180b900090b44000c48103501c070354404619030745c54112250303802401100d4070700b2441c542c603007058804804076000400c0281c0c025000c01d101000d845002c1c940c000c80e40241c09a0008052082d00404811109910030844100713241d50281082580030b000b240d48101c0d41030207141d90000078412441c107110703111049000200b083d03580e0a20107a089403907018142110b94042c01c07040350142e03421001481e506000b81d10b001280300c0c40034006460300c81c01300c0b0a002601e4010030b9007100155120001c0c1e002c2c2007200025419441c00c040030551441d0111102c0306509030700c011008003071b4000c0d0301c410499035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 604688758 1250 604687508 604687511
    0x8091c021b0a2c090a0b01060c050c030703030302041401170a09020a031a070e011715030109200102190302030906090a2c13030903023106090501090b0f090c0d 70
    0x980488681189103852804038540c3c4100c10000e011800b012410b4100c0380c3d40824401103590a1110450342095088012501440b0f03501d0202140c0d03500f08003100045101e5513026a40c1c5061510b0750600415041420f03041c0a58200c02480c3e400c00503c0c01c5900174031425000800c00450b00001e0030340034071540003510140d10b90605007040709407007454a200c1ca0040d10b546a2120508004480319500c2030040f120303100b000340105445465220380e050b80d0000c0140007046116050311030300710000180700400d03a01d00d842c0780d040350503513010f109030700a070300700c0e100210029401510065100d2058150052240c1e40006105400755100c440341c102520350f1b5144841076616404021001001464425000c0301c0302d01e00050664100c0580720990341d5140e510800d020b865a401d0000000a001c00c0400c0741d10030551601015052041c11030040c6140c8601065061600c0340300303812204107822240102d4105072804011380ca1f00881807078184400e1361240c1455554540300c60403400b03450141c1070900d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 604690008 1250 604688758 604688789
    0x3150604080c01020105010e04051b040f0c0e0a0e0403021c0c0f2006042607150f0305090607050a0f030b040513020a05060c0c010c1a0708091c021b0a 66
    0x120002940c60b000c120a800030000ba076229400d001c0340c030310100e030002c016a00840101010569071101e860741e02001800100c2e4414480b558101aa0404c2c1c0034400000d041c0704e41910712b1701e00781e9040e00041094141641c124109030300c0c025141c0d00d90590350701620010350000c201d0310f44a1401000002e80114280520021f680350500c11078032900c500a480e540c14952000301407030850111403c58045500c1c0f10001c11440c424464410b41d8503200d9404d0f130040800000e984020744d41c90384040c107656500c00085074041d601c040d003201c101514414a81e8806420050102c0c0c0080880f1411991402c100000000d01401200075203072004106400c9420401070002401c4903402e4180400d10899080c032880d91654103001c580c0c000c085071760020303a00481440c00036502501c02036824501416401e40c407c40004010003c0341e4094820000003062a0100014000c0a02c5440031100f03e1090f0b003506440c18200c02981c500c4c41440300304030172000424100c44da980721005030004040d40343e21400b24 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 604691258 1250 604690008 604690019
    0x1b0904060e01080f0705090114060d02070605010302030d08040b010303052b06080d0203031306050603070909051e0d020d050a0201270c050a0f0e100503010e06090d2303150604 77
    0x1200020f11a01d441e51007004408000e4840c04150101560400b0706000b07026860720410900d0210004c03c2c2541000b01001254407010310350000b04142d900803d00825194510702c1850702d0100b00004c0b03801044030042c2400000703a4903503000343c11241c0528242d612140c50040214010304124040d50212501400d0043c1d96602e80c3c0040086a0201098514507080e01101340e0f240e01c01240c0b00c0c2929010305000400150f02d40d0b10582d0400c0001e011113100c542c0b19100902214181801604c00d54801c01d050807100800081d9503040b904c00002a10010b11900406542e508101c000e0005000c00460a625068801d52040c441c5096032000d50300341341c05908051508402200c1c0030355658000c00340100d85030405990550449034001c9004850318a8214140d1054602410390086102104400a0319035801d0080f000b00c1821180500f51030300380301c0452490844096141018014800a1200d0741200da02500c07102c40c900c81949566a980e444500d122642040321280d449000032501060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 604692508 1250 604691258 604691279
    0x7201b06191e050a080105040f0e03131a09060a0c050c1909060605030712020c0a0b07111b010c0605090703121e030b0d030f020c1f08060907081b090406 67
    0x1011581100c580d10840c07102c0c102e805109070010040840c5850004110a04140e4085600e80c0d180840001e002d100042c1c4550940c3e00c00fa81200a062603d01c0c01e100c462052801102c221840741d103487d19000000c40030481c203010b070032025020f00c800703840d2076000d04c5000d0204260031000182030403010a0920803030580b05041d40079503038016142c594041079483c090001ca03406050541c480220240c1d808250300041e50040c12009100d0181c1440301001030101c01005000d00d44e2034603000c001c3e0204040680c2fa180c42906640b500d03011885003440c00b80d801070700199000e40c10400100315a80c46004151501d50580d00c001c7c00b90a02c5412280d4180d482212920084265000c9504c02646080110242c60001c1080ca034443d414204020000f80181403030b5110310194016209101e0104000902070740c0861000f81d528580d01d0162201c0743d61060764690f000004440701100d83c00c00c1b034030082007000000c02d94222440025486580c49001400f99140910001d0061042648902009a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 604693758 1250 604692508 604692527
    0x311130e161d2203030608120a030c02070f05120109051009020108010f0303171f0b0a1106010b1213050f030706060b07030215070309020406080607201b0619 69
    0x100480c02c1d16590114100e4040381d994000c200c5544901400c10001c0300c1520348103142001207003816aa0302c00041c070b543c0140244200c00900440107a140e02304031f0310160035101140749070400c54200348001d10500e48090041401e03207000360b07106804050700e050410f004001614000c1c0007807061400300310f4098456080900344500c00e03601c50b0400d990f0784007080c1c0c030100782d030000601150f00400c40c1803648139910141135106124044541002e810ba4000640030b990740d4004020041c40081e008071080c0e004264180f18090100040100e0762420b1158603890107200d840401d43d181c01c40c04a0320340441088000f00e015000020f440d1028800150150740750700c15101124418200500050100b05400c243c401264040d0060030200300032140402a000c002040b807004d00d552144040c000d6286e511840b005004010b0007049503041c840070203090749070204114480c00304c140000c1040c5190209840c80e600f0007038038040200000100001704c0c80d0140b041c07134105851152045c0c515041c5e01c2494203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 604695008 1250 604693758 604693769
    0x604120314030f0601080c1207020f070f050d0206182e1106070806031c0203180f060f07080f030c0304300e03070b030408220311130e16 60
    0x861000c607820140c180381e020403034609150545100004540c1d50044058590002c1041111860006c40702d90851a0101c203a8081c00103034000b50307851a46010401101d40504402010b1046003841d11001030880c0310000c1c80203009680108204070000140a07511603017500040492581400f18940741c10003480d200032848903021030740c11440103d8054404030300000c00240c050403243e07a449006841081c0013400e0180c02d4820800002d4850303001c1d0707624010190302540590740e1182011182481c5d04090b100d00c40c402e0b049040e1020103542c90070304a59540d4003007040d042d120b40540c00c10501d02c2c0a0418040170748407002013080a01a0348400851203544500f2210000d09042c80c00110102c0c2000c240c2c842c0100340074900302d0528000c01078020070031001411210141e4a484406010350000c0d01d040f01c440c4800309085144440c107403000c607034038981400c450405525507190900fa50581c0c02180e0b0050903407200c0221a005560030003c0e807c4540e4044590900c00140c04c5800d00150f071180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 604696258 1250 604695008 604695017
    0x11030c0a0f03050f1302031e01090606050907050a08040c09090f02040e0106030b2a0c010204080717060c0c010e16080c1503150d0b040b0601090909171806041203 71
    0x10303800d0240280300f0103000e4084007009400542e508a8811110b035a0b600e0144d07414403480c88413000c0d4080400000e401004460000f04046802d454044240c405542110384651044400c00c5141c5a01100740e0307081000a15081003592214105010301450710b401c0901803e080101d203805100f5000c5000d05501c0c425981007080490100006088801d64000100b00c0c2c2030007000b2401444802d541c291090281e9440c05040390740e280481700c1c5580c020031004031947d40200c1c08000050040c0240300c02000740cad0240501509203082260b4444000900c04408030001185070908042c3c2540030b00c000e0f200c2042114a101c1e240101d81115806a12900c4500e125440648195003081305040440c0b011a521060a54958149111607501450803154000e0381c0c00701000301244102180390700403030090510940030b040101c001003032a1059045100c02c6400c0074114400030740c80c00300000036090209501919186014046140364101c41c0240c3d0f805040864013007101020f42c030820540b14170940f40c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 604697508 1250 604696258 604696277
    0x108070c1a07170f0c0d02090307090902101704060507090e09010e011d1e01091505040b0c0304150b0f0303070c090b0f010503010b0f04050405070c0b07021c110111030c0a 75
    0x1046158080441d0f04c0c0030040c10300f80218007004c00d610b0160101c044005c40140c2824405000301f480c111b140d0b404101180c0d103407104001903007800802c0010405c01460718809461801d1100c0f80c5000d0040e10042409548100027500a8480c5801401501e150700002040f4180030307134458080e260140440100b54a801e190700400040708641c2c07444009581d02030025088880d80e11102900c0110140e9801c1d5210441d440001e200760003000806407030344400060764101820329541c204002401d038036659600f00184404135000c006c001040c29106040424400345034004140d0100f00600a1505884080f40e04010801811010400c5c0e5403039207003c0028901440400c100300c0041c046050202e182000140034510030640281500201c16003400d1a20390382c0e00c045004c840701207640b103000510000e4000208404039201e517411029071310080c4115690042100b00010002c444c2d10700344503108616600380c500a4108000105214101c3c41d1245407680e40f2613901d40c860840d00000032031000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 604698758 1250 604697508 604697537
    0xa060e010906020120220b0a02010b03030406140703030b031c030b090106210e0a03050408060a0905060105121c090501120c0203090904020301020d061e050607050a020108070c1a07 79
    0x314051800780580400c0281d031404151910156111300540003900102406c15020504004c40742401807501a0100d40d4600300340d200203085038501001d5611940040200b004501d070b00421200748407910748045581d500e01450144e00504103490203d805000300d428500c20b8080704031184046007900e1b1030620503002080d04008500030240110000303d13242e000302000128400034000d450581c42200081c00049280295250101c10740044001030000202445209024000590081100c8905001000c0155a03858403208140280c038054802101c1020041004002e80358215240704402121031420b03d0009041481c0b90040740d000c101102142d00904000d8840d00720418040c0d4003030340c2010400030400c641d840002c2d0041ea070564090204805480c0c007485084000c0030502203803c0306110000340003000c81a90b41c0302070702c204030030310101d400303c2c0c00494000000c03942407a045015a58109040c1e625540011024104c8543c03081d8001d4649607619010317008503080d4442c00c1c1d0125100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 604700008 1250 604698758 604698761
    0x20041103010503030712180b03070f020613060b0604030c0e1e09070e070c050102030708060415080703121e0905040f0c0f1101060b0d0b04140717040804050a060e0109060201 76
    0x81c400d02d90181c1c800c0211402050002c0c105040c1108180780c2000d110140182800c41c50440b078016851110780081480b03070241d00016a400c00155900241019181403910300e4050100004090301c240e407a0603104003550744400807140075603400071040b2082c3d9104c1010710384a50f011903200120900c109c10b03465000c100c04440c03507c500c851000400055081030703408040040c029180318180700181059500050b003e00103544189403590301d40c0c45510307000c0100001c0e50601c44051030902c154920031b1122407008118030050740d82085c1603280b01c8100020458000c4c10885104003012080c16020040f20750000d118402c44208032818401d4008004040046800035000c5e840030800d030003d00205140200703008001003821100004002e681c60007480c1c2154841802c008400d5914905c458943c0303030030b2203180c203da0b03074038039200d002494000005040d01070a5114201038600402c006002c004441c001c403400303000d000c0e242040345980e0b03100142a41c0304c0b8071805408108020700105100b80305 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 604701258 1250 604700008 604700011
    0x50901110a030b0a0603290d06050915060901120b1003060c11060a0213090c02120d1e2705100609050a1b0207120206040306050106020c0a0b1216020a20041103 70
    0x51032090281e0110040400d504c00ba01c00440d160071540c2e5044230360220301948241c91080005502500407072500e0741e604504104020415031103450980c00601082c5240c403034044510f584a030401065480703400c04003207c03030065070000b0036035410b0206801c00f007503000b15824014211401124101d07107071580f841069014500c01440003c0b2040400c00041e8269005081c0041090042d10308481c000d801c400115808810010311198a562081e2020720150030001e29101d05072008000501c0c141c0381002c407032444600b560b0001c040032020b040500100303008030300611464410420000d5074405c0f403034000d408200c0f01401190b1400048850301586c8034018516214140d014009482c01c10341d0000b003001641c2400d03038101c3c0c028030010000890034070a090280026800070b1201d0010301d01080784860180e00021071076841402040e04102005000981008035038059952080218900303e10704000e40702d001d0a103564a212512804130700c100366841c607000644003408070401c0c41000c40183d100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 604702508 1250 604701258 604701281
    0x605060301241d060a0302121513020715110f03010807170309010801061218110906032a12010f0b0f030a030c0803041a090f190510050901110a030b0a0603 68
    0x160b955001005181c444001c0c881000e00e806c1c014201110200f41200c50401215281c0903003038250103014841c07503d243e41c10400d54190703000354a05030045d034600c5401c0c0c507a80d00c0320704116210281c0d041d1171442c80050b0b402c00d00800000544960f5208480c40d80d0311024414110900ea0f000c0815800d4040402142c01012068542c03070308603464075904642c50041c528091007515964118070301c110341390801002c5003038018243c01c0c4003840030781d04000326001d003d001d19100f5802004012400e101c2d80d00c42007074000d5a8a140314107849180301250180c2850144203416510340b0089003001d50340e5512604d01d07800140c13642e400f138080307004c2403564500d142031002c1c000ca5812801c400006442c000110341c41485800b00800001c43e40000700f403800340a58100c603190700b2030000d44081c0c41b4100b1504038912400c10300380d21103024546515481e5a041020045400e07290b03c001100c50ba02500b204040c603608202030703070703540d07217003280080c018200805218401c0603804c0340020024401e00a8400c01074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 604703758 1250 604702508 604702547
    0x509040201020312070e060a021b04020301180c020a020405011e06090b16020a1715060d0201080a0c11120702030f0114060d060b0301020406050c1e030307050d060506030124 76
    0x284000c004503c2d038000600364010400040656400c4e615841f026101425040e0014505180d4559402540a52010b00345014605c1400100715400c070308201c0851345400d044002800107510501281010b20480c0b0281d0850b00b003030000101103070014402c0b60450f4080120000c410384407442118046694072550085000521034010f691030300302004146e00d4402400c0c0c0c080345542c1d441007014610310341c7c4118026001000002c1c014800c052415a000000712008880c9070b0590b80007030319100005c1d1010078042d0303842327003415006406003441d6501c0c440148111031400c00d01d01000038480e802003004901a000d04404081d0a080c14059104083e280804640250b40c03280b00b40f08510003042010383c6c0c03803503c9244110094038288000d2014010f15030320341c1e0380c0d1584901c0062511b01295035810142480c1c82100210610100950390415410710b0b140342e45242c5950303100c0203410181c0281d42d00250000001a0001c0d081d06902100718a1554106200d00c04600584040c6a01a584003014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 604705008 1250 604703758 604703767
    0xf040e1026061803040f0801050f0106052b14040b07110a0f03050703090306060803030a14090705010810090516090806090a02101205071106011215051008060405030703030605090402010203 83
    0x407642c210f206500790010100f10780c01d02d5501d103201809401c0c17580c4004103d03551a0309004001c0030102145000d098075040c40c1d4909108a90320402139888130098151120314039142c1c0310308854a07080f4138200c1c500c02e050a003c2d82050b0400c0c0a152005072960b002081180b92042403090000c142800c03066004000c050401245440a035401ea00031070048040080400f00400041d11a1041030080c00e05035000f96100d20309904404202d615050b18142c3c02c44005042081c4d40c01c00003514003e07a1401e1074040c000e0307151401d8480c400000e40e00043d03052402d100801107400e25014000920b42c2c2241da070500080d54920b11503450700010380d5000d030b40341c01a40d0b030a800b5080c80150141c00484619154010603500000c45044500580c2c1c080001088080f80306000d0030700700069405804140c4a00303141c490585d1301c0001c4072500701c1c9020611502d4000003500030300e121242400030503000f4103480c0580360500e000398480d80030000440c0030a103440f01c08203c505100307040c079115550607001540b03032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 604706258 1250 604705008 604705021
    0x2060a1820060a08010510030207200a0b0a05070c0506040f03060b0f04051905091b010c0f0f0b04061a0603060d0f02030f01020a08160507080f040e102606 68
    0x940701d961400d10507209500925007500c410009100c40740795540c3d814400c1d41440e081211000071a105c40040500602c65600800c15090100c0c8802440c110003000c00170900d8081040030809512010000384086003505000e5003010080110310f2007059440d4140d07458504012107402240211241821002010b000080742136000d140d040030010801c0da01f00e038264001609440c000c88061804007528000c40300522414050036030000d072480007070120080170956031180010382c5203082c0e04204010401c070060094901c11400c0081c1c0001e102000710605061580d1600d000356011150b0303510305422602000039103406040980030083c0240d1854842c441001034614142409440200078603c0c03040c01641c0400414500090100002d41c0362124500081c0080c10001c0c008001003400c034803c41e0311594418210740352030ba88481e41903280c0b4141d02c0050001e004035000395251010040610041c032b2341303110042c01185c0c1000851260481c210000754922014a603614403a98020b00210700d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 604707508 1250 604706258 604706273
    0x309030203102a1713150e0d0f140f040905010e0709090908090d020612042d1104022212061113141201020d020909060a0b0d0c03020d1b02060a18 64
    0x20803201d40d00308201c8110302c1b5103c0c801c0e1402e6514040d041740d0b54031485512814001d210031502c039035503410000e503034031207014024100652040800c0c11040780000d4a1102c0c5d0548001d031006050000310802013036855a4030307202c0f006825600d0348041003003920f0000d0703800d920340615070849500101d050704202c000d806001c04800c1c000c004a03440070091000c1a2a0000140240d00c83e5000341a91800440410040c0d001d00d00c000030790600f404c140e00300381340210b03405d240e00c108181e0094030010303035410012040440d00e460018003103030f075004841e2002407001c00010030744a80d40d001d40030402c80c02c40103140d1084a0310411480840032100001c08000d031801c6200e1403010a04080d195800e0101610b2505007241d02460461440c16404203000d6000c0c20041001d9078450300a407202d0a20a0900c0c585d00558000c16258009903a02c41c80700c0f910080c46901942d030352081000042c40702200701911f200c0d0041002008000501c10030000030740b403200314000c0c025a034850f500c0f034050300351041d03d4100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 604708758 1250 604707508 604707511
    0x2406080711012c1b3729070b0405070f0b0304170a080403120f0c05040f05040c05030a020a031404200a0f0603051b040305060709120b0f040309030203102a17 69
    0x42030007440701036406600070744442178070b507428043c0008808142025091800d06450541504030003084100c0710440004040880b04241e8101c41c0c46503281c0e8440c80c04034603141454100084d10040d01000048681d03910000d580a14401d0992012100450380d110109028100d20040018030304008180401c2c01000c0740001441741c2e81000c540d03501c0c0c840403201654902c01c0c034000020400a02000800b4410040344040c100458060121111001c401462400301425403c0c02d2039000441a840501075071000030800d854260001080c0380c18107100c800c80150751480c6040744c840290060340f51a01104400584807400c84c5032a1580c1031400031401400011300d4580e005c0e24400002c140c0c0340b01140900021446003004041a103403c01e0020582d00c2c07150300c10358500e4402240e00000400f01136109620042190b840c1c0403640d1a41011900341c1140c1d0701c00307905070145068444586132950459070300e017a802c840c000940710002c40304a0902c80c1c2c0002c2500003801da0301a4800d007281c10300446 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 604710008 1250 604708758 604708789
    0x3071109041419140304060f111f0b010e0301090b0c0c030f1303030215040f0602031504050c04090b010c05060c09150a0503010501032406080711012c1b 67
    0x7018402154481a80740072543d5411001000d040a90b40040140400d945005060960041e5007042d1420348003408000d80d01e0240300074490450310b00c8014000420413150720100d41c080344c0e2040e082e0fa02c1c1c641c00034440f0000300360000c0d01400300c020300350605000301000a503111402c012103a0b40c0910b080900c0d040b00035095440e010410400c0d0072644030b28064202d00b01038821130400c0524514000c2e140c0620b080b1152505003c4000b04004551230401c0e01140da90807100140c0e0380d82d900445280480220340010b0792061610302400214405480039009640d14040b0400a40d5440401503c181406190041c050f03400314000480400300e000180c2a9000c020b000c840c94003c40000541040d044000312100140002c00100820360381030082a10000f0a651101070040608445110307502d2203005100c20f00844001003100140719400080c1d000340c038000200920340300201c501c41035050821a800c0116401c00300000c90b1078001c40c0c1045600030703104006110300c0c411414458041880c2220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 604711258 1250 604710008 604710023
    0xd0921020306270111030708011d150f040c08010306061406090607030908070b0304120309051b0303090d0b0105270a0b0303130b0c0d02010c0f08060604080d021e0307110904 76
    0x403010303908002d020f00201c45c0c0c01c0100d02901c07458140780041000c40164000100c0c201e42c403041c4543c110000f68481d82181c00a0503c6005840010214022a40039a002d42d001441c3c448103000460f4040d00c1981a00d10442080c8015039403001d50000001d006070103541e00580800017400c9626001c0b000301840303072290a080e0451541c8000751414045941d002c03107040c02c800410801000078a0600000130030050508118068458035078950320140c1034801c81001c0407043e40c050840e5410415209007050040600050f0002490400c1c1c5403c2c00380315081c01030644c02c44282502500001c0701d00314044014486d03c41e65259610f4bd809040c0941d00f00d60180400c008440d04084e10009600117850654240c0396902c0150380020300c1c00d64a640840c00716403600700c1035000c940c0c1c0328038a003c1c603200c1464a075082e52601000620184265800300e0400e200d202e80e00300001d41c003c281c0500f2200303c2c007030030340b01c40c5c0c010700b00070b41c6920401c240281401c9501044540b03503c0c003000415040b50061340c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 604712508 1250 604711258 604711321
    0x51803091c140f150f010e06010c0309090f0903111207080d0f0219021b030304061206082b0806030a060203151918150501030b120d0921020306 63
    0x280908245600701101e4098204c800705446405401c141c69800c0420703021018000c1d850144042e03200e040140c1242e0400900b1100700f0241440781e0103810103000f1100c4100034500c02040408003d2180c40c2c000c03400304500d241c1c1c62642c800003003402c040e000c00014800340360400a80c1e8044850303020b016205078a42d0344505640201c0c8151000d0070b0f00c5090592054034542003058043e19080c0d151002c00c107485002410104162000b000369411100d06050132440320760400b0501001e400190050340e250700c00c1c02e00800800c02001d9502d0369110000c0d0a620500020000894546404403040d61f003544c80300340c40c400018842d42c000c55108072961060250b40c074410000440b40f2941a644010351841c442c024444030280701601001c80d0707d1200100107003512440300c940151170b544501410305a850041d411a51102030550465259101c1a100c440150307030350290100185000e80200b600d216190341710711911503564008403030b40007801040306039039000b01c043c0c51941d600100c500c1c1400100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 604713758 1250 604712508 604712543
    0x14090706030b06120408040e0a0924060e1003140f0304060507020a0e13030207151706060412030503070e011115041104060f080c190308030c070b0a051803091c 70
    0x1300c03030240b0f1041801954482c60310644800642e4041e207000380c130615041081c400920b80038140c040210f050700d098600304800003111002080642e009a407441407400801c2004050000c7c0182500d01c103070141da040111000b0b0a95840c0c3d0306800701101a2b0041009100990003203000d007003150b1004100980302506c031821000040b070180c1d210300c44000d81c50b0811080540501c021310141201e0032650b42c1c50560110014404181015111851031481010954603128001128050607800c14401314200f0305140040031684100c07030340000541e91114180143d88100540e99152400b003006207111442080c401c0d091000143c021108410403030886202912140540c100070701101288106482c03a00c80844d050190040003a44900042c0d0240d007135041e402c40c1e80405232600060b4140d200d9481e095100d80604c40d00d10041c0003d0511810403880307012a80209124500c0519900540305210140c03642c3c1c3e00542c000180d010b0001c0a036280200503002c113003406540104894110b00350b529 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 604715008 1250 604713758 604713787
    0x14180607050c04050702030f160c050409031e0807080a050601030605130204081207050304061b020406030f03020d1d0f2202090a0b030408091302070c1814090706030b06 74
    0x85084800da0420100840c6910300f0380704003540981c59001851030300d940c90040c102c15101740d0400b0020b0100360100b070018041c200c4610b5020b040007810030019004513040242440454401e200241500344640801051140c00c0c124000e5403186c95000854541010100142a00402c400d0405649410000d01b940c0c1d0005002c4122050f1000181da69043c0340d01c1c06d0520801e0300044141031800c00031000061000803c5404803885460a0303000000002e0301c100d40207114000295025040481c080188841d1032040c50965100c0c1d0201c0d41180603100c01603c5c0c4000200780c0d20b060100000044516061041094050190080c0600300c4214003401c0d80c0703d643c0843c0c1081e080c2c1c69020581116a0905000b4a0081c02c0c1c4054914110300e01607450403014071502e200580940c061001150180701c007901070b504003c1d40100c034111600d440303080ca0302030654000d00c1c08106070b003440000b200845a140c200750203104540b02070b003920381c01c1c0032069001d03044001e00b09402c0f027410040c8000e100081c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 604716258 1250 604715008 604715017
    0xa05180a0c0603060506161b0b0d02031509090607030c02030705012901021207020409170c010b031605011d030304080d03240501120b190803220501141806 68
    0xa4107a900490305024006003101d40641090380541c42c2003290000d0f00c0701c22204101c0349913020309040310922013420316501144496100c0941c05101090031011060140c025500c115008000c031441c00c204c070410488003032403d807440b6440d03410548c0402c0d0301c28800d0b049a45c14500500403246042d8050b680d039030841d070f0003c0320f008003284a0f80300c086c6040013010b407088100e0024801040e03820b100080070682c900c50003000a10442d13451410130708028444296215101c40c80c880c26840e400c88082803400b8040c10b40207a4440d0007109084a030411204801c81d0589506a403000004001ea02c02d5004c1a00e0007450550f040c07105101c00602e007242000030302a0300210796404100342450046942d544103050b803858201d18500401402540d0780700000c3c140000d050f03080450700800900c041041a4100c07551040c4000d0684d40101c1c551600100a24401003a086207189000700c1a078404e03a042260300910303000441c8024404100625035000d0b191041e8002d840b914010614800110180d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 604717508 1250 604716258 604716263
    0xc090b0a050310050118090f0915020705061b0f0d0b0607030908060601020d0822022709160510020c0409030c03170702070501030f0b3007030302060a05180a 69
    0x4000b080103441c01c0700b480d4030f0005003803e08051000400d0650f00a8140286010300824140d03601001645030103a40c00910101d03800c044200180d664481c00d110103540f0007030080c2c8084c41024041080c0195150851040790140c100c07031401d20b592501c41c210180c0c001000402d131075450701c1c440700b0155210f400820341c80c0e1007503d9003013290380ba00e4100350a0108c0180654150f41290218248468002c0580f586c45010000706207404080a4485c10010b0f6040e50080e402403140c001850003500000d07800c401003021a21011519a60800c40c1030307a0748108805454000c2e501c01d0100504c0c20070f848032a00248003401a41e5103810002c0c003140c1100e0071400140d0000b0b230002c600d04c0525410404d1441c0c03030000801411a5403402034000b9640e00c15511819040581c4c611403034120541650003008501390042100350007880e98045c904401d1302a10002d10040e00400300007076105e030700145c0b4600f142c0d03068001d81516a1503940590040c100200300030343c0e094608056941e40b0405000b807044092 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 604718758 1250 604717508 604717517
    0xf010c06090b090c091b0405010e0d140102030702011d0d0e0a08010c050307030f140f0a140f0103020109050a1a07061103070c03080604060501020a020d05030f0f121501080a0c090b0a 80
    0x581c400b00172040381d010704001190f00e103c00c1400b0900700480100d03030a81c2d0007030818413400019038000ca0b504201807a000340c01398940c2d00301000500410b400440c0100c1087d8001c0c4034a0101c000c145019049900d8500040e031300c000694003915004240700c0e41355140050103003030103540c0c4412203400d5074041c07941540010710010401c106a500351081450a5000f41c1c0c0800002000f200790410b80340020380011114240a030000340c20004a07081540003490240013680c0a08264080180881080c0005c03404039a0448010806041c03040c80041255101000142101c841c00c80d041c130541d0000c0700941c2c05035150402c01900c20301c0d840c01540124615500c1c080407900b03908006021603005000540324a08000e4208000c0c2e9000400400d40303074046407210340a210914015195100c0c203404401d2482003c82c0050889003040090980c540d108c20a050b03955884001d8130104214281d1142e0203d55428040380801000c1d5024038880a03e90034404000c6031100307285041d036003000c0c91110024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604720008 1250 604718758 604718773
    0x207181517010509060f040b0a200a20010203070512070e151b010501080705121006060918020a052b0216150b0603180111030f070e0d020f010c06090b09 67
    0x185410820f0540c0040d1a20001e901c40c00c1c15523603001140e82c064281030389181c94a486404142c600e00307071500e000074030202c0c030380d40d4812518010f00369440c003201d1011502e0003c2140c8064400c18001c036407141e00380c1e1362030501c2c140340082404062103014005804000c0b080c209102240c4580d0700721a0040b03110401c4545440356003c043d40301c041001307842c2020340d05280c01045043d20000e001c0d8183c0e00c04549071a40028000c0740c3c1841c11400c0c07241c00e421242001e000050494010b070800e402e5a680c114a07100c00340813003048000f41d226800d10000042d030100440ca44801c1c0e140c0d803404400a5028100c8a81980901c0b010203170707005640794580800c10046801c0c01c02c0460806403c6114910344140031116680c00000e0080c04001c10003000101211800b0907d118203601c03250300118001402c0d07440341016004081d007208116070200106804940749040d0f4a40b165200d00d040b5402010f021444000400440311314001c2107003151001c0c0c0f90014600050903480350948070303001030001400715 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604721258 1250 604720008 604720021
    0x9211f020301090c030c050d020706150e011a030108150612120c070e010305030403030818010e01090b0f060d0303021b07080d020601050d0c1512050f100602071815170105 75
    0xb200e00e401d030518281841c000c45511b80580010a503454072020500c01a25920340d030401001404004007121580382a25401048240b107103030380d850603519524644510583c060748910030900c001c0c010650742d640310000b1601c8020150a11a41c000700c0503100302d41d40031a03107a0036840c10441d542c1051800001040100c0d00070802c0007030b2802010f90400c1c441080d4550b4450546a200346e00000e0304204000340082c80820842503110f0341050703841c00800182e1240c050b094001d0429880440340410345801046802000307503202400385038010070107580700045170303400c0d00290f000b40354008000c08507510301d0381e4043c0d003032041000610702d850140c5042c020f010802030400390160045031007022a048448003050101c00070a00b5500703907402000d1112021001a030304c11812505d0180d2031810035080148d030544c074640d0a070041001603049220952146410b07602d40c10b81c4c0c045c00d541c4540710402c0092004554004a94a01204001960705070322a591242c44103001c8250070036980d100c2050140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604722508 1250 604721258 604721261
    0x1e09050f0607140405060c0c0d050c1504050f0103150f08030301051302040b18180408131a070b1302062803061503051f0f05010206010b09211f02030109 67
    0x920842c0340c40e008403054200481018180118055603014200200784c2e09258542003207510190f0900a0544400710701e5450303c0c6540c1c070683c2c1c200d6400349408400044040c0441c806446c25180000d2041504003038840046000349030483c1420014048540001400c054100c02c10b000303031440401030740d81c0798180402d008414500200d558981441041304202001c20725040e074054522100502d040f00d010040000c0d40200c074401d11003400c3c41914140b00400400c00e001b044015245103268940d640c0c2d401442c00e15000d182a203407840355003040080c0c0012000c4654690203440100000030a0000d82c0104a59030440041005100c02c5203241e420440c4600c00d10104580c003528003444802d060029001c40301c40034209240900d9190008078041050880703044205100d0075a900e003100340e45030181c85a0036900d1086074054010303d0000700c5c686008004865103c500540058600065450007401c840245030300c1c1101ca00403000d0035021000d00d035400c1041262041d50260301e0754102143d103030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604723758 1250 604722508 604722511
    0x415260c0904020f0d2a1401090f050d0510050c09030f010519110c01090303020901030b150313081c021908070909150b0705030a022505041e09050f06 66
    0x9108101c0e0404120050b07540512900246000740c8803440c90021600d410f494400742c00c0582103200040d820301c42d0640c0c0178100c1c003d044800a500b454441c030001001515003008500078041700d075006100c00c1c00a424100d01040c401480327482145ca0203100b484804085071000d6070314144e901d6000407a0421807408108032401f0340160310080090742050f0a003011508070b841c5400f403403c4c0d200c01c90304c0c0d0085964000d0b00d5a0b02c00aa000348205002c1e80380040095101d9000503010900d1703c14100d10382d050030840c08550310003c0d810319245072078140752042104a40c110803101c924042000c2d0340703024000507401501c40c2000e900561500700e0900c1c00c800c0035003080d11203010000300130200300607154031000d0203040303816481c4000380c1c400c0418088810320b91150020031040c040002c0203000c0020000003000036003456401e6915891031841c00600c041292417242d8190b6029803018411f91809602c0100345a2880082c1c03121000325110200c160759089000342c41c1a0003403005109001018007015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604725008 1250 604723758 604723783
    0x12110301031a010e060915030109050c0a0b040f0504020d06031a09060604090503070b0601140a0809060601090807090522050c120309010249030f020a0905041526 71
    0x1c02c1541c1020000501540018486031044400401040d01e20101d03136001a00c0c0c400203070091004040c541003090740c5e8000380c4840d6001d4101d403600002c8252041d03041d11f003900d00c40c0708003900c8580b40c00c1c20400a0f41100c1030304001c40c1c0d641c000001c00600d203c00103100640c1200403009403443c05003400350a00d0700041c103090065080000100c00594040201c441540c1d000d4032100898030386200480d08440c088841c00c00ca1400001d4046d802c0d600300e03c002d44944000e200311001d07556081e0044bd51945030348075503c6c0a5000c3e0ba41400740f000300e40c20482d40241c440c2c030f950009105a445100e11160500400d841c15044084d640e919070a1003515000c9049580780107600c1c204000f00000d503500d409018054410511520a1200c4d5000c2c103000c10200f841055441c1c4000c80b0400c01221101d1150160700110f40740020401c1180c00c06d00940701381c4022500c0d4208513a00e0700b030603c006442080068072404090ba04041a209114484451190507800c1c010810351041c0d11028501412102d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604726258 1250 604725008 604725053
    0x90d030b06040e0613112205040606050a05030406020906040b0d0b1008240405040803070f020703030507081810030f061202031c12020d05061011120a1211030103 71
    0x20312002251a01c05500010182c1360030341d0305c4140c030b48030b88001c010440810340c1c034840014005001042d2a04408510005007042103401d0717590b24100710860b0142d20840340421400d0005c0e11003d80188080e507402405051302500c0c0c081503500140345544285c01540002c000400d907400d0318200d038030410005440948455518105101e0007801c0d190000f400414101031100d04140110310080480d10301510240040c40f00b03082514280b0000e4000700c401c1c42c0091200740502c901c0b41d01c00a102804c0340d4040e240e0a2404c4060b440b03449080d80040c0b884840e0401c5c900c140301c6d0a0b210740c030800311107042940d000a0b10320690000700060314040da21184224451000c0b25000d47e4010601c0c00b10084c0030903102c031140c0c482d1082035070720b40c0885181040c85403010862100d404200d401461103480122003100c1940d502038810340d901480c030304500301154050000f941003000d4210050083e04841e04040c0403c0c0c0c20f40c031403441601c44184034080c200c0c5001c0010803c00040303041804414100145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604727508 1250 604726258 604726267
    0x5190c0906170703080c030c01020d092d030f09150801030309080309031c021216020306010e0f0a09170a050903010c05040806070507030c0b010305030c1006060f140d05090d030b06 79
    0x1d42c3c1d40c821141c00058080d14001030140e2160000f00704135605000781c0070096440d8000c0f82e1035400103002c407550a490b5071410190300c00c1d0346c00054840ea441604c40400340388500c1d0303190710112040490f000c402014020742d14804a841c03400c800000b501c105039561401025819850f00030071840712648078040d641e1003480701324601c1d500810151610941c018045040d0441030408a2410416041264400800092940340b40a4004647e60031a00030350494075a030b48d0f2a03406c0b00c880d43c0211852045414148081003c03030306250000d5400c24010002c0e120713a00f003507003d0800382d54002d07200900803601c0041d1020250400f80240e203190380b420f041a40c01c00b0f1421038020b40b507100040c4240100080020180301305802140c00c0c40d407a54001c06003d85541c0c480c940b20b5900da000c06038552241c420310501001300e20003400b030320090340c0c521341c1c60801c000444502030710621051100c0c04100307a010701c0320f06808201403003010301c900a0030b002070180300c0d6110400303001c991041c903076103005e89410003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604728758 1250 604727508 604727549
    0x140c090a0f05060f13170a0506070e0906040b030a02061c0509070b070311281b0803090409060905060405010b0a091104120218040c0603142205190c0906 67
    0x1580d0340c40c1c001e030080a0f5540085d000c01c148105440e04048014881000310b5015603c00240c49502c0911030400c8551688400304240c6840d840c1c05a410341c8a0003d03400220b00781810303005404145005400c540410269038005031060300807104250800e090582c503e9480c030b1041c018180c00504090182243d10f040c009000513511400b2030203024031658200c2d010943d9420440d4800031410010000c034040300800350403001d12403841e0191b070503461840403404c00041c0402003030103c0e44d40380c00845c03819003d00c0621015200c2e81400340d4a0903565081c010100d041480414860381c416800042c003c903040080010004080d005032107070034078000d4003801c1207803003030211816148500c80c2c020a41e4240e100140103180c0002806110784032820500c010003290a0111080c0c0303d950300c0a20a03007580300150300c0c1203a811208441441045024111011440480545003d0140040c0c0b00d240d01600c1c903658690b614000b00f1260f690260701c080140040a100703140c0070b0031500b000c00203142500d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604730008 1250 604728758 604728769
    0x1618090509150112110d1401020a08150a090b041508030304020907020a1a0c04150908060703150e04080906040803090301140402010c1103070f060c150903020718140c090a0f05 77
    0x81d24018405008071940c0212607031085001210f00398855201d02d806201f10700d155020750010740248002c200c07500049070300f0810120400f04102e10280104484915203046076000c0d29044d41c040da0031a5541603041011400b03481450082d0103888011562420310348107101c2420001020941107401c4821389000090101e14801308101c98800d03040000e844580c4009150300c541c0d0701021f540c02d40c82440682543d000740f610800c851406091f5a52035641d49000d40036900c110b601061001c000040c01e00900c045040090b070003e010b02007003410003840703201082440d80a81c01c2500c0710341c00400c0040311481c0902400d0321016103034032030031414185a8000792204448290082401881110340130441c0c84c01c1024200900d1505e00818180d0342d05c420103041592015009c0e5103095955225803800d4100f030145448096143e4003c002051400c041107203403200c5074082c08001511030491000300041c0000d4180280466485103a58030040004c01100e0741c1e441d80000440c1c4403103e4100116902c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604731258 1250 604730008 604730039
    0x140108010203010f0e0705160609060605090c1b010b0d0b0a05071e0c14030307090f17061308120c040e09120d0b03010204030c0b0c150f16180905091501 67
    0xc1801120717050f207403a90180c896014124010264180c0d018a0b17070709004440c0c015200031405202c080044039114820301400100c01c0300d480c01c0301030040189070789151425007a01071034040c00300002a083d4071000001c0340d0007181802541ea403d011014010300700c206104440d00700c0464188602e402c036501c1004001e406107003030300d002480400960307001400030400300d800d00402aa4152075481c5060b00700a0554000d81c000e62013141006200030410b609041e80260b905038200c0002c220603590301402e100c1510340070780c08a414807002c0c06003541840d8003034840c50107a4244095240c856080c294840c540e0314000780070b440154440100c80b0242802141141d9566121034400705548500401003400780c4a5940b004100c01000000004c5085108020344202071900c02900e5100303011030401c400c1104155030a901e011048400f081d00e000c1086111a4800d0b82030818510000340d14034078040401c0f150388401001622001080010343c0d050080303081000f25201c225406505200251590101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604732508 1250 604731258 604731269
    0x1020307090302130b04050a020c010c0c0209010905070908030c06071121031b0708030a14010303020c0d06270311030c060123060d1a0d02181504020a03140108010203010f 75
    0xe00814040c1301041e8004264111014205002a0800030300b400d000354050364030060765510302404020386078802c180c10b00000380c005014095a900b0070f8202c0c801000d003c2c0c040c40500c00070140000d50004144041c0a44a6010700a007803113240042c0045d14801e6074081001454014012a181054800702d5a1500a24184c1e11685a43c0c80a9504e0f41840000010103c1120045402c00401001d28002e602c04d015240080c0102c0c400b85c24901d9888400b0f00004006d038204000114040c2029051807404500a0f100401d66250320392100c02080351010300b42c00e0503a40310070f42c8003d15400c9a10700350900001001940340c082d5079a801030b00c2c0c2506004503000c61080f0301d540350480d0100c000c5900c1c050002405a0f55429014018030020440020100c0540c40240c031204a18540900076810706a00038004108009070424044007010b00289489001120103c8400841d111031000d403c1e84192600c00107900c5000010303c010b080030580c0f085031f20382e004000500211110b04030050842c0e6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604733758 1250 604732508 604732519
    0x50706050f030f220602030105040c030203040c06120b12010911030f100e1203010b0a170601050a0806040f18052109060a090816051201060506092b140d0201020307090302 75
    0x102e82c549006010302c604044030f5000aa41e081d04c806008003a401981283c4044804003c0b051400c40c042d070503070100f2100a8080354001d94100300c5c0c0b81c0500307052058826807401c0080d14070b0751030300001c000400001f51120103039510b030018000c1108040e0840300c190b104a000b00407645600c0d10342540c4003c4040e40740b001030b49605441e5a404020001070104c6504c8aa9240d160740e114911681da580050420000013540106401141c8140340d80840c058501a9210313031500c00c06400554a801c03028000c0c0b81c2055440080608001c102d102d201c0c20004001c10355a54402d1a040451502241ca41941e10300183c1c40403010b21414000c0480b6201d81040c2c4a00b903c4d449041c1b41034032034803c02e50040403180500e6005030074460140130060140c030f5044403031094040445001c42e00b220620300506e904420704124442d86450004007612000818002d1102c075140081030074034592600303881c110f0703009483e140f214040080a21410156400603c001c60540c50035007801040728000d844043c0c041d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604735008 1250 604733758 604733761
    0x7050f01050903010518100b01090308070206120a0e0d021501140114040b0a09080a02010f050d0204050411030a05060d0f03031109040911030708030a0804021306051309050706050f030f 81
    0x264010826121110b100030700070460b5203040704040031000d0950070745442c40c1c040d0088079400c0050500c82c04c0c0051406940c3d18280d41c1c20360f40d4401b40c3d0383c0000c03002e9911003801c0c0100500c0002d038084042c4900004440440c1e004441c0d9105440c0203184250780c000c0d0740002c2b000d09041d50341c4102c4181107c802100043da400003100060398000307940806440c481030001804030b810701e402001400c5044560b03541c128016521130215803680b6890800070700040c481020130b990144184090324840d00d00d00b00c01480d10303965a00007403c0340c00b170301110800309038040200140190305200c1d0f10350100060360944920f41869981380b05060040100409142e1b03205a19091101010b0540d40307881c002038810403041c152030134142032030710008903814403c2c850110302040a55000c000c0c0e8200300e4254031400440d444603400c01889200c00f00070b028001e035917820300060030f94844440d01100c21140000240712021030070326074101401c580109080c4041084210030300408442141d0740140700d2030100c14079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604736258 1250 604735008 604735039
    0x904020d02040e1b0312030108030909190c020703110405010302010f03020304030201021306081f06200f01060e01091802130f0608030d0213092c1009080901080a05090705 75
    0x40480304000e01c0c0600c00d88190300c403c280e02c0004030100001c21000c4404000f10020034000c1c907c024016465240c0060140c60a14244020000d40080103000001c00362158450343c2c1c8111442c002030710b40142e000c0c2004100b0322400307400e40c4944900903a070602940d130464002800004000f95200105075000002609051003981a220003030611104903c00b01d5a4400040402d4029544a83c1440503180144207580c5440304c62803c40e001c549910701c110b5042918945010020400400395025110302c0007000302003881000d0103840c92942d560015414044072404031110640c09280000100a07400e0250b51141c85160040c030740910040790b514000e89002000c1c2c103441e400742c0d00510012401e00c0c20101c05801902440d4030144a104540c0d0381d641c580c0c4140c6180c00d500da1104060180d01c039003c45d2502e909000001001e0b021135210005443e0740c0740c02c0700c01812091b43c1070000880c00c91800e60344800c10396000300c280b207400d000301d08181940ca601e601d940d100c2c1a2080105e440302950 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604737508 1250 604736258 604736261
    0x1090c0605030c2203021002370c122303030c030408070f030e03010e070b0a270906030b090a111c020301050f0f0c0703300f290904020d0204 62
    0x3144c0b802a182104450010030768214180c0c0c903000c1248202d541c0d21242c45820310008250301e06100c500185800c505aa595041081810b000c1078207420411064141c0802c001c01c00200080c20740540c282412441c40c02d003401703260340c00400da0b10403a0155202c2070104800100b502e800034040d840c269500e07121890b050780d1901c122440200290b80c0740d000c40c8145500050214a030b1340f0244c00a01111400c5a00b1a807100210300400c20100002c1c880f0407902c07442084020010030691825031003244124407404103088c03442e40240b000503104c0c2d0043c410000c440c840d507904054010010203421200340d9909465142c5001207901940030011880c14003205409041c0c00c0702c0c1c02034020400d90a00c4a81d225681b07200311807450350005c1c510b000c503080c021500212a002a01940d502c1c0c040900c500c08100e02d070f1a262180084410000a443f80580c1a440b550701c48038980d08000131346a6602c00a201f02d41c100d20700b0508011601c0500c041c003a00c4500002c3e030711650403218a0b000307511f940700260 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604738758 1250 604737508 604737517
    0xf0507050105070306030201090b120f1e0408040302040c03020c25051003050a0e06130f21110c0103050105061804060909080a0311090f21060a0c03050901090c0605030c 74
    0x10419800c02e02480761298240e8011410399000f81e84212241b600c90411110911880300410038100054000030b0200d42505030043c3c0000700400000341140401c2ea48882c9804140c809031b41000001404008515107413090b1088000c141c2001e45c01c1c459402c950580b50419881c91022410804c02500032162075840000054000241042913080101c407000700189000c807180a410341c903004c45d660110400040842c030940800480c0e981c1d11101d6507928803d40707642e080440750907020100c1051101c0c101c02e844600c2c1c4046a5070215a296030b181c2c07182c542000148e1550504d494a80107021a44607c0100c811048503180910120340c640301c041030041c1865030140d5105460080b010081160400003400751040540e01071003440026142070480d0f00c101c8116035800f13201441b030310030942044410440020014005c1c0c26051141c404168203004c01210781d5180140d85980d41315015406200f86600203880d9030003006072140503900c2042a008600640092010100010b001840d0010854 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604740008 1250 604738758 604738763
    0x100b15030702011d0106180908030105061e0a2a02091321020c120706080a1802030a030503220b0f0c070609060f0506190b0c0c030601260607080105010f0507 69
    0x281e450400d40d140c1030003030a0501803a00f41e0210401f0b600b02404150264070012600320b411a865039190500f0444198042511440310103407425040140c1c01c4190003810314136806031a0150441d042551481000000458a40c410000e01d004100980c07039890b4150f6100c5100c01c5a910590880d080c146400000c019180c0d03407280030380c2d0f4000185640841c0500c034214060303541d11440b45555000d50340340d19150203144002001000064044200e54106a003c00c58150300340350004141d402080c1080c000400590102d14000248221a8540c4840341c420041b03525502610b0207840c4d031000e56080c40948240455206c40000c1000f4650040032220318980c0b002c010402e0703800703074503081700540850818012028a0400010024140405401a100c0d010700328144420704090240400e0b0304100741401040c4600d40302c8240c00e840030000c0c94041c040440c00301000f90708004c0c400e8440e8903c0041c0784042e8000c1c005000201e50015603440c1926000d00708000840c001c00380803220741c021080003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604741258 1250 604740008 604740041
    0xf060a0b1207031a450412090302190305060705040b090609010e130501080c04020403050a1b0506070b16030903120e10020301030605090c0f030c09060a090914100b1503070201 77
    0x1c18036100118603550341050741200c104003807a0014001c0d42114017040024655040003c00142440e41c0410070390035282082000e9076100d030082500540d414030240b1b2002c410603418002d01c4420803106500c00e14a03d4031510b01400c03c004d6808034020300c840e060203a000030506801a0307000700da0880070b112018045040c505158600400902007c0c41041c1b03240c0206045141d1500b018000c0b1000d0380d4001c002028241100c0c2c1e944840e007000c0c411905c108a5280402207041c1d0740b1940100012801807007048218181403404400c0742c44500d030510f0500d80351a16140000fa089035140348038101545001400109424105041c801e07010a071070140d900c0040044100607403035000f14040d1042500b150411900c3c0028803e03905000701c0030580c507900c101c000c00800d1038100d40360359000f00301404440005944a01a00c01c1d11040502108c40c15104090305480d10420841c0c4101c44990f20024000c810f1108042003001c040643c078140c07100d00000000300194002d401a80030304110088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604742508 1250 604741258 604741279
    0x10b041403102307020c061b07150e03011413230102031608060919020d0207080a0327020603070327030e0a050a150c1a0f060a0b1207031a 61
    0x14003c0c0518840101d10681e981520102d400b007840019100050440034013600d10340444410244040005105121307420700c10000b011400c4900200b1038440e400d500d8451117503803149070b4201400d5a00b2080c19130f80c2c1c03049050410001c00d08501d6a03508458205010444483c0d20f0342c440b032804090000f4000031980000305104040c2000c0103001825201a610008180c61758010000003220584d0440421508005906580d08035640240441007040b000140780c4101951100c0300c40d0441464800400e03503a80e07107200c4640500b132000b410001120090aa6521158006901c81c00094a06020584d9621503c1500550141501e01d0340490042083c26809586001040c00e0500c8413224041d2039480c41c0080c3c03074103111f040d03101503540d01540401e0002e4840c2088039214910702090319078000031940d2244400c0c3e5401868004c80d0a0301000200c4d1400c14140582c590b4258012856540200002c504807000700c0d070f1103a00204649408034000140600e1000c0b002c2c24000d029920400814 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604743758 1250 604742508 604742531
    0x161d060a110a0b06091305120307020106180e06070504080d0804060902043803060406050606070b01030303020a02070506090609040906020c0714150306030604241404030314010b04140310 82
    0x7091813241004440b040d100e5610611100340c865174040c0001c14941c0318601940e0b20340180405160700500a100009203da560301e2942c0d018140044c4126030141d40380b542204690042c00b2655014086003040c0345807501e0000580e0743d030704503503540200304503c0201040c2000502e0700a00c0c501d60b0008d0051000401240c0f041d02c1d0940104c0c0c40b480e10b01011900907006998800055200c5c900050181c965aa42c170340311071014080081c44140c1c014030810400d0b0004104a4134039010b1402603a0050b21880c02380400b82c540040390b0805803150f40f0a006100166945c0022628929026100420340500c20314280020f4003414200300d410b40100b0a01190408080c42031510f01e01040700e151135107070304d000f10b100014401a0750540d0180c00010001e0042019a80900c20030090400840b80180701200c00c0000c45040f00b1080317103401814410f02046c0755140c001c1450011100100c0e01040d4501104815548924400c0383c007130a0b000010740880761780500030000d000c212050203000e03445082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604745008 1250 604743758 604743773
    0x6020309120a020318010206011208090d140f070509010f03060b0a0510020a1a040b010605031e04032706080a11040e01080303100906060203090906032103161d060a110a 74
    0xa8000346409540d446405c8425803000036828125001d045141e9141c000540320f040041e070048401d1900007170280341e00c800140b2050b01d0090303420010790140021b60041c41a540c241140c0e50301462141d418000180114030401070a582140d07440000041d0070304224000c43d21110b036560281364010702018181140540101e91598640e10035004405554013802550000d400141d401030800a49040180140343c0944011a000040d43c00c50740b090182070040d03a18018001c540880000c0c0d10041150008200e184400c0c00451126001c12040750400000815640d4001c0800e42416120300344030517149200c800b154040c0001e040c1c0071301550784502c1455640d0707200782c0ba4510300856807500041e9608841c407410090314145e50141d4588007142c0100403e481c0081e20860340341c01228040c003a0008401102e018090325a00b0f025207900d003441c215105070301115a40c0080c40307840d40c48102d402510840019415200321680364948503410012641c00c04211110701a51080501103028000b04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604746258 1250 604745008 604745017
    0x203070308180306101406040918120c02010c032109050c1002150f07050c0f15060402040f03081b03030a1a0d0f02090a1e021213080706020309120a0203 67
    0x10b038410003014400d0030080c90b948035003ca420003403030314a8072800d000d0f03901001121a18458001e001e5400c3c80d072103c4100045070002c050718040800507404940c01c025010310101c40c16001e60400c0b4248684580000e070210840381d4009080012000c1a20300100300107401000035003405a080080c20b03a1440c240c0e64906112540d40c1c444c6031030088060106100040d480404104100744120320303160300749844041d40000c0c090f0014480c00f4091100c4911003081340001d000c0050f0300921101f1001420340030407031000380c82d1364015801008144411450b8807102300890384d0083c3d0655540707182c00280c032900350690b01608082c0c00000207004010b5450b0308403816061141a034111003604480802c260355644000040030794010314040400352034003c02590303010301245008501030b04c0360440d8407041d1100d0606a4106903020400158241202120640c41444c1940c1c3c4005224244c031003500500481d4401010180c00100140b4418002c0c0101c41001403036800e25034a52060b0b0034081d440307400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604747508 1250 604746258 604746277
    0x1a25080105030615030a060c0201020d2d0209100c1704060224010303080622020409150510020601030209070905040525020d120c14030c0418020702011b030c0203070308 74
    0x100e4004c07070000042c807803040c0c5450320024010154103215a07142d80c09410050502425035600303011060322290b06000ea43c0c052803043d02c5c0e5001d429032807010750202d91508020707a00341e1031061154000035111622600103541081c01c0001d40c44044c1e140c2000c0e40a21307580720080307400740441c001940907000200502504100301c54401c890000c035400203881003091002500044061011900714200a13103000d001c4002c0418a104901210324880c040e640240d100340340c40c079074960880000040f02c141c0f82e00070780801c4520a10610340000000c0d524101800042e11507944040440c05a81c064040540180405030003800249844c4410200208030181280c201c6068841807800c100c3c40800c80080241981d100d0103000d00f1070303210400040507003020302001d2210059024224022070805148994036511b140b41da5142030103001e490b006190301c003080c800da006100402c0141e0300b12a5141c7c0060144401c0910001b590030226140307640c0c120b02940501803001c000c0140311416006020004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604748758 1250 604747508 604747513
    0xf160602040503122a0f060708070e0315010510120e01020406031404030f140f121005011704020405060f09041a1302030c06130e070203041503091a2508010503 70
    0x4000204904c040e120780000d6580d40c51001c00300000407940241411550070081c000c43e40716103040101e16203080001e445503030100340307610100004903070312221600c200c10003038019081e507560807050f02e0840d99041c09001d104a0358160345d42c0c203892054000001c0511208000c1c880000001c8109000358498015407000034148068803503140e0056881d40c3c0500d81c0b554a10760b40b43e091210469040305000d41000d03601000704642d02201d80050701912400d40d488200e1082801c0c2001d100350100110f512481c180400c40034a51350a403181007038540d2107501500c020915540360400541d21b0442240b00c10384c40304450b401e1000f40801d0003610300000e10b156072540103075100e06031007091833111014001e62541c4609496005410450003503d2900100c0145140303c580740d6100e09440c1c1001c644a200507800400d0030000b017007201016150800b520304041010fa4229169807042440800485600c4040500130415a0750000d06081c0640c1400705100c0c4030410084001703014503001e1150900c00e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604750008 1250 604748758 604748773
    0x10b340302210319020d091b0e040b15010c020a0b070b090c031e0a0f050d03060e0c070602090102071a0705010608010606080f040302150a0e100903020d050f160602040503 75
    0x10b0b1038141c801500140500740d141c1c2143e5820201d8904441c040c040002d000d07070240030305a0602c01c24010804418460807640548019002058000b62110b5001782e0f03075001e80109000109540844003500641400015604642208016511800400f0000350010481c140025042d01044041c00b030b024401d0301c40d860651107250140e90703999040c4051580c0b5400500003d8203400c84100c0c0c2c9203604848400780c075200b050b9034560b44503519203418150348a400c5001c18800d030b0342e807603c110310161000e00121180c9041c1740c10124401d01134120020302c070f2540001d4280441e07008101b100028046508400070154604a002039160800001102c0c0ca40c01c0503c0441c40d031030107016040580d00b05968045295562018600709004090016002d5002c0c058030402100d6880e4000e038801c401d440008035903035809080085c60b02c510390796a01d400524003030b010340010f0340c0498010060600c6e894255140c03800b03507010441c188955a24442d642100380810710401503540c003c1c10803248100c0984035034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604751258 1250 604750008 604750033
    0x140609070c05160e0f1e0106030c09030503040801050f13050712081c020c011103060d03030504081303050c09070201090c030206030a11030103060911190b03070c050d0e27010b340302 80
    0x211b407406284107500c0c4000c0042c07218502c280e01450030000c01d850002400c50381c94407080d0555100d60002a40d5944a201300100c002d4034030b0003660031104403000801d21b4040c030b032601a00c51400d402580c42c2030700490341700021b10051600340d4048441e600014440002c803004120020751060039500055400e00d0000180040d4440c03d90380302300e402600040c2d407401c0c40d6134100c000b410000c00840300b09009104607840180d10f104c03106e018602c40c0000b006040e00308800c214980038020310740c9046a04014099000801a00c400780449505a0b00940c0720340302d114205015110000001c551030700c0c0440000b0030301807641c00c02e002d0f544c0203400307400b1040844414031146414044100c4803c00100c00304200d070420080007554440352030314010503c3ea10342d550b106c0c103004c4850480c90000f00c4c218602c1419240102d684681c0741e44c40e80d104104062230113200765941005206098101201198002503c0010340140499000b08510380000ca8182c490304003000e0f030a031005500611403c1e0540d400b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604752508 1250 604751258 604751281
    0x60601020a030e090601050c0304061d0604140d0c0914041407050d0f034a0d08030603160303080f0709060c0f150e070603140609070c05160e0f 63
    0x81e4503405943c0e52120061181c240500c0000c09000c2504100d01005044994407003480900085c1443d680c42040001c1d07100070514034861942d60303032407092104010030032a4074003003400405070700c40603140c102f03400034079003440320144007254800c46080b424a007640c85210312100307541b8495441440021819070144d00340a55500c1d050040c03030741080d100d12120010540030700c0500f19691003450300e4000814942180c0c410321203102e80d12180315800083d91400c0e40e42c03a0f040c2c44110041074820f001451182d03000500950094000079094410010200b4000d44050003524020340720104104284c03641c03032031f0080c8050000c0b01d020b28100d240c0c00c003042c4800e00c291017404c216419603540301c4660540e512010100d0034030710b02c11288a4803602c940595a8000d0081c403800440b80c8002c1c01c840da01c0e0110103002d84060b02d10704ca1b1200516400c11040d955645122a0003888a03d002107001801d40346c620304e04035880c1413001200d00c3c540000030303030741d105698a140b041100d0a403000c0c264444400c1503a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604753758 1250 604752508 604752523
    0x1302040e010b090f04050f0102160201120e060601031808030103120f08100b1c0c020706030f05010b120402150c031b0604051f06030f05100605060c030706110c190506060102 76
    0x203500a82150100b40b003440e13419a0b00d600301c0e0184069441c0240048003141c220380c000000f200f55003032424034172700566170080100c0175000301c0440207024100300c0c003203c10740703031000144114107141d40c82e4014907410071003600044043c0d5204118a40c1d9584a052041503105464541e40000e90b5200c802c104c01840b030134000b80106030511001074040d0a08001a4158025003a0503100c8020070030514607200340c80c002c00c1e10104154014220342c03418000b0090580e440058a0744500d8144001007000c0a840c104403811900790001c18903464603a803001504003131840c4045201c5010109240b140104040018107003480d401907034200c0700b400c01504a403603480460700035101d40c102401b100c80340203003244003240c0d101c070903035002801c00d44980e56110402c0400105540c0d40d0f0010b0704000020245105000152008844a40c00d05001c003800750350300c0c40381610040401d0b0311403007445449000d100c1561410042d407810b998440101d02034561030754290700010b81d03e91140d4030110351039500200d604e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604755008 1250 604753758 604753781
    0x171312050a060b0d0b0c0906250302011a150d06080703060b0307060806010804141204030501050108010b0604032004020405090c1315050919030203030406210212220602031302040e01 80
    0xc000d60f90798900c4100c6d00d9000502c1c0f254010f1800c201e1440c103201c0644040301001d241e05504c500e490340600300207007150b1110080c5580003a000d0b024213016900c1c0030500c14a401401c40c1195102008603003000078003007542c4044070a115040021041108035003000c81e000509600710342082d079031400d0445060a0544040c0c0c0440c0384040414003048e031407a007500702603090b9400c42da03143e40356130a41c4116501036401914265596401840100001c0c0102e40e140801200d0315410300781580c13184505201048405d0040c0c5030100848c80780c03a06c603501624000c00006040002d01d18060b805103d41d540480c1005405400241000c100c3c12409081209120301ca5500d090510500505220a100e80c503c0400c0032901740c000c000005079000c00007031001c1e01d41039031418215001502c2407115030644d82c400700401c074014407240901c00740f01400264000340030f078500d240b41d00c00c03400e03210a0142c40d004094600c034000400c004402c1c0c0d920000c00c4509100340d4040001c0140c80e00c026089a0148422 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604756258 1250 604755008 604755023
    0x41e06031410090209031f0905011b02060610110105040303060e06100e0d03021903050c0f03030f0a1d0d0e0a0b03041e051014180a171312050a060b0d 66
    0x5010345041c503405801c1092015040f10185000100c20794403124040507040520b50719988c414080060a00514510060104041e00c80c029405800303515590020011806072038959010070f840303886450f41d84100c0b1b800000070481400e00b0704005016044900841040c1c003200700108000d42484050304001081540d15114084500c02c03c0120448072840c081d0114482d510b1900003031090b1079200020944030381c680755600c800d5901c509040c820108550300380350308148108200c02031a180840c1d848030504d0800211100e4103299070710540989580400d00f403041044140e416074000d0451703164480100d5401c101c4a43d43d00c1c101c01e5900c0110b030020038948a410340344040c6542550310b658860302c91170641c1d0a82103820350000445110b070b4509010680080b081c410070780c100c600b42c0b800c0d524480d000f8000242541e159070750b0071300c0c5844001841c0da5000580c403696006210b03488024251480764034407004a54105a9902c0b8041141035500b58a0215000722501e401462810b003554001603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604757508 1250 604756258 604756291
    0x18110306030a1502070206031f061409093705130809090925030201080604020307200c03070603021207030204081c050906030405060901050c090a0e0c041e060314 71
    0x43d0411007000c10003800e9501502441400b0060f5905009075105040c40340c101200780f2242448000002c1890f8000400d1020301204a500e042c40c00041382d008041c01c0e41e881116031140064802c1e44190075800203001001e010b08040203905400300c0c5200001c5000052000340c8840700220209c03ca02a0300403d0740804100440c03207801e02c0c4a502c0e51040682c000d40b8103515111002180103c4c0500c003003466070701c03821810701c2150381000019410500c141e40c21403c518108601800c28200c65094407091219070740e038007045a8041014035880303040074059448055498402a001c0d400442c1d29003480c984110004000501c2f030300c00e8404440c982c4006150742c080c0c8076030307140d8020b48400e001d00410600300032840194503460011405a0f1141c0300400701441c00e0007680e405c4900140c01880c65074001c0015680903130f1484071081c00c1d1110300c0701d0b01c1070a48503140d040500d44100d03070003540d13100300c1c51541084c00c00c41c002d601402c03511161400d120703540c64400a100390040440d4080f1912601e201e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604758758 1250 604757508 604757513
    0x20307030c0c0e1003050609060402011b0f060e150108031e0f1e0a17010b030a0218030d08040b0f010612090203251814040f021918110306030a 63
    0x1040302041e28007425a40c450103881e44100301e1000001c0391200303140d141c2d0400030070412408018959009401c0c10107440b40d0f04090740004c05551410001244440e40450724106000b0340e946a9001c6540c4101c0c2008020250b1200c162a0b00c05400014100701250000160211000c02140c1e0300000f440e128002c1e80511640c400d034250404416008024070911000c441500b2200034207111003503070010303640c484541d03010041c03400030041401c032010500745004200690f510300a42e9001001c0f047c0168540c00180e0b00350600c45400f680e1250305108115030101c0c5075820006c1d45000d00e01070f146540305550342e0751070224500c41c207100382c02c0000c0c9002480c002c40b4502e540902603807072005098400891130400c4820712150f400070030038000d1031f1000c010080c0443d0320801001d0341d206658140141040382e51041e01c00c001c0100050001020001a50219910105019601c10b05a6540b0f180f540e00c0e9803400c0364450744020700390344d0b45207800f0b03505a18100900c1624401c1500800804110340c05a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604760008 1250 604758758 604758767
    0x512011b030e1c050d0f1b080c0f040e0405070b0a0219021203073c0f080408060103111c0506070f020f010609051510050a0518040e0607021c02030703 66
    0x428440e29580100490340b040e6008088600a80f207000d550381c1600c032110503843c0350807950303002400c01e51940f0f0240200c204040080071a9211422820812080c1d9030b0b80c00b038007a1a204010000c0754019000401094603400019154003c0d4041c50495181980300c44100392039220b02c543d01c00260f13005172000c403040d080175031400859034409400e0714080c01d1f080c0c00e000c1c0f950700082022141d200d040329505c010503180c02040c00703400e011000300c5194080c007241c002c40801582c58014110f28258042d20040c404910101c5005003400001c41e4090343e076900f001040d05040e0400c4500c99001c44200c401000c0305900040446500600070b4030103900d500300290748000000a811040d400b13918600801100207104c3e000c01426680f4000c40d1618020080320141880c00a805110b40c02c13001e004900740c1d078060107591140403030f4101141e45426000f2408484411017404561160a03c0711249006001182c00350091849400719503990a540c0c0e140110508413031103110042e4418491440464400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604761258 1250 604760008 604760021
    0x8030901060e0c18150d02090f0a0308180a031a040f0b1e0a110a120906090c050906030601050312070201120c0810060e0a0302211005010512011b03 65
    0x200002500a80e1aa012a021541121006503020300400c860b9908054403c0401c0600f5080f905800b660b80c10b000194018003402e0160242140d0105542c807190316415241409841d0084c042e034200c0760381c2e240030b4215600c11019500135040880381f03244035007001c0ea410710650764014010340904420030701d440140c8000405c150307131800c00c9040ca00081406411514091401c07800041c8054200c40d0308142805406048400c100345007810780d501031003030101070703a681c5021403074400d83c100c4a00c0944001350003c0d0001821243c5440040000c004019980808a90b020790b042e90b0199500e404041d25200e00344a400e406030002001003c0050110b4001d08001e0b1050601940540e104071101040b10107030700519011880203800c2c080013445d00c107082c1b001404540b81203180e12240e5000b013055400300384402409031140d0300302d0006030b060408030b03d119004828216a00200419442c0307000d44402e2017503d001e0000e9480819008106004030810750204002c40e407103c44030f0f0f00e401c80c002c102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604762508 1250 604761258 604761271
    0x40201021006030c3b0403050403060c030c0f020d0c0312060f0e06120a030f120f1a010e030a020904140a0c0b0304150504050c0904210201020d23040803 67
    0x1034141050700c241814400d100c081d501030b1049151003401c184500c8406250400300b40080c040080036000c0e807621810740c400420441031072208440c2c803903150640e800e0141d81c10007084d041c2006200c01001d07a02d43e000303500f118902e503074042174000c05110a9031510511103031600024020201140030070f0060314408031494000e58001072a03070b540c1c60110701c0240705801c0035006a42c00c00911005c0d242c001e1032600d0300207428001d0400703a012940d001d0003a040c140760000502151000480501265a1003207a0400307226109021441c0315220907080310f12503c1d4824003003440b07161f0161081c14000740038144ea9902404426640d26580c0b02e81e4081000e0f40041296403240854100c00600448003540c010803420304103540f00d0400749040031014680403c140046840c140070040420b01c0000c00203140781c001e81c0d00070540d880d642009844191b10140490440e0701481201785010340c158014001002d91440802005850a609604051001c4004084d4522007004100441c8100c40110f80201c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604763758 1250 604762508 604762513
    0x807020708120304020907110615041811090f070906030504050721140a020d08210c070201080a0608031e04050310060e091c12110d020717090109060804020102 70
    0x10740e61200395141c1040c00000d40c103880d038040103200c1103046c941c0c0c405801400c1824404c41d29a070740742902d5a82d9000030030074201c1c444003401e00d00181e22250b0145130800031800d44110041040d0030000400107051311028040d444910000c2c820080c01000c86000d02e01658030f1a0340d56190002c120090800038006581d5800740c0d00000030503c59990040d80c00b501c8120040081c0741490401d14840003c0e400501d04036003041d041800165140c0c090039541542c17003044e42ea00c54005075081c3e1401031307040300c3c0100d030034403e40c0500c000e1985030405098050701c00da0700c0b500d41342e540594813025030f54581f283e514954818401c2602410800d00300546040100809a04041c0e407000002e1519446042060501e0750ba180e090002205036440c2c1d950100d180c900038840c10b020807400c2e46260143c46e0490041045a05c098078185105400c84040f0460b25101e95841e154007a01c0d0304001e5010017800c8030521020840d00e83d030014280203503881050161a0300028520700038080e104e10100030b00c102d0450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604765008 1250 604763758 604763773
    0x81903050a03200409150f03030509100e0406030302010b1c05070302152214090f180c060c0609070602070b09061b0a060914010b06090402130513150512030a080702 72
    0x1c3c82c90030041e20080c091080c000c940500c203051501183d0b4650740140301c1d00f00f070009003400426040403c64600d0001030701c0d0b021003000085400c88008140c00021548a8245400042896070542011040940c11502000c203400403440c4100e00c1c8031521802446c40c0c010000400147ca003101c500072842c2c05940c0314524200c0c515004498031800b060f490a207210182806002e8849200c408a148450640e400981820501c0c80b84800880080084640991690500320104002d125071a1507200150100b520b038005407446980f40c4030100c0701c6500e540318104c00003c0003072001985d0070881e25840003035803a080810301400780136400707002030301c0512085221440004034204003446483d8012000000e080c074440c030f8581c51411043c00c071f25001d40c1c140380d0003c616544403000c4482c00441202c00590303e800d01c60000d8401905075001550002035511621101182d07a0007101c0d49100f44075400740003a84070f07000c10a160b803503498150b21551050107004440ca009031141c03900101280102c40301c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604766258 1250 604765008 604765061
    0x180f06030a05101e0204140f040b040c03060314030a0503070302071a012c06031009261308031204032003040602030406021614010c0c0b040e01081903050a03 69
    0x419180c0c0d401d10200940d203058204d80c1c0e4500c1c0e90b0410050380b80040540ca0300e40381459004d03070351100d0310100f4402e14100a02c0c2000d643d0703c0d4086244032074007820901580b81c481e4405401000144401d44d1032048156003582d00c003201000b1550304629070f40f80c040c00c540320000118025000000211281c0381107180984060f042000518001d00c0c07034480640003070a440340e2040710040d800c242c40d030581e85c1d0384003440100c0c1d8012880b01c44041012000040c7c103511400d00102000c81191b00e007a0981001d801d60102c07444181c01001010060302800100c80e0341c4031a016540d1085904001809210901090001e442511a110443c0250181c5076485070250700040c1141e000342d0000c00540c0c000601007151a030148141003140902000081100b480c011039541c04840c00c50496041250003140c0d5010800c401800201070701c208208039840c1c540340c03e4000e000e010280103144030303407041c142450301c0032a42020100340c20341d042e40d0322410300190300000d901600c880503140710344281c0c040c1c03220070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604767508 1250 604766258 604766263
    0xd1704090f1a0d0b15010507080f07050f030f0a0c150606030e2503121b05010906060503060601090e100902030a02030103020909030c120906090301150302010905180f06030a05 77
    0x1684103012800181c095002c02c50300420710141010310b00807010445500b000c912180b02955001166034040c620b604054001203c9511070024024840440814520302d00901c43c0702500045208508072041c1c0c090004030550303203000390504071030303486c60402400707803d288103100d030482040c0300ba2403c8060b10049240901910210380200002036a601102c000b07020f010403000c1c005000c0d4006035a8a0b280040d03224002c80114000030341800701c04417002c5e00c920b124400c8800112140303003089000140b1490031902800703050800b40da0840c208840440d00c1d283c04180140079920503110158000d191a40d6003c20300c00080500c1e8200192940001b101070050000b14030891381c1d0b040c0140d41e581107104101c4183c81c0a441d28129038400d104185001000080c40101c50040c940c415484410b02c100040081c4181421a90194201802704142540405894054a100f601c407400030721b4403a030621540c0b00c503841c0d00303055400c203071808100c0c034000c20300c01c1580011018003900d0500340b00c3c1e21001c1c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604768758 1250 604767508 604767521
    0x80f060f1b09030f100f09020a0311010c0c080708010c0e060712030f09030804050d05091804110a06082707170c150d0b010309020d1217150f06090d170409 68
    0x1502d03810250001c42c0c100086e219481e010300e2103903001c00060b600b0b5000309807000054000100055900a03001e400c076030180c2040c81400d94480000c0d00143d80322013500d80c88424a1140c03082540c00d00f600400301c41d000d84100120800007034505400c20020307031182440c10101400540506070754082281480c40a40245a10580070391180100c0b8206858000d15200c1c60321159801c024040c031003c00540d036604c080700306021042a4500c0030340c07a50700304809110004040140c1c002010380f4001034094001d0711181c4690101402c180034210480951411170310003100d58007050b005182d040c0b005481030510010904c2820003161408046240460580d84148107804052480800e007100c020840d40a90300358982c00786028840341405501180e480016980300034120000360008414882c4180120041c8955a4259148908000c0070100790f8038004000785000340e2141c22a6841030812400b128008440a0a02d00391506240c07244030340400e080030b403d480d00504000c009680c4145010f9907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604770008 1250 604768758 604768783
    0x6030120033301110303040308040201081f03030c0605090a0305030a0e0c040c2714060304080705161a1c05060607121206060e030a140a06060807080f060f1b0903 71
    0x28254042d0050014003002ca0342d001400c150f0b0701c10000c000c0006d0f44001107540107a07082c2480d4107aa100d0400c440080e010008914880c80701d01d000000074907034010294045280910410090342e02d500701d002c1d4a58807600d1300600071035000c10116034000d25591003110085064001e4500111000c4009030545e01c0b0700f42d00000043d805600c04400d120048543c561840c04405400005490b2000001840300f0000c906407040a000c030002d41400b81d154111060a54030105903007801110104103031219207580141200d28104406901100481c44202d404424071704c0b8481a04403071030f0320403030060540245981e40041c0240800c00004440d41c40340c200303213142500c84602209503450745504441c0345502050800444041000c41a107002c81c86c601c00e0342d000040b10744e191400010891620100510042c0158078000e4001103030710010410100344e4410304151009403105840e007a503941020340304803e46c0790f404000300b1403424440400e402c000913182c80d0316003451403502c00a414841071074883c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604771258 1250 604770008 604770091
    0x50301060b0316020304230112020a080f0c07020616020a0510110105071d012f010e100c4e0501171f2d050603012003 52
    0xd001d00e559003c0a520f4003500303148021400c1c645003007022a500d0b041c2649840d1202c204010740c0e800360b441003d00c00c001d030304049029551503154440c020301d4484100d07a107620088410b00860001c03184102158081d07134004003000d00701029400c181c2810700c0504070480c0d101d002c804c0c00040c651a1401c0307030380e8860035640341c48079880812050b031400d4400081600040029040ea22640c031007141c8500c0322074030001e01c0c0c0302e050702d0070520403021100d0500d466100c404102880801003c42c0540092400403450400d0300d008039160700341c1c2025200106100004141c0d52104e0407903001c0030080503915258070fa60704021001036482040183d840054030340500d55840d10070960b0408142c020107004095100c04100040c007420310094603440040513070310b000003a4648000d51040c09070022081c8440e503403581d850000c0007a034001c00b03580c240c40080d00303e242031000142e060318041c49040383d00040103c1c2000c8013080c41c10048010761009001c04a6000d412032030160120440210032070340b03881243c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604772508 1250 604771258 604771261
    0x151201060f08280203040302010e06090a060b060f220b0711100810060e04110f070201090605030c091507051b011b110405090a0614010e0109090b040b06010306050301060b03 76
    0x40c0142408001041440041c0708101860701c080e0803841d0803062481003e00041c3c0f02c2d140c500d0103d01500c22030240c60038502c64203007446100c02c4041451020306105a4040150790000b80610140d0b000b4010180101281400035940c4842d032903600e40500b442c40c7c0c040005860301c1d540404040e42000805a55096048214240c203050501a088801c4494145034079207251801009186c51158010501041603091200c00562182e8200a07828586ea800554491801900002e81c903041204280d000901c042e20006900b8007400c11070307004103507000f416407a2200f4203040c00303038420108996003500c0302c080000340080707041405401c18150f03890500c00c48440e0312070b000400180030b44200151500e45d0a00440c002084401c2034400540252030116040e698201d00c541091805031001e84480d0504007095000c1080d40b01c40f41c10f03a08401c09004180e603d81441c807049a2603c403004010030031400104022920f48034000d584064149000307c4c10301e803581c01207402d490305a031001090440100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604773758 1250 604772508 604772537
    0x206130b0d02120f0421021e280c060f05220501020609030f12060a080709020408010501060f0215060a1211130e060c03041b0602061501090b0915120106 67
    0x800580104c540021026542025258640d0340f03042c0c60108582074940e1145440d00c240240710341c1241b458121070341d1201d50b0441c1d0706152100c020b020844100c40a141c03006c0b40100c0c0252241f5025a000072410b03a81508040d41900c0c01940d000c0b0701b0040c00028001c04a500100400031340e10290820b515549a600d80400a45001c00140c8000d250703800512a42018029003c2599002c0f004528207211076140c030000718072004c50941140c20640210324004c507010a0940092003201d02c20310003041561303a81d1038107e985684101a00d001071304011044864040c0402201da0042802051000310a5488214a40240e030f036100803250001a6030552100b07140980d5148806500c1a1707007031009119000100740c0300c00005018044409000c0045014000e0005400c415221203822003003405807103800180d6507040480741e8100108042c4030708070320341d445204c0c807400b1102d411320402d0a040360a41004110701c0c24103588500d030300d030606c03000340821124031580f4020030058039a03000a0b80240c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604775008 1250 604773758 604773787
    0xd060b0903151324020310141903082206020d1b08070f031101090b0612120313030c0501060603091709060406270620010510030206130b0d02 62
    0x40301c0700c442c0c40305150308102c807442c1e04100d03a0b60b8035070b4028084807000413100d00d8408084110f40b200c2580c9440072041043c44401c500e4420103883e503540040e01502e00030b00c1041060680d02c00c000c140c80c030311114200006004030300030308600005c54820b60400c903951018003040c0241c5500001c01607010b085420303122a000003c000e1041d04250803400280311039183e82c10f25118442000b0a6400f010f1042030606204107a01440030451034001e001da4103290070044002c2ca4140e8105100300b03540340020403144000900041004102d2651a0850707940d0300c5100300e030491100c0150f0501c0640e4a0000001c1c034203102d4407002d400c440d02c0015111805003801d01500d40c220300d08104001c2e0400a6100d40e50312001500c04440d25850404400b411204a110450020040d8103803080703012031000c140381fa00644180d01502501e42c0e00130b000d0030401c5021342a00c50540d050340c00315880c50010710143c2424402801d482c207203840564000d03a501d4405003020741c4001007041d04550701003040795601004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604776258 1250 604775008 604775023
    0x1807021b0303070218192405030d0f0e0a0503010509060f01120b0a0b01112d0307030e0603060d1718010c050c041d01020d090515010f09050403050d060b0903 69
    0x181d00540c20b01910703034041818540103140c42400c1882c20300001e101d41c103844008100c2807030511803e124500d1076400d0f84802d0318162003000d04800b40280045502d00300040d071001c0229070741d03a80841d01c1d0354a03001511030b0079051550b00d401202040000c909510709001705401402c040b0010440c501e4a400700150640c1c06070000ba09012010399008080f84000042031b422014050001030100700c8a00103903408650302445000e24010980c940100c4854000c094030764112070f1140390b4018401180302902da03c0360b500003e0100d00100580490740c20010080c640c03195001c0e00c00e559032001611814440360150501c1442c42e0300029805a0f0002601c00c0b50500c0202070902c40e00b030031030566038070f070701d40c4400c8807001e0042e41d8400c100d00543d26083c001c9520306100800855441e160120518007505c408101a1010b00c5203041015100300b92414403412504003070035030026103081c00081400b80c00c01030010360400400b0700c60b000109038144078200040080e9002c00b5035848409060604003001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604777508 1250 604776258 604776313
    0xc0509180d1103042103030609060b070b0901020d02131e03030f0509010e04020301090b011e051905040819050d020607050a030e0312010e04150903170402180702 71
    0x55418200303032038900000300000e03550010300700341c400c2500c11011140746000340e5211900500d079140e650030b80c6a140070300602c012402580e007070014030b480b817140c0030541d0307014420b43e940c44108010f1320f00890703a5a11900d03000944031002520308403a03100070109a1308140313428100241030b00d104100b2003414040810103003000c030500f441c00d00d2031610054070081d1038111000c10f01100107802d02e001e81c801c0e401d14511100c010030031500c1e940c443c40a04020410320390b030075012507c1c2c100d09203000f00c4240c403614600009a0f5030305180c0381c6001d00d40c3e4001d006580495007402000e10022500043c24090300c40c819040211006145201e410060314000d54032442c3c10030b64211800b480a0b603940201141e80e144600e05000c1440e480c5a4080c51035807050107460074981d10440004560419104901d501850080c4480c00498003110340f060200c4440d040c1c000e000c12001c1410410b028600d04181d54010b00040c2215280031581509000c0408200e51102c01600017070403103d4050301207600c5504800c17 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604778758 1250 604777508 604777531
    0x60c091905120601170c010f0f121d010c110303040f0c120b07080c07030e0f0607051213050910091802030607201203061e060f07060f0c08040f0501180c0509 69
    0xf071003034001901c14200c00d1208d0082091054290700300c203000d503112495041c02101d0801c103d00080c8040428240000d10501c542d500b808514000c0510a4004000c44884000510710b5a12030307995440c600101d26004694198004c0000aa0340f1549131100c08424014003015000703140441e00100042c0f0001c10180b8146001d11020000c240d119440c0000a041595000d03190715203400000d105000341d99000f8003d102e042a40140040d107100941160384581c41e8004000303854100704401510f046442c00a1100003040c10000c4030502e0304803c004200c01f141c058019101500440c0c142401152518080b0301d24540724840c45190740c2481580c15010400340c85d4250031100e101c0707641e21011f4000c611415103402d6019600060300c60b02181410000d049603a10b05001200c40c0c45038010a40a9903118a08106500303000840d000706400103501d595501c81c0c84d03440703594101c06010000700c01d550565841441c451003480c088059541c0340c0c007500c100c40e140d80c40c00c001c0202c5a44000c00a011a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604780008 1250 604778758 604778773
    0xa050d0504083705011406060c060c09010516050d090f21060b031509010c030b090403050a0207032a090b0d0b0403020f030403061a03060c09190512060117 68
    0x480022610b48940c00c540030300382ca6550398030b0480c1c1401020f40001880b40c0001041c0100030810154007070300c0c3d2146250003c04556641c0e04c2049290b01414048401c907401c14000580842c80c5400117100030001414210b00700305074107000d0008060340da40100c0301c07030340280301c00c00803e40c018116034010881e40c014514054144055006004030a002c170b10100529001e000d41001f5041d0403145040e01d028040741d03c407101e03950301c0a02541003513690002552030017070046480c034401d00445542203402b070300f40040d036256a03408543c90751002c14075000b18001c01c04007100103102d0428180a114030003800c040c40781600300311902040c1c15640100c00441c40c041c041e94040e110b002d45981510703008430084c01c01d60340c0c0e814184c0c02c1c003070b00310303140000c1d400300140100402425a1010800e00304032405020413007141070900d5540d690a0310035448404092041103420300d09049001601e011456000d1202666403020588103802e40010030103a4104400501c2600c00708a035020f82c055a02d801858071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604781258 1250 604780008 604780019
    0x9011814150412030e07180b0109030506070f0f17040201080406090615050a091808030603190b1027020d02121603140c04141f0f08060a0f0b0c07050a0303020a050d0504 74
    0x80c0041c87d03080805520740d829521076a0060014100564001007600d4032441d106000034100c440b8900d265001c96000c590143d5200c1c4500103c00401c400003480c41001d440c3e0740c00641e92560014001c5440a0300c0d00c050b60005181c5000b02c1c84240c0341001c219030703520b040400f0040c0c00e072160303000b901c4200e00c0e080348ac040101122104d00100c90308900100e80c2c2c0e4903401d010900b04106400c0a00103c184440311800b000f0829440ca44200700380d03c0340911460311006601030384880f660203c10589000022080d03500466030081c0f008400c4900d005241860f0031900c1c2140791000c0743c4e90403a149985a4030103207a5058002c0c18001840b0400f92500303843d2401101e001030207180501d020710b019400c46c1004680b19135080c20900b02c4050704c04850346a00040040424203805801000204048041401410088007403001d4441c07418220701640d0034040421480d401040d051480d91140c14030014050b12484040c8c000b450181d4081c006d040000c6c10007d2920764900000b074100a01044200f00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604782508 1250 604781258 604781279
    0x11070f030f03021804050a15030807060f0e0d030f020d110304020307060504181a13021905160615051c05070f0b09120a0206030a1409011814150412030e07 68
    0x4a030001c1754000341d035896050188008140e019075039402101902e60102c24001124041c0040c144641814010321400c2c0340325405841c98905900d00e0355000488442045000b0f4100060012100d507005081001074130f441706c180c03214040d44910042001080c407041d0300301030050501510080c01c0051900c3d14081c0518901090740c1c12001506580e9561503409840070260300e40d001e08018580119800300149090095000440e2601d41030f074505000071b05580103409890180c03a04a184080c02101901c401c0c01409440c014106201a00c0f000821250303251601818042080703080900c000086141c0300b441c10419401c030003204c0d04505020408500c4901c06c5403030014082d18051000000580100d25000120070000d601560100c10040341c00002e50001050000e0010302d0110b60300c40041d01c6c0e0032070f10100c601c6000f41c200c3d007601c400440c61000380581101c40340030480325082851903980c82c0a00d0243c408850092155041c4000158180181800a00e030350024100d194030701811140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604783758 1250 604782508 604782547
    0xb0a0606020703120203040f060906120501060e12010b041d0d020703170f0c25050108040b22080a0201050417090306011403030409020403050c09011a040b0d11070f030f0302 76
    0x401000c4c810200006152091095400604d080c080c0f11800f035454850242c08290180100000142d200e003c00c60006400c8c010141258070a8a03000006811030081c8916284801d4502d4030542d2128000314560715244136440643d0f5248040100354100c50708542d0500800554a4007194401002400030030f600301e00101c207403d4080301e0660b9561032104140c619008003941c2c004240281346106000404101da06000e83d007d00840d21069910b031001991600c40035a00a4840980f480001e28482006e61030714281c4406014030b000602c1e1199500c04150f070101d041c1ca40141d46840c1400308101c2005e44242d10540d071381c207000e41001d0048000c030380c1d00c0005204942d4071200d40220440b26032018012034003c2d00b000a015540c0e151070341481941c440400903454000c40c6103000000340b06000c5440c0d00900b5401d007060394507107827804a80a80b907822003071600355007541d281e007801d10b075078030500045c08418860070014a601c8454103002d08032400c1e5020f802d041c180100408012035a8000404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604785008 1250 604783758 604783763
    0x708060a021c0504050706110304081c03060e07090e0114011d190f031110050703081e04060c0311090f15070804060203181e13270b0a0606020703 64
    0x1030b110200742c2800d4045900d200b0681001da072501042c84280200402d8090130758030b02d510381c10340d4880c4008d0029900d114500c5404440e03000903041080007030501e011042500b170245008100d02c1d840d0311107118410b40a650b0407010902010b01000340001c1061298010918540c2c055420345440001074040c0010301807420a40e128040d02d49210350314030b40345400b030065046641d0f001d00e8586010704407140c06404243c030700c10002101100140b03001a24100303182090b50300c003800c4c400c0f669070075900a0005020580789950604000003050f0a0303000083c0700da4000c8201064161040d40064121654042940c001035010444e1520640311142006083c0c1c1056900a061034400300072606a030082171401071841c0400140021003580c000007401d03c020140002100c0c040c0d02c0810010b440004c0c403421a1110f401401c407400d6480c05241d40380c01a031410742c01040d40454400081c80140301030003005070034124040d8520500c40d124901d241e010002c4c0c83c0401c8501d0902501941d261181d1100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604786258 1250 604785008 604785011
    0x70209060105090301060f090c080906010f0e2203051c0902060405060f0d020a020a17121504020d060305340b0a1710060e010309111002070b0d0203040606080708060a 73
    0xc0c82039850946c040001865400860010b82d9141c094520103030880030480f90000317540c0c402141c44000d020400e1412a65010b0124070f07034601d48800385114130002888400f030541c0030310007c0c6d440080505041c003203910030398034285c0d980510701003d030b5001820301ea0040054500b540400c01621010101c405650084a05549818200d4442c1401c3c4c0f0480b1008001c10b400890403902540d000070301e11303000a05c40c503060000352490924400b582c1c09050200a010301c1114046410308003001d0088821400160026103480c82c05c4905800383d81d03841d0700458480c0d106003144a051110134aa1a1a00c407440d48103c0e59017000c85c3c04000c00c06900d02815032000c10018054880324014006114422070460451900380b40c1280c1c2c0441c1c0090a01c203440c04101c201e9a540301b250320901c035401e1590ba0101e800b056506260381404405000d4035030703200a5105418010503c0e50040c0090401502014030169a0b132a0a1400200341c4031a81d0040307040d5807000100b400b00d0800440e013191b0000e001d000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604787508 1250 604786258 604786267
    0x8040c21140307150b120303070c080a090e041202010f0c0512310204180308070f12060902030105130c05030114010909020d09021e10050f073302070209060105 70
    0x1155400d600c03031070300000d0402003014401c07a01c00713115030003112584008640504041c0d412980c240d40700c0c8400c440e50340c0001c29010341d04001400c4071000e400e01e4034542c60900e0203941c590000c2820480e047d202500c40c003066819009030150309018101d0f49000d0104240020b280340a4042c100d8081c850700100c1645203140010480216100d81c2d200d41100300c1c0703c80ca414001900c0e12503112100c04000e9000303030305080ca010b80e0b004195809109850740b41e5185591940c031018122840e0307141d250160200891000802c140ba42d1500030f00e0302800c000100180d0307135450602000b109a0002103c00c00c4039007080805002c80f500b050940b81150f20040424580483c1440103c41c0840e0a41201c1c015520102d444001502c15a000c0b071041d0707100362169031000007801c00b0006045001070300e007544090440045085103100b00c015214010361503003580c1c1000b501d42e0b11b00c0c603c4405048058080020036240c094020303607045880c8030b060245402140342c1f0720b868010400e04035000309a941440000117 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604788758 1250 604787508 604787543
    0x303040c0f141302310e040804141807020c030115080303040305030a0b0a1517040b0c181305271c110f0304050f0603131415010608040c21 61
    0x804917480540c1c1d40404200030b80ca0801340b10b0440b400c10011421100c550b00d40458200f820b100658006c5800075865400c00349003022039035980d00e0403041aa0802c0040ca50220461030103420103010300c04d83d40291018810800526084440d468203049680c03030100320411030001c000c001c40c0d8000780c06150003980ca070340710105003014001c008070041d000120754000142e00c1c60308a50000284c03005a80c0c0325181c4410441030030901e48140c40280c007061403000800c4000e2408030040241c4809a003003a05604100d030300280c001054000c418032155180e00c00c010b420b502094100c400300d000c81c03c2042c41000c1d0504000e80d2912130004011090000c01420080b0700d00450111903180c01c2c0e0340403146800300719a00103450b038000744030301c1d4021866208042214079040d8156813044292450109921b0302c941c90304460359181c041d40d48002d0040c6090719008042c45c03200507001c4d01701c646401d03495090a180214005240f80d200d00249403080b01c80e000708030402d8410322147e41c1c001d040380d0100c0d603c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604790008 1250 604788758 604788761
    0xf01020708030309150702030307020d08091006030f0302010b011404050409210315060306180f020c03030702060f150d15020c0f011b0306030201021009050106090c020303040c0f1413 80
    0x64100c0c1e8102e11000c4100000003d00040030942c4005410032510203450702e50701680c0ea8081a590311000d60040b120b00c4811f603116070706c40b5034081003142c101c9050401041070720084513001c1d002540c0600f0302040e51014150240100000712200380703400010700741c01f103400030070f6801180030305807103141c45020f1401407212680000405124a284d000801c010040026004060341c0c1141c01c0b241c075560000151050292054400b11408400a181d06007000a0180020a40c10a02c00c0c407071a1f0a010103900e00d10100081c500c981400c0d00208203904121441c90003010000b40000401903000450844c1c035241c0c0180001202c2c1d01c103080c1e203c010703040c51120b8003a0103024079040441c89441015001d0000540254030020302c0c4c1141000c9150090000b141641c840e40406070150380404009454001a54001e0220034020400003400c2925a6808000d82d817805868000680c004020300c024001c1004242c0001d00101d00c101d10068903140c5405080751401d51224858000403800580c0280a0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604791258 1250 604790008 604790023
    0x50603100c0305070305010e060a03030305090307051608010f02040b2703060a142d100506030705090415030b010501140c0a0c030b100803030c07020d060f020c0c040203060603060f0102 81
    0x100c1200380425854030344000d0040104540000010b8202000001c04803851440140078074805804c0c01075041c15a2015809008086c007112501c1c80304108803804654107010071004079210241031102c0d5450000c1450075215407154102482e44100420070800095800311a0a6030003a44041c04000b1020480c246025001c070700503406d8094803007000041001580010944c000d0509400d000780c443c1c56207140341210013840480f055000042c0d44491850700398109038080c403191003c400c02503e13440800e05a410584402002c0b40004c2004003041c41d06000d25294200d034100d492000710702e140c5800892003018030400e411301151544000848504600302c0c0c0c2150307100c100710f40c01c84c03080d807901400741c0b00e030b138481a030300c0d00c0e000c201040c003860f1070441036411959100e0046080d900c2e010b0b28040c243d400014201c4c0d1040d00c0000200001e0018010b50103043c003011030068541a00303040340b60409070a8401d462107103104000300300903550788000b900e420120648030740c40d201c420a00141d01d008003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604792508 1250 604791258 604791283
    0xf0b13180b040501151709030a1b0f08040f08211c11090114030f01151716021b0102070b031308120901061202031507050409021b1203100306050603 65
    0x285070000c54601714031031403084003069079540c041400c80314204c6c1d4a101981030707900010613042045006803079441703181c620103000201d00300814680b2143d075406002c080c5450b011558008046400c03c1042030484854004006d07071005031842d45c491210040001210b0003015402c42000f051901c4140000c0040010002d00101e080018403192a90341c24513400800d1114005410b440d03409810908040c02d5900031a550480c04d80380740d0034a84150207850194014004111007200c24035018807614070748a0140c5007042603001c41d18000c2c0340090130400d424804c002c415a075940c0a4400b0b981c0014480219083e502c400c540700d44941d54002c0c090310840401406c0e8000c08200d82141d00c160381c0b00301c1d014941110007004041c4d504d02c04c5082d1424001006507254010080c04e0403c8440c01031410b0b8424101d1400515054490016a007240c02038554500801039040c0c0001c1242c200300501e09010350f0a000d030b10b06501d0240320711510084907000040411381c441d00071032143c0c0c508000340c520404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604793758 1250 604792508 604792511
    0x1203022109031603050606010e0607030305090c040f23010f1701060e070f0809010b18100801050702030a09080105280207170c010c0305010303021b1206100f0b13180b04 74
    0xb0345541d443c048a000030300090720103000350400f00b031441d070150300000564035000d04060f0900d101070301c058000b800003c00c202200c0c00751411284003581c3e41d00ca2403840a44195000940d41707050308000c2c2d04a00c0078520032440c00d100078010310002c91409100c3e01150007241e11154180240828036002d480d841c0d101c54800c040700418030030010703003208681403030a1150741d0b035803040d031745071004a0300741c54403142001e030081e02c4031501c0000d40d03004142c0c4c903031710a4414544540380c950707507440f05007101c034200c03841401604042803024569902224200040500c20002d11403400c020f008540c58030007160091525091340c3c0040e985401c182e80640d411340780c01130176103003400001807804902c5900080c803482003940303800791112459001e4415641a03030b80541c0201208010394141482000110504a922100d001c0b050052101e01304501d6204c1d10321085207818180c0307442030b090000c11407034000d100000ca040c800c0b191041c030303912b5180088500c1c00c000d544592007041303203c1004020100c2002c3e00705 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604795008 1250 604793758 604793773
    0x50405030f010e0f1b1e030604140f0319270b0306010306090213140d0c03050a020306070207030305030c21090f060921030907080d0315120302210903 66
    0xd041903201c99901c00d1002c061303c0014060840c4142c0700c4059400815041400e040c410026050240006803503aa510712080f138a07442c6040040e107444001c480484040d00c0360189950341c1c20051115500e0344c07004c58001d604000155628484400b1420050400c00100301c0c43d5164040c02c179501700049404a241c481c4116441d90140f210a51041714040d02003418001c0c0010f02c85818422604004000740400c10507600380544000c04120408403964800700e030782d170f1300808209080f10010086200e07800030968000c0314810f15040020043c4040255000f60000b00007090700030046981c1305107110b80255458412802c051510004122100d000c005140c0400107403500005040b42da500c01c070011180290b60320b1100300d9075281d076044041d0301420b002e010310510003a140041c5d5007105a14095860803500c40d03901c2880d105d000d050100000c1c1d110361100040e8400501620082e24003800b22031206001500e0181d500c00c0d10342e01c102c004c0d24040714201d0140e03148409590301d5400013070540388903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604796258 1250 604795008 604795033
    0xf0f0c010212010e10170c0f220911040513060b040939050a0911120403050d0e0102120c030714040f080c060c191106030c04090c0c0c140105040503 65
    0x60301402c4850030021488417501142819052110704104100da03001840c40e0784c0003009005031444407551007038101202240034034141d2028580040e18400c05107000650b00307101d041101504d0b038100d814600075407901d814002221104101e000c1c40d290441d001040d83e03200703440801c00404c2201d40103480445014426105400c480d00700030f4000e820b010654503200d22441e92484451010310515a00680082040010403500e4104c0400521241822405e015a0b4801856200320484e01100003840002c3c0c0002801d460344208039555031000021420225805115551110050702400485401100046400c0c0c03280301c00e0811001c15036666034440d03958046900d111165805075807000c1c002d8070031a0099007441800c0c1d5000301d4514005150300c94400300d0038081c02040841c103840948665600001c292030756401035000f155480d0381c2da9039503484d04621304110707003801c88010b081004005241300800c0b4440284019035401c001421042c04109006032403034030a030348c0b240c0d4060040300a400d0a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604797508 1250 604796258 604796279
    0x15180306021b0f061803040312050717040b03040b04020609031f141b070510021801120c081f0302120604020f01020703260405121f020f0f0c01021201 66
    0x1e00c01110000003029842e20502545900700030f80d04920550084000406101400c07400410307840c0e055041e00e1925449440b90004030709003003014000306600166803820000030b400118940300145203894242410030094101c00e11018001400700e845000c0030405541d41d040c211280040000e044901a80c500030320008131150003111105660328041200240718114500184950752031141c2e0800b88010303c02c07001c10b80d0040c000032b07100d1b8801c0c181c45c6450285103100070110480703090035440c441c14100c800109928488501d041603141000e038254406a003102c07400740c101d51001d070b588417180350080c40300030100403650010794001d02092840d00d1040c00032401c680540d009030303001019801004010f9030340f01c0c21b0b848011304901010100d400100003010b421000d00303800c15081450141c0e503034009842e0001c482e0084a441d00300011400321019024001d08096201c40c0e425410700348010968501d900800380d814441078000030301e034901c2c0f082c02e6040306c1665060568001c1301e56165440e504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604798758 1250 604797508 604797517
    0x4050f0601090801020f09060a030b030a0f0627030c022205151f030c0c140609010506040507050702010c080405090123190501030b300105060d0206041518030602 71
    0x340424078102c4080745010040c02120720340070542c1c00d0b0903c2e0101c010244580d030361100300c62104040c1d0300c000b5040140c0d010302c017031a00f80d0300810254050018034184030b81282e818030003251240c00c020348c0d598048024494640340aa4040c100b110107400b40d4000b156022520590380708041080481c40d4003408095803099000c0c82080c00106035081011050050228070120051416042d150401081034401c0e001032241010314035042801d070b100c0e551016084d400ca2015403100750051010804000424031406a2102c400c8805102c035040200029040303108514000e41084205a1f0200500051310100c03001801c000e1300318401c40d170303480083c02609010b201c0419034050004543d880c03c1e1802442500700446800940201c851608005500600801d0004d0b03030814030640d00701c003180842d514810707560b402e40c3c0020300c040c0e1000300305542100d600400041c4924128200400961991400d49082d1060124204801c41200a0984001c01d007102c40c9401c1030700c2400e02208010280c0c002c1d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604800008 1250 604798758 604798771
    0xe01020c0a0606050306010e060603101809020f1f03020c120a0908070b0301030309170a1a16080f04080307120606050909180a06050c2109061e2404050f 67
    0x208103681e04d5900301525001d0070301c500d640503408000440e40c98a400d500444d0841000e4924956813552080c0400e690321494030b0745006165114000803c0d41040500300595000856001e03500d0412807140048421414089404140d80442d0038246088104807100c0800c070342ca840d039502ca00e5055402811500344d4001c0c036150340269500004c100711100162410b0307c0e070544500c95030382c0c1408541e404092040e0401142e41c421600118045a003808185c1900c000c40c0301c0c80f003614034150000001d0140b074002e8840812503082d040202004c3c0501d5815046617001c0c0902e5981e40752007108480380503240980300009840e01e2030000d00203801000401e203502040d5052203160f0740380036811000003206c20b1200300d5030b0000c01102c0b00085803684490f91100703a5421003410034810408400c0c40640000300c2c0c551a03582c0301d0512064100410096038032031103085c000c0c0c010303205058604191300e00103801010030b624011003c1c1900305038416142d03c100380c081c008011500d03101900c140c0351003065520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604801258 1250 604800008 604800011
    0xa15080a020a08032803020d0f1506020705090a05060109030c0e010914130f0215070507080106080a020315090a1202100e0d021f09050a03050703170f07080a0e01020c0a06 75
    0xa83d030342e0102c2526041900c01c158440c0c94459240c0200742d00d40f840c420304e800c0650800051268819038840d2000e1180d088030002455513102000c1d041c0307590942c0010041d580013080402c41e07644da40c10381c0c0b60701080b54000880c56840c0d0342c0c0143c810003410341000740311342c855000219035a030103001503a0480304285418842a006c10703c4040d5803007000e44500001c04200c0d420315000c41c80b20710b2625038641c80030340319101d4182a45031240440d002021b00b11210780000c0340400511b5002d000e410007608200d00542030541841d40080d1340d5462036084440c0900405002031741c13060040c0700046071141c01a02070f104100ca0315400070348488450400428841c64083c42c1d10030440300082ca0355404907075400801ca04c01908040300554070001030040c1000c0c0d103510f0098001070301441070000c61f920a84a09458130400e10b0050b0590305680442d0306006150800c11400300074041840750480d285051038041d50300c8101d60407016103010003421b0303041d40c0002124101000f0004481c00c226009010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604802508 1250 604801258 604801279
    0x91a0d031206150801050108100f0f080f0313121103060a09140c092a0a021f090c0605090613031b05060c0c04110705060910050604230a15080a02 64
    0x101c140443d110700250500140d4040018801c0354007401d10b264000b485080036482301c950b110442c003c42c0c0b400341c1000c8020b100e0880304018200c0c0401c070030701c01c5c010a040a0340c01d014540d10140b9107580e40f4032612003144918500a014440c1654460030301490240c00d0312403038a0204600405401c06070340842d0f12019548526030002008104201c0c24080103102441a4842c182a62000782000c51a4130b140590071400d5010498640000c180704c0855030050f0085528822000d10541c09180d0740d11540e0742403c01c684009003141650405890046c00c00f04d03151042c26020413180e00503190a41c26150004030b01100384907501c0109940a00380086545070282c40d0010b005e80360080d00f1036940d055004046825451515400015200501090003400c0135056200c070342c5004815580003042e0380010500c401852110700605500100c240e40c14031003409800300c801c1d4408203210b50303507042a0308400441c010b580741e900000d4a07170043c0c101311040c1c552903200345074031010380381422403003039030541c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604803758 1250 604802508 604802519
    0x10f05010302150c150718031a06030303130b0c1605060f2809050309061c0b0a050112050403120c050d050f060306130501060b04150e0613091a0d031206 67
    0x1011180d141e0640c2e40079040040710000201102c14010381074006020161f107821001d103180418001c000e5015100458400c07a510301c642c05124805030031140650020410001807800d018160342116520170060402c5a860300148030450040b03014020344500504001400d0001c00500c40c2d000b0101d0f0111808140c8404010b640b4140d40c0f803058420241340f504010f00308581c10782c406503045005405891810b8890302c0003a2441d80034038000076020b0300006450384160303058822414428002c1e6959405903040070f0002e0047c3e091504c540b031030325403210700040c1058854061f080412801e44018001040c01e5600a011500405140e001c01480c2038000341040c0348034024680110405409000640c80386042e041c013420400da0165095901c070003000826909090040c0014041400fa9070f8240d41c121000410581c1c4140c25203120380018812642342c100c000402d41c0c00c80c1c03914880000c0010303101149005031040788183c42c0e80000c406c5801c0040c1504215141901c0034040d60401c076103500e85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604805008 1250 604803758 604803799
    0x10e030f0304150c051b1b060304150e0708010b0a0320010212160209060915010516080412050d141605010605030709051b0703020703080c010e0f0d030c172205010f05010302 76
    0x80c522190b112511003003414900b4004c0027543c01a000d0307024620500a00c035001019120b4003403202d225036005000400c40c12000b0704c80d2131001c1e003049031518102071070f48c2c58840499094054907003540c440001800741d02c0e8001c2158061403448190890380355201d011000d81e0b0089100c3e0180d000d100d0701c0001440500d0401078003440350315540c2d020140341811400440d0160030401e03d19001440c101564004900c100e00035200600c455011909580098a85a0305080362030000e00c0503c82d04411400c0d81c01602415602c0b00f241c2180d060300821500d00340305015102c258481034150095840c04581810141c101e41d1040c0016078150b903500e000e03501d04030020b110f80c4002400607048404180700068403400144100300360b50b4008a900410075000d941490604c071007003105580464070440045802d4015206409280d00701031480c1100a5a000c80c048001402d0764000203241400d48a210015000c000b41583c01500801020700d00c00c0030640140303020302043e031041645141031018020130 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604806258 1250 604805008 604805023
    0x180117070f0513231f080a110f01021218011103040b0708030a0b0405130605130c0302090a021e040f0b0316080c040b07080304060b03010e030f0304150c051b 69
    0x90f000c0000c0c0401411540e00070107032860070014084048005000c220a44043d4a026501960700100e22901c1c50000502409003a0701001694000004900105d21a0311645900b05410354464000c0141a00102e040803201444d60780c1000300454119030044003415556842c600c20b0304d0b0421a80345000c40380f0750f240901e02c034000d002d40003003041c41c0014085002858100c10784034408100035030303080b0005044d11000c03222010564000411101402214007400d600300e21421920030343c1d50350b46d031941d45040340c4601010380601c003111b01180320040150b04454140d400c510180500c9101007900c0442d070390040c0b15120b0548104000402d004100f141149d02407a403280400c099032203141c2042da100078008060000740e20051000084034807400c001407003030603c1209180c0c2c3e28a0240f4002007110403d01c0c010b4040c1e132401c1c09101900000104480b2510514100e09440b40e5551030302513600c80082c040e41001d00c0c00c0c260542c1003940c00502070070a41908c070003507158112031900256a100c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604807508 1250 604806258 604806269
    0x1020c030d14010e160516050309030c0915090c280e01080708070c030c0501060b071b05220b0a06050403151103060f010504032009090a0b0601030209180117070f 71
    0xd4040109408046008030089a2016800d000e4140001a00308078131408828102351420f40001801a2040c90140400710070070008603540866414091420f005c0c140020342154040c86000700464402d94006055452007d07840104402c0e4442802c00c01321808000b03101000400d4510b6803000096000e464a24403a501550343c2410980e1040030803100707108954420350600c861240420302060081c01104007074409000d1040c1c0d100309a103480c1405c98045003000799031850030001441981d49011b111554050b501c54002c068000c090601c0d8020b0842e03030b1b141ca910443c400d10015006802c180988100d81c0030b1300100d9074001c107181604068030184844904c0070442000010200c4c41c207240110413400d410324089081640700da90700301405084c1c140c410110b1103014506182480c05a524a40c081c8801e800341c00160040c0d9140344150074054100340c10f06801055800154032050b010100164640d00c1c0b6642d07a580d00e031100e44040102e007030301840354004c41101080760300b101202502280c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604808758 1250 604807508 604807529
    0x10603090308071b020a030809130b03150c0d0c02010614120a120c0c0b040f060906021f0902030105070c06150f18061802192f070801020c030d1401 65
    0x50f19901c1c11180105500110507a070340d43c0c802807101503110182101c002d548038100b190703545c1d071f0703c0301c10881c4800b130300c400040d401ca0910840c62402d450209600307554443c8515120025100c0a549a00038059491181d40309854a64200f40301c9a05421220468a610f20003811040c101000d000710304140540b00e0480fa8005140c1c030b400036080c02e20591507142c103803800104954081d650a00048450f500c604114030002c5001d00080750300700300d0f250090116080c894062440e080c406500c820302a0350301c405600340019203112808294000300841c5500500800031440c100c8009407070b80103c520305a40c00c6140082c03a00320140810000d0060380c1c5162a907004140c542480c02c030040841c1d00f50302c0821500e4800c000f4000700301550130042e0ac01c15400140c0c882e00710b046d400300d880e00c15481807020001040c00203120a070722440412007a89041030760004414001c0100c52a00542d0b03802718400307610006030300c0b41c400f10200180c040c06c1034201040c03011415080003444501000e02a4100c0c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604810008 1250 604808758 604808761
    0x1110050708181909090507080d02061812041d090606030a0f020402070615060810060c080c0f120409110c1c0216092316030209040902060705070e010603090308 70
    0x11940720b0494010341500030a0b4a2082c115645544000240d0350300441300251515564000c010b41841000c018100c84401030031508400c8000954a0034003400b801c641c114100d0164840070001d00c0200c120b0288407880545d6160340301c17404030b145084001080021000c540c08600140400f03e0200e000c0c62004000b441e0b08c03049911400342c0c0f101c0954040742c0c055402c01030140040d0403400b81a01e03045003a00011070706854800080c00080c401004242580400301e42400100d800821f200912604a0308143c0c80f20320784080c16282009246e441c0080703104108c002c420080d03a01e03001303005680a140c2c00340850801e01c80c0d8181c00d4002c0c111182d0898005059507601d8080d143c8103000110228411503011240d6418448105200c50f00620f00c0c5684a00741702150130801e444100c0501442007034007002c1d00d03000d0200945005071000500c105600010700f0329850781c4541110380c0b0240c0050400e5038410940c9000d590b6054148251003041810800000d500740c02881a0580035030552a111f445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604811258 1250 604810008 604810027
    0x70804172b0e01030608010c051b07030c1401051b1605040203010e072307050d0e010813200909070603050106081009150915031b06120c09121110050708 67
    0x1c070305550710b150404d40d81e51400202c02c04240035616009031562125aa518541e9200c1411410000750205465102a00030000a5202c144000844014903688050071040c100101e40c1c51280102c05902c2407401007114809840c0410140721804000c041801040d03070340d42c1403000b40c2c00240301d6910001020320008035414042d000349907444000d41c04180600010b884214401e40100c1000d82e0684c0c40b80a1440100390032201030101c051003400c0009a91500e2404841a41326114000700041c4890020722404030280b08034142c200401001c02c0c1407484c1008000d130390f841c00e03031051100107410035000180403070007005e21500601c521007604601e0303801c2004050140969519100c4010303408500002e40580034400c1404400c84800801501451410005480c45094000e40328400b00030004000c030a0b04140342220307401303003a0b030003145565000304183c40c003030381e01c0d17100d000884d03c1031407101c0801c80a45940b100c242c400300c6240448131100b20080750306010b484001421000701b0401c0c40107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604812508 1250 604811258 604811267
    0xd0809190302060c0c0f0a0311040b011206030b0a27030c0203030706020406050d06050a0503031b0a0503160b010f03030e01050c070f080a05060f0403091505070804172b 74
    0x19021034610016421035526030210b03000354841c034801c14040d0022094043c140c40c080c0c0040300340d400111101e599090658843c403000c51480383c0440d02c40c940c0c80110b06060390041c59403885200a181040103095505d0a00710401c0e0402c03200c00e681c2c0380c545189040c181580c8010310030728207051041807058001c1a40c046d20010311549040e64103200a11981c0005001400240040c0c0545d0391040e444200f055a0201660b410303800c5644501c129100a0000c0c0d00d0020668811101b410507026a01c10103d85040c00d00300322600140c0203020010310000514500c080c4a21451701c2400b070183d180c1e80c0d40e004c600803c00315010040c00503414804100a542c4a50058007081d2038405c01e681c40b1554030010552a90550390020907540c00c444d100703c0500006002450784078002c0102081c00b4540b641d00180b182c0c2c0c2c0d50080064190000b400050030350b11540c03d903628194001e14042d40e0f0f40d01c95015070036503101070000c0301d414840d401040d10404107e03500c2040c1d20300031298420303e45048000984 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604813758 1250 604812508 604812529
    0x50a0e150f06120327030d1e0e0607050f0d090f0501080712140106020d093005150c07020405181b010201200903070e04120c020f0d0b090c0d0809 64
    0x108140b00920005222018003201c101c0b2180f1215441301085803800240747c244040700f82140c01b841240e16007401460321181e01a0910713a503914141d44540541c500180c103d0068010181c060300c1640503856001500140a0908034129200c0a43d0b0b40c0d65024400940005030294034009120000070400c030034090048410b12480210011400b85001c02c41d26820503405d80c0f080005920000442d01000c1d0045141000f409605c0004840f83e0240003d40822508404506d81e4900300c98960340d05208091108405002c85684000c240d4105040c0400294020f44401c0e03104a150402090f40c2c2e4440e8080c46c41c1c0150110098010311003410242c00240640c0d5091a05554031140b129440703814500e1a8103808071629095034513180013000b41450910b10783c00c2000e800845005004c0404c030340c0c446c5019541c5581c85c001007981c0451001c110107580984266030010100740c034441c1041003410b0355a202d480000c080b640a200300d0750401030980c0d1003040140c014181000f460b81e441c107100b214030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604815008 1250 604813758 604813789
    0x504030504080607121505090c090a180e070b03090c0409060b0a0b030117030304021f0210020723010b130b0d0c0e100501030b0a120c050301050a0e150f06 68
    0x360a09a4510035282001402c44682c4000340710071280b0308900c0c401e4482e148149000c1013005080500f80008942107100145c0f807114481c1020644240c41d036544020340c800351070b400c42d941000981060061001e000b10507040b050900842002141c074814031000d0742d2003208c0000040a14501100038480109140802a2400d1341c5032a981102c1c0d4582032080c000a20000c4070041d501d6150a580c910495088414400c5a4108100f407101590740d0048040f60700c00030003005c80401e071507000180d10b8070f0701c0002255403c50001ca605c10510540c08800d05019118045140d19140031140c1c0608880032010a5544200e403429100400ca030750341e202c20f940072005000c00c1c3e4611125102e05400c240380c3e51004000e060300a04204040c0c0349000d04000400013170030144664030910300090440c041c00d0081c0e003410824010094240105200880014013001d0000c20003402e000c0c880034064a03135415814040d10500300340403c1c10f2103805c0b105200301148800c00c600d54a40c081082030b000c1658a91 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604816258 1250 604815008 604815017
    0x15090501090210020d020f0c180a0f0f060503010c0206012411060a0501030515010501200316030206101707030803250906081f060302030c070c09050a050f040c0603050403 75
    0x290740050b2188442c0aa094031683c0043c0080c1d41203010081c680082c441d240360850300a59a4103140b13844006c0c2c11007148050404810780c9544202c01000203014a011000966060a1000030241d2281e448901681c4041e402401606400101079a59040a10404103100a0043c101045071481c54141c607088465103440b40848500189091802105590011201da9110b0040080003c00c0040c02201c005140080390258940000604036882c104168862000700c43c034010340c004d10034011100c0a10f141081550034140070700300296242c204650240443c100c01e60b020554095a03441d154180b42a40010701ca1542160340d45255074001800480d80c0c844421001c9412030b0b400c6030580c2d01805266100684185003000c02046400d000c0c1c20710462440e1303506a083e07407542c02921001680d1590401503034a4541c034001c10054070070060007a142044c600c00c0401c80c161503401c03250007014015411b01542d12410030040504000381c45c0245807100c1c0041c02c000184c042d41115602500a040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604817508 1250 604816258 604816271
    0x1003050f0129030c041d0f0a05040f1203060e06031b04020702030a08030c090102010c030507020d03050705130905011814011206020403020607030507141603140f1606030b060715090501 81
    0x1540310183d0070a0721814a0755034003040a006003400702c0c031b030740c0c0b44246203e00b00c1c000d508018100c060000006000443c48985440c0082c051100821244000c2c03a03002c1141400540c1c00100100104101e00a0000da4034445010484a1030009191400ca0a40b0b040d02d00c0840304480030040203502c01c0c00d0403130b00750085980c80404201c652010711300c90107030318090990f10580600024211500050554241841c110612805640c00900f144048405060000c1d6545a8510994490243c1d1650f109520502500451006a82e8115904030380c0314070400403000c84026030381c20a030f6010390410441011414010403000c100d0110a0346071a000e1400146015102c0c3c01007a62580f0203041500031840000d4900104480d064241d51929072660140055403d0003120302001d803180d11000e00328540f04c00b40c2300c0b5130503410701100480d000c228080303ca01681d11031940c10f98245612070b210100e8505030400310241480d4084a011a61002d02d00e00c0802c00702081a0041140342c030247e800d03669414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604818758 1250 604817508 604817579
    0x207060e0706090e06040207110f1f0f0305130f231005040b0604060f090207061407020c010909051b032208090a0f03020f0d02030322051003050f01 65
    0x71680c000360a090781c0d0100003d06120300c1d448080e4000d4501c0703014074030402c0381d6404210b02c4015280c0d12030007182c18080341e034024000600754041e07a00203d10b51204c5e25041c1c2580c290004c540d00a220001c3c0c606012503919500110701003000004081c0c2074088645188000900002c0000c0c00308028803901c64a002036111400d2500d2320030180d0081c92503560081c002400179510040354003400482e41030283c00e041481a0a003190780e442101c400da500403070320703404010701500109031201d18694032403800e1070710400007581d8801c03101c10b0501040400700013144103161030141511905540548844001c0200e82c40c08545d400103105540b2403034510be82c04100160100502c2d83c0c240205041616416443c2c03c004c40f280180c0e000740801b61801030100010789490b41640c45528040302e90015406940c00400d045202d1098120703c5294600a9481090120f201010070b84200b5a1038502d1000c4425003a0116001030b0b490304846003925004001c04154242401e6002c0c81080e00c8411000069 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604820008 1250 604818758 604818763
    0xb091b03100e0906010321020a15110c03030417030c03070c15020c0c0a080114010306091b030303050106080c04120b04020301110d06031b05013906050402031614040207060e 76
    0xb9202e0150f42e0300300341c004205001d8a09a0855400402208002c01d54120390700a940c5058145000b4000d0200b1105144411510343c00300c00b4030342e000403050355141e03208180242c0707a40c0704841c00c0381c00c40140840060100034100549100745c50001c403203031560711440070544070540c03040c00840f41e400d18805c42260b0030405002400f100509000149100c030550b000300007060810f600b1a00c0640c1c90b0650308818400d00000060440341c001c03a00182c0c141650a00086002035186203206600484400000301a4594405030494519a5620599840e00d20240486114503ca10181c440c0c42c0440500414200c030526500035100030000168205d035982101100d410501c2850803003a9a80303010014071517002c00c4041c2e4216940c02da100c42c3c41c180303000a1f2501c2007040d00074220010703008400c100150783c42c41c6035580d00007081d010040041d4526142000c2c0c0b0301182c04a00a00400543e00c0740d18100c1100b550a0b14907111802c024502c40c041071000940040d034081d501c0b55222011524082c906 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 604821258 1250 604820008 604820011
    0x415020d0216060507030b151b0705030708070906120803040326180c150412030c020a090b1e100f020a0227070503220f0b07050c010b091b03100e 64
    0x298501285624242e0303c09005c0b07400480816014048c000048005d801074201220011242c0010080d031080c0c21a04003450010aa006076400d840ba0301d01c041041000041d150044a500032010f02c00d036030729a80d0161108960000041c030545017400864002402003000c10681d01c0d0381e803540302070441d107110b06a003400c105440f48041d0001c1e46006182125040c808000e10001c2950000160000c100407181075108c0c51003414803100c1d8180e02c03a070805109000c8221110b8008081000941d01d4241c071070014010b508245104150000e0550031100d10b1149402140d40014a80c10400741140001d0b0b60000d540010041180100d4a00100590b600c59004011206ca480f900401d03c04034004283c045074003400304014054140200081c80c4030104a40285011802481105203064580388003190900072000304011210720401035020303480400780045510100007407154084282c207103e9080d07000c0e03400240401d208201c162107416001d0080d07400400d8140e45640080d5610030078401080c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 604822508 1250 604821258 604821263
    0x2060103150e1f02281d0a1a07170909061f0315050a031a24010c0309030b15010f11070b1608070f15060510080c1e1902060415020d0216 60
    0x40c2c5400d0038000d5101c1003100c59110030071b1498101d044402d00103400395070540304181051110090225010301040203503400305034054400c90340400591000000381d0066202540515642d00001e80b070f9140c1510290300242c800641c80c03030300441241c011009400b810007048207000b019000003d6a441e0744844000642c014150b41c8211440340c0303103c01c140c0c4005403c590700030360300c0c001e030050041012003c902074100c24280250002e960340390030340d01041c89500c003601d1074a0207001c010300300c2d840c40071102d07284500360b988940c07000c88614180e8101c008841586d0240e48941d005201101c982c200078018905115a110641c4400f56210002c59101803001c642040502580104220014100d40c00300036440a0078000c0c1d50034400880c20005003044600304000160002c01d440c20550000c4901045000c1505505050940460f00841d40326850081110074141010a0000d00c0400d00301c3c01076510100748070851282c1d0303d0703070806500301080c080720899082100492001c10660070b10344030307403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 604823758 1250 604822508 604822567
    0x9080a1a070305010515030417120906100602071403010b04021c18020d0b060f100c0c1509150519170f0103030e0111011b02060103150e1f02 62
    0x811038500480103000a03051005250408006012681c2c40c00100c038068480e0344030391601e0b9541c0d03081ca000320300000d0380e15410705a00021070121440c40000118415007100e0b0031203c440c1c075481444080d4030510310510f001070f00004405c0c40000d201c40001212024000c0c00440e104244038001801c0f030703001c0090124000d0346c4814003040160300780500800760b07100005c0b50456040e40e801091420310f40608c0144041c581000045072603845900002e44500c014084600380e102c1e03000050907140c03a0a070155850030b1080307800928054403101e0344041c070040f5034912011910f481d08240906024030400024802c0c180301c0240c0031510360642c0445074900b5500d20203014010044030310409000f41074880d032034075000f006002194000d001d1040c40c440a00e4054980036001c00945d00500312492950044405280310b600559400600941620b0103064072602e045050100c2008540c00a842001c0b290400140c03040360507040e20303c1d8580c102500c4005441c0c040328405411500881010040300304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 604825008 1250 604823758 604823783
    0x10c110615012a0606230301020c07140d0506091b01050c1b0607020301090f051e070506070c181505030d0815010c02031c02011a090f060109080a 64
    0x1140402449800c081100082861909070701c0000301070081c036107004543d08032000011102081c0400d4084200350708a0420010359841d0316001c0c08107031704110f0254288001d80d91401241c58180708036910b1040351402412000d2400601000c0310854030500c5e5030094451610001091042c80301a101e4151900030b0424009081d440360401004420024104034041c03128054141e00020780080082c1d84000b40030440b105400011410b00c81d00e20001d400d9424080c43e101004543c10325622031602c5042520110707004060340721413200c641a4510345541c00080100058100038000700010703806003046162107621454424036528a400f00001c640d07580386955455611003403459000b500d0f0440292a40f80b0b00800d0061030000b0190004940d01d003507068003040c50380108410036015a01409079842c2d80e410804e400b02c020007801045000d0750070426104ac070134500c0c002445540c00010b28a001070b0301d46070000b00f6111002040241441409880402c40100801600144510545054140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 604826258 1250 604825008 604825037
    0x40b1e13030917061504152304050705030106050a0c0609050a1a0c07080c010603021009080f010207080a3002071401060f0506030a14010e0403020f1b1908010c 70
    0x10030b81c5907100d00b61254100007900c202d49808148260000e003c001c401d00745229a800260003030560342e10a0b40100c02440001130440b4441e0b18004003048050b0154540c0390755003050209444c1c5c110f0383d18000850410041c03101900803000340060308054604220421125075850b0215201440181c03410392000805e01d04015a10f090b002140f000010b4098143c18001480103590181c01c000078080ba1002c00c1003000f0403025441138000315001031416403030000090002c0c002002c01d0044030000e0003864151116941c0500880759071640c0000c00074542000340c44115026102419a03da5a01c16490b21000e12610400707401c000c81c10035440103076030700039a1a210160305d200007906c0d03107141d041920400100c06244440b40803600140c500a903a40e0382e200f10303000202030440c9d000070b00307062400c00402c0540410445501c21803081d001c8402d02c3d2000c900043e80d80440744001003170f00b1220191841c1ea82000300c2c800b4415280c50106070900c80e101e4001d1400d5500d517450f140c00003405400c003400d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 604827508 1250 604826258 604826267
    0xf050105062409031606030e070906030201020c0438040b010c0b0117030c010c05250b0a0b1c050a1e080d0b06041d040312020909040b1e1303 62
    0x40050040b0b4409698420086141c400d0100c0d59210038520100814000c0c19a01c1c03c0c4004080b02d14082d22980c0c6031038440d00b000c0c00034854003010706004d1103104001304180c252440b464003640c2e0160010b040c00b0146a0400003d0b10034032581c0c182e080342c06040b048040c600c4151402c40c2d4680051041c540301141c005000c2110ba4a9000703604203d071a0364000c012400c0d6a0f00b180c103582c400d0340c021103040c0b0009032007459485120032a6442e0742c64010407450319603001c1c0107000c0c4120340781280404000800341d1243e900d107400a000d1301c0d555002010401859055106928071038024040110450800040e0080f0b050f00f00744c10348580c0c1240c40c4030b030100a0105a40e15180520003c1980e2202c0240c035440c0c418001e01ca40300c20b60344d43e01e091244d400e55648040d10001c00c0040c81c40c120001ea051145c1d144044252400c40114809138514520505c1b41d0080d00c1e49400050070040c020741d071355240d4600544c40136010243c040c40400c0001248210b441c416849500800c0101c9040100f82c42d0040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 604828758 1250 604827508 604827511
    0x30a050711030f030f0403020307020a030b01080d0806030c0111010e03070f060f020708070f1b080313050102030405130908040909080a0909020f1812010c0e03012a0f050c0601030f050105 82
    0x3605410400c80c0084101c0f103281079079040004003107041010b60b240d18069141d0b01c00c0010107035005103140303400420000700c004100d0503980300c04d00740c40098228000948280340282e41280c1d040d0030485410030f0039442030000780ca03098901d00c00418404050741c411425a44050002e40352400307088a18014000c00e80289100c0354480ba80451030030b1030315228845030b0700841c20014225618201c0d00e000703000b544034000c54000010300c454101740c1c1c0d840140d195079920400b031202e40300b20460000a0b542d8008400e41d011144058510b03041d07400114081002000300b03140480c0d001d4030500010030b06203202d03c03031480131502c80c45502e95103042106014040d1750303103503108040080c010409500684054010741e0480c21441a41c00360580c00360b000200707c0c11451813014403542c80d05020840c810781c13081c080a0020404e03002000044900c807510707074070958120310502c0511200d20301c110b41c25102b1440c03001d1a0324036140c1242003103000b490450401c0d40c00e074429180344240c0c02c800c1051240a1090380d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 604830008 1250 604828758 604828787
    0x819022506110a0c0627050a06080a0b1503040203060a061a0f0c030a020102070b130f060506061207032301030503040b032206050105010314091e1e1c021b060a050906030a0507 77
    0x700c8011f14000c001403a840030ba00884040100c00e2000c11a4500c2c0b41d0820f1503444d02c01804d0303214500750130180c80b072241c008480c02c2c2d103c2d1041001041d02240030340304031406c1d03900c1101059000e0b8001c040e40501948140342e01ca410b00001c004111071100244040c0044000e039600142e80c40000382000106440060b04144410b200c854441000aa500880d04080b40e800040803c15640d8100000c801d402920586155540322404000c420b541c10760048101d034124941d00e481c8240000a10804007000740801000d0740d208000a100841074a00555804105801d0f410443c0154a0030b9035500e00000c10201c0b20070b900e500051180b0368040c0142010711300300c016880070b00c0c03500c4c8034030540c0c41102d03802e0404001c0c144030441818000500c00880a0600e00e403003203140c51701d28400c866840400030788400c80e03803180d103404185440c408031b600d00180700102d100200000441d802c002056104030441c0003401001c03c41203900b621001c010394400c5000c608001914a8124005001400c030903102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 604831258 1250 604830008 604830077
    0x2701020f241e161407060902030d17041103070b040e0703060909020d0f03030f020c0a020a050603090a060b06070c0324060b250819022506110a0c06 65
    0x80300c02c0241c851900650102c00b4200c0740c181c0f107605490544080080012002c0701510000310325041c88025044158254400d07002c882d100204098221401f21002658100d2404440d0119012681d8902c60000b001001000c0c6d6404954464050344140c2c4168015500100f04504101c07041f9010700c2003000901c0c0f049024030081b6650341c0054000d0400320b600400e001307082742c0b92406041c03103544031240c81040058110f41d9103440c54422640c40e40d855031300b00d12800c10b00f400460315042100540c2d0198041c640148010005a07517580007810300907032500d41000b010700015000c180c9801c2124000c6004002c10062851640d0045898000b000790329030f0340504100701080300e005050200d500c031000d0507000742603244034514404050b034006900a03101c0d03400465406080021900304040b00013154007124600c0f03240036585c0742c045404440100d02c19240540400906000e00201d03200d5440020542d90502d07140e50741c8417000140f40e00480001002ca2550034804240c4604a1581500ca40729 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 604832508 1250 604831258 604831291
    0x9050a0605150f060a1403150f10320304290601120c0306090e0715030519020901170a0c020d0302030c030622050702030715022701020f24 61
    0x3c514140805115030340200c00025400382c01ca44581e0810042d0700e640010960351f410a00c00450b00604481d0b2160b04c59980040c000c40f051600001034246900c2684a80207a0f00380070040c041a02815020301d4116000c15034a40b1404140c00c001b14407403849150004804d044ca4214001075003089a88039010640c0302003440026038000d01404445107010b0300119603000c0c080c4044024105541c48000711600b418002030100201260020a54111340f02c401c100d102e8240040b0141d40b010355090000d041640e4103142c80c0b210980050000542c18101826805060340d01c4030103c040889481030506d58402201030141c2e410311034060480d103070346415429405d000c43c40f00000d110150404c0e108031805070f40907091007210b040d41c100c0110450302c00c00c000e103000392000e522640311020840308020824003181010909100740c4000c5084000012295900001005e003104070700340c40241176226521800100c0d07401001035000c01c80e441d6451900038040d18814080c02a0050b2814036910100c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 604833758 1250 604832508 604832551
    0x9060203040c0b12061e121509030a050406030b0d080c1b03010c0503013005010506210318040b0a06090810200a0c1226090a140f0109050a0605 63
    0x240540c0142c3c040307075036001d40c003050107041080d240350f506c500b41c02c840c18080e07a8400e01004915406201c4221320000d4003a55401034503512407156240041c00b1690500c411301038184294007903100c0d400040c10300c0240d48040d4948462030b811040f00c142095000603800c000c038210030950003d0b6080160b0013440506c06510740a84130b40030500a0700355a40341082c006480b40301360300480f01181c22034402420000b20500b0054042c14003290000e0040d102e03441c1e07503251456240031060314240e94070040e506001c0207805551114003007442d07090b449515200c08600d640e030342d10310800081ca016205c018620b498513840360b05110074803801410142c5418482c1814150114007402690022003840349c0e940b98065055840d104a8032001d402c040c82d090a65031501d030014880016407450040702c0c80c103005841c8043e4244c64085607500ca1940100d200c29000803000c07040a030101c65098251880b070884500b403e421104222400d4a0303680c03117501c0000c10302c680c2e031049a4101c1d5902c1030451802c08203e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 604835008 1250 604833758 604833787
    0x90309180e010b030325020f09090a14150c0a090f060906080609040b01120602210f0912090d0206040e0c0a090b12060603060d0f0b07180509040609080c0109060203040c0b 75
    0x20308114054081d0f080c0600300719501c1c04008403e5888c020300c040501e043c1650340c1c41d51000068000c48502445001343d10305900002000030000030500308607400d42c0d4034141d5041c80c640003200c011b000c5c0003900402064101c501d565010107843d03c3c0e03607443c40d42850228020f243c0700000d40518003a240440a200100b01240c4456040d02d0150303034188071600052030482e0003449200e000698840c04000805025904012224022122a0072141c0c0f0394540c4007010b80c884409071141c00181c54204080b10f60303818080040817030b030343c002054a810151b4402c08080c034060220340708925480002451040c60750420813220280103001e58143c1401c040c1c02400c1c2d07001402801c014860940880020650f6844442148041b0361041d120080f17112a80f401c40118802070b609000801c10303446008010004071490b540848000a085065a0301c0b04c2e19080000c01e140b14017503907501400c002d01c880d040024090620414421500180c0d20310742410618800c2d20385820034481c42d101000800007291a8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 604836258 1250 604835008 604835047
    0x7122d0219050a0807030c0c0306021801050c0c040b010c020306090d0906050c0606060310121a0c0c060f04030201062706050a080c12010e25050a0608010603090309180e010b0303 78
    0x70202c80356445e2030070304040d2880c00310644003c1c40070540f00703408000c12105801070071100704084113540c4076038011001901c4a0188016001066010103c62000303486c040e000078000c0b8070306041c43c10003d1590380100782402e404940640c080c0c1c2c01a82c80301640c551108080b07000f40203c1c5000d900703040002001c00d0300c2d20809400300c1c0c803481000c00418000b884a200f4070b8000c000380c145102d80d0044900e402c008440a42001d0a4248903190024040030b01400450384000f14281c090810381e99400d0b5003994020b0060001e900710341d0f03940b81c00714400c04440c085540c00c0000c04401008020400b110301e050701d001c2d400080c00f41c070740580704200084001131203010803402203900c0850b141c0301c0c0c16590300400011034001590301ca6500d80c49005c20380110f400d041802d45c044d940242c5030f200c1c024020b04100c01e220701c000066461004003c418400e90100c8140c1d4841c1c503041c0c1e0000d607a001c0319192000c1c03250051107469990305810222400922034284404025000785040c02d180650141c4a4140e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 604837508 1250 604836258 604836263
    0x306010816030f0204080607030c030e120c031605070e0703060b04050f150f04031103070303020d1209061103061f051801030207080a05041e080307122d0219050a 71
    0xc200d00d50011650003500243e840b0001110219200c80d52280c80c15550b400c1613400d140424601100c0306502ca00c82d002e0080c0403d1040001d01d1000e0038207065030159400390410310130f03500081c44500358202c1061440e0350a140260010b000785400d050b1f005000c82009400d9030241482e0100402031540a00e0554080b9407086030b524011074850b1010802e826940070080318001c800283c80c1048007111320151080e240500781c1003080090100c00d140d96001a4040074026a0240c0c0b2000700080c412101c04050300b10381d032008207080005503212000e5459402020342201008400c20a00b420000b9070504141c1d80d4105082c1c9451142c070f030142a1b4404d1504010a0f21440545601d059000e03404a402c0c1a9100d000b03295200c60011004cc01034026001e460740c5244203c0c00c9820119002d51f0490507544944046c5113406c10940d2002c0c90000c41030200d400744904001001300484802c0c52000d06511105a920700c080c5110b80028100700c52403585e00400c00e100b54014011400018072408440c0d0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 604838758 1250 604837508 604837531
    0x105010c050f0610060912020915010519050406080708100e18150103030e030a080a080a060306090609020307090603031e050909070201060f060903021c06020f1b07050603060108 78
    0x6210708020782801030b081698185480341c0d60520401404090b401d03c11100395540340729400e911001120919002220301950010b003407004110382d80c40701e400507000b9101c1418100d20304186801303400904607070092290007080c1c020804005042e0400703034003035101d8064509810585046401c8000c0d0039031038001d50012089180005401c51a42441440342d43c0295049501030401810f548a50b007400340801c400051000c0450358080c2400111864480c3c0d0100080f403c041c400c1e00125100350004001ca1440703030b1645c40c0000461113612403011400d0096401140c2c2010b24014035140c002ca0f81c0c001545a031134104100007003a405100401034604410b6030390050703100481c040391107010707960445521841d50f006129019805500a60440351461b011188041d60352000303489500d601c1c40041e41011280c03140145c0e28100c410f864402501c00c000060915840303864210042e017051442d20201c051070161a410b4201c20045080101022590345203149001e000003801e051000e0090500c45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 604840008 1250 604838758 604838777
    0x70609050607170c070806060a0801150e0402130903020312060909150c0c060f07020706090501120c092304051006020c010503180a150b0a0503070b0a020313080303010314060708010501 81
    0x100740502284c4118150108a0b00c8460304ca400080e21520180d0724148914200f40000035203410600490b452a00782407240d188040c030344507211440800041c400c991240c031007006040c2c07208451045036a0030340654001d6456441d142403141e1003a0380506078a114bc440d102c1049140c4000040c040103100320341d81c0d00c420301d840b40c41030106a401581240e04a0b4000c0b54100907440310300c98426032042d9403960888180c0c40d0303030741c0701541c03001c885000e41800281801412441c1c040503410540345401649090001c0c84e50342e02c1d4103800a070030000c1442d080c04009905020342d10f0240201c075002100503850004181c07a105010b075a41c4418001c460502c8000300004880001d40303400041e105120000307460798040c151900e01100b00d40c500d070904485103010550700090410303941180650750050002c1c00e8060a000007000300760454441c5004512040002c802c01042c2c24030400002c000b40c400540d129411868000c40c2c040ca40201806c055120004118100b5880342c10581114401c1c02d00c694032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 604841258 1250 604840008 604840043
    0x301060e064f0c0c0c15110d020d2c090601120c081005010305090c09041e0807030f08040c06120612060f050615040e06010c05010203040302371403040f060908070609050607 76
    0x78030318441141050740c0a223030150f00381150041784589102403141e079000c200940003405d4001101440011243c14010542d82c1e0031142020b610075a0002c005062074000450451030762410b4800d100c5400d400282480705102105098540d245c020b86001d003004d014034034103900da0703603603803119034424a10403030760f5234041010301441c0403a0380350100e0100c8904240306e101d0700701800d00f940124412000922801c801803500c42c410740005002da81d0102910380564503240d0100c90f10a070a110340c1014607980d0030005044080e08200156441c416040410014009114002228401400c190181c0b00d1004c0b00302141c82180219820742e10454403410103070f01c032200121030440d00c030030004003c0d600c0042071006051300011019411a460700b1034000302c510010302601c802c544120990414805c0c3d02c0d1b040005043e4424600c0c42034100001c030380c00c1c26039a881da0150000142d202c2008966000ba05000194090180030060119828409036981c41d250101c1d00ca0310490402400d103e80e8840c14889 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 604842508 1250 604841258 604841267
    0x20c0f0402090307062a0b060409030e04180b0705040e0121020d060209090702070612020d090206070f150504030504030f020d0b01140301060e064f0c0c0c15 69
    0x20b00303400183c2220b204e00d032511000340583c554500340c99681c42c2c00d1109070301c411034200c0540780d002c2d03800b1601c2483c981703803031041c0806410700180440900607040070b40d1009480300e10031407100000c503441221b0f40c4003240c02c1400e15103101038030110812000b000f040c02595100c030590f40c11204480c01040c1060004402031a200c055154025406080030228005112850700604030303100301110500d2003619203901c2660b59801a00c180d0380498110314426100c80340d240d000e884030071216a8041000e070070035030001c1d02a90211030121104400a0380f003605101c001d101d108030b00144004100481c2c105034030040d00600a510000305401000c40c68681117440e9000c1c1184c940ba4488651002e55840795000e10b01c200034001d00f43e00a620b440304c00510740035480140d034003405002e081a0080c03a401e400f02c0d1015040d0042190504407075881e6690b5800340c80b504041c4a0781d51029804110b0070303842d800c00c10b4542c2220300404104842c04030714041490000310400301c80e07082441100404d002081503e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 604843758 1250 604842508 604842517
    0xa0209040309150507050d0314010603180b01032102010504020604050909010b03010c0201020a1814060304080715020406030c0f0822020402041203140f030c070218270d020c0f0402 79
    0x10022400f520b890182c0741c010000e40002ca228000b5144581c03081c41c4100c3c203d801005210b0f6100b084030004220107806030740684034101221802c600101000d85030b15010b50700a03802102e88140068000d001d50b204c0d0071701e55407a4241c84c402403000c1d0405800040c00c80c007881c0207641c0b01c0c1102c1008225031010275404072500308005802488010248140030b8003d41003140000e0210300ba0104403d05000e00c140300d40b05461600031400d1419108106101e1a600014002c40394210100280404921405c103002403120b041e00340036a541e42056001401c4e01c085003004020b001eaa0500d01104a4108984135400b42c1284c0750305e6402c1d0548840610003400040c00a50414400180410300134004180c0600c807501a480e0340d00c0e4080300300c1107007215106440c003035120010240007060507469400e00500f0078500041550b422405071101006040070140d500381050000c1d040c804100c40381360783c06030089418080141003034080c035a60281d1510740038811a0303c40d0030b1600108040c0da0311907040e503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 604845008 1250 604843758 604843769
    0x302040504140f221502120a02070203070509070e0d06061a041412280c150e0303180123130906081c0e0d05030c0318040e0a0209040309 60
    0x744030200c1d0349148a40c800d0000c0da2030040303900807180019198400c8a0a290480381d01403041d21000311340d51911340c0030320748035142d0720116902080081c1700700c40c120a560780034036021080140da0340714504c100b41c03134812280d0000c1d01400524081110150300b000c0d00080c820010340314880003202500d010380c0101a5030700036502000300f282088500024200107007064480031043c1c1045110484200001141541c410075410341c04808a00c2681d10400504626200d64003030094410341185e5070100090515000310300ca10044042e510000360f880004030020b1b41e000d0700a140742982d00dd42d5403140c882c1c0c608480e41401039041c964174003281c10004a00c01c4191001d00c1d81d8441500040e480240001441400700040c1840c81c042480c24000c600403400d203041d001c0e0b08034606103800090720002d0340c00358502d50041d04080d02c84086401840149849400d22016641d2000c0c080140c10b01050011000340c0524503190310324101c405c002800c920751a4048600401643c0d852a040b1000d0404d43c104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 604846258 1250 604845008 604845011
    0xf040221010f09060b0a0b040b0703050d1107060b0103290607080310030506090c0a060311190207060201060f05060717160b0403080a0905100216080726030910020a0302040504 77
    0x100c0c10b0500507907110651251240c201401000c40c42c0d010050800240c0c00f0720f49450008200c1005031500c1c400040010a1103410400d00f840c113100744041c100e501ca42d80b540d41030f620005800042080c00c0c8140f5907030002c2401c04010f01102001002111040030f01c0f07585803007103244240e8241e03650320f070240d81c0a41e40c0100440c1c0e5030714040034240b0300a43c07180310032140c074461500420200800400c2d480c84d030500203000101c84134030b0020b085010300b00b10402d0110942c01044404100166030200004000d259001414000d1900c4002070071100244e01c00d03408400314000600080d81c40d60102c9036810f0300039100c0c0800d4603044505952034441c110884058895440581e0100519103d01ca4810f0b806500c412800d5600c41c5a100241e4204c1c4a00a0080d00101c5042c413403404240c4c0981041700f03030f54100c80f0b4003da241d500c54031590301055041d250705102407030028045404001d02900c51a281e00410304600f0301c55551660340c241e8100c101845234011480400c03003031081c0d0698004280040c130 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 604847508 1250 604846258 604846271
    0xe340801051302071e110a0b0316030912081005120717010b0904060c170f07180506040e06041d10020a050f0a0305090f0f15040c080304060504060908060f04022101 72
    0x90f0040a01400c05d048801c0304c100318002041d45880d05c0a0000c941c4480c408a1856903000c250411060303141c2b040074203055441c2c05200100340325a065080d400c1079a26000d0380c500b440c20382c001500302c0c65803203a4407950301e1124561507010003140324421500c003070302c03000e021492074a040703030140038600b01c0190000010b8080200780401034101704070501480e2621001c1034070b85c0054441d142e07000c49207041002c2c0e01c0700c00b1440c0c0c1ca10503505c0424100c858003d10001c40e480b00c0018010341d019910540d500311b400e1051222520b082d20881c545603030004900184540f018103040e482e444209850301817954081140707081c0502940032a5a00340b5134011142d0f5440300307881d0180c010182919003070414131401c82100324054000410450507280e8000511044841d49100600000003c00440342c05060305d20018500c08204041d001414040d2a420b8446040003001040c4610355800322109500200500c81d00f0f14108103029001501911074009000c0e200c0d24a1104588011184611358603141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 604848758 1250 604847508 604847543
    0x30115181a010e09311407121214030901140c03130b09010e100903021006230d050f010624120b0105090a08101d0d0305100e34080105130207 62
    0x400d45d41c1c3c4034841e10300e241c0c80403c0c0000b000d54440c41c41c01f40b00414500042c0550119600d2882020120414500040108814660740740903410640c0c4505041e91100f05210302c00390b05400340750b40800041032103415031408002e80100d06029110140401c41e07000d0100726580300030b4015445100595049a680e9103200f00813034010540010140c0040c001e9a85100b100c0c500e40c015882110310007034510b20080003440e075041c110101e4560455000d880500f0341e00c0015000e0080042002c10640002801032a00418460303008100c10703d0003c03402c14141802cac0c40c0f82c0103d096640d1201e8110001707440b0207060010f0b2500d204507110a90721004540d0009101c22000542c030381c1c00307450181c061041070b0001d85510b0020207007070555050360300921070b400c108921a078070540c0c1c49140d9128150b40786d40d41c1c000e4407012140c280d5041c103101c143d03603101800c04600307001800c9001c411003100b020145e008032402040c2c02c8060140d20b00c03030310240c0c00c8080041902d8060703d010a4010050802c4045403d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 604850008 1250 604848758 604848841
    0xb041b0503461e0c2a11090c0703201c02070902090321300f01031e08040b04080109020f040e0d0e030115181a010e09 52
    0x45035104114960003070244070a09240607070448018082c101c00d811690285903080542810300c801c0c2c0070410700b10028945a1595201c030782174005850ba04100314043c508041880345d078280d0803180075006800c1807201c48080e00c0c2c11070300b1154251819070604000100708102d407400e503412a041c6c0e803152781060400d80e15643d04440f4004402d4007251003203603032041e03500300342d01405154640c10341100003030442c03a2400094048200d80d4200d40203103001d60440c500f1603e0a0720540400a280c00503491007030300007103000804c3d00b101890308401d40030340c990fa54242e00c0d0002c0b006d0451180b42c0b200390310000c00c0080707402e903006001d5941c051500c039511503050350700800d04034805911a6256551400c07640c10030b4460400d007004250302038240000507100a0711000104c00009415641c1d40000e1560765100c2280d040182c82030610901c60003032a003000800341e0b1808042c4400c043c684000c0c00304103a0708a80615040141501d003888541d840560408012540e402080446072090040e0b10868852 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 604851258 1250 604850008 604850101
    0x20402210610180603150306090f110103200a17010602010e0c0a0806070c0311070303050a1d060a0e040f0c0503090709020307050915160b09010b041b0503 68
    0x54520b8070358103448040c2228810010181c491000203000c206000c8940310707030480d40038068690800110716030707130343d035074504941c03a01601303581046100034040c0c20401c44030024a101c500900c2c1c18440c00e88140406607040c84c80d50480d0490003000101005618020310460980316902d0091840e150ba44d040068044d0544034814030303140c0900788a801083c1b401c0742c071034415100008010039090342c07580300c25035154011580a0f0144803440811022041041042c031000e58031a980312070301d8891411014144001403500301e180084034000e0201c86c0d89a190030745011441e44e2800c2d422882c1a000801e000785184249280b0702c505040e240403009820070021030049054004a5801d590f0300c08401c4120701007601e40200144041050150358030f041101c8280750030309038250b145003907051000001c0c10364903020704540400302882001401c680c20b20a540d0080016a0280007d00740d2640015460f10664281c200340318020000c05c511201c8034007101d01c8019000010040d01e00c8034076400186982 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 604852508 1250 604851258 604851271
    0xd0c030b0115030911040b06070f060b0103110c12090103140c030103110616032d0801170c06090d0c0506070501091e12110f12040e06060901170402040221 68
    0x4080d0b200c0708656100c1d204802c0715039000074401107000c00600400c8090040203017550380c0aa42841801c022079801890002c15612616000440c21404000941600d1601d00c5401110303a05020303024601030701003a006200e0309072402081c0e4501007880140c0c0204540540e010b12018090200300f030892141e0f00a6060760b0107445406025550941000001c1c4940f254042c82d0705188581c40d00000d01604000c440300e0142c440d504014002486820710010680c0c44c0301c0c0000d41c0070001001186c910382842440140090301030180b03550304401040d034904c101d0340c4e803e0280e1600400b01c024445001c4042c4040c2c00020301d42aa43e03102401d00501030800d00000b5100c281c01c900701100039409070409480b0003903108892411032680b03000143d5400007034a0005209018110010500e0401400780315201800101600c1e00e880c107000001e40641d00041025018401c01c100103000b9030b0304015a083c4a8071f1000f03034103500c0d81d928400300f006070003021600c1c0151402607003205944148500890711515 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 604853758 1250 604852508 604852529
    0x1508011a0f090402061c09060c0c020f03030a0203091e0405090a0b0112020d02060d0b120708010e0f0604120306090c050c0f1c0e010207030c1706011505180d0c030b01 73
    0x119034400b084001841520000e5016100300074007002d1000d800750a81c0c3c503000b00300e000102412191070b120f041c0c40d000c0200703c0001d580701e440c40086180031700982a806005400844c140300e100f000107540c074070920001c10b00c165508124042c1c8a80d10b06a40d08401d14090700900050610810340f0365114480c01d0f044484040c0c1c0c10001c03850080111002c4034040d0014080303c0045016028010b465028180d10006580c54081c68100c41d01d9000902e0baa039007584008044180c940301d8a41c2c2111140005105c081e04021648901c3c0040004c1d03a03908a504402d0300003003408620070607401002564080c203078090620840043c0e198010000d040c020024005554252000e03451140c0c95280986014183c5910750b01c5201d041f89c82545112a07003881801140c19140d00c035221444140c0031035102e040705a01c6030344064040842480306038010403010001050282148a010b00710340160707107a44200c200c1c10a80d900c00c642e10001d100000c50380105025810584034100b0307800c8660240078541150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 604855008 1250 604853758 604853779
    0xd0c080d020c010c06020f12010803030603100e0c011421060109120c06030f0e06041506060c0807020409080d050a06051005070b011809021201150b0405131508011a 72
    0x407030000c5900e040d4080705945040742901c03a9070f00d000094020010340a000441404691003c0440b800c4040c06030801c90700950301e070300c0d145040514200d04050305401880c240080111840c00008561002007402d0034640300c503052401c83d00388640120a0312901648030b0030f1805400803021461140104800c1e620082c0b01c94441e0020580503d0400c0020a181600c51040043c0380c80f035800318100014680d4040781058030104224036140c0241c40c01d43e120a05580d0095048905204180042c5001e0a00c0700303003407041d510f035850a4020104040d02032600e603480c050800803c0021140740d000f144a0070425402c000c060b80c8014444c900400d4011005400c01c5903810340a10241d40c0707080c1c0d0105030452168240b40c015549400c1304000010201c1d200c0380c01e04016541c82e89211800390b104000000c0940660448418081e00e07544651500c0c102000700f03000e01d4450b003c2194131200c55120104140810340c001c1c441d00b801e29801603106510707011a840e01e1b9241c2410030088000101c901c220344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 604856115 1107 604855008 604855033
    0xa230601051615050f2802040f0b0a020f011104050d05010e0124060801120201030c1419021605010507140a06090c050414072c0d0c08 59
    0x220045a06000d10400c903c0d104213a03102c11083c51090740740c240610951441c81c4241188480412858178540c1c5103041e40d0103c07070051510f08440408141e0319800000c0a8101c0c41c0c80c10014003a98030309850054050184044000765002c0b054542441d000030070140000140c4122061354031140c0201d12071394203110700200982c111a4141a10040e60221800d90030700390009400d002ca82401400610f02c5581d406940560a08000440580220301550420101815400040c0000402c1c1d001d03681446100480c880719134088603101c5400741c1030300201030018001d150006806208840100d44500e015010840320002541d44051650f2030303681c1034540004003580c1030b180f030180070005801c041c8211480d009044024400301e08101400a0102c0700e04801c10010b0800701d0544800c1031005540882c0c0150300510745441d950007890400310041207032144403814050138071121403 = true := by decide +kernel

theorem cover : BRFrame.Cov 604676258 604856115 := by
  have h0 := BRFrame.cov_init 604676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 604676258 ≤ n) (h2 : n < 604856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
