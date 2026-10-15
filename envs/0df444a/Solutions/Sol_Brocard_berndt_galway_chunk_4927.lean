-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4927
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:04.605418+00:00
-- url     : https://prove2.me/submissions/f3826ab0-e71f-42df-bc38-cb86c9fd5a0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885971223 ≤ n < 886151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885972473 1250 885971223 885971279
    0x1020315040b030709020307030f1b02120d18230d0207030f020402070b190507030c210e0604052a010f142109060c16030c08071410060609 61
    0x4240000c4c10b103585500310500640c4040100b100f425819001300c070542c1360f0314504100c41074507040d094000310424030120001da88500130620714618040018040700001120014100030210400c8029001c00d281c01e03110310301464a040c101e80e1861055419084a181c0140801142d4160186d12443c2510000d499010550084010354035203030100c8403a0359204865405038030b0a8915980480f10490300c0010540c41e0a00161000c0e00a219041c03128003d038075980614883c09556424100c085011000d8154403034503840c03e100c80800c5254010b0f48184050480d07184a03507001d00d000d003c01d003c8445680000340a01c0c04d640d030003901052940016207007034591100201d0b500c0d1003a1140307407007902e00c0850442098442d0141062094010145082500c050351190510000300d4043c1020760303001080040a1640001c0c0a01080c01070b07144643c0e1514200300c0309480f40000d8076180e24001c6031680100b02c0383d40781c0a10b540f19140280c0345e5400c002d000141403d850703002802004401c0711099900c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885973723 1250 885972473 885972491
    0x1a090f06120a0c0915031205130b03012301020c150304060209031207030215060112052a09010809010b01051c060803030c0d0e06040c06030c020a050d0c120e060702130e100e07080102031504 83
    0x9c00c0b041c0001d40105492556a56928192a58400c01c03140c11004134206003a400100c03984003040c0c140f5200001003884854042c0c200b508040c070380c00036104441c0c0e2039082001e101151024400700300c211188000f09a11200a8200641000c84d080c0c007a0b00007078022410040d1603078001c00405e81004090900292603500d01214002c0e08400012441301c0c0300c41160b40110034104071703000f042071100a0381c9141140d121a45400d0903240740700d80781808144148418140c0801a03610702c40c8100080c08085039959031010060b003554019112201c120f0380006449605103d9070142c132010346c640c4401803246c0d103440d885404402c0f600380100410075884045c480d400c6482040f0403114190000140d507032017180080e018040020f01081100c5c4003004124075455140a0140449805405402c591070a01940c0c01c100d440c0c0c07001c21040e165950b49001c40b102c40c000801000552880b010000500c20144044403890f001712540f1031800c03a030040041101038060000c0490700c07040161000300d05010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885974973 1250 885973723 885973747
    0x6080402040917191803120203040f061205150904031803080f03010602060108030f0f09210115051903060908090904030203030a1a090f06120a0c0915031205 69
    0x1e0420400390200c3d441034844031054200d83c0081ca03108014181000040c540c0d85420f0360f0340e902e00c0c19003904200300c0c50000c2020030246820320303411038040d1041da85450345811032828602404d4100c8400601e00342c0281c001d0301030303078807890341c1042c80c2950300d00c000745003800081d4000c03200420003410840783e072405414005404119601071580b001545880358104210a044da0304240310380c000601c166800002d00c00e0b00841102c81c85400c90140c00d00d000c0200003103103180d034010a2485c0e0005507003d02d81100500054440385c1d010b60880000c030714000400440007180005405c2648100000e4501c0f4084560880b400c0d000c0340d6000c500442c0003542d908103481d181c000e51607200d800120b01020841016404002035101e144e00400c20042e444080e10021038243c2c102c040c00317400c002e103100811318801c11601c84503400f00000342245654a69038040500b081798010040b00c07000882c02c41402820f80345d00800024640201800819a10b551034102541206100d05401d10030009101d4072846 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885976223 1250 885974973 885974981
    0xc06100603060b2d070609020414010b030106082206020702040f05070903110307051206090609030901050f0d0e0d030204140607050c0d1406071e091401030b030a02150a080115090608040204 83
    0xf000391381000c0d84400c0315042050181402c10422449189080c00c148050202c999103e8180c6840c60700c11425603092000c00d035031002001d424a0715024150380c084054056400240d0a00b07072041a015807111110720510040d00c0b5904a081031041c1020b0070400c21951091314041200d402c141c3c4285410418404603080c070083d500120f0304420594080c0f80151000510103004240410031110f8a90710010f507603031280a00002280001c074104175400d200f41700b00e8041d2560360001e403030008402030b0003603240d494070400314003103000700b900071604000907141c90403500407400041e541145007615903035a4a44900c1e001003414825640b031801d00c0c040c0103044013010703515010a000c0b00c0450824040140800c08a50095000d00314031f00b2600401d0307072040d00c0c104100e9803054804035003241c4803001500a8a0b1890006030107100c0d46212802680d40d20b520109d0091580000b541c1d1003c098100811450050308a041000303000c180555015a0000958048681500d008689501c8520024000e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885977473 1250 885976223 885976297
    0xf110d1a030106060e15030f060105030924070909050903070b0415020304260a091a070203011407110d02030913020c1b09090703051e01110c06100603060b 68
    0x6600e007010100e1035176080343d01a1502e0780112020543c3d890400d40c01b040b5071000b11035031500d0b40390082c04180720307501650140d40c126240c031041d0303118074a6520400942c182d1959881002e41e800340306108a65820106a0000d8190303008240568035003420040d50300d1184002c020080342074803000505006200e00e0f182801010a00150364030b04180c01d00280c0032190b4160860020410003100740c1c540701c16012501600b60586900458900d048000c907212910b1506041c596401000540010b980a10480e0030044503800d42d0740050619000050000c4004074100010794000700300b8000b0035400005035628048101c81c52034552103e03090800c0680203c0a40200030712807461180c1001e0100048000079541c02e40350b014113075a40f10080765884e03400f031101a000350406034505801200c0e001c1907507020340b20700c800891043c45000ca01e6499520460f500d03c160340000083c0b00c100c4680760760703c5000781140e1405126550605030b5043c0385202e1540c0c111810703207010a403c0c43c01240b5146145034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885978723 1250 885977473 885977479
    0x180c0c0d020c040b0609011b02121009050606061e0903031c020d050609062116120c08011b18080d051308011a13020412080d0f110d1a 59
    0x4803114038010b5a62820006060b116505101d83d4500900b0000151646098143d441000020294910546500c1c2d1174000747e070025983d19843d01e01e40c008120b511000c101044001510f6155810142d01303000014050070b200b24004c1025604480000c4e0006030b4100f600c148055884d059400000d1448c411070b84403c9408100c140f0011081001d41d016140f130394000442404581d45050402869510031640c1c0c0d80d01030085400d407400300445c41c0e842100d0540aa0880d29080104c84140e078001c0061b51208c80e142c2c140e804c0320001c2082c6521350b0030081910303400a1000c01030075105200890021900041000039504054010740807030f448401c01407090405450f01c0114401e0014103c0d44411212400a900c000000918540511400c080380905500c1c40c0c560b500cad07070020403121009403015410313596000c0c08041650150308901c0f0140600c02c0d1b440d548c0d00c458140b03404094402d1900d4142216203456032484042c01520111289503151000000392480061280303a9101e001e0500c06070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885979973 1250 885978723 885978733
    0x40b0306090607050a11151504050108070612021b060717100306050411090930030a11040b0c0c040c021b0909100f150b0712030b120138180c0c 63
    0x680c0d000104109406800143c241715188d4222070140020380c0c400f84138002c02940030200c01c00049118400d0141c0e000e905020242c0ba010280551815800005860703001540060003800803241d00301011035007828424200c142e061030034046403080c0e00700b688005441ca9407680006810081200340e0060174a400400381e40d15420003020546d40c5405512000d40e08000709108084000308294071801c2504c0a032400f2455a614a05003002812140450050420b821300010171005000781c040d0007005800e01c010070203103411200b040240c41c90103c2d4002950007600c02601c8444c142c0344410b81c02d0109542090346912818559840c1c00100020084050328109203250b04080c5138003d828560186030400030300c1c03503c440300841c15120700600140107a0020368816503107806900540408040100791000c01e541000040e801c1d160fa007894071803100e0022080d68580d00b0710902a001405003242c681d580d035191500401d00440410305014120015240080c201100c900d00b215003490b44141030b91 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885981223 1250 885979973 885979993
    0x6020a170d11030f040b0705040302062d0a030e0d08090616021f091515121112030901090f05100507060b0406180c08070c060b0a05040218040b0306090607050a11 71
    0x2144c104090b1800c598401010300803e10861040041e6000d40f0f030000d2215240c54000300c0380046040900250b0181e0702102800c61880c8a540303800780c0301d40c03030b0141c4000c140060305020071800c100c0e00c64402014000350303005004030001c002801641c0240100013900840b03030110070992400c00078181c05d02c80664941c1040c400560fa070b410030300360b4510075903800c4d6014144034200e00a0781c4410141c09030020071880f04100c045004c510540c1d9113800b4071001d0703964604050200b00710040b03c240c001d00c2d5a01c0080c0d24049544c0c8480c1c2c001c001d204400391188250304103000036040d683e400043d042046804102d0500b441141d611001241c800100108a0942d4400101698990340704c152145140b0b4139040d01e0f4042c0c0600c3c00c441c4034102a5a44a19144061b6100001071050402071a0850180c50000c2003d032281d00c0140310070010146041c4503245013104005c141d841c0300100758003a8200005200300b103500050765130b4104440342045900d072660924101d600ca0302c010380c042030300c2c46081e40352 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885982473 1250 885981223 885981241
    0xf0210090b040f060809030909040b0c0c030d0b1906142b0905060937060f0f0f0e070621021602091311010f020f0105090c0a06020a170d1103 62
    0x144112581c985030180e10f561b41e2100b0b03540301d001c3d20140503000142c141c002000140c281114aa116400c01c3c841b03800c145124014901c2c3d40c2005a640a560f075484d10320144500c0c02144c0303060b80100404414450600b4203800610010b40000b00781ca0700800858002205a0850a03820b00490740d0000140642d1032110504003a05001000340e40c80d0050101041c402000480c0c580c1e0011000081c500c081401e81c940c01c00465140e84070001c00d0444c0c08031f0784001403074600540501002c002c401148482d0f2030003040044072410403540311682d01e0402640d00e0024080380800031161a8188000f070740a82c14001d4010040030f0709003600c4144002a0042511190300071170000364002e58413806181e859050108114106c41c0300905001044035541c42d1644c1b00c0d8010407441009441600e1400d54003280803800d640e07003a603007000c0741d0304601201c241d1414820381a9004000303d200900000c1444c1c1c8800f0b05031100402c0f0b00d240e40900150146491383c458102954911940c605140d480c40d14100e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885983723 1250 885982473 885982499
    0x306090f030305071b020d170c0a0308010506181003020708070b100f0e0402040e0118080408060705040b07060e010204150810091a06180d0c06030b0103090f0210090b04 74
    0x101c0200b8580004103400c00d10030480219503203c10440c01e1420f810396000c000c10700f010550202da000b92a40d00b03440401c86c601018000322100030740182080c0c1218540508000f034140c012901410007440111800c0000d02d1000c010b11605840c595104140624100c002c3e1182003400344c07110030006001000c00c40b1200410744645c00d01041c01d24502c1e202c012110440300c1d02e1040f0f5061414103c045000751416512031031317407a0920070000482c02c189400121041e140301c40150750701c2c0004901000f9807a010700c030742070f400803451030702a203000c0c2801025240750080840280560740c0d00e8000281445003541100e01511014050241c18011101b0082000c030307088070740d014140d620200c0090000c03400d002e44266580780c0c1d007507411880700001c144407450f0003952440c10030038188810707a07505840d203203c03112219000300781d0708040c0d42c20010050141c81003103842c2410589016400e0000c500c0c40b411920340c45a0403180c0c080c2d8188540011543c0e618980c211200d1300c040020001101401c2c449 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885984973 1250 885983723 885983753
    0x80c04150504080601140108012705070309060f0b09010b0304050102040b030c0c0d141815030c1306080f1b19020102041401030203011d0405030f1303020f1f08060604030609 76
    0x4111380d510ba03294850050404c4980010340e01166480c2d0060044911070700500b200c0f401d4042c2602e01c100b58200b200b400760798050340c2c9080070030369680b28201400014010700c40c202074059402d0000100e074101149084a0500c2070141254011011500b0080c080d01201c0003088070201359a168204040680501c1d4060b940f00840c40c0b00e8050b41800b4070b40502c1400c146240c8031b100d19824147c0001c0014100f904103a00d01c0c0d485410703003100c0f0406c2c008041c06180181d07000304816444207803a00c81306516a40030f81058041c0407400d41001461a0405d4072180e0103000040f180d01c40c070050007269030302c0d4001c03540344e8402c17950304d9180089025415030242048801d81c48034446d12111312070041d000c0344400c1c0554140c5003410705500c03c3d80c8d159a0301403504180302d00203c07860800030b0000c0f68980e4001a4a40c00d100309032900c200309610f0080340352034050404960906034140307103061082c0c003127405158030300501200784001006555000d090b00c001310f03005402407003035422500d000c41c043c0312190 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885986223 1250 885984973 885984989
    0x120c120310170604051015080105040b041e050a02011b14371b1d0f011d07030504320d030b0a060804050a0c150807030b0d03080c04150504 61
    0x407482c56815140040c034240519040809001e58081907003071752000e0b0031135107000300c0d408441c6003000944040c00d2180901c91801941604079a081c24a850140c07400182d06070700c22190704408078004590049407944545509081c0b640140720b07111500d1860031000b02025000e0031050800d043c2031038000c03a110028450000340f208960810400c00c5a00e440c100007e108a0140c2418400000f00d06003007040f8254028600c0c4000740d41d07691080d80000d00200b889004e030402e81402e1120850650203102e02412074010310908940b0f200322400315400e00241100101611078000c54244100d40b8240c400c00d4548010800b518a243e846e03460038580c510070049000d00ca01140009003500c00c1c801c04d014440700170041420310b80750100882c0c144901900c1500c3c2800344113900400284200810402003008010107040d00b9408600a0910000144a5024141080c00d21500c1e40c0c0c80003007a07030300c240c1d040c141840c01c0d03114031a8a901701e000b250404980032581c03c804283c2a5000406402105c00c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885987473 1250 885986223 885986249
    0x40c1d03061e040503040b0313060b031b06090d02040509030c0715020607080406020c0d0905040b030105011419090c03060806150a09240609060e04090203120c120310 73
    0x4040c190340e81011240b00000100c00d503030705014180401c00d01d9030014010000c690a1540303820f00000325600c1510b1b1009842d84d01c1a80008100290240703040e0200700324090201c0c407018031041c000c4d8620703c0c42140c2c81030030300107030034140e90b0f0b110105a0689900500200032610b8004201a0b580d8441449a5000e2003148000291000000b501c0c0e11815001e60161172b26449050b030a943d958005801103800035003c0c042c0800240f005c010b0507202c6846039032070450701807420080c0421920b82c00401400f07641800f00501018003450f04001c01c0340000c2d5000041080c04007611800007201e5000440010706001c160941c9a44c035800201c245c560b040f047c0e640513210240c012082199481180750482c02c011010440446203921611510032640d11208150321342c900b80000807003460b0805404580708150500030a984071341c10b8200d0010541f41080b42c1511074000030358480c01e104086440e5200040e100c0c800310030601076012070641c409442c64403420040200c0c5945103590042607035000311 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885988723 1250 885987473 885987527
    0x41803050d0e0714040e0307140304050909011a0f06070b0a0f0522020402090f090412020f030a0903080307200606040b06030c0d0b0109080a11030d0203090616030905040c 75
    0x41420f104554440b0f464003840d40c4003d05204c007a2130713403003500310242c0030600a041c00b0410b03a110706008040b00001440c0c1d5241040c003007000c4800044c00004c1983e01d0180074805240340103611414241c0100c1e004407184072148001000c5214061000b4000b44585c01440000d40080c0c0214402105404c010701260341c440a0003800c41e09680c660800e90032a040b4001d0144c1032650052050302405841d05000c0020100410b0f1609003d550480d1240411058000c50070b03414816071a90740c0304080510f1820000d405c00a1101c0401d000152950000101080d06d10740030b000222920707400c41540f2812884040020364403010203c51060040f42445802403080c0303020400c981c411002c030010981040d9400e0100c1c00200540e0012070305100c4440b0700811445020842403880c503100f41544113001e80c0c19801d01d8103004034000d40e40e00755070060140c03410699548080e958480c1081d05017004540590404031a41512a80020782007460182003414007039100d8100c0341c0c1c0c20360881503c56640305c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885989973 1250 885988723 885988751
    0x106270f12021206040506011a0d0c0807080106031506180801181202030a081306090203330f0f09010f060f14011103180d0b01091e020c1b041803050d 66
    0x3124010306c2d40d08082e0050056426215806007109070104049041401507400304080794099504c58001c5006201081200c950182415000d040c552a06014000030384407000e40c0745026000d1780041c0548074800c903480ba60040c100f8401490558000d1102020701c14411484988510b000d030713001695034890701c160710700000c00c50f081d1004a070342d100709a0b80d440045c10006102a80125601c03130b00c90038424050b0750304020468840c14040424032010b1458540340751455424bc1c10344c01d60b42455001c010725074541c3d2465941c81310f1804a101441d5640c880207600400084207200302d00d500d404004140d405609802405641318111942c000c60791300e500550326080001c0f101e180540c8200400200030b100c640f21003000300d201420b54082d0030010b41e5214038010b0709800c9038041c01d40e2543c0d9440002403c40c48410540d055100071890145410b140540740c40412060a8030a2441c0c603030307840c15031103e03032004950510130509500b00351200d180082181d071055002211040c03d080010300014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885991223 1250 885989973 885989983
    0x1270614040e070c0323030105030c0901030803160912050d0f0e030a14030403060e0f060711070303080705090402070c090f150e100513090204140106270f120212 71
    0x200d00c29549011951504000c90f203210590000310200038406c000c1108200c0c0300013120111200c88121251030b90b0400041c5468648407110f003901c12200ea41c01003011606100860380c00c20b120f00c2c84c8840d010700d580c8040e512114294062100240c0c1700c4a20010305c2070110b01c44050400a40e42c1003c607107000101125001b01d1407101d103900d90040c202e0344000404482c4a0610101c0d0070702928105a0f4980f1500100d81c0e10502c5902a0307080544182c54034402405800d90019850a200003001c0d03030410700301c1c0d5031241404002c05000d10600852800c901800540741d280b07100400030b41d0b5916252400180410181c4240050203007400810742d208031043c02105880c4100071b110082d224504007000800714070243c400c44c41000ca0b800c0105980c2c0340e0980490642c1e241880c049402c0807a1710500084850b00101036602005000041c4041b66101da00d5281134403a450900400c0d07070b5110003143c010103440d48890b0451102d10b400150f80310111070460402402110510040102140099111 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885992473 1250 885991223 885991229
    0x6040b0f010c0507170a120906140d02120403030c08070f0f0518060f0309121801050a030b030706090e0a0207080306100207320f03100207020127061404 67
    0x15100400d0203040303510514010031494001c400b192034843d5940240303050011400784140312134003d260810305122440020310000c201c5440d1900c100c91a0080081c50001c003d102c19240000002d101d0740441c031150155440282140c07a5928076040515001d801065843e048234017103070f0180005401a0f001320103103e80e6041c10f481d401900010a041100d60b0741c00100350525403d500742c2c1090041d10780e04041d2019620402a0742c1d03803400d010800926000411032400d4402d1000c120240c0c0550704070107a010fa1070000c0c02c100e91108040303002034014080c00f5030340c9034143c4511700c400075500358030480c0c131012a02498012a955180d21001109900c1100c5000e40141d0080000c100075041500790040a00100c1c0306a5036260344590394a8503140c400400c90011040e20903011005004183c001642c00400f1617500310000120302c003103526020341c260714803a456404074484040d6401010200c0c480d0010203130924002c114507100305544101070007080c0000b100b4100e51103202410701c0440d416 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885993723 1250 885992473 885992479
    0x301060915140d020a0c050604140f0a050c310203100501020c0d020d050f0a0303060509090d0e0108150409080a030e15060d020402190201050403180605040e090f060a0b0906040b 78
    0x143c0a0840e10440c0a5401001900c003006403030386500020400500040c0d000e0391250203404038051682610900c5d02c0c1c80754010180503044000004001071001a4900240b401640d2020f1120504152100c00d508071040310350070030004042c00c0002808582c000d41c4a52052080003403815110001242d0707800702e882c200d0703030070550b000d0005d4091303e440d501000d17850f0311034800c80d0b1070701848000c0f1604016480c10104e02103030315201d0520091410008280c1e1180100000b086246800e14009101106140c405030500020704041004054500495401ca40000d002440b4810444c0f402c8401544a546141d00003450040b80420000022841041083c4c004060215a80741c28040102c2c120100300100c1c2d0040d07080003d14140044d622440d00700032240e400001d84c515250a000d0850070000c4400e50b113022a201d000c0c0b041940240a881c169120301c0040c0da0965950b803161032800d0f03090000c0004a10503003007041005003a035000189468029a10b00704107031958000c2c003099408008003180c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885994973 1250 885993723 885993727
    0x46060903031205180a0308042916090932130602030603010212010905041a10060c02180c07170301050105030112031211070201031112011217030106091514 68
    0x1420324903d420454122115041203c0c848003400451840c10000074000c602254515082009201900c0e00e5048410601c10f00c11001407800e00d509080807034001d149840d000d405d2080c9011051240086001071710510344100b01d901c40064000442d4010030000000614084454406269000311043d00444660b07840812084446d07466101a420003040036030107641c2405456040111482164000d1201480000c0d06003064242040306048081140444100c04c800340b162107007803041c84c4401c83c0e01038078041907020030610004881154113440740051007100000d00c84048040c8000700f054a01c0b542c2600580350240e0680b0206000901c2400c0c00f10318180010048050020481c8000c1442454018100d60001c007049040300e000c80640035a448002c5070220071960140715208045c14261403050a10440d002c46019241e814040e84400f8a2400301e0b4204000d8222000c241c3c0a420b140102e40320360711303070034014101515442141d0b542e09400c0c0c81c41c40514011144005c0c001020341c0818 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885996223 1250 885994973 885994997
    0x13030e0603040503070f0c0312020604031d031203010806010806090a05070b0f13080f0d030902090c0c070f08160b090306040311070305010609240b07024606090303 72
    0xc001d400040c01900c0e103010801140b40010002407940f03102611566500c40c05034207500f0500c0380b5080140344041558419010f01012a40040ea20084922140c20340b0501c3e80380341010030700f0309141050010034805e0210010802e41c00c0400d1550581d8522012120b2965802e00c0142d034544400d00040c107260001300050040e0b0001c0801445c8140c1184012441c0c0880c2100548941d240d81e448001c03517401581150000c0b400c240b28a01c94a00760345414460020250001807450b10040c0c0b00c3d4155600000f00500c0307820301805000d00600e0800c0700c0c4480f4a5540642c1901c074108400c0b00d405a45200c0c50214100c004c802c01e560b00070382c010340104015a956901950540300c115819889481800030010000d0000d0007210041c203910400820014084005d0744200b00514158140a0700c034040c00340400070b4880113072041d46d9011664100c6030546080703a8404035130050791250405940001d03403032208107001042c00c06258620b000e64019550f030f410403500c10b0080c6c00010b00140240c1d03962 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885997473 1250 885996223 885996229
    0xb1501021c0813230d09051807020a0209041212091a0405030f0f09130209180c130e04030837020910081012020609100c020a0807090513030e 62
    0xc0d540001c101c030a12074040441c1e12641c0c9074182034084001941385034a07124202c80380500500c0e4100c001810603801036420180020400141403000c4d000c142c50080004070414800c02500c62416005020701001e0300340b50400142d142428404100403c502d1941c242c0044440c0c807490301c0c81034220f003c20000000308902500c204034040c0054400d0700c82804401c0b200f050740801803012540c0d516030a42d4403038902003408071a03250b10008001c03052061000744056224109040031400da1904443c0450380ca07009004942e0140074240c100c11300402034041003602c402c062050085000b038540b1311450340e402c1c0400e0800112807138040600d6032a0030500b0f00c448140f00401c885031003113000160400740c8010201e840400d10000450006d10741105126145e1041040303e03014000c024091f0f00140c2641d004034160340b15400c00940140138000884070a184500c1924100f10b500411480d144c1d0f6031809040d50302c0025005907594145000049034604001d1620b0a54035645038690007205031070700d410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885998723 1250 885997473 885997487
    0x90803030403091e0b040b09040e16050904060204030503032806082112070903021f020c0f13062303061504021c050106020d11011e180503070b1501021c 67
    0x5034003480002c07000105d8121686805403001e000c6030510192984401000c0105489001510010580140c25901da00f1001c580380c441c196682a100e81c50306448502d0040d000384100d901c007404034040481800b07040e04151450b03401d5880b510100407507134254820703040d04035501d520a801e1194401001070740401c6400b06a140c201c1c00601d2400e041049403290192504405c0710400000391800030b05004518243c40305240b241c4410001254140304500d02030340c1c0344841020140f1a183c1c05c203410b0340956501c40d0102020b00701400c180b00480e44d4206540d14281500c2a4039000c5200e00c03c03e1643e03007000a5800d1003905152000c2c6442e002e560180300095000c801da0150040f40b03070008054150081c0603140c003d042c154014042c1000c14000104900260210340c156a410314240607a40004200380600c6402004030000c1d41840c400e9106102d4400410024141d02000c00d8601c1840350189000303225504581e00f12051001e0f081c012a00c81c072001030384140445040103454050b030702c1b03220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885999973 1250 885998723 885998759
    0x40909032718231602071520010c09030605090114010e2502070905010f0501020c0f041e1506110d03021818160311040b130b0f030709080303040309 65
    0xb1001415420303400c2010b2108481419000b1000d4446090240458440c1d221341040c0d0a244050b04030b06007044c03840300d440c2c01c24419000c00c010080c003e044c603a0690300464204010114000c2000f5200030801a02880325440305850080c0340c01c1c0000d8038008103004580e0400d190030845113440e807c0c1246240fa455003d081103000d0001007510f61024295452540f8259a05e0780040c1419071800d20494243c03070741600302050304106e000c0300b040380341d0f00042c2260082000b04c80c001400d82072a40402c0060100360011003005240401c0c540381800170303510010851058951803414a03031a5001503d0b00708240c00d080c00b165120b9185054168400d6000d00720740c2080c4110781200c1d641d0300c2c00040190101c1100030542d060b051052220644a20890402c110414202485401242a40c003551400390303110303845110000103030300401102259210000361501c449460384076818491410926082240e0316408116203080c0491810000020380e4400c9901d0382e1035070070340c0e800c11011401c0040748079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886001223 1250 885999973 886000019
    0x1b081e16051c0218091920030a0c0f06030b10050301121e060506130b150706020405030304150206010608060d0609030e03010f020306041503350409090327 68
    0x62a031600503941d510030009500d1340c40742148003604220440600b40b103d480401c40d801b84012008200003011211070b00d5040e6982030310740f1540c4004c500400d0501c0c600c000010311158a2240124950100302d0340d6805951941d03801f04060030003102444461200f442414002c14010b1004001e000d20030212132001034420100c1c1404005c1411326116100450303102114415219410448242401c81014000303420080040c44604110b80102d042400030203030000808000090302402e010f80d80d01110700802015017100c1d5180d0340c800044a508044030440c2c401030088900000703289224400a500480c80104407850320f40842c3c1d0b4020040c040080b048040c445161485041ca98080c07040d800703070014100d000b680d43c1c0b5140382040b0444130f0342c02d04400300310307400341d00ac0c8042015603c29540e005212162a100d4040388408103000c880c3d0100c10910b4600b001802080410081d0480100d443c440e44a03841e12924201c510360581d89003504001c100c0c00010010440791841c1304a02081c00041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886002473 1250 886001223 886001269
    0x150207050a050303010303170a05040309061107170d11030a020601050607110d0606090c020d1b061b05220302181902070803010e01170709091b081e1605 67
    0x142da140d50954100342d00580110704011408000d61035070301919540180301d080c04000c10702e007a07640988440d5983c020741040000350740820ba405402000b440000c1c05030140c0c014001620744518695807200c00240100180d8010040407880800006892194016402401d0305030300304028081c5540080c0c03015569001516200349650b125a240600c030300d4020740c2d0100301c0c0e90400c14030406850380c41484000715444401419419580a516201100c000c1000c10b030715812141445030241c81c28008009006900001104880c1e0b0004014039006078199100781104031404d40d840810a0345100281d0410f001c0415560845940c00c17107541e02015040403044500120703041c101c2281c0040a0403540c06900000500040d0700240c42c0347d00400884041000501110690301d48034106485900b402544448025040020300c0845206188121440d03110181d80e45108a688440d074070b0045d0302c080203030b801c110301d843e4000c0b03503180c184440000d184000514001c01c1c408006444e10300548982c4d09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886003723 1250 886002473 886002493
    0xa060806150412051615030504050f1203040b0714040306022d0417010203071b0f1a04030e12120c07090207050a030f09140904211d09010315020705 65
    0x201e01c040c0010709041c2d800070103c16541e01c1c00354a0013030140c0d44025020800c000c00c1104907110407844a02c0d10580c500801c00da1114682640340404a51007582c0d580244070b12031202030488005540305600401004032503898030201682c03068100b00100b045141c0c00c00062011a41c00d8009054180f03c268400c0c50144200d0400d00010424446c021881d8500140801c401941491105142e12098000314074504202c3c0002c0c2c16031022040c0750310160906100d040a01c2145410035040c603800640e00494034405c071840702c2d81040c0441c0d044003c50043e80d205400c03418030500c00205004c030a001015959000c12031100c1344d412540c928503e500c1039400205440c7c0c49400034015041c4a4002010000220301d4094400b0920061003800c10904d4a03081003410b544040c054a48007043d02c0184907502c13203040544441e40c00076201210514201480c0451031787c40014207140012681015002c00e820208000c0d00b10428400981124400c00e8034614001c1e440e40180101c0740704e00102c8039030b0700c0c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886004973 1250 886003723 886003759
    0x20d0203061603060e13030f021002030403030204051c05060a020d06050303070501060602010c14070f030509060c0a030305011a190c0f08090307050409051c051b030403140703020a060806 82
    0x1045403440354950305007070000d0881e80c160207410060700545030a0086450100301c1caa2424401b0b141c041c081000482c40c900c40f00c0d00074000e00c0e20b001d01c0084195036914141c14050042c0d802441440d0064141580b4043c44000101000c007000d54020090a1039459869485c0042e4101c049003010706540d41400117181c0e07030100020031946101e00000308545241800207400c60b103070031040310180311000440e203801886060486a4a9a001d5640400c0c1d00da21b0500310b80c0c034020b0300b00030350700a01c0010302c02070070b820006031900c030b15440ba5406000603a01e0b000d041c01508401c5072001d00b0340324103000c828445010040001d9103c0c1d243e24060710081100c1d11000300780302600c03c095135066000111121a400e00b44100806440180c9041c41480c000355182d680da0f80c1c03822048465110000361381c070070192003a001c4501492145c900c00d40401a1850190388030707407240c84126480340c03068688101e581ca01050200880c1e4006000000f0f2500d84002510400c400400d12540450101140c40c01d4039 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886006223 1250 886004973 886004983
    0x3030a0525020604020a14091303030b04020307111b010e090a180320120712091a0901020717190302030c0105040f02120106150f0203040e0c091f0e0409020d0203 71
    0x7072a4001c200a04160040c40782c0c0301c0564214240844d411011031030709403222050303650804c0e480540c07100380d0841410200c00500d50044002d80c801d00010078802001d9000703100070105100d10f03081d188061030400420310012803004105001c110601c4415080346001c48501d50301c903940003000700701c003880d00a001c04920b0706441d080780421100110b00c0460080500d03100d0480c7c021900404040402401c0341615024010700104801303d003442c03211205200780c1d62a0010060002950030481c5006001003880c3c1014030394900602c191a0000b50008410b4030064500301b00710080d01107903005c1008003002c1c5115440c00e1303007588004c00445542340d00900c200c030300c42ca014200c4062144c06c584104070001090705655001a0704001040c041440c503921084a844501c2c01d0550241c4100c44041e400c0d4011907100c00c6400c03217038200304042005001c000300484c0600710342d10200070070200b0340681961005d417107100000c1c034541d03d100c0c202c1c02c05521103144a4002007100b91007440350780c0003078545 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886007473 1250 886006223 886006291
    0x10020f0d03050405190515070e13020309010b030303060609060a0c0813060f050c061602070f030c050108091204120807150606020105090d1403060a150e01020705010c0503030a05 78
    0xa40c2c0c0e04108001c0c060b040c4000390042ca0005c94078400d0021a40f80c4a54403108584c444411603c550003095030b03140206016600d82e180540b4519500d09941d20b64002901300b01c4d880d500650030b002e4440c000c0d280210480e803042d40000c21440c1400102820700010360840c8222506001d101d8901c036000c030340c82da0040c1207659a04c1c1d0b140c00045091500003801e851986c80b080d03003445414401c40c0764044000c185154059030001c80c00c881070410f40001c920300b84966000d01c40e1241e4110010080c0b00a4060540071b0322070a88a0603500e4031021222550b81340e51800035407031540140414042801000c0ea004481070240e035800d81440e400307484e1401c800c2c00042c000540d090341c40408020302038085c02950350102510000c0e000c0341c80b01000140c60311031125028440500e0001c0012880d0b036420034040094403a45942c0301c420040c4100141c90240540025030251003104000500396119109507001e10b03920030f015604585402545001034076014101004800b01305617002d441c402000d01340045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886008723 1250 886007473 886007477
    0x5150109020a030f050c03160203091002030409110301080706120f0219020115080c01051e0406090e01090c0f050702030c190f170d11010603020d030f17060102070510020f0d 76
    0x540d00311102c01400300d45040c460120399070f04041c2040280c05a41c41900d03130200c8c18000d844c0b5440c64002040341184074407100943e204241c176204200301a0f00002a1040d0380c90b003481000303c24169215507056000c240b00da042c147d4800340c0203202880c492009460010031402010a104200da551403060341c011900000e0450602d040da10f011660900a0a5210030003000c01700e4042c0c01d200885d9101c0c161b00001e07074140a40043c1024014104c0b913020a00c07901400560381c8c640342c684200a008a5092007003404007103c8100105808107144269904054030f0f0b2210780c4608000d03081a90181c22104041c0c0e031501400141d42c00541b2807001c504221211908242042400d000ca101c10020307032a08050241b03207284403a203524820001d407046040300b40e402e260720030704d03c00c00502d4007604090308000e4101164000302d500709600a5100c50b082d8005032504401c07005000c01039010403204440c0e160050b0b01c054010005801d0091382c0040400b01c510586403000e01c4449a81d1816540400182c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886009973 1250 886008723 886008727
    0x14040807030813170a05070b09060402030601090b0102150712060906060912021e0d0f111c0c0b09011202041203020d170105040f060512100e07030312090515010902 72
    0x10181e0007800683d000188048001d4003003660b40303030030043c801c81030342c500644000050003181450043e0300303840c9207690061485031380c3d10b031040c86e140c5c0b2031405842c200c0c040d2080e8000481c1001e501e01601c8800c41c07060b4006c2011440d1a840e02c840b160b805090801800540700084110068902a80003c0c2104820210300385140c0780c8001c0c803010b803591003042400c040140200041c0d6808000d07541072081d0210600310002260b000485461038000c005000940d80c440360070802c9108100f0300500d00040780c61422407001c80228040a1410203801010000004014441c494554000d4a28940107140c0300d41002246c080300c00403a07000750001d0f07068030804450f40e002c169041041440000407403419801c1e502c0d90282c0340303000c1c2c4418082c1c1489142c60354441e032800b07181d40c1d11407401000700030403c8082100000045032184442c80c0001945800c181424040640c001100c0c001c481c0d0607a2050024551034982100801000754101c034030780107040e480b01c4840041950a40648100b40f4016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886011223 1250 886009973 886009987
    0xf0a12090318050a05010212030a330e0f2703120906010b04180b011e0509040f1509020f04031a0f070305060d030c020307030b3909010f03140408 64
    0x6042c81035a038402442240b03418800d10003640c0c00726070407201408054003580c172a150410b442c40076001c42d40c51502c2c240d00ca401c0c00b0303113405110101c941c006d284048044154941b1280603090500d0304545680000d001f0b0404074107124455410050b4010092944840c40c6441c80d0305981581d00c41c1104141003401d0505204150b0740910045006002911405d0b10f41450a0a0510303a65004000c10022554806c0710030b1080c0d0184d803024900d085501540c42c41203d840e140580140c00944009004620344000003500440c4d921030362401901300103071611424070b0840d040d406544400e040b80d8843c0810302c0000005600309100c9001001390b000360403003916000320301c00c50401d801000318041504020a2110310380f625440d50f88040c1d01481e00d08400388841c0082031500001d544010844114801048030918800104951184800711442410051551100a1150550f0b5600380c1440b040040b030403550b01a02c240c50300e60307801d801c02081020045914000d0590115000c0c0c604040c001034030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886012473 1250 886011223 886011257
    0x90307051203040b0412020304050604260a05190606030605090d0206100e04150219020c0301060e1e1b0327010507080f0a0e0a050109050d080c0f0a120903 68
    0xc5500c0c00d100300445046140c0f903254070401c42805480600651400740045420510910494001e02405031a40380d48556500180700c00780c4070074850499802e10b82841034012100403c16008581d04031001b03001038054210321300e10142c103000045030801c6da59800000041c049004080c820316048001d42148102031030042c1c01d101c40141414031710381c0600c1c41440310140c0700021640042d0170000d80c3d110403504454001c000e206d507a113120019034043c8070044910360700161a0030b10030710503002030001d05d60301e501900403400c01f901c5503c00303100b0f030800ca4180c60b01051200780c0d0101e01c100d0701c2c081a608285007100e9651040d100640c480f840c00143d99209506c00080c8540120510002c10861510040041413450301600200311350940c50080f031602c8015800000214038003805803011080076140c024000c0081c2d54045400c0e000b0800d4020a00340140d00c141d200b078107180891881c1c80030f100510346040d0b01c010849410b21900503000c0c00c1180180c415104014400d840f002c41d0a0152229 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886013723 1250 886012473 886012483
    0xa02010c0908060a0c0c081603020c0312040e0601020c09010801090b1302090f18010e1e010b0102060103150f060311122404020f090405030a030e01020405150a021509030705 76
    0x420500040180400107030000241c00c2c0e5004c01d0103c00064004602e03034044416848142018018071004541020030303801e0303242180d003040c0c07080e002c0b110500c2000042c142c0b13400240d840c0c0404600c06000c10450f01d030b14166502d03031111051042e201c082c006031000402e803032030a0f0800895a03660300c8091080010301d0b081545c21070f4280101ca042040540c0c00917444000040021466500290100b5001d0b4554040c40c110000002c000b8050700e50f40700942039896030003040b001d8454540700c4960401c02c0c810300c0340314204881a4098140c0340e0031030322440200402c0b801c101d01500d59403184043d01c0302d060710034440030314866418810301052290400203084040098002e540e00f080008088501c0c0b100305142c107041d121156401540da8900005840041c4a0052a00b08060104001c2007180c040010150b248107a03c04201d00804000002d00700e0040c0e010340b40e008103c0d5154500341032101d00140030540c80c02d104496180318003010507208054250313480c500c07a03400032403480c0c108002400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886014973 1250 886013723 886013741
    0x2100807120219030f0905010c050c0c0409050c151e04051810060c17070303020304031205010f091e1506030e1603060e031908180d12020d02130b0a0201 67
    0x9095040041d43c00e8500481a5500c2c1d060302031503628000491100160f400100005030010f008000300200008041c00583c01101d03560407a01231507061001a03d854030503d080141c11000034a090340c1c403042230100003002c60720103030490001800b082d0903804401080103100c2c0098014951110310740f20501c10382c0820070f081d11480c112224100080388080c0ea681b0720458000d0300d06004004c5031410401d001101004004524840003d000414103401d9001540594440c0e901c0030110b1100d980c104d82122002c1c010540c030a444c0305010440c600c0b641d000364507052402c0001030b2114801c0d009443c115955030500030401d05940400300315103a0188124040c80d001407018040300d8200540b821b0002ca40740c04000c026507034271580c01070130080800580f10355040b21900302000c1701000201404214089407a00d14126100a2402c0319100210304070402d601f0544500306c640340c0d50711686002e908001b00f031800c2c140c1c0c01e009540c002040302d0b40d00c0b001032110201070355490382400402800d58a0280b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886016223 1250 886014973 886015007
    0xf0d06081f0e120a03091403031f140f0402040504140612030f0715111204110a14040c020c030d050409050105010207053102030c0a030f0e1905070302100807 69
    0xb100901001c1e0046500482c0f0800e0780142641c552004100b5001403011440280c003409200c5002509113a000000394004e030390044404038001c54a49811804050b14002c0d800321491000f0940304600301601c0c24844420000c001508050b00c81b00480c3c104c6120010508000a0f4401440060300703212400300360701c0043c04043e519040c0c0c6110300b06207901c90341e6030080092508228082c3d60403400d900981316514101d0811755102e44032414400401401d540c19240020b540200362800c2c9003204000007180c13210b80e08084072a4011080000800445035000190b006070341910031180e806100d604846030b256207629413500d0403c45814102c0384140c003c0307410b5500284041c880d964030503a41c4c15003203860710184a5003106c04c0c1c0444003034046084042c45194004410b1101c482d05101c060b0414202c00c0e80c007084400c002c0e130b4a0609403007034402e44a485400070700e46180d81600c22000c0b8100709001d4000c8481a903a00d9010505600c03409101100103040b810074480000e9009000b02c0f440352004e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886017473 1250 886016223 886016231
    0x3040623070f150506040c1d03010204030b0106020a0c081603060f1506180e060a12080f0a120f05040818030a0209070203040f0b071703090f0f010507090611120f0d06081f 75
    0x1141d000f03008e00e014961183e2021703052104002c466642501124040d690046148226507525280a951001c08000440348440c0c1640701040b03034600050314511207000c0906401402c0c0c5152154401040d040342070000940e125081c20450354a941f80d100000c2401e56116541c841e5001750404101c15250059018841d010342400101c0d07441c80c00c03220135200e0090881e0f08141491034078031103511802c41c2481c6401d10101d504001d16400040c0060054000351081c400140b1021580302259011a0001c1c180c00d001e2181200c009954a81021907003005412204c3c10a0550001010079a00701c1e44440103900004090060141c600c4081c0010400390007040d05081940ea500b1814180f0740b841104c0308a00070000440700d5200f000f0701080d45000006a4006030803030600c03540601421140c02020030a90354000403803501c1170000700d003c02519800f4109810040029081070340c0900f50040300348505010b00a061042482220000d01000c0024040a03032201c0c10130540078480c0b5690060700f0700d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886018723 1250 886017473 886017491
    0xc0d0b0d0b0c1e1303141606020601050120060103110301180c080c1c08031b0a030e011b0c020d051203090a0c1208032712030a060803040623070f15050604 68
    0x1d100c040304c0a90754803c6140000340f040000b2907180610079588408003401c66480051034507008112607050301d4081c0d03600d00c0541080b503200d06e02e807038800c00341500d160b000000410224a0051003908c040c04021f00214088400180800e8036066410702540c114210550400c500c54042141032469032040d210001080f48110b00b44c81500c841541c00b0b002c0303400000004884580201c9541d0400302084e07289919900300e6180100105101c06103907800b51f28040d9608684068074101d0f8154003100d0b034a05244504a5091107101e0081c840c04803180d2290220f002010071302d25020718403401a0100400340202181003200c1c0704112940b0007556481c004682c140410500800c0300d500941113601420030074142c48a010140700c2c1400011418040e100160405407074010083d40100405502481703000d4032409683e84910852040c0e001058410600b03c20b11201148540842d98514400d0781c14903031180c88403041034013403030012a52002c184400c1e40c041c040d24800c651300b100042d00d0410003068 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886019973 1250 886018723 886018747
    0xc0f241e0501321005130905100611030f0304030f0f0804150203060a0503030c0a0c08032a160609091401050a060c020d02120a03170c0d0b0d0b0c1e 65
    0x240700c500030404402420910110000d0f0351800200040010380340c10880441c04000514075003020516210080e0b8a180009030400140500f0b40150003c140c4e44298520b0044141d95488d810781d00100c0c24082484114141a0301e00007540c03189002c0e0b10b81d02800030f075412000b402054038441c103070180011401803002003028108000d02c20486010016034079258140000c158201540c811030f414030002030071a108000c00304820f0042da11030710020001c2500c9006003600c174051042561903241805501151003a040d18902448010010a031364000c04100c07540400c04d0b003603030010004600304c1030381003040325101e02c01c00c4000081c100d40c549595051070f002440d00c810510500040000c034841d040190740e990583e03004244d900800c062405900346085a48400d580784003503011a010703541c0306c8a100c0c04181c0362403240b540c41000500e494003402c0302c40000e1101d03140b425003185c880481e0400003241400d030540035000303007120982c41d031822410031520f02092480c03032041c1003002c0c4148a403500d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886021223 1250 886019973 886019999
    0x717040f060e06070501062309160309170a031d1902090a23070807021b01181502210405031b040b0a090e0d030c0c0f241e0501 56
    0x59042e2601403000e500079000106680500003015006500c0c0c101c0c00211a50503a0400303080c5594615074005040f161010428115002c44494500007092030f49003450034803a9200020540c4101030300311000303100100c0404150020503401c2d0200369100040b0540750300075205102d14604000007040916a1918110780d00080e601009001c1e46509012411141e00f5400a0b81c5103001000101e404100e444040d0b0101072080c1c508501181d0960b020412943c0f01044450803404400d0a144001818100460b0100f94008804250100782c0b20302040c041d00c00c2d44201d0380c2c14100c0d4000e20020165203403801c6141c891503c142d8440004000400c207503100860404100348149414010300c000050124000e803541c1b5500716800040320034046400c840c40c0d40000e1890400d082102d00c0d074034114000f07034120382c180304c0040c0203d019010094005410b450465421600c1483c4203c0c2038007001181042d004008be20781c2d42040c0e201e1449480302c06034241380404100c0340000501240d450098810451 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886022473 1250 886021223 886021229
    0xa170a0e0a021203161b0b03010b07080a020a240e0f0a080903010b0402041d010603090206070f031106090c091006090605070f0c0b03010e24040209010915050717040f 73
    0x741c0c40f0125450300100c0c1807040c2c52660150100e020304211140c68000741083c00e2010720111804c3c1c00310045014042030069905071641040510303d0311026864450305908004075010440c0702d0448040000341d1112400d400c0c18401039010049080d40d030a4081c01d40f1580740640701198408441030320002800075003c0d101c140c02c109416a50211440864003414851101a410900010b400518140084c00b452140040003260802c241d032130307450031425201501d00195009605200080108a440d40b290a40c2c41c480d0414200c6109009040b40c1809000c6030080208d800903442021a8203015420311740c08039010222011003070034031002510042550056a0800c0f101255940402145542450000d9084403100c0d95203507448082c00078a5200b4001d044c2c1002c0ca04010070a5120b1b2a8000c40200a100c90038104000b03018085c40003d42001c40304030304021591000046100c0d8440c82100300107070507554030743d4405540c02c050840014140c0b0450000504110401550b5408194a010707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886023723 1250 886022473 886022479
    0x2105040201021f0905030301061e0309050a020402091c0818180f071803080307110d1e03110f1905120c0a03090b0f09010c09081b03010608030a170a0e0a02 68
    0x183c08206500203001002000780389210020010070b10941001d542c0e0441038a0504012041305c3c8940120161354008a0041036548450051001071600f5006446100000f410443d14081c0d0401420180e1001390000d0315141000110b107410345c030200c241182010025620315020240c01e117200b907521503004028604108000c0c0110391405e1040b41220190016488000360841d01c1c0e0030111456801941d0040c0030490800c1e9201e800c980103c1c2003040d902181c1c4941e00c004040405501c286142c3c000d1010405540314520310298034858042c20b84801250750450b20380f4071829000400c00c00d031325206000d00c441448a04514803240050316440aa058040303500d0b044a075600b9030241590f0781005004148000800104a41141e41c0b5481441c0c1c01e0000e10070041c6401c01a00c8c0941180206100d0390002e420350244452804082090ba60024000040c8603540325150707070a5070880318050b40081e00c810b2071400d050389241c005540111007220208040c1500034006542c4e07100b01c01000740 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886024973 1250 886023723 886023763
    0xa020903011e02090315131101050c070b09091e13110604060c030207051207050108060d050105070206010609051519030f1e1d07030f05010b030706210504020102 71
    0x401a10290002c80550031410320344055503040410321070280d0840d0f20031501900c00d825011550311240000b960088100c00b4012049805a0321011103c1c070201804a060040401800d440360800b00481c03002445031820701c0d80c40340e9000d4100b00c0c044001030a0700c10300107903c0300d403c80000342c500589074110010b1036000000d000c1d589800b500070f81038903407045d03800800800c1c00205c058021203000e400900c2542507034400b50b100c1081045008a4822007074940d4880d00c803d2165500401700710350007540003461320b007940c0401d988080c03d45108603501801600084d004121a0303800c8107440020b400c1c11070301c400181c522132a0b800340d9400b070000162220b900c01c140d60380c10603000e82e001e800d915080e103400780a074040005d001403000c64500143c040c01840c040881c03840404601180c14400101c2000d000428034648a003060010404015110703550f0711220b080803590b041000b00c0051115490742c600c0704005600d048031134245412a82c010381d04010401c00183e901203900b40009405000d126 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886026223 1250 886024973 886024987
    0x121109040201091e0e10030204050a0504050705011d04020c0309130209030607030906150e180f0604020609121501030606080a030e0111011e050402120d0c061d0102130302010815090a02 81
    0x10401c00802e41c00417803110340f0038061280d6028034a5084007528000e5070b041c003441d01c0304c164003c2243d800301ca0240c42500010f03414800340d882016401a00e14640540102c000c4601c3c000404a030302a030904690790780000b802d1072b010705011111034a118a170310001c6007032541c0c01000c6615410014260b00c20955a2f41184c420000c940c0d0100000005985001d0422925902c2c0403020003000e030f4600511111144000030b84240c00104038a103001d50074040c0043d62125424825103411240c4496030008640c1182e2030000c10400003c02d940502154000d015455030400001b00e41c1300b43c1150f41190404200103000c20741000d03914480c1c0c4400e1814140104403a4601c60041c8401c48119034480c0e40740c0900e003c1c81c0440c3e04081d02590080390700d0003072004040745081d0f40e00c03070400c1480046240f0380d1001300820300c43c0c0c0c85240802c0c1040031600c5540c0b001c00d031290886e031010070040d084551500c1700b8819964070031005540100e4000096010600340000a03010711001000000d1040c2c000940c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886027473 1250 886026223 886026269
    0x3090618040507210b12010926090d020f1807030507140f090d030e040c12060e0103020a2112021e01050c1e04080312011404050103150903030908030112110904020109 73
    0x50301000440746d00070014460a40703452103286079a541e800308044601140d404200303548408031007014500609400051000d6070910100d04940040b0b6544152100c5401c2e004074001d0311020f110f1071841e5400a0ba0340f038602006090007001804149000c0390074041d031011410790208480027007801f02e906079004074440c80e003140c030206207440c0160072a040102580201e60003000030100b4400c0701c41c00340300300360310b4480e40d44c0c2c01d40013480041d40c050242c2004001c0c001d40c02602c00502c038640c032802d0800000030341700d508a0341c58518030940181d01100350348204403482441c1000616503003000303000609081d0043e44485c01070424403004030300f0071840c6041601c46401110002c0181030f050300d0300e808080120784c1881c0c5003481081d461241500c1c580713640340fa06201d00c906981d8460100100300c4d403180f8801c0d00510003150200d041c10381d80c81000000c030390f0000c0134500808060a0780b482c040b08a28202180b00d00007600d01e8042d5181a0034030006030303005149030042c1d889060706000303064809080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886028723 1250 886027473 886027489
    0x101710020c10050a0c0f08100308120601030c03090c06180801050108010b120c010c0308090c15030703061706010b0309071509170a030e09060303090618040507210b 72
    0x10610005100091400c0c440300c02003000203503a8403150003004140c1c1c0d00c40c60001600c1d185075000c00011000200c85101500904c089600b01410701e45401040d038980d0707150041d582c840715072000e003c0008001c2007601d41c0e16000c4e02400180710f00d01800900901e645403000901c80d4003c178014044c0d019800207160501000c0703440184403400090100d13503590001c582c02090407118190069192000013440c20034005500c220800060b920310344100c006480c02c0702d4005014102500c0e50190402d030301c0d0759035a1030003510040007011a00d10b40d24185035030003604644040e401208142c40c01d4981c03078511000803480504480000040d0f940d00e5032410b1381e4234101680c6030080100403401c20780b000c145690020400080e02c061544010703652800480c0d1981d501c01c20070000380007a0400d032030800c1c0c506100440c1c1d81c01640143c120703800e040b84640050619005903410b0441d00c10704500414241c40c05000302038005182e424083c1083c02440610b010f0f04603004441e00f10542c88a21142c901e13110421 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886029973 1250 886028723 886028743
    0xb25030f0b19030b09030f09041a091e150d080304061401030c0305060c12071d0a172107060504020f0a03030f120510050103090c0506071511031017 65
    0x30250102510701d90300e5103400601e900084c2c0702514090002400190000100c1d414200d101c0200340c01c0001700c60400c0081c1000500c11081440d05036900315041d2910048a80541c0002c072035004414907030003000e207002a00620ba5203040d080034001c40a591140b11082681a8003c445143e99554905280028280c00c8448000d00111000000103012200f4050f9054038401c2c0155035890b191800104820300880d641001048110400f08108500414503080001c00c4060816070340440400010000002544004519400182c46d415281c1c07050107403510ba86000d02d0100a0242d1010854006001302d5000410301c950b50004a025075445151010300d0040c01000e540d0116203a140c002d0640b1841d450001c0450780b660740c2072100c0c0310340d80100c0d441040c1ca4180300c5000b901c0d00f03004401500d5842c10649203071003062000f082ca510341c54000e05120340144001044003200f0f50743c60080760f6008441244a1006009008801c0b98140c142021942e6010601c6d48081145030341509000e00b543c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886031223 1250 886029973 886029979
    0x80c06010305060405120a090e041502030c09010909020c0717070f0b1b070b0d0906110a0207060f0f140307020f011505120303010510031d0a0f0b25030f0b 68
    0x1900010400500040d00da128512034010344003d82e41c1c0c0b4400700340c20702440358100c01040c9090414000080342da841c0a500a00800107001c62114511141040f64802e880400d1004400101d901e40c1d941c026900000904c1b0700c1d0303011803909410b01e00c2c1985805103030080380404c04d00c150940e00000c01c1082401e018190310384208004a0740d408401141d584000303802480401e0b2482a00361400f000b0440344112034029404502d06200c07922001c0081c00c80d000300325003859a50340c0c840d910705a000042d0285140d0b070340007464190706000c4007400048000c000d82041003500c0c1071101a8640c003072250120342d04071036900349d22616000b00076814120b641c03120401c1c43d864102c1c01a4020501c0707107441c0407200c6c192110401e9920603480b09803244001d001d6950088090281c22104620980c801c151100855601c000071514400d001c0d4180440c00c1c1c416101040040d0706d43c400c0c040c00c0d1840da904011500d10511084009200103190b004100c50300c00e060640c0e8a003084034807161500f120040382801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886032473 1250 886031223 886031233
    0x6170a0c3602070c051f030f020d0501080706110d0e040c05041d01030c050d03020c0607110a060305011a030103110108091e061501031415010219051e0c01050403020409080c 76
    0x8160781000750410740003070700c00840c152800222030030f000302c3c0500c4102000d421040d000d41030000540141c08512440c9810b980c4c2000a40d5000d10240300d030601809003000981940391829100034900054010302602c150801080d000c48503400c61590701c0c0d8118143d8010802203041902a42c0b0381c000c5600c4401c140c1e8041042c6062003a8400301076050364415000446099110000d000000740c40c1c140080c003583c0b100c84080c09503c0e0500180c1a40d5228513240d1800018013004690020b0050740705102107911200140480040080528468003490300401d00710361441c0c07185240f00d00c1030096507060100d00d202040318010288040f4100d031182e41e41ca82090480101c8540e03035030a0445200f1040c02003200130b0301d003d610034000c112000c0c003195840d5045450300449170140c00311908502d0306510900360342440102582e001450405e00600241c102019408600024210760b1081e220160300f14126441c1540e8100040d18240ca806a40c0008c11080394a840300092091481614441c070403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886033723 1250 886032473 886032569
    0x403210f0f1d03090d0230010b040b0a06030518060c09030c0a0302061c0902031e0c0102120a1812111014071403090a0906170a0c 57
    0x3074000104546419404220350320040030009110101d0840010280d00204030410652074411885010304e0700040c44100c0c2c4030000c4c0140440c200030802100c500310640011460703400b200307116000c1c49903030544082c856000c8c40b90015903a0715041c0070703020506075a907021891800c0f000c0380e100031096014080ba146428440018192030b00640d05543c401d10601c08520740074101940030200301d03540a828141480d0740e140c9904441c0d0181818100c480d5611989030f40503907010004108100514604000c1042d4501041414000e016254030b040d175109041d0300b99401c400714100d4500074907516002c1080c410744000c00c1a40c80303c0d5800b0618281128055000b4020001807000c02128112000754000c2c181135001e541440755120f03d0060000140a128045090840385481030303821041901c0c908401749000030841c0100350444411140e80700000e0090f112070890280a46550303400500fa2090256035275032140389240920202d0300ea0424401c0000300c1025400c00c821041d2008962050303134 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886034973 1250 886033723 886033751
    0xf031e090503092b0602070812150a0506030402010e10021e030a110f1507030b0402071b05040902031b0117093901031a06040b1806030906040321 64
    0x3c14140c291207140b006861400d2025803099541c8444a0240c0d000f91190345502c0e0300d0001d40040509442480080054054681220310a50300c5554034151904400c11841c0c00c6c010390070000d8100174000d40d010800d00c0b0251303800902e16080c030317401201c10708900840f0f49012410416405104164810700e400c0400f9843c0c40072001d003601182c103503203200c0d032401e0301e82406968000c107440301000c8c0e422840308040d980c010814aa0f0380701c0003030f0801244022030400030030100d911008003a02d0300c400411100c0042d420259024009281c115007d0202e8202a0002600c079841200b41a10359040c0580783c0010780d0143c001c4450103a60810004d03030b640b03084403080e51070750306590785508070a00c04481d05903580045040d0380700040450034010100b081440040d0f004011581010310444034900c1800d4159550707400030005840f4030003a103512040c2d01c5501c40e40840c0313100b8515101b50000d00030002e520400040280d80207405280c0903aa600c040b081c440b1210303038601000d0410900f45001013240e51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886036223 1250 886034973 886034977
    0x40b1602030c0102060c16030e0a121a0127110309160b0301060504140d120201090b0a020f0f250c060e190915120308061905010f031e090503 62
    0x2900070703026140c1c2074041c00012602d07440c04031a2680080c030144a40f181c0032907044040c1400a22070304102c0020031103030000500100b415840011001001c00c00744040205403044845100017614280300c0a504100d4550403480c0075074400801c807800d80701032030400f10054000414040c0c0112800e6079a040c04040107884045103404080310040c185c80014035a1346070400c6034100c4a00d03940d100c0c200707410404070301a5001d07030b03600d9141d100844e230102d4004075110b415400d00c46001500005110302c0c0d28500700c51078100c001c1541d039125105100710112544414120f86a00840203c20f0307507a244031303000003012900d0304080396a00c40241840c1c1c030100140d01c003189050f07400c5900d89101e90414002080840d0004c070703809034401c0d40181010031a1040d00e8020004107010810310b003222907124051014000180c190940004e85800244074180c2059109a00044503500c9200086400c000000e4410f141c594211400c040c0d0301c003c0c1250b00c036280c5d030301410301c001103040502140260707003405a0380c0e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886037473 1250 886036223 886036267
    0xc04090b0f0c0a0807110a050715090605030c0a14130b0a110c131e1a01030605120c0d031e0903200108040b0403030608071502011103130f0206040b 65
    0x7030446503000c96007040540341980d0004502d0b03500c560880d07603107100890b418039120842d11014890116903500280e0140f00301c5014242d00300c03106150175a02c007030040c60342c0c600f1b0b4048001e1240c104240012080890100c81040d01d1508103126031280403440c903040c030300c50a1400c10842446420105420045400070800c140d015524512006404160941c40300c80505240340d211041025801c000ca60a80100841d083c625006c03038195182c001700c1b20b06030b07500c030104103501c0704295004a42c9581c0520603800130b4041500c26107a8460304550b925a1181e8070040710b417044640115000405100302d001c041088505000302100d01b000b00b00c06840c110b40f1703000c11504255000000800280400d0500f01c2c0320384140e5440a0984a40c1c4400c022070002900c29030400d80c40b01d0300801d000c4401c00c494802400e0651801c00c1641140000078215036884416400e1101e0030418009281d40343c2034000b408a800c001860400342c0d4030b1000802510443e440440041c3d40401c0400b200842c00b1030700110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886038723 1250 886037473 886037491
    0x8040b0a0f08161e02010e0a03030e0601080a03080408090a03020d0305120609190b0d0b040b070912080a110c1c06050c0a0903080a0504082b090e0703020c0c04090b 72
    0x5911101d100003c1c18001c0903122001850082c003280c5803803903800309148021264000016800b000c07202c0181007040c254016000300c2d0719003418a407241030410500e4010081040501003500032030384d000f000148007a0025084440c0816903d0940d07407002131020040d9070003400c03510461858070300900150047d031000807000209034001052801d1201c18544108480c405600c4801c01d1500600003c10f907407a451a00300d5564204000016040d816050103280a044804054900500014800300700341d040802607440010540d40060021800e80343d5002540c18a080c2d01c0310342d60740076813504407a854883d80c8075000a6038000c40c55821200e04480c207005800c00c0c0304542d80d0401781011031003440d5020300043c217010310401c0811807034806440340000d2403030020700d0b240d0768022461509111250707603692404074818906503005190f002010216081c10451300b11403500341805a0140d00415110038150000386d0404c00c2c000500040d085050024410411485a4103069000343d1040b100d5401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886039973 1250 886038723 886038737
    0x1c05030a140a090b0601080403091203050d05280b0f0f061315020c0a290d0e0325030e0105160804080307030e01090b0d09020a0512060a0b01030e0a060908040b0a0f 72
    0xc00c5500c11f0038001e1095805494200075649050749401401c9501c46003a020808107002d25140a1058041c21340508020940000e10800c565081803505140350608100240b174001021810f4955807000d103010700c001c444410709c582c845004600c65210b400341658080300814004905444c058480000c00303c00c2d9802c40d44541e80a40900c05500c203940141d6041c0320001030700e07040300071035000044664070301924520b080c0700c3c41c2c0ca940c0c0183d550003807a000050b0404514400c040c01d0040c4100d000c08450302c0d01c5031001c0440d8401401109408058a0410000140c4400c1401c40a004ea610300f9a000d03504564503651505480d1303c3e03800816046001441c259180a1300e507104110301c00661712070a021525100304100540000c1031540340c00c030780001c0c1030440041d507569000743c8205000126009006a8540700c1d205900300c603c160071013414180f4211400540740d10000e112601a9440100002d86a6807070600c86214000d6030b01c042940c04000070a1000b099001c4c0300c10a14903681d4541d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886041223 1250 886039973 886039981
    0xc05060414070f180507140c030405100813020108090f10060e060406030803070e0121050f0c13170f1204060807020c13020a0e060d0b121c05030a140a090b 68
    0x141401c850b03124074154002e0891013808030854070380c080d0303400842e81e0410311007484003c40320120702c0c3c2041d1038a0b03400c1c0c2c001103010055820306600024019100d4a015800e501e8009041001d00b626003074013a0401120400041403154100709402000f40004219480a1108119070300503150302c0c003c20880c0c0324840c002c206141003900800090301d030700c040c8060440d0f0b12003c04881c0e0120640f0240d0400160040c840407103040001c0c6014648218a8086070134a000e910340050b9a8014103d002111000c121014209034841e00010079980a000301100c6284043c4a60703103011403403500c0600c1401041400c04c00c0b440303240c1c0100210746541d1101b10382962141c0080e070312800070f85d00b0b440d0054144844c50603c800a070380200385030a224105003204808801c0490b0098011101180001c0d550310086641d514101c0700b03545c41020107600078110500d00d11486c021a40403140c08005100010021547c5403210360003000f01c034803441710f5010381840c005210401400c11110300b40c4000c80300401003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886042473 1250 886041223 886041239
    0x5060118141c05210715060e090a0507150909062d0501020a030c03020102130602011a040b03070e04020a030515070f080609012606090312130308010b0a0c0506041407 73
    0x51241d002000b401c25891544c070b501c41c070b04480341c150002418080040b2000a2400c101c25050b01c07840000000e00e00781407181104201c0c9010b412087d240e40f2115105000072000154003065528603c1e0b580c007101c8150006551040d5240c00002c4100d05041000c14521a042140b046501e04441c84084111901401c4134600d19070307024503030058101401910100f4052299007545602c00e100051808040341d0341c60010812540105005075101c81d0744801c240010b00c0103005102085a00b04591940d41000a55461051040200001d402400101555100c1706c100d4015074006c400d0300c9aa080400400040081c01c4400a01044201c0d031482c16051081c1a414030901c8081d0040c04140d013000150107128406041110710b540311200d0f0030510350340c00c0c0b00380d60040e02070900a546805100b200b071140c0c40c0c40181020803480c0c502608001095100d042141142c4002c00d4603641d803412034400301d820170f0180704040c1c214850502408200300c040004503000000010503606d10948030b4401d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886043723 1250 886042473 886042519
    0x1b1201020721080c0f0f0702060a02011b0314060f040204050d0b010e0c0f0706090c0f0e090114060d0818040c080f0c090d14070f080703060b030d050d0506011814 71
    0x100c41100074050040e4000c404a105c02450035072081008036017001030320b81c002202d55010000c0c29005075180c0206071001c2d80c4c10a446441aa05424140043d02c9a09506000c0d040c008010b180b04a01c80c0f0120f145a455942c11200900000361910301420718904045600d10b0003880341da0040558100001c810b8195201907405903004840702c20b1506155031100000383c510540155102e2103144000a074040c03c14070f160001f04044c0c209111703907183c00d040c0182180d40321001c491000c01c161040010558581e001c0101c3c00d50f018003101e1b103441e045c0d04a81d00824140541c0fa801515285200c01d44641055904d44560180080d4042651325102e08040a016800500d40c1240c1d406a0250000d10f903601190780b1110800101d8090650300c4a600104543c6607100c2203241c0c21040e0240f080c08814012401000c000750014030804185c90001803051043d600503124080c0d5840c08030f103c0d81c0c4185601c3c0991030075001c01c0400c41c0d40f90f0340c03d0100343d60021070b034920030307144a100c3c49011410005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886044973 1250 886043723 886043731
    0x1d0a0308210a0b06070609020a050405130201021605011e260123010e13110d0b0a0602150a1109100210060608010b030f06060f03040303060303140304051b120102072108 74
    0x80303c1d0601e1183d56810011f4402d0040480e4889001e02c4081101e072518030860340304101c4d00c00300c0342150722140006420075036840d4480c4500100d0080520459800c03001281e0384445543c803c03103038450544812540b101d01406070b541031810048541d1108030005d800745050350250b80d0800c4000048014013000f00d26200d1003140402c8900c0440e145515201d07240191200f520a0046400e042d12502203143c0c1c0c2c044252010815030307620801030642440b99a41c409042280020050345040400d51140c60000400c40090141ca0b4014160501002800d503802004082c02ca0404d80d1180707000a500c4d61400603103501901d150400020341144140c4125040f914040002c619503180d000911408200c010600b90b04000200030218407500600010f501c9503000e9500080c2942c21454002e204400c51040303101c40c00024010302002ca0404540c50041b1125240e20340640801c40011551001c40c04240041c00d5101007452400d0103480200c503082d8502c0750313001d640300b816680015508800151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886046223 1250 886044973 886044979
    0x1b0806030d1202090102070e0a050406050610090b18040c0908010c02011109040c050705150405070e010501050a1d1206150d03021b03010b0a08030910020105071d0a0308210a0b 77
    0xb000d0314032404120f5008050040c4188107a528182d1902c010240c400810f5650350001541c500410090040a00c01c0582044d01201d410a81452aa4000f000c29400e400f0304085450f0000781644c06203454400d00190340350250007072081a070690310250440481d40b0510100354207003d60903ca00c2d00c180300340c11a100c5816078aa08085002c014000101122120082031010802026002c034030b007040800704180c1d1101880c0312030700c0d0038038190742001201e500c40950b1802203070040c0300d03507a00034083d035880502c1071900e11000303440040071075041040c0c07286c1700760002c52005c800c03400c040c4041001840b0b1100312103035600020401c0140503207400344c000081c0041c2c102008800300390800350ba410011101c002d0010504d58130210000d60720000990100d019035000081c40c640c01d08100000b440880114002041035241c05103000c1c019060818113082e01d0038413400083c042e03a517498040f6010b59008070320030ba124a03000034920b2064142101c2018085515000200c0c1030416014402c221717107000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886047473 1250 886046223 886046237
    0x6061302090a21051c031a0603071d100e18060a050603090f03031915140d0602040e040b090f031c0509030d091511130e07121b0806030d 60
    0x3404014500c1e10b2050100000003c250480000c03074010010613020f0040c954600c2c032140000e05000c0c0855a40350f403426520b1922042c6180c41d9550b9000b40c3e9032007001400c00d60016400d50394507014050a00175060f902030b80000790452003940c042c109a05088007561150501285107d0030613402000715000340c1c0c80040d24506001c11308205000d0750700180800c04403030045100400550841c0c00c2121244013403540c03800110b8000b00c590094100c01b802c4d404980e1042424558030b05d035101c00c0c0003941809418800c0d044410001c0690454006020440031038480c0d0400745002c40704080250741205032481003004948203180040110b40402c0b0a042c0165242c441c07141510020b050000c03e0041107000600440b011001c4900540c0e40081c442d960580c000302c12000100115110b00c14803000181003030010110300c1c0350b040911002e41340d0094849800760f035201400c44826054003140c07099035041034541000801000c03030541400341e0603180d1400c9561800245a030740d8156100b190001900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886048723 1250 886047473 886047479
    0x2f090114031009030c0c0b2d0403050303101e212109230d02041a13060f060507050a02010c141e061006020a03080a061706061302090a 59
    0x118100c06020548068107032508100c00031154011580003e1040c0c0109001300e080c0010400e21070a07000c06444030500c139070700300141c000403040801154010158444a040070491112903083c0545005591010446e944c91505000c00101a140c522407a90800140410244103054520220341a84ca01010000103105484101e401003260380c18143e8510680b00c00e20f42c00d0700c49810b80f0168890780758695078a414075064140c00c100d07203e81d0036940b0840e400c00354101180c2c0d84400d84040503070102c5020032a1035110350310807a5161540c840310b61042142032110840c0301d507a00100c1c00ca034400c010144c141c0b07554040617540351268101c01400e030740002c00c0b1400107600411701800c0190082a405070340310b00b1166414500b41514200c1c8501c44407103500303071021140411140c0d6010a03210b45107050f00385403c0c0003a640340441003005050100b500c0002d000410036622040040240b588880f0880ca501080f0940fa080c0c2520346a02403d80c07100018800480383c0201c85007032201410111818ac6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886049973 1250 886048723 886048739
    0x21c0c150209060f13090c030203060306060319020405180106170d0201020403240f0203130b06060703051c02071e050613081902010b04020a02070f060801080c090903070f2f0901 78
    0x4440002c000103007403002404500c4a11b1481020841070860714010f03070300d0414104041c03500d04c000b030859210794092801017044e940090100d0900035415100030505803a09000341c1d40c08145003c10820f00d40c03a0020000c0c4076a0305100c1001d05c00c1126080d074046a11042049080c0e00c5540806049825007904101740241d00700090440c40d9104400010707480d425204840c00d0342c0c815601c2284c60a00c1124880a020135551010380043d401c80300203142001550380903056009a00240f0308a40703003024166002505901120000759011100d0703900c10500c500d80c10301c941d0a0840507901d0340b140c207000440300c88010142200898000103243d0600460b82c03860160003643e84e1501045549403050030925032907e0015043c40b0209401078641d143c10200d030301e040400f2540c0f10000b003200d1b900c01042402c5012581d90f01c10380f400c1d1220b0101c1d540c0c0820035451413095600082c92140288482014401c0c01c1b0740320039030040c030000030442445584e0000e8885488110f205503000721440f00400c1840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886051223 1250 886049973 886049977
    0x1020613020315070504090f02093a050a0308010623030a02040f15080903071119030813050a0902180f040b0a0b041505041d0601021c0c150209060f 65
    0x3a100504440c58403143d60841c0e0406a025200d5030301040c1d000c9000d000c201e000380143c009083c0c00c10360840c00d12800400003081c01700102c81408141610280d08030903001020204070101d00307407180c00d040c0300006180603030b60703101035540640c005490a17001082c0f4910030054120307040c1800202c181da8803212000c120b100d50000c4c0ca0351744003da007040009a10301300c0010b0131004140102c464810814080c0e4041c0240c2e000a1115805030020401080024600e00c0c0316460007230150b400410302810206405030140650b00080e00400011908600d002d04052100c000d0ba902030f22840f00d1b1660f601000c00903405840070404404203080e54a41c42c90800e1584e0b810710712402400840c3c240301c0d07240410405409a0844809602c0018081c4402030a6517401c3c00c03000c12610b042441c0515011644640360364a008070030708849400041103013a032080260f489141c020004448148030740b22400b8111581c0c1180890b20b10015480707403500c421940c82510640003024003028900403804c20800442d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886052473 1250 886051223 886051261
    0x50d1a07022407081b09030a0614010b0f04170a060524030705130b1504030c080c1e060a0c080301080703020a0e1e09030d1401030b0603010614221404140705010206 72
    0x5c00d10511800c281a5410401013010381d0040d840091340c0703448800c040018640c160012002e000c010044100c4092070681101c1c1200c1c3d095641205603200b800c1220305002100c400030b0000c504001c00e00ca01ca450480c40c5c0c4203048a00a490b000c1d4542c0e16007810384428a83c41111740c081c0704198030442800643e0020310003420010b0108180f980c140d100b0110030f400c16001910fa80c60b040e101071106150400c5002c0c80b01e44115091842c04c41003403040c01c1d211000c0c40c200390151402180b82c50101e4010303c440c0e030701141c0c008991502c035a1216420f681d030340014413007644112400c400024020b0345035005c6502070744010740541aa0001e0030707646081d000c0c011340520303081e2204201e200c103452203510030341d40d00d00b102c4030183c5034951560030151614071002c0d0105110364502303901084007034504010900c0c3e0309419215050b4140f02801c140000c0b0918850740006281401c5040000c046a401c649124a1148581c075414110600640d690740c0301c1390040e180503070310a001050000b40150b80b01c2001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886053723 1250 886052473 886052521
    0x1151112160f03021509070315020711040f0e2103070c0f0501090605060411090901030204180b0a0501060f1d090621011b020a0b01050d1a0702240708 66
    0x8540031070307644020560242c5003d9005820031100140301d4003e4103015500205110010200ca07411501c4c1d00a0792202c4025104c03120351f00003421410001002100d40702e5240c0108200421864001c880c0041c0654400c901000d001e8a0456009840c1d10001f08540310003e180850855a40360710643c3d004003042e2003590130900d8a599000099424011410540c1c0f1070b03035000c00c2c00c0c00e0101c10b110070340d0710700369444140400038812140a52140050241100d030126000310b4084042c100e18042044620700c0902414004403c005010006812003412101690ba0319100020400f100f110100071a242e444c2aa661018a01e1180c0c80c10401454020f40c00500b02e10004104908080d030000405141d00510394541e036003040d0380c02142032440c5800040740094041420035640f000c41640050044074810340c4450035031380522009040d00c46d01c543d1154100d0f58203044ca40c9000c0e41d560314a52803126100d4043c000c406000e0026070980740120116141c0b0600b0f51604c1d00524581c01d455010702d54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886054973 1250 886053723 886053757
    0x2030a08160c050a0303023c0f06070e33042301030c090603050a090c1d090102160b15091305010501080712150216060501151112 57
    0x40890420002890007422215406403854040d01d00b140d10102640d00881c8076981015003000400c1e0040340e9446900c182c0460801c2440301c140303205e030101c888440025520310440c400070900c80e50004003001c03590844803c80d982c0d650780c004100e13030780ca800400c8030750071008030510104001d00e907c0f48009008400107040101c3e007001303015034a06810552117421001079851441c92400c03600d464901c256002840c0c144040784c11140b026000429078400c171000c06669500062540c1e2180d401080b07a076900003c03480109640c1d00004105085030001544000c0200c004031394a61014400c4541210030401d56801c220182d44403020070910080641d1910701000307403c9076541c2e4841200c1d9101c1c900d00010412042001e003055400c40e40160814401503006100a008600c100594100441d038040d0285410940c40c000910203401125402d51480358000c041034204a00d44c0c1226042c0c402d14846150b120718003500840e51500c8120100e00366800c07002d039004020050000400b120300030710500e40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886056223 1250 886054973 886054993
    0xa150522030c061103150904031e09050402030705030708160807120f09050f0d03020301031a061305012408060a061101061a0c0115060519030e061f0504150506070203 73
    0x50940c0c4102c0703000003130204000100700c00c4049090304140140390507160341c085807030259000791400900f940081c4040c05030b50351007405244110190b0014100150044d512800c01c94005426a08165510008030340501c001032259581c10501c00c3c0c1e1f1072101d54840c0d4240d100d000d03045d681d50119002844500341c07034500241001c0c8190140c18a806c0c4600020042c100d03e103451942000300e403801100030540100010008680c040d0381d1441900f80326800e0003816140c420001c0d40d1080703900c3d841700a141c21b10000045148500c5c0030988400d003150500f0a4002034103500701c1b00b0800444110303510550240041c4101da114540440100b0389481c00002c80343d4881170990141c5290402c04903081d1800146624903182c20b00a5210386020030840c4d4040c1d50070844054618010100700c484901160100481c00d03600c6a00501a0002c052050b40d40c00d080100c01d130b50303032400d46a10400c14022061000140f9003890321801d0322142c5440110f00e0103d0414041000d15806540282d038140f148800f14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886057473 1250 886056223 886056233
    0x2011425030e011805011802180903160302060f010506030103031d040216060902180903030705071a09030d0c0219030c0611130e010909120503180601080a150522030c 73
    0x11a445001680344d6400300001441e0140c2520030035641002c19901005000c40180c4551007654646800d550003000740d9650750340c0b503510f0740c06030016030381d0182183d1565006164003c01d9150003219040060305141c1e0300c0c1c1c820b02c42c03984002e1000500195125070b64100745541407480c03004005008001510b00695410b071b00a502181c3c2c0003d8405075903c5000a04600e0425070801200f90400e031503521500d80012544d4681c00024018018840d00049090400c00001c400c0c648011440b41c000199040407803242d40d42e07400c0340e09224090707072500041c805158000901c088860101801450b02c000c42d079a4210303981c1142c60380440b5800d8607900b00c2540481804050300b410b05207075495841c0c5a140c040e681c80380f0f86060f807100c01c02514100e4120086004c241520300107480c14107046503a9200c1017070f00040040551103040070340c0180400803c0c0c1c0d6001186504036035004803d80f81180007603840003c00c460040e600c0c0000d5014098800100f81e08800e43c0c4402d060182c203000c404c1c400540c640d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886058723 1250 886057473 886057481
    0x18120a080c07050103060807080703201807030f092102031903050405070b09090720010c121d3004081c08072a08070f020102011425030e01 61
    0x10604450b00480300511841d40d0510480000b860340c800100341507460540711689520300d0b408040d25003a40b4904801b0f0183e442c101c0c0c5081070001031b0485c0c40c010200c620390301e103001064070410006401c100c0814a040103600401508a810001c0914014482c03003030a52111a1700d11641c095020a204400202c0901c802c88011040103440c08030309481c2618101e07003025444e42001103044001e21003440030351101c600250b4403400c3d0741407400d4840091540101284500c0c01416103031344c00c190189400c1c940c0501c2e030a0003e03007509418000d4000b910361030f00320072829941019495024622040e1409034001142c051680c049100c0080c0d01092070040f4140c5d813080d00600c60030f51002c0480c210402000007440c00c45555840c140c030342c50812000007480395104000f88040040c0b016001007046003400280f240481d440701030395036180030500d007a0340304241c9803000ba8003551900300c00042a00c6200c007490b00c196600400001000008007040070b25074504080355040503600d80c0c210032140c4003442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886059973 1250 886058723 886058737
    0x6040f050f070f0207030b0601080703090210030f15050607080f0702180105091e04030c11130515010504060c0f06060e0123030102040602030f0c01090209040b1b18120a08 75
    0x5900c400d1031a00b01c40c00303081011550040000c650100320300b00042005004000e411900919108034903031a00c0c001207024001078040070750f002c00040c2d5924070300742e0964400000200c0d808028040580303440c42e1042c041d60700744503041e00480c0030007511000503040c000500c1c20000314043d0303d050820315000704040d0f00c046580010080700c14001071081d8a010380c10507500400e020034074041100840d03c41518190007410041c103011095282004002003039480b125010805006c40070320010743d1200c4805080d040d10329000e040300e0000580400c1d44104100c0d0305a0f4040d440729412032000b60307140e07031624100c90800d403405c5945500c04207040203d110414000c00c880d07110360702c41c1d22440f02c0707440d03507000711528042c801c1c0e00c10007080107400d40110955032125002c501c22030311403202590203809841258002036010240794100f000700104043d000f070145e1800c18000000380c190740c8080e10b9a11440c810040e03611204042103001c1e14000c90f0485400c2c08403802d481003a0345035a241852a00144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886061223 1250 886059973 886059991
    0x9151d0702010b040207020a0302060a02120c070f150f05070609020a03500102090a031b0603050403090911071205040602210a11120a0207060305011d0f06040f05 71
    0x42401000c9034240074445804004860452800842e64000f54015006100083c01030501040c030045081c001d0080780f0500b1134906240b44d941012005080c2c80740182e019816042146a20100316100000c0c1010381d00c01c3d26443d0703140607005070241903c80b5048408120b40e0991504040740050700d075800024021445280c2d2018141e0144280010490441c00d04181514032028019041c06c2e0700019403111801d44100d81490b4150b003000240a441029415a00800d4049000040011142901c03019500c0d4000402d04540ca4840c1201070721030940380600003d1071003a045c0000c816540c402c44080b1103035031401d03240c16181d40e240c3c107481c0056941080400c00200c1c01700549501400f43c601009001c0402e040e0040100c1c9601c5080d002d00201201001806074124031000d504001c1c00f07941d21034000619031243d20800c4025030b1240c5c2c0d4012800000d0800000064043c050620100e04805c4504012010341d16a0107001002c000104065030158517203011501e090380700d21a46025025035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886062473 1250 886061223 886061279
    0x303050306090117060a150e100f0e190b01110d0c0510020a1e090b030c030106031d0309090a0b060f040f1a180307050909010e01050711070915 63
    0x801c1c20858035001c143c3c49010700c6100c011036051a00008601140d2007054220005240c40d64102019603e075002d4220715060700d00182404148490f0321036440440361990089180c00b40c4809005e8042c10b41550428540c1c0c402d051a91079000c00c0380c12140c0c0b0386038185480803240e2482c0b070040c0d2512640c40c0c100c402050404050320305200b03080c803d50203102407100c025880e01e100c01c0c3d0002d0107040e01062a1010301040e07030300303410340611401001008104981c4503507280c0c02e0078485c0c010654000c1c85038034007081ca01200595004056034008040c01c0640c0080c40c101030320340050200c2007000400e001c2d141a5501c07201c48103591400040e010078611540c180c0e48035400c1c4200108034104a820482d00000080103048814580300c0481d010540c1740c5001e90f4100c2c102c5008203281c10300d15041580e001c500003082200340d030b40550207a0000000c1c807009000903102c44c1c50584928015022036411504420070920a09945070006040300d030401c910001070030790702c002c03a00d660302c01c1c0195070351401c940c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886063723 1250 886062473 886062481
    0x20f09031e030702040b030304080102040339170f0f0102070b060603040b06060d0902221a0105030c16152310031e0609050609150118051f03030503 65
    0x10400041c24808107400401c600c4070141908a82e80e030083c2d01000b407149440e54030078401e6485c1402568010203921000307548881e10380c94030541c00c150300000c0b080c80303005050103051400b49449810400e101c00101c1c58180380d0602c021448007018250030312040748100c0705d0500c4100810402d010384151428001a2111105c3c80d0000d80b00c10054a031030312840050041c400810240c20843e0741200e82191201d036541041040b40c006001210b00c00b03175014505650106e484e00300c1c071210450861802c0420000300300840001d841e0040b202c04080d00180c402c2c8001070080343c80100600d0308001032640d00f00303044103030303602c0700d40511200313103030756020340d01e41c51083c1e618141e0100300000b00c00b001c81d044c4104d282c5800b0480810203c0c0c440542492030480c11040c504148925451809401c49828805e007130b071508015035912015a21035040d441800d91142c280d8840302d120354147e546a141000703500d50007900c510042c1030040c00c1c1e40301d1001c2400344000c0c10012041070000075403103502e4003600ca01e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886064973 1250 886063723 886063729
    0x7020a080d0906020c060f070f06110706050a0c120b040b09130606080712032a0f020102190206040302040b28080606010f080a090326010504150807060c0213020f09 72
    0x9a55030280013554000e09400c9507541d18802030b240008000801e064450f000f030f091114113180354040150540d40b07000300c0b0182c240c1011000b0b01710709010361821720464a6012200d4200e03590301c000c074000600c82106102101c441d03038020a07483d590051000c43c10342d4200000402c095011794902c0c0d00c1c21401d41814003005910300500006101e0403025185d11480c03e034031000c904802c008000c007042071040000d4911011400111526600100200c6080741c492074a00d920b00d0007050305902610490740506040741d400081c4001141d030181c0502c3c242032465081c4005007061101c0b40ba44001600f03d28000604400c84119500c0c8014280c4602c407031801503c1400c020010b00901d04201c1140c0035000403075002001103030020a10000010509454281154103036222071050000112100d5111008003400d44028103880c0c08a40800100c0300d00c0c4040e41007555240700381010307900309400c10400a40103600501c4142d0025240c0d005d200203400e60482242c3c032007e1b8407041024041580c5000d41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886066223 1250 886064973 886064987
    0xf0207020f090705040e0c130303020f060108061909060b0d08070b060904020604060e01031d010608100506100f050c0613030e0118050418020913211d0607020a080d 72
    0x45816102c018407410302000c01081e503c11070182c2001d481d054008a0441e00c01c1c001183c289542c02030b119036030687c036841d00942b01d8142896002c2c07144190710010a1401000c183d65010380688141d8002102c4114801005000941400d43d0303d660f907078000541c0c9072206440703040020f12803218503644484c107180c442030240d00589824002da0a010403c0010303103840382282c06840c03681c01d00030300c000284030040b40604240e1550390400d03e01c421484075148015004002690041d10980702c0c3d0f202c226a01004807103040700c0c43c641c400b84001079440100e001d020618a15803d52a040d4601f5040400c154076021045d100c403403000a061007101e080c56488041c2d4150401c09103418808441c1c1c600310b00c0000f0a0601076036114039a42c6800c3e01c15403030180b006092282e800703051010309140c405000748880700307216005e035480b948604454001c80c03080c00c20811039450070b440707102e182c0c0c2c84100154051040c03028a039400c603100301b121801580e9000e6881008020031801403031000c1d06030100070111 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886067473 1250 886066223 886066249
    0x51002030a05070206030405210c0c0102031812030f04150e041404060b121f0b0111030d050a090605090c1215010b09150a020f011401050d060f0e010f020702 69
    0x540091081c1c06003103070b0150460f503c4907011a04a501c1c3c1e00d5506060707060090900c001d41d0f000c1c42800c540c0ca007001e0440c0150141070b510809840550b40d06400581e01c07480391501000c08041e600142600e40c1c0b404071030a0816110035001c403130800e8000d2010340090752154226007410303070484440c01401e943c000c00a00c800d00086d60140100740014015032851240503200500c46038852061081c5070301c0304200340480008040403150850005181c0940301c5540301460300c0818100440c64180d540a0508000110180c400a6140c00d200340d6100c0010803003e0004440242c40320a5407000c600d1601a1030300901c82c0d00003901d10070201c40c041200c1404801000d42140c0c011499030381521545209040c1142c603103100c841e035180c0002002803852030703203281c00380c0c46200042148403c0390b50020300d110312100c1c848000c102031000c00d0801d24104009110b003d81c40946024190300048a54100c43c1c0c1c0c0c002461008281080b40c0880f45080d60b10512004403000d41c00308100f419881d08132030803402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886068723 1250 886067473 886067477
    0x60905060a0b1c022706090f130305161217150d0212151608090a1104020c0a12020d17010b0702120307050a030509130515011b020d0c0510 61
    0x39000060301040c00301c0800070f41070203440c600d0f50018084d512455030002d1051008034010a521085014000306008182c8420340100240400550390325110780d09940600d003c4070340b20f40408120740c4c04541c1d130742c07003282c107200c08140702c43c407400c001400b48a285020030266143e40d40c0e044000495400d030391400a040010f0b2a10007142c0c100d440d101c2c0036a4000d03694054844c8031009076252061898102c0144d22a0b40e0190041c081011919a14911070317041606a600c2c10307030701d4036074801603a901d03d420500501403c0b008a00d08038186482c0c0c1c01801503440002c242c0700700b0451a1201e5540f0f98260641d1009a003000d4441c030083c0d980050015400f8a51407401d40007541004944000c0d4010480000d0040e10400d4012001807420820364181952000031202460a503180c0100103403c984d46160060800e007000034401d4442d405802d1041d201d1070040038807442c0300801100d4880100d04000055030070300f0b01280c00b580743e6020082d00b850080e80c40000f00d91600c4140500c1c44908618401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886069973 1250 886068723 886068731
    0xc0f0a0f14070b2110061e140304081908220318030309090c0c1106030711060c071401020901140d090b0906040c05010507030f030b0f2e0314061516060905060a 70
    0x5400003800320440d400703860760301c0d47d004d8042d00a075486840900e80b4401c010000c8100b00030094a0001040b213030031041105a9039210720001510840d500f6905005295100c0303031012043c0c11210740501d50715000345049052440310000c480b503c0039107504203a00003102c41c6401c0c008807065002c0c07001031112918140245041e01e89131031200070640c0c69414420030000011032030721449444107180381a001d90a039409428150a192010360000b5001c580c02040e55405400c001c4062082d2001c0d90010b131905108083e00424480c02540620180c02996548528840104a001c3c803128820560f0000030249070401e030404520711445a800241005020484000080d500c8050005824140c0c01c02240030001c0000243e00381f043c0c019000c0c0c004968000c003101001d41c1c1848800c0981c0d10410100b210341075003030300b02c01f40c540600c070008040c02c440001c01d0042c1003509003064803c04d9200518200090741c7d0185000c0c100c0381d0003d9545a850b116110705100042c08141d40025045030100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886071223 1250 886069973 886069979
    0x6050105120411030a02100207030314120601030f0f0e010e060a02040b180109031a0402090a06081e100e030d0621081c020307050c0f0a0f14070b2110 66
    0x8074220340140014101c0715101e007441c41a032820030000d00b110790300502c2c1e891044404440207641d02602c0c4000e43c001440c085d00240b031540032100f181d08007105580c0c924944e81d6100019000b80c01c802540c1c220043c2d503150007080145441c40340344014103140c00086003c00e02d002902c0d183c5800609107032522441003008020702200340f8106c42200042c01000110b0040807001642c0c880d240340d1025048030f03039101000c0340c11140200418030072031003110010f6454035102c0544c0201d44942c00b61000c99032040702510308610081c1e550f12000d0108800312801c060000b0038410079240e030f540039058150b20110320340819203054042c040282000300300401400c4144151600c00610302c2d6130181040382c0014840300f80d010306080181850429090030341d500e0070300d0040100194010060725500f80100080d000782100c0104801c0780c4c00f0b80010010704134042c1da0312041402940680f81788040d2050b10000907545081070007801140240c0b950000178900c3c0d0884024001d50020107901070b0300b500c1031041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886072473 1250 886071223 886071247
    0x903030609060d0305120c0c10110f070c031b080f0d020a03140712050d060902070f030e0a0e0f060f01020607022a031603030e03030f160204020712021006050105 71
    0xa942d00c00c900711089141c107891130405584a00c45c4c024045151003403513003006104d20001e8000c0012846030f40c11520030154440b0ba0104a4204803c01c0c070714013808024007100e03407001001401c0a1400307a080d00d00c1417a620364074141c0c0c00c9449141500700441c9400100300600c410310065010009403005400c5444500348000d4440040b848010144a0071040b549030b0f451182d0261900b4031740c088043c3d6010060440054580d40294200043c0c3c142400f0700402c2c2203800b40240c80302141d0003003801c072418103559415554503003c00901038100e055400c0006420b14040d4445010704200d403071440c2d40b404d00700c0a100c9100300c0e42d400d2034150740c40b4400f4494510b50001d08110b1a414209800c0c640c001c3d14015104c003030301c1c2141c00300d0381845070340365010002021440e00c1084900c00e03100c909441003d20189030700e0380a880300c0020700c07070000e200e24002d02d1682c0803480c006d280f008000511b000036580e40c40789808420100080140d00c480a24031181c00c0d64401c1720050082400c0481c1403624015070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886073723 1250 886072473 886072489
    0xb0c01141b090918060a140a0c0207090203040201031e020d11040312030f0e0d110609062e090609090b0709080c040f141905061f1d04050c070b09030306 67
    0x81c0380a00c503200c0010700000c1141150f0403101c45104185c1c1d01e141002c0314100b029180400d01790204810a40114010b440207218015000b00b440d009022407e140190000094000400070f9050544030031606c00d00c80d00d01c3e0b8812281d10942c4800503183d04000c403244086030031018141850b07800c00c10050021442c81d010f0704406113605d2902242082070703050304030302404c400014070740c0e14440c1c00d0070012080e4001036550303c0075002c1e4007202e150350703201a00140d4941e800d54400c018004140188800e54000302400c01c480d034081103c03980c0027543c65030301d0b8040701c941e6402140003961f9640c00c41c0c104462600f00e6908005039183c55191a030600d0b04068a6041c8000910311903a83c03000c03c8540c1844642000410350304088500b2410300e402c4010300710b0082001020704d4428940400a2810726060115084602598100c1a0500c211100c01e942108402d000f4a4400038a5409822036580314040c00e445a14402c90290b2200d4180c40c0c00305042c1400352048840790010300c2000420784414007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886074973 1250 886073723 886073737
    0x3070305210a050403121e12051e060d03091d0105011205071409150c01051009060621020d1a031603151e11041430070b0c01141b 57
    0x11068001e90001301514604002007407440801070a00d0141f1103290090283d00111110b5030081c409a40c480f103209240e500d407040107029400185001c54610300307001c22100c96503482414001143c0340c59040d00b40b40070541d02c0000000040d0080180312559109120212540c40d50000380101c3c20045009000c90440d15002e108900003c0340c0306080b60303038030b1545801511000e0401503980d146080500e002e040110382404002c0c0c442c01d00002c12108a10403081104c1840e65800000c002045600141604003100181c1c417540a21407001b1554603071058000d0304544100f00c0c101300180e081414104205220009504a81c00e0070800224102c12620402c45860300c0c00042c0300e0811008030401507801c51000d50341c8902c0d011a038800c51546030000c0040e02d444101c008441042c050403c54440544008401040e960482c444003c6040c03042a0400c0c881c0035003941c01c92919083c140c4000c0e000116040300c541c1d110700601d0404482907214a402550f101018141c2c042c00c0d42c0c0c00081485182 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886076223 1250 886074973 886074983
    0x212060405060301020f0f13082406012c030f0d02030708090105130e1e07050a0e011e0c0b1302010c0311010f021605010b010521040f0203070305210a050403 69
    0x701190307001e604403901d42c0218048141c1f03c280d000d076101041c1d00300705914144880b2601c4042100c481c001140d0f01c1182c86500b901c0142001c20800c00801c05014000e02e05021508603585282c13000c081650b05401d4030f001401000c1e0015800b007510b410b50884400304c01d0740021702039414240d40482150003064001d80d2040d603a25050300121003600c2502d40c0d110420010302c0011034000c01c041d01d41802540ca00040004850109140f042007643c20b46548010a208010702c6460768020f001400001b041410310010f0540303400c01406035015922503d0000a502c03800381020016262a0320b80c009031481040c9080341e400b603001900581c81c1c0c18028080c00488a86c1014000e0300350002c00d004071030741034259144c0e0980105420038010f80b141c105c5155003085171141c1154883e0007600c03002c0c2c510700e90002240840d0214200754120140003a14221900c0c0c039202c02580701089000010f61107030300182141414002000711503800322081c09120441002046103580d03009050701c003603035040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886077473 1250 886076223 886076231
    0x603121e0408070f060302040f060c020a0f0603020901170112022112180d0b0105060c0f03280c1208090307020a081b09040f080c0a1506170102120604 66
    0x400941100305000c0c0c103032a44650005008550b80c0004200c01c01111103500901c14a0768480c802a4103a01940c010301c640b41c0080380041011903c181d158407007040c000b070320100e2281c0e00c4035505000d110351500510046900050740c4021968414142c040300c04503040200c07041d505000c80722072072a00e007460281c840d03130a44118600d0300c0181c0440340500e80c9100d0444000354141045005650403400201030f4414010114060a08000c032115048942c0007460200380e0f802e000030041c4a422021681e5082e00c2100b01d180c1074104100000c0054050411807459855409456402c0040341304501100b00b281214101c8001800b01425906d61119402c0c280c0042d03680c6481c09146000c0c4110281d40180f9048000136000c10100300040c141c40c2840382946a6100b107030030300203181c00582c3c0c005c1c2050003540641300894003040c003400107500b400d0b080d2000d4a1041e111718400150301e03422801c586542c0d034010451050304918500307a40103d50004c1d400d048070800b0000004200800e100d00507515 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886078723 1250 886077473 886077487
    0x92a0e04080c10060609061106190c02030903070b1926280606020105150d110f06040b0a0e04140a110c0709060e0106020f030313020d02090a2003060312 67
    0x814403c041030409400c50400c8035641e914401403400203103100c0c0f100030030364034a8901210a004034030303188625000c1d010507580f407820402200080202040683c110b0000340b1440800ba075080c042d0754014403070b80c9400303900d03041c050503150b00303c1195085d46410702c200c103044207a048103c030f85034011418000300b014105a50790b0519031190b401d00c10071a40c48044001d000c0050b03c4580d070040c01580d00342d900800041c1c0d581001510702140c9202c080780e10401c40121100058a03021044c00310303081c080d01280302e500c0c0e1280442d9480e0096006002d00f483c000c1556846141e100426a4802c501201d0600c4120002e0104050780100944281401500c0d013404100c2c0c4000f5100322070002000c981140c804940d00d800d1540203101d10700601010a1075400005613148c400100d0041d04003200001e10700d1a140c4040744076124186050480e00040300040c01800750365001a114400c0c10b003540c01217404104030a610b04941e00c841d4181c1c4100d038050040c0001c5440000c0c4094483c1980c0c000d440e65004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886079973 1250 886078723 886078747
    0xa090501020d0f05040b061005042303060c04081009150b0a080d0f031505090c0a020a2405070c0809040e1617070b04150305061201092a0e0408 63
    0xc121986a40110f08003610303c030600c1120380c00117201d9406004507400325211031081003d15149096a1000034100b44401d020040049014178400e50406400c1038009902a005c40c0c2007840448500001280c042001c2080344018420b50031000014401002071205030b07a51490090141c000040c5526582d50b10910640c03614510400640f80f40c00464001c070540c02c00040c422804038000c8000641404040203200c013142e8000b10079900010300f144240d55030080c0d42d6506421000160701140305a5a90708003080c803109081104103040c146106480c1042800c100646030068902401c0141130948900415640000c0d90007000c41200d001c18040490781080c2d160044143c5021a9800ca59100042d0080386440d2003d0102092055074007580e5961010007582c01284100320f00300c0400000c0e00d01541c400da2015911020081c0310f2941e5000c5c0c090000d0844500c42c5044800c540745144000070560541300b003100a60104005201850030003020421710304018000404940300842d1aa000c25 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886081223 1250 886079973 886079977
    0x4150203070507290304020d0f020102150f1608090a14160b09010e060a0e09040305210117011a0405070905060c03070b070302041401120204081605100807080a09050102 74
    0x42c1c2100403582100e4030740c0f072400d04040f1302c404e5200800e215085113040c0e40f4004010750384129002410000303c0344145e25a51403402800700102d0443c054040126034502d0781a00c8240240b041c100c0700d03011344c50101002c0411408002c142401d002c118000c01c0000ca40015120700060703880840e0071040b07411404240d24004519060400000d842c0b00b001c90f01c0d0765081c0140903000d40982c2c655451440b400140300301032049081c8a000911200c00180f11030038001c1100d90018403a10f009481c01005918140807030f11144c0d111080e101202e0010404002e040102c0a1280500b200030499550000e02c89054464003800386409a030715480020b014501501d0450020100541807a642d4090180d03015140c1d40144012540421710034041040c81d0320038800d580c2910386150a100320643e050006480e640c000c45104904d007a020131020a0200c0e05000c451041c40c1c0606060204070b050800b0045607641103080342040000c0768041043d2030f40d00814503034000440200c0054510140e040441c064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886082473 1250 886081223 886081237
    0x40605090402030a02310b0f090103020112051b030c07050f07051806120304060903051603121d03011a1201091a04082701030e1519020c120a080907060504150203 71
    0x9800d04501103000d80c1c211f500030b0a40101c048484610b040c50a60401c070b5005020f00000c0d00007941e40201018414440c4e2150340c0084040c05110340069846460040951088400c02d12940d004039802080010402943e0301034400940501925401e2001244039980303403031802d50b050895a000300e200c603180c13096030002803100002560f0b070703890b00c400000e0601d100c1840704035028410000e520303401801a0401c3c01c141d03580300c0c000c01c1d100f2800c203e0441b2408607030700c007040401803c0e800b0427484e03940074400c40103540040206a0308040f484404c000e07c01c1d00710700d1483c40701d17410429038074005110250300c01105039070700d00382c8401d0381c540781012103040c0251082d03400c0303083d0a0195400303c1502c41185030340d0f9403800d0303a090001c10680c00d03106464040c5a0032112403100000c0202e04c0c1d071104181c02902c01403400b1030060078200800c1d841494440d5200e600103603400c001031040862980700c1121903104140d2001040f1440c9805001400c0348980e10070300f0605081c06584050581c4280125014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886083723 1250 886082473 886082539
    0xf0901170405010204150503070207050402181f031103060904120221180102031801120b210c091b0706110c010c0e100207050f030102040b0403030c02040605090402030a02 75
    0x290700c0c051070024000c4d40503000c0e00c4903081804100302030b5540700d0300c03c03284543c080d5805020b20f03900d04010301010f50009a5014032024071401e01d03107642e0302c800000c0c10b0301d80c2c2c641070b15a003170188821303015040382c14440d18502c00c42010403c010850b01e440c3c00c1305400980c0710080c203800d5030620b03800300d080c402d400e640c1c1c4022507900312075400e52180060240c044000741c400081181403000c801642c0c3d9203c0c8d107162000681300a02c089145600801881000031034555000c1810b603d0100056580b9036035072602200010306103400201440d0400114911030b07025103450106050140c0c1e04d00d41d4884801401d14010800a9198100b0909400c4020003800940541341c8640c100c08105019100300005680060005d141100480c03070300c140c082c42800da240d00580000d034280000d00c00d01303100001c40c098041d9020807002a480019034001d03c02140607980d03803100d0240510400040d24030b294020352141d1204014807001d40da001c0f800000a50b030423220300942a10160301c900f42c100cdc8590700d90780c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886084973 1250 886083723 886083767
    0x30e030307090807050901030b0f061201240504050105030604062403060c1101020307140304060e060106050d060e01050f1c0b01080c011227050309040510170a03050f0901 75
    0x30066002500d000030f40742c0301c000341c07080c460302c8600380420b1200900c07000d0801141c0901007041d61061505154000308041c1031b01e00440e403002d417042d09545518144031400704d41444110f0301e10303019804000140c40308940500c00d81d40b40034006981d034180034001620f2141c0d00c80b0602c00c4400c01b15a0815503503000340407696460742da400c00000800320200c0031000300d52012903a440c0c2c0301040c400c5034420312081e00c075000d60541da54005c0c0c0d060b400081048465550300d0b0048031088100b00880c070300030302e401d64034195200c0950543c0000c3c2c9040ba4040350269035000014012546c50700c500c001c0001381560245080e5050105041c0e0b0350201311b41c0900075035134180000c0380c40c20b408942018260820f8031002170780d800c290520011110f03603111703140e00c441200d0890342d66104500e24442815004008032400e145c10030000404841080d100800e20029000d003c004141281c00400c801081c1c0f03001500740480e098a000d400c901c0b528455482512000603031500683c060205041e03ea208000d084d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886086223 1250 886084973 886084981
    0xa030b09040804080c040902031c02071d0130080703030f1104082404030810080d2001051522090609022107090207060b04050a0c0806030d0519030e0303 67
    0x4102940b1078050014140030703031452000181018040c1c1003a148d0301800520300c1c00200541012174049003d04217085000d072010008440720728107100010400d488904c1d5800394501140018441c0076411000c1d0442c41d4050104181c18400081080c01900921156600c4000d850218010020105111010f80c5440408600d0044242c09081512a198116064403403003005034524000c1006001207624845800900080e104495450300035404a84002c40346445801040c00c00760040340040005080302c0d1401401840b00d10100e0000002c613000300300600301002550204100201c90714000d0101d4a00341010400440103c90010003110040090b00007600e0490302904072a481680316540440007500b403840300f040880c2c00c00f915100103008461400c4c4001c40650440c4100342d07403040e42c0344000c080c030b0340f100d000b0144920109007001990709200b10016040c400c0c003074030180c00790b804001c10b130024076004000c03030700280c8040c44801010500040110043c0c20f208241c52910301001c0244 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886087473 1250 886086223 886086233
    0x12070503010f0204051c020637050a270f0f260604031805040515010305010e010b0409020f040b0403080c010605060306090a0203181c030605040b150a030b0904 70
    0x1015284200d009101040340810184241d024074060a50b011410f0030080c203020100084000105201803c3c450410f4002c1d800f1089a2000288aa0079104c1c1250200d034000e018143c400120856402c200b420255030344801011030b40940d4003c1c203020f0b540c90080903018207400040c0c0007401e10180c4e200c40c2d0f41d100d01c01c00c017100c8801d1041085200e4854012450b842c050b040e40d50102c913a620003002c4540e940c0c3c404403003d5082841c51307248800102c02c041008e84541c001c0030b2054942c440f0a40e04014024001000c441050b40560400c80141d001405990281001c84080350b420160142e116003109030010858403d581c01441002d8000800004001c07600d03020301185020840200f12942c1c1d514144101440202c0c1c280394460640d00005d842649958099034200545042e0307400d4131245009140d20b4050400d9030483e04030180b61160f48510f60602442c0c010b00340a803800d01000600002255500d888010381070f01015001c5048088948264440319180400824101c03950405041c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886088723 1250 886087473 886087483
    0x3080a020c2b170c15041217060d03090806070804020a090b0a03031b0c0e180c0d29040317220b06041107080d0c020706020706051812 59
    0xe030052080c0d81c0b0382030b66040c07142c014209000d00c100303000c034126400d80d0390501c56081d605075081104809100d1100a40e40801080c918203011101d00346282c1400d003082c00c48403019001078020890705030f4540000c1c66103c5034054010000762019022042e0a00d001d9410701c1a581001d105882070104200520341c0c0003180c0e81c0250700960b070030440140c48034050030580740c2e40503100e500240ca031281040000e10483e022001e250715800d80c10000140d0395a0203052080c160f018440203642e40c02404070790000d6061000103100c64000404007680810085500740311411805070501c0c45048080600b035485801c4180841605414080903240514015144c1e11480c42d441060162520000700400d4800518244000d040c0c40c804680070810350343c49041c504010459a0400e80701c0302001d02902c0d000b80500013180c858002c40da02c03110980b181c2811110030307030301c2241103621812081000c585c0201d66441a80c4043c509240d0700d814402c001c3c1021551008500c0d00602c2006400300b14a8010039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886089973 1250 886088723 886088743
    0x61c0e12031f080615060d0212130c120c180b09090d030c08010e150105090402120a1121090115081c0201110f030621060f063703080a02 60
    0x41c40c10003264440300481e80d10f140c02c0700d541031762401d0703e286202c4518100010300308411909801510700b481c4102c1802200c502580c841802d4050002181d04200b491441700003c0d140032680400c9000305a240e00110030300a120b0a800400d54641c0c8181800c420f8100d4121103c0241003e402c42c14000901d607581d4a0079250312000030310700b1712400e012501c10f1200504071079107608154880d480b5002d2540701da400e0000440d0505c041041a00303000d0301d0b2400a400c01d0812810300103058541011341c4030a4030050500d20082c004c040254440d05d02100240124480b16003090108030303560035404a00400c401c03980400000c210400c001448000002c411401088c00d1a1083d81c1c146e00e90300580c01d8888038245070b500c4c0c6209000b82d42c0502c1503200a1984030760002c064243d50b020791046101c070160440000141600050108180f410300ca00d0140e0300110181c40f65200e000c0756035010141c000e03805c8401a4400801d1421807010034110000001640d0820803095481d03200c1d07a0702940d0350059035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886091223 1250 886089973 886090021
    0x721020304031b030209010b0c0703140a170408060c1b012a080603031605030d0615090e0106050301050d020409060c0203090f091918150902040b061c0e1203 69
    0x41034074103050700d0f0f240703500f4200d9034042d0122007164200000c60364260411034004020b84203054002020400105548040d540888080c0610742000d05014441c03080c1c85102c442c4041d820402000415400207049a01003504409140c540c04904000454840d078804006001d60038020351103940e1500c08480042c0c0c451000c80b082d8a824034050503101e0900460b40e5070b5043d002071010780041100f86420748846882007003070301d180c40825000f840445249030043c1c9100500903042d50b840d25040040d000103004640c0c4111059031502d04010600c1c4030501440c1c0c0030b61a4410034000b19212904000f072441d500074410300c01103030641e40003543c0707070031481583d403142a0703c2403400c80c1410b01c2410540501100e618a4029143d584070000c05410780806820741ca0180081071004140c00318524a4a20702010740401c020030700380100000d1307502c0c1002083c400ea4007008241100d01c420300c0041c1c0045081000401c100d4004500d0f14101140e801244424010000070090391a85584200c14403100c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886092473 1250 886091223 886091243
    0x90102040611010b030c152502040c05040b041a0d0513050c0f1507051603061401090e0312070e0414060a08030703050a11070f0e1b0f0d02072102030403 67
    0x85802c103090b288000c0e08940c060f00804040d20030781c00c0620205c940301e951011078030715107509888030020b803e44100c40320b004680180200e4007145081d000300d2580c4a558a0443d007414101480c103081031107648281c1c00400031500c1d1030b50000b40184140d509030084004100151b260190030a400411110800c55950181c9000d2401c00e03c0c1404810703003000c0c1c02402a454a0004101480c0c040c0d105010613102845440718603807059820410340e4014600c60700c0003003050000d00200103038903001a00070b00e004606155809110020010542c2c0712003062280401b444d440700c0c1005e5404a80031080d81d0340060078148403404107441e01900c14040c48007078030204020b940d55001e8540700d008442006000070320401103041010712480d005001c60a1140c00c1c3e130421540e620000e520018103501c8045e044516004200800000310440e0595410072003550389030100740c07070170940144114120f200c2c882d54040f030000140f282d60301069018509119211031012030303c0b24080c1d9640c00c03a00c003ca07903034048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886093723 1250 886092473 886092497
    0x6050901030b0913030e0f030a030f02010f14060108040c08011104030308011a340b04021c0309060f0e03010c180b040509010b090409120f02071e0515070b0901020406 73
    0x1078034151141c4c0c0607850343c0501c489540d41c125039802100420a80c0041d034005003103003595003440200d1206100e516140405a1201d601a0a40e4208880348586619248880103401000741c82c1683c001c50918020010741e0b241c1c0703402c0112039100d4201c0b101c598a440c09001825031107200400985e070090311200301c0c9a0b40c1d806944c0d5265140103542c003141c803080c45410181184240010210030301c0500c4d844a003040d00c900b16044c2c20031042c1c01d07103900c5100c4003400250705200c1c00c4107907880b1501c03800c21041d100c2524007034180300d034030b2140000f0494020800e0360003500c134001d41c1c00000c13002402480004035803e0000c0a4180d0210740340c0c0d94021885000480c0031040081307804a0f2401741001005a20b80100031103550080140150096150345083c0002020301001c110050003540f2034544000c07a48100a18001d883c4c1c005005c9558032002c00695900314618030402c560080307452070121001c03640c2d9a40c46000d003035801840600c414050180045044d00500259540d0340c3c0e8030740b008d0346 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886094973 1250 886093723 886093729
    0x106080f01111c0c090b070f060b0105071703071403011e0806042607080d0c0305090c0a050f121014070e131a03030c0705030c04140115090f06050901030b 68
    0x2095003090b6150f0359000141441c4504141c00c003000619041c1018015240d40d0100742c2000c0c2d00c903000480c0d40140c1e041501d01000503505c00d80012640c00e180c071a060483e10b554001603034800160788014031901000092000744540602e091031a03940340c01c80d840303595070a43c680c000c100d83c0412510b0107212040218041c2800500d1510854014013a00d405104618003107218451380c290580703c44004202078008504a00000e011840c4450300c0000c445c141c14000a00302c0707102400c0145107030000d105140b00c595440307601c14103541003102e040b10052580d00014441c84c1d02c08940d004507000c2c500c0035140c0c14070340764840500c0700310701140b8040c41c1c0c0e00c0d42e00444506000c01e030782550290342c115a203484d40126038040c01c0e40840192802000b02045000031345580c00c4001d40e07480341c0d0320010003480345050a110b501c201460036101400b5501c030184100200d0304050003921840105c20303402035034181c030500d01c0038010070f4004001112213403924002040c55000424560219041c82e035a80c800d81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886096223 1250 886094973 886094977
    0x1c050c0c031c4b1a03010506040b3a03050d06050307030f030f201b04090f0b0718090501080c1906030c09030c0602010203100b120103080313050106080f0111 69
    0x896003501e0f418560f012a01210028a080010001d000703c05044110018240384610200306038444011014008102e04044c00d6600c0104182d0189051a8030ba0380e294480980c2d80011181d82d01c049140c1080340766507a0180010501c8000c61422043c440c0710a068014004001c038545c0304034244102a2920f06040c1d40318000c1c44002c2c001400e40c0840d2011034803a1000c0020b028040c50840b2056a806d501c0d103d00c2182525001582c0c0c110b9400982010f0098402d0390900d502035400303124800c1705881e04185021100400b4004110140000b810984640c01c17810380c0d11030740e0360212699504e82190900900090040420030321402060050524001c0c00090071001880001901182403940c00c8024005918201c2d0a10201c80400b00001704402c5203940a0a543c0d0b00050b00d030700e460150f041115000707601000701c0c1a0100800f9460088448100781500c6e0050340b1196280c40d401c0e40c14420b0210848060241d5181c040b006c55810400315944034086440002130241004101c0108158 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886097473 1250 886096223 886096271
    0x6020405100e090c0904090f060c0306051207060c02030a0c0e060a21110d1a250e011d0607050706020c010f0c0f0302150a051b1c050c0c031c 62
    0xc3d83c0c0000040144100030028108454098800305400f0304584d43c51700303810b1080300125035140c0c42c5c00107003030714561506c40e400040108461411a445450340c0d901d841d8060b6019100400c141000d002003551002c010382103c03e0b6100907451231196032040010960201902c010380700b400642c400080040030001c40200070409050741c5c1180701c2981d40d03001aa6270b04d400720035402c100300003410030120752244000e80c42d20002085c0201d0f6031820241c801c02844282d09050070358025419110401d990154450526010030b0819180d8014602d4600420680c404403065108034006070341010880d0209581046900c65000c40700680400310041d074244565009800c000f0361405003034004140142400c1000c2c0e80240141d51144070151589884100c0850303c0420080e114000d205100180c5103000740b0810402c04014248540f00780040c1030040100400381d4a1a1120040780d003111503023045941c155101011259540c0d03035800b00e00c2044201212103800c840c9413003c0d004084410720036800744 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886098723 1250 886097473 886097479
    0x90c0a0813021f0306090c020a060c050a2109020d03050c10020316030504060b0603010e01171c05130503010501290a05070f0302030910050309010507110303062101020706020405100e 80
    0x11000c2507415182d000c030f40c21500c0320708140e00c800b00000c030f211642c8100c05a05505502409407000d00341000070903640d8003100c040400101b00010b50f101580000d400e25541c410380b5001202c18041c2d4101005000225000380d48941001400c40030550854010403442e5072940a03504c0c9003072140100800c9000841d1b414a0f189110a01c6000b482d1081d400700e64040d102c0d070000030300c41c1c4005001c80d0043e04243c112601c0d5480401c01404000e003d078410b0090078485500500b00824614500f841c4840c804a110f07060000110300d001c0e0784590203104001405001c0d008108640c0e4a171940000b2038000305600c410f0004001100340886468030488003005000d0711060f19182d100c0d0f8480d141701001c2d0301e0030707011408148860740717480c0c0d07401613080c011100c561b44481d140d080c04034445003110310143c140e070203101203180e178900c1e4158040190703940500115550f580a01103054929407030b0b021040b08041c5544009960700800400c1e5000c3c2c82510300c141c440c48a0703800200c03020344084036017030041a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886099973 1250 886098723 886098739
    0xf0c081b1915020f130b041a0304080a0c020d0b090304090b06091e1f0806210615010306030b091e070602060105061305061b2e0c020705090c0a081302 66
    0x214032105400a04c094919a0308071480c0c40c02441040c050090325800184881800103410003802000c0c0714920f1801e225a0602807450030690759401641c45088080000d00a0015185081d03540740d10b0031021842c0c010040c8801846d00d43c00c0030340c60f5840b0f80510341201c1d01c0d1030280181e50806009550300100040c0949100c03a00344203459000203a001079080d4090b038000786912419030b81c0a000040c40d40280c5640003141002e00c10031000041400303c100d400001104c40300d88a050000ea00f40d004070420810200300710026004074050103540d00080c1800e030703420003805219240080c0c076242801400c050190148000e41101e40c0b1020a4804c40005901c020014420344c40d028005011484112403c1d20803d9641c00209600f80c009440030b05d40c00c1c003000303003100d007980f001e011850314403804140032100040120207042840d00c4208106446503038900d41501e103140200076070360181900078448411850226020342e601e61182d01c1c6e03040018851408036590000302080045030aa00425500e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 886101223 1250 886099973 886100003
    0x13f1202070303091802091c020102060604092001140a0207031502030108250513140105060f072306040c03060e060709120606051914090114010f0c081b19 68
    0x40c880c0061002c541c040c0b45d00f0802003e8a40d140e610142000c23004844010445216000190812100900d09805681400b07180e100080c2c0c5058035841901640211201c25580b541c0101e9182d1039a1a50609010380000c640050680001c0c020b02100e02c07482a1089188580e100075050340000e00c0f44007070a5000740c050400e12040a910b429a440030b164007400850354a034000713180103090300d40d403142c0c45544041c0350541c403200c0c194580c003500c0d00351000361a00b81118107640141c49440e1000d01801c00150340460354106021551030602c44460480d2180c1c102414481004500c07440112466032502c0d0141080d4000451224425a215107500340c0e003529200034091410f9071123604440c7d241d80c0704808901d9565256403852448480350455046505242c114482904159503051058071840010007960b00c8012034080118003c0c038004030300e001d048000351518070301204000d1000c80082000c14660080e1542001812484421610841034012604071102000d000c060139100742c0003158 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 886102473 1250 886101223 886101239
    0x20040306180507120f2003012f07020f030106032405040c0308090d050d08150301061815090504030c0209060f0d02060307050d05010b041a0f03013f120207030309 71
    0x24038a03080c082d040c811988000e643c0c0341c88406c2d0155901800907241070b05589010b00b424403031200294120f9030048140703007942216211a0034180c0e129506003a0000e056011500c80d0b500300ba40c005c4000d0001c4c00b8403074480c50045240110f6150441d03003409441881140d403c40c501880d4015504800800a01d904544410740380b0f503c041c0c1c080f40c1201c0d15021660014104205000a40c8541c2d5100d1505062140340c00340c900c5010440ca610980c140041802000148504003021440da0745000840f046500644101d00425610103000c49151504020515400c00c20380d00e030f464403c81e2159002d42d2104100030288028118254104261502c2c0710010b0400f0300c020768000340a400d002d81000641c1c040c0c8400c0c3c40b000d0308600400c41022804001c0140340a0800c0551810359071014103010b4003a0b0a02c1d9a80014030039a03c41c0500602c036071595007408030006a800d801002092882c0100c800e00c40c0385a01150800c884000301c21040f407803460f01c085050403c2e2585651126000d910342025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 886103723 1250 886102473 886102499
    0x18021923060c030d140604110d02160206070f11150a030902031011120c0c0d0e0406260c01090b07060b030f0a0c060e01090f0e040620040306180507 65
    0x20340350010000c015005450b03104101030407000d01a424080341c40c01e100c00d9111307850b5001509950090b0f0501c4500700c0356a000c4003d891035400360010068507002040d40451740d4100f8050003035084540011082e0511440030204000c850254103170500c510120300070b0191414502c11888222501400300300416032098100d82500c40c001411a04a40340410407001210f1122403003491300c80340003481c540c040003901142c55002c43c0e514451821700c00912880c0351260103108030182007003203e004200c525a1a80d018030080d010000880c000121441c00758a245d01e1449600050f034412600300299540c46401884152506041041d080c400d041c1e582d480984800083d441d494000c8040f84160100200003000702e42d070090b00c3c00c0c0145850a0700c0500610881030815040195818050061008043c0711000320bd04d0080564600c3c5e94505081e0000c5c1092841d0302c03540801240b1200704031080002810641e4080d00d410040e02d82c5111140e145e118440400505ca03030400c610400148810100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 886104973 1250 886103723 886103789
    0x403020121050a020a0806030102032a0d0f020d0b09061c05100203070507020108091c0f1b03020d020c18040204050c041d16080402030a0602030910180219 68
    0x20320a0400c5a030442008140c0b44226801d95150f030307010946803031090307000509a4018a054008624505040140762915213405000c2c8404070384003404024543c5000341201c11451454008210301a1010100006075200ca80d40a40d15810540502c0c42031401480841c01043c004024414040e00000d010144251510041d20030f4010303040300302c44a6500c0d0000f1403040b44581d551665890203480003401c403072406400355489601c400c5152124280030310000c0b0006040c1c0c1000c1444000c405d4048541c080f035485002400f200c40c00420003010340000340d000f04c500701030b000c1d140c500c9030900c05c4c40740e0860011884541c21001002240150416034030041e0040760006000d882d10303403103c038021a00b10035105202d9544049804000141c80010903940362081130385854001810190006070b0744143d4000050300d00e42d4000003103508039004000110814100f16011f00a80d9000142080b202255050985c09500c5030f60040c0b000c00050704240341540d217082000303d680d8199141401030192401c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 886106223 1250 886104973 886105007
    0xe100906080a09020a09091a1e04020a030f230309030a11031203010e04020307060309050312070e0d030503010807060513120f0c0e07020c0f1305130c0e0f060d030504030201 76
    0x6561080941c5039900c030407001d0040c0f95004902442c0910f0f000c50008c458210301d003206a40d01c1c042c03107010358015190902450780380360410036949681c000602251569840100603c5010880c0300410600070307802c810749181881c0ea801480a000c042c2070300ca1207085446a45a0401c9010b480015203c46041c03413005070241c1100c10180e10001d00c900968020b07081814080c031000100f00462508004a40c060121807400b40031841e0385130344480c0d890203000000592403041c800002c10180c400c0c2a035620117100140302281401503420f016000754000c0c01141514020660b02140f0140504115001c0c03400542d41281c1c0b10785800001c0c0441c0303900460031100f00d20780c40002c04c0032a900400c042d0240900e8075481560703080c5440044e1030000f000014034001c16402c2903580e09555000c00b12085950003000105d00d40e070315160b404030b503081c0a00d001030980c45464000b0072401c00119013544a100981440f001d203803140c40c20440c03091003101005000820421050006500c0b80218080d0740d0011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 886107473 1250 886106223 886106231
    0x2304060309050c2413090c08160207030c1809021c0c05030a0201090b070c050406090c17010b0f090a08011805150408041403100606020d090501110304052115070e100906080a 76
    0x14031011b0f06031120a1000b030001260402031000011030b000c62510040c483d40001e040803407942d07480b03180b90310b10343c0314044c440b010284860124a0890304281c98842c0e004005500800344004402c0e030f0010025400e0b102d242d079140000c28107090000d10311290366016103907002c2103403800b60a070041d94405801100c070340d856000c00240c00e482d41c7c014500030b024000e4000c510040d044200030040c5004002c0071740f0b5040c091004001d4041c03014104c0c0c494142c059102a510903075007000c52464510303907100b0042076117440c2161a031201032202400003544108250f80700a641c1c0724402c0c00c0c004041d0360203892380d00c04001c00c00c86100b40b009860601000501580e0007001c6246108007280c80700d038460009038000c20111f61075036600c54020800303080e003420303c1c0c05038400c42401c5640d680118054140034150740a112481c21031201045260000d45804441400ca440c1c2c02c86620000b0681d641c40114600c0d0000c80500e141031428124800300c41e585401c0c1c007600d0110308480200c400f4005a128640c1c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 886108723 1250 886107473 886107479
    0x304140105100303081609051e1306170a1a0a1404050709060801020c0c040507090e13020112051303230706061802192304060309050c2413 61
    0x80c01418422040d80b440031448034038505000c2c0c40395a0003032000c00c00040740c1c1c4460000b241c00c0800303141a11400d0300c100c08095540301c010b03550f88008070365582d401081e881d848061440190001001d96aa06403456403950341c0120b45c90780c0e148030400061105241010f00d0184464810300c0580c404a020008034101042001040b00e50000752000c1d00c180d0001c0710113106050141c041d210082c02c000c03001718035021008000e42e464a00c00d00e4104c0c8229150b50200700c000d4400d41c9154050185100c0e41805410142d02200054240040490100740503103801680146903204581c0b04a00e510f40c40c00800301142c3d0100d40001450442084c5003504c01c0007440e140e014403000d040c02c03600c6081d000030a10b00b01a030211004840c02104452940100410b0000920500c4d00400c04851410103c5c8201c0f8034800c09800804e400350552000500821300080d03180e4942c02803c41d6900507800c0d6010104103c0034007041e0011030f401002d074502240cc40500c0c1500d03280041036111840b09034100c3c2d19072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 886109973 1250 886108723 886108763
    0x10605091801170f060105011209050106050a180605040218040b0406080d020c03070803040510080901060b070f060b0d050705060d021309271707080d150612060b09060304 75
    0x40c082e0440e08209203400e06101c030f00e020812090b0000621000107280c03d601d040c1c0001c01007c0c42ca801c0c200702d80d40342c001010822009400c0b403806010000c00d20141142c4410301c81c5840c0e0304c2031400b412002d04025001526082c5442101c4c004551607140040d589004000e000103404070b19401a0041d40d0740800107400b200a20400c503032200b060703001d4118201c004042504d44100f07600001081d4100b048101b03e107648200411754049858200000c05c0d07503032504c4e124014081c50740f180f00c0200e4001440c10801400e290301c800c005120780c004012220f031000901c408900003820040465100f20014030051421314003914111098180142c5440e058561405044010fa031010708042d8680400c3c12024080101d140100302c80442a51910314503921071208068050010324074800c800104a0248454070048403242c99407002c00740106003284030704020311000d501c116400a841e034480c6440310b40b0540145404c454801d2072880c01c01c00d02408004c501d81c405172040b16108031040310141805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 886111223 1250 886109973 886110019
    0xd0507050c012d0e1905010501090606020c0f0108220605010302180705160305270a080d080402190305070b0405031c080403120609180c090b0901060509 67
    0x41095900e250700c41c0640407040c0e0039500300d01c10040c810590741965484265106410400000604401042d008034440c421803e00703e00003007240541c1c10750743c070440030b00c041508a10704907010b881c410494281d072940100c0c1c980840c09141d0b0ba12035000c1c42205115071084140f2504608801400c2244c0c00021004e00c0410b2040401103590f207031a03a0040013035240c2071103075204c0381c1101ea590340340510300388030700500343c0c07141802422000140e84041401c1c14070031019034150386a24082100d0310010760f0000e21032649840c070224441c4da5120800700d042c800c045106840d0840a84500341651655420412107121000855084102076040080411420021a001008026202961682044d0505052503a121800500c81049101504e812131303004d60050703482909032070014000b14081034120084c2c42581d0000c00c00c030741000c260040d4690083c600702a0b140c4600c9940e103140f43d0750794007007050f80c6444900b40e92059201004105141c0214020f184060008001802142e890400410760b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 886112473 1250 886111223 886111231
    0x602090d03020c0411071e0611120a0606021237171506030402010309240b281205010906050c0913050606041e0e070206190209100c05030d05 62
    0x10f0340030148403400c1c3d060510a249485000300b590626010050300c071040c4044031010440b804148414200c018013440e503000a00140000321104d030382e00204980b00b00c0002080c1d92513036015251810001d111400001c51140d4079060b607001c503040ca0100c840408003030180880305c0a105101106c91040005d8030104545010150b4035854410700c000f0308040021900145020151752234440c006407196200410359510076030919011520000e140740c41000400220950050b058031200c409201451030340000c001c1031002d4600d46c141003035103039801085080310100c40400e02822a0107025444070a039121075081d000300c0000c26441d504d035903070200b00d034070444e0b902c2c1c11164049218081362503c4417092a6405070035005204a040060004480307220364440e12001d13041106042645920001c2d030b00c801001c1d01c1054058038a007040c00a034940700100da850710742521082d00160382100e02e10960707100c100041c003c1003401003600070940787c4040c0054181c81030300c82405441080d80a900416210f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 886113723 1250 886112473 886112477
    0x40f0501142416120c020f09132010173106051902070309051c0b0f0601020d08010e0c13080129010f0503040602072303091905090f040602090d03 64
    0x880f88050a081903038141107402c800c2041558841c0001507903405114000c640c00440d2441965251200309003100704c00081c00400b00d044001002c2c0c018030f0200d0000c030740c00c0c1040c1c0b00344818106000003100c0c404600d490406580c000700700807820718108000b070713200496406080b80d80d2051140341000d80c1103005100846205488000300180c0e4000c2d0b040c1c114481a5008080d81484015130f00900058a9030059600460001c04030982c6d13031612500030411160043d2144980f410218400c0e00742031800c070f99083c0903204101c40140d4051184031071170304841c0041c0107030902e503d07050030346200382e801030300c1c1117025105052001c1039058080c4a408212403080c0d00c41a80c54007081003841d003010001c10403034140040242090385a40c0c006e030807a540b01c0e51241c00141c0e239418a142c0801581c0d00741010440207100c00400c04140c00c03002004007140e60044418909003e42e01b0642c0300440c1046c0512500b040c204008a48007641c60159039420612504003d0b0503c408000881c102e140022402d0300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 886114973 1250 886113723 886113757
    0xa0b030f06090c0a060528030f09080903060f0907060c1b2c09070e0604090503040e071b0c090507030e0d09061202040602030714100609060302040f05011424 69
    0x60714039204d202c6400800480c02c210b4244205001000c184607502e100030b00d00920700c036440700e00c002e1007944604182031070400b0800241e0850304002480c2d801c8545150f0007445000046070703515054040c3c0500c50303038401c001494a9414200c0440e907040c100c26044035058811448905448440389454001d8100305071180303800c9000b00090307042ca1098203840c103403c000c3c03d010b00081d40d00c0407444400b41e9000e071a0540b5141ca0300000f20700100801800030b0003901006c0350100c0d81102d41d554443c043c030700c981c1d500c4006007014020304d00601000b0342c0041c1b10f1039500300200b0400c10950456a88680241000540380c03038903500107801c200b03d03124803000180391140305104d401d40100c2d07245c6100010060440c2800d0070880043d650388206034000d4070425560240b4841c4800804c08202c0707819160000b071050990b1840d0f440d0140c000303804120300c41c0f420550407020090661041c01d0403034074002c941a080c42051410f0100c03200000d500c0542d242d003060002010316010754001c060b088600c0c0c00c060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 886116223 1250 886114973 886114993
    0xf11060f09011709030d110912070602060907050303030402011202090d060c030c03023a020d02130b090a061107030803180d0207080d2f01060905090309090a0b030f0609 74
    0x4007102d5110032035044200e0781d0004d004800e60000140d441401e4000400622514810700c4c0919501528101f103510450768088405111804580070048a40940072100309444994546444220354002e080c2c060744140000350166101d428180002c40c0416001807900344048003180c083d00085009560064554200f140d02c0c030b600d4070480e00200c04030b1808509240800c00501900d00000110f00018000803001d03c0c801d06450000034111907000070110350b540541342914019401064180b12509008074000402014410460314001d0008245003065420200c0503100400032400301080b81c46007600200c000b40880000b076004000d07a80c06002c0341104100041e1608280740081011904220030800080d035001458030190003030741c240704a0304000d81103c0315410000c0400101c060100384559400f9075410350100b41030312240d50003440130781c0c2c2c2e20b418203035a071082c0341e44c90b604071405030300040c100c4035640d0002e0342c4500c0c014152884000b984074400d1034440b0540d9240c110341c11002d185 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 886117473 1250 886116223 886116227
    0x2010b011404050a0b07051204080c0a05010c0b061005130b03041e030c0303020a17040b060a09020a0e0d060f0518100501060c12350108010501120f11060f0901 70
    0x100780c221000c4076500e8542810300c00451440d103014400c00d03405000200d4210308018042c000740d0303c000c0b4200006911641c1c1c646000395115104880c042c06640846000b168079442907000645094000f8110f07001501d4010074040f4400c805065413042000a00c00101d440300040701140007041c00440d22034890a15040201800c1d102242c0082403a0a100c04000001d401400820007550107040051f202c0c0b84030081035680495005004ca0b56411981c204404c10504007500350060400399000e140203500e45c4502c0d012072050480a03008a1461000d03981e0510704422001456031080c140411144451508d40040c1e4405480e852120100795656030756026003040066218080c1c0d0740c060100f94900200074107030310481600a4080c0c1d1072051200c20142c020101c02498410a118404000450041244c6248410013103404d140b8610b2000282401e414010385040e240416000b03041c060380b41d984e080322009030844c00c0b00c101030420f1010308203a4842000c0d16008402080c1c00303981e94461400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 886118723 1250 886117473 886117487
    0x909062101050a0e061e07050304031b12030b030609070510020304030501061716180522060f0e1c030e0f0f1011030f0105041122030501050603150c091f02010b01 71
    0x10101400c42c50140740528100281c0030147c016103c1c0c1002581c1e522141001c0301c3c07400801006040d440340c51481c0c0f000b0480b400b510140d11500954040003401c1101c020903444280696040002c1d900c0700800b44598a07150200f103406540307500440c1d252070346d07940d10103003525259484a40b240f001c001540301040814419107100c030f14400c1c0d5055009041841c010783e502c80382d2020010145d070343c4001030f60b800c0502e240c04c1c01e140031800d5844041c8409180c080b001e401d51540b840c0e5642c0c01c02e14020545440011240d0142c44a03c04003407075013074400000c130010054450360b08480d209492411421101c10300c9041241c200000103403060903040b500540c180d545a01c1c041d10036031010420084040d1002c1001c506480040f034011a900b2105020222640034858084e007801030030084480181413490718500489104000a0200765100d400300b54444003d445204481007813400068807110302c0030002c2161000092144002c030000303140105103000c0c034031015000340c0e5595204044560b00f1541e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 886119973 1250 886118723 886118731
    0xe130209090c0f0909031206010c02060d09022701120c051002070e070f0e10020705062d04050102100216141608070f0905091212010f08030909062101050a0e06 70
    0x1000c40b40345c1844410640c0d203208908400d2005e21843c804150180e01c40c1c040703401920303001854961a451002e5100c0010011000100d104102c400c4110800c03096403ca020039062202803203502d56844c104c1d0102c1d02c07030351010b011201c2844170040802c00d81d4a2000081130f4010590003490040d041c1040d03c40d032074502412060038454070651700c502095200540000b61182607640c0e4440006400050386050380039040a9408440032811201c280712425618134161800c14a90128170030710b040c0014240304601030700740181c122400580a6401036002412240e070141c2580c0d1948680d81c0320764440c0103001c201c40e40c064006030382c0141c112196540c0c800c00f500c3c84502404180d8503002c4003420a00c128441c0c0142c1c0394507480054541c200c1440358000303c010b0300c812140c0c0c91018100300051400240074280305442e011030042a4100c002040d1a4540d02c054035107113032a240c2c4c03010410030392241d030404400340b0000d820405003a0303000e008141c011500340c0300200300407074101c040e80d081c218014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 886121223 1250 886119973 886119979
    0x412050403110d0f0c080d02100204030201170c04030b01030803151e2103030a0c12050408070b0612010c0305011a2d07051203060a09150e130209090c0f 67
    0x80010300106107020500c0ca04500115030f000200c1c01103183c1000d0f0040c18100c041c05c0e40c1c0d00d02e040000c21001c0070074516066103195007030700c0840b031714442610100e000b03c0c00b010f40004c80400703400840c07080c0d00d03241c2500103031210182c03814140d03039175241d04802000340c108a91582010082c484681c02000c00014284801c8441c1000300441c894400440e0340d07112905845040e10042d0b207145003641503d10f540c2d4880306420769a480ca002c40012000c0c0510318802000549055520002210a071280314051036001c102c0625104258807194501c100240c14540c0c000b1000c0104468248248600b25211500d038401080540c58102d04034602d5511203a10312828100b00a000742d1103c40740340c1440e04601903443c40c54008600381003c400b6020307080e00101644198901d591046041c0c00c0034600c00d02d001c54403500c0850b00c0d810700c3e00c01d42d0b01e055a051021303032121005010701d4034051340c8580d0041c0070080d072404100c00e580004981c8541070301c500000d50450005071070b10303040206c003503000c1460a03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 886122473 1250 886121223 886121227
    0x509031c020924300903160318080a060b090601030b030a080307020703080a0804170426120f07021c050a1e080a1709120a0818010212041205 62
    0x980104000c034902d0801400600585081050503400c0079055403000801c0c0c04c0040030034281d800710082c0030203140c003030b880402120b1000070b41e8040d0300100721400441480308942445500d55001e0340c807254004008021030284810103d6006410010105003078028100403800030701076418804e0519019089904150800ca031440d01a03e00041c540086640a180940d4981d40d94a0072418548140c000400900c00010030a0300560f100e40a280264000d084071604040d00d43e10705805031040f40b007400400482a0a0202600020054810400e21a4003602c0840810035044a80d0b80c0c04803010407490500070515900354204011003815411494031070400c0600c00d0307128681c0d00c50703580310000c00200d484010301504084031200785c0d22460380700c02525201c0c8a400d90181071040c00e00c040d404d030703d601a0000740c5800800519014401e0f43c510107030f454140414001c661100c40180101c00c0100c0170a000c0f815000309200900c500c3c4006512144d040c10113103804091001c550b28000100401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 886123723 1250 886122473 886122487
    0x51f0b1011190510091b0501030b0d060f0605030613030201110306061c0e120703031a061c0b0a141305010803030a0c021f05070f11030a0c080d0509031c02 68
    0x70004000305040e05155480d035aa403038900d04079180600c143c150700e8660781402c0c007120801c40c550140000712005420745ea203256444000440c100c40f008401c45a125450307104480218005a000150b0140701035804141903807240c01181c82d0100c00e880500d590341c00078008806060f07080c8161000c2c0030300b60342494507604010700000c1150084c0305080002c002e000304a01c100500d60b502101c1d10303900e28002c0e40c0d000c0344c0da0501d11803e40c1081c00180d011030b007440c1d840c450b01140b00b03144280090000701014104820013000d00d1402d80c0f503140886400d40c2e50018550607070ba540450300003c000c100b40040c4903a04a4007407041e141c8686c002c3d19445800c003001408007190100a69901035030220f000108000c200d0380c01ca01c0d04c071820305003032400e82c80101000b528000301e4100500c01e071b182c1d46034a0030710078480310229070743d030560741414170150820b2102030902e6210b41c0110204501034080c190402049001314412030380240d54401e140ea00004401d1500300c0d8540c100da690401e00223085041a40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 886124973 1250 886123723 886123757
    0xe090f150103022101180b06090f070e030c09010306061e080c0f04140a0b0405060126091212150d0506040308060402130b030906131707051f0b10 64
    0x18042c08001d101d1040c8a011011a1012450041122910b40000c0c09410303048102062071441100d0709444004100001460500304068040d005d004444082001603aa0640888031625203c4885a1501512007145150340c1c81c007400d18065402802e00140e1945040c103110812046021500800200010100b010400101d40d50504010643e07600c400f44184200240042502c420000b00c03942c400003d0000b401c001398402180014291402c124541b00c0074010350314001000c0c0c22801000b9440c1000661800440c02160861074100072100800e56a8610a8090f0070010b41c54600c94040c4081020001142c1e10b4482204010394034104140c0c091344a10351140d2004001501784604017020801e05e4030ba40d8119098818035801050605460740790f0091150b01c25101980d0a00c50400400c0c18a0101040c1d000c0941c0d104802c070b506c2c0d02d03045440078bc0c150007603901031743d060041c0b92070040540100340d01051243c2d403c0d10000b404d41e204000b0402001d01c80101a0200085045d401d04061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 886126223 1250 886124973 886125013
    0x1503030903030309050c061b010c052d0d051608010b0310150e1201060602010605040b030619090c0e0412020a081606020c01060b0a08012907031106010e090f 69
    0xb03405150105035500c0c1d40c10310034500b42c40b00e0105500007500068441c41910f41c0820000840702c0c110007404200d07c541004c40780c03401810316036400f8040000e41c285070301140d11203080302c105030100c1e01d07802d0040703012401048610482d02d42a500ba020841c400d03840303600081e401c3c013412510205500f50708050254200c00c121078012620b6550041603407039200780c000c410010210100a00000e601500d80344414007074070b0244601c502641c00c050000c11342d45058040d201c40740c0005001410540d03a8441c4c492001400241c180f441c81e83c0d10241c002c003043d02d44203000060518082e21080e1410a0b183c000803c00188a45100710740020000000080e90b54003295803035901070310716500f62140c9040400007445030480ca0500c41d0318088001840c0c0f160f0b400a440a02d0854036203c039503030b81e24152805110b459401583c81821954910000074500c6070107003051a01030300d0103003007081039041d0f443d151500a030030009525811004004440310100803030080303000020702801d0003080c0d1103461241a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 886127473 1250 886126223 886126229
    0x170705030702040c031517010f0e0d050304150501030807120e032a181006050f190306030f1a15090c0a020f030430080d110415110115030309 62
    0x31510307440004c20403886900041403800b190002c1c4e004ca01d175200001001802c450014035041d5090801080c4400202e10400900c5000341d00640a01048030034115043c0c1d000800495458001d00d02c00e145100040c410240a9485040c10307540e900081c0c1406040420030351001010003e448003011100e403008507001e403000c8000c0200e00344030a01d1450814040e030350b076100c00d50024500b409400100200c0420306000304404d0941d070061680b80c070070031a0b080c80382ca82d264444110800c0f44d00c071001a00b111240c50b250180c900001c00d00d4503a682d001c0c00341d800c9042a10303001c0b1030301c0100042510340a00a07411a916000d46c90160030324002040b1841c0c0d0050414800103400700361031048500030300504018000d4a015281ea4544072100a1104114100301e41400d20f086050b400c2141c416240b8003200d5134001d80c08038105014414050041c04603010b00c1c01e4104401d001c001149090081c0c07032613030300c0a5500d45a8941c078110303204d5403c4905010301588100c6c440d800030004290000b007e4016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 886128723 1250 886127473 886127479
    0x108010b03011d06030c0d06060e011401080708071202070506040303060e1b07050339030708040509090109120f030e0109020f13201207020607140d14040807170705030702 75
    0x140c0c0c4c45a0019091941c0348000940000004c158001040103e500c0300c4281c8803a899190486c0c0d0301e404140848070303201c51100340441d510502245849000307908555110700c1c24070340b440030360300f071004814180e0304582004c65595200405000403d44c241c001c09001d407120710b01204d15031a001040c0702001c1d1003204115445880018058107000b41030080f640d03008600d02580303d002000c00d401f0507042c9031600346170007900f00c40820102e000e40040b0459501c030740c005058504080c08c1c0300c1004511100030341401361540d625454800001d0491100c0943d140b40d980b241c610011041304041d09035503040750403240e40d0f40340c01c0e55600140e07100f1100b04400482940c010030241454900d400050001d210a0043c0c4201030a0f000407000c060b0000b0071000c0d80000340004246c980d60010399a6030000d40c0e514010507201c110140b4030305840400b803c1c0019600a01044014640b001c03d00405d1040d18240d842190018012091001c8012000040ca07010a01c00349007001640b00c40c0e84a0099800c0244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 886129973 1250 886128723 886128779
    0xf031a04021f050d050f07260610020309040524030f0d030b0105040b04271b052b0c0e01110606010318200a080d0e09040c0f030c050108010b0301 64
    0x84900c3c41502a5910041203940810081c10a00c0c00182c05460844000d80015440c00044210249614505002414490341b104c40c988603d020044086003d54031171085100038403500c005550f447c0142030107040c60b8904070604010200c402c800c5070a0481d0121f01980c000c44500180e803c00207549220344641d45400905140040012111441180d015580e41917020a000c0b4954007249501100b4044002c801e003500c1004903400000c0e0385119456100c400311400e2800c4226000780c00500c17619946161f5560b805500c2000c4440304411110b8550038144d584040b6040b09800c030000d04408038003400c0440c5481e42d41015942e03140401422a81095160701c0c074604021401600700c10a25404444450a90f81004d031281e0540c05081ba0b180c0719810814001445d1800070652450741155603aa09a80b5008481401900031001d08100d8040510a80005402c41036049410213944070390101c441e114a130800040074404180c20000c0004010401000740c050003580f102e61603152803180e14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 886131223 1250 886129973 886130029
    0x20c01080412050403020a0e010807050121050c0c0a05211213051507050a03201e0c0106060206040309060206010e06040c27090f14060d050a0c0f031a0402 68
    0x2140f034060703948020341000300c600c4041051086c2c4c100780360580f904141100e401c0c40c0e841d801100d0f05800841d13056064440d10500003101e04690704559070208050f0103281c50030441c00300e130030300e00301d02c40f5402c3d180c2d5000790740b8182072043c1e50341c0707107200e42c0e0000d0f41c2103400e1084501206205180c0034021000a082c8420b48400304001800b80040e40c8a00d0800c44000d0700d0540c00241240d0f02070741000000074a40742c5106900c0040ca9020b44148a082550b14180030f43c0011301d21042d01480506004071205001c0c52001100900489029003031a90140c5014100f628000e001200590404015900200014481606249a169031150b401c0364045000e00043c41e003502d10b0300e20344102c5007680c038001350301d190341a40d0450312504441030150f0810551085420304001c0303800080b0b040f185540f050340812520b1801c0703404003075200d0040058400349205039079490b6826000781c1c040f208200c0d010381c04100740410f800c0140043d1980c900d05042515281e800200901150661011b1160205244c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 886132473 1250 886131223 886131227
    0x507052805102f010516031506020606010c0602070807060b09130b04020105280e1c12180f0905060f04050f0c0309010b06070807060506011b11060c06040303050103050d020c01080412 80
    0x20039030000f9600020095410940d00e40c0d04c42180d10307000788000c242005c2c00c0050070824200d00200300c3c0e10039805060151680801110a410046c00c1551681d4090001801140d880b00051001502c0340d24000b034009008401d00401800050401c8500f00811150700c0208468100c005c1d07000b03a0910308141e44131642003805c01d82c0d0741500040a0351505c581c0704041e1254200d030118007801e10460b299148503101c40c40c055942c0824020040c2020050142c804945000301100060000f0122540e1a80794841c001c00d21900c40544c48a462162190180155800c03c103c41403040314094800340468500409030403c0340d400039202c003054400010000d01101003c2d8030401034a080144802c2e620296414030103841c0d004150150703005841c11000c141190302541c4890813030052214004510203440d00c82c2c10541d880301031003641040c0c3c00c2003008400c0300140045403060b032003038400040d81e505500b00341c0e02e80343c0b01c2807002c425580404901070950782c000200a2344683d201c020070010701008041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 886133723 1250 886132473 886132547
    0x6180f030f030709052b140a240903090b0a03110a05071e02061602010e040e0307171e0901090e010306090b07140d0f0b0d05070e0f06010912050705280510 68
    0x140c10003801234082d1002046298030502c8002c07581c550071440c01049801114045500b06180100402c49202042100d500d804020f8052000783e420002006012075103010402d5200c0c1203d040003c600040c220100003110400003031480780c0c2110944c508030598080352491041c90302104d00d18110200900441e8403454180c162114040c10a2210284004056589800c502c8048038030010480029501c0c2c035200041d2254940030003000c1220030140c841c910740c2540078110460410503e844042400c400d00841580250300c66500002c1c03c508608051111440c05070140003000380c4105101f000c004c450b815178000d03001e010b03000100450352402d19401000c201c03c0700740e00205043c0d40d010510401048481c00c42d980d5503407101142d80c2b41d856403000d1850031568140412046202481429a0808080015489070045540f12034030342c00090100708510000400c4218240c0d0788014a20b841c1c01810000e041c00e841d410310b040c6000e100a0044030300302d204030340c020200c0140180c0d0f031000480c4c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 886134973 1250 886133723 886133753
    0x120703140d0f020c0307030e0f0109030b100e15030d0c08031504020c2407080c030c25140705031603060209010c21030608030702010206180f030f030709052b 69
    0x7900b1136a9102000041da1030350802001034010590844080046042980007141d444005941e1244c000b42160343d1151076050147c955004105400b0000c500c221060b8881802000c4900c282100c0c05110700c105450326881103130140400c03940b0041c001c001182001500c1e0450002e42103c0040d40036500494000e0082da0042030241c8a4003482c40421114011007015051142280000564849a0035110b14400b502e00640f880403c02c001800c2000c0500540001c058003d44503141c8007200001c41401401d03050b050301c01c1041c0800d8005500c50822a5100a0000354060410240c0000b004405252144006031031650005407090b540c0e8400e014081a644d401924691503040c403881ca9000c01c42d0b81d180074404245080400302c1c003044000709070303892958140d005120075660b40c821600c0500911200c6c2440e840344174000114048240701426020b18410042500d030701d4200d10041c050300c0554003444c0a240e000d849281440032400c810b080b00e40c00d9001d02d145e92104d40c9401c46c00c440d6050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 886136223 1250 886134973 886135001
    0xe0f0a0605010302010e03120a08040201171e01080c0f0402070303090f060e01141512071508160f0f08100504050109050414010c12110702060307020f120703140d 71
    0x2882085103660016040c3c1e8000e9030380504021002e000c1c103a42e01c0c070040c03c030350112000344020b01c00248110315031940309106140c003984006418548144051054800c41c071402c03840b0b83c6a403054840c8000690040070380030002d0915000800c00301c0d05110320048021300454002500f031003814040c1d0400300c81c65500c0006111460618100b000040107661540d503203c1d401d00700454a008001c140060080700c2c100400500003c6400c20001545038080d2a21440d00403404000768442900094400f000d001d03071140581858807030011b481c80941404a54240212904d240c2480ca501040c0814812600c0c03c088104e07403602c10300802941c0e22503000b40d070b10505100000c2851856504441e0055104941302300441203044800c600740c1d4444011100041c80c0000181d0301540a500311032040d90f4126a4603151403d0303500410101d500484104015a0041201502110007041020300c42031807550180e04049441c1d9008100c0d400c00e901403510601c010804800800715a03001d5010300da228 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 886137473 1250 886136223 886136233
    0xc0f05030a0804062003071d1f0305062b05011407030c03150e150109030602070302010203091b030312180703143708161a0603011406040e0f 62
    0xa074100800300241110201c80b8103040c130101001c03e01e40440c05103e98142e018600341542d40c3c1c90811905844802801c4101202041d1650003940b140484980c0811440f00504084051200d020301a20780207032501c1c2c081c0b0f641002c0004001d98401351303684c400c264294004d41c0540c0354140a40985588071020103050028000c3c04101a050780c080d92030703480c041c0c800380002002c060181030304250b281300f04070101c04c4560005500c1c8074001c03030b840041c5005041c00c10240f5200d440301c00c100d8009190480c09130794004180403d400f010007203003403d03015013058845511090b0003c6500c1e40603500213a0401d020a0002c03034036464010030076903d036015030070072101d0540ea2030401020310171030744000789460300494500c2412803072001c00c82d40c16808003020001c4081003401210048810a035407d07107080c2424001c40705008541120090711a004240700d151615586544448001e00078103001e00c680c4c5032a200e5040303005003407542030380643c04403030008407001c0022040c0e08080385460805024050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886138723 1250 886137473 886137487
    0x3060203102c0c090d020103020a091a03061918050a0905030a021f0603200a03080f190507052a060a03020c0c060708030a02090406090903120b030c0a060c0f0503 71
    0x100c0500000b082c0d0726940c80e100d5001003040b9214031584036400250949004025501a070020100a003080c0307440e905060360760111500300c0052500c1c4072003a540010902c211032901c0e428114803038154640c0248898a000310f48940c16490029501c0c0f12600c51002500c40c00140c1c0c02410403030b4004090f240d80b0300501e07400075215000140c0b03003c0d072081860090a061455441070740140d0b80c0c0407081d11185c0368862188500c81c403140800d29841a14018040002043c1340060140301c041301c2c40301c40e101c0211400e290628810746201c4420007800740728030004500c000504c3c0d8403028007010181d50300071482145d025116030340c08559400807000523111051591550060070840c092505603511000320108002440c030801401a044840034004186100c1950780101220704004100151081d60740e180e02082d1441010b068010421444404500724640e010b040100502100500740b1114801c0000b0340d0031100d40140c90404c0b00c680411020814440040d0307500507008000c881d1aa48 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 886139973 1250 886138723 886138769
    0x30c080d031d0c04020f0415091703160206030421020a020f0f03150703090c0f08150f0112020402072111070803090d031701080102041d100306020310 66
    0x20142044000a15050b103071441c42140540e8038030701c107a028000e000520294020007010b5080080154044842004002207079600d01c0040c80e64200544c640b80183c40c5002d2107922016120b08150320301d03410402c640040250510600811f03280d048500c680c880d01d850805651000d0a681e065000a50f03401a1a0a40e5000601150f102d4800c4484031b01c2002c490052204c00a4500c03e001d4040d8004201e00081d920181e0030300764070800703a10740040d41c0300182c0c8400131a465598002d14020b500d00505100600003131102c041018500141c003a0f89040c10f8400800280b4148100000c2444401003030045680300e804444499801c070194944804008c0c00b20301352100e00b611841c1c0406c980c4203904070f640b400440c0b11011104040c1c06981090610800d20000e8442d18a040782008070700c9000540b064003030a0760390701a041c410001601c0e1400c0c219404650720100103601400c64100341046010540c801c0100292580b100c00582c4945561f116200cc03c503107604969141d4481c1d21080400740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 886141223 1250 886139973 886139983
    0x90901140a05060f2505061e060105160308060105070b0a05010510020a030909090c170f0d020a0b34032c0c0d050f1605040f0b0306041506030c08 64
    0x1000464403480d03820b94501c100046881500c51405403204144224003040c200082c1c03060075803041141c04000c10320240d5a0303074280f42c1d04503108004085440c840c122510340042069a1043c03082c20a980b80c201c140f01a01e000341c542c410014100140800042c8184e4402c5041e40d400f40c0d8460030301c054500f0124000e5010f480c007406100e01801c004400480c4a0b44005082c446142c0c26458034448541085080d2024103010382003900c8070b010340c11000070101d044044002a50f01d20401800c8a10300e98000e00e4240003c41c14420115802840400302158030720b28115000140d04060740c00d1000d2040c104240c40a002c10012500c0c84051100c9003030540540009603000075001451411342c420241c0308000d00c0d5010100e01c41e55020308407070395003400d004c0c40c82d8120301d009400300c500b0401d101c8402e0740381c2003044c1510200440b55203010040b42c01c150180b156060a0a4014000b0031003030740c04a507032801d00502c041d1400c1064002901140034640c0550091a00000000d01190300c5a440503519 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 886142473 1250 886141223 886141259
    0x1c18030326010b0d0207051c03050f09030a09060315030807080309060601031407031d06090a02090f070e01050f0f0703171806070e01030f05070c03080901021602100302090901 77
    0x202503181214075074040307480340d00341620103c3c0340c803900340822856104000d4003c000201d4503403043c0344100e0b400d4040f0911120030680d00b86d40209039850107051382081d000015000f60310f5580240031403900c10f500010903906a81c0d0510b0001146600d28a808602c10203950025002c0351703001504000f44060500110b2051400c5000c4032100d88400c3d00450480d09082010f4120008400200741d26038488e03000100c1c03a0038103040d80000c2c86d0000c84494200001542e01d0001c0ea4001c0d543d0380c046003002e40d0fa00b40e2010241c441c5c61503526000b400600b0440c8003d0300c89041020004201c2100a05001641e441d04022480261203603407a1a014107a5019140c422010031a50f01c00600c0b4a00354070380c01000060060050203403600d0b1130074140d81c0401c080d241241419161800010540440d208040c884c4441d5502e150407020b1505002e000c0030000b80010500d6401084460015100c45c0325100000b5419078200c8101103402008070001d000344061983e00104040000610b03c0486192a800d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 886143723 1250 886142473 886142507
    0xa15021207090f0605032e0f1211011b120807080637090e0607030e03040e190e010e0a05010b04180602090f1f0216081c180303 56
    0x10540701d07001d05549000441c400c0b03208a00c891003040c04080e10810185401180311200303140d2200250550036440544181c025103480b01c0403000304000e0058902c1c0e0303c018018840402d60312030050300d84982c044002c0e031246041c402d00759000003020117490102d0b1182d43d0045d42614454009e041d005148180c1618100d0009140c0004184e041c60020040340315904815400210324000036588078844a90000c04840c02c89600f50005035100c00b03011701c19000303824901500c014a0250000703011113a10480e1481d6035407080c40103014040d810300701643c0140301e00c0743d007104400410038408042c1ca041c82803074901d54240030074000f030568000384041800744208c0003448030400c0001030004580d5080d049200c500390480d901d00200c1d859500511901d540070f00060054041c000104000d2b8080c10342242151240b410301e50000d585c1881010901c112102d82420380381c1c9841c02482d59002d4a1100c001c00c1d644001c45098018081d140503110450042d0803030301d4a84d6070b424090001c001d440c000101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 886144973 1250 886143723 886143757
    0x20d03020c0103061401051e0c030c0304180b2209062c03250609060501030b0106090b070b0105011b0b01080304031b08061909020603280509030a03020a020a1502 71
    0x5988880c1d03a2800403250b4060b558075048c44002c502c0c0b4a5000c1d20b45000e66514441049010840403040c8018442d0840c1c0308021075a0328039280246100780c212096480c0a54600340c2c4c040303c01d44d150020041d1404d185003080a0007003416094200600141d44024034a6151000c121042200305021442d01d400b466800b204183c003000d001034480c400d681641000c040140142010442d20480004016006400004400015a40d1601142e6082e0000e0751818810070042215a40c0185124003511a6080d55414010940e4a00e21080411b0058505001c51a40d4080510860079025a0025003110703400045581d40c200d402c0e03c80c0d11500090b61024080b850315940801d41c04030200071a40180b00815299072264180300402c584900491030841d144d0141c1b030056036401002e10b01a4045500f14090020f05421824183c9035402c8c880980d0b6042c0000c2115041010040d100481c80743d040150381d070480003808a00703201c680c00d002481c0500c1003003010065021540686281e28180030740e04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 886146223 1250 886144973 886144979
    0x10513151e0507112d0c0d060605090903211302100302030a0b030106030b0c0f04081203060109140307051507020406080f060f1501050703090512100f0c0912030c020d03020c010306 79
    0xd80391502d95140c0003007543e0290080c1040180c19000f18035001400302034410006c0c1c0d180c0001c0d042c482440003502d0554640c42c0a01c4a8500303402680c2c0c1003103d450086203041c4200c1d40741c151150181c1c0e10b076140c01d0760b49000140150240c01c8104200c035801800d0700c0032081ea44030090000c1d001034588a9006207001000203035420148036100a0341d0700a12261070b03560700d0741d1442c0b1076070b4042100405614024400005c0d9405c042101030304041450741c0c0181c491030100e0005001054940c002c402c07095818008549644000c00c0080541d40d040d99003175005461400110024458020001d4101d4502180001d032418007155030211410710900784e031801e40302c0320205460700800351940d03440819903441c1380e80036601420003030401030301c281454070340541c0c0d0b5400594890340c44150051140c00c0146065000c400c04c1c030131280d25807030030b000070030202c0400312000b040b003611805440000000e6500c180203141c0200c50b20f054250340101201c404c00820703d0000c0d1a51191110680443d003025804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 886147473 1250 886146223 886146257
    0x3020601030c060e130506120607090305060a020a21060b130306062c15090c0a09080102190c0212010510031a16051e0301170f010513151e0507 63
    0x2c10130030540108080d0050720560844c4008242c0580983c1e80116007041c000a0074105005003841840310b81c9130b00c500c161075410100d040980013003140225a20422485282d5500450340300d080035441d810140701084410712020080480d9080314a4186021904989100b01c1c1e000e0321060702e111f00424801e1603aa1000180d81c000c16031484801c0e60001c044200b01c000344400c4140d48542c0c61040c1042108800000c42c401e03001c1070f90f1207100b90700c0004814010980101c0c44000401c40301d40210f1420f2031005282c2c0c00c1020490030b040c20010000c107003100355546c200c0000e04400e012802040030b070a110000810300500c074441101c9501010029080c80041501440d03c51200c041000c07044000089088920354420803840240c0007119804208020988d0003850180801a04a5200303c0f2070036445882c0004940210714141e0401c01084120b030744a001201d1600d0f403054402c41c1d040184945030004d07150003030b55141000a2084002c1c0d03103114541003940507010b181c0307441203280c1d01c1c0000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 886148723 1250 886147473 886147487
    0x7030822090c050403023a021c050c13020d020408030301030c080a110108090f07030302030c100912110f060c070c05040c230d1508060609040c030b0709050d03020601030c06 76
    0xc1d0301c0401d105210410240c10001c1701003000e0700c484450701c0d070b0010780454030b0b208002030410b107441c03d41c47c1003107100c08505142d40f030f40d5442c20800524001a9003030380d584541e0349042c1c1c0d01290090070051041c14480729150140c81c0b0100c00f0240c195107075500c54040360b50380e800034802610f041c1e800b1100001c81c0e4201194220040742c02c403000154070364a4130019511513401900d195058072881c80540d0030404140f00c5500518440d50103981d82c2c0f40a2851a4130f861000d00102900320b00d0040e806c0c0008403002040c0316140441e061030b408410070380602e681003040c0aa1181d2460048904202101034800c3c0148802c5104407065070506440e0304c00e02c400c03220f1014003d00450800c0510b4a0380c55201c62890b09211000c5a06924040c661040c90007669503014081d0908000c1c41c03410311003101c0038004107a00403801d0302da0708203070f01c1c00b601c6100b41d030b504512014104907942004039081e80e00c140b100c400600000740014101c050780b860001d540d001e091009a501c03111044021964910580f6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 886149973 1250 886148723 886148741
    0x6010b0f040b07080c0a03080601030f0e0a0609020105090d030207181404033204080f0f10050a061d07091e051201180f11060708070f050703082209 65
    0x400504003030410001d524290300507082601e104c2c00030721003c00031600c100100e48005129a44501ea01e00b040c034005400c0d5415a0004417400d03003400280810240001008540b65401a0020816010704c2c0016506445580b01d07050f00b245005803000d00f03041d0005085ca00700e034a01040840c0c0c007085018100c04075510510f011101941c02000710300424450f0200d09480207003000e84031280c00c08941400b001c9007411060f0343d2105030205040103038100a02422281310740d003e014103060040002d1454462648190003c0c40503981e102007202c49c80243c1c003504c060400c0c030784107070300d00c041a0307619424420301100c0350300c001010b540010030542c8500f14401e080e40c241700121181c96041c40200419250045501074896603903514200c030100c2207261102c980303805038181d65030318020741c03c0101c03200140b81e04a1b03000d61000c000d02c1002030003030802c4036011500000720400569883c90710a04181c41c80c0d00140c80d100c8080b4103981602e01e1711249800051624086110b459074481e036100503240300038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 886151079 1106 886149973 886149997
    0x1090e0a1e15050603010302090708040804050a0605090f0f01020613111c030f05030402090f040f061407020d08010317030c13060e090f0f07030e0a06091406010b 71
    0x2e900801402003520359519543c19500819071510703000d0401c500308000c00c000501400035050583d0b01030803009242004032551030710b004100d0740012441900c0340c0204402024035142c140300b492036100c81a0042e0200780d4407041181144043c0007415207407005a000140c00d107540380343c0341c5400c00c0303060300200010000a05008002803500d00f4104188101002440702603511070981c035904c00c1000342000035940e034030b282014243c0d003001c2d00141150309200000d0352264000c51010b20801072903003102c40d4045c0b0070b00101d404950a10010b0034540070140f98a00c041a040c004550080c40c40c001303145800740301c0302c61880c0c8031a941c5c44080007508883d109103580c68040005a081800d000c0d80c41d203036092015000482101c041c164005240c1e960302072800280c024080884000e41104080280c1455400c000c010310403074003420144c9014110000c40d0303031902c0c0340c180c8110014807 = true := by decide +kernel

theorem cover : BRFrame.Cov 885971223 886151079 := by
  have h0 := BRFrame.cov_init 885971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885971223 ≤ n) (h2 : n < 886151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
