-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3867
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:54:53.486263+00:00
-- url     : https://prove2.me/submissions/a82d4bd3-558a-45af-8cc4-a8ed15c91a53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 695323741 ≤ n < 695503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 695324991 1250 695323741 695323751
    0x306040f0506220617061f0605040b0a03061a070201030b0f010509210d051c0c0e21060a020d050a0213172404111206060415090e010c02191e06 63
    0x340c50700c1d00c01e20903801019803c0c2d01140030011f204031030040c1c40c0e1120400c00c403104030b018a00f103802001c0d84594041d074500c080b00460f80c0060746019401440c00750061150300d10220044410500640c0c20150050740024200710b0304c800b027400d0201189108902c180d64241c6000100070603c032022078400c042c01521038140b01c8118217600f0500c01144009515600c2c60351310880062500074001c940d14507050500d10b08003c008615030066034a074400c00003902c1004001c00e880314141c00c11400302c808000340d80a0f80301000589207a0707600500c1c1049882504000f607480c1e6002a004034014550902e885101024061010041000880d500d1200b100c084503400f0020560010981c0c805a203d00c04800c01b440600c420801101044ca09884e42030702c039488a556240350b0166180f0000d014640038940d9640c994021140d15141c1d040078005086091108031400d090040c005c124415003080140100203090080003400701503051110307000740d404913040c51246070400c1142c21201d1300301c0c1d12569603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 695326241 1250 695324991 695324999
    0x10203071704030c242a0809040c0c0b01030b090a0602160b010b0a02100c1b11011b050d0e06090409150507090b0d150308030a020306040f05062206 65
    0x10350001c03000c148011880e551900c0c55868102e1464000d5009810a0855404182038240405c04590617841c000d203041a419003008140c0b06800724040001c00400040343d0b00d2106008003540149681e01c01030780c0070080082c10300130440b401950080020290034007000100082222500c0458004189000341c4080060725aa14000c03a445080442c61400c3d0b00d000300818031103c00107180c01096410300e001c0c9814a082c000946500581d0300c50041c4030340ea24808054284580e0100d11005030307620720034503100e200e0f091040c25417110944150009650104490617014a1006e103508160700c9402041c402010440030345080104902481d0880720600030a0074a58940c0900f426090050b03000b40304da44080b202d080c0990380000d003050280220f0001c10082024200100e803c007003842c440000e4034105070b00030b001c0e40e0380c030f160310182c580070000c02071182082d41a801140580750464080006030400281d140c00e58404854540d4054a1903100308000c00707a500300a040720310810300c001807003516 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 695327491 1250 695326241 695326253
    0x90c0509060c0a0605060d08090904031806050903010c020d0c060b0d02100e1e0a061404080d0f030614010c0f02130f02090a140906010c03020118030e1c2001020307 72
    0x8544803002d0305601420b00c240c140701c0c480c4201a00010140d0780398a40d03000e1601c540c41d03207105040c3c0d201d006440c03080018003407502c24503611700c10f248202c20608030305070340313040c001c01d250081c03a20745101e540f90072804140e103400020052150552030700c45c81005e801e40e0f142c1c0750090941d01460b6412208004d03044005035244036240c00203c20744e03107414018030000c40900c40340901550b007031103110000c0402c409084c0d85440402c42150040e01c0c180c042469444900c0b0704502403940900c0041c4650741301c030050700b0303002442a4552400c0c0d507410042e1996a4488440d0207600706100e60225074010034100c04611000f030441075280c0040c1c00880381c0710400e0052030480d280e05031090311155000c10018010319007038081900030459a04800d2802403100c001440d00b0702d0140200d4103000b0708840c43c5007094001e4004500c55410752603408907909039070402070401202600c44903c64a0f4101c1140c0b00450b0f0380003004080c1c0d4100c0d035041c80801189400c460140070003480c0906612091010300b001401d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 695328741 1250 695327491 695327497
    0x1e020a1514041502010f050105060f0a030f020406020c03150411060d020c1006050a090b131d0111030a29120c0904110a210f0321050405060a0b0a090c050906 69
    0x541035408031043c000c4000000d00710b404503043c445c012810301004003d543d403840c0948494006c010602595040900402d500802c20002c00d81000c0780042000070300c0d13940216180e10344a500b64146c480c0d00031440342055043c80700319030050068012100e20071060402030003074108500003201c01403503c07007600011490a9001c0c0170047c0f506441d40300521007030412141e09030003420102c4091224814403000500c03040001d41d074150130107940b2444910381840f602c007040c418600e624020400ca582981c4c1800725a03008880b1408000e0808000d8100c10001001002c2208220300318030b480c80d0302c01d00401107952100040d00505106011021a540d92050b40d2180664403440d038803545101c1000074440a0740c09c0d40c1c0000c00402002c1d10190040f0384101a00310200c3e07003c004508484842d260039980e264031300d4011010f0884280307489850003480c2d0b2081c8d008600440803207001e0b07030f01e40341650b0580c5c20440119070400e848203400c02c020440307074000e507058943e03c0c1030036410071041e1400304207960 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 695329991 1250 695328741 695328749
    0x31d011b0606080f190206091906120b0901080c1002030c01141603020906030a1806050106081008071203030e0f0d1d030105011d09070e131e020a151404 67
    0x141d50b107900308103101c02045419079a85100740a032941d00c1400c4a0100d0843c20341c00e01900540000034860318507940e940f0080d8601404c2d80c0202040740e141c9a0042005011010079081d26140c209064424a040c403201d5040317440c120024020000d448092202c0101d0503110003003948070501030400152070a00500f080d00c051858000014501440082211103901d810001414410000303a140d64483c40211b075800a19100040f84407486a440c1c1207410070101c030040d008500d00400494042c0d4001d140c01e01803400340316400000f0f07854160b641e40325440d0744180c50751a5400d8140d013001a009400008030b64155209581840b802c0c4a10181084c0d000c807074a400040b00c15544801807040c034480000903003000d900130001981400c0c41109200b0b074400740170420b040e0080008440b001c042000034003400c400c80c0307a1611400c00d03034001c8200c1c5000710000c41d010080e56103039820035020b111711441007940042079001c825140c010060100300c204920881004623030400c405107004101c0040c0020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 695331241 1250 695329991 695330003
    0xc09060506040b0901032a17010e061203070204021317060907050103150302040510050307170a0f110a030b1806090a0201030e120a05030f09030c0d0e060405040f020405010e010c031d011b 82
    0x2c1f01041d000b000e66809121350744180402c1c03801444140020740185a02034801c1d40c403100000c00440c0c2c094658011000025485400091120f00700c404910641d401c440c6d408003212040c07252800090b840303400403100b01080798001a01044070f50310a410201403d4140c030001041a40c0740c0c1c0205007038035421103003030501700380800702080b140c20f081000344000c1a5002c0d04c80d111303080da07000842c0c03240c008643c06480c4034035869008080c400c24201180c05801c0050010401c1c0750303070b890400020072003120b02c200101c03a0f80d044030102c0e120100380c03103205030400300c00b4090551040d80190000e20041c0046252442071186408030190182c2c000d10310540306440c0e5540702c1c43e014142000c6c16030010301001d1140c2040c801040070020002d4030411190309400c188540c8000305002c42c41034081d56101661160501c8171403051000141c0c001d0061301c07002e0740d416582c40241d50040d12400300b10080100081c0c807a803010210341b8440741c2c007184042c6052400030780b403900703280d814031038960840401d03151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 695332491 1250 695331241 695331311
    0x60307050d020423010504150e010311030a0e0111070218041a01080a1b060c0210181707080307020108130c090e030a031a060a080903040b040e040c09060506040b090103 74
    0x41032010a04c0d04080e140c0911700945801c0c100003410380e205105150650900c018001c680c1c01301d81c007d41050340c18800e19111a9202c0c9031034940c08015203441000c3d400194640140503424007100004c0310b2510303030003404003000007006030420310078544028800d49441c420080e1109402e44090f910700d0003230507800b0040007102d03180c2c1805960407194248960b503c0c1844001009855041103804803c0350b0102c80031100c0e613450041c103503003400102408145101134240040345803441ca080e030503440c003030900460700c24a440790a90342c2c0c2c0344102d10002c0d010405c0003000480800e04581f000280d40c0c4a0340c00250300580c1c4036064808d071540b001c148504c6800215400481c1581841407011001000c202818001c0320070300481e1052003100d1040003003018050020b20000340400890300203000914500703550b9540c442500c5a0003038103650841b0178008440b4001042d5041c0d0250720241d5100806492500d1300e00001926150b0142e1040d505042e100c2d5030a505d501c1811005031a8001965160700e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 695333741 1250 695332491 695332529
    0x150603010b040306050c03100b0313120903061a0d0f0f060f0207060506150313020a0806010801021e1903050402040b120303070207120b0609060a08010504110a05010e0f060307050d0204 81
    0x100782c45c002440d84031030746030510410020744440e50024046403038129a09a49031951015000944a11071000d000c041c07480041c81840340e40420494101c83c090324080205558407203525400c0c19141c4102a40541d4079403d0602140d211810b01e0080c0f4450401203001000c940da40501b03440c81c0328032a0a010b039001c100c9005202071401401d0f030240040f1401000c0140380d4540c81010300026024045000044c4599021034071503101c80f03006800301030b040b21180e6a403403404034043e41c4240280055042c01d890008000d10400041d101d000c4800791f090340c0901c011041c100d00070840201f080c1c3e032064640600307514135120a40b4140300c0241e541c002d10f81e645400035020f442c0c02c1c0365a00403008298805044030100d041e032911560801d4007160180000d4981c0300010791290300540180810307500c1c00d0203100400030030b01011161a50103039035800d8515a104015100d5800c42460720b81c004202400d20790051902400650b03004030642030041c14011003014840482c0c02c01c0c4c02004a507000e130b00b8442 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 695334991 1250 695333741 695333753
    0x30309050102010903230708030c19090e040f060f0207060902010305060d08030402040e21040305060c120a0b041d01060306061403030f1809130209061203040b03150603010b0403 78
    0x24020380800e000038043c64034107550081c03144111103c2c203803a0703400100410a0703500e031090803681c0054210440340d4030f80c1408015650b4030307404910b00d56100400048661181405481000215081c0440c1840955159162a240030100c1c5104407549641d69441207980c8030980b0141000074000c0b07500040320f030b821b40300142c100c403400b9141610039030b80c0c0c980b400001030180c0304580d4450b80c140c5000c98140b01502c6614030348032980c0c11503e03c1d44406071074418521410f002038021a0f005400326034071501c03080e1030300c80d580c41117080b422240b02000c000a02c24402d6501700ca110900050000510403035125800849001401d04201040e5142e203420020b0207480d006690240030300150440d00040810002070b52440740100c241e150356804128040d480c0800d0000c0b00500314060325001e49854000781821090b40300d5801203100c1c94109000c2000c50400b4051508030614840081d454241032403030311005600000c113025030110704c0340c1c045c2000d81c6403e0040c500030624050f01c6500c03503003149840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 695336241 1250 695334991 695335007
    0x60f3303061d0601110c101d03010c08090c040225111f0329310c020607030c091a07020409060e10110d05190c08160e180606041e0303 59
    0x3580f05a1016001701521303526640587c44421060030254007202c40d081c030800300218041010703a419441c120140d0b0180d500071925a10403003403a8151403d1015002c1000102e004000554001500c400c0e9800f070301c44255580204005d0141026242c0d0281050004201c40ca11960340c0781d0b0b184d004421710712110f8250155500f0500c01c1640d400d002d081741c220189403400c265031210700c00c100020783c1060002c2926107003075980c2e80c640600e82201d82c0d19061034010f440c1c0f501444005204900004070994843c3c85034043e030b0400d580d2242a5146015042401008030700b15800000ca010403218006039240d105074000588140d0010035032518003800740d400c0903041c00e4101c0b1020705100f03002000c2502401198422807130488005907070f440700e04144035100b4020042e584400d00e0660501c5015802c0b5113203610400307000f9070320b1030a04074103501100c054469001640d00010920041d0200c1504d440d4255802000540024281981c0f401c002e9401c06407200c0f54030b04048404014014594080c001c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 695337491 1250 695336241 695336267
    0xd0203071401030c08130204050424140609100b090105091305070e1c06270308010905130b04020904020324070f2609010b13060f3303061d0601 63
    0x2821700c0703250103501ca0b040e1302c480c0e2038001e104580c2d84c00003d080004230080c0071174020000c10884007200d04020030340010b007001e5043c4451714444500160785843c0c0100c07102d104008070103c2200542c41c001c1260000d8004104842c1404801d1100104584441c1e43c50341c424080d41c1d4000c03c450904840c082c2c442142c400f09240980350040c0c0391480d800d8007080030000e450744010001204044074421111000d90910b440004d20301a02c56602499808143e541c1a9807000208100da40c60b5200c100b140d41e400d482c4010050f00340c200005e009443c0040301c455201c0d00107000e1f00c86c4036004c101c807403c800312014890b412410014060020950707114103e9421001181480703000c000ca840c3d07001c02d42100500b840e401620182001403041e1100390070200740b156002c1d03c0700b40c0804003101c0a074060203190180c1610b0380c024810004100f000303070b0381244400741d030902c004a0402250310112103400e5a028924103164544800250030420159004050786810b0446145130600e00c0004000c11840ba06c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 695338741 1250 695337491 695337497
    0x4091e0c08090a031b0c03061b020c03072108040b0a02070801020304080313030c0212010614040b152115030d0314010b0c0a14010603210504060e0d0203071401030c 72
    0x800c2001d0307040c001940f0001aa0075050541c00c8140058604c0d02d140b505150062002c04502d40000c10820b950f0004204280d00701c024125100e0f01d03a50481e41c99030350786110795042e40600c07000c00101031340404a00007130142050040d03d1a0303542c0c881c08150b505c40d03800b1420101c0c00007100c3c03030116410321101c0081c000440c000e41c598102626494070b81d00028100c401002d0b512240c0740101170068552290f05a4094200038108604284050080a0510646481500746400f002d098a001d100e0008148002040e02500160442d03c00a00d80c02c02842e0007184050342903401200400b06805910039004005699804003180060504001c40e50101200385030505c1e0700702c030030030380c512a8030341c103403105201c90036203622614a045203825109100130b807407100007440342c10b09200c2c1900901e0540c0d0007003404051802120060207000f403001100540010000d1209001aa00c16800800c07030440003132680c00002c0164000070309000346030384241220710004c40e85001d41d58040c0203141c29205541 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 695339991 1250 695338741 695338757
    0xc090a020f090f03210a1704201201020c0304050a060e0f0103050603031b01050106080106110d18030b0f0604060f05010c080304060216050309150307050d1104091e0c 73
    0x600703120814092050210700c42c2d421a650070039070351030820241850741c040c684041041c070324031080e804e51a88080450b00c000341c3c50541044205040c200b00a00030b40e8046020810042e4038540c4004400500c01d505512050211001041d03a509001400b150006c040295559038a0001003000400c5140d1000c2c00f84107840c0ca00300c1d00740d0340360702c0300c10120b640a00300880c15540d488000b034214807411801d8000d401600c0380c1d044040005612072416074002d6180e00030380e6600e8a06c261101081a84144190782c40705c11054001841260441040c942a04210030000d85a9443c6800c011084462206042141040040324581402828000c01c4188a14403501d0309050000b00034110b4468040c05000b030002c00f00d8200441070f8100c8825a4114048600e081081e240041c1c89500030695035218105035108206150010003c60b4016010f03501e60303a00d810b1100504501502030380300b0005c5240000e0000140710b2101d13010b000007040e41c0c8010170342c0104402001e90100c40203075801e50204a044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 695341241 1250 695339991 695340007
    0x181f02011a28090609021c1b0f1704081e04080d03051801050f0411030d09050d05120a0207181a01110f070303050c010507080f24040606020c090a02 65
    0x10003000a114000c0654010340305400b201403041802039205140d082c1c901140050100300641c05046100310001040e01d1848103a150031050f10541144141000849242001c915004a002c900c030403400e41050072180e120140c141e201c481e421a0241c5400703030005054903035551a0818a103107296203040f410b05007800c1410484c3d40308480d40c08601415075800118008900c40101c200ca103580c0100240414540364110546151080c4c4040b02c10b0851502600c3c7e503071a0104406035001110780c4c03940d10712880c080802c680500600803c1c1d80074001e070003d0100300041a001003482d12881d4000f4400d80d882e02c070789031004042c07100d055101c551601d032900b0342204d1520180c2c00041401d10f481020319080e0382d0650704160f041c01c01c007811031285074000010990420040d00c10516414000c0000f0b03030f58150155103141003182c9582c140c80100c4001000360000d1030500d0350811182d005014009407000111701240c00d15048903015078001c13003000186207814140d8076403201103012709500348810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 695342491 1250 695341241 695341249
    0x1006050339071a040309090f09080a020a0c0608040819030209040f0501140307030b181002121504090b010e0c070f0c030501050702190204020a0c02131d0d14181f02011a 74
    0x19401f40c030b0200e64403500320010095103900400325150300005400da40b1341075150040c2d510041e07540304981000e002400018424000c0012921039070b0429405440e001040c100c84014441100440d02455401c1c03002860f0f6440da485003c2c100c000716200001c0650409407591034140c4e041f20b40d10312907480a18240005255003408681022222030112071010340344034110708004502c1010550544041148002a82c0c01070446009031030030080f11035005510b60500c401c0e03500c0c18101510712140c11004000c8954a0500c082c0d001070f03403480319401c1042a50703c50190020340e51094940c44415202402401790030f200c0e082c5c002c8001d000900c0780c201802d290141c8a840500c01a10550b804100e41812502603101a40490380c020100944866190314910061210b001c0c16003030840c0140d41c100740f46900080ca81d00e000f401c0d0b1640840242805501c1140746d0086012105004600c20010604d86800420143c20850410103024040120703030000e01311070340c2c568900f1415111400e80180b50322 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 695343741 1250 695342491 695342507
    0x6150105072d1209061b02130e0109060b030607030606090e040204090b330a0b03040203070803040308030f0f0103020609011d0310090303051006050339071a0403 71
    0x50721900700c14500d042e0500102141c0c0201144a802039a6006100100041c0082c032085032012921070100907521881c0481c0d142d1440103000145080c052080b82c00361070a645420b108410b40a40400d614141d040b04900f07482c0029811622262501f20551052505001c00c0d0ba0142052404100c0d4074a4100002e0480c0101d21031a1110356000000c9001d41d260f0381c00031000180c2210b0220004c1c00d0007452080700500d4a0140b8a12005016031040c440d80401c01c5681d039204000e0206001d5818849425000e82c0084c100700d9051107203a00c0083d860a05201420045001d02e00a544034074200703280c9041d01d0001800c440c0b003104401c00500040e0783d40c10030380366165403e190454002e04646030380f400d0354910b02d91481d414420042003a610001d6a003045129a120742c1c0e003400692a43c42c442013480b50309005000200e8030500005403144280d14091640202950034048000704040030307081c2d04000c400001041c2140001c4500c01d01829001d030300e4000800c0c140301ea038107242984008000f44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 695344991 1250 695343741 695343743
    0x16050102120f12070c051c12090302060a0213090516080a020c0a080304060b0d0c0f0b250318060509040e03090112020c0a05120c06090a050c3705030615010507 70
    0x291400b400719130100c0c401c154001c5020703806000c80d0031841110010155103060181100b00003500d41000e041c0c0b6414078001c21801c00d40c07640042c0203d413030b00c0c04248080e4001449045030100c00c0e1000090316081d07030103914061514400e0381c41c1c0090313918000501500300140301c500070320f00402010030a60000528603290f960004c03926a00c89c4c03103900c1c001c0054500340c0c4034958080701d1800c82e6418046007004050480d0415a040110035950781c180c0d81281c020038a034170100d5900d01a040c03103190481200c006175540b291810300512464201c2e040003070605034202d980000c0002c01c4030354150806114074120003c07580011802c0c43e80e140c000900102041c444010026000700c1c928034804410060055415070010503100c0607140107519000c03d0f0400200700c02540700c0e0744081010391001103828030080c0d030408040c2c1600b00796101800004071f044200c0c28030302c21425031104503040c400330714400ca00f0200351602c02410720f003d003090315200d00036101d1071a222111561103401c0c0e0b04001216543c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 695346241 1250 695344991 695345017
    0x30406090f02032a12150c1308030a021002070b040312020f0d021c09030212280f030b030102031003020d0602090301090302030a03060803030c040e090a0516050102120f 74
    0x1640c0d8a421004503030750342802501885210490900c2c4840d003900e0071a0300380d58998034000c02c559481003000380540c1400314603041d00045a000a01c0c0c2901d105642c0c0043e40d440d19900c2c110750340880c0c584545807603211008039000403d40b040ea1503414011444a540c3d9900e080d0304082d0a515429541c0401400c002e05104802c0c1d41e01c202d034412a019605280b40c10002035841d607004402c0d800103035000307800c084140740320310008031107494240c0303d0710081d144c050f80242507541000d0100013490f03100d1b04c8414400740c03511468808508800c441031100c1201030b40c4801c03020360340076806010b403500f0048891190740103104118204108424050491f601103614080c800300c0d0f414188000c3c4620b40301580c26500f000c5010b8181600000142451210740d07404000b00d50f610350307100d604c0c1d020a480e250140318017000308110a0f41140d1509820a40072000d89448150036610240f9090f42c0108150101c00c4910042000391b8040c454481d0343d42f18511291316040b2000301d400c0861081403002d081c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 695347491 1250 695346241 695346251
    0x303040305030f130b090a0212070e0105090a14070e0909070e060f010c05190b0a05010b070201080411031f060609030c06031e060e0f01090c080f1305100209090903040308030406 78
    0x5003104c002c10b2409034030b030070031507080c21707070038203000c02a2640040c01040e400f4902001485003045000140602102c1940c02041d04690900041140844018080303501a540324500e04003c03500320001c450080c0707810b0700c60914100e140814000c1c00c203002414000c03e500a80401c00c082154801103950042c03088614010b02505080103a030013600420001e0120712510100d44280c850190300301040314001e41005032140e8a442c7c000c001c2e180240145030380850107011480c01540617101250704544a40d0802941c0d40110000c41e20b00100d007010042e2203a8082d6540d21041154400d1602521081c80e01c01070842c10750722002d03030400040c4130300c030201a03803110680ca104030402c1074694400019181400a250307116085060100c0607a04007072440628030002034503518911442018450b50386890140d170707803003807071601c11f1450040040e400c0310b45070147d00c00000c0041c402d00c0c00700c0c681c5110040c3ca5103408000c0c0204064028503008c2d40754410001032000c40c3d030380c0c01941c1e4010390103030b03001c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 695348741 1250 695347491 695347501
    0xb1206061504170709061a1611060d0b0901140f1207050907030204050112091e03050d0908041e0305101109040c08090111180609040e1504140303040305030f 69
    0x10403803045622400d0b181501020020a00c0b501003558405c59040003c1408490b80b03c45007440302e01d00e041f0100940c40c034100103402007241e104141c0790840740078500c1d00781036954002c04500c40380e0060036890112990784061200b545894940316001d850500303d000840c840d14000714658100400d02c2520610101c8144c0c00351110421091002e010081d182c03003468101a4006130194009018103800f0808000c611410b000182c414100d0f5950007045d80507071822043c0001c00180201c80302a02081010443d140040c4c00c6400b801054500c01c0c643c0c155102d1401604d601c0c0359100c50751044024081c200100040f4400141760992200100350008582105284601c5244215280560000d00307044407106400e40103517800d0300c5201000000d002080d80598801030300d1042c5400c0c05105400003080341c0c2581407070006814507410242000502d00341d10000039242840743c01d01800d9640c0640e007000100310310f40300c1404003c0c3d8800c00a60440c00e0554001d03110307000051010310f640a0b644000b071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 695349991 1250 695348741 695348779
    0x1006021b0415120b0702150408071416090b0a0311121603030f02010c030b0303180411161e0c03020f060d1b0e0f030304051917010f0b120606 62
    0x5079007256010144115603103050418034440c20f50016111400960001001d45001068807948084d1121b00001c540da41d03690394240503044188180ca85200007860300b00341000421040240380380c032803102540340780340c14119019240d080751202c1c015403040000704005200c03c422105c80b48822154802031031001c0690f1803400d40200b07071005442c00c50040000a03d41c000340c0c503c08410182c0d0003400038202c101001d50540780c4e81604c0c1a015031040111614890b080d61240d03181d454000d0001c951031a5000070059160481d8030155102d104001032a004c04c80c1010f000d00088502c2140c04031071040d40c7c0c0744d141342440c0c03510002c0e0180d074054940c10080d07600c500440b01010880101040305000f0710320016076141000440d035001c60b0b0b00034006500c40ca414603081000b81300003401145400d08140c2402039141c00242001c200c08004400410142c0d01c404009a0b00b486090001035030000e0381c2c400000b035079404000d09000c0c000141d0302004104010803019401441542d010740d500401030298 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 695351241 1250 695349991 695350001
    0x5090a020f0d060306020306010306060f140a020304080f0d180b03040813330e0604031202030f190e09041203240e1b19030c03060f060210051006021b04 67
    0x41c0c052545441401300400100da400342d80504800c2c0e80810a05444010a8400e01d030303083d8208010400c142142c6001d50079800080c044200a44140c0b4102990365040504d08002081c250307072503410034011402015032045c180340e511041050715092051920030203c86d640300143c0080c02541000402008001041e640348006080e1541c2010300c241d081d00f408c2180c1d003030900902070340b090240d20341d00c69103203d0311040001d00350090805203800c2ca180d44903040001e60703840c10000d60006000721040c030000c0101030009030980361914880300d006508010111041c0c0182e01c3e2017041d80304c090201085c54041256404200360a00040003003d44600b4034400340e0280b00300c110b2516031400440e08010000f005401141d00c05000881000680261040b5008000c25445040715511900d04842e1017a000004240d5890500150503615030116503100c20840e040040540d02c842c441000ca20705030b106060307220385000784d140e4050741400002500d0b66041010300401c0345100c504004156103503402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 695352491 1250 695351241 695351257
    0xa020909131e030e0a050102030408100b150f2101120b0402190f060206010e04020102030724050406021b0d0509040b040e0a0b160206060a15120e010b04110405090a020f 74
    0x941c01d1210460f1038010310f040300141c0c045016000f052000035855000000382d8058940880c00b400c004544802a60001c1803032100c0d65622207a9002066001c0c94407000400740741c24000030580d40c81c01c0d0781d06040c80404000d56013100c1640300c0e0004111100404114064155000c4d088200c02e444e0340c000140c1042e01400c505901207a10750001a908640c0e8a100044420f0368003903c06070303030f80c0c7c02840790204011200030380560810860500011500c1c0702c10140c091520341844160340f91848d40307000b1900121030850300903500080f00764400000e0440e00954074007002c000e220101d01c1c06030003006d6009031011a8020741e25440f03082610303901c0d500f1810210050000300c0d5024040c900740116641e4041c0ca56040031300240d0801e136a06e034400300d4454800c403c0031b019290720707901e081801e94100500f200408204503a08480c0000f0310491701170300b000c001000c0004100703100301d81c1c20401181c84010544a00002c100010445904c6010741141c0c030040c0000e006071110905000c00040e44100e0007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 695353741 1250 695352491 695352533
    0x2250812360a060302070f02061c0e1b030606031c1b12170408030601050d110c210c15090712050d09150c12090807060c06050a02090913 60
    0x18040794101d8000d0040991003412609088956074629040d022445800d0b4082c08000000c4001030141c280f040050040480d014000540d415034540b1410490307001040c601e010f500312003070040c043c0c118442d84c4103c10304101c01038000c504281001a64846481c03407000f01403400d4446020100740950f00c00c00c28407507421803102c0f01c00f20501e0078103410094000ca01001c140d0079041208401500316010748210760010b55185151910001550160440780007029144c0e00e4038142030685100c0c0340607200c040c84c1700005004841d01c0e4075110f0b041c408910100100030340c0c1409240340c10440008c601c000c1c01001407001c0d05648803104054101600343c0c101011408120301c20008001002941100441031540c0784526540c40b444602c1560320310011a000144403d5030722000f244a2440340b007019941420724175005030742d6003a580d0505c0155808040401c3c540c0c0f80e48403d101c00e6000312a804043c10138214603000c0d51a00141111002824000142805101e81c8080041c04891034507010401d071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 695354991 1250 695353741 695353807
    0xf04081002180a0e2a0f031e060105070b13080403150606020d09060804050f0a0302070603110f070303020d140a020a0315260a231005060105030a02071106040602250812 74
    0x14804480c40e481900d11000c1c210354076090407a420311000235a401a1070517511180b90207020303141d01d104d100002c2c14120050446010031703400105440020b0004501c2030040c981d41400802c04d0008862003503201d4400e641101d00510100ca50203202c00301640d40301d0904025a8461b81071940c90400c007004051201d05c90f44081c0000c1c150002140e1040303488594080c0b1070071002c01504a0540105000019829810b0220900090107a00540600110210005418621007101c465121b500741c13880e28203280d0004c2c0c80c00c0c0307041c1e01d805803200c0d40d0a40c2044008185c50900030866010b016540d0303528446800d6003c1c2401034040c4007103c1200c0c2c02aa8146a046550070001c2a004800074595040c0c4200d0310701212068141c0101071040d04141c4440342107941b2485490080d50000004462440c26a14440d4072a41e0300e40203030000e06502d074010941183c0120141b280049521594203160032a600308022000c8006a94403200c0c0642c400c15407134410080710600c60b802c95481c280c078143c18007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 695356241 1250 695354991 695355007
    0x501050708040512040312080612011d16030b04080c1002030709060906170c0d1538070f111c06050703020a020709020f04081002180a0e2a 61
    0x211603014000ca000f00c0955603203030b07034030640c11a50303110307a110081200400342100824680207601c00c1c0c1d8400c50107450700b031040091030049801c480c0c0a44100038213002d00904142046c5040182d0001c0700c980450500c00503046403501704504c0d00c014802040000300141070428004240070b0340a81e0700c1015029510390030300700c40c0074160f80c1c40c40c0514400141558400940503108401001d81c4640786c0d900b107030b41519500003a216650041d1000301080392034080107400030009080035402044481c00b0080380c0080003c3c1c480050fa030380d400041010355454001030341800750f50115080300d0fa01002640380d428892401d400d00210465200c1d0703005245a41d64903a9a00701a003e01034a4803c2c4c0003001640e450680a8081780a10005c0300c0050b4400d04042c00444202d84c020013904200d001558180360f5190105454405030b202000307556034000c10b2400395081036101d22102044c0859001e50301906040f196000c240d80100740f124851509020311744100006900d9040044158100a50f2001c01c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 695357491 1250 695356241 695356247
    0x50403081318050603010506060306060d051f0b03240303040605070312050403030e010b0108070e06031819030306060f21062102030f010603051903030f062715090c02070305010507 79
    0x46130440c0c003a50800f070018103146804000c41e803190074020866030810f46241d0f07030013004000c002c01c8890707092100e2082000c00c42d40030350780e44014050700440b15524504180c000c0080705d51103010503a40700340c010700400c09580110a4038107451542c50002d07100c015504046510060100d42c44503103e103800244010300d54141c029150201d0107800a10005844c10b004454200040340c1800010310701d6080d00100707160900c0152b0f002540401e1000398640b1a100c03c0b0b00741021605603940300c1240c011010200b54143c0500001005c0711308000c1000240414040c002c030380c0c030100e0ec00d448403260a841c000402903500c00030190103140d080070803015a10311189503640c00d840f02a4841d03c60711944051040050044000340e80d400f0014180300d0703940200b009050307840003000f1001d05484084004281d0854070804000b8881c196054444003900810074008000d820404500c01d8240b009d000d0f5a1000605c500f01180d4800c18001180680b50308200e0034881c040d04020815402c0030305100d540d0740c3c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 695358741 1250 695357491 695357501
    0x602070204180203100c0e060a08010f2c090313060201060f0b070c0306020306030a170316031a22111e270406030f0507030b090d050403081318 63
    0x11081ea810403080351045044a4508107108000798164042c0f503007101016403076007000034034129900b00303008103030300750750000d9a1600000785000026084034010080030186034182c1000b0854504060100352418410703100400e50182000005440c0c0404242d101d4000c204480070000d0f0008082480b80d1110402400303030000d4410460b41460440b000301712903104204441100c0c2e40501c0030380c0c142d03286580700b402a4000600c01c41d454014008042c01003104200b5810f80d03106000402540c03454440072114040c10320101840c200352624141d40e2415064442d010b00b81242102c1d0050150441e0100083c10541800741d0070070981412070003005942030704050034603040490300380103140c2140e08451205004089000350b25902c2d0031105402c0e01c00c039000c428040d0001600c04159251030303072101c04551800010440e502d9010080800603c09541101e5800400d030b40f029117804070b26000014a640624003001c1e00498001404500c047c5081104400404103180700101524403020258018a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695359991 1250 695358741 695358743
    0x409060c030e0102090a0519050307080706140a0c02010e060c0f072d180b0a140307060906050a03051008060412020d080c0d1e021b0705060301080d120f0207060207 72
    0x1a06090000c0c2c00301d02d06000f0b996007040058041885140382c8020007254600c03101c10400c01500000c0049140e840a02080c0090714401c00107042140c41c0c508024038840c00c0401194580c04240001e5440d5071344070644c848a580c09282c10494441000c0002d102d500c15030074140854891000c51180c0c1e05400310314002160300c1d0100c0407a00380940764507414041540480c01d043e90900110600c5224500381168034104001d0f84000f401142a42c0403520402d42c50300841001c03407800b0001d4100385002c10145000c1c2405160903201140303014005400e81c05034a030072600785038640c00042c84900c04401008001e000b80021111542801d041c6040880402d500c00c00050003002030782c8090714003800f20a80a44404c0508500e48020b40c1101401800740e0340e1090040388040388a02d500c800b80c3c0c00a842c044000c0900c00c81c07820b9049041d9490704c1c200d82c2c0442e02843d03050004004c0424003044083c444040c03801c00711000468031103500018201c802d00070f00180c2c8040f405a052003600d5001d08502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695361241 1250 695359991 695359997
    0xa1416031107030b07050d0605030703030306051f050306010e0414040c06080703050c0901111c180503010e0307020609010c171305190b16020d0b07030c0f020316020f0409060c 77
    0x40744022000720b03220802808090414407454010a118910400c0107103081c80001d0740004481c0d8071034002034101660780d8015000641c90b40c105200d81d280c081500280351101e4040318140c0144054003400034000100981e05100c0484a0b640e0036880d943c00c241c1c00600c82c0c0514600d036291902e083c2d00450124020400090403100c00600c1d024001d104d014003581e4a103030030074246100d0f10011030f8580d410040c00c030014045c070703040c4080350448801006917400003501c0d480300120962546854072465a44000d05c01c1c0c0c10440b00300907c1c0e6003c021101682c0e01034070207998401c101c00058030034002140c0010b250000040d9500b241000c40c40151140c00d1106100058260fa1803081005d071846402d4180700c1c103641c1910411588002c4070060604a20400c646070241029800145588101d40d40603503840e8010420410b04652501c14040080c4040c00d10100105401c24004c2d5030303018594070300280d4100500848250741d5202c041c4009070500030070030f000c0d1004034640030001c0c004010100c404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695362491 1250 695361241 695361257
    0x151806010e0114191203090e1302011103070209010506090402071e020a12030503130302070b0403110307120308010311131d010515030d03050c2104050c0d020a030201050a141603 78
    0xd40d1070300e42005a5141e25414030008142d04110341d81d02c1200404101b00c090004418001a8140381000310a20800219041103045040d03400050702c403000b01018040c071038000308003410043e03940d00348403815144280c52507511a4001d101060080c0b0030220b000c0d01c12440741d4507801103264486007005215100341c4040d242e240c1e441e03a030007094007200900100800d405100041c3c01d102c103a07244007010b41c068130454442c24ac3d01d09041241d076000360010365502d2400401848507090800107440203109880040e1480781c0e007514000d00031081804014104103119200b03041c60b0355280d043d1000000340c2d00040210358044461036101a0304181c9040c265400c00c00094442e2054903480c3d6402d18014015040100030504100c0c028000181700107604101804500b4121a0810884001c410b4440c040f200d14201030800501c0c1c005203007005881607105c205c0d4107006803140e029840440741e080c01c1c045e44805030f0850503266414881a0920070b41c50204401200080e003c556000403030003926200c01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695363741 1250 695362491 695362529
    0x90a27020a0f05090d1b1a0306030721060f0204080c030a02100c0f14060405190f03112a01090501050c060f0c040f06120e0a05151806010e01 62
    0x1a800341d840c140011800100000642501400003000b018000800d10586280300307944044c0103401c92032040c03528111800f01481101140300d25000c8a4904174451030540c64684000fa03070f01d03001401048810340712076110461070403180c2c0c2442c10140d8070010510182d661110000001e42152040074064460031011420905002c60750344056900641901d00b507003031201c070603039114208040c11146407080c1c01c1a600410b0491106000c40603070301c40504000c3c100b90a0070307481c11460000c41c0604103e102d10007000a50b4044c200d0901c20b80c1420500710b07182c2444580350070b000b2071075041c0e44050000c543e07040e0341112800c084580c0000c242c07106001c060b01d94004661034040d20504401d540c0c0304001080000d03101240f0aa80403500000c1c0d98035168407010143c3e81c0f42d00b107602c400c021038544180303421a5a124060704004500c40c0c2c00610707451031a078407040d946c1c00100025161402d24500440c41030f4074000205401c91000348101c0d44c003543e4a0312090b100140034441c030901ea40154005e04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695364991 1250 695363741 695363819
    0xe01080c1003150501031d0109050c0108060907021504170a0c0506011d010515070f4e0201060b04120c060305090303151c0303090302070b0406050f0708090a 69
    0x452210110f801c400c40e090030400158000c1615150900048580341940b04401a0034000e21280c14400d00103000c403103100c080050301808000d050300c0e106024520070466496070000c0c005501350421603074403d55480744c0c10146010118805414800500055040350194110600707140c01441340b81103d003180eaa07026500400884544158048080000100000d151501c0c80c03c0c4482c1c0101c1c21145800859500c1240c0e030401c40c40c0c11035208404072a02101020350b0200040801c0c4c5c880c180080000c1c0300103003200c144002146c0890303030042e00c464140c0582c1c400d501520103407107568000c1c0d0f5606d4503008481c100c1048440304a03440c248039100412114840c0c05a41d0203018904010b40c1151100382c00112119150604a034210242d10120000e200c0482c0c1803c240314020b450000d5501e00605000342400b03415007011001e65010081089255032100031109000d034820f010301d807a5404c17450a11064030801c442da0b6030203000f5450100310f182c1020384d00080207070013200c4013a2540e0341c00125 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695366241 1250 695364991 695365001
    0x1401080f070b0c0a15060906170622030f020114011707080304032117041a0609040c0501030c0c02311103010603050402010c050f010518060103050c06130e01080c1003 73
    0x95600405441000601c07450028041449000d90206901d41c90b4030402c7c0c04c613011a48000c81e440e030700d02c0541c55201014801e40b50098245602003801c1860400300d424075040300c100090810400c06900c035410740c400c0d403081c5a20004115030030001c0d41d485000c0c1c4130000d61111806070302d005500000540110000480e0200c2e030f84255032408141d41c845281c24a82d9800f410041800f03440300c0d450700d1800107920110700c540e20420308c80442501c0d480d208030b041c10005240601400b046014000400c44d44040070084800910b40450302046451045800b1440c1c030704000c0d040b102440120182181c0d0401c442010360719960012002c2450f2030980d42540c001d44061503a00d402000140f00c3c1c64400d4004030391160040c1020100804140d450500d085681610800142d55480900100301a104e4116248140700401003550394115180c0d1f40d2942d088000a0384903480c00210340c200d03c8403000207a8020004903550785890340e9030740c500b19154030361020700620510042508049850080c810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695367491 1250 695366241 695366257
    0xc030f06050f04150e010312031a090606030a180503031509100311060702060a030614040207420911040207110f010201110c100608030c0a12031401080f070b 69
    0x290b44516110b010502c0002c1070034500c94080d0032020380c804600426151002070096200381c440c44542040d801004044030b641040b0400300c0256131449604540c1d8403050313076410135000c4401c565651620020500182001004000e500900310450001d101e0080050751003010341c2c610b035080e1750303060b0010000480000ca8822005d40148031043c0f020800c0c445184100c4103028000c01d2400081e6000220389801009660001984582d0700703100e03555002819800d080d81c26942507040140647e2500503a06d2180c2860803c00080004a500c00d003c00c44190b9000344104503070001c0d680b4294404018110080b801d54494041c0b0b142c01e1902e08051086490058010100004500354038040000c4501644d4450f4110340d2150007045050f0b404ca0010503101e000d1000411078442041148011307034980d94006000c6030024081e0a80449002c25184c0c2d5082e846a45d41406552030041030300180359840038244034040450000c01c1e0f0160004544890444410864941ca03030f58510704141c5100f1265 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695368741 1250 695367491 695367499
    0x1c1209151107080f07050a1a040c05030c0a0530150601020c0d020f0a0308210a02040e0f07170f06041a011b0c09110a0f080601020615060702040f0c030f0605 69
    0x1140c40d513240490005095020300c14000e41d001d0b40543e46800e101e420b0202d140c1c3d002c460100050004100801c800c8034001d1401707502900e10003500200044403040c26105090246a02620b8160711498040e01000d0303690104203008200206085480c0d0781c0c000d03503040e094480c0d11200c08544650300015814000840092840c4084404c0e5800d1182c450084141c243d04840c4076000400040c0e00003000c0d00c0805055048201c903105d0b40801c00f65246400380021481c2c038410041880085844815180d014100c19151700380c0340c4500c00111000315070161010040d40044c018841103403100c4503100d008520440d41800018400f1125000c820700703401406003c19010224400c8800103000a40c2a06004030041545503940351580d00a45581d805130200070200002d0f18148150840646000c00c091450401d1407440c0120020390b03501c0015010381c0c0300b21002171519900b035440004403101070b54050720901682040e00c2c07810010388450040c00c00441d08208080c2440d6506100d03010490360010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695369991 1250 695368741 695368747
    0x2040e010e0c07062705010b03010605010519230a030207021e1f03140907060807020706090501030504020f060703030606090503030a050904020d0615020f010f020c1c120915110708 79
    0x15550100404050360690a140703000605c42c04c1038000c1050380041701c2c1c001d600120341581392404050071a010303900002d060210920130044210200c41c0d10700c0140c121802e10030300881030394580403400c2035001e60110803c00006401c0389103640c1030700600038440c42a500c60018886803d5659203071802141c1058011100c0490450400e403240c1e0307000c03108805401c00041b030002c644d101c1420760400b110110b01d40d52084008000103540081d40d42e9100c002031001c1c3c00818246000101110214800c01d8100360701c403804102076580d4220440ac14050003041c40c1c2e924110741ca000b41c080c0c8010311406010a0b581200001c0340d08011086510b0080c00c0c2c3c1e0341030700e0701400d02d08110080d044041c104801542c1c50001042c1040111030765481060550024030f4807a0040243da4251415410700780d0a171401440101c1c48000000350306003480079511070007660704090394800ca6040c03001c4161308802c142050084011b0001d1000d162001d00c6016030240f1202080c80d240c00b00318401c940d00100206010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695371241 1250 695369991 695369993
    0x10603020705030d24170c01020d05030a0510050a080c030607030c020a061505040e1506102001140126060103110d060e120d0b010908060601030903111002040e010e0c07 74
    0x41c1d2200400d964443c48800b900c0f041d5069041c050b005c141c00034055009100385800e0507400400c2101c1c07201c4030910041044800710f2800905a000140c058070b001c03902d860208030b80700e55409803840900409000c0710403050791081c801d92b4462403603040500034040d000210b5001d51203401003200d00350303031500284035807211079071513200500d043d2041400410610710045140d6449001d43d4060100300401002c520b031004400244983d00580700a201d01140c055803e0865001108d1400f44806108040c141442c08460140901400041b03c4150342c006c5c0004600b12844c2450f907200d5401c181d8209161121060031a5900d00c400c0c04060710451814102342001e107080c6041c80b039010720405000c51200b0200e5007007450000b00301844200502d000ca100e905802942c85407400701d20f424a02844002e00c1c0100c65a200c4a004d0f0006041544900380f45040c180115200b0301e00300600760459070f000010800303050080d0024090030071040110000003800030b405022243c011031261203010f03d04405 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695372491 1250 695371241 695371267
    0x3081003030915120c08010510030207020a030609021f030615020f060a0c05070501060801020a1e0c140f1905071e050f04090f0b010e0a0c0516020301090506011d01060302070503 78
    0x107000b0b00013003003007482c280d584465050003500e00d94481500c0303e007029410042046009410400300300304052041c405640940d40d114141c0301242c0d0440750025580c540380c0041211250002d90030105444034041301c00c0302c1941031740074a04a13030002403403001000307007200d080340c0366907614010f08416804000814213506159220300e1040310f590814910304006c40e642c2d0390070b503001e591040006075408075411682c0c54101c020031480391a4140d541c032002002420103003003a082d03500301400007005240341c030008400800100c22006050022142040c508c0901d5803500c0303090b1503040352035000708100001c030f00082c2c860780900f02c030001e1120b403c5241440d041c40b5018070201c2c14039501c59120f00b02c40c0e000c9082c805515044501034030013801158104400800d203c0b8000e0680711003146050000451154010107560a0792280754540b4028070290000a015220400d0050181d0044c032000107840804c50301800c2110300c00e10080b40181e070b40c40e90305404a010301d440160250700100061404903030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695373741 1250 695372491 695372519
    0x110601140a030c0b040509060a051e01030213030506040203190201090b0304211d06030603071a0d0203070804060b01020628140a0207022812050a080a0c030810030309 73
    0x19000201c001d6890725000101282075100d007204050003c3d00348241e090806c90140c1c82070003078568004c2e103864440071910400086202c41a079501340b4030320303840700d80c840c4d011180c8002c0481c08098015490741401a2602c1c0185e404908c02d100e1500d600c083c000c4e8040405000c1601619061485444c2413900160790344000c0080f40c048000d801c0701c60600080401c070005041f0781e03580c1e00900d0360051060044800820001c2446007005000308980d0b90340014070441075407480703100717004090000d664040160007440140024180044100b1400c59400a1258811401503000340143c0c4403800069031515001c0d11420030641081c440011990000000e10b007d80b004500d001032141d030260031090a41300140d40c501030303241d000505a415880d0403662186a40030b51044041d08043c0110300c0b003c0c0c56002d1141445402d0008507140c1403200074403a4060762908003032200e980b0b29403004001d240c1d02c00300d5021004202540003003441c810844008009403a8540c491a60940c10f05080e040c41c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695374991 1250 695373741 695373779
    0x60f060f030f02040303111015050411040905090c0109120c0e04050c0a0303021f3b0a0b01030b09010902100e0312040e010314060405030d0507051210090c110601 71
    0x42c0c64401002d01a64644000c100460007551460030307900d013001c01d081c2010400c00b25003c1b000c0c14040500b03000c0d045c000d00902180d0b000c030390009014050004664082c0616403100710510b281004201194001089141c1d00102c240d82c0c2d1100d12352210b81c04102c030583d02a020b040100d0501041c01070a0495514941160040089502039082000010800006500304a0042e041001c003140025018070700e69844034030b040c005000d01c0d111680000381400310b00e0854010318411015000d9540c00c1d06208200a15000090304c050f5011400c00d9a5004828401102c20103070b2403000030000141880354054a5038024441c1c2500c58804004440390f440c0d0b12103850781409450000340207a03080c107000300300800d8800038508007985982080c49200890b8110b01c055500400d0410001540110031a04a407115041c001416114081c04440e14010601e40d00110340420003485106070181c09050101d41c1c0001c000c0c001c445501c842151404c242c04240101640300d4401844040210480441c0362 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695376241 1250 695374991 695374997
    0x302040c030e0a03030b0102011104060c1205070b0901050402130e0a2612040b090c10230c1e121e0d05040828050a0810050a17060a060f060f 62
    0x850401641c03c2c2032141031a42100480c1d42c8810401030b0b541c0a0060350003111000d1612410301e4600309020f4504041001c0042a00101c4031542903040e0040b02960006a042110070004d4604400d1145c0200810340d000d0f44541d031203451760070f130b00740c1e10340900c03075030b40c42d4180c040d101c00311541d0340311034a40d1030f21500101596074184407604400e0500780035160100c03041101c05036908040c181901c42c0100a06101c255420030310000507079446802a2403c0d99440e0f151a14035000003800c104203a8500200440100400154840056100140b4030490b40302c0c030070205100c8401c1420721a03944072524560a000341c0306000358502010f985100840340c40071380250900d41911035151004603941114122448070340481d0b0302204a94500810079900c84202d00c2a0710807407141000360803805a1081c1d40c0420900400041c1c4030140c02c640b03507000380009044022150388555581c003071000e094810080a01c01c6d82e00140d1407600034050318044030f5805000c0c0b409541401c008a444504000c80c4400f8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695377491 1250 695376241 695376251
    0x220801050412031d160302120102070b0c0307090816090c0f021b221506030b061207020c102601120b060105211005100e1011010e0303010509100f0302040c03 69
    0x20900040c5c188100c2c4604140080d8158410070001003800041c070602688103018103c001030f00e0600c15a0042410240c0ca0340741d1361850021944101c140e001101305004030003265060031405036103181601c500c0502804919107030082190448584075002c401a03001c130054400702003024084102d08200070303283c01064920305c1140742d402c0c480c442c019807000f41c0d81c07210400502d00044c42c102c0507044510b014052030343c0d40c9001a18a00410f40e403120b820118002084003207008014a01a80101400761010200c0700e6002419685105000d030b8203102400040200480083c4d6815040e00c41084200c4900c03003042e118258030620041065040c0301080112a82c0039807141c08000401002c0c044a03096440d200450111300c0e025a4003849c003a100301110003c0c041d80001c9403036440102981c40118141418200300d41c10003e903402615a540790088284201c60f001c402103060314420303110905540c8400003c20700300790070b900c41e80e00348a502d1007041c001864030f034100c51004c400fa40740c0420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695378741 1250 695377491 695377541
    0x100e0613171e0a0b15040f0c0c02010933050c030c010e070b030c2d0f07050105090a030804060527010b0f060f04060e0d05010222080105041203 63
    0x41c00110074900c0780745500485840c4030390040b4007076000340141c07544050304a05041d0307640c80400c0880074140e142041082590724045440329071141c603020140650920601e9103401018188101003201640007491200b001718100320100d0303880040304001204080301c00194500801c10791000010403003040410440c45907580307400c00281001603490000012110b0505030707903610b40700301540641100c0d8801c1c810040c181030120300740d410116500121059030b0b0f9118030440c3d240c081d02d01c000c02c4001000b050101100409a0140038585d200f04000c2040f621104145a0ba48141900c001c1c0081c8150001400240694000e15000788900e1111052810306502118051404d10550b0800d03a560b201c00d01c5085c0740042c5c40c90024501a40c1c1d040ca000b50b5244004840d10490280c01c0510980a45007a0162240b4100301340b00341d0440000c43d25685918a805e00d0310000c408a41d0010381c9450001c100c500c4180b040c0390007035900991640765120019400e0300a042500c02120ba030844692a0413 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695379991 1250 695378741 695378759
    0xe0a0609030f0908010b0a06030c140f0c0c040207050a021908120a08070306030203030f0c070b0d0b010801081225050a030509031b0f010804020d0c0803030114100e0613 74
    0x102901c2a111102d51181c038800040c20410385520219036a07040040c0340403541c480c06103050070ba03000351501103101400440d06543c1c1c171001308100b40c1555400a00400304980010151038004c0b12030054451000b041400c0006a0190807409007803500000351000051400e402c042c107044034110200c11800e540c6050b040c0c1001e1401040d540c1c04503001650b41e001941c00510365501c40c01d40c0c00c2c20886079082d0b0b004266240101070440500460014601c400300d802004620014080846129626034400464001038080c119040340801e440c04004070325600046044101c95450400781428030624601824122075551180003214407044841e801085040c09102e1000b4040d0b02c40c80e5075145023101349480c2003240d103d03000341c102001205600e04e40d02c81c905402c2c00c000910b01079131542c403a07000140c0c051080d841c00511850030504006903007803000c0091412900c0000300316505003a40700170b01118012010f11000000d5601e114100e19143c00c401800e02c6080844040340f550303403907001e08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695381241 1250 695379991 695380001
    0x5072102010c08060108270c060f0429161401020c0a0c050f090c0d1803080406060b0f07150b0406030b10051009090e10020a08061503090a060e0a06 65
    0x600181d469480441d0481e80005809420200a2078001d0741c5251840c0d03480c605000754030848409804404030720750344480801a03051081c4004100c1da41e200e40b4403400040c41c1c0c0c054401c05001119a0280c503000700c0c101240d0140c004041c01149140461000c131864104200c540e0480345100b0305c0c05c06040d000c03c00d1025043c001800760090917003040f5810034411000a41d8099840344001d00407640711074407540d440680010908450580700d2152888250240803007400c8410702048d142c3c6008113040d80400342030b0182d40540c1041001503101c00d260130741442000d0750050146810001d1200080f2400707028012400d1151000414000d03020019050f42ea070740d402516820025424071101d5480030544500402080f181181040070f00f010181040c1c0c418810850307540e984411030b480e803c005102000d1100c2640c2811507841e4a1100054000b03e0300f514960300400421402c000000502e104a038050350500e8010843d100f515a603c8024085000d200c141c80e010f4418071000144c00f0b8011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695382491 1250 695381241 695381303
    0x30c02010c080d1a041b050d14100e01060c0c050607050c0a080a03030b0d050a0f0809060d0501170706091e030c17120301031208090a2015030103050c010507 69
    0x200700c1e00800200340b0602d01c440002c19104601d0b04204400c6e010000c0039a5203072000e1130900a448100303080c1060b0007005010f4410003400c0648041054801c0341c40380740800d9038041044060180d80380d5008407150040141c006040c0e20034400180003030b150400180a90620400031a5058903049021461500445c1d10442e03a56001512034010141c05000e24560704005881d2503119042340d455890380c58884501c0030b050718090045100c00d004d200d8044030f010101c050b1050742e444010050540040034248941004135142d000d00140c04403000c071342135048601c20b40e111003c0c181071421180101e02d000012003640200c1440000000f90030700504070092500741075080121041517101414441d101060511a000c00c10042c0001001e00c12200c900542e17516120000382c0e18a41420715050b80082d015021a900c1c0c640305d42900b4454007102c07840042a9004600c400788400040381030302080c00010034030f410000b080315080d44100d000c0d101c25030290000700054201003100c80340846002c92 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695383741 1250 695382491 695382517
    0xf0706030b0f0108040b040605040f0602120103021e10030b0301020903070e0103110109030510020a0c050a0506061003140c071a0a05040c0f060503070e1f020a0b1012030c02010c08 79
    0xa0301c4103841c40d0100d81c0d11019070003030074440c10914180d6184030040c1c400074002003c0380d0b6200081800d10684aa420088561140c001c41d0341c2d9190300c890b142d050308240f100f02d00c1047c0000400601c4100140d40d45d944c204040c1a410420100346401d40c01b03018240481c1d0380541d8203010713903d01554100180d200170440c01c085440c0075411410302d1180c10700400c0300d040c1030041080d020000030304002354022480209040040c1c0762002503030120341100042101520502c610f00890b8140400803420a008040c2140e2040b1200180b08050303099803180010751168080700030000d6a1424114000e100241c0b0500c40010a0b018810b0782a0442d1401d4a28900716680e40c030412080080781020f80003c0c3c000420300c04011071070716200419600c001441030007003145511202a041e29141030305054006d06400e0400030081c4444025a1b035124504151403200e001c0300403500703503400030102d58151180030b403c0001c559a10348060312a0403103000100d0401c1030714610040401c9044000c0d00c6c45525501e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695384991 1250 695383741 695383751
    0x91c1b0b1e090303040311010309150509100b0a0e060d0803091f02090a0302100c02060a111005060a0b0f1c0507030e0105091b06090303120405100e1e0f070603 70
    0x160a40054007064100d80d241440100140781a40d036000080c0c9040760307400200101d0181000004a015100c1c020b00109106480411156907003401d80000b03220380c0e1a801269114880900204140d03030b15107200b80d801501908080c40900307000100c065005901402148802c1c031165a41d029691044403000b078103400103c44000c4400040d0000a510f0114131001c0d820080032034009001002c1038070000740321b428107020700c2007290f01401d10b101220f0b4000340380c1a16155000b030090204030f51121491018010f2018040c0c8034000c510681e40101e0002d001c41c041c9030b06003104001aa40902c0030b0014234507040c8002072461400007020f07086440003900c049514280100c0c050142c0d0005071251149905110812194100009140140c2001c80302c0d0b00b1b4a284005003c2a0316218401186406002c0040d00d2440c010350700411500440c4034004591010002c00502d400b00d400040703650341a038010001c014828007681e0754003201034503400c0c283c4500f4818165064a001c503a94002400b0076114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695386241 1250 695384991 695385007
    0x120f0d0503060a140a09020c100f0203010f0e09030a1119060c170403020c091506391f060806090706260604020c0c090403110111091c1b0b 61
    0x25a01010003010300400040b0030407010000120345c201c41d40220001ca59020403620038284081000304030740c00c1d0710041000305a01d104c3c0c2c2c0c64040d5009000d041c0030600c0034203001981e410002155482142c1c4407018606241070701604070f07200010743c2c0050000d0300c12000200b1b1091909010a40218070900c400550b0030a10b140103010401c0015003501c4501036102080042a00420403078891807085818a030199181005c02251039526202581c0152010a40c2101005a035070403a8212402508800b0035003441c0b400c801d08440300e41d5001d00d10b500199002004850f60700c2075048108130304540440c0c40d5446480d40c92400d03004603a4070b0010342c03110008100543e0441002c500300103501c91000000400c00f140ca0913680b05c041c104900485d80010b001c0103210041c00314207070141c030081c588502410641401481c2a55483e05844c043d442c00300030303640039001603089414881c1e0240c043c0141c1c48220f1140c1003082c61100d000c1c2c503500300011079004024100303440744014010f0420510380385e043d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695387491 1250 695386241 695386249
    0xb090f0a060e06010f030b06040801140a0501080703020a140f040509030a030b0405061005373203100503060711010506030106081509011b0302071103070f05120f0d050306 75
    0x1940b0800e1480c290030144a202d9030700c02c0d9004502c14250401043c06074180010031161320880d44130501c907510700200800105806540701d07010362840c840500c1241d80b0360044544502c1c072480000d6000c80384a80030000c1000c0803050b0900203000401c0b044034000f25074046020745074200c40180300f81d0400101c804030680c040c4108000840c040d24200301c01d103000302c04a240400344440600c01e00c0008102e11000c00e030180b40c40790800c1000f80800390454042400c075500c50100d0540710b800f2a000c0358101351140792000410f00b20b96040c2c000c98280c480c0b01c13800c1d44826070018021004051301c058004c200c0d602c0803c4010302480c0039a592070107003039000019500310749000d05400d1003641010010410b00e040080c40e010000c14802c0210360b141c6031095654010442c00c0100e42410444c40e1100c0846909a40544941ea02929007140680b080e01d0416807510f08a0191042d50a641c0700207003c0e0303040c0010720450f001144001c4130410b21080d40d80f03170301d810800e80c142000900c00100304450750074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695388741 1250 695387491 695387501
    0x1e080118230603060f090c060705030708121008121608360607020d060506031009080301050108090313060e01050706090f140d0203030705092107080c01020307081c0b090f0a 76
    0x71400c030001402d414049056034856007841c1f0031511a143c013141c0714041c080c2c14001c541d0700d2903100700711a5941030500254111948112103500156400785000140785901040454400d800d8980040c0391015844491350a41401d040c1550504400c0c00943c0d00c05010302d40406810340415108003103007458250606003620828440d0b8001d40741805240016140c0d0030103d040c0310b81c08800400c0c07607502d140101e031070300220b00d0180420314102422081840040b000446c142c072000e07a0790740442e660341d0061a90380e110f241050409000404c80c20032030a07200d02c50b0110301d00340500d0040d145c20100d44424040e05c0340802d00f5034020310444880c40030410030b401c0d400305049031080030b8200c46403030040280d12404018245014031130000307241d9005a0794400d48040381c41c0d100700c240f0001c0140d4070800313695140728002c4504034410303840c0e02d04003580004155550f0030380c00300d8010f1030321a0a29007480d000c203040600ca020191210345021003a607a517030030503200e2600e000381e5505610340521000d069903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695389991 1250 695388741 695388751
    0x32206022101050a0303120c030908160209070c0b15130e010e0d0908070e0901021201180c11070b0c0717030a1404060e04020a0c05030a03020a1e08011823060306 71
    0x2003183e1410000603800c100034034401c0c7d80303000000451201e0040c040c0c020f0030309000014502200080c09103512260010340c42da980d4001c0e0b40040b07040d0342d810310699400c0c06074800a0418200800050740d403200601304a10302c9140946505075200c14107100d03a00703988680342010050394503042c55039034061081142c44281c400d903282c41c03004586040f2981783c550740380380110400c92200000045441000350100d654210681003d42595070f541d4002c0c02003503140d07100618900d0701381206a0700e140d1088110480d0701d20240064190249000e1216015901c11241d4031110300587c1c0c4001032010039019000580c8404c071000c0c5543c0e28040c07d0040c030f14622003a0700c042c01340d824082407101507800100c0a01005040e50016078800070b89905231002c403070001c801001c510000030032402a603032540150542c12850345804c51140e18202c820030801c02402103402c00501104010041c00021410380700c2000004c40c000903620901e04006c00c10941c07052654110041c0382c40600115050400c03038540d102e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695391241 1250 695389991 695389999
    0x50d11031204143316050a03050304020112090201090510020c040911010215011203030e0c0d080c010b0405040f02011b14010606080a0e0a020907090f0f06030c02060c03220602210105 80
    0x7480c400c120405100611040c24001c044007080c0341000b8035400e07a00b80c5001b07411804071490342c1b20a01d4028a2907000711007ca00160a6460310281c0c01d01c05c2c0a51040e040c1d050f158050301c1420070301401030f000407144160b000c600c20364480383c8003615540301d1141103074011080d2040c4070040d40000391074060264000300900440304010003850194041001409500d441c000c5445442c1a94071403a24a21580560380801d900314040100800c003401001c0d01070b403050082c08900003100422003112412980545182d0080440c0e40042d88590501c20342c003c1014070001201140792500b01e015005801040100ea40d00c4c142441501d03040610540d0007441c41e401801850b1551a205490b00201980203005554160200d4000c0b4060f2039102c0191080703403003c0700400d81e904034640d8aa59213228800c00709150202c001d051074804590244550f0181403894515219103080340d100100c980d1180f00d9041000758136800140c0940028400d1840303070b1510007045c1089418202650f03c06a126502c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695392491 1250 695391241 695391289
    0x21203010602060c0a050d140712140a15031a04060501050a050303160c0504110d0509010b0604030f0510021614061006050306060c0706050406090b0301050d1103120414 74
    0x1100d980011031030342c003c41d11110b86482c0d170b0107400203880c1d900400d01d03031070246400c08401c1c104500c58010b11511903070382076880e9009001030480c0101142c0000e9000901c401107030000401b0b01080c2d4004246490254204011242c0d85c0d07200c41c0400380f00e0300101800300d00d041c0140310038018140034060241404842c030301011850040081d03681e104042c114184000d9050000c8103000c2e842021000078000540305014440341e004c4001095401190b4401d4050b203808003084072400148214009210080c00072441c29055456021204583c000c04607918172504003964510006030000c0c051521450701101d00007607507072030444046042c40da060a0658400d0b8208102e0106020520040b210181440e60b601d4541c07901240c118441c02103111428030400300006102c40d400001401102d21b00d90310740d42116140c2e80001018070007031003007507446a80c014004002c41d005003060b58180d4001402c0311114102822144d070780d504a07911241500f40c4040814909003402c10301508070610b0760b10481c00e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695393741 1250 695392491 695392499
    0x8060a0e0d090315061e05041109030d2d1d030d02120903010b0603010b03100b1614010209040501030506101409130f0609050d3b0103020706020c03070302120301 71
    0x950070b500d1001911030303014034a988900300401e9004501030703e140300b442d40e03d11800d583c0c4404041c802d4401e09005a14160700c41c604814000d05072441541c0090243c500202a1401141c00c08103a22081d00d511108402041c2440c2c1c2a034200680003501c0d8540e10a60f1b21845c0e41d2140406400c0c0301d40d0b000e40c00078143c081c82140c6c0881d41000308028070030000e03150300341040464010280024003940001c170000001c034181e0a41c01c00b4501c00d43d01d8107680030f01c480d141ca0100b02503000319000000007421210440c40000c0702c803d4070f80030890028000504184d4458005000c0d20303030031b03801610b6541040702403080d800744143e22440600382c00010051405134060215100f00c0300248101060f040d06c40303090080100c0343e0f0585400741e80144003804540003d061051701c0300b45400c02c41020a4940240000323000c10840e0201da00950392080c41800d00d22000c540100002c078056080c1019800c1201800040051002c1c00d240041440195110340d50707868040d281c9590111550592401400100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695394991 1250 695393741 695393747
    0x80a06060b09130510081515030f0309060706141f30050f0f10051e07140c0f01090204060519031203150603050603160612150f08060a0e0d 61
    0x20340302d50707412400505544c0d54903145d26411030136088811207010344007002a10041c111550350040f200b5100c41c183e00a4944101566845041c00c10b00e4a500305001081161822401911400d40518008a02c4a00e07000d94000c05003000c0301c0e008a000f00700e0b40303181507200038541d05030b0191400c6e003c41c490740349158041c0c00c9401042000030840c0c0904100034410800705202c0120b407007801c03401700d584509203101180d480b1007000c0c681c00103240ca031500096040342c4244102c80380180312240b448650300c841d4012540725103090310700b0f04525401c00c140c8411280420001c89800840c0c4d0002032003081a10403c016107015500991150501072150780e0101c03603020401c01200da00c803004650f4034214032030650103800b10b01c0450b544001404030020b501601a0403092280b1012010359010043c6030b1200284448540600340015104103010401020954001c0c01e02c000302c0c141d5106250b0b81c60550300c0c10f0340340035000074446802c010184042a04e080c0504070806054601800d140b01c4403220003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695396241 1250 695394991 695395009
    0x60102100908090301090b15010c02091311150c061b091002010605090a020403150e061612060b040f08030403020f04050a0207020d0c170f0c0d02011206080a06060b09 73
    0x1503504603540c40e2580d0401c00c100084070389042c03001d03000340805007060a00e000d040600721040c0701012103030040144250301c22080c40000e964020b00100450b114a124240000c0317a01404940c80b00314850141c2440e070340e46c11200d00001003244943c0d03070382c6100788010f03003032003800360640c9213401005038480c2c032100e004816070720400d4007513032882c0c51202d1241c800c901403c0c096001c983c000140b02c0500000f90141e800501c1524051a4401d441c155011014001c48070400500c6100350000720215410304e8031003c0030021400c1601d40403000161800d07079032080741c6565000c0315011100250400c5604201980c0000070141e68010f5401e091440e00810a2802c16003c4184202c2e540e0002410025440d41aa403405401601c0d0716205625450240c8030158540603110032007110343c825075010240007130000c1028040a018140c0b40100307006101c1c072142001c000300e05001600884102d000c5845c851031004240c844014142086a401c24900b110030940000d5541d900400420829031611455 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695397491 1250 695396241 695396263
    0x2b1805070306050c041203021b313e0c030403030e1c050601031b050d060902010c080c0a020f060406020312061504030c1706130b060a09060602061608060102 69
    0xc041060b13034404803900b072940304681040c4542c200c15440c00c1c0c14164009014032846000c03030140101583c0c60030402c00c07015014001005c604e10f0380d8104500ca032a000741280030100c1140d2010600b01035005403451500e810300d46103000c0048450030307009a50300030356054a07040c5007400c206181a00a80809850388524000039040c88030301c40072807889485200c1020707514160380301d6038001400b0742c0c6007003a181d00007880156480000192014010340080040c0d004942c40181140c81e402030030380e500c9010305812034040e130600000c41820f501040002c00240000c5241101400106081c1d10400c01503000380e8180c0b5003d4602403100f40103050700042120402c5910555800e0f81e03680380c00006142d1401008000501c0e000070070000100680b02d5001c5c001d982042c195040701c0302525104980d951000c0b5055449800c81c09100d10108500e01c40c15030b0040e502512610310390740c460300392900340d4440350b205100691168041012500c88114034900b80c00c00762805a0007070a1500000350340340507089d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695398741 1250 695397491 695397503
    0x16030305370221070c0507060351090e0115030b090a05030a05120912070209071211040e090604020f060c0102120c040302191203080c2b18050703 64
    0x103000c1070380707070f60442003145a1580110303141280c5000c240081c40303120306400845641c49641c201240c2d0a020b40103281040e4021008070746201031821816505450f8403130603605802020142480700081c8440f9040141c803004c0d0340c9411103203058076160132582d992070200080c1c1d242c0381c40c0701a80c48500a0140450382c002180c540340da124850500d042200c00c410007441440002406002c60350000054071500c030300381544440a0f0746803102240c07216548240c0740c1c1c124004004540052400403500d5030000c001e03103030214000c0004101c540840362060441c070303036540c0080340030800b904050740e90075800149500034040da8101540861409000d5003a041d01ca81c02c081b41c1c2c010a001d096058401c48902c40f04100d003681420700c50b403001c0b07611a0206030700805440540c2c000114407a0700e404c045a400a100c80005041c80d00c080385c55a00c040d00d004e899400412484403032011009a104d140d002e000f407500c145130362400d07500c01200d100f0310713101d2401000c4000c0710011036070108455040340e810907 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695399991 1250 695398741 695398747
    0x1a040e040b04020f041a0f09010f0b1b0d020709320703090f1202150c2203060e060a0509070b030a0c0201020c0d020616080c07060b0105160303053702 66
    0x2100040c0b0900e078448085400134944200f086c4040e000354007508122205540791f4001503079080c240b08440200740034503203100b2003410041010511450007000d01e040100215991a00c1030300b02c041c100181d907070701c5e5401a400400240004a201d11032100c4c0910303458950420340c070803914a00409004002d151200b644031000180c6018002d0700510041c07503020031140c0c524105450301514851406503070f00f005100b800c05c000c640000c005420b9015201035541c00b0b082820340e2a02007083d040c00c0919262050321740200000103044d5001d030000394154a805003007a131403c0d140c3c002c12100d001b42021025440710a00f080400c0051341220340018100601184c2c1c9034298100f81d01902c00c00118401c103205205e05401c1160340825910702400201d11103400c015141c0504444c2080b06031030f400d00b8070b03104200d290f000410590003d1409801130400900b0003100d0207006080b1081800243d0100fa141e10030030032407000e82c504001d03203c1e00c0c01048003400448034041d11080803100c0c40d0040f5085e400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695401241 1250 695399991 695399993
    0xa1401030c121409151012050c090a0f0b01022404232109010914030a080406050406020705030601120f0816140c01030e061609090f061a040e040b04 65
    0x2c1ea6040222214800c0911074040c9540400005000c00c8889415a02500a00c80c0602070030140060142e2071010341c1300c2c900d80c00e29100d00390f4842c1e50b880031900b6124103241d1036916140e00740a94419100c01c040000c40340c0c03000784220f09564250380001c0c110f400205e103c04c0c00191060102000744030040035507880e5a6285841c3c241d014407a05845800010034280c0e4640034000505501072000d40c9445070014682000240b285005000910380454040b003000c2c85030f4a14010548a8008000e080311039180554079540f1080d441600114001440014103204098041042d00d0041500781c00500d2107614000100c1d903c0f5000c000d0041c41200044540420b0040440513982240c285c4400355404c3e4155140948150b2241400032005001b03081d162030b10796010384680324407c4007074000350841341e5500044070907500d41c1440f43d10500582000200e9440301e61302c580703400700f2040f450004a260030b29101d0b001070040d07802c7c2d01304444410082408200001441250032a40c0440402019155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695402491 1250 695401241 695401247
    0x2030a0f0c080d09171204200a0f06141c0504080c0304080706110d081503012403030212030709120c0905130c05030a1109060d0c0603050103030e0a1401030c 69
    0x210401900400300400d001c0c15079141c3d03501c0100114450104002c035002c0c4c14603101014020300c02e10701c4001030040000307000310780c21011241c01e00520b1500a010615070f4800122100c0d01c0c0d411030b112490b200b0605010646d0400640c0700c2680520a069003060a230301c05a0401c4007414040c02030130354646012504004d60b000941d4403a01403001540d848075101c8080a039201c9080c03040c000010461000e4141088020595851601c000e0781c60310515611004004000d820036031806401d59a0744040200e140358580c0329a0311703000c5007515221103a1440c1402450100d030006110007108040091000c226044905032046980c040c0e4100300701100380c14003040c08105540545001330030301c401c0041080c0c5102144204a20074051a509035484005241e40d4051141d8001c0c034070380c011707140d11816140c191096607018400500d0b8420681c6980c0e00c2c041d4100341c0da0310210100340c58400500405800901e00c202018040d40d1203035041d0b29000d00030400c1003040d0351035030605585003007071408144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695403741 1250 695402491 695402507
    0x1c08090f030f0a060506041107030e09180109060203040b070203032401032702012d0c06020403050d080f01050405040b060108150312092403220b0a0f05150102030a0f 73
    0x40c40740c0c00c2d5003c4460701d00388403003c0d20040b5901da1085261141c0791f0070060305c40c01030326007642d09540c1d55000351081c00140719501e140a00402e081d24503007100d95400d40d00034090311052911440f4007685908051410700e4581c100600101c055400600c02c0014421442401c680c11074141803200c0713038040c41100103a0003010912005144c000f48052041002d0000c0030000c40c06c503100f0b03612107a00d5141110b901d804090070311154554288881284541075101d078900a0305940980c40041c90540d0381d41c1c1d003900e00b91262408801144d803403000c010511044011701801810b0030b960500c014546070f602c014491000901280c107119040d004514401078404a0311007601c0090708445040340d000020b28000d400007082288030340080c1956522a2070018410b9911600710381440b400c40d11019840c405442c440d01007010f4101461402c440410203012206020b00c0c1e07040c10002d40c10381d26680000a80780b004003080c0c0004c0311100d914030fa90f60300008441404080c0d2818015101d030804080384c000d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695404991 1250 695403741 695403763
    0x1d0306191e0504020f180a020a0912030c0b01150509010c08070c03030e0411120a020f1603050d0605040b09040201030c11060c0406020d0807230403201c08090f03 71
    0x41111603070081209180e070301c21801a0700840301d01c10303401030100422410300c98914074141e00c58240004220b5184094014120411042c109494125110105d104001c02c0001d010381c00110040810300034000d07604c0c41180074044031030304102a507881c40c1d0090310030710a040c80c040c1008403151042043c00040c1e01500c200591001c00700c0655a564140104800c3c41900c045116070704d002c1c00722220011b00411501c0c83d0f04200c0c4010442e0790b40c4000c55000350400884804403800410803030328141d460100000c3c15078404c1c1c90301612001420212802c42e02540c000c64060740c608140c001c2d2a40d0380481e0b007075005909180c04070b081c2e070088004807003281031503100e01d001c1d20840c010b10014540c5a009001919070310b03800c56020017941c400495481c001a80c0e04c002203a800c4000040741c800d500c0b079642c50121015009840c00707a580c0c0d5401c01050007150341490503140d1040c081101d1914052404444461402c040282c005a480c0c03100188200480d03c0e02c40c40d0382a441280903103051103000e40708 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695406241 1250 695404991 695405021
    0x20d050f0d1e050108160302030714010302041502010608071403191509140d0206070f050a2109020307060305071706030c0612010602011812080901060b04151d030619 73
    0x21010b55000d080162000380101d101ca405010b2200d00080c04200ca44d00c03c40b50005c00403d0200e180010307061103100d440014504046d0208030124801c0c0b0f40c02e01c19450360b4800d07400090290f2600c5000c0b07040103107903081001000016052001a941d001a0b01c3c2041004030345500e110340d90720b140880541040011007064641010481c45c14095210080702044550f141550800106104100e880e08802c44078100450015103403040081c1c45a4058074011a050410004104c1c01005810700018074200321b103420340e00c90f4184421410305000c0c6900a241d1406c09100c6414080c4c00544401c03021a1000d0120548100007402643c0822100410300d40c040c0c000c40d80d0301c58000b0f048031904004d00038100550300b0b20303a001282c00158400801c116800c006500d5070b261710760804031604180580101150740d2940404206c1c206150002c00040880b081c0c040d002103680c12000e003c40f000b0712088200146c07152100f0f95130340c901295030b69101a6044446252030340f08007402d0000d05190080c0b00b45 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695407491 1250 695406241 695406281
    0x80109030504060827031c0504170a090306060e0a0e0c090c070501180f0c060f120209240406090f05030c120307060608030d0e0a020f040b060c0105040c090c020d050f0d 74
    0xc103000c80100646064040d07500b40390310b480080391f000c5e150309660003010180c540a00100805100c8013511403520945401600690340b0340703401c2c3c01d60301d03a500300041c452651024000b210703c562103840c1010506074040d00303040308010000303417900c8070040031200d06000014842007045801c3d8000c0e11085051545038641000710304003069400c0c0c1103401107a003043e40c88004682d9602942a040d0381111954814520414080303102010f500330a4290750001340101044030f040c040721007041c88180704941c0c266250f0f07182400003440040300e90320100200d0003080042c01305071404a04460188419122201c4850007640303018614450504054011442d00c800460f444602000400700310005440038050346454100681d2100d0002c00029842042e100d0711700c070a424160482d07003054900400040c14101c409881a084d00c0c41268210345114102c0b40030300c440c0401d4421107441202c148003d140d104407110000c0c0c01845842400c00d10b1080c007042d8000c4a001c00c0c2c0001c40c083c0001c002c400310b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695408741 1250 695407491 695407561
    0xc151d06090a0e0c0c01060b03010e19090501053301050d0203091c03020d050709180b0a05040c081807030f0b15180604052401050d0f150806010801090305040608 71
    0x85a40007040e00c60061b509160340050b4403035807002507034140c40c6403a074070040a40b100c0e091801c10f40195030b49480b40c240c5841c0002d002c12028881c0e1882042c000050001100f01d5861400405880c0c02a4424050b100208013201d660b00109176146454903120060762512840020b51610703180300c4600310215610f5034490741c0349603d50081c00d840395100701c05206d10348480000b070300d040c40e51b13005410545081101c050070210113074100c5075444002400da10903175525000440c3c180c402846078100402c03045001d02c809501914400c080c0c148070342e80500140c500310ba4030388845100715103014100f07402800c00b05400d0039070a111454070240007000300c00c00300c02c88414a450f000e011508940b00e20314020005411010000c0b54442601e440807c98208550500041d0783d40c1d0010ac4400100503621518050341e00c05502c296221030420851940c0483d2826034450f1034903005804c007140b0741c1d0500c1840c40000b0f4011042c3c5054858a0419410b5a503850401203550360001d00712a29800014080b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695409991 1250 695408741 695408761
    0x20103020c0c031c1d01052205090c040e060405280605030604060e0105090a11010f1b0c0510050c03181c06050123090c0310030f0c151d06090a0e 64
    0x114110845d403150440c043ca085c4641d0b06820100300701d1804034004004441d09001c80350346220540b070408089000a0752900041559100125203940441d840080c0c00c0c003032002c140c10303d10707031000c0229810301461501e0741348803100d03043c00d0700182c220b0cc4031001803800d20700311900300401410018048429a203054206640034144012090701c07103510b4030000c950b20540c042101b80c413483c0c0140302d1100304d8020f88011030300c0b0041d41011400700000712501452982d001403081d80a1402401c40c4984c01d030405040101c96040358202c6030610108114800c004040403060b03a180080c15600b0880c90001240840c3e40b10101942058031150081544010841c4562085051b209124080055906640c0907504d0f01c1940307900c80d991000300400020485140c181c000d585c0021103c410540541e603d0b035848242d0440d810040341c625202180a0008680e0550300088a5030b0f40e2400701c1c198043c50f03a01e40380d60b40000400d203020701000182200c50f5160300b030301c440c010f00c40c854044a1074a0905446 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695411241 1250 695409991 695410033
    0x18030d02070b01061d010809070e01032105070b0103060b04020f070605090d050c07030b063c1e04050c0c0a030315060311190215040803190e0307020103020c0c03 71
    0x1c40d07005148000101c2c1083c03049805d20503050300c9030100690b00740c03140e0054600720001001c51525206900005c134032600000c1c912402580310b04d08050b02080c140d100791b00e40161012150382002006e000d0840865405219a8116a004003002a0445c8400046000f911640854a001c01400144581044800d030320080c80340c1c800c0001d071540482c1c800750440303441c4104903400200da4030286080c80441d02001c02c0766004000204160340340d06011180e40003051808521494400d80740c00e0040e0801042842c14900300401c0300e0065001e034010b8002e036040e40c2010301d0b5034003450751a00002c0d4121194021100c1c940c0c0002d003201c20360000c13850024050182e80e50114403400703154000041d0307cbc0c000c1c080e48100d0100c0d164141d00302220350320008408060765148000b1071103a0103006081d03072200112035010760302403641103a891815002da48204400000c030700110500e0048103198803100802078440750741c2d091034007598031002c901c030207403509000001566141c00342014403c04030302c124481c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695412491 1250 695411241 695411243
    0x5130923070207180b210312090604030c03050c100518010f0203040b0106081b070c050f030f0606010c150e010b03150403080f060409060501060e010917031218030d0207 74
    0x100101541d11414220380740c03103544c400e51400418240084000f1000c503040300031145000751142e404101840b20b009910044c102800d541900000358601c24488130031f01c1c841e800140d45004041a00b0035950042101100410240421001140c4661840c9003030090040701c00c480c607801e00413401d04180c40509010004e58103900d541c80d000d14140150110700a8a02c03540d041080203806a20300340e000e48031800020300c0303185044400300302003440c3c1004a000d000313820f001700c10754400d840c100802d00008200d010940c40c0b00394800d41400d0180000090b100341e00035401c1c40c140c1040c1e040c2e480d140b00a1403102a0342c840240c241401c1501801055110911b00d5000714104c40c0321694406003540394003002c2c2c0e00640020380305000140700e0601c000b55940c12003800b400000d400701e419210700c401ca4070281c10000014505c81c20300c45207503a000b6660800b03002c40103203000c01c42c007032440c41780d98911038400c54400346d111060022f580349800c01e080d0654104d0300e00a4a689105200303161009602030a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695413741 1250 695412491 695412551
    0x190509071409011a0f0f0d090606081609020a0e0418050c01090b0d1109040504050601080c0105120f07090b0f07031e211b020703150c0c03051309 64
    0xc201c0e440c08010150480d1030031070200342c042d09a00c80342407181d4000c03001071419240410490680d03030b1040c402000308044500d00010701c0d6284d840c101066a040d9031201165900c0000104558480f40e82580e0407180160350042c8e0340c0603801404d940721400000d440c2d0788289002640110395603002007440059100f0f009031000411200c0040d01c103a50340e4090344e42c80003000d100144200c1c0a9522502940d960030000720b0078143c0c1c500c0001c0c1502c504460440b91130304214010002d49004120322440b404003400d00d541001d4610341412070b00c02008194a03504070003c0007141600e070140c6220001b4141a4410a0740e5842040403c2525808030f4000c50001c1d60800c0030b01ca00c0706480600070041c8000780d59116403110404000c20405411804485043d9910880c8620000e10340000b0b0481c14402d40182c8003292560404071004607008017055401c0c1e0801d902d00d03030310b507501060241c0c2d0a03500d81885a2a4800381e1801c0800300d0141d080340ea145890100c2c40c01c0c550150302240c0940d003003552 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695414991 1250 695413741 695413769
    0x4050c0d0b0406050c1603050a090b0403060903020d030c1d06040f0825050904020d03030e100b15040e0610031e02032208031302040b180907060f080601050319050907 73
    0x1c210700124816980192404610b00781d42d1b03000248140010a81200103150a000c1d10340c46595003401d82e13000364800c03034240d9603481b0400c0030590140310099100c80b40b81400c006503a40301c2405480c0290300c4152002003601a1002134035503440c3c8099602a00d9840300c02c0d2442c44e180c03007a05030348492168065607124041d1891744061007040c9510419a180580b000c915901c8580c02d101d160042c40301c0031024503480b03191710070580204006010883e000c1c08004030300e1045035428803500f00e1000c0714582d480c100802060101c0c0042480326070704401b003500d040010301d5022004130f0003010243c0c0d01d508001c010401a1150703282940245010b5149009041151250015243c1b00d031180003000402404040c80042c0d01c910070390a8140e80c00303001400116100d114140064101d840c000d03805403841344580d00f4000c0c1c85204204c6140549505e00b00100b03070101859000d800404020025410040000300080f07a10907884c0b042c40a0902c229801d20945c00e00441d40c2e5281d00d464002e00041507041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695416241 1250 695414991 695415001
    0x3060b181f0c12020a050d0306140109080d0c051c08071704170c010f14180d09050607080702030f06010501140f09100c1b0e0a0c0e010804050c0d0b040605 68
    0x320820307070751150315502ea074401c03040c090362418010f00d240b401200c01d40c01443c04400109505105108203d09130b5a0002031403402e00140d60140e40107200018100140031000b40314584000604200104081c14000d2142800e464500d00d4103151080e180c5070844048000444550407440c1c01d406841183c568014034460010402c1c4007110072a000b92038070300911002c9022044d00001462104414000807520000100450381580c4681c41050314200c0b43d1400c002c42d0060030150030000f08807040140c02d108449000003803642034180242403107204009409010440510200c9258640c060281d85110103400b03070301034407910248549030205002c81d43c2c0d00200707188401111101501030a03414141345940d02070000d4a00700115030020f12031103d42e004081060030341900042d03e400c0748109101802c00300c004c4171048025012040581c10035000c1d2841e82e80001c1c0e01c505c2e1480a1a0040940d500c03410315030300e044100e40d940341e00300c42041550300600c42013407011480f0741e0080d0014407182d220 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695417491 1250 695416241 695416279
    0x90f0b15040e0d3501080d030c140d02040e0c030f151c0501021b030d060609050a0522051504050112020f122d0105090601061e03060b18 60
    0x3010556202540188841502c2e01c0c1c0103e09144004070340612420b450107842000b0380a0b0309104c0401030050b44410b00401c800c1c4800c01208a030f8213403601d8240000c070640c034005081c80100c00545c20486070003113000d070300103003195041d01c00520007490142d00a041c04540e00b985544207451141a100c50140000d81342800d4410317405103002c2c0070b080302c031a44850b40105107001c82d004404a40301c2d50208601c01880d4410786000d050040894040c0d80e480c04406200070846100d41d000c0c03c18032049035002c01140da640c020601c201e0344140c2d280344107221200d1041109440499500e0f040903d81800d001e0b111205441c04005003c0685007000382c1d1741c0380c00380f20540a4100b54001c1d80845080f810050a0411070140b1643e0703560038040313800b440c0c0c000c4092915080b4038074031400000e00348410590300c06c00c03d0103001e80003500000600915418004000c104910050660b0010441c17543c007200b030715100f035110000400c80f07003003400e07201c00c490580120314002050350180b20792070452100c046922 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695418741 1250 695417491 695417501
    0x70c060612030e010e10050903030d0c181710050a1503030e01260a0921020303060a06050c070311010e0618030d0801141309120201090506010812040302060d090f0b1504 74
    0x3c00400e20200c211b4420320448255102404158050009014550083c1100d0203402c40c581e440342c443c90300301968402605a103513a20362003820307071101c08540c0310b1014102044155085450340c1d00820395030343d016103a001402a81810701d1090391400800005d040d440124282d008100b6030759450404c002c40304400320315132700810724a0440071002c0850203000c01031b400840754500c42c5072011000380c2c01008480001842c00814400b5070800401c1280620345410007401510040c101581041c0318100c00554841450000800008850b04403584507801141a25009039000301460742c2d400300e0000c2e03a00b001603400461400380c414038900e0ba1896008020807416510341e200101d210150900070400c0400106440d201d40fa99200700300ea0205400034840d03000c480b403e4002055500003490803500d80300c0705038450034164122503015030984005404a404503a011207080d501e410540f000e92000300130303d03040203054950040d600130801543c03924180c0b096000d034402c1043c0d4075400e000c2c002a10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695419991 1250 695418741 695418767
    0x50a020a051812070603140a0c0c030f05040b040611010b0405041205071a04080a11240c09030118050f0d1205040f1502091f0512070c060612030e01 65
    0x2070040c810345107844203118441c1072010b001010310009401c0091524103011071900414006522201001c00e04200c0001c2d107038004075040d40401020308210001824000080340c0141000400d181201c407244c1704070280d501808009080907900c0e540c800c002b8001c40c3d0821500d41c40340d400d11500c5030452610b0f2081c2481150001c66200842c05051130071a407590080204903100c01825000601c41c2c0c0702c070b6103594400d81c49040c80a40d40c0000b8540500780c40f103c5482400a580f0407006007041c4000d1012404402040c24070f039513a16262800c41a80c1303409581c03050b54142d8030f42074500290340d40032018081c0d0f040c000c8054a00710101192110749580ba09007400300412201d6481902501c040d50019620500902d0b1400d603d8282e40d07204141c2485400e0300148481d004a0780e45c00f1858010600e00540e50395209450381d0521907030000d003240c00390007a4808049540000200304600544c0c0310105260302c02c0040010780e03140e8031001004a01500241c4c00a40400c13550201940500c030401054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695421241 1250 695419991 695419997
    0xf0c120105071e050706020316031503050705040221040b100602031207050a02010b15030105130905060403030c14030112030905010507111c170a0809160603050402062704050a020a 79
    0x30300f5030344000014000b1550a50300030050708020aa0106590303201540c0281010f07140010324021800c8002c0a4039030400070a0b86c0300c4040641000007410015a01c400c41d8420b0310b001d0b8850094081b64100c141184450301d14680001c400c00c0104276030301e2002d0f0b1241c000151078914040e21260201e07940c1c0030700040008444815400308143d50301640246c0001e01c01480049440c0d009100481d8400ca401c6d1500c4141100c00b03c0144964546600c1010b00700c0c4900b04100400035907602d60b543d440602400103030034542d892198411a510880d448528202d54034100c40e920350303403101c208884002d2903030160000341160b0804203580d0300c81d00846403d96044400051960103840c1002100e80300200e0226412042c01544000070b007401045440c1700401010b41c98464407030b00c41c0074100c9480280000e80c1078106240c0b45422200801c0700c0c5040c0c613020300c0c0003c1c544c3e86034400310f9800d20404109484d1100e0200d040c0740e0ba080507040012004105035001d01042d1104455a02139000d115030301c8000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695422491 1250 695421241 695421257
    0x160206060d080c0f0a1403070f080c010b09041202070f0803030f070306170c1f0c1106070209041b0e0714030a0f0207080d05010b0f04050f030a050f0c12010507 70
    0x12441c291885424603409818101e241032841e00f09a842e0400e655919803590b0010201103050110a444086680c01484003841c604030982d500d22a04100e24900280310b202d0210310348070a89403d500001c03510300041c1c803042d654202420081e102100501d441801442805c81c046a84882d05006404460699004600716141d850140000301401270089042550f81d0000069003030056004040d510045005082c0034a90303201803140316008224520407804c0c255041414981d0701c00d020101e20b58201c1484001e01040c0340c00182c07140b1914901950050051040c082482200c1581c0c902c0150741003440c240c0380d03a403040150300c050002c80301030b0007103030706e056911200504950040d075020854100020f8100411490b2a0032608000d0040d00d04000c00310700819000701600c103281c050040da96290303003802040d0942d0305662040d03004090003005225003100b02c9032420404400d08560050a8608408104070702d5a61081080303407291142e8048440e00c042c0c40341c180300d2180545801d81d640c1807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695423741 1250 695422491 695422501
    0x415060906051c0218130308220f0c0b04030c05040f11090402070303151d010807050604090b0f040504060b0301060b0909040209060111073c18020705070f03030206160206 75
    0x208070f40f1038110a80e00140090a003081422031840a644207440e03180720540f80c8001410001c0084000a1203049200c0004844042c0c8840111410400ca54000b000c08144890b03860a003084030400e9000d44400103000c6008810000d4000c10403082d1041030700e01700100c01e110104401a1181800b9000301c3e443d0070000c07800c0c20f007401d0f001462251301a040108042a412600402504440e8400d400e5050b0201d04206621121040c0c5d43c010b00041c0d00620909043c040001c8451060388035010515a98001405654841d840d40c4040504020002c0010741703402d081802c050417904e18210320070751915002060787d0070230000761120200c000c0c0c402c14480d41c465081c0000300303c001d08104d040c00050204000c40c500700300540b0000d40b520000d03095004d00d80e012080c185e00d60ba01c51541c40ea00c0400c07080442a20918001030880b8100070105034000d10069248001b44200c581c0680b403070080c4100403648142c03400907002140e100c2d600311142c941d602d140c6416111740342484240180c00c404040b070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695424991 1250 695423741 695423779
    0x230303070803340c03080612060115020c0108010803030c21070c1101031406240307090e0c0306060d1d0102040b040509070e09010909080f0d150807080322030b041506090605 76
    0x40e070b01c47c0d40a0070381040807010003136043c98900c099000388801e818800500400c00e9041c802040c1e015401e003042140c5504200c007168407400024401410848049000802d40409001c1035480c143c82800d21807083c144880001c0101c0f0501c90180c8240d844110403220951091143c802c0c1c11106880c01101074851108000354040b8892940000d40400b0b07040101c6007540400650082c0c1d0b81e03072106036400d8606042035951100c01003a03400c28540c240f0400030184c0303c000071981a4011290009908001380071260054205114444a150310200e80815140c50301002882990401c94003880182d443c681d040f260f00002c0f20a440e000700c420001000085011b401820441d03100300c60f41070074410b424003010400d030040203c108d102a104c00b03004035a804142002d01c0a40b0141c00644003d0741000102562813182161030030f00c0440002c40c5821500d460031880000d10781c00440001c860031f1901303040c003445440410325030b0418034000c00015030a81030300c1110100c1e42d0141c00e41300409449034141c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695426241 1250 695424991 695425007
    0xa0c23060d020903160906060c0b060d020315070306060215010b07031407020411090f0d0b01060e0a0902070b10060207033206040b1b0301230303070803340c03 70
    0x200700360315020310140c0c9a50f80d003886031038110304000c031a00d40c280e45014030380b009407810340c0e000200344500001e038400490080071943d0380c0240c040d121070111321661720100780b03000c01c1c07403000c600c2c030281441c24001e0351030b07040d001740d4100e80050b402c5403101c0c840034000c1d59200c8400c1c0f15843ca045010000000080d006200703010490160380220703400d220300d60f00498242c90384290000fa04000008000340c0c1c5182003000f2545614059811000217078460351881c2074104180100c1c400e020403500c010300140e0741c4c042d2001c003030440c82e0811340d11840d142c030b0454142c240c25204158035420300503002c03440718800110503084a0304440200d10708640c00a0030301300400420b000c0d1160a40d00904001c10302420049940110f105c1d8290704200d18000c406d00c9006200000c01240c034070003c100402c440308c500c12800030a84480d884081c0b0040042c00003a14510501c0c070000e08481000c0104401400301441d0000c020251607684a010107180c0c1c0a01c01c14071f40c03030010704046908207920101180c032030004c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695427491 1250 695426241 695426257
    0x30f0e0105060303091012050705070201030e0307020d0b190905030406020c011701060509010507120f3002030a02090a060305040c05060a1b080412050304090608070f031205090a03050a0c2306 84
    0x20b0600f944a04807c1c0d03041e01d508840120124030006210001c551380351150f642462041c40145090442650000320000e64419001e0300045a1a0119040400701683e2100d8861400b800f08024103c52800f070740c8903001031146401502509000c2583d42d40110715004072051640041455682000c00035a601d400c8090f55504002090118100041e040941c4600003145600c0f000a984c1e801c020051055100c000c207a0240202c4007165106907120790240390640c1240e03400540c91390303900301191009002e100b250551050031220001401e0303806a0040e4080c074002c10b40b041003551074005000c110301c103007111000003641c4414441ca1030610600507440c0140700b003028900d0f00360b55010070700703402010b0344040c0c40d950400181009111010300c1402c00404243c401303884050f00d0040d5403c61020f503440003034840c200314410070f0350151141044404072800148a05481d544905200c0d5a42c40313640011541440e0141d00070860200742020205050b29030309074005000429002e04c00e140e044149 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695428741 1250 695427491 695427497
    0xf0f030406061d100b0c0703080c2805010c08070509101e0203090a080a0201090501081e0c0301180b100c0c170604150b010f030207080c010c030f0e01050603030910 72
    0x5404151642403210514800100701011211400d01c0e44503c0407814080e400341049145c1040340e80c840040c0429031600312500710703a00340e40790300c8068201d5041403003070f042e18200c1210b1400b55902c02c00481c0e80c2141001d0080303000f000090351465094078025030a44080000c100c09100b030848615007166800b8280030145481d003040410400b109004801d104220405030b0804107216040c9c1c10b01d55105001061044024000d4000b55000030f00405154000c03030303041280e5440002c6410100e11018400c43c04000d281c01c000e45484040d10400790002c1c092040303107966844a490824609001c0c0c1c5182500c000d005415510701c0c1c43d0300341d0b03114181c0d1001f2548840040f00c000307002001d28045150703464124001e4541c0c0d1a1070302d018144810340086803890310b450110060341f142d910103403c50702c0c6451030500681d1501207040100035030082c0d050701446036003460101c64520364507401c41c41c50030086005c01c0c0691001c0c40d44041c242c80003154005d070558070502c504005450500088014090300341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695429991 1250 695428741 695428751
    0x501230f040317180409030c02120717060618071e0801030303111305012601031110020a0c050f1c120e06160209071106010e0106020d09060503130503090a0303230f0f030406 76
    0x1a001c0ac00703400c1c550034001da80d44c0080b0170421004100070418150440b210003e02414a020f80c0024290032450240c0c20304c00030000c000400302405910801c4040032010110700d030000c02200014610142400200d002900384600b60218503030340790170790713280d5103116158000e82814003004680781c001801e40301028841c10480c1c0b000e0a980d000c01940a5030107a004488005d045005102060189660301011580591113403030101d804204c1d03c8056502c03c1364003402094220001911102600d6102c1c44001441c400f0307081000103a00c50800083d0854855040d488030110400406005030f2401490a1010852080040c5840290340b079002845042c01030445045031900c0e0301e86603098018044440304c0c10300620a81e601040440d0200007503280c2001f480b410080001d00a001c040d040c65075400e02d03645201c041107000e006407080400e0282c4000004ea0750303401c000b04441c0d4030381d50080c0e14079400c4070018100c000d84421680d0101d0000380d1280303046112820214554001407064508070750318 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695431241 1250 695429991 695429993
    0x7020c1210060902070512071a09030d0e0102120919030e0a03051c080a0b102019200105030f130506190f05010501090501230f040317180409030c 64
    0x80c461003003d80300c02c0000503191130043c50091301c1e00e0100c00c01e03076054a000b0702c01c5200060440d140c0c81da880444203c50b0310b89132900030300f10b4074500500380302c145c040b0300340800f9102042055016240c21401d18440d8030142d20340c000210385030748460007580c2c48400e0030100003010900503002100f001034080c0c4402d03141980c81e02c030b050a0101c017641504106001c445003100300c170740c0411500e070042c0d2084801c024201c4500700160354840c03001c0914090140c09038601030b000d9070300032074080300400301820b0742da12031141e400200c1220a10344044540395a4000140a104220f441d0071201c454180c4401d031540c0c40d04880386030201402401045444d51040c08000060750074000030b8041e4820100d880225017906061200391a003050040b2881031a110042100340ea00034070b6003044900c2030805402d0003040603030024070f107010350f2412083d008000034201e901da4507440040007200c5c09403d900308000c02c1803c04201c2071107894110120200c6421400380070341741aa0102644500c81d0506010040b11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695432491 1250 695431241 695431273
    0x20c1f110f07080705100e09060d1103331b2b090b0c070203060a1503060e03030702010e030a080105011d180115050c0a0605060406050d050102040f060807020c12 71
    0xa542003c0c0c0035402c0038208028608000f45201101480c03800c0032204801140c0200d0031035207004000512a05040000001380410702c15200c5d1040d10140503030300c0c441017650206852002105001045402c4107450041b010707000750011740507402000007541110b040304240300c004d400c5a1001c4050340c03280d8100c1030706001c00c03801d035414a5502081c00300d81e202090a000303144ca4002040095503610800444005a41c00329605034095452900018408080c0d5600f204820f0303140c00041009240c401d840306240c9000000e07610884140d03009000003074041c1110b5440740503c401820105000c0030040c8017a42c05080300d00a000e0105c0c1040303005610201c00904101d030b6000b04401688003050040c0310003582d6400305d10f1700303400754100b407440c02c000312050715039990920101600b20f40e500c2c80450066660764010304010301c00208040034583e454100715000303511502c26003400310300243c000135006c4e0140d600941b1a039a03980250a008140c0424001a440905104280c1c1c0c0200d048200d01c2c162 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695433741 1250 695432491 695432503
    0x90a0f08010501050d031b031b050a02031b0a150315121b0f03060902060909010e18070b0702060c1606020a02040e07050d080a170c0901020c1f110f 65
    0x160115044a6145001030190840d101078000ca4094070211100002203030b082042e90501c04d10000804012a40d1400c08503052510454041082c0d10900c03480f0007404000540c01d01e004e4001c80903190740340307548984104002c08904045030484156030f0104043e00c2255090702c2c03280306c1c504001c0b40081004000000c01c45040d000b8000000700f0010340760a000040220340042c0c0312450b40007481c1c80c03c0c1103084824022502c0001d00d4903444101401c01c5480f080165054000060042c003515611070b2982c101880d01101d90907005041082c0f1903446540c0011300703c045400300b0800c540703400d4070742d003e0051035448101520f845102e0340d0403041d030390544010010700400d0154084c0c13000780007500c100030941ea22a4110032155110003030038071403940e5038404038071415030011040e030340d4440300c1200f83c03202e0f40c0090b035006001294404114144500b08000c1542c644241c1c2600c12584190b001c021108408600884419030b450340b6040759140951080c00c0c00e011040111440410290036007440c1c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695434991 1250 695433741 695433749
    0x9031c0c02131b0903150b190608011a1219021e04090c1416020d0b011d06011110020a09030203160617090c06030a020729070c020112050903090a 64
    0x56034512403002c00360f03c0c104500a5a042c03600e0460182c0f403440d10303081e185801d10401030a0060b901d0400e00d606a030b40341050b204100322000d66074000360380c80402a003110024801c030031044018808000c001d9003854100c1e80c1c040c1d00981c0b1411191a2441000b032180a22b081d50b0308800c0c3e0800070110000c10740e445030190115006019a03841d800e120740074003030700e14a1004005000001c15543e106110403410f0758081452010310304036042180c00060b41c00d000303405020300782d150304000200740e420400c0c00d45401c5c0301e403041c90104151203040044403002171084035000d1980000c0d1040641d5102070300205644d840a00d4441c0701c003034a0b0b80000781018140a001822400c405004011968001c1451400f56600400d051010310340303892280d841d100144111403040c080000010719040c41541036a188542280c20954070200803041d9100301010072918110030000c8000007441d051044070359030042c607030694036100e5100c82d80c400c4c4030141c08003a000002c0c5000c00c0c840b60515440d8182128018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695436241 1250 695434991 695435029
    0xd020c010b010e041401050f0301090b070305160903020d140705270f01050a060f3501051e090c0c0a0803160203040e0f10031b05090105040209031c0c02 67
    0x7000000001d4215903000d025603000d1420182d42490250349000c5943c1100c2003903030892a5601d40d200000d00400f8050320081020700030100b442091581a40b0203445020b06049040c003825070350b20141c640030028400258000c010f5680100040c04c0013503490300c1e01d2034010494a0144e19080064034105c800d0784111100c2219600188402120b000c0098202414016136105035050902042420036079000b041c09104010110841151003102c00c2001000c810080c1084882590800c640310410b8480b90264890720310000f03e45840d00c2c41d82e81c22002c01c40c41d041e01c40d900c514420b01c205804014003038004001c3c240115084014141701000300c0500c80d80c0c0b81640c92403c2d01c070f13046c0d41e42d000e02d04003c00c6500030b000510001c00440e40d11a041018544010521f550305007041c8128840e5400040c4090344841d406079910030826915000d40b04120350f003040b40c1c0c0e2158140b00c120700910b1160b0341c3c5580a140c08110501c1520f454403242c00581c540264541040d0b00420ba400003903500000d44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695437491 1250 695436241 695436251
    0x9020904050a05150105181e18091b011107030f0c120f230f07090c081003080a0c06111206060309070e0c041208030106020729030a020d020c01 63
    0x140c03805200d100d07403103007611204110780d04003d0144000107584650180c1804400030702e524204002e18140804210000c0c200c2c0c980b88078070111483c1d007001b1007500034042c1640e8120b2600c44004d1200e010f125091104c010401041c510b54030800070a18030b0fa00078140801d80042d1452050f0510200300503600980c1d00a50042e030500e0321303030300c038075821340c031800242480d140450002130121b00421070701074000750714144129100b80d001c0001c045111840c0131038420705051241c01030002c00c50004440030a40208035542034000140c46045040b6907201e842d007800c14003400020207080107440e00700a80c2c0f5140d0161003103551060115410380c1000c2c294035001165003600359000400c1603500043c00e40301da90171030400c25143d540e511904e0085064004032800002d5500036a24203a4005001c088a01403000d405810614151340c001e01031480140900400410824503240c5120f0445079659104010100e0b40e4604c6907450300050a4000180d8080000c0c11406e2040e00180000342c03641c400003d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695438741 1250 695437491 695437507
    0x20c0703110303030f040b040602040902070f030905010c0201051603020c03160e010902180409140a06050f01050d05060a0218041a090708091b030a0804120507230f04060f0902 77
    0x440d03400c0c000551840b030383c0100100b0a10a10b801e582030341165215101c59103070384483c03800b540030f40619005941c41902c085891700070b0140807060f0032200b60013511403c00c601d84440045404c0301d107121300030380070410400100f050008000c00741511240284180d07110036940c000001e0a1504184401c4120f0380c1401052007041034200d051801002501c0c4214509601200d104414400043e0880d2082ea600d2481c4800d001c0c10200d0055501e031100c0a4a40c102000d151880c010710068801d440c000510300000f080d60b003088680840c43d250450014944d9565442c0c00e41c0c0a90300820381900282544000e003036841d1154040c0e081d0741c041200d0482661000c041c14013204007001001c41c410011140103110603103002241c400021a10502441c08080841010a11b050303c14500280a072600107800500800e94000c2984154403031070640b079000303645464800001542c00b204209000000d00031050703900d01a07460f250440f00240c40455010f54404c5455080b101d10f1780060545600010325003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695439991 1250 695438741 695438753
    0xe0c100c08093c10030b0a081e070e0601020a14010b06030a051915061b0b0c0a1b020f010e0d0c030819051c232503050601171306020c0703 61
    0xa10031402500191250f1080d100000b0300c50100c18180c40d09142da12200b10004d44c5990283c85d01500018088030680700d0303000c8210400310109480d01026002c1d10902140d0140441a0907006500c16402031581d000c580d210b900c60060382040d40b914541d81d030f086e21180c0f510b0340f001440c031403054004001030350310307000042c1c503c410604030302c0303201203480c0c200e0001c00010300c100c1c070005550152602202c3c280e1001c04e41000720b1901380000d41011040c0c820400098140402422110499603d8a90703640709100e81c590035107030b5454000c1d880359a000308040745501c10030300c11614003030040c4078181c00007041e1201020381c49282c209851403040041c18040000c40641c2c030f10060b1456180841c82c0101032046a010301113008080c1c10705945910803004011418000002900006c0ba44025103050090403404046000c0392074403c88807054014034042c600910642d40b0070768041c0c5407840a00349c800340000710305400401150500c4034844414000c02d0726407010b05241c3c500100201001c5045003414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695441241 1250 695439991 695440069
    0x31201091a12060406020310080106090f0c02070308042907050f0d050a120f09051212060d12030f1104061107050a03050709020702030a240e0c100c0809 67
    0x40c0502203840b0040b4090b0400980c45501075008400103071682c55000b40d510941d2055402402c6030344c28503c1c04904022a9480110145201801040044462102a03031a04050312010300400400c0c08100248100c24180da4400c24448045d20760081c603014072401d0640284034203440da41d10010524006003c200581c01702040319080060900600e2a4024030140400c040c00d224580c4803c02c0c20030040340b64020000cc07507400010344000b82c2ea0042c0c54140c03034021000c009503840700d50020481508003418121086030300700142005000c0410b0040d40a4000300510a0001c0d0f980c4206219920040000d80060512541e400805002c1d81c03201d01d2030a951b90300250701c0780000720f80c104001100003401204588a05001603101c4000380000303800c080191030081c00c1008007020482c8000310b031225144201c01646810001c11a40034071966980718410a01500001d144031660340c0680100804916035200d810314502e480f0307000011400107180d80001480d07010324002c4101c0382d00b101d0703200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695442491 1250 695441241 695441291
    0x20a050c12031909061404030f1d06070201110c0a14010305060306060303070f03091d0712060806070c11060d020405011205040c0506070f05011118030f0304030305030903120109 78
    0x10040c107508004000f985400b9080010144003590741e5100d204003c03003900214001803507402042c031a440c003801e010748400e00c1c041c000380001d59040103010796045c624040c0c2450080c003414075810100540d00540310f5512424140d249485000d0303443c583e50751081400406001e9010040c5500305681e400901903e0f4042c2044e071194000204100040d24008103843c2480d030030844000d112130070781c20262061411608032021801002050450b0039008656082c090107495840d80c2013082c10700c4145e0100c032598021941103401481c082800349119518040900340140103034240d46011000040c9140e0002001e5800307070f60007103070401080da045420740c017641015410900443c5001c1ea1743d10002c08090103903901c48c030408108403062001c2c0b8075901c40c1c5568084000c200c0031080c9403016987c2d42101e0203803a030000000740b20810a06001c10040320b518280801181001d043d0f03034003a00c0c150802000c0c010188000d014040c8000403070380c1024001d10107c403000a065003001c2407068050b581c011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695443741 1250 695442491 695442523
    0xc010e0d020607060908192f060703020a09080709050916030b010b1b19051e100b120601060f090e040f020d060f090506060a080c0105031b0d020a050c 66
    0x20800c016031035050465882ca54816800103031207481c1c3c50140044d010303031072101701201d8846440c991301a40202a503007d400c884003943c2c000c0540c084035034400070803410025206070400408504600d000e90003400d4148510f040071081c880d00c600c002c5151002d11381c8a0304059441d01c003880380140090210882c406522200a101b882c00e6858402c00044188600030800e03170000781502617864940944602018510103455194426864000c9919840c00c000d8400d80075112003052118440d40d120400003840a01620008203009001001820800d0305103030414826000040d07900c1c0140200307800b03841c1c5921500c0c1e4981992200901410454100404411001041c403010601e0040c186600d15411160040c3c4151145040d40c083e05d040c0350f002000c80e04080000e0104400411124441d620a9540c80c40155849031039941c0c0700d205203400c0d400319a041002c40d20900c601e000c50724404540c0f0036143d01e4801d14081c6401264891085080020400b0031009140070003845008940913208d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695444991 1250 695443741 695443759
    0x160e150720090105180a14090c120c0d1e0203061e01050a050a050603061201060b070308100f03020622090f0f0504032c04020a0503040c0602010c17180601080c010e 72
    0x11021030304aa9003944103914100100700040c1c0d86c40010b0304400d030710003e400e00c4039100d13080c140d51040c0d40729031510040d48982c440041c0c001080900294103194502c0041c010b043d806901c0d03c4410013074060030700390140d9000d0340307003480c0c0580c9041041c580103413440c24001d040d854641814034088401a000203200e61340e010010043d65903035100346070943d01e0441c1c00d41c3d541d4443c2ca00040210010309a000019403d21000280c410f083c0c130b0180032218000d0b1103404003070717603042c09001100d40709004603006006542800d0000d42011405002d00d800c901c1001c6142404e2030008280b5014950300492495854a1a40d500e2a4642c000c00400c2c640c210818041814503030380191800c440750016000400485032002c0000c1604500d800c600036001c0c0c000c541d152010480241154802c41e0700350744210b524031000440c42e20500c0f582e241407800b40e40da105044000c03102080b903800081c00a000d4026464180110090b0601501d402040c2e624001d1001107442c034005030041025020340d503c40d01e148 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695446241 1250 695444991 695444999
    0xb0f100f060525020307080106050a0501091508090a0515060a050306090d030c02010902060705030912030a0c0314091923240408060403170f160e1507200901 69
    0xb0550700e81c01009280008180b4000200061074125940042d501d4850240c00151422040d4070000540d641560500d0001d6240d42c01559001d030f1301d1155601c0e01400003c070f07548480c131560b80e41c0d800c4040c240c1170300c9160080e03454442c82c00b54007520a0b401400e0350002d001c03161070461026002814282d014100c5850720842040c0c60781150007000c4145600d805550582900c03e41c080d001e40d40e070051181d510740c8044c0c14610390701d80105180d94041c120070051000040e4002040c1c1e200c10b400d6554240e4000e10075070342147d50000422003030240c0e0105000c6030a05030344108010300f4040e00b1304280b10a891904041d4012403e1101e401d140407071000000042c291142c10100c4d100d9078190030344022404003066007000c10300c190f40c03100303105004980600040503401203881040c80500103000c180b6807a55100351483c1e41c0151018030300071445005504245019581c5103e0800c0700818004e50603450120110050380000421626030080b4000445d90300404104401c03202015a81c410300b640c14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695447491 1250 695446241 695446247
    0x171006091406010f0e0409030201060e07110304060c1b091b030e25150c140d0905010c050c04060603270c170102090607060b120a1e0f0b0f100f06 64
    0x2d801141003020b803414082c8818014480a4a4000b0142c001c001c004108c3c2402030080049005503a190f200190220302d00520405081034000842e201452034503103000f034144c8201502c0c0700110b0b4800010010340b42c4120010000d40018070740c02c04080383c5050307a04071540910158040071801c2c03614000d040040743c1c0c8001003032002442d0071913080c2280c4180c4606000490300a90001d041d200f03d0450458035258003030100d061540c481d041c1c100001c40780b41c000d01c0d00d60b4684180a00007030000354040090b903100b0340240800b41d00840a60741500c0800010405465181c1c10440102e5110f050300f0140e000003801080c02200c40140324003441805a585131083e4405125400c1074074060500c814100c0d02c02c1d8103d0308100e800800503540d802a601d06100034005c980e10051054000d82000722114501046074490190b0007482d40c1d4501955001801c5c0000300d020060352400069802d042c000340072030420600a07982c030f0b1000c03001032a01c0701c08003c4d68809504508041807004d43d0821070560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695448741 1250 695447491 695447531
    0x180e01060507150c020c190e0a05060402221a070203070909020a080a0b0105010801090c0f050f13090506030601060516120e03030a09060207050d0f02040e0717100609 73
    0x14903049075240c2c41d0b42000c1010282c00701000d60182d240c01a0401101d03000204610081803d0f1000e0340e5041d100301424000001310301c1003205049460b400a842074095a01242d40014001c1006042414210b9007000840307101d8004020b0b403842d11801d004010403a4040301c0e0603501d011445150880d1680401e8864040e841a82071468580943c00c04554400100c503000d021440201c0d80b0b0210380c1d00342075058410a00c1107a010418000021034000098080d80890201c42c0e00c0700c0300b10303400020046440b540b0225150100000c14401102906860b032820b1000788000c04000c00e482c10094101820100182e228006022040061104c14400c2c502101111500300f5032408030480c51500994958194100c6240d060000040030350110360469100010390320240e0848210340d44482c00c0c41348001198074084d08102d8000c0ca00b00c01840c09400141c00c00d2864016500d03200c2d0350758501d413040e801c82c0400c00c0b442e0700b041201c410301070b84910070100106410f04007032080710024651f6068600d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695449991 1250 695448741 695448749
    0x601140d02060306150f180109031a04020604090e03030405010b01050a09170102040302100203070b0702070501020c090c0c030304050a120507030801171c05040306051506120709050d0605010303180e01 88
    0x1c00c0220024402c1c2e91495217040c50031207210a560364a2050101d0351840c0d900ca1400f149250b60120501c0016510880c410350a0300c0c3d110040c58800401c680c0400c039400001031040342e001c40d04200100d104052400303810b540055440040d900c034103044c42c00c180ad41c4c4003e560f10b410040c041c800c44144ca5840601c0004035008801e8010030b0344440c02c00680644255080650086d254003100d1240d16400002402e6907030017240ea140082e221100200d071209907034824103005910124031079031207260100c8610303005220021704030710300751805541c031b0b0660704100d4050340c2c690000012a0309000d00100354120540c0d8a2400307a143c0344030790394064084001801b41b01120280c228820404100c10000c4040c6000710f02e004400d1030f005490018000d903c54041101c9440c182030101e001c0403426030500d1545080109111301380030f1043c9135040e4a89006145000300500e00078005140e8a90400c64038000e409003001044a42c11803c015020003000c41c00004c80400d0003400b0020012114040e505403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695451241 1250 695449991 695449999
    0x9120f0a03090203240610051b10111c06060f5f0a05031018020a08010e04020a030b092a0a05060a020a020103112205030601140d02 58
    0x2203814100490080504400080d058070130428016900c1400d145410781004001e071540160b6515903090185050765158204003042050100c184001440c00c00148009021400c8801441c48030002805454140140000d03846002540c040c00070000403200104000c419401d020003894100014210203401d81c60343c00f0095480c40302c89001b0101c240e044000420b80014091740e00b006222810000c02d117201c0015520441c40c0c98241300d19814080c0081812001c0d1181d05080c0c00010503107455000404204400b48021008a12040741d5526681b041240708001178903006119000740c80800e060300070b04500341c0d40d00208030040e61495440801d6a03807210000c00562146c0216928000790030074a040405062030390100340e0500c2c0d040d201d41c040000c0392a5007409030744805002103449040f041d0801600314600803409540030741c001034010360400049510340400341980c0c40d090b1995945000d024441003c0c00c010750318003089500d000d07211030004452103005010010703154191000009000f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695452491 1250 695451241 695451247
    0x209060a03080a0f0e180a1a0303070501020d060f080d110c130b130b0105030c07110d0305030601020601081f0b0406150203070c0b030f0133020f0609120f 68
    0x494480515400c011a8400002519140111400b40140e500100ea00f8002540030396103c62625049011050a040d040040c0c65107880e2550341c0d002034050391800302c8078405103003480d15050310200010801540078000058031800d5082c5140244d500075404518000c0424000f2b0101540108180000216500340b448480b1101d6816509000c40c8019443e800010105c2e04485c0100640052220385412a450385070007840c040c00004485541440c180020300500000306200441001054540d004800030790b00f030808030002036900d40e07504400f20b001540c04014000a9601080014003511504c4003174030300e45660036282e001d410180360100396140c1e240c84c40100b4584407079029102030300c07016000c01c040007010781e406592030384411400c03151100104800120410310303c0603030b805140081c20003040359217000f80c5a03c0006542c84000004a5945101444035510a2005004007059005081d0b5111802c94650601c18028940082030700072030391542e00070031311200326000200e41c0c4a007551 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695453741 1250 695452491 695452501
    0x6041124070c15026702030a09091a01120b030a080d1a030c040b18040c1505030c040909031209051c17040b09030f0d0b1e0d030e040908030f0403021c0c0209 69
    0x300c004515403945c151039258a841c00b100d03800303c02048824001d0b00e552070000c0d640d152003811110414145900448402065a010762250024034503200c50768202041926030303800040c0c10450b4107403003140c040c1400140000b1443d21350060100d20074030702c0721600c244040d100c0421f0315003507400a8103100307503a40c0c3d880c013019580326260b030026440212503851940c0340c18540281f812005018034100403580d2100070755628481d0080300d20490841003041e04041c5410a1340010b0b00b0b0084045040c0541803c2100903075440d4445c1000c15070091005000003c15400581445465809003804114000327019075600710715000601c0d01f065010349890050340c3c4041009003180100c0003070100da100c00241c4002840560781080d00a030390200d13103000c0c4a001c1c154020303460f03640c0c148089030000c070070080e030401080c00b074480c1c000091405000442c02c0c41469403513000703c0c1c0c400c480d024000300d0316409202c00c6c07550400100400018121044410700d0a07030324060041c40900d20004d10441541000070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695454991 1250 695453741 695453893
    0x606030e030903100f230906090a030f0f110d1701080d0818150406020a0e0105040e07140f0406021005010f03050703080c150906041124070c1502 64
    0x4652900b241442c9040c44215905050144007903c0b1f4070300702d00c11000420b42c2138501064035000c003607260310f414062101c049415104001c02d028500b0038000100030f100442d401c02e01101090042513034500c10005140303071f0500403820040c3c00c4510781e40c0c80008406203a03600403284940149035100c503d407051880107000d80c90400c4251003071070b00c80803031024001040801d0300035000010081e01c0741d089103103212004550501480c452060710510303000100b910303507000342c80c002c08030a00c00100030b14041d0008400c2000d58000e60000e0010703800506c004083d100184a41d40c058140c2c1c040142d0f0542c83d54032081c1d681c0045010103070986000082022240004000d181000600e19070001158613100d02240d0310f81404880c142c44480d0000e2010489280c8a03014940d01d441c11401d86104d001c1c80c000034401d507081804121182042018042b614603640c08401c01c50400ea580203000525170401c840409070b08002c078210b0440e00407545100700040100b10ae00c900086021105140241c01d0007103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695456241 1250 695454991 695455001
    0x618290607060605032409192603100f0b04050d200d14012406031109030f0d020d020a0f080703030f060f090e1c110708100606030e030903100f 63
    0x4c950501c40c4406c0d410450305000c43e00300364500301c0c8001e004c130b40d40c0c0c050400c1d4a40322400782c0c0303034501d0591122050000e0628910b04480d00c0500300385003e80c00032840c400421381d0095039102c1c4a007103100401c12900041c80264805802e0307403a03407681081c1c500f40101d201400903880084c4080803460b40300041804990500d01c3c9003500900704001170045040400e44c1c002001c8000c0303015401c20701440158000b0800700f03081183c0401c419040c03945400c50480003030082036000000303d00204031744d00103a03904211901e000188400070308030070f10880d03001030f140110700300c40c070425504030050810200381c4c40307105101c403190080105550340c01036180445c01809680c41c1c407c40e031441c1407008200101181000e8040c4c800051082106110001d1150394404120803041c0c00380007514034a040c1c86104047c9840c010140808641100703882d44005800c140e5070381c11100500380e40311001c02420354140a0f40502980c040051803500d44040c0100c5d840e090040c11451002d500c0f031b005000005069406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695457491 1250 695456241 695456249
    0x608060402010503072a060501050d03120515060d050105100801030b07080a0605040221060a03110d020105090307380d0504033f0c02030307080406020d06182906070606 74
    0x22014030590021010300c80c03d00f84006c1175170040e1808001146504008a90314952034042d203844208001c0c1002003c06460000e0042062107d1500800540d031075040c09030800120344000412990f0400b4140069013031042119000c20120400410118041c50260fa801050929100303e0a03500d07044003030044e00c003d6200c00e401034800542c50360012580f11015042082c1503801548540b100f008003c0c85240314040a81002e2071482d0b0b2103020314040c13013082101481810300320b003058008800241400380c00c0e48500c2221400d90728440d80d5404142445262480a1780004240a0052031411490050640e030000150341c5001040605004500020a800c100580000075411080c02c9810311103200c0c0c0c418180010f0a441c0f041c5448541c05105070f102115070056055945000d41150080300150003510560303820480c3c1907414040c0d014080103800b1500914021f260044260b801700d52148545c0101040741480350000121511940312b2800350840f050394861420f0b0038a100100f28a40c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695458741 1250 695457491 695457527
    0x110c0d03050d05071b05160609050f06090d0804080307060f110702010305041401060b18040c142113020f0906030c01050c1203070309052802060c0a0b04080c070603060806040201050307 81
    0x2840f40400c00c00040ca01d1011110b60900071f9155901e1100303442070b0b1013901880354000300c0c0c8224416942030200c06405201002030400b000c04541b13842d05075942d40542c102031041d401c00039600e806e22801f801101c001d4000c49000700000b03984100850b083c0d0058000083c1095194008181801103800c07601c092070400c030008012969680e2207482070307540034440c1200e40540c00700003404649014411040c103182c1544415400544034801c842c401d0384090203801e90b02c9025203000302c100d03a02018440c03280c50f20400509003201c550040150b022020542103104140c60f0080059036140410680b81040007820b00c151200b403410507c6060100d0520a80d61010f004806c200c40f25515401c1400c4c1c56019000340c8031988607903a500100c11042c68400ca503441141c454140042c108134005200c503000007003c2d41c0c0d90036960b643d003048003003050f08c00303480207240420f03400a8803106000803001410642810007019207007144207034031441c00410180c10300c031010000800e090300580c90304004a40c504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695459991 1250 695458741 695458787
    0xb07030207051b100206040819110706050d050a020910111005090d0818151503060a09033209010504030b040f050d0e0f10090503010606110c0d03050d0507 68
    0x43c0300760404011400544900d6401c0800d0314000e0001c511a406560000c0708549880d040854101c0500003001c3e80d5010404400003e245440080c0948400f8100da903a82982c0c0e61500d0543c03900341d440161482d407203c1d204203c103880f0755070341d4072070030105030f0090a0058003c2a56a205030400c0d030041c1070201070343c5c04c003c200b02d010000030030220710030142c2d03443d5103880703860b203180380c2c02210703607001140340f49500800c100d0703174035103800d204196000844030046103406045001280c1881019244041540d40311a41c035030805400640250b030001e0300741d000e143c0e6510504242004000e00c0215141c40800020325544545d105600b1600910341043c2c60b00141d080a1801c0c0c4e959014240301916140600304000e01010722500c400116400c00906c64035401c01100e04008100501c01403400038882c0010b0000f0301c544080c005c0d04002e00b95a01c60350142c00716040154240a581400759100740c8001c140480001e40000540d421024040000102a910484240c0700b800c4240c11030602c03001c0d10303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 695461241 1250 695459991 695460013
    0xf08101109040c03063614041e020a090f060b0c07030f020a1d090d0512010b16060f02091c170d15170c01020a1e031407050d090f050d0b0703020705 65
    0x203000c0a034000c0007031560464900c03040e46d42074049070304d806803144110361500c0120380480da050b01c24240042d07484070008544103440e40000c3c902800c941c4105030942e210b0056401d030580c03603c22000106021003030b40d450840004180d60f11090907000c002c00150040b13003140f080d511111010b00c00744c807441b9035440d501485010030041070002107800f480746202e0b002c04025401e2180054450300d83c9046103884099082007114025908802000741c4078007020b5248901240041c0200249038010810060392080c000d400e01012121030004401084008400c2d40006002c51b422014580c56408089495a4454082401901c00044840340d080003100011520010701d5641c00208905030040700d011055040c01640c541d541d0316406040d50381803241d07031055280700c4000780f04020300c42d10701490001c0300000c020350b580e005241c050b03a159000580544001c0c0d04141080e01500c004601c50f171086207801c0011303404c0807040c1d00c01049104280007107030205021741c0664401c1e991000581d4840b001c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 695462491 1250 695461241 695461289
    0x170c04020d0e060c07080403060e010f0c030b010e060408100c180312030e0c0a030b13060608070f1d04170403020913060c050c060f06190f08101109040c0306 69
    0x1040c41020031409500081384031020844220f448055101036803034103007403850301c03520003c004c3c44441420319529541c210701d2b40c0341544503040307640702580c800141040400303000403c0d0070b081c51203440c00390b102040280184980001d01c00350308401c44e44042074109484000700c1d055010889007588540e400c8101004200105010341e88586060754200001d124001da031554800c01c16820343d8100514880510126491b030380a01d600080038803101d9084105507440b02c003200c071207500400d0203820008060181440c0303221140c0c000d00030785c0300c2d0118400d234803a00603a01c28005400200445032920266044010302d401b41c400a5030010145495442c100036020303c071900002007210741c18170302540107064134000c0b8242d4017410344020040803d96a00720844908034009490380394841d8600d00030b0040012544c4051025141c0241110210f0f880c01c00482d00e402103e03022400c1c81400c20662058000c20501541c0c8401c03011907020901e41ca5854095001380184e811542020161a007001080b40c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 695463741 1250 695462491 695462501
    0x30f070210090c1707050a06210207032705031203010e090a02090c0a03110a21051302010e0d05120c0c01031b0f09080d0201150801150b03100b071202060f06010801170c04020d 77
    0x109c0844034440c841c40d101c080e004a205118005012806031104807086d810100503d2058081c000c541040b480c3c0c4840001e454854042d107407440c0104008018020919940c04044d0840440d00042c08540039990003d140c0c004001e214403890000811003a01c1c451080e0030107060815203000f065914607160f40001d00079450b407240c00e10058071580c180c2014a03010b114142c41006041c80958445030706500454400101800d1254480d08606000d00458414041152030991013011250b41d0082c14a00904210680c14103c0c14103103031221110052540082002c004401c601c1e00900b88130040707109440010f01c0341c025040610525002c03141c03050b0150302c24021000e004010244241c1c0d1001c2450076500683c050360000f10401c5010008000f1941c09141c203c500419844203050700c1b01c2064505401081003603c0c44000001d80c85ca100790103100047c0c11036882d10314000145000c0c40043c02010061184d0a030314480d17440c280c065481c05003e9410b40c40c0e801401555100b28108422001e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 695464991 1250 695463741 695463767
    0x240409060e180c01030f1e0b0a0e0907140420040f0b09031e10021201090507030b0f1c020d050f0d051e0f0f030f070210090c1707050a06 60
    0x500c0050219050280004080190800c4100140144a843d400450103046d80003c2c50b05080c1e11030f01200d281840300c64034074610341641c1c040007800d000c5010810088007420742c0328402034002034060002e0098041088429569004803100c01c200507100854010010000c2d040d054400701c1d03214800000540000704101c8150000e45040d154842d07040000510850003140d0349940540394071502208038030120603071814200c0030b503041001520302e80c5040c0e070b004c0050048440704100050000e002140300e0302d600311030140f07010840d5014a501086070b00341c18541300e038400d48120501c0428403400d50101e901a560261a03084507044903e4425a600030102c500d03844c0380241000768880310304c42d100780d40907484041d88803206082d0203c41000d407039015402c1c02c6c01e100820051030b11a883d03a000198050740c004a110000380c034240344002e0070561030301c2c0010340b0603007450301c200301142c40c550002d03003540c188400301d9002071280820185443c406901c0940c01c01035946000034502e400c056056410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 695466241 1250 695464991 695465009
    0x20120060106080a0b09010315060e07081605040b0a12200309010b010c0b130302012d050109050c070209130615141c080a09090f0614040506030303040224040906 71
    0x10751034540f1513609a03003c0d101c2c2182c0125141004101060903499405a2034181d80d00c0055081e8407040036110803130b000ca4044012400300c40502150240e841820714941d081440c0040c10706083c05034290582c0714180b2080204903204c054540a2205940035181201401c122400c0460a0300001c54503a00f045400011700e500e80020418154021404d18070407079840340b0200c80c260b8540402e09015003c40e0000d82c1150b50b6101a0b81d4510051043c0785540382490500a681d541c034001c2c04015030b41c050300040182030411050203000c0c0088030590305a640d0446400d05181d98050114980307074203504000e05038904000615400041404800e400d40f2701088119402d012400140300841c581e842c01c0d1201e0811902d80c00010605050140c2509419442c080141715a5104d040c42952102605c0c1340c0d00f1039649404100c400c054422640a280701500d06200c07600c1c11000081c2c4034040240084c0c06010389440b1641000b0480e0b49030a040c00d4102c034104e49547c3c40d820703200003c0c5254040c3d1560 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 695467491 1250 695466241 695466257
    0x90318140a0e0f0f041109010311040510050306070e060702060d05011802040b0f0c010b120f010e160e04080715020a090806060306280207060b040501061e0c020120060106 75
    0x104042c022401846000c2c55484180d82d0349807a80b405408100041080d500294680744044943d600d040030a03000318000d0181d00c0240002d0001c00044800c0075010700202e1401202c1086140c4001c07031803e900c4003090400c0c10561a0903004504c41340b1515038000d50000000449210010290b4010b6050301e14a0381940704581d00007032140704a10a0b40118441040240005486020f8000080661040040010580150b1080410600004001300040d15046820b01708001c400920908800302099002420130000d0301d00794080980310fa0041c5c030740440312400003400740900201107642c2c090744005482402440c041000303000303400c003003010400580d43c1c1d00d000800160024990340606001009411192109221940020001341c915010722020440c500e00c04500361019120f294010720010a607003508404100881e00160010424003c1003d030b58022502c605241c0c0007030000d24109100300080d18001610115259400b10000414103c0d181e2003200d000300b2024100d900503111050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 695468741 1250 695467491 695467499
    0x60e1e0c031515031603050a09030c080d11270405150f030106120623070f080606090a27020f0a05091f1106010b04030312090318140a 59
    0x1114a40545028032140303018004105411503001144015100080451108078141c5405080c950000c54800c00c1592000400041d082d0301802629030013010300784204070341c004030754024205a00343c510161651802103048001084c0390303481201038211519009890b4804032802404011003001e0703110100192516602890034035000d418003403245075400104000c5040148004150308800d400d5040d03403100d03c0021103465400025074218040c050115501d502000d02c0e00806407040260f4204900c0b403000c2207402540404040003c01840c500000541c0303610001a0b4107000320868254080580100010401c6c0c502e00c5014070301500407007401840c1a00345000d000ca005091601000900411802021610400050bc1a04401464210f1404010070002c2072038201c2741c920b07008103401c0d000b075544600d01000082d00400104c4044c0b45040d0840d90020102207224501c55042c0d600c55010404140c0101c450607018032144100380b0020703a5440d100c00000e84030300e411500500c02410045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 695469991 1250 695468741 695468791
    0x6030f0f1a010515092b02032404030c0c03021c03030b01020f0d121d0601051813020f120607020709111809040206190203030103030e0303071106030c0706060e 70
    0x281241c1c0024a864010003105010007003a85c084c0f8400d9520000380b010501c80018005000054002e00341e80f031420381c0f40144181450103061800c00311100604c500501e030a00c080c6070b43d880d4015414604070b05115190302d80405801d070141c00095004185900700110764039201040da001038007a59050101c2c03000c000c0107a80307500d00c00c82c83d01100d401c008508410740f0701901602041c605a440c0c0007030808078103a070890500040b032002204907003000004110b41d1600103100384000303e40204070038484c244003200b010340b20f80c1a84007c0c011814181d0410003646e07050b0042030103c1c0031005417100781c41c2c00308000352102c0a9000302c002c00f0f031030b01d0001035032651180c00366228050014640703c880a038030340420880303200c014002c80c1c2c0720b10100300305205005030000c000608111600190348a505515002d0040000d03900e400e4000c7d032040c41104086855090b08007440401a10000e50f2a210f41509071414800c5100103000c80b0304103940080c2c081c82100c013651265044001c0d20a00e4880103100c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 695471241 1250 695469991 695470043
    0x100209060702062d1c0c0e04050c09060d020a02160b0d360c08070b1c1d0303010609050105030c09040e01110a170105010f02030301140d0605070203120f06060406110106030f0f 77
    0x98000541f0608000035905080e030040ea0440c129041140c202824840021000da0201c15110301054001c9030901d038560301000b0884101c5078420441400d1400d08604414501402d01d03982016500e6441d02494080d10320600d8901c8545600307002c00c40e2040a400200907000d502d0122407103c0344040001c0d400001260700e8081d58402140c051030100d151185014640c14106000181c030350318005107010740309032500803100c00003a101a517140d40c034049010b006807165620a6050110400800050040841c01c81d01c2440b4200c90000308182d034601040c1c0103040707040b4140f00c1000005182040284c111941d81c50052440c801d4806aa803100011101c031a08184048096442400180941c210390442c41c0365a56014080e12200042d0781c988805907917007a0341030307409a080060300000031a0f580100a5000310045202c000da41428004503440d8071403845084100605003505482d04e000a40128000f580c001407241c2145419080c284060690300c1c0080380c41d038422101c2051114110201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 695472491 1250 695471241 695471261
    0x80a08061504081203102402100902061605070b0f040f05030c0906120f030a0806030d020d02191104141f05030a08070206190809100209060702062d1c 66
    0x103403e4451008042c2804d903000034141c481520212080411404d8010317040c45c2c0c40c01c1e68986041031240a002000e4180610b40d91201242030400c0c44203c05610345d042140d0350b01d080d603510031440d03003200e0030002d06041054004051440300040c41c0105821920701500503101211035426501e81e44908040e9104039401c3c4c1c25412802c42c600150b0300e403500700820400307101820169080002e4040000741154401601600031038108400d0280d14102000404d441211394001407046025210020755260504005e550104c848089907000700b043c807075580140008007901c00d210740b0034400860700031b17004100d8911140310030500825110303403030100854086400290140409002036201c8142503485498280d070025000c002c2002d080c28098802c0c02155a66601d01c00607080806c20103082c03042c0c50412100d014011300072010250398100c12036001c103030b04a880640d10000c000800c07903040700d0080b0403440c54598036038075260441c600004140c840801c2421131000e100e0720043d07004032074030090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 695473741 1250 695472491 695472493
    0x2011d010c030b09190c14132c0c0d061805060301181109060d1e11030f150402010e0603310302060a0903110a05070f0803040b0f07020d080a0806150408 67
    0x640e001000c1711a5210425080d15890801c652a0124490382042d0780501c5036031403858001c8504001c45482000308404110301502e080c200b00d5104010f18808805c0a03020b0a41240c00140b030703444c1c0d464a40c0c0080700505080120a070090070880d4180f008100c1110007070700a500b03004182c083c841441c08071601c134640c44116010707017190440a21461101c0140026009015214164040b40040d101c070010400c0b800c2c414003100400b8034201450903040403a041c02a48060502c1d100554086000088610307600140001355843c0e0004070b5070781190507403071340c1c02c810008240018980d910507484980c00e552030b054588000380d00701680040c1c401820180050700604041800785050303400440f5424082c0c68102c001d01071300004142041c18101045400d640070f10070403c0810454483c00d002400f000b006541061310b400001c0001c1e01c62204022120704001610000715903130720020341d4480c0e03000030009460789008080500700b9441a541c25218103441150031480c180800106c03000d498180c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 695474991 1250 695473741 695473771
    0x80f010606200c090c07061a06220b0301030c1401020d0f0c060e01020f0a02100501031e14070b0318060601050a1101020c030309161706040b0702011d010c030b09 71
    0xb500c503544050340c8040280c1c3d00507030300769160790f5940900e100d001c1d40c40100c1d2150f070780049143c80030840d806002c4402c04000200c8500045940d0342c419500c6541544a00906114884851240d0344100d81c00003400c15030007000100502150b030180d0700944804843d204600303ca200f00690ba1680041e5484000540803e47d04420318410600311510520640010580c0442d900c58207082ea00005181e81803c0030200d810682c4940c1000259081144a5002c0041754107603194031a0742203008c1103da8842151003082410010703d00032600c1e1011401c400c1c0e404c00350b103c25508440380c1c8151000040500401c040d0034a110f000700701280100b8058440602c0d048000030b003507504d40c0400c1d51f5020195405d1181c410b400f90141b00540c40746068002422802c4410035054405004c1d0340c01400d0540d078000520400da001c0080d4054000c1d80081681e8000c1c0c0c0d075410200d0260124800021400c1c2821b181d64460880542280e846414aa20140081c6c0c00e038800b80000d0100480c2c0c00d030640d02e01c0c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 695476241 1250 695474991 695475017
    0x2101080a0b010b0a020307120305150405040506010e0c0705010612150519111209030a1806230d14101401021b04022203170c03270307030c080f010606 66
    0xa00007813402d54154010b032070400c0d000d07840b00b40c840c0e040700c1448004030f5151410000340399081c00384c2007414601180c08001c507003890380314035641c1c1f0030500803181815158070125854807650750a5482c10340d440b000030b04c2100d40740d03400d6281c400481c0c2c000311030041c03d090611121407000d0040300d00c2158104469651400310410031000740c40d8112602528813001c110b00709a5101d841806449080e804000359030710486014000e10000944081904084c190b000a000b00365004004004064681648004001904c12180c603c0d11508440307075010352070801341201000c09850098426098210038022580d540d560117858060050301c12030060f0412424810b00880288aa1000440c007030b000504001041c034a82c0d03c070f44441114003103107000c0c81030304000b048440742504800b403d21021041c140701c61004010b40c0c81c05902e004e04a80c3d900f0344d00444101100c01c170081c1c0708100007000c41e19180d50702d040220440d444c1c0c5c080c890450164a41d0030f01407040501410381214040d54428080d000c2d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 695477491 1250 695476241 695476259
    0x1009030804020904170f09100e030a12050d0507170709050117040c08031b01060503120a050304020d1e0309050a060e0603040c05060a1215061d0607082101080a0b01 72
    0x8010000c8400c2c540c094403060310070750300c0d4021b015010014241c2d595951850307410096030b28011a8010f082010616641d0b40684010451014007a80701840b00040044220b0075200da004400402c0c06551420042015040d800024002c401e419150713240619214024211040ca00c2c501801d804142e82001a441c600034110380903a200380902404110f0030b80b110004d03406c4d54050520948503480c0c4e034401103a607407400e00c580002450200e0003032604a02216610100c2d0082c0581c00043c003002100140c1517481d42c01c10851702036808242d54990044559100440100c0c19005800046100002160f0707414850040401e0b680d0545075400000300400411410390f00040046840d001181000030301a2191400f400280920f52280a449008000c1840c215000a103403524100c08119081100320703040310243c01c04000481140d0026001c040104155200e0344030010000100028100728090710071110720720b1a100010041c04036640c034021956206000b40d070191000c8000801000b4400c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 695478741 1250 695477491 695477509
    0x1506050a1202010c060e070501020607030c090e1504052701050402090a1d01051005040c02010507080c0c070b0742050406110d0c0810140609010203040b040f0305100903080402 77
    0x22051404d4503a144095941c00191107016501c841e1550000c00103004a41c1c0610020f0ba21441620301000b44960b0520300905414261084207038203d00000403c410112922076982401e2016005000c5d42c01d220141e40e041107100b04c030010105a080c40008004041030103440d0255030020000c8070161100c050020041103400703100780108403001d084100d900c500307000e510b12950318001d03058103c070718110901094656414012007103900d4242006141c0e0b811541d031070f400002c03041d4590b40724129030a81d28509111030b084090380842c042001b10410030004204002e000480c06040c03c44890322440184c0410780b0340c5109644500c0303545501905850342e10060384a4016a40859440c08100c204202a88505d4907001c102d510350340c80c4003000d84c002e543c00390844a21240800440d10744181504840075003010306210350000101c204481e03108000340c40162018840c59680d85540301366084c502426444221402d0007038400c400b100903410700c1003108494042e00e034503d40b59901d50800500342 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695479991 1250 695478741 695478743
    0x50c1815070b0c041e030b0f06240c010f050c0a030902031501030303050a0b030c0f0103110d1b14090105030103080c070806310804061805030d08041506050a12 70
    0xe800e1049902045a459401c2e001d100d100542943e100d0401008461003008401e091418940d00c2c0010000140c0c24000e0300e17440740300c210f40c0000603260310740004d640c131015400342c0f01d0044010107040041300412004112041e1a20003c0003550355550000094400407150280300001c14400a1007240c0280c00c845281480201503850f10303d40002c01c01c1d03040c4020f80041c0c00290340d640802c030981e00d062240d1800360604500409030110070ba000140411804c2c01e00c03604154995001802596112003610100021414103008070300c100307101d0a02e040042004000000d00b0a2229003407241d5880803550500d1040c6d442c1c5180d6821526075000b59030050307809035011b202e800400900030000388240c90150390303070010398403c41410240c02c075400012041d0300b158544100c104d0500003008401211704483e040e0402118043c03201071880481849584001d4140c014446924000e69105003240d100d54410302551314800c0d80c8043e410100d070424056117400c50030308001808040407105032603400c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 695481241 1250 695479991 695480029
    0x103120f05090301020a08181f09230d081b040302060705160603020414090606030a1508190b0a0e0d05131a071e2a150206060301050c18 60
    0x202d07919010a00f26849070300c2c40000190000184444005d000e103280c0100c0303107558014000340100e205078407000306120300560f817415078138a20081003002e001c080d41c2100980c0c00410440795042044151521402c41d00100014030380750016611410060205003804c1c4456030380c50a05096609110917548854002c0d559482480e03015006581041d03a0180a001d060f68003623116458a402c2800c0c8440d0015914481c0c1c10031002c022a545401068a030710000e200030105d808050300c4002c0282e0801c680006485009200b61181c80e070341460b0f040c407021481001d0200c0c00ba0b803568006022200300c211000001d8002e0b00c40760034041d12600140c40510050580003014960354003600401c0c04940c100100c81c90f0300400c0b42002d004440601e0a100883c445a03021040b605595041609a02400300c0103241502e07810b00c850b441c2c00c0016000a4480003010ba004417404000203036440408440b5a8441e41c200300018442203560000d4a100c00300000040800c0c68500c8104403007240803900820070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 695482491 1250 695481241 695481247
    0x1081602192a0306060911090d080909010308030601080a0c1e09081e01060e010b0f03071205480c0a0c06090e0a06030f0b130501020c0c090f0103120f05 67
    0xb10055207100402010804919a11514030b145803002c2039074116031180d0445440c1951220ba9042940308440307418200301da0b00d1074003151514150000b40524005603400004100000c0100111140114010304003601d40c403a043da00e4a800c481500c0001105c600041c0c410000c40201601d660107900008003036082044005403940c804a00d0014a0501c14010407035814018241e18000e121f0744002d0500c80300c03040d92941c1802a52481c1d84108003042112800003c0007400e540d12500d480d1401c0c1c154840e0034405414189007102d0304556800d010008069281002070081c1545111030b601401c4032a03800c1c80d600300540703c04e0200d8010380714281442c004c407162807001070702080c42c40c00902080d44400b842541441c840800885000f04103680031464842d003400480d0b9807059000d1502c2e400070003111242c0d201c14200c49210502c3e5001415580042800062002c010904414480d401d840640890303440b480154081d050038400a0540360b0f83c0b070100000b841c4a2400621808014140940303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 695483741 1250 695482491 695482523
    0x80609130642080d14210705181008060f150a0908060708090334050f010b0d15090206070b01080102090f0607021e040609020d0207020108160219 64
    0x3000101c040c801c111082481800b85002d003960785030340000b070701d4420020301401c0310868020306002601028282c0a44020600404464100900200c0ca01c0064400c030b4690900c1240506150001c8000943c006480b411400301414402100c42c94060f0703c1d40d403550740f9191842448400c0048441c0e0540000d04404600702500b2400700610001c1d1556969030902e40ca0180b2007414100007a00c52801c0058840910610900c00015210410304070401000740707035100c8818010000c3d031124400b032401d6203a00d41c0d10601101140001c0360b0a00c010090200085038001c02c07806030401c01c00204412040e0002050072010340e48080d1085101510b02c40c601200c503269090640c409034041d0f030590b0340000b600c10042c00d1a000008413818240c40603814030481d50300251058045034104035107208020041c52490780d036500044020701d0f034145d086584595100c8040083e6025000c00e9000c640c50801117400c1105440e01580c000341d050b4054194620411121200d0300031000b01035482d6042c40000304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 695484991 1250 695483741 695483801
    0x80613021903060609080718020c1f060602010228031e150b0f0a080a02190507061d1c030b060c150a1a010e0406030b0112030806091306 60
    0x4003504256061500c070310464030300c00074159849504910100105a802046001130008a000640b0381203451403c0030030301c60a048000303014150001440744038209407083d0f03001d9102c02c40054081905400e2102503100c0d1001e070700780e108038130300c1181045038496040200386890344180d041202500d0f02049803a840840c0886030f003d99010007460580c0e45030115041c20003120258000c10600f003181d0b003040710402d060040350158000380170030711401c40d001491342d1102d5070403030705c00f4101d42108408450340d03003000070010b070810301040b100c0318a8110220107074000c1e0080c01c0d4120010f003000b001d4803680c1d041034283c0180d0812504051540740d48900016948940107008000001401411411846068007042e0380e00a425007000515101e40c810814242e00b0703503415003140a0030164000c40303103140030038010011588043d181c400700000220b2498030044e2401c800c14080da9810401e502e5110400500d1407041d615210307002c1c01da1361850b0020703200340c0103404031940d082240303140b84280603400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 695486241 1250 695484991 695484997
    0x10e150d11030f0714030c0d1506030f201603030209040f0c0807172d0406020307021c020a02090c0d0609021c020301053001020c0c0f0d0b0708061302 66
    0x41c940e2840c04401c1100d5021490075240d400011403501c0460640ba0404050a40c4400780c040702014000241100c80200345411801c4400c08600b181d0000556036007005008207022044d0460050820344100300700d180340740b4445d035141840c142d62443e0040c2d60154140c000031078081107040c50340901405850b648c0c0c51007514001e20001c08045040c0e10304500040501d01d00404034000c1c0421444600881d01e030301000316521000d0807107003446214240050700f000300303840360b1142c014078008401c0104101d981c0c1c000d5801010179400322071101032042070030400006026507000050707102e041c502001d07103032074618150089100d508a0b80340200da41c04c05c00c01e451140c0c0102d15190340000f1040c01d60141140100b0594007905021400d550400c80014402d1041820045013000e81c00060100ba0b84010a211051864240210b40c4c5005c00103c1d580c94442502c2c2061007040c0081182420303040c8175145520081e40038101d030345c50b6921640203aa642401500d03c030b0b0080a00b40c4100c1c2800385500c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 695487491 1250 695486241 695486261
    0xc0f010207030314071b240509010c0801150c03050d0209060d2405130209010e0a03140c012115051003050f10050618030c0d0f0c06050405010e150d 65
    0x201151403208507180d0081c001000e0807040400515071241720070b4140080100c0300c52544981c520a444402c7c0c28004200360005403a003101c945000c2c00d200401205600000302c615050321307079120301ea0343c03042c503c46815041d541340c4002c40d1401c0d02d142c0000388504014000f080f4188401400c18894001141c09030300003240540d4038a540d0b42800f1500b040c64442480eaa14500c620f0760547c9040c0000300388190f4401092101d400e80100740344010340e020703210310041100d015041c54041a0f4a00340900c200c011480f5954050080340c103000354651050092201c000508041016514000b0610f0001000b80814a818100000e40c01054981d00d11500380e200381c807941d80c0030646040c62001d901d8000b1300603084245040e100d4104006540ba1903050321074024080c1c40c0c406a10710044046030400d0030126400e94030001802c900f8003003003000340c0d2071a52140106910f008140c0c0707680040e11503200d64010240464140c04400c5071603e0110b68800010003085035503404c1181381d061080a69181c245 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 695488741 1250 695487491 695487497
    0x71b0f03050c120c0c0d060609020f04140103180f02010c05340509010e0a0b220c030510180e030a0c030f0305010b040e0c07022d03010b10050c0f01020703 68
    0x10800c00151080040c0c0f12003608415200c0d2402411540d00c0750345501c0c000816001e803140e1b00c200f1701441031982c805170040102d600155591141c202424449034480c1c0500b01c0700742a15091001e5651107072180c982c045901c2a110441ca01d055100c01c80e4121510030100c1c10044400f03801c3d400208144070240105515429108120700e50004240c41943c6c000041006003a4211081145d903440c90b90035411070f100b00c0300c0400070b502c0380c41144003e4140b000e40aa048040842c00540e000c0c4150b020081106c0104c20030440e0b684408021004c0d506e040c2c80070070b40c00205c0c0d00705210050795003a0300410500d0841001405520350001c2905540007161840041782e0001c030580300303043e0442300801881c2000c0c0760411607581024621a414002c03801f60040e110b1410000031060b2060310205e80342c3c1e41d00107140310349a41d08100c8060684c3d1040e49502e1098080050201042c201400b80f880b1310000140101c81d0054204001c96440c2c000041c43e00302c600c42c24200049031403080c03006124081c040e0f5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 695489991 1250 695488741 695488747
    0x801092703050a02010b181f090606180909050c10051b0106050907050a0522090509010b041a0114160c080a050d0905060306041d10050a0605010c020603071b0f0305 72
    0xf019086645100d012401840140f016641e07802403404c0c865480349268800c004a019241b06010750940550004d4081328600000812080e80040382d55031030920140c51100d8035915800c0d41001d840105a0003002c0d030b40a0f56a01d00c4a160110540d410307004949440c50400c0c02c0307030300e00c0d4000b00d1a2004050320759540d108140082e003400d07a5800d074441e0490826625044075200001c2407403044d50a81d1101080320a80b80100100501c1034000911500006100c0c901b0030205260080c200a0002d512032031802036070040c0100c0d19541d807880e00350141c5820700c20440d95a03a00a060784074040e03281c52949803030712520015110014070380261207868002c204151043c43c05a00e420580c400500171710644c91400c100d26664a03044a9111500707580c0400c14000903094034819a010700d0490007540207189142d4214640741c1e00c000e214040390b44d02448101da5500043d02c80c6280c030030380603401c141d04100081c5424062840106010040c89050610710721544071407030000c40e107a204130300280b000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 695491241 1250 695489991 695490007
    0x1320d150602010504030c0b0601050723071403250503010603050a06050907120f0501090b070f1202070206030403110c04020a0302070506090d0f0309030e09090a0b09070303080109270305 82
    0x44048200541082d0000b0080c600309510040c11150749036030020607404542000a4407a44984103441c1c403240d01007d4003030203c0c5c0d1002904025a540450301460384036080d4001940203101403031944000014000d060242c0c1840e080d0301d152424401026656070054038001101d860900c503500c01075000d10064180380e10340c0c3c070b4008103840010b00700044075480703104240b0500842001303120140d540f05284d100140310714941a809000385100c06002d062907081008081078008078002c0060740c15965241016000120032812030140b0034010350803150500001d80080c0c0600d141052000e5041c04070703501e2a080c0302c009401d0f83d1052080d0300c0083d40115114081060030000310b90004004400380c046401e00d050000d14101c10a02d5000401d501e03401e08070b00b4140501607118420001070040d00040c58030b00c10656032009a82c0080341e01581c0040001c00303c540100e400019203a265903041c0c544d034070300700e8100050013010200401841105429a8408200c0482d84000d030340f1030780b6225261401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 695492491 1250 695491241 695491271
    0x19140f03011a030103080409020307020f0d09050a050402030912070203030f0d0b0a080a11040c0e1c051c0503040f0c09050f010828510b01320d 63
    0x752220b0080c20481c140010701c0084c60203000d54007620b01c070900050310395450141c00c914018690b40a40003038010182e20049043d40700c00780c0b0080d980140c40d9034060755682c1e002c1c04200e2008840c000c00035048040c0d04054507030402c0051404500080c21a803c0440d104100da52075404101664040d03545c40c503c4080702d04040180d40010810040035080700c00c0944c0320300b1030240b4241d104500c60783da208581640d13640641c070071000d402d40c050000c0000414100036000710102d680c03000c2d1241d215020300311a550854001c0c134000c528a55462604540703880d80c400f50307840d840e07820441d01c10010780740100f400c08240c4503132441404076000210007940740140b00e9051000c0c912081040c1450b96840100600f41c0f8a9030842a69110306c00b5488003020075060000c50200028654282d5001501d40440411814080d07038000065101120381c1e4451491401c1121240140b031800f0030010481c42001e030820200c038180703a5041000300031141d01c1010a400721940700c0c0074840c0d50706507a030b2403000850302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 695493741 1250 695492491 695492519
    0x90e010c0309080706110d02040b030415020a1d0a0b0d0504020f090610050f0f04270b010c020d050c12011d0c060316090510110c090c19140f0301 64
    0x420782020070a4480b1515400355900c03698001030a00303500c2d0b449451030020b03060120b03042614154002c6484548441d0039542c140c1c030550341035a00c280030060b02500402307075108030b6403c034625841e03000200506402d4402590b1403220096403140130032600060b61048500207181c0910020000035040c6050f104011f442c040ca0920b045c001c070700f28000c000c0d9a844104543c000380b5030604011fa00c40c0410211042c8900c140004032003441404180041c03041000fa10740c04103441c900c0c0d1010307021180b4124101c00c541f01810100c0c002056185a2805400d0518014011502400a035070705030511101041ea5490042440c440744c0e90f650311440c648682c0460101d0414000c04042d00f150f8400341d0000740d641c000641403d550401100e4090b0700340340644004c500800024040380722016240102a00c0500c0f052010303501c500030034407007280a00c2c041c100203118403110480141003001d00a050100c658070010441e0500403160710a008000f501b1000e03100000c03181404a940c1d604086590f01c00c1c031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 695494991 1250 695493741 695493761
    0xc090406021201030609030f0f0906120b10020a02011b080409050903090d0b0610020105061311040e1509060306160e010201090b040c061e0e060f0f0c0703050f1204030209130b01090e01 81
    0x88001849c0e00390003680304030320904440309841c0c003010380f501c1c41401070000c22010301da03540e000c0f840d030745e1700b14986d5008035804030042d0007600d0300d07121404100705280040448510003810100100700c24840b50006a001940014011007101c0c1044002c0000c94800140250156000b80c0184100f21051400c1401107041d044a803000744618108140424040c2c010317030080c00000c0b511071400100722800002914000c01013042803600da4140303e19001e15100350a000d0078000c003220400500142000911a4025441d0200191030340c4403921040700c0302502c1949013030441d501d58840c41c010948100d0701d01d00070b5003d404c0b00c41c44c1038070b82800540541000408140805a0300119040c2160081502400c0384010348002350340d014004e10707112585c82501c4400f806200007194a41c0d42100015040c002d6034031520884240c55500f003600e0382d80d5008917880c12140d8004110074001414031444680d041000c1c81610b100240c03290341c0f202c03400e0b407003600202c0d501551281c0f11606060309004d003414031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 695496241 1250 695494991 695494997
    0x803180f0a05010c0e030a0803061504150f0915080c0d060b0909010608070804080c03160f02010305010b03010f0522050c1206010e0105180d060c0e0a0f080c090406021201030609030f 80
    0x210702007008030381c03942c201d120701402908d0040001243c1da00d42540e00c2c0c80c00344881070500d41e180d80b552401080301d0b150840b030100080b114402d04110728002c801c98425140c40b441105130262415100b12141400106103500040c000e02072028100440d000ea82d001c1c206800885880340441018080110f205a2000040051000031320082540094040e5001034001031080c0c0d40e0058403880d240f851055120040e8005160b03900d001c2030018002607501224401d98083c0100d0366142c0c0300c160340340420300803848240d6101c10104400d10b010f030800c403800e400e440e6082804c00103050f8800221002111a142a480000740385a4002c0c0648141c660000c0242820b140310308074800005d04900802950400c0520f01c000d070381d03599a8420030503000e1154003410600651041401c014155003560300c03103602600b10104007081c4400f602c1040801ea4841400419985210748104004072001920548800e81c2c01c00403d815486100d003802c0c00303940105e20118611005280003004129120214420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 695497491 1250 695496241 695496257
    0x60f0603021201021e03250504081608030a030b0d020d0c0503120a050d020d0e0a05010e0c031c0e01050d050408031006030e07051210020d0c02061803070803180f0a05010c 75
    0x140c480c0f0211070700300c68180885c4240c803903503520100010555043d00058810885800610382198031800070020b036000e04064412601c445d001c0418042c0d054026004260000d001019510f031080e40280d545401c000c004000a0314a50003113111106100d1003070f030341550481000d20240c1420403221b4607030341042c1071562411041150041a600481d81c5c610303904e81c0c0006c1c1c5040034070040d0300300c0034050141d20140c40d0394000e6454014001d000803043e000d20ba0180121620b40e91902140007468070540d541d109401c80940d9004848440390071401c00d040c030609020104021640380f050500c81c502c00d03603500e40d0303905240307410700000ba880c0d0744444100341c1004036011f051274010420070b0440c0c1c415200003209002e4103491a0814000c00102d0348003500c081594604140380350404c55420070079809035503513501c0303441d84920320380b00820540d81541d004001c001d0016502d00011540428080f0b44182c03000a04100b107402c0c07020980642440c2d40c4032810100074003000f0311030700300826903504003802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 695498741 1250 695497491 695497507
    0x923070e100308090d080a021b01020f15100b040807090b0603071e030f180b07020d0504030b22050c0f190e1503010c0804030923090402040603060f060302120102 71
    0x200c071480d000040c20003a000c100443d040e01e8441c4c0400e0038540c041c1c400d6482c0d10f0140c40c02913603400b00f000c803113a24605608810b100c550000c01e00060003c1c2c40b1014211036440742c1d8540500c500090150742d813003040c11400080482100010704090701c0c00d0303c00780485500d8038043c0030507a1080d10400e40308200c208180b008039034116014012984090312100910f044d00307a0180c0080c01070a02c802501420702c60300061400c8901d010501ca244142e00500d61034480800881c1d070362801050060100344100701c180007180018010a0780080740d030300c410840c3e41071188a2202c52900340300c100c3e000e51100003000141c1c901201401036913007003503038402070400b6000304107082c00c0020b01c600c94011000c1d04c042403c03042e035142d800104007400b40080c45510b0705400e00400310841100d013540050007015010412480703062007401c20307001e03c03c101030300d1002e00c000300140c1d00405001284d006580d07a038008005030f49405000080003080c0f40005000d407650060040b0283e0092230303840381d6441001401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 695499991 1250 695498741 695498761
    0x5010e01230406050a0b0702030709090b1f05060706050919080d090318030c0510020d0e040c0e04091b08010615201c0e1e0909010923070e 61
    0x101d41c1e4040703141d402168004079021800804454210f00d4000070f007068046a1510b1010041206c64425001c55144a40c0c91040208607514004010512260f090101d400042c000d042d80204040851b80170102591700d04c000b801552291070100c40071900c60040092404041c00a0312051040317555505507888079645804107407242501030400c15039070700d115006040c032403100b95003d459005d042c091115207038244203008030528030a0380d1040b204400c001c500315101240209803610f99481e168805281302c0100310103011580c14031005c2019482c400c245a54031805007201160042200c0b1000007965810003810b011365420000c0701c0c0c2e05240741004000ba10807100e41c0018114589040081c240701c0a1212400004502c508148550200181c208400780807481da1441180c40d00342440c445507090142d8520510300aa9090b060144016120306200c014168028820000000e200e807207940c60081c0c6402d8964520601448030300150307850a420030000c0090154100d003000706140540c445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 695501241 1250 695499991 695500019
    0x30708060901050907121512050106150c030503221506090515030303010e0a020702120c03010c03111813020d0b0f0117130302031b030d140c04030605090c031c0305010e01 75
    0x40c500c00c6d943c0c1c5054a494090341030303c0d00e0107044402940e288500060600c28040c15060141c1c0708044085480780000c2401581d8181b28181c0c03540b90a400e59690700c030f403030b0405000250300a60005403d01c0503000141d400801440080e001e10740000c00c4c5082c20350b8641207a00042c1544200c403103003100b007105590000140c90464040303100c1072800381e480c00b031004080c3c0144e0700003d40201d680ca20210403107a000c208914080004d6000304452401c20104800341d0740c000c501c005c85e80c030b000c00404042c0707200b14110405110024150b01900050341c1c04001c100da0000360030340e03091565038003409012307d0802c810700031046003403800090110b2031880d101d0100d40d015004034030025402d501078003018002d0099030014100d070701c0d0032540c070b4071228500754890340030f070011080c0346190200000c85180002c003154010100700c1d03003490a042c295030f1904003d040181040b5002d10a40303503082000c0c2e4040203890881e0408541d00100c40010443c040c046d82c2c01a0041d41c0c4194040c40140712140c040414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 695502491 1250 695501241 695501267
    0x906060406120221120a030e01090c0302040513150b090105060a0203031807030b100504202b0c05040501020f0c1c1a0703020406020d05040317030615030708060901050907 75
    0x107503c624040c07101c1c000704c4058011304000d500840a412051240a5024103183c0c07082d500c06000d90700380703ca0708508884446d54024204101c4160620150801d80d000c10742c0f054000350201103604c4d4a03140c0c0c46460045c009030000081d01c8415520349030808400301801404141c0e48a402c000c80d000010b9240c4c00000c0c40903038041442455050701039010440c4400840e00800341c0507050404815030215800107000783e130f00a5041108441c03c0c0c07003001444d00c2107840600300c00c40c1804810311403c20560507420600e519032880d1007008004000503c2804110100340c1c8909950b14501310000e800c001c4030640c1c0d5001508034480c01d030315544030a615105403288856290480d000301e4589804600b0440b1660303040c1000d0441005000e50b016402041a2400d0ba0212a14a031882008132414891804000e15400c86058016150aa0300b8003031a041a40101200820314040403114003503002100d0001c0022224001d02c5081d0a00c4410580034000c1568064440c1c6004e1001428820b00707040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 695503597 1106 695502491 695502499
    0xf030305103c1d06040b0d08030a0f020f031006180308040e1e0f060406050d0b130503042304060e0105151c020a0809060604061202 58
    0x80c001c02e07a0070452403040c0d04042da00346a4081c9101c0b1401c502000c929640000c070316003141c00c80a28500b15840c1c1e440074140b51500c200403d031080c0519040c0510103143e078500c04110403404495101c0001c54000c03804c0395541040400910441130749801845021040c4600c56001556503c01c80d181c0343d480541e40c03410360040c181c1601c441c1c8001031900c0c0080100b00010400400c0e00e6501181c1141c3e6100982602e0a400c18503030740460340b500d040b06e09a010000d141c036051154001030071781070b24005410b0344103a442c42480c0d803019041401740c81180a44408101c801c104507800b03018090f400402d255810804940c001010044c1d030361245040c80000300b42090341c503200324101ca6004040d210402d188041001d015800108400c5282c64080c2000104078003600040c003000202d42c8e00d107015440d014902c01d05101d00a00703024452814401c0400c0f050804080c44150290115 = true := by decide +kernel

theorem cover : BRFrame.Cov 695323741 695503597 := by
  have h0 := BRFrame.cov_init 695323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 695323741 ≤ n) (h2 : n < 695503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
