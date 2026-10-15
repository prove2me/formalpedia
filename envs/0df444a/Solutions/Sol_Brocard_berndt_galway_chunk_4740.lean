-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4740
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:35:12.137378+00:00
-- url     : https://prove2.me/submissions/38fc3c1f-ac46-44ce-8768-e251de9ae254

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 852338129 ≤ n < 852517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 852339379 1250 852338129 852338167
    0x40f06030203010b0f01080115111b0a09180b0a0b18100b0304050d050f160c17030304030c29010b0c0f070f03030f0905041a040608030a080c0a0908060408 68
    0x400d5518210900d401c200003808140d050113503501000d090080c100241d07114ae4040c40d030704014142203419808070740c43c6c0d601e10384414071021480703510380d00004610b003100e60007103640d06180e92801004903022a03079840c100c40300040402d0041591030200d46c4090360ba4070f02240070150380000000300e0341882041c180380c04060781c00081c0301c254100300344400920000341c91600d01d6440e2501540f103124825403200948580b050429500c900c4030801c60a02199054680480315600c00e15103120380c0d454415922800104c8005d0007050000100c0c401107040c000c50b001404071101c86000d007040d00c4500d6118103201c2078101d4070125102103501001030324100304026106410200824001d490f2040c0081e1110090000904001200c031850b10003e0007a0314030009014000c0081c040400010481d05544003d0218284aa0304103400040d0308507000c02114011481566600500d60f40c100c021906a88142130b0300040040343c58001403403140a2109500a034801d081403907582c7c80b801c2c05084001300d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 852340629 1250 852339379 852339401
    0x627020102010c0f0806040b0d0803010e0106090501090803090d08090a06090905070201020301121410020301151706060403020f06070c12060507021c030504051c0e15030f01180605040f0603020301 86
    0x21401020b2601203400070050342c0d200300c0843e400704290a5010105e589c8040c00c010092201b80003000125220000141c0241039401e959a000699a5101c004489881c454811744030682c00402542c041c1d030070441006401c650050104500e89200b200101d03446e801c117a4004400107118060a1080100d2406502d4002c1d60341d200075802c55040007005140c411502200502e406070070501100041c4017840011801d00d000e90085489683d01d42403900269180482d240000300d403004040c0c3c2e5403c0419507103004001c09420242000d0035a8203014521802e4007280c0d500800078001071000500400c2c2410143c24403c590500c0302c011403070310506441d4094001c1c0c0070364200c014083c6407001c0181030822842e800b803401180c55181d500f0124140901e1480031400840100f00001c2e40e0f54120b6038a98506d20181c5204084043e4980344400c6804142c80400384041c0020040017004440d0303e014180c03c104501c00107000d42d803440090b040b52610510400742d41d031142e000700154603003031040c190040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 852341879 1250 852340629 852340637
    0x801050105060c070e13020d2004060b0306060d0908160b090a080702211b10021f0b030f0303042402090d02010503100b07081e04080c0105070627020102010c 69
    0x81c1900300380341e0311390070705000740700381c01e00684002a00f140c1c50b80d034410400341d0044c2c0b5a0364180701d14144071b0100f28540201115542c4d065942c0441424548103420461725054009030850721420104000f82d4060781d052801280c55580900c0420308031070050251000c5001901e403054036524082ca2440f40c020810b2144e03030460b080f0300010504030002c9908507a411540c07106420011404888694400003603001144240101c4c0c6c00802868076030002c01308011181902d84400251040b0781c0c400c0c48955032003007005100142602d4130029000b08400c3c10004040d034100003288041c2e01c1c510341040b038099034004034851000072501b00c081d1030100800d2040c0b00540c604940100401e001104110000381005400030000e0031508001e100c190103030040c241d01e19615650b60810210035040200c00d25107801c0c2c01c090444800b23800c10304032800c0b13600030009841c0b603480250056950b900840d5055030400c4e10303200d84613104070f070071441c0114101000400c000d484241e80002400c582c1c0310b1640b08244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 852343129 1250 852341879 852341887
    0x10503010c2105250210051609030b040c1d040c0e041e020303040b0d0b0f0f0a0308210403020a110f0109090f020d05161805010906120e03040f080105010506 69
    0x2541c0c000c0b0881c180e0780c0a40108440e2600300c002c0c0007241544c115411464000200c0000a550100301e540c0b01c02c0540000b804a500c038242ca03544145590400b040100d03151704010000190f034109045d034028000c42c200b6522642d600c0803000500d40351440000b4030102c05040008100d410798113800903083ca0029001c5034549940e4400c0c61403241e204c480d0300e0140c1f40c00d50000319607041041351702030318680490740e480b00110986070b8081c0240030202440740d1400b0107907800505000118441e0150002c1050041a02e10f4503100102e0340110049075505828100030031441d0038480303e440c05a8425030050501841d141040b00d000600c3c111654401c000c14641401d0903a03014919105940c0f1605001507120b10544901c0d00074070a40061030241424030f010407240001480d034a000c0c241c150b0326958030100e108040c2c120309400500640340405d4460703000740055442410400100d8042c51000250111050101c9207180c1207030f4070207106440001170910103d1b0007030040a00404050f100b407401c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 852344379 1250 852343129 852343157
    0xd1b02060108030a0512060d0519020405060f0a031514010e06040c082a0403020301060605030f01061b1121010501060e040213090e2415010e0a03030f0c0515010503010c 74
    0xe1441400106001017107a200803447d1580d800c40c2c1e86d0480c603032000c105c0d161010182c00300d40c2068880c0c4801d900c51407810000440e90700b090302284545990040180d001c01d81195604a5540c1c0a000069000c607a0b5500c0071241c6e1144042d81406030100c0e004060032841c104d4100400e8400607452a02007114500900000543d102e03000c50b1980a10103d000d0080f560000701a4a4090b56002039810340c00c10000107261a0050010350040c1510220307a101c41c0c0c0c0f1400182c0700c0390802d02285112140e081612001b041400890b50384500c0010452154045d910015021580000c0740440c940c0c4d5407400100130703103030b00316049041100c0150340560821418a8244603005040c1c03050010071a06e0301c0602d010460240082c884542681d00c0c031500006014003285502001102c0c109040d40f48021441c1c50781d0300914a414580c040241500b0043c0e003140d500b19404d0041120810a0024007001c1e02e000400610008150b0744803a06540150741c5424100350035a0308400d041c0c000d01555008842c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 852345629 1250 852344379 852344387
    0x2030c0c1014160f0807030f0f09140d081b07020d0302150a180b04080f0c0a03030f02120a1d0a0302060906130206031f05150706060501091214030d1b02060108030a 72
    0x3030800003174200813400d5a64804280e019044456400407002c0ca840c41c00c0400020070f134440c40074140a501c0c0801510ba034940f005a480106400700004224042c0003c0c50594150240e408a1304000014508240f031503408186003401e0600d0440c056048220034645103000c10b200c0ca0341c003600c009410310500310020080b0310502c0d60f021025050709506c40000c0c00348211070b812609009007070103c4558900340549256114180b001c01140000d04204a008414825009450703001c4c00c4141d414055480308106d08000301101c45844128103980c800d0f9030030303800f01400070301482402031300540890b18280420394140400108260380105824001c1c0016840e40b4081e80d134011142040102030706801c5500309850003181c3d225940c030403158990f1390700a403404005080964844c803400e00c845615a0300540d00840d80d07000320504400c006200714045003104113035100ca60301d0a23060f6464079016a104906845031809409800311414081c09040c0b43d04000080c010180380000e18240101044020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 852346879 1250 852345629 852345647
    0x150203120f131509050a030f03050708010b04090e0c0915030f06071407111306090e0604031202070c05040609060e010902070317060310092a050f010302030c0c101416 73
    0x141460f00008603002141020b540302103c9190070108460032540d0130700d00102038506102d40100001d06041c08140c00d607008061150590f128009014106421302c0d04400003027002110b224840e20801050300781945443c0000c03800f889001000b05208410482894039100d000e003091030140d030041042100080d4405802c0c82e008201d00d844c50f944138100d040c038028031060143e806501c41c406094031100340150350b00140468080b44424804400404034440d218030003264040e001c80c4080501407171b4000158028400c49200310310300c20b0031036150f81c041002c541c0e154018000242d910740003031000003003030710301540100031040e42035240040968004100207840300c0e024144544a8021580c980e409214100080c116132600300f0000c100c9091000b84e0780b04c4070003041180d1311403070305085940b0071480c005019218094104459104020300440c000e510003400014040c03403e021005040e0010f00410f01140c5804501140c1a081c011881c812124003906510601111910414200d13400a40d00c0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 852348129 1250 852346879 852346883
    0xb04080d0806060403120807081e0402090a11071a0c070f02060d0902090f010302010e030c03030301170f0d0207140a051309080c010e0a17030c1b07150203120f13 71
    0x44450b01d507640410010700840d04000e2010703180b04079222440341c0c404802880b0384400c0d6105425a1a00d9102000c2581917003e501c140c0c0703c0390000240941030850010b40c002c201c0301030010b0420307002a14100a5081020700b101c0c2504c410f46000901c1200400d583e40002407200814506145603540700c0380903840d9a002401404003240343c4480e08519030048001e20f4014203d4850342c40c021007110700f0364400f40001c9000c900e1a650a0300380e4140010000d0440700301070003d500e1a4203060311480244150412103805104009603403008850a015026100d0216001401e215060940c145011081014024001e2030110303010481503a03003008580b0318590041c000141c405e902e040c0030a1600c5504040c19940d0f0901c0703a91840b01c2d0001441c600150302451020282c02d03600d080d110211701c02511000600107052080a0403150601d00001902c2c6d4890101d40d40c00e42d440301d40c80200240010004050b0b040800c440320400350300f12446600c0b40e610980400f491822407506040e24100d0600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 852349379 1250 852348129 852348137
    0x9100806030712240f1b0e01081b040308030f0903130528080a0201032003011703040e07080118110a030b06040e09030a02100608060105120a0c0605040f0b04080d 71
    0x1541c404c3c8280f03aa00c5035002d4500001c840016011036a040e0003615108041241d4030b85810300c1610689160000f4081d4103001d03950300d0200f0340c03402004407403641c4050142040001d01e64002001c18800c14001c200462041074455124a400035104801e04402010815260800c03c005140480504050010b0b508212104400581d00e0031307180070b1a110384040c1403900d00ea034400100711040c00090f000b100b207100340d0b020300c020b1401a6000e62039003c1810640808081400140007110034140380601480c0e9141c1103c1c01d0a60314034503d20084010f8031408042000d800040c0708103050780e403441c800c0805d50344003440f40c00001c0290349524456620207a00709030341e42441ca0742c19034640d000c172402086540000071150805c24589601d0b17501040b81d6001521a0328806007a00d404c6000d40d42c00c441088016040a80c80d02003403200c580d030180c1d103024281c010603c241001415801446020f8002940c910f80c589041c100e00c09017000320364210021481c0c06210800c522080000c070740b40003207643d02d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 852350629 1250 852349379 852349409
    0xa08010603020619120608031803012703050d052a070c060509041d070801140112030c08070b0f0f090f030306120102040f03030e0414060112052a091008060307 70
    0x207011a52031020211400055086c0340000904a5000025003040e5030510501c0c000100907078205400c907030400301e40384602810021620b405014140014803407034000d0810510300103610540f641110001c450580f01c00c0c000940b415518030502210b002034a0828000c285040041c2e02e86510300705241c4070b10300801400068260f0b40b030f103403234225a100d010f00301c0c02c0c071060807486000700f80c407552140903c15442d8681109040501540403c00c0d0403a00300c00803564034000c0d1074a04440720a80508250b4507a10104580000503d941c8551032250101d07000b00041810b040c1c000014800000d40700221a51025480c0c018001000c0102c7e40c00901c21252406800c5c0b00320440b0740039025591250441400c42000081456044240e80c801b000c02124104600b4003da104005564000e03616180000c2c09c8286100124400303500041d009907585000d440b003a0001c002c000784682c05070781910751120000c01c00300b41608004500c03540502d164200700c0c88034a020404250307140003521a480101d54041c1d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 852351879 1250 852350629 852350677
    0x101e0e04200a120b0c0301051507020f0612180c0a0e060307081213092a0c05030310081e0c060d0905011b180503060c0904060e0103110a080106030206 66
    0x1e203003102401000707000051040c0c0d81e1045241590442d007029905401c822002440704007504007103030b05a0b04001c3c030760501e520b404114a50705800c4004204e0b000002804e955100d683c44070f014140680040e01d402645180080400d0004400c207011100300707500080300c0c80081e6a40741e01817004c0c1c03a00c2202601640c0c1d504000640b030601c1030b5203c4507003400383c07805210004d04080d008150010840f0306058045548403210002c03210b40d0045e59a4040420449040d07100d01d20f4000c07506480145080002c08015842d0303141941d006680a0000c0031401d40c040140000c2440302a032980081c1222128440000d01c0c11900c910748401070611036400066044221607241d4013007405590030200820544007100e800768814034152500e44040760500ca0104202d07551082514103803030340030b0043c2440f6150001440c4a40d000f440800303907c1a1100c4001c41d00d01c003003040360741c0298094420320809041c89020f014800526400c0400380f40d040c0001407000d07031104c0049034504080104401c1c00e1440e01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 852353129 1250 852351879 852351923
    0x20a091e02030a06150c0b0c0309010b030d02030a090506030606030105060a11030a020a02121b0909032b0b030f0606130902040e0c100e0d021c0b101e0e04 68
    0x903069400401e1000c41800070040481c0e120009880002401c007542d403100300401e40f404203400400810700ea6a0500061a4220303403c0a183c0203490314001081400450000904001140755000300590000c16a4007040fa4000904001404195540e40c0f560604d54040341c0244014041c1a0088100003481841c2d984200c542856240c55142a25100c420a4000949840e000714060b03204a06114280b005908085411000c81517010742401040080700b003444800c0034010080103d9000511070180d40d16000070514141040c0120008494200c1d12010412a074092a00d20701907070081140400000c800100c01c7d402a07000c441440c0301d050110039403c040e00345150000c1d0410b0070003620000c24080042e02031542c22048a1415030300c4100760080300d2802040c40318a0388104209402409828200012562105009491f4101070201d886000300804103540341c102c9441902030070805c21b0160341401d02c562240c1040310340d0680c9458142104580042d0014100040660f441c0d10003201c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 852354379 1250 852353129 852353171
    0x9010e041109120304030201081803030403211508060c0a080106030f0908070b093904090507080a060b0907120e0115140a050411070b0c0f0d09050f010603020a09 71
    0x100030b12100000c440064071039105d402c50310049000c00d00180120b903078400b030b60601304e14484480c070007182190380c2ca0f02c1c1140c0749440c04000c404841e01c0b200241420004501607501304d020b080903201003441c5071035112403a20078018090300c2c40880910401d14650b50100231036044500d40e15010031803a07200c0c11100018820352070000c2100c240042c000003088072240400d88035001a074103071001540d64910040c0c214500403074031019080c0c184004800ca0030003220b604034100014000081c4640d65a0301c2606d00862904449219800084854100b040c00d000c3c01d010100113480b52402410502409410f0000c0c0d401c1c102482e03916006008034401e000d6200d1841e00074401008085103503030300310095586900460300f500403003880d00013060a0401e03000b010f107440705d401d91142c504189516074448000000d0150f8910010400141041c20081d0001c1d11f4550003180000070340006e176182082ca8104600001d00d4a0f0341840810009603071fa04140b84201ea0088030301043c031030032841040c104400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 852355629 1250 852354379 852354397
    0x3041512020f0414030c04060b091002010b10180f0b0301060f0203120705032202030c0d0510140612210f07051e010c3b03030304050d1409010e0411 65
    0x4040b030009513640010200a00c401c0082c2d007038503901400d00c41400181e40860045811084041006801c1c508002d02503403401d01440c8000155010404001520340034040c5503007000804800e854440001045500c00c000c200c00040284024030b01412040f65000520422013131141c44c80e40707210100e00901c1114000d8900802110362850071401c040e1841d0029160f058101d803151031000d0300c3e0f070302c851315246485400400800841d82c101d01000b0310542150700c02c030342c2400fa0310060030708108180540f600c1c40b00c640749022682d00d000d50900c080c40400058102c2ea9521143c41e0251501401050000d0b80300c00d01c014680d260301080100516100c1c1c104002c0c802e11402d881044c02c802c0c140060900250864028010002441000c0b520402c40e01349080c1c803030302140e0443c402d110450307401c1c40b405a0501140c00e80e180e81040000d086400840b0140d0340740e0000008a50b80139404044c0b2940d8080180c4000d04081d491070000300f0b603c41c5150500e000c4d907503c41c00f01504040c05402c4e10340320a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 852356879 1250 852355629 852355657
    0xa110108070c021f08010503010b0310090303151403150105100f140c0c030c040606080f1909350901110f01090c0905090111070816120504060801080304151202 70
    0xc201c284c806140c04128003000002149000003040303d18041c0104603007164002e00800100300c0740082980145101d0380102c050564600041039040c7e40908130a0041c2030a400034000c1920300018982410b4a141c1015910202e00d40180020780e2500b0007a03403810f1403032030410040d0500b548241c80e45880c070070f012900100d001c142c86111031130000e030070b040058094003035070603030301400080c8410340708540117440c0451800c0300081c1c0300c080b01c50300c210351001c60195540b64005180e4110421500d0840c020343d2507081090612420380000c18005120680201d1101d039104802010840300b4012030100342c1c1000340b64410070b14560b10800c090a04482c8030002001543d0061815940440c403034840d5a004d142000009001d494061180c0580c02414003001440d00e07141e035031104a9980058100d242880460706201c0210b81d0a03800462140882d442d5290780c1d80c144800a07041c800d0585c04130619600401090002010044401d1003c00071401c1028004500603404800b03400b45481c015950 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 852358129 1250 852356879 852356899
    0x5071101061205070b040e07120917030f100e06010c060609230c091e0103020d050a0e0c120a02042313150506030d080a020909041a07020a110108070c02 67
    0xb50103a40001c140c8240b146048602d51a030b1400107007000e01491040c640c100716a08006071100e4020000600419195a00001c1c0c001265503800c11074410320414200091010080105080501e40380c2c5400246840740045a0307413038003070360031000000108210304202c2c50044076810042c168101c080605003000307091090007000d85c40b520001400e282f07114458440400800c1030b0504000880d0030658002d081d004000011440c0e0b00b00b60711700c90903c18100365003000a41c40c0c0180b540b140c1d5010303181c1040040b5080908015042c178000803014080e2041e0f241800400314040002088440c1d41e90540f8003148010145225024402c0107206108500701c41c601000a0402143d940c90b803903a10801c0403c1841110800d428100e610480300103030554005116600720314090400d581c2d10800681e005890034030a00081000a50191070071a090103c58100c1d8010f6128120726903406591403008154034815a1200c800440d41105602e050210b40c4012031042d07032042d40b90f0000950080c00c08054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 852359379 1250 852358129 852358139
    0xb04020d020702150c0615011e021c141204060b0303040b03090d0305010305102004180c050909010b07230606210a060b040e12031005061306030507110106 68
    0x195111201c12886403003001c07004000080050140c3c1c45c8141d900b40180b03100d6880703c1e02031640807500000390341800740c46000786e00c40d601000c0d806a182c000c1a4044c005082d008052a55211484803001c02400012503d00707616161384800e54800321070040d031960701d6488600b014001403400b030008603014000064040303004110309005501510700c8008a911301a0945001c508441080c0001081c5402541d0841c610100640000307a56203d5607180356400d91410106020a80c03155102044442c20082c410325030783caa900c07400a444c40d880c10145e190140c0d8400007104408140178600084001244c3d00f800e01045001d28810000c1981071041c01000040400d5a0388108544440c4910f81c40c1d0f18940706200502c06090030360038000010618200d80e40da074440030b00818410310390419520a04800351314020400704408400c50b201a42d0b40e410140e8004090101d1500328501a00c81000900c99400c014040381007210440d141c002a81d40302c0001c01c644007252520b00241540c01c0ca400807403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852360629 1250 852359379 852359381
    0x607020a081608060402090f0928061506020d18080601240207030222110d06060206160f0302090105090a1e1a0a08060121060501300b040b04020d 64
    0x1c1401c0c0c2c804000040c0c07580d611161542c8401c21100203400c0070000010400c2e260a20a00b0f80d000640d460070745410180310300c1e600400d0b1240003a141c04010b03041010390b0038007400e80f00c1d59402281030490120000d0a18002079910700c2084054001c01c0b500103118140703894230020100140c04124180c1d903035960359910360b840a00034400c2500143c920401c0d4000602d0000079134604a95020740000004020807c0c20300c03041000c00341c040c7d01e06072a1203030010400c03034070f000514a00030041400148203090080007032803c817000303124064865002030f01240c520382003081003001101c180340159642404200484250182081d84d68201d040740b42c01040c11400502c0c000001c5007004420140b6a075a4030007003240042c1d400207600c900004011120016100300801e55000b401810598940e82e01d06034001c046c007000850410540d96030329010710903583e109080034039262203c550f1030018016010510300302d50581d500101825510300c03105420751501d410020001e400100215160942040240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852361879 1250 852360629 852360643
    0xa050402040e030a020c01140d3e0706020d0b03010906090201080a0c08060f04140a0f06060504060f111002070606030b0604020705030318011103070e0901171207020607020a08 77
    0x2072041d0b0070b00700c010240d0a000010380f4001590b42d0b0080c0b91100a59005440c5e280c0d03015810400c04104100140c0030001c81c1c040c46441c80d06285c0380141d0031401880c9041c1c031141e885604030300f0710640045030032407400b20403c0e100416007003880141e640e40150b034020002c0c940c40100a0701765081481c200140b10321a4070018030f05000780c84140f07084e07803201002800c0710030500380540400c2c481c0c00825000d04114003058030703c2001420000e00318540803407101000504071541041d03507403124500700769815180141d00c0240340c00c2c10203e00b024105403002e4016802903817030404100b01e030016607106007420080d481640321040011580c0d190b0f80e0812070064285808161480c1005201182c038504051003181c0036903030070001075401d640350703480c9504445006480c0500d4a648036542504a007103410000e50059140751100f00040520000740007500b881680144c0e10b00c0b40071441100d00390004035814a0701e1401e2023110b0b07610001c40c03000403c03a00401c00041d4128203442c10218003100001100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852363129 1250 852361879 852361883
    0xb0613121401020f3f0a271209030804090e2b08042d02130b0310090c08061e01090b010c02010e180f180a0c0302060306180a0504 57
    0x80780c1116403040da01d03420b070302c0b4020404003456010050b410720703003580314461a0400c441c40e001002400c0030b0b80022000701c402c01411400d4115040c01d1022010040c17080124601550201c460a8070064001c401403040141c4040c0c100549080c100c4c441d1407040e6140b201030359204d180c45456a4460380e642d0002e000341540001544540e64410280b50720200c20003040a81b106d03100c6605503030300001181d00c0312001d0411903400c4c80390703c00403034440f03100120191b4000b18000c1440c502d00890041121030501411103204c0c2034a440b4068083da100840d50340c440900048022400c0c10492414040c3c4685982c0101c10b04d010b00410310010103c0904210206e07042c10100710816601c8100310012228503510f070b82c0c0480d214000351401940244103100c40380e80c1c01030051001300802c0b0398110301d02c40704071110400443d0050400c21000c80e8100c41e15200710b403900040c40400701e41d641e40303189080796001c082d2050a01000040042d9542c0100034540d10fa02d50385054203040c040d14400260000342c0741 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852364379 1250 852363129 852363143
    0x70209071d011701150233070815060a0203090d0f02090c0a020a0b0a06080a050601060323010e0a0e03071101090b030712050411040213210c090b061312 67
    0x1c1c0c412942c450034010700300c0741c2801800c99460b4600701c419051704441c4601c20003540110b0201003408010b0381c401460b51400d4800b481c083e8021003043c1c0d5020788005121009100c0301800303000700310700c10060740c60810034240c0300c1c1c5079643c126481c141d19602402c1020b541c082c981c418030404010b5000140c00e00c5078400e079001e000c5511821101c014030f0050755810070042e8820490040440c194140c4690002c3c00c01034006031540d00c0f5108603040ca52840c1080e01d46600a81c01004143d0345441178645030881c017079410840c0c0119602080c510303901813040a003044044e0380418803504c00d50340140d1115542d242200d40e00c042c2454009881d50300480700300c7c081400c114000890300345000c00c4a1040100b59201b14038054428010001420041c00954040b510400c5440098170b0350310040003400d03030300d00301c186c00c4034030f04050301c582da2083c986036050240401180e503001400d40d41c0880c0659040d83c0000c038026030034001040b0240074611a40a400000c030000003580b901f1a44852000340c041c00d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852365629 1250 852364379 852364427
    0x90911090903030105010503130f0206070b1806100b0706140115020f0303070e010f120213090f0911010f0c1506030605060a05030c0f0a15021e150606030c07020907 72
    0x5901c0b5200e000902c10140070800401c00a2a510071152015481c184602001011900e064010400ba50400707a0200c030102c02010070f02032030007030300c0c2e010586007403450004203031916100f0708926036810703d40303c0c0d4074031240e0100701541005a15042504038004091541c0750030b6030345200d00c0030814002e401d00c502500800040a010500c04400c40c1e100da820354496085450300c980044812224038030090003040340007040150064403a0008007070301032031130010010302802c0003000b104030781803071191044942c541a040c0c000a540008100304070403090030b00d1310100406190a65038040c14203001050100703c2401c1000d03000310b0b54000e00070f803030169000700582d541c0d0f4004c0c0400240103009040d03050340b007c03031402010701d80440d154941c5600648000290703561a48000c4000541e01c415602503040203440d4008601647d503032080c0701400700300a01c20a8407100c04c00503044000350015004e09000000101000c1200c801c5400d040d502070200495461b100000800000004c1151894420790340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852366879 1250 852365629 852365641
    0xb070c050a060305040b0429070503060102010b0d020310110f0705340b0906120f04031b030509041802060307080a1803020c09090f0a08030118020a08070c060609091109 74
    0x8480c5520465020107140507d072900d48607050760342540c080005110704c0746241e40082d000d114100c0c030700400b11034a5554490919000281c00e4038110b1054902034000070842c0f031301595002441c80702c2e1003400745000402540300040d18140344580201e9042200001500b60200320b4009044d81c040c004920140b04ca500024011005260f100c1c6004a091042018103010300f200315070080040310300c01000d0910300f1a1429143ca5149012a0201d00c42c04d9210100000e01d504400c6640c0903245507066013400444503a0050840d0189041440c003490741d4020129042241c0706c007000c55139400500751078481ca07082c10002c1042c0411540c2010031030030706008a58006161b8a000004bd42c13507000f40c08008900700610020440040c0080c03003920880c02ca49030819014010a40c240b405084059540c0d810000300d00340841196240030b05040c13040201850441c0e009041c0e03a0442d805180404a5402508051000d420b01e908039020302c42c5000400401c0180500502020080c00d441400e5650360b50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852368129 1250 852366879 852366881
    0x20a0812040b24092806090c031103181915110c03040608040c0e251805090601201605060922090501050112050f07050a1203090b070c050a0603 63
    0x525800c0d408004600f034184034a1901e4150305034000c00e10000003903820100c03541e80461051880e85440c12554602003071140c0a094050005071580d6030406202e05c2c44130042079441c80c8001054117120702c059a10b0740248103000d01140140c00c2210150314008030302c1c0c0c00c1c80b6403100c0303c0c10480c00f905403400843e01d401105ea0070940c1d040f841048090b60a2602c5e240083e100305800030700860f0110f03030303001e00800d01c483c40359607041c01040306035400c0e002090ba0001c0d07010b914010100c1c4c01d00b0b100b0142c030017034005d00303400e140c110549000361800d90160721580016600400d01715500300440c2100c07a00007280142c0002d40d00b00c00d0825a8103100076503500c00c2400001d116101070141c114003080d00c5102e40d405ea45214241303800241d000018025040d03291282194400c2c1c11413610312805003203047c184071040150b014410380c1d00d4003901202d8501400100c1085851042080c8004122143c0042c18007950303c040c020030f58014819900c11f2640780040c3c1d05a45400344500c0761489100200d412886 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852369379 1250 852368129 852368161
    0x1103010f02030108210a120b04020a0f120e06060d0303090606031124030f0705040305160306140f040210120e030702010807020d020606010c0c0b12180a03021c020a0812040b 76
    0x1c45c00c405181a40c41081211010307881c0c52200c01581d1511810000f9807546c0c802000c0070f4074255a5a010800040b07001054100c1b000c29528030302e820940489a85030f0085001741d006001100c0c80903442c00c041c541500034000c010703400340041d03103081000024045c0000c0a5142070208540b0785011860800c64242000301e90307460580540f005000003001107a101c1300c150f4000380c441c1020b82c20660f60751f40301b52410000c034510b209124107086c010404c0208a0090000c0c11542c42c0241095282c00501702c4c07a28071004001900c074151440c2e00a2685004582124800d01450824050b11800c00343c4d080d62a8042c1310201d0015414400080c200703072010400140001d1250301820707042c0c403241d004490b403034800c80041d038095003114000034180608400074108100440e08030441440e040c0d450065000e50a01501400c0e001400700c031001036400f00e18540303114400c100940d95501981720491070f10148032002480114002942c42844810265240c4124401e100000030742e07407584000858528 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852370629 1250 852369379 852369433
    0x40929010909150e03040b04090b2b2d03030911040212011215050a0b0a0b0c030a050d06030803010b0c06130b0a0e10061404270f1103010f02030108 65
    0x3050003010822080103820000b4107915101c203c5c0d003000e880342c03082c802c20b501a51001f911103030340300820929420000907039000c13910021400940c0c22140341401c1190b00c9500c40003800d0b030a402031710040c15010b03c0e48100092981d030307500c650141403500e0b001d801004c0700d01045d10300010540c1c1d01d07001458140210342020720003042c2014541d280854680070007010020032585500384405d484401902882028464105200c001c144540e481d001e0010703a007019001034034401d800b0400000c424100000700c1d0790811061610b181d5400941900c0c6004103120740004180d4200000002407c856000242c0702c044105000e990302034607049201c10720464070f800c005210303228031400100c40010030341c410308203a5514019a210002d40ca101102243c40e2a08507080405a07a12198024107261140c2210300620621a5108420100e130701d4424050244005201d80400d240300d40810203c00d943c07001f410307000380090081c2c000e84903494004c2d42090048100501c03c0e030042e041030f00391180355116242 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852371879 1250 852370629 852370643
    0x30a03091a090c0909010f02030a0606111c0507060207050a0501020a11010c120c20100c1704080a0203040f0b0d0b040207020d0b06210601090b09090c0906040929010909 74
    0x3143d1401480520350004108041c00e550b82e04600e10000800d00003544100410800029001e04165010300b011240c64603110b1070703074440001030000c008118071540030503815090080d1143c0703107031801d032000c0d01c5030501c0105940509030803e020048150046c00c0e1804441e00e94100d000c2c2090041401c03034400132036440000d03d12401c001022802d95001252484d11031804002d0303490b410450130390254182c1d07055440340d4042501c05082100300e204e40c590200c01841c103d40104911201d0729039005003e031000d80101c0000070304210305d9000700b085030700409011429441a40d5035842c0c04586800042c92443c965082004401c1545003504c210349945a00501c40c0c0d002d02010784645902540040c04140c00c0403050a00345880c00e00e20001442480301c1030300402181d07040007504001d4035100d41026014090b103206101c072015001c01d40038040002600c00750001c0c7e450b000001d0241064480c05400c1208074141c4910803108240510044042410280c0c260703642d8050307000c2110034524010b40b00b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852373129 1250 852371879 852371893
    0x5061b1c050d110d051905090a0c0b0c210901021618110d060b0c070905010305030f0307090506040b0d0506092806081504060b0d022808030a03091a09 66
    0x10415592010307242e43c00445450341802c0c4078843d5202101d1060b1071030450302c9110014600c40c10480e005440c0e0005242000d0001200940d0724440c001c10180501c0c030407445c0200b040b080071401042403c00d541890100c1c0c94000e0821015031110340e04c24040c0600500500c60300c0400c80e01050030303203c2251681260203580340c0007045c84d0002041d40c0326001c8a030740400c01c0f0f44180d541e07950140364060251742e20350f55030300d102030110a071074510b0b55171041341c0050070240100007240340403003521800c2d0b28402c80c0d682c0da60307120a41250310b98801c3c1c015a600110124000c905400c4074000342520404411007000241c41d148104107116000310703525000d070500700307814207003500a40e440c4000b200f0446c40c000c2000741d10340c0002ca08243c0a07940100140c49520200002d0202d140121039260000b51290045000329401041c401e1100050050008201d500f0780c04c16081c0d0b5000800050443c1019240c4a0608900050141840041c1940c0001031014840c9607100014038583c090030664000303241c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852374379 1250 852373129 852373147
    0x15010605090f190501030f05101a1908040302060702120d090c0305060a0209100e0310230f090d02010b10030c1701030501060302090114010e0f060405061b1c05 70
    0x20768040c0120340d4014401116500321615110182c200750500380802c50040741c2020001400c640c5044645101c20b820802408203400b80900f8090076200744c0e40361040040b0700168207018611034030004154071100c4200c1241102c1d408015140214401c2d804d07030300e050310341c95800c981da42983e421000030000c2c01c2129101046507580b06420b000c1c807131154181e01543c2d98036007600340700c0d080b99043c2a9030b0700011410540e141041c81c0c00003070640c41c02c1074046c5038401408603580c1c0503000000003089568000e001c007000940c4092480c0d80b0380102c0c4c06151450404540c01d024002a64460258485c40d0b102c0d02c0140d006000f41d040035032000d0154000b10b000b01d4401c4014095038240300f000c0c016640c7c40d9042c0f84c034502c0c8126000c0c40c060000400c049285205104903044141c0c008200e120080310982c7c03c0341c0e441403052a0050702216129424095040021003e116903803010364040b0b00001c424000710340c40c4100c0a4681c18003815201611600740072000c20a14040d210b0f40091710801420705 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852375629 1250 852374379 852374387
    0xf030a0522050c1011010f0207050c100c06050411040e0a0309050d080304080d15080c0306010603050c071b05120f0d0e0108071110180b150a140f04050709080708150106 74
    0x2007110500e40740789000c00e007403170707240c03c5841584402402035000101e4500703110040000740a00c0a082d281c0e200c07400319408005018144603070006002d140c940300410148688081001000b142c001c108100b030055184009a540c44162000ca001c00c400c207400041d02c1c40e0126800c0200ea801500043c03569444d0364802c05141e00c00d500490f611a83e032500b07225081c03100e4140c00c0c090415500208801c1c00104100749c80c01a05a0018040505010400c94812000820f5800c00c0360f0001940c1a01090300503800030000150700856084203c06810800c000c600080b0161440341940c02c1e64400d445801003281e803000c401004501203036841c008074810034410004030455180030b01c00e442c0c8006811800d44c05581c2c0758980701c0c9400c2c4900b00d001080c40000c401c5070380c125031401528006c0da20800b0200740200451720510040d802848183d502c180c03100300d80e0084202d4000c0040003c3d1501c2000645044510b0283c5c0c1d086205d0228082031428001540c8507081d1407441071000241c2c80c040c0111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852376879 1250 852375629 852375649
    0xf050103020f070c03030909060918030e010207030203032b0b060708070f1e0605090d1e05160606030c080c010e040c05070b010e0a0e0c090a050601050f030a0522050c 73
    0x503490724208082c00100b1403070510000614480c0d607c200f5058503140508099510035040486000d1500551800116107294900e40599050404d600e8003154000183e060007810381c0013075003502000442f01c0d00c02e035580305014111459010300110810121880b60b00300c40c04200460707005034040000f07501082c200350203480058840c10101306950081c1d9a842420320000201c07a00c40000c44200c102000958000c4e0355000450400a2034003420320403004040c4194003034a1098082c0505007881421322850441e031710681001078001c5842c200d4039002c002849541b00950300c0120311000442c6801d0040f4066103c504140c0d54100700c040004100001003210301d603807800784039040100c01300040d030703030303042c03503008110810012560b03140000419099812004681c9110f810541d8010b2056840c04011900080e0784040090341e82c1da4040107803283c1c89000202c0c80d1080001c000c20406241940186214117103000050104500c186101c24411110900c000d11a4025203c40c80725410107121107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852378129 1250 852376879 852376897
    0x10f0219030c080c0111070212060f07080a180c0608090321060a260f030a091703040f0b071703010810050411060d091e0b01290a081008070f05010302 66
    0x210341381c0425a21080d0031910030300a80c0c03101c041d0208140003903190250000d5220240c4c00c002e0903941c9030040191030180e00041c50401800100404a814100940e02000c030441c8030b10680e038202e1400d42840c02c1001c80070311458000440d00303000140540c3d0080b0640d1000c00384001c10090001c800781403105151801400a50001030382d2000040300c03120480740c1030f07490080c814456052084800301c0da0800300c860180b0b50700c5034020030400006d40d910180c034204448940300c40005204606000310f08610841c1d2100140090480000c140b0100510003003d55503c15000304e44007408084e06200d01e40001d00c140d0340e55401400080030707400b40c140c1200c2c0e4410303c61011001e01543c90800141c81b80c000b0482c011149565810b400108103418070425904150499004c10012859440c084170050501600e91810000c0c0c445a103034548009a030640346140844498a45001040050485101311501c0840b0310344102c0c00509084041090300c20340300310180041c4144d0130f01d001075000c6e600050301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852379379 1250 852378129 852378143
    0x60620010b04050a0209040b040246020709060e04031b110411180f091305070b180f0411190504120f050f010212011502010f050f0105010f0219030c 65
    0x2100d0701542d910702c940c600c074814007100142c89649040c240402c480700d20600500542c0304102d0203420b1690700c009440f41c1d5045420b042c0424060030107002c0c9001681d001c002d4440c0720070014641068011404c0c2c801c2e54200002001880c0e0341d41d0240036a1242541c0c003801140940500328244500003c10307001c21800b034100504165940c00110b021102400702d8403002c40380200c0c81e800c2001489a1003000c03420f044801d42c08402d240c20000c2c00c000f81c054900030246c0c0310302030010100102441018010017641e082c0c2502c0f0440d02001d590301c40c0900b51000c1c45101659940718040c5030a100d81c0003102e4002c8656800d10075510319210480420511038010310900f40310005a00c0210f1500085061050216040700a064900240f410009003041d41e4542d00602c1a980c080e60f60021940c11601c09a0b0780d2032000c1303172201044c1e0041003103841495002c5d00300010811054000312005040358420ba88498500428880403601d448800d1500c1c54414051104480070a1143c4071201c076450140709 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852380629 1250 852379379 852379391
    0x702090a1104350d020c04060e0f13060203190b0607050a0b060604030f0501020409060e250c08030a1a06040f1802040803030f01092d051005030706020c120106062001 73
    0x1010089441030600001e9407944924044c401081d41441040a0b9140554090004c0740c1070480300c1c4400500180600115070f01480080c080c0400003a40c0303014280c0200e0b0440d582d061039540a00c41b0420203914030042802d14681640c0c2d400c20034122504690018060321240380d40d66200280c451016010304d52080c024040800440c111151030100944502c00044e039071403602c0403101c1903c4190b0310107011841c02e6402c005020070103c0c2c100380c0c4030325885c2d104004090b01e5401620030184400028100100110801c4089070302c2d0761200d06616609a60314400302c0180040240740d00c01e078005e5030540c400c2d0070001c0052030a1500074041031001d82070301605240d158140e0520390f400031525806421011001001a980380c0d204240010118000340c48000d44c41d8050050b07010525840c141c050b560310130004082800000c01c1c20054100281134a01142d600e6500030f40e80c1401c01009403149001e02400c6503a00014416003003110501d0321202010540718440140c1d01240601181055480308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852381879 1250 852380629 852380699
    0xe01030b03120c0106080a170309011d06310f1a04050601180c0f0c020d1202071a1315021005070c031704080d02220b0702090a1104 58
    0xb001085855881c081015111440d0000e010b0945600341c0c000e0800d5000010040e010542004d900c200024841580680c2d9455101c0ca0a00401c4842c403040d034401d1004203c02c044400103d084ca000d8a80c1c000f28001c0800309c44802415031901040140d07011000071484130000b091612034100c514029040c1034000702444050740f007141c0d41101c08644603040180113000d411408003040d200b0000406040018440c014005069010300020510611901c03003030400442d0b850125580d5903550014103800880e0398004040c0d0340d0b400034010103200301d40d8403102c03000d54000c000949144c203908e01745083c0301501c0c0030952404d039800e0512400443c082c01d20022000c51050282c24011101659006542c003001d0030300500d0340c810000070a44038101a020b01020884c02c0066480351884202c0060352070140000c07210852100c2d15000020001010380010000e030b40b540a4200e26001341c2c4c401210b41d80f81d00340c05c421600c02072510120404c0c00c0c07005001d00d2102841140038186218410344000c0d44503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852383129 1250 852381879 852381883
    0xf09012115050f07020d08011d09010b030129010302031003030e030f03040e1005030604230a050a060f0501120804030320010e070305070821090609091504111204030e01030b03 77
    0x4443d0003041c0410042030050540c1c0c100810740703103891249051841541011002141c0426040000c1070f06003140003c1400d941c802c0d030024503001c40041c0200051b0000d040d0181400f481807010400d01090a0850241c550080c000c403842a510341ea151100d207821980c041d51b10b400c0f079800c003075018440c201209107500340c100018400ba200d81d4074070000c07621304045003848099881d0400340c080c0c0c000030103000000d02c071025841c1040a0f100990052411240c050300d142030740c2e901d03000d0210705c100b10094041c000c030b940c814840010101028012a030700c84005851605010304010101c0204100030030110340b090695040350600303161000050f002c0d4039204e9003902c0088441070082d4001c1c0004104100781000000d008000480141c4201410305a80d00300300201014412110200041c018a1540c0c0b008221003d81000502c4038981c1d041c0a1028060816200d09550165281c0811036100b40d100005607012142c190400803600d43d110303170b001c651401c50b030711140c0c0c181031f10b420580a0721740c0c00b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852384379 1250 852383129 852383131
    0x717010b2817010509060a0c0e010e030f100b0f030106050d170706052409070e09130506010f08070f0e04140726070e010b04150905031006050f0901211505 68
    0x4002e00115141c1407040216050650241410f01c00a10700140c0011440c1c0005c207401646409007032145401303050b040440d040800140850015002e08900c1d00a90a03082c1e000c150781e140203540d1031039110070b040107050881350280516070b40591b2200c080000111042d600c4c01c040c00c0002011410702c0c01ea9581c2c5416210305449040d548030001c2e1120485403001007803071384404002c4850a0b81c0742080600a480c10842181e0103000c1d0709054001500249103170184980c00340c0c010225040d640c0c0d100b91100c62014540216800740c0240040007400550802c00c42007941c00c2e500d0b182000d605c4039940c0f502c5118101b81000346030700070180c00088419188041c105c500d2245c602d01340c40281c40f04541e034185041508904807980a010040c001c484425041d01c0544404480c030241840441130140d40035461a8802e5031f140c030451500306640c0ca1a074010310202e6a0540d07026260305101410010401002d000c1c0b400e049192412034030110340310f082d0410b41c030ba0080120920171810340c1200f90507984 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852385629 1250 852384379 852384419
    0x8090f070b0c19060b010f140d09060e03040f051201020f040b0706150323061005010c0302030d0c090302040e0303070806010f0c050313050906010503040503030a0c0e030f0717010b28 80
    0x16550081c0b442c175580000181a0841e0940b600c0800c11107110007007012402280c2d800e0400b65920040c1208005059101102084201c1c4c112074a0326580c0011040c1c008050183c680074041020120218041c14001d4030002c0851011860a01e800d01c2a040516000200107480782500d403481140c0d4aa90840348030043c60062850295a07941c0b10420004484121500c200c1540003a040041c8152603607024000d0781c0007485c20751101039031420200c0c6140200c581e046016031811045043c559084440b640449109490601000c8a030000745509c0c3d010841c1c5160200b01c40100041b0b007981b00c0c100c0303481d1031420303401d00084c1d031420b035150145590401045400c605500700350034415854145e00300c59010741c0c04d203415032440c54646d8030703540c60b4040602100d00150301c8040080120740503607401102c088003d8103c0d0116100c0204c41030752030015110b000c11854031003140500c004018011145500e2014100401d2640760a9000c0c0111205030060803028013030301d1012425000074025403134400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852386879 1250 852385629 852385631
    0x10504031520120604020d06050a0e01050102060a06080a0b040c1d180105010501020a080f040b0c0615040e0703150204090519050a0504170a0309061b08090f070b0c1906 74
    0x20b000c200d010318080007203401d20700c2d4030800d2002040c02c01c2030880b070380e500c0202900d01580703d0000ca0300c0d0390007601240e080355510825129011442000300110076048602c26030072036525450700d074200404c239901800b500d9004e07080145150046242403480c04d0300103204001e101d680f0b9540340c400c0003a90404041041107e0558018408086400c56010303d0814444d0000c200d25407511001075550407203400300412060300407540305007140422040d03600909018500590341c00c8100754076510b03000119408a096510807d800b0b03c9400c1610485c1c01c2042c901c402040300c281147c0301ca02c000b08540b083e01d204560208030114241d00f4900405c1d000e00032006c05585132444044030001a205c004140c500f85a250000304408544020780020443e00014840795903200001411806045000c1024105508015011203940c0c0c0c0d01d1549407072100386560f1345810380c896980c0b664940c041080c9000d1140d0200303400340900e2122200030049030a4103012582c05250b01c548000c50b0205030700e0240c4885d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852388129 1250 852386879 852386891
    0xf200a080a1502211005040c0e090a09030203091c0609030c030228140f0604030801140a0b0f03090a0b070201020316110d12091e02010e0904050703020f0105040315 72
    0x2040110b59540038441c0c1d040190f007002a0b02d500c04840403500150041115012804101c0742030940c080040075040c0a8000d000b0501c55110107040308544a1310140503180b110002a007014040c401c80f602c00da810b034007843c541010501000200407440c1e01d141c4051100d06800c2c1e00007481c610a43d9802c038400d40702c0402502d01c0e420b010341030044041d0700580d2101090142c11982c0001000041e40c1e552110b5108180c003880701c0f107240b130607000d44411615031040c03405000c1030640040e54603040b00c0d0710003032414801d04050148200c2c4c8001e403140001c954810b015032140d140001020355400311ba000c003103e4880e425602c80c003980780e405035400c2000d82d5000040c2310107590713020b203c010320039203500f81807001c1100078134107503a41c2c1c101d0765008041000000304046064020b80001c14481d0f0840c03034210020711031b10944c0240b404020340883c0802c0940360307100042d09141d009644070342c1e00b0801818141f4030395000e01a5900000940c0c5040010822000c0001110b00b03855860703000c5481400104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852389379 1250 852388129 852388133
    0xf09050d0503010602060705161e0c080a020108040609020f0d0605041a0c191e09050406080a170307051c1406090c0f0f07172101030f200a080a 63
    0x3040004500c2400704401000103200054002401c0364105001e0306c1e00580e11040c081c0f8070103058080311001410751403003803690142400b40c41c00f0486001d00641d0101e04003940c4001d0180da50469400007808a0190700c0000c01260351613001100650000d4602815501c020b00060010b80117040c084996982d1102800240240003141210346108103030200a1810507104101d0340380580300340c0708502c8090103420035200e03114048010014446030300d940303802c0b81049009000c0d02107900505011718a00078000440340700c0041c4212181e0380000c99002003602551100306c035030340003c0a480511208029403009e0300d03840018100c451056001c0083d1482c00e0708000038035502c018011911850f8100b0901045c07050642c2150b10321281d440703c036941c4001a050304d04e6070b402818000b81c04410b50381140d410700f4070620010030402d01c141900741c029000603411940c14041c2170101510000040045d03000207500d101c01148801050582d070346004e0740f590009100d6500c3e503041180960429100202 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852390629 1250 852389379 852389383
    0x1e010b1213020105070624171005010510050a0311040e0924060f0a0b040b04030b0705040311040b010201090b0c13060c050316020111010504030f1115070e130f0905 72
    0xc1c2100040c0c0210140e010140c00007003680c02800c00160090380c0c0e44003d504101118003080d800d01000300d0640c1900c1790b40e03011164502200c17a0400b074640c00380e0401e52a400301c5500ca0981031b01c600805900d252040058120745031f4101c206508149680d40440320803042884000c0c01c01002c04050b00101c6280c91748802d400d00309020110070010031841180c4c2c9510011100141e8481b9040c1c03000341000032100c0004a2000c1194441030589600140210710705540c00024404d40f40200d41803001911440c5c012141342c030a52101034282c1400e0b5920940d036107040d80200c910202c05100115000c00c0c1d40e1240703003041c02c1c1502d20628401000407030b00d1811784d2005c1084000c0400e4240220603140a468140e16486030322600b62010a08410403421a0300130311441c0380c03030a4584020040c9184c14a03002e850302017241c12070390101d04003861440703464900003005d506040d90b43c010714080351140801641c900d40e8481d03880790f20855004516211086c24864030390740727a41c1e041d00414040c0b11303400c0c224 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852391879 1250 852390629 852390631
    0x30d0f0c03050915060a180f14010605040b0f04090f060302041b0509060a020a0803071706153907030605010b160809011b05160f1406031e010b12 64
    0x14050609040403c090301034080748440305101c420410140c0c9954080c0018a030f4a00394200c0c04800e4810004080494569801040d1100c03079000c042000200d01c8401d08a41002481868001813041005103c507004000c090006c0400030300320b01d42003d0b100c044000030390701030060a50001c1d0b40e80c1d50410940c6800c0c00b8043c0c6000c16005400416a215800180b451162502b0107000340000550403004a200300710949007141c0103138031282c030b074100054018290a0700d100c042e00704228440201c0c45a2800e41410100300b141904094501b810103031300b0150001c40407103803020801070086c5480c4c9170b41c0b03d140d901c4142480e800103000c0d00c1d4110b01d04101150b4041e0402880030100b80500b60f040091008280080c9401844840e22400c460b401200c9070b04450500c0350201900c16881807c2020000da43d0a106a101c104015034a4840000c2c0f8a400c140e0b11841c030044440b002c203203e040c103000c0700550700800e407500342410119500d215844a01c0080e4004415940002071224a0040105400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852393129 1250 852391879 852391901
    0x60911031005060303090d05120f0d0b0414040b07180602070f08030c0304061107051507030e010e010e041e0c0207081c020a02010e010c020409080c0f070f0b090102030705030d0f 78
    0xc1080d802d019000c41d07031701d009100303003030380168240c001000a026040000f8865203003944072041e51800000c194144541080848004450505180252603e402d0044807214400031807907016560b40d80e240c000340ca01300a4840c000f802080c81c40d000c0c1c51281c081207200600143c2c1c004101051920501c0f030700b1000b242d801078119810070300c000b445841002c07040b541105d920b8600f194090400382c203510b0506a19a00042d801030402c41798603290322071030b00642581070003a11101402c0c4482001503400c903400303441540c001080080d00078018901948455403243c1940c4958006a06803040c0400301e40c1c401c8075110144c1e00c0318604000926041100200c0540b040c811041c03030721070140019554688400c1d000341030142c3c0b061400560392207503c0b80c034170647e001130090002039928100b0703110b41d510201600d581c5018405261192540000340c00044544542e00d000b00f00740f0b00310b1201d0080d008603801e036045010800903140403c4080002c2c1c040f015400f0381c00190740c09040181c0b0304607000e01080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852394379 1250 852393129 852393131
    0x51507110306090f0f060f0606251a01080c010903151404080d06080307150f091a0402030c0a030803130303090c141c200a0b041e120206030a090f0609110310 69
    0x10447c0ba21242c495182c0c1000703040c0e580a48405030b00003648241034007000100000c040ca00c0c7e04c0b20600c803501000f40003c0400c10045281c40e601e4100e0b00d51a03c500407081408203090040400000d030024400e2180900c2c070708030010748614103e0058030307224829681a07410150109000720345981074410301000304480d00045141c140303959106110071a0510341404040d5503104d401c105a00d5a0b000b8410007a03000503c1d1490512405405036904403e4a050380248a5803100018500f040000401030b80d41081d00541140c1d01c0420051001c40000c108a042680f514510300000d0700f480324041c0a17103010304a03000039204e5441400300d4545004c00fa00c941d41803c1c1101c401003408810280c030039902c104104001c404250002c18690b690b01c2c0c0c0050031300b90000800046100d4402090001205203811a014ac5076030707010308118030307540d81030302950080d000c02c049440401c8130741c460788000303105140321400c00e8020384448080341d0040c00141d98500c44a0048540c41c0380034002d0380c41c00c2e290118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852395629 1250 852394379 852394381
    0xf020d0207060b101707020705061603020d020d021902030c0d0803010603180b0f1f0b0c06010f0e010e13050102190e09010602120705030f03070309170301051507110306090f0f06 78
    0x1d40208200c5070300c0f01c0d0640d0b807074a1708007040005100340000c2c1c01400019008a07500d05c40c0048411050200c00400d400500440e10f51505291000c240c5d10610880e6900400003040c024000e200840100001282c0c1841a0b0f00c842003c3e49509050144131401121130300d84a42c54a000a01a10400a00c03904200341103401c0100040e42810144d8101d12001c541040135982d0141c8040032304000328176464400d20384a40090040c10181c0203000848448056070100d9036500e40b04001080540031317200048104200511464030014505a0300c00c0c03940043c1240341e400398031140e00326031020401074030300100082008405500100041d041c1101a10544182d44c0b410380c00a40782c00c400ea8080a200000040710030610504209a411003000707860750075038a043c1000301034001d00074240c048810100c081880b5220720304c074405a038100d4401401c9081c00c4003032130b9485c03001540038245c01c9500d480e0040310244151400c01001d8825a800001092283c18520041c0c2c5000d060304002042070b80404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852396879 1250 852395629 852395659
    0x90304150c24141008010c021c0305060109030c091a09090604110105121f12030509010807110321100b09060309032104060507080f190f020d0207060b 66
    0x307522040d10380380800e20510050300b01003841c0a4050410510101c010000502908500e240405000c491291008120003403240340140e8a8003880d422410711b4032104000404428040c6e0003840c0e0000c2d0514085965544039560f00034012050b8102001a07540c40c026200d05510f00c800e1588000c3c0210340d0101c0705e20f440079205a40700e40040c0f0081c5190003900d000718083c1d00506c19030340080d401031170610162416604a1004229401c83d92950039480e03000081c01000340c00748019426015a00d0a02e4410900015100c5000140c2000d0803c0000150700e840301006101420049060181c0b140418140400d85281d12101815000d64445491800c002c0d403034055040310140d01068a0303841e22035565141650441c003442c0790701240c00c10b4240030741d10f40da44042d03011881580708203000c0140b51200c0310304850401c0304840000d10100c0e07490208002240c4c070074010000750000000400c4a0510540301d00603a08030840e803003106600418000100300040c02220988034003541d03a49020030882c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852398129 1250 852396879 852396893
    0xc0f03162909030d1809320403050a11160b0306011806050d23011205010c02060f071b12020c1503090619060f032a24020f0105090304150c 61
    0x131410302040c00350703180700c08a41c600e41120240003405440d000700484800f03880c4d00a65a44015000c1c0710409280340400010040d61a01600460f0035a64050400748081016264100240c80b1000035210f6202c1c1c2503210070017281542d015100700603010b9120b003807000000d4159840002d400380cad0fa812070754040c0304072039010701900c0718400b9210340030850b81005181082c541d00311240c4071200101103030000c00c0c0489014803607000c0318481d10080100c820754000482c0c41e500c05907130104c17030b94801c10041117590b807044030071500060821480c888001c40d1a0b5a00c909500030100500142e000081c00980610741034030aa0008680aa480d80c03440c40c04d25040d54580600030300c00700d000b500da0100004050001e520220103001c60780c00e402041516801d140c0504e19080700004580d491106c401c0415003003080b03404c81143d45032068000c80318804c1d12582a0100c040c90b0301030451040c601040c02d500024002c641c05000c040c4007940c3d480307080c4000c0c1d030014220030507000c05000210a03810001580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852399379 1250 852398129 852398143
    0x1e090b0a1a160515070909020712030b041503050c0a12080405040c0c0609150506061801030506030a1a0406050106020316060b060708070b0609060a05030c0f0316290903 74
    0x20112503640307880441e0540100c203010b150140c030600c10341201c003e00450075445039001750742c04e44901d566180c0d10700307480f42640715030000145926521040103600074000e80003091070400060010585550352600340c20081819801540c103030784800c409136114280250650040d20f11449644410b4200c0d4a0300c0c9003510603441100d0042e507449408403040761203041d80c0b803000bc0e880542400350045504210401d010008046603040f45048003041162400004a0343d0b880d00f1025211030300014140103600502000300059094001e03c2d0640c80003698102d0b0000031803e910340390380400e0421b410008111901604041c05540c020070040881c05900003168001d140c3c0404080380c020840f502007002070042d0301c0002d045100218104080000c041c0a40b48034200075180c0110300d80d503120400c030425a00e48121a05030f00040e1081c1005e0408030b0b00490b214001030201d0b070a40f03241c03c217030546a00a5501028210710303408882c0d080120000c8440f43c000042c010061708091076000025100e0304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852400629 1250 852399379 852399419
    0x207080301050d020102030415171303020a02090a18050604060f05040c0e0c0d021b010c030b0612060a0e04050a11010201050402100f09050306130311030f120a061e090b0a 75
    0x142c86103980c0110383c1b003001150050030300a9024100c2c410384807006825900c28480403e815002d600c000340c00c905100c138001c0c1031680c0560040c0316a8500790240f00c84d1600c05091000340720348429901c1905400d0301070350001184950300818051405040980844040d600703240d4110f42404144400b06800e4400c40085c3c54809101c160192200e00f14400203104920031005498000702c0d61464520000c03013080303100e030800c0000f44044090420304800b02c842e016000d50380018144150141504266102d40e030080d000342c03e00c0380e440e48135902c8100c90b103800c6800300c07620b034060003400c0104004490704150404081c0000c0c00310b400c090740020140541c80e40c00d02d04104054600c03050907881800c24900a1102401307030b410905140d081030544031620802540400d0002a800b014060000704030390002100200341030800092a1200204902c046c15500740280c4900b004aa0700c0301701d44202d0721040484117030035011403605500405030384403014042d2180000d02000c0011200c1c11040b0043d01d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852401879 1250 852400629 852400639
    0x3120b101d04090b060f1008070c02010207080708011e020a091205010b0d050c0a0e090a0809130230270a050304120c0e07020d141c0c0e04020708030105 67
    0x348003001c41c030085940411045601c1030800c0d96000500c4200c1000e0b83c0981c00903140600000941d50074844100d404a0030040051031200004800d5841010b0104d02644140305641e2088d6a920110746480303000d41081c0c07500d035501d824652180403000340c00b00c45008016015410101c082c40090140d2849209041d090208801610b040204c01c1d40301d0f1400540040c5000c130f20440703e0809669a40c90302c0301207401404400c00200b2083c818403000e501c01c2051074001d10000b0304079540c1c1000703500f0044286800c500369104102c40c2d17100c1d500107807404201e484440d060340c031041d01881010b400d801440d50140780640046c0100382c20140c10403400300e039a02c03450f09009008800e28601d00715901d40c01803c14000820040b402e00d01104030010107900030720101d04d216440701c0c030001d20036a0648003103000d81c0c002061a20034038014017040b122100c5a400d842e003050103412201c0040003480344941c580940e00c440441020750030144040e04071b4401d850440c202401c0b640c80901c03610040c0250f0b4454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852403129 1250 852401879 852401897
    0x30201080417070b06032811040e0f0115051e010e0f100509040501050301050c0a03090302030d18020108280b0a091404050606011707180812040303120b10 68
    0x40000c04a030311180d100b0303149240365a98424249040410420380c1c081b4400c1c09500d6407042c101001a41c90480c284c8030a41d0007010740c419a40b00381e502102040c81b5500503072280c400504002c0140004c0c607a082c883c8001040c03a03280f060080100c41c1d66500030a1140726039009246121a01c201c040074556000c1c20400c01440f03881d00090a90f00004038000d501c4203050350301c000c0c03141d4040090084590192010300050341c8580c20942a0b6404880220100b5000e121500302203100b5001710394000d0181c010341e031400300b10000480c252460f4501100010420040010443d688442400c1e8072494001a0307540348920304040c3c01c6801c03210002d1021301d948070540c0c000c8954038996140001e2070a014100300100304020010f1101008440907102030241000094040d40103941d00d008081c20303000c03250303050f0b51500b40c1a15002e55100c1406548c04200d00003250080080100807000c8034019852a01c0d40c4c070f180f900420302c401000d2040071440c1400b06d2071409032900740800c4180041d0f41044807030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852404379 1250 852403129 852403133
    0x602151b0d09170d0b06041a181818060601020714040e03070c030212070e04201203040f050111031b1f0501062601090b0d080d0606030b0a030c0302010804 68
    0x1d08890302e8040d00d5041e043c1c02d1810411500300040500401903601400700c0000d4600b013103298017942c03280c03035030f94503445020b0900a03c8030350060820b07038120340c0219032032041200070403513543d4410b000780c1c00490b1440038401e1a904c0a9041d20740350084c0c41c0100320525002000070b40712000c521444040c403050240040c10f941e00c0742c02608c2d07041c4024007125201d800c0d6080260b40c401c400e02c002e074003901d40c0c40c1041c180000c0100ea6401611703c109040081d58a483e43c2e620700140c80070070004120458125058001d58038121100460b10010004646503410300088403c810410b502c098140141124800212440403040d40c2c84201d40010710034022290201780d60a00c0d03211b0300e92544040d0207140f80c15400c2e03807550100341681d000f0382da00600054005880418140c2400c600700c50302d84030000400c2a4115a002000765480240c0044034511059a8000d641d4000d1460740840c103441c1c030000e1040740d41c10712a007401841c040b1003c44240d890740c0c403084120744403400041c3c1080902c2c000501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852405629 1250 852404379 852404381
    0x141518040c050f2e05040929031204181b080627040221030c0d02010f1404260a05030a0b0102060c040b0a2d030b0105091c050f010c090602151b0d 64
    0x20802d41760244000100c0c0e01c4240b08c203030000c0758141c1c1d1034440f00700c80e4622800e000070941c1c912402d002e0054542420480c1d00c1051036007040700309640940300e100103149000c6840c020b6071145125250200a410640c0403c00c4190000150002c05c0c1045106040c2400300c07c1203080d00290162042c1c65640742c59202d251a403903554021254501c40080c00108200c2c0000e25403440407955802000780c040d12010300710980d030346400c0f0304128002100114012440e4407102e81070400040e140240860005580c1c1c080540152031480c000c11030120404c0910352060058081600e02480500141d151803c104001d50241d80a9051208008110242102e006024210032850000c0201000744111007402507024141e0141c880081c1c200329640305254052010f690318448000d1010209680e040c5102c4c83d040c1600e20144e540b8413912000199000303080c401c3c0700e550f000035905c501c0340a04054000e4a0500401b040716404146a400c120000d410702d0090105d5001c003c0000395601604880700c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852406879 1250 852405629 852405637
    0xc0618040606110d1b080a030b03010f140c030403080705070f02060d020403140d0917120c01020901081b0703030504030c051b030d03141518040c050f2e05 68
    0x15402070314048000c00e41580050440e00755880c00310880d4500c2455610464294801c1c0310040c500c0800005c407280050340c40360180090540382e240000382d400d0f501000900b5a2003200241340e04c1a0765030080c080c1c10309501509035000904544251450400341e40c024101d99000746000c0812401080b203000708000600f856009580080000b42c41d030324040490710007580944401c0320320020000c2c00c48008200495030250a1900f516415045460542009100510745250380d102d801400c020b80c8005503c24080d10400c06c010000580b01e011041c005040300034060664500c46400d0b08500100917080c0d01201c100992519000c5000e86540c07a00741c2e04800843d030002c1480c054400d254000344000a0714210f201011021a070340766079800800d4040714001502c0c454004596170002c0c0404484040038a08048040c2c80000002c903030b5502d804210704180d03000c0b2404080035008002c1d500d04901c40d446420310440d008045114407110801e580b645004032041c1c80d43c0100c0044c1401801030060fa = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852408129 1250 852406879 852406927
    0x50c0a08040c0902071514070c06020c07080f010617061003110607061b0e180420060d09020a0b0c0d0c020310090309030210140f0309071716170c06 65
    0x150348401c070310300e45a4130020b06036140280c094503001c0369107121802d00381028000c05250300c4422a04849e0340380e03038001c1d500100200702d8510a5410010f59103000700050074560300040000209542041000320550b5000081400960301101c140849404c100e504207044039841446400d294a005012901c00d000700c1da0064a075500c1c11003030348110701064400800c13241e078a0351001203800c0604100103d403180c00c001c1920700003280c0c0c0058005098803030032000f180d90710b580c82001200700a0005080303600200000220305c0d1598041000c6080040034074014140084e034082c01c00b004040100d03a2906180201d0707081141c030b00490010340d02c0074840c59001c00da03c1c60091100c0d0030030f810043d000760140d100403401040c4902200004501c107030700d0000301d000400c56203864100c01c19006002d07904054515401d5014090000960348410710003002c0e41101ea4000e440c21030b140000c1c65038034800c0341d0700071502c07810244410005104049040e2090190031140a510340c152401c00224014100c404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852409379 1250 852408129 852408131
    0x1b050318150f091e1509010603080301030f0c050d11220509071a0f0a2003030114030d02010902090622020a110d111c1e0305071101050c0a08040c09 65
    0xc0c00190a00c01c0c02d001d105409443c200c81c150710b0301c0300000760001c401c96601c1c111500a441c4443e5070944041901d9086460540085499900ca880702c01e8207610070f82c01140c207010104010010000c400c52240c0040400321807003601d0243d1511044140301c00300046600c100340502144c1800e82d82c0c5250142c220760350303000c200940c0c0740c42500143e42c0c11081c0151903003100e010486c2542c1c403013108101d9544050b82c0142d181840303031919094074014903c241c049120403004150984140080001c1c6008045090348890300c034140310f0501d41000192030f41802164100303040200541c8804e0b2440b81c000d0700540310346040883d00141c54940e808490b9002a17203d00004600400b42d52000d01601d00080c5a004d03206000c0e441a4207955089200f1061905900a4448400c8001072a54010816001805c0407081061110409242c1200c45014400404d6458043c0b2407615408910f2424100d100c4000f04024205091001130600810342904e0070400c2c030400003410400b805080d500100342e5008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852410629 1250 852409379 852409381
    0x7090e0a122c01140906040e060315040c170a030c12030b030f010507022503030c0206190c3e04020708040e1b07080a18051c02041b05031815 62
    0x60020b294060341441d140021340f5004c0000c58060f0144c22240c4011005144510302454070307201070b0740980d0041c00107034140611110a240e500326010400c2c81a481a07903010031460404864a02460b1132041391320306079018400b00c40002c0d402c40103c841058000c2800030000c80120300840240141203c0c0e42c1c0c2502841d040d6400428054000324045d046a400341d0b1710a200820305903049407a5502080305180d131061081010078002c02c96452102c0c00584614601120040d0500e141c41c4640c3e442c600250b1806105400c0c0a011034179520394501c6110790500740d000d041450040051002c9190b004003c2542c9e41c241207955a50440e42e6059001307076520344a0382d1340d03a801104840c0c111522842d00c2c12044081911202c440200d0301c0650f408040b0302e05002c003411044443c0360729400000b0307000c0329010b008036140e501e07541c00d40e007401c05404080d0300310f015904c140010f41e079151001940e0078002c054001860b41d005000e41380c1c46940080c809490110b00d00b501458030303c00d11022454402418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852411879 1250 852410629 852410687
    0x4030c03060c110d11030d0203090d02010e0613380a0f06050a06031505060d091104060602060609070203071b060e0109080c0d0c080d0f0207090e0a12 66
    0x2090a20440e4000c403010032a28012410603240606459441030450b0000040c01e1280c0740100e00221500303a0b14000c84c3d087c1101304050f8002c992003a01d000302507034040312200702e0741c0394240549848804050301820060601d44114204850031200c020541156020302582030140720301409110145264280070883c10700c406c0d1100ba46095070a6070280381440c144c51105041e078040c210071140701800c40c0f0429403034034104800816501e14081c901d01850003000032540d42d600060908900708100c00030340031109140200c001e00321804490300407030910604000c2c264001c02c01651200040c0e644401e10382c2c0300c83c4101d05601c0740e080c00030b00301c2205910300d01124000c0b14041e0141c442540b2146007a0b091680151440c244501c1120001e03440009403d4090402c603c0c5001c02500c030f0a20442c0c029141e4502900340381188180c1d00015000100f0658500d504005550003807007601c204009010751341d100e02d42c5074110b0120141c5049004510798003c02d10503070b040c00142c4201c8966482d540c0d118 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852413129 1250 852411879 852411893
    0xa210f05061008060c09031b040207061a01090501180504052805180604150b010302070503040806060406120503030c0a0e190510090e15010905220c260a110403 70
    0x50183c5941442004001203c50310f56000320340c02103400030028882c1960700402114410b40700d50030343d500244c080c0104000208079010780080d1030340c80e070307200c0161001c04000140100143d030702641c10002c2020002d90800c44040b140002d5400a9402207441e81e20a102c0400d201c841c1d16103003010010025031031202c4165035005070b0050103400c03505490186e00c0500b2035540c403015503005d840c0e2098901000700210b001e0b40115496101814003604200c0c40d80c41d042d0441c1c00c20390000f1240c0c0c021100304040e40c9040c0c82900064154010503014039004c40d2a16990f034000140003078602d190001d149909103000342c030b01c0c41c40302e10300425040e1000c0c40c03465407001d124a248a403030700400e142e4441c10815801456a207042d02c0402c0c0c1a46000da442e0741c5100d908a00c505075043c1848182007001c50551921550098405801d038206241c0c0f24200585808480c001c900130030402160400015035500c94043d900d04000c02d030645030110b900c070608103100400c3d840a41604000000400104020030b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852414379 1250 852413129 852413161
    0x3020910180b1315050a090501180207080d0b040f02070f0203060703020301140607020a08030f0c0c0607020108150f090a140603070e04020d080c0d0507050c0a210f0506 74
    0x440651800400d1038408840309030b4074004049580400c00c1c1610810a0307809510000307503a6a44c2d90f10580c041c0d641d50100f08102941d030090110152034400500c070366402103d18448507020404118500044ea46481c00603008403001c2c0c154240d115920f1106a99841d0015081d40c00c0c0c0ca1021556034003107161146000c801c60f03004030b0080c01114001041d0074001d1007541c1c12900d529451401d0017640404200305a40400c2040780e00c00600c070408506940200080e014401e80010402e550384016090309240501d030a010300d100d200f04000030700050341c0c480182d80e0030020303000c035551f20340d0021400180c109400100154000d285d440402421101503000001401c160900f09001c5450b0141031640b6502c3c01e01031080440c074003801160043c02c00b1640010382c0381c01404061300b42418440d4050401e01d5400c2c42c2d000055021038000107001c1c042c0801046483c040b60307180d58070751425a10a03840004845880003000c50103000360244001360500300601c60f880000d860407440e10032144458000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852415629 1250 852414379 852414389
    0x50c1006060323150d030311181825031b0216050402040317030712060308040303110f060a020c01150b031f031a100e0a060806071412070903020910 65
    0xc1d00c80641204900d031503001e40141044104010340c02400014000103015488003107003055601e00c00d2804000a000151044d14400e27480340c076000044000300111b91005039070441c11020810144084d400d000000c0b580b000440c021441d03000105c1f03190950040400082c198055071030b070009420b0f0284e004c26446507441b410200c064003144c4940c04c2c0402c9000354080104618010000e201403c0c0c0803002942d0712403081d1403e245103508001e4a04140c500701d900441d03118070040350501c101504118003a03a0811000700400c0c0b60310101ca0719030303034866000c3c01d003050403030b0300084040c0144020b411128070189031600030340e246540c030490000750750b200301d654042c3d611410121b0101c140b49004140105ca40100709014201c044045403d40200301404124841801c400c00103501528400058410425018002107042c5000f034007900300200101010100241c944240400300c00c05425200d50b0010051074202030f540b00203042e0307000c41e003540000c0d40c800402d0003002403840a03504598103841c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852416879 1250 852415629 852415661
    0x3f07050a12090b1c020304210201021207030b0913062c0d02010b01140c030403060524010809030f0d112212030504051903060c0905030609070305030a050c10060603 72
    0x103603a01c0d4000d0680c06034040d13043c2c03290480b82c6054404000360b0060341d00700d8041c8403189000f1100004404550760600c2c03000340542d4000c2010030710300b15140b280c07982c800b0301da040034400902e017040051650300c40140000064081008014288621680074480290f21440300c403040c591032440c40181e403001034500154600c51160f01a0301580b042c0228010903206840e20303000d502c0c50b80d034003152607004281c4071009880181700000220b10903004070350141291800d040400a042614101400d001c2d00290303050144000601110100010854800102c0245079640f1510a444075202410044040040104011078a01e0092a059204a101d04021440700c07a005a0351040000c90f0888460040e01080052000300110705100d030428503425020403282c460203460f650359000f00d0700c001c200c00f0000b4040f410140310340d060403c081c03600082241c0092203550b1030f6540b05a1b0340e1040c11a0142004004100200038140421030300a001721400800e000c090f40b12400100101800500f81280c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852418129 1250 852416879 852416897
    0x1020d090c09140105100c06061202180714070206090d1101020d030e06060607051c081905010b070f030207080312070e010e010212160804030c0501023f07050a12 71
    0x8504180318440e4520140510040c643c0c5ca4403080292401a46903108140000700c1400c1000540d0340c80b8030000b070141c48006084d50390301401846031250100703000e102c00c0340f2280184034810340c0184240060740807800300d040e0344107014404901d01c1d0041d55107098205501440d81c20403c0410f0102c28811042a800c40705d4540200c0800c40959054440186480c3c2001c03001c502039091201c01802224040da045132081030700c1d425480349800807000100000b0f00300e681032143ca2100984c407003040c13044205d001c1c845c81d41003071400030107440360303801c000d0400c008501e0b0001098000d2080600034090107085d03e0311410110854000700d481161540e0000d06060740740d2903a58042c030301f0710180d4001a4010448503880c24031402c0c580c0c5c090790140314002801111100000c4402004002443c8500c3e422000d06192500182c60302d0380c5843e11f0700e0414900a540c41c03900380403054019002002c00d03201d943c40072190041030118800d54101071308500074001c1000600070140080f407442526607983c5414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852419379 1250 852418129 852418139
    0x9051c02031207050a090b0307030c09090603020105040e06120d1823040f3b07030201080f070c02150909011401090306110f0a081b0711040f0b0301020d090c 69
    0x1a4454000e03550400d01018012400081c1319401615440b8041d06182501ea40c0b0380c603001d102070308116410340010791502c5e009841d9560141040b0300502855109000490031503001801038000c078010000c4a014800c00142c1503910b0a02042d11405081d00790b072103103490080014822070702c0e00003c0c50740130310b49500010703040c880c189001c1040000d010a6001c14044208010207020000400303c1c00580703d254030070b444040d10869200c0c03140c204902c00c03090f50000b5010142c041d03080c0644285c54104400410250f42c001a02c40c0c0c2c45082030045072002e64928500781c89184400c0806500040c0000c2175945104040005050260007140c2c860116a40c0300d90b52403101603c0001140056081c000800010b805a040700c400b0500e074000290401c003284043c59450340042d921480056410300601032542d092006065950041da441c103850044251290801e5400b4021541c2c0901e42d10380c1c81c004040503680c003c41056200500940d0b991070200b0200340540500c05054030b4281c450400012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852420629 1250 852419379 852419383
    0xb09011d0903040e04020d0311011a0a15051e04090513060e1209010c11090a02031b040f0b030604090c0306062102031b030a08030c031005010e031209120109051c02 72
    0x42281c4460013150030580d269401d014840018038411000c0c400e4580100c0d18500081c050514101e429441c415213a00140c000c100e0a00f40c4d41e440a13584c07c000b11130743c1b80c60a52005c12211290707000905000280a0304c2d1b075500c018030840e8081a00185000e003440145a00100c40c81d00141c01040b05000701028040b40c0c07a00c4151400050950344010071045503194091401803030105c2c000d080d00040d0350040804500d802d0421102c1040441c4d0010800200c072404101401d946da280d003030f4042c01c0c03d0501100081d1030400d0300660200d20703000f10000d1034981d01d503080002e0999002050a01d00d603642c1ca40200644028081c0101c0c80a41c07003551000f5482000c1030344c0c102d40c1c000f4010300040c00001040a807248030020400d0b013602603540d424002c034080d800190b02801508480940d2450050005400e00d0502d41190741045441c88400c03100d42d500080380101c82c0c5150b00c0303c80d030b00c9149500082c103003503070121074484070750034941610705008000c04c031342043d114024800c0341705a844c860101c1e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852421879 1250 852420629 852420637
    0x30406061508010e1b16060612171b2521060203090a0813080d1e0e0301020d11120c0c030406030b1c0b070e032e0b09011d0903 56
    0x1000841c14001001640202c494840e00404080384440c0c0b42d04c48403460104503440810740c0c3e01b2030303003034007202608028075849110300400881040c070080040035580c443c0d5041d05034207120072881000c0b8418001310446444000e034074035031004440004841002d040000302500c100504884040b10001a005c119008201c944092186000301c184590380d60b810020340010f40000458803603680000d00141918004228501c0038404508141d0300d0501540d10f01554228008100250342001803010012940c000d121007071181401e004800000740440d0090249403010500c6502b85510080941c14003402400032151003450610304d0b42d0350000005051080408891312a40200406c200481c0300ea4040210400002d000c26181060744240700f40700019000241c030240d00c0c050600040c41d40010441b150102d040c0c02a000c0c1d0310408d1a50380600b100d8600c0420303401401240980000f086a00c04d005640c0300600445165031103e043e00c20411500c00e0140054907103801180010000005031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852423129 1250 852421879 852421919
    0x50709050a051903080a0909060909020f060a031515121a190b030a02030106020d1e0c0302070305120405090a1109060f13140f0910030201050f071703040606 69
    0x1c03580342868030040c00161581000d81c1c00c00c00e00c040101100140042d801040c00182d1950382c500000c0c200001181119070b10b52103810010700e403110f100300585403840034a410141c200c40543c1c5075401002c0540103000a0108170121114020011528410100e52400d00da070326540c814203d008015103000403145174002e101d07610a80255202c600c0d15028900b00d50b40900e26817521600f9545003908a450307081952148801c54000c8018004141d04208030303c030341d95403403404c580c84001102da480001d941c1da068040410400390403200505000b0410407004542c0001140c111007980d0311196110b070400e0103407501c01e02044000c290301c502180900c24a03051030250b200d02e07004450042001e140c0c402c850340750ba00101440b03a1155803074109201d900421003202414810301420003003110726002e80301d00c5072182803a80140f01d000c0f03051a040c0c0e01600e5081c01c00507a80c00c05003840c42c0507030080b40401801c61008000c421741c591500c50245000d5032203a10b01340400c6495510600d500007002c0d000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852424379 1250 852423129 852423139
    0x1e06040f0602030403050d09050a0201110114060f03030405120a02040b030303160e0a030213140a090510111b07030c05100503070e0a150c0c090e0706111c1205070905 73
    0x1241001c900c09500950f00148079041007890302c0c09504000c0251080f4810a40700d83e0003480c000025940c011f000c0b00070403420fa130700801042e044483e03403c00b40034024012034011039141001040c2d60302d0803c100c41c081c0030001d00105444400c207104958038241c0300012802361f400c2c0070a444140c1030000a0701e01409018154003103c100c2e101c4110703138105030a07250591007108441d000025072192001000300080104002c0350148010140c28800d5101030b1018202070320b414454000700c4c2c0d0105612a510b281d6210104840b4043c1d800340303216000f10714401c42600c000000b881c0024000040c210102c03441540d00c06d8245554008003c09186a0804840440c0c01040050901d1b071203a604200100b500401100c02a0788420f02042005904000040815440001d4006012030000c444000b015445130500c0075480350000b00341c80b20807a10811040c0703c420041c0030300c5058203110101d516100f0b81c448510070b084410000b03081c4800c0c0c80720075003403510702408295014410480030003500d001a01d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852425629 1250 852424379 852424403
    0xb0f03070e161e05130608100e0406060b161103030f03070c051c170a1b1b051c030c1d060a03110301060503040201020f03041a1c0e1e0604 61
    0x3081456200c91400301810050311100034003942d08560f0030300300202d401ea0741d129217803030300c001c05010790681c03540120051081c400104660f85144660303003001d4a251100380c26950b04c0768a40074000c1c1545401007514801c0210304096116004000c151000b03000d100d80075000c0001e50103040d140d10403030031075800b465010800aa03440c0e002d007004601c0035205400b00c0b0000349006400781102085010f0316400686c14034040c0485c80c00780012540c000c4080b440c10401c0700c02d08051030f54441a02c104442c1070040048911409000009690aa140d045425127042500301c48100c0010011092040046454054021803003442500d441c1840a001d48011940510100411071242c0000c2e2581c0c0070144c8a503c6032500c40a002e001c0d6008007401d40303c0503145d040500c000390070440c510b410610254020b000030442e0b004046108000e46005020140d03807075040c2c2016248008400010005d401d0410144c44c1109070009480e0340c44903507000e840c0781e0160000b041c881c0c41d140c043d01d018080c0300141d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852426879 1250 852425629 852425641
    0x203040311163005010f021e0c0706030c05040b0a0503012d1419080607021c0e0f0a24030f020a0509090a0207141501061b0f06110d0b0f03070e 63
    0x42045140031103050040141c50880c0c1c0c03a1403e448066071800c04240d0041800c008e04007215012150544240410303908001014440a6660030035108810426131200541003520740501c04581c007900e80c18010542e543c0c2c012101400c6503000b0300c05c41021ba80b100f001c12462105408244801000350701111000514000d1181c8401d1400c0044680c41001d5000d04005100807107004001809040080c00361460700810103420b084000c00d000c42018100c0560700d03121a408003c40400c0c0508944800300c51a0341e0340030070040b454a4020501542c1c2200c07000360002d0b00c0c8100c000c54509590b406210074000c00300004143d005901c0b4050210b4020301c49100a0b2074203259031540001c0000c0010b04005403522452686040381d030340c484c5690854039a100340b81c9040040d281c05071030242041d8600e20030340403c1e070310780c01107000c0f000d440c4090f6042c0c80c00800c4080d400c0704010f44c10181923141c403441c0701c89100e0000c3c0103114807540705d11410024654507081c007040d40821903202c4020030072031703540b20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852428129 1250 852426879 852426929
    0xc12010501090b0a0e0307120609020a152a0c03060e0f010219030b1201060b030403031b090303080601020a0501060b040821040611010912110c01110607180801020304031116 76
    0x1320050540c107014847c000315054040c10f01812100340120720100d00c440300340c01071000048881d0003880f01c10510400c52801d0030b8101100e070300880030501210520300c0f100e0455811960060743c0080c001250080000706014894203c115401c0301441520761404175030040900702c0c4a40c3c10b00010103c514046811000d010380d210140403c4040d1175210080707114101c00d42102c55603041150042004400e20042c580d16100348011208400342d0300c3c81403024000302034200019880010204038400002400f90391083c40742e8182994007500a01059889a035100743d00d401c140035900c0c191040c002100c0c51310740c130708c002c000718080c481032024500750420900700c1c0d008441e40c0780c0e19141e43d00d81c03140e400080d050065141d80f010456580043c054078205001b070521032052820f0f07041000602c00b020b211000030a00940118460070312500300c10503003032040f104820170342c8409125403000c0300b00800d06400c6141c7c8241c1d42c0864040d80c1c1d510055040a855906d42c0d80183d40d040021040b055400c8082 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852429379 1250 852428129 852428147
    0x10c0e010f110a1e1203020c12090d060f270c091d0d02010c09080609060601050a02010b0d051e03030919020d0b070c0c080c01050706020706090b0c12010501090b0a 72
    0x30b0791040d50201c001c640c0300c0d11010b19040c0d14400e800030141c451303041809100742c1c3e2540d0507172281c0780551510750b02e000b039540d890400c0e0b000c20782c801e01c000030300420320743d6000d5807187c02c180c0c050350501c1100c0b00040c00e54002d0400030082c0b54000d00400021040c4d0311280d0080440c00e9000c002e440307009040c280c905008007070b281c4002400751501d0480c80b1203807100704021040d22400f90300124001550310002048101d16a0007800ac903840b04040c003040c0580464007690004081c607101e0344a8001c8003080340505603040c00700b60080101c0c41910b00744038000c00c0c6000800c661281580c014a0750b488a140e0301d200403114164150004c0410200c840280354040a00c0e5000500e600401e1000b5242d28841190982c0d018001c160000d02c641c08000c551901074006040c1d040180c4600710700000040c0c15071150590003007a0325400202c0508008883d40522003203500441c810415140090150440307600c6800c0040340c500348034000280c0c1c5d40c4030f030b03075050203841701030f10828182549034100b6904108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852430629 1250 852429379 852429407
    0x80307050a0b1b0d06061d010c0f2102030322020904170d02120601030606031a09060a03080403050a0302063103140c0307020a0b040302060316020c0d110102010c0e010f 74
    0x43d42d0014550311150003018001c1d100c110100012254a00711010308401e0001c0654200c22001040c8240540e0304890517000f83c81c1c1010503038403452900e1034402c281645054400c0e80421848680402066002029520501c5040c0100c404200309a5010482504c09007000398050031480008000a4810103c003a990b9101c0440b9401c00c1c00e81e4400c0403d0340c00c40c00e403031a00458110200a110769040c01900010402410104000e803030003034100e15450701d400d10329401f0302c01d01d40c003040c0c1d10348525660301b0003075812800702e503107440e120700e00345032646800d190030b5005108640104044840011080c1c2100070145003040f1001140054941c400d0040c2e0010b809000f0f00011401c95043c4010041414507000c50155543e0703801380c810480e001103160000445044180000c1c00103845441c00c40c1e41222400200b1141051104402ca2400b02100181c0f900000c0740c6e1490010010310003200d003040712098000388201c00c00391a040390b0340780d10b1226550004071140500002e05024500320700c2c40354 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852431879 1250 852430629 852430651
    0x9050d1112160228030317070801080705010e030304080312042d110117090c01030e0312010504420b120f130f0c03030e09041a0a09020d050c040501080307050a0b 71
    0x42068481361074800c01691003500032030b00c1d095011001151200f0b000c0d40c04811401c0c080e1065043c10401992400d55003d09414000c4c40049549165001c1050307400400300c5070126983c0707030049800e41b000440244c808580c40348614001502c1d10f0402120001c40281d10300d14140b800060381c64004c4070310300304074109040c4282c0c051a400c54601c8240c0c078a1003114107000030501ca8045000040459078501c01c00300654000b0700240898a04032030181d4115070b0110b074007140e0494002c0c0d114002c3d000d400f0030213240c04a0154035074502c0c00860712100300c614455040019060341c807002c800c414030034001d1029041d203007000004c0400c3d8000c19543e40014480c1070200104001d40c0e221080c801701039009442003072021108004041d80918003542d080360550380340009090036030b01e00081d00d03049088140c0d11072120700083d18039809d951140c0d0001d6001400c0c0058840f01c1d0802540f1002d545280300d0083e420600040303001c400000486103900c0c3d10138001c14164080d5100c0340c003c0d25000c1d01b1100c907a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852433129 1250 852431879 852431929
    0x503150a0f0b1e0906030d0e091b0c01090c120f0f050c0a0902070506070201140a090501111b010606080c09040504060f020c0319140703050c0109050d11121602 70
    0x40c0c43c2c0816508410341c900c00380c842140f08040401861480c01001141309a0111403101074007540803424450740e981c1500e05030140c0c1c58070f00501d0072042e0701003031803070000b82c3c080ba101102800540044d07100c5ca018003c82c80f030480d100d00681c070a26004d803d0160000804800703038000900ca140501e000a400b076802d94845844041c0004c0c0d020300342d60b0100400716004102e550500000703010305904014a40000c01c02c1c0c442248850855000041c02000301e59074034580368051010a4100c04000c0314a409101c0e92107001c6c04d0204840b290aa100140381d610300326021540038021404a805200c90301d02c402c1c1000d103400b0800002c0e1600030000c40700345860b00c110f000f1210a90014240c8610150301940d19a06480c1044070784079260f14040c801c0151402175224002ca03104221403d544c4c06281880e80d40c100070040c24094400301c000180984505036200d90021380c481444030001c0302d80e5060761aa0b200307481280c026401030b48941c000c80d40c06030007228018078107042c0c45000002c101c40e05e403c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852434379 1250 852433129 852433151
    0xf1503391009051c020907050d02041a0403051b010e10030b0a122105070609061806060f06030e1b010c0b041208130308042004020c160503150a0f 64
    0x500c0815881903000c00c0002e1402d0050380740a25490440c1031040c5a00d048010030394000601904002d05102c4c1030100000e14420005500d8044034054522800c101544040b03003070408403250b04c10310054809001d42d111343c40404031295102412030005a5a25031000703040c000300850310b003000d05182c003403680e980e00c1ca41d001e44035110302c540103092445a810981c05681000004140440307203185014051119414600d6080f0080c3c07280d60350000f00018403403903103150000060849041d00383d000413101c18060208146500f01d481030f20281c0521950441c0e0b42c10041e400d40d240300620500c0b40e00156002c4155180c4400045403903a414586820b40384030949844211000982d42981c1c11101c0450828209030031642c103d4001812800079501100c640e24000c00c41140a04001e040003041200c41c924090301c8200703461041c00081045554501e00c211307603641c40c40d098078032500e0703c2c0040c08001180d1401141c0102d15140007810f01c030b110341c0c49002d908001c110388005145603076910340c00074403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852435629 1250 852434379 852434389
    0x408061602010b180a090804080a1103160b0403060c0905060304030302090301050f19050a0e0118020301050c09060409020309160303050a0311181e090f150339 70
    0x4000d8450480030103000216003402400d56a5a8100a014507403900c50b098411440b04802a44034440c80c01c0041c41d1022071820f80d1092040354042d075158483d15911a00317001c00b82d41c1040c46036000324100e808000d041100c010242490f032103240720704d140900c41000401c200e07070004001303500c0c24034240d10101e80700c01c0051416002520203400195010542c655241401d10800d40c2002c841ca41c0e220180c0b502d801e06581500380c4100b000c00f055211700200314945215040100e141c10450024400c512040840344428106001e00b42d20030760070304001c91019403051080302c404a03070281501d8509410008075001951000c0e10b00b800d5880f9141807001c07646404c090721b001441c400e54540e42da4000e1110020180c400141c4000c000d603c04002160480d2010009507440c0e0209441e41502200781680c1c034100d1a00d640d0707510f03800072081420001c220810040c11481807034410000c000369114034082c9170765858224440d4202d0102e14042620800d115840300035940b05441c2a20385801c00100070071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852436879 1250 852435629 852435631
    0xb0a0e0a080a0908060c0d0e0a0512090a0b12040b070e1f120608190807020619020d02010c05090d02030a02150d0e030c0c0603070513240206100e0c040806 68
    0x962040004120240d5031039010f6240c1d4002c0001c803009103031604141c11030310800d1084401c0140b580f507580d010070364101c80070f10000769002c0c2c00009603100031101039247c009550003040307264411101ca080c04613410002106485181030480115041582e95039902d04035100c01520307142c1401084942240359568400840c0b0725148820f9001441c0c240703910001c0c0c041c0c10220080569907060034014040130f0302c0003554408a460504007000c030490207040c1011580325660000c0c0d00844005000e540150304450051040c0b400c3e9421940c511003040822402c80d16400e5444d00013650400050010741362030b011100f807103800102941c0f00682caaa0006e541d0b8650303203ca140181d0404070346400081f0340303232003000b40e0040c402d2f004d949040340b01c82d0500c0d11140040701540c07140e400400802c2429108105a905031810f0041842d0302648075007890034030003404800354400d28004080d20300024408034a941c090104420100401401c00e04804001d6000a0101c0c0c40400c0a01c40050b400200f04000c13 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852438129 1250 852436879 852436883
    0x2031519180207150b010c0b0a15090c08071805040b010504090f150812030109050903041703030a060f0b03070e0f030a141c051206030a06092003010b030a0b0a0e0a 72
    0x43e520150ba10303240764495410801101d04034946562215143d030064499910b9503400110041d440da103030b0200200511584e0b031039240c0e0248203c400308046c11290700c42d150b5800141c80f401ca5554076064200c038103a10031000705201070810313181040316007881e421864a151050410904068913200010704807141c030b40140104580342e141100d043c8240c4020074011f0030041d80a00300b0804000459503040c4810b104040704c05a58800043c4002d8090064401070701101100402c18248481c085039640c00607030302160030524015000030585103082c1260112820718a80320b0640d9a007040c00e54044d90308070029074204004d04207e13a003a0b9000d2001212907485002c0400c0000c0102458070301d0300702e1100e0100c4041024285001c10550044e058072035450036003101020342e0317503000b001ca400c4c4000d0700c400030324440c01c0050400070060640800a828001c20401380da1a2121604041c242c80c40380e8607058154124082140118042c015403ea0160b410034002c9110303800141200d00d000b03140141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852439379 1250 852438129 852438131
    0x712060f090f150203010b070b15060c06010303021513030305040201020a0615060e191707080111220e06060a17010308030f0f0103120e120114060f040203151918 71
    0x40b0900300960180100c2050420300f00071415503042c000790035081c4c1f003124005000e40b070400700018218601e071542d0313400142014240c2030f200d060f1240c509079250030a0204074054011103103006007001d41d60850501c00d0482840424040b80c468a09500400300034105074114040d22000c41c0c041075850007440c641482d50b40081c240245007880c020404400403821a104203005510101b0896261441c20309940d8a0450390444074980074400d4980207155001c0002942040040411350107000b0181c03141035060714190259644200d1000a08680303402218204580000422024105800907050407201801c000101e00d1034036600c2c0410201c26482160f82c2000041080300102c50300c9084c0d60007203c40100c135030155065542e940070030380300321000d8010030040c040d00e54106d0759601c1c2d90003e5403002030003c00c810410074110180100702141c0c038a0040d201120b80422074240703842140e10480f02050b103c800d24494000b080441c2e40c0c0b0740b0320200c46001002002c40c04c1900705030580700410078260 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852440629 1250 852439379 852439403
    0x50901200f0318030613020f062b1a09070513030606030b01050a05011d0607290610050f0d0e01230f0a0203090613061d0f011d0712060f09 61
    0x24400b6075001c3e00d00c0d016000e41c0106091284d03800d00c0184040005604481d02890340c0a40360100c0d507140620300c81d134105000090820003611250310300c20446009441002d02095042c3c0d803c41142035109a031795a040102a000542142e01c124007a01894012814a4607030941d217465160584d0320079041602c460000a004001d280f0707141c110307140241020300301031034142c80814800340200c55800c900360140c0310005942c0d01f0401c00c034900d00c210600d010518440800b492450140701c0800b241e10307034007d442d1140d0103940300d0300071425202c54601c401c181501d00482c0f84040d601410710440407444030b40d2038601c523900f10080c480f11015000c10541984004d45010f00c0480081c1c0006082020640e10400070300c54500404100c15a0280da2103a12411003d02c510b0f0910092000c1125409140c0348a420765100c00c030003041c0010359024503002400710041c200c50396002c886104001c8801c641c0304d00002c003c1c4c04001c1d2402840d1071b001e1000015501c0e00c251104081d074201c034404443d4000030803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852441879 1250 852440629 852440647
    0x30408071b3308100608060d060513032d030e210c010c09030f06150b040b09031513020d15020417012a030f0b03030408030a0f030c050901200f03 64
    0x200d015682c10700540341215150800b032100d1140010b0a005120801c803a0340001009a01c5a40c105959541d0200040056140c14100d50100c902902d2044000407503001940139200c40400c2130340c001c032406603001c1c0d800f1000c10500f07400500e0980645445402106020070102c120304800786031000244540c5039a03030791082611401c440b45a6089030038021410700c00d00115150b044003a10f1b9a80c8018001007090702c0c002ca0880480888c1e2207000b01c09000100030504460100182c008910240e00712a10001840e81d29541440119035445010044440315805458501c0c044141c2d9070095400c40100300a000d06181680d11a0308003c10180320200881c809102c00d10402e80f425214405115000c9205c00418a80d05e4510907994201510b0704000b90b81d480381c6501c880b0315010000d0440791340360b55811089072240c00803038850020500142c1e0390050a4024001d02d04052410b0b654180313003104990054811400d800f003203404c10001e44443c1080014204011800641440000c40d211078040f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852443129 1250 852441879 852441959
    0x40509010e070f0e0403050f1e0408070b030f1501110d03061505071110030204080a120e060304080a050f04050405040f0507140906240a090503070506030408071b 71
    0x82d48040307040c1803c640c0800a52410007000d80d0841c2d030500e0200c3d41da6130000c0c008401030203207111504401c1444400c81241c801d00d44014005c6400300d9064034020b6035074800d001d129020803542c04100156000000d5401c06c3c0c0d803880036180c000c050404031100c14461a5651134082c02d5408000071940d5120240402d07004002c2c03e031000070701880d00301d12308a0349903250a80940c01032a0f043c0034001301c445120b841406501070b40e01400782c000032590382440c54280412820000b0341114040341c0d248582501e00e080c50f20440780714030b421064085c075040c02c4100c103c4007075001c3d08070320078114400d010105070313569980100c1e03024078042c0c00030071140c040360f040090034204554441c40146000003d0002d1540b65040001d9000c4400c581202480c88084684e01000c907000410308a42040080d54988194015010780c0a40780150201c500f0b96483d40c0038841e86102c150b502506110060214000060200aa002040300c80c04c06481240c2e40d1024881509036020340070411f605440411003100090b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852444379 1250 852443129 852443143
    0x613050705241809151e0f120c0405070c0506010e101a03061216051315060206013605060a03062306090601080711160f0602010c03050f0112050c040509010e 69
    0x2640c0d401c07040e8058094001040e64034490300501810750f400e0fa030b6880701d50700c5642030000d40744043c0082001440d0705092341c0d2107a80f041d9030144210310b03107004103980b1407240320241030781580500101003503400c1c044000d1461900410760a000440e45001040c0e9000d04d4042e406e0741c54900f071041c0d4032820a4030400c602d84070224905005a03100d0145118907103103040240701110760544a0b1508d1005002d40c18024200085108000030780c50580000e81c80c0d40003821504071101e4130000711420340084010741d88005004001880041d41881c10340424010368041500803030b00801e0740c5c0c072090341d030761b41c0d030081c1c9070008000703079541d4003000c0d80e40042040e550185a0003001122820103d181800010b4401d004c080c0400c410090000c002d0710942c4020042414604c0c126407070090307078a680d8200c00001c01407a005110040d400c240311411400c7c06801440e0080642740d442421076801c2c104140c02ca1684540305031824800c1c00d00300c0140351168402d1030301a004a034000300b182003080b01150b01c0e20003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852445629 1250 852444379 852444391
    0x20a0b07060b150306010e01020a0f03110f03070b0703020c0f010c03020301050112060b160f0b01120606090c020d0e01030f110304020a050307150807090e0f090613050705241809 78
    0xb43c0d002d200c1401500030700880e0b07032203031003424208022888040104c0c58508902c10090040c0e00f802914020706800c8460580c0c003280c207404841c050054a903136140c03a4011248000e009030b02c0c8038041403586010350054072072002c03044101d0310300c90381150945003551260440c0c175020943c0040144259640080c50304114007240b4014000385280c503211500e1031107000050102d04410000c120204441d00010041e2150001202c00300c658454801e080d18820411049a95038680203001400d1103441c05140001d00b183e8015000c4000b10803c01d403001d08819480e40d04140c0c1d01e0104010280346407041c5103110340600c01d9291680307020710522960301c0d00f9401c6140700e0b900c10b074401c102e49041c00c580707620100c505152030365858440d0702043e03070708900c90b4000500c541d541c0401c2004281c1d0110b2214441d003824021203800e901c9614040c02c008506000141c00398011000c14091802c004a0a80c1200f0b8910001502010300700c0c1c07401c20a4001e200003460100b0401035480c12803920000b01078000d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852446879 1250 852445629 852445639
    0x9020d1a091902030a0f031e031b1d01080709080d121406130207170304060902011707050a050f0d0219020106090c0e0d0204110a030b01020105130512030a09020a0b07060b 75
    0x40203600000d58651048400038986d04082c0144000c05100345029106d4051a001180144101c5c100180141841d5500c1140030081e403442100800d00c1622419030b100d1404500840300c00140e00110b801c8400108105c0c14400ca88000203550304d41044440c0340300002c0c0d503c0414500c0c0101c05142603d01c40c178504000101e040085c40301c699556468501c03803a0740e0403001039580d54546401d004c6030198560560051201200b00802d00110f6086206028801d0765050b0304850740d400352000c0c0400c03d90f0650009072051240f0864607015000514490804803c0f007402c0c1080001c178032043c0d03807003005c1c040500c1c5507500080744141d409000c1d0300080c00160303001b40080d180f0880000c0060b10b100e40041d101d020090646c80640d203840d88880303e1340c001d80340c0da666194020f44000d07014014503d4407500561030f0000140d07250022090780303c500d40e07020700030349142c0342984002c282c690005020010a50b80c1c412031080141d07540c000380c3c070003880035003551526190a414a0f100304c90002c080203010f2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852448129 1250 852446879 852446923
    0x1c020f0a081906060e0106080a1d0706110f062802040515091c0305041d041109040c0e0f0a1406010c02100c06090602030103210507030309020d1a09 65
    0x61804201d4501e0080368403410420982c0301d0500402130803c5500c90000c4684880002c11142d52050360305200c2e6541c11703006d120014141441d1440302c00e03082c074a9a20754011503814044a845404441c0c40310020344212074680c5400a0b0441c206a41951b02c258220b43c00380030102c140d128000700c1c89100008517011070425181a022455144214001c5040f0040024881c18179544074180058043c42d54501801c003c1c405140c05071440d0b116010300000040c144a0741d502e20001e00652034402c0768860200c2c5400c0900382f045c401c200a01400c119501c0079048004180c5007510700441d4440c45074182143c81d45d0500d115404100d4518501a46c84901100100300c402e90b04a00c1600d40564140c90b1161410100c080454000300b009400a148500301101030080c000c494003d03505a0b8099800340709081d416403484c5005080c14080710000c54014003c03040403d0080e400400c1340c900103485510884c1c1207954080800c86c0421851088140c40d10500c102e518040009800c0c140742171003e0512 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852449379 1250 852448129 852448139
    0xa180b0c0d170408030c07060c0306050111010606050702060d06051507020406150828060617090105040b0103060e010b150d0e070506040314010e0d02060403122a0309021c020f0a 78
    0x2d81c060043c800f07880b100000011411030242d0400719000180c00c07001c1004000c0100c14020040c018034420b5a0024002e8240110300030410b02c101d20440300c403602c0303c500d480c0c0d00d58207104460700403004e80504103030b403060006003540310685000e0425184c489443e680d90380600c1040110381454200f0369144510501500400e41c000b035660340c08c40f03507505280010426020308440851501040750a580e8140580000c10a070801ca01400140280381001d80c40e5581101140c2250000c0b20007038071002c1c022004001244182d80002c3c0e0450103e2300200d40e50819001255103c2403500107043d00b20400030344a001701c1d103141b0030a100082c8090242181c02d01d04000169680900d000150041da1649051214501c003548860300c40c070001819901c48081c00a0044d40781c490844040d03021410056200300002d00510903d40000021081900000102d1445001003180b2043c6103080c59904c04a900150355284c0060b105a03014840f1440349001601c1881803062582c2d4000340215106d52040c0301c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852450629 1250 852449379 852449417
    0xf090b0a0209030c032418032208012c0f030a120e07062c030d0f1808010e01060602010e060103020d031701150e010e0112020a180b0c0d 60
    0xe04154614030142e1100003120000f401e15400c6008540e140c400c80043c1c5e0700c8560304401d2203004c9540701042c25001e030740d200d61005031003080821606040d0400c105006c12a0003900c2d02081459182c040c0d010596102d030405800c440361013080f072800d4480044c0e1a100c5421254441a507411078030040d1441c080002d0032141d0701d00403103460f8802d101e0701c1140400f0701499580300c4103850498130100d03110a9510030000d40100511400541040b00c0510180351400060342903001000000e001002c813050981000c0701c41d0241d0302403030b82c00c00840a030040000d03100031611001610b048000007904004a040300750031545160f01c0502964100901c2020b42100400c00c0f40c11250140c2c1e00783d0070302c070b881e20f8200c42443d00f00d6003103408100d0316400403592101c110729000c2d541c80c0d940c80c0c58030f1480280700155448045d43d0492400148030040f44404903d0a070081c02544c0194200480c0c5551103c10248454010350003030503e41901203181050050300704402503500c04503040c1140c01c40d440c002004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852451879 1250 852450629 852450631
    0xf1503090314031b030f041b08060402061e0c0114090d1d0406030818010306050901050d060b010917010504020a060309120f1704030c0c32030a0c180f090b 68
    0x40c2c1214007100140342c482035407111103101000c18040d940c0e42d2070613000a0054000680317003a28100a0b1010929200b03c0480700a0240c0f6841801080d455640d642003080c0c0754041c5407226010841c0d049030701d0b8035215100103803407128152070012802c555402c0c200b841501d8010021411940040c581c24001c6821072020b43c0343c008098802e4120503da4000700b07014041c1640000c000c07990000d100072001f04a031082d1440b40100344d80c1400917598520801954001c280269039005444e01c1522002403c268086104040d060521b804540d607a030050502e41424000f4141950351154100710440c03512140c0c0d00003400090a0401010341030362900c510b880358104405050001c12070281256902515400d50050802001d43c011443c1a01c1d004006500060085507064034840010039411000c0708001e14029000400110545210011402c10060150019094062412900d0105000701840d5000c0d003040c80001c07414691b4060a21300321a034502d00102050b00d003034140c45c0003801022000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852453129 1250 852451879 852451907
    0x509130c0504141503010b0c150420030f0d0c03030608060c09060706181112060f0718090c0f020d0c0308070804082a0d1d0126010f15030903 62
    0x2450310f200004001c20840c03109912202c54608000c0300000e120100d010080001202c0e907800d030b170404510021040311074882510000c141002c200140b100d6030802d80302105007090001c003107500e44801c04156900701502001d400700024440e0f2034800500da018002c45000341054002800c8625100d405030f6960b0051041c1e1a104000015801003401903542049859003194080d12444242c41d00d015424801540303c1c0f50b0081f82c00810342803142c54003184152190048200f0144299101d82040300ca001c41a03200f1002c00c041368102285007990f901c5410005c0090f41c0b5850200b94440d0b60191800b0440d49007030042003000e10b880720009600c01c030b030f05800c02100c0c1000c04440c0c84514140c2c80c14018100704440c0b07080c00e00084e186851110f80c00c0d81008043c075050b01e59400302200c0440700048100d64000c01c203a250b40c5030b8131055100358070b021084592079100c1e1480c110389079902803401c1c2083e440840070901031641400700d0307004603621041008481c1000c0041020940d00900146008154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852454379 1250 852453129 852453149
    0x20606060f07051f0204030308061e060a1101020d062907060b01051c051906030f020d172d0a02060a1d15040b130201050304300509130c0504 62
    0x40300c04000041014131a0395240710b12400d03040c501540c005000350407034801900003442c0300e00800c0e402c0c10a04050600524180301b200001654030341805035640c082003442c010000f514091000c40b110078406414a03228103103010339030303603e04660142851020304810080142e1200c0868110a55804a48500c0e07401035000c41c2c24030140380140c900d40600065a00d03504010402e1010580c1d1683c0a540304440f41681c040c0754890100150044400600004003031401440d0803030013500d0074140c0e040c500e602c1000c0045016500d010074061a030008020342c40b640ba4140008039030302c0c080b41901c61440d98490310850800003101c00096450401814600045039a8003030401410302c00c014007003a440036041120250400311804402112003118181c80d651755000c04128402080e10100c0300c4603405a4455042d5252622440d07081c4094804200c40d1404040c000501d11080d61a402c0d00c40201d5203880743c450040324140881186100c0850000c00e1414403081c4005401c00165000d44500601e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852455629 1250 852454379 852454387
    0xf01120b04110408030c0d140f0c0304030f200609062502041a011b02180703060f030803060f030114150d05011119020706081b0706050f1501020606060f 67
    0x10104000300b20301191660580400100441d44050004c02040042c405000700c3c4c200a0b500d89088400203254040c2d52801720703080010700c6071000108060300e00903801009980c030b0701c0c5c0e59a40c2c0b0807000e101c0c0001103d02da84a0712003180000000304028580300c00994a007881d1051b001c001484a21a4051250700422003103201108000341c1580d1100c080d902070020400e5056101c00d9014601058001a0000c0c46c2d0f5025075020150711b505484a0700d41c0900450000c045c0b400c101040b002d0000c00a1042650750000098041d4a00c214400194090041a41c0d6800c1400038450400c2c2049132031030181e03041020111884180c0e001107580450440e0f460390060343c80340005040021800e60181c16903080c08842c40104010000520f072030000340154410306801510f080c0d07180c1d1154810540481d8000300060585140c1d03245071507200c0c94230a049031400201d551a031007243c0041d01c840c02d03036808510800c111011007204031551040240010216847c00304006030a41c815100000c40c0d520000c070b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852456879 1250 852455629 852455651
    0xa0f08091209270a06170c13051803130608070512040320070914010e040812040312090c03170f030103140c0a0b0c0d030615180506040f080c0f0112 65
    0xc1c03082a220440c030400d80c840c0d8280311400c82c003e0459809520b100e00060600c010006e0000100e10f80c1102011b012840071183c4c62440c1002084001c00403655242410328100e1540824801407505200858480515600b07100c0024103000000f00030000340001040842c01064410402a90040c2d2514140558100d1066440c00010805811101510071648042044001a000805800441040b00342160b0365821101030b0440300366405031102200708507101040302c01040e21030f1b105009041c411441c551444641c42114800003098400381e8130201c2c140101304020150454600003044142d080900c01040041107200620005046403110f001b2444040e1040c0300c000364a000c004d12180c105661490590aa90700c6600280e806000719443c214205001c0d11688060b85c1408400703c0111b80c02030b0055411880c4016a403199241d842c000007002e964880080026002411142d04034601c0c1620007031401d0110a0180e22a16030810140d0035030340d0280d0041d2540c641c01f440490804101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852458129 1250 852456879 852456919
    0x6080c0f130e0115030503030a0c210b061b1f0209010e0d0c051c050f0a21030e0d03091104020f0304170c07120506070f0207090908040b0a0f08091209 66
    0xb066048013074110000000140840030016601c15402c3e540c1c00c0c0404c0c88020070440711520701440a0310b942000d40e0860715030030807a0f4010ba86200c0b001d0003503031401c01c3c070045061075000d6413401148c040c1d00c403030300342c15110018801c0031900706605071066050000b001e0002e006210b0081c8024013418400d10b606041c0655480140b00030407001d0035070380f03684080ca03080300300c1038024036010703282441003140c24100001c001580707086068000e4031240c0c81140000c0003c8a18507100c07003403810151200d9000140c50000c1c80342c101e59030601d40303001a0201c21860040c15400310042520710481c4140442c140c0c6103072a0b0116030740140e010170b0a61203001e180916409600540c00c82c040706100d603650200342c81d20a44186084240100100c80869960010460f103040d00e010303d940040c1c1000e20100144110390700054101c500c611034480c20252150f1310f4400e10f81124002100150700b81e1241e2034000e400c801c0c0c0760340280a10b0302401c3c0130010f882c2012820b102d140d9003c0d000b01803004d01c02c0d200703000f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852459379 1250 852458129 852458141
    0xf0a090f09061104150e09040b0717070801060225050111100501030b060f040504050703021c0f0804050a060207061b110d03030b09090102120c0721020106080c0f130e01 74
    0x10001d0b007001001d0b508000d110050304140151051140c81a0f60326540501400a80c0c0c1c021100504044e41035507295140c404840002e08940d052120014030711040c2a003076000144503480550324140355624050000303141c00d005c0b01511014034200008203001c89050004041079a400b03003031118002d49105103051a00900310b56002460740351500107c05c0080c02980c140c0248070481e41c0000d44001c020800088403021b507002009a400b04038200018149080b280304150402d044401c200551903c4010850103a108115100c001c00507091200e407404c000404080c00b001c2c070040050b01c0c20800080d00d20310401d05000c1c0091060f4640504100b001750180d06180405468982004050301d0040c024043d20300c0614440d08030038000401061051053650a1403503000c00070206501c84a919100507400a5030036106c551401d4030301213400e1130700b4145800680440d400055428030300f55080d410800c202445500c503c0c4005100805540d0300540c69044c1c5039200da001900c40241502c203401041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 852460629 1250 852459379 852459383
    0x80a1116030207320d03140d29030a0311030f2a0d2109060501080307050c030d0509010513210203060a021e16021503090c0f0a090f09 59
    0x401029440d041507030200f0740320121503841d60040c5222044000440541d41c02034005903100032004000d5600749880210b00081c41d0090500b40b400780407168400e0002e9101c00c0481241c1d907142d007400d14032420702d074115403200f102d294445850008a840066103541e41c03010054100403294221111000041c401c91b8100c0900e40d255503034a48002084107840411200e0300b0003502103003e070084010401281c980303103441c6140e0f200303204001840440c100800000c0d1064842c160317034100d039000140c0144222400381016200854945206262840c50400b00c0120340d4002e8110340b4255002e150040280c510441090809a032101955800781544071001e0740400140701c21070300751201d002c000107a6800414025001d440785580e6400040059228092051513034a003006000c4810541c0c000181400300b00c43c0103030075444441900026075180f0401100f800d42c060000900034840c0c820407210308103000684d01141107040c900c0000b841d544941c45255015600e800c010401c580c640e51005003165 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 852461879 1250 852460629 852460657
    0x5040c05090a0f050a06170a0b070302070f021504050a0f031709030a050a080a03060e0c0301060309030c06020301060503190e1b030106260f1f09150f0902040c050a080a11 75
    0x303e0306150b1703e00540114032030440c1403201034804400f500030100712400965000560441c241e00ca0060440c02944031a0040d58268034180c500c03c01a52508a0181e00580c00481d064585041000f0807075400140e502480d01401c0e014403c0000440c943c81d42241480c0c440300440c0c5410700a4040383c00d06402c0b800040850161041c0c100800003c400503140c580359998040100541b5040d8044500c44241d441d40308100051004100c224031a401c14016035201b0314080b800580a9030f5008142e070030030b0300030001090000c810030218914030021840d600c0401030b014088640b1401080341c03542c004405503138040c20300384c1c0f1100c9282c9094012100600d1001c03504844494003000f928058045001501801d0141d0708403051140400038488040311074441c0343e0000708070810240001070900c82812514a0aa9040440150314a00c40c0d0502e0680704500800e541c14688100b10407900126480c0060040901c40c6e80f2402d5440440d050307010300c00d201c00040075118001004458000d049080d9054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 852463129 1250 852461879 852461881
    0x201180302030115141c1103070f141c0b04170c030c0609060603060907060c062d0501050103020412080c0f0105040c0614041a18060417070905040c05090a0f05 70
    0x113820002d420000321040000c40c8001c0f140c0000400509040c1000303103c40c04a40f4944420110300410200c514004000f0100c80000380d92301003000542000e503000c44d992009074024980b15042103901910302418024142c0b000b402d1a560390050350310044c0c4060b040c1c8000214020030f0a07480002c0340c251507030701800c807900c508003425595501c1404031a040514010030300460401c0c1000109680100d5000c805850400e0500004440b1100340c4c0500741c90242e1207142800c602c014180d1aa103160020030892021050821816420390324180e0095042620411041104661103003040103000c2d8010031681e6a4181e022206140c2000c80740c0f8000d29500e028180300402030b44013800c404844c00340e00c540c00941120040c00b122400340b4400c181c00400780c00150701e0f865800b00000d061f080d6441e0904400d10181c28046682030308030b50031110fa5442c03011050f80001c44100556402011702070701c00d004a10301030303079080c0c503160061050314054500c11020400300c02c00c030307003101c420400c41501c10092 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 852464379 1250 852463129 852463151
    0x3070e010902030a0e12071104050c190c0b1504050f100501140705010c0c02030607080601022d0a05071a0301030f0204050c160609030306140f010f11010e060106030b0a0f0302011803020301 83
    0x91540520002c852300c41e20180340204600340341c010684904030380340d182030a100c2080b4141421251003407034a41009175549901001600090302d01d030060f490240c820700300302600e4080c042200c2000d89050341d5145a9003c00000a94910000e010b50700d081c605803024a03541810302d400390048500007021542030940003b103030380d4840740071420240200c00703c41280d100c414007500c41e00b03070944c0ca06006070005072068109030ba50030704034900450b04220506070001c10000060030644c00030300c116035642204608028111501e80804552003550900f03a256500d5603655100b000c01e01e030402401242c40e013000404411858050380c8500c001c0f040090445041c40c5401d8000b4540100100c0c042440c2c08000300b88000d10007141c840d0a14050480708070000d04030015960440c0c00c0501c2d00030888040c04a0001d81d400380200c405c01c074544070091086504020011303069130b140005060145039120400c11460703d00e510039908494081c204112402610000c0c180d580d8100d8201a40540c01c0806e0320b04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 852465629 1250 852464379 852464413
    0xf10020706112106060408060403030516181806080303090705030d05090607110a082515120f090c060807090b03010803091c050a0f1103070e010902030a0e 68
    0x24140e12941040000011040e40840d241c05985400d000001d4604050984060559040c2d031308103000400301030402d0f03503552803980342440482d01100001d0300c0e030301400300281d1054400d81c042c0e542d80c00c05e0b5900144212103001c0031680c1d0720038407101e0010801c1405070182c59611540240c115602581c2e900d04d840400c071542c0301c4007441424003d02c690400705990f01c2c8188152100c03600c004004501d001e1154982130302e40c8201c1d42d075649c0c1c4103181202c0054081c2d03003080007420152400300d1015810000b01d05182207402141e02802503c86000305401420f5030011642a5a0a141c5000608039150821300002800e0300b40005045d00394581020034a1a040248184100364235540d004040c0d8403005010080e000a01c542e20282d401031007011030500c2c005a1204c03151105e010902d101d500b007501d5041c5888242034003511015138034a031000070f00c40240316018185000341d00134000c0d64600030408104040510480209690200100b00320207030540060804011030002c98100902c01c84c1300352 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 852466879 1250 852465629 852465637
    0xf060909050a0311030406120b010905031608060a0203010e061e067b04150e03030403110f06040503180d0c060e0d0b0a2003060f010f020f1002 63
    0x1a004c40c20800d10003135282030020444003500c0056580341c002200c400e15400146c501c00060318140100701c00081b030720740c800704a149520314170001c1600c0c03841d01e0198010304142002d401e0041d46c500400050062911515070240c014009036040c400e5400f801e10020040f0750f111081583c445c8000038600081c4803074a414030041016444c04001c010515038200c90102d0680c56607402003841590742e44201803054981d9120300c0c03107103020349040244001d40d022803150035074480200c88401350144002e02c0454141c003807260004800800c411035855400e103940c0d00000b030009041081500190500440034400f001c1a8469141101c0700d508140c07030070f107403650000d1000d810032002828950010340b6050110a01c11a00000d83c40900c500f440c00403101c1c14401d0a825401c09442190300780001d001e01113442c401c0310030240014803030046404a03044050401c40e14004d100060082c048241c0d80e140014501c850242010405040308103020b84c185a100c3d000030300c0c64003811a4514858500c0d4000f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 852468129 1250 852466879 852466883
    0xd0c120b041a09060f0a021309020c060108070f0e07050909070c05010c0c0c090213150804050601050108091c140711270f0424020909010e06130f060909050a 69
    0x460188114100410904441214207009a1340014040707010031031603e10b0607070040c0c0d000304098585110500210b0002e042a80040c91181d8009031184920000780310042c090800c8202400007180360040322216032165009001d901402000811030450051044a100007000342c006405032828005c09800180034a0381968154207101d50200c00e60310942aa0b401641d01c241c0c020145400d10003610000c0d00144541406c10060043c045584402c24125403102c03400d995694849107402e02d406800d010041e40403d041c042010180300c9064070219a140f10001c0000c0c221126042c0d80404840c84400c80c990f41c221140c0014a1105110420403030b1410a40e05440008045844221180c201c80f9030400b0902041004800300758001d405404164201c2c0c055102c96145050303400410349121950400d40d4070b410b9000461a51a0410011391030041098802c400310b02c0c502000030407543d81c109401d244505590300034004141c2c0e01d5600010182200e6103041101c1c460170302e40140c3c2c601ca66641 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 852469379 1250 852468129 852468143
    0xf1103070605180f010203450604030906020106050d15110408100e0604020901050915060f1801020703120507080705150105150702150d0f050907090605030705030c0d0c120b04 77
    0x14640320904c0c14001c0304d0003000c8015a000c1466400160040d029650600b48034241c00700c051444105c0882d03118811070449980003a1209007868a000780c55143c1c254400000e590518108000940d244280002880c0c2c0054500c0f8014110381800360090a51801207006071b074000c580403070074003c0002c8210008a42d1070041100e001d01c2403442d80c1d10f2101700c500030740c4514078000501440c00e0000c4820340040c815010301c00750001c0900042e405800104044040b204046061510a0300e800780300c0790501070a00240c4506401c640300d0f03140c0351000c0c9100100b8440300142ea101044203e000f150100d5403c207080d20100c0200d04402800d5030b00a00c145445010000501421004104202c500140e4000c01071242080c0184060701c4a403c040d025081990f81c402000702014014011030340f19404c482e01420480e810201224111545070700014060f5021075410700c203a0b00c0004640c514180200c590a403550240d240191419103180c02400c40e4507100a45c20080003c02900075004070300c00c0b15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 852470629 1250 852469379 852469393
    0x409051e011e1805010c0503060103050c07050a08090120030d11030112021e060304030f140f0d020f040810050103030818030a030b0630070e010f110307060518 70
    0x8818281c40c0d0700544405121519120002c000a50350310031091092801400d02818505450701400c59241184440200f100001044000e6034580300f200d6210100e80c6002d4144442da45035650394241410b001481340000044250f01c6a0103181050080c140d004a1410284048000607480750002a03100700454200078104080201000540f816507000c520030064a043c2d5130200500380e100c0420107482007120b0700d4004a2038a40b44000e51149009031508040c51480c074a004088103480341a5101c4842d0a006410f2103080a20844082580782031001d070322811000071844452045920003040751041d0000c2018050085d04000e040720f000c1d45400280d9034030302e503801d49042c50280030071120b50400c102c440032030b500076400f403000c00c2006030031a4180b04400024201c0041a031960300811000710002e05061410840886c0e800415450502e00d00c0d040c800018160110303158801d018840244003222038800c081059030400e54003c1003d10030350400018036214556800360010306400303042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 852471879 1250 852470629 852470683
    0x304200303160b011a18011202070b060f040e19080f040f0e0105100504032910080f010b0d020909100c050301090c030e0d05090a080607050a0801120c051e040905 71
    0x175401d410451015a03021745041d00d014010b9004c05c0561805505002207124801d40640380762014060940c41401d141c15207080c11010030090045c0400900e00c40c600740103807104008030101d5601c0080c10003800340023482d90b161415801c1c500502d0080d106444c004100042d0744175601d051501200c914814150301a42c88100340078960254034084d0300441c004200030000254400c0d1007a03c83d90b032500012502c4c4107808600b1600141c140d48201c4480d0409105003c0701100f440fa60401c4107101c4000c004850040010601c841d44400019101e02c460400007403585406104142e58601c1d203400412000d000c0d148040d00039042030281031141440c21151f441c0703d82c000e11030254230324900c1004000d54003a00070211202e6110165007034000107111030008113075404015040c02a20a616580d0b100c2100036802400200164840754145000b604104081107280380c0f00700a0b038005031000d216404495401d00440d05074501801d4025141c2441c00040c00000700740fa1155001400004280103049 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 852473129 1250 852471879 852471899
    0x602091e0306010b09030c03010e010b0a0e060a05100c060501060221070b19090f0506070e030303041e0c1508040b091b1201060b040b120703110304200303160b01 71
    0x160308600c0d0181d100c000180031003980c6001420a01100408403400c10010501103400c0d5155948840a1070391070707504880c0c1c01c7c5400101d00014000900003039000780360200010341b000c2090711404e4007502102100710840d40c030428030b0202c107903000310041c0b105507914a8003d6a4041880c07294121591444000b04550100404c442850750007500341e4419890303440703210359000d103046841c002c115984c01d02c2ca40081d254248913414140100b02428a80c6880d00c40981131001e6000784030322035041001041f0005004514942c22280e407c3c00c40342c03075404071385003e4034200da4941010000194425200e990b0f01e600c001214880c600c5103040c1c0300c1c0382c0c40e140765450761401044001c0d0104098035140600600705991036507045e501c01c200104481d0b5031190300c141603a20a401c503101b030075000103060074250540d195a6401540e2494200045540301c1d01c0c103410360101803c02002c041008280d6440d094440c182e501411400078250303641c070184200410801b0750310003003c441b00b500d0310740002072805030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 852474379 1250 852473129 852473179
    0x112030318030f030b120d020105060f06040b0301060507030e1c0512160807020625050d050306060f03040c091107050f150106082809021320070201031404060209 71
    0x2050f150100f508203210016805020501407540e040030340e0851541002030204252480900c0c10340000540303081420a11542510704017602d40a000104820094079048904403811a411803030510745840d0240b070101c4810103440c240070391111049450f0385030300d1055145412218410411500042684140f00401e4040c503116501078485c540003400c041160200200000f03480102402e180011104000142484180c8204c543ca81104520343c10000200300c512074007001e60034044d0030352620000281c03451044146002007030801001003410440e500d007800004e130a07140014041a50100000b5903103410081c015502c61054080300c00e02410046614481c41000c0304020400340c0c24a5010340d203101000d04060314600d014021841e0010b250944ea161200014802113901c41541c0100080207101c00400c980c40c07440c01d0121412070303145548056100c01c000d005d0035102c160b00d0005170010000c2403852250601c0a40c02c01040080300d50051141e002e04580380c0b010001d42542228403025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 852475629 1250 852474379 852474383
    0x4050303060112231602030403050c1203210613060f0506070c1a0910030209090a0f0608070f2c0c0d11070b0a0b010f090504050402030c090112030318 66
    0xc001240d01d40d445241c2c000c005a01252010a45000200031070491219554244002d5002035080c001d0b4000c00805070009541d20380f00440c105411030321410303180e408a55034148a00c1c5280f4840100c001f080c816901250f0f0b00304000c0103039000e05440305603c004c00f141c42e54862403013a025000150341500c40c20058420003032000450078104800c2c070115a2119400b96013414403200000746004e20b1031101c02c1460380c91040380361a80032107402e004500001e1900708040c180144030700b020a4860600b980d521150b20034022a0312580901b8440c01807955400c02030103401804400701e0140041ca0031042151000900700c1401001d1010442d9810408c034402c45038150044c020840c0e490300c01c0c000c2d1000c02d5114000040110900f0405905940020400c56180d400c280800812015502caa03c1401c002800e045404030f601c02c1c002049800180070b1039104030b556402150640d2004c00001044010103080c500d0f0650310781847e203603c46103100007180040d01b454201d0407440d142e11616007100d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 852476879 1250 852475629 852475633
    0xe0702010e060f06040b100c021c02010e10140a0915030509030a11100203090c09090c0f061e0c0f37030201090503030c040905010f0303021e0106030203030409050601080f0405 77
    0x3d20741c00e608841122002d00004e81c01390719002c407901d10390b54003009042c881400c0d0301d4900d8001035072720511681c488040c5420190885074881d48001d81d8005142c2c005101003102c00404041c868441039901181000b40b01849401c0491000e60701500818040c09891503555840c5c2c3c0d0004c104007c40559408076040c0c1601e41092000c000c1080c0221002c05074614500180c0d82c401000c0745100089030022075401c01c0941c40713065082e585052807549550018030100c0580440e10f00000440c200e5614000c03501e008550000c0d49420300074000000d40005511f416a40d55981e5204040d41d686481498044020340240d2110305002c0c18000d51a01c100780c000304119401c0302d103c07801288020b1420314194155504c8444550010300c00b4801117100b00070031200d00352aa41080988070444405802c40f4003c02004501403001c650001010a04054500b040018207460314003c24050230340c81c0d2000b500b6110111300403404084c1c070341105118480030381c0d034000241e56204c1c051039000420b4602402d15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 852478129 1250 852476879 852476881
    0x50409081603030b03010c030b011d0a1401110601030c0602121c020702040e1e01060f0b250f081206030a0218060d0f0c03030207080f0c27100e0702010e06 68
    0x1607403110310880e104600a00b00081c40c149440d010034203580e00e1008010009a40e12043c4040e9070300540000c00c61009070420b08521500c1d840800e0b040301550041000b040400b08200d4216071040201e00282111807055403a036594030b20b8591180b01c0c1c80d00409025003d0107010010346089082913480d180540240300a03156072403581c40e402980300c0c2c103040e0303002a100c2004043e8070f1010401c06420408007644000d251a07034043d03107800c40308035400c450701e2103c040104001c08500217094031030001002c8604158000b000c102102c900504401c005d11440002c4806010b004514000d0608680300d140340307000030743d2003108142d1070310301401c40294050f22013801d991000500c86001c0d0760003500a414850300c025030361075070041d4807040c4000700d8441590050900400d0b5041c071118004082d0300004026082c5401c102684920900d6602401071603c40b078015400000c2c4002c9a05583e0348a20840c410b00780000c5040024110f401600608070390b0b48007141c071441c4140324407001045011f02400c15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 852479379 1250 852478129 852478147
    0xb060d031b06021215010e0102010c270e180c0111060a09060f0213050f030a0f120e0d0602090f0a150302030c041511010b041107030c030c150c020705040908 69
    0x21803048501c02c1d00d245070700b40301040d101c41c04007114a01034688065844215841a000140800c0895413554116414400d1030740086800c1010403000415001940d0045841000109041301a6a11041c02c80c1202028000089106960004111021801e4a00c5014640019103130250b070b0320202c0d84207030710031400544002210361011582902c10500840c0301c00c20600004141d030846411102040030035003040200349082d00b4048040302c025000303050070f1400342e194041301d001e500001605020020280200da40d01c11400c03840303020b500a00760144800e00d030405000039080b1030302044c040d9441c1c1d0300c0b002d041c0c40d000740c5041c122001d4400c0480c03140c1c00c01d0400c8002e500094014130542d0800e000100d980d0711810340c01d404007000e40c0d540d00580a9900c030064252034032082480c0c01a80b92200101101c80d0f001c0c12104025010705004128580340d2400711894951504003808107120a1000429084a50002c1406004690880f0007150302c52040004503036207214000c10820042141c1c101c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 852480629 1250 852479379 852479417
    0x80a1e0e30070e10050919020d020a080a20091905060d020310091b0c03021006030602180102010b06071218080606042307031505030102160b060d03 65
    0x1464024030611098198015064a00c111807011070300315540242c102880305002150b0241d0b88007000d41a2002d415180c60003041c01707800064032400e02c48141d25488070007c0c0b81038045420b16100344d0411035545002403001003261100b50b6003903561908110b96854842c0003035440001d101802000180740c500c0300410811940003017140340b01880790700e40c03001800fa80c9000141c074171069288030169a030700c0c00001c0014401d0b42c0340c002c030510321b181c09207014200304119280b4440380d81604140401c2c0c43c41e0b0a041c0d1401d10343c0000100224249070000c02040100d402030044501400d00c0c2c400d403900024016400c2e14500706210790804030174000403010a14040c54000d480703141d400e060b441e08000301e1001c400c840c0c0e250019120350307122000b8803656040602c2089501504200290205030804080220b20000505401d0070552120700c107403281400c02050038010b01e00200210f43e1040000e0224510640b0440244c0c0c0003034188000a4003400c00c004203201c4554136941f07207800f414410304c0c030203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 852481879 1250 852480629 852480649
    0x150c030f17010621090b0709081902150909040c1707180b06070b0406020304030801050d150f022101030c061103030f0c090a03050a050f2404050a0f080a1e0e 69
    0x600304c1182e01c911082c41c144c4520100c240c00703107101c00042e10b004a00640b41c49155800a2000e901120b45580c0701060119001c05603a811510060610104101c1c027003103009021420742d0052070a0107001c02c11544800a00c211091600d803a5045506940402d450710481c0c0b2807160a0503241c50300c88049150366000074400341004102d030303040c410300d0340701c181704110101c80460340c03154000140414160403514007801890103c6040d14059015614288101c44144600c100303181c42c2c1124803041c4a0a8043e1009071004075001101c4154002e40c04560f05030030311060301e41a610100104010f031041013500180745611004500d541c0f9660242c402a0800500400540f9424042c008455846503202401140194020482d801d20380c01e04500380194042c0141c4564010041e80c0580f9010020440b40368101c0c0444200795983d60404a0614001403001403c2d18031302108001004001c030082c0c140d500a9036070341790504010703c1d400c6200268034100140400c2c08a0300300c1c1c5061030910110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 852483129 1250 852481879 852481907
    0x4140114061308150417030103030e0d2d0b36010b1306080d020109150c12050408031006050909160c0c0314010f02040509041b150c030f170106 63
    0x2d6591070b500d1121504007090441000c00107201403060005100405460f0781c80300c100c00c0340ca01e1840d4035580d00682011048000c05000701c84a428000078011030322a0300078080303002880010b210900c807484810310301441c4000c40300006043e000c2041c01c40351220384400c0a00c0300c0700305d41c4008050500d1200b01400d0032480c9426640302ca00c004c1443c0c03603a1400603c0c0355400b82c008a10b860816041314103101040c2c0c80c03602103a14104000d0046010100e81c8034030b80742030600000f20080000d208442d44e120b1048002040750800e030a2100300003441004500c02c40040d18148800c0342c071404226604d20920044640c044a00c002040030034681d6000f501405020707003000302d0350005913900c0e0000c0705078940c42528000400891400000401c1c02030804c02d40c0184811403405041c5070010301d984030f000e0405000030030405000342184401440c3ea0b000b8040178035909659040058000700900c7c400082140000d144031000001117000da00b8000f00d0304024034840c0c071160b0810f842114102002c0802c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 852484379 1250 852483129 852483157
    0x150408031b0f0a0509011d0d020906012007031109040c15110d0c0501050109020405031e160906080d0906051209011d0105040b0c0309100507030b09070c020414011406 73
    0x10028038100700d00051140b0f40650b21150307221030700440090031841c03100442c3e8600c4042c0d511a400d8075541c81441d03040241c0c2c120341c07080441e1a20b8004854a00c44000c0ca20603100402c2c001c0307440201d0000300d000440e0b12130050032004000c1c503400d1025509081e21300070088400c8550a1101c50b00420b074143c0c0c09990b61070108085131000740c807180b038081a88103900100d02c0745d111000900030280030786405030910140c1075140c075240c1004290782da03143e5100f44042c0d4040b400002c0d40c80d030041c08101d1040030703100304403103000d034880c0203d034000c0400b4451900e01e84100400404014041d08561080b81c1464807050308140b0554130908054038000d11088465503105118142c4101807801c103181c4000410000a04d4035251a002c01c6603c0f014003d198000014020001c1c94040003483c01f118690b00e43c000b090a40311140260090420180ca1503030090603a410032440d83c0e4060f004012170b41c02150240a08060901c19021410081c00380318142110551442d4041c1401001030500002000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 852485629 1250 852484379 852484387
    0x705070f0b0a0504051b01050a120204030f1209060f09090c02120d0b0f0d0b0408070f0204050a1a0901060813030c080f130e01080303040f1406150102150408031b 71
    0x15070781c114107408548241e202c5683d0414002882402c000c929018031200c40304896110b091070000e4018040e01c444c4000700309541820134181c514a4054078002c0da80196420f00d40c0e800b91418110304040f034022540091859000000d01c203200321112082d00140342c9449031401d080c4080d001c003510100c14208198400d40a00f1603605c41c80000034880e07408005800186442c44004200041c0031070100c85219942029140d030108616180c401e070459030002086079511154504103010340c03150000070790b01c58034240c10024206c4a94200103403414109201c07840006483c1e080054008083c080e03c8001200600050481301140c6a484400360083c1000700c9640d01c00e55802d541540005840c908050003c0b40d42c0c2a01181c590220340a00030b02182003d20798149a081540c1e800020400307040854540d1086061100300b007491055442e0a4056820500d820019440c90515400c1d544d8014801c40e04945a4200030040e150301495104040c0c51458580403003001c3c0180480c0d582d0481424200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 852486879 1250 852485629 852485633
    0x708030c160c17030301050603010b0307020a05030c1c1707030506040e060a06050a0b120a0c09050936060109270c08060f0c031b130611100b03060705070f 68
    0x20581e6152540308036030380041542001681c007900c0d00510300805543e8428001841181da4160540f41512002030304243c60f0740e20103808034a41661010701030a00e00002502c1c001116001c103a11500f800c0c8801c884c1d0300c5110040b02203802c0d4032511030034440b81004402140350349200350400e60700610010004202c030755030a02c0e52414904140c52071205281c1d00c250410003414100014030041ca00b02d060a03003840a000d100c040107140051404104aa0700c85d5028001401103040c40042d003005031840940e80f50600760544c1e80d01c080342041c041440346010300348480b034940b41d580792092149405840d03164604a000030180c2210840b030201441042e052405a881c402c42c10f2400341d000c1c41817100e02301d24021140f4100390000c0c10102d0007000407030801012541040440e5008011001102c000c41101101c4040c140100c054100714541c055100103002035220790f128803c80c90200079200c040c0846200035045640b00764246825400c0180000c60310380c062406000741038080e0b0050b0503209032036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 852488129 1250 852486879 852486907
    0xf1211030c210f030307050a1110090614010b090f0103110c0d0c110a060801050108040303061e032a061115181606050316030b040f0b10030b060708030c 67
    0x5000c4604202c0354207003502c001458100311034803003203180002135440d50421400040061080003441824400000a07881100300204010302191010b0f0000300001e0006291190213405d0010b03032842c0c0070014000114140080744101c130448200140011150b00c489001074001d002d41c01d11204a220b030a10400556450134084c001e660002565601200003442c44c04904102142c1130181c0200d80c21801400a83e410460b160305507102401c0c0100c00356140c1c0b604030040c04503600001c0c800d01d90649a28860003800615209403885440d841030520950768450203401c500d4800c8142d00703c0c000004100c00350058100c2d0f42046a0902550b99880704071950840c42c400c01d407040800040c1d9a18100703c2f01d9414000c1c1311302d42046090400320300d444c00c0001041800301406115001e00584140d02c442070080c1d1011070540800340050000e8504011241e0040c080e554160f4011200b146a03182014442d00c10340004400c0104401d0404009444030440c1da000181404840e61081040300c800c8030718 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 852489379 1250 852488129 852488149
    0x605010501031d0709110417010b090703150303031109103b040b1305070e210c130b09010e0a05090f060106050d02090607060504061a0d12140f04060305010f1211030c 73
    0x802c00000c2b506c160600c0a020f00d100b00184041d003018a000440c08580140085100869405150202e202c8065912100643c0f190fa418550300039107c800e03d80c081a000720340b800301501e44280035070642d0740b60080000000c0da074241e0f031102c000303011101e6801840c107940000d0fa28100985411590b4646e0300705e04c0101c1c3c4068131081c01242007145174052502d406c28050014401000340c0c00c6038001c0075000360b503613030342e00c850b07003c0c42503041c5480c0c040f0703243c40d80d804060b409000601c0281c880d40d42d035031100200d910030b644588001c3d00b0000014000c01d40003824a001001000007801243e1038214115810340041d010405a19020040c03403103590b8605010300641030141c180050310b407c152410000300c800a440c294480307002e0071107001c2a9500c06903c0c440141c3c2081040d016410001e03001c407041090345000300e54034500461700d51004003125020b0310644481c0d40b0200616600c0381d400b800511564480d0003104210102d001000804004c01c0c4245550041c2c1107070040400000010702e1102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 852490629 1250 852489379 852489419
    0x804090e0705010309020f10050d1d0c0303040501170415021c0b03060106020c011116120b1315022b020a080f0106090e0c04090203040605010501031d07091104 70
    0x14440c0d0490122610a02801d00100000d003400c00403412958045a5400300d43c68603c0d00c150361988400d80b045004070100d5940740c008040170040b90713031401202101981211111001c5125200b1011828200042120246c3e04c05848003407488540402003030402100810460b88000044508054011f40340003400101c440c1080c00c41d0030008584401c400c4800e8003000340d120303602040041014503000326400d51005c8080c03a01e00c0c0c544128402d1a0301e0100151200c2041e500ba10f4030000d005801d07169484030340c600c43c0c1600680350711064010881e0112800001e0003030041007074030050b23072885540141300740e010804031030710281a001045a0094000c04801501c50b80000710606c100e50b01c00703825640000080103078011541440c034024403128684c00780000d070741d0b00303100481c411001c00b00965004204c0f0b042c00359920300d40340c80e00c07401411007845502e002c1707420315004e501100e042040d85100c2902c03100c000c00381a440d00e5a1840641900c1d002c440d40306104001c089880201d0000c0c04da4964 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 852491879 1250 852490629 852490631
    0x210210506030d020105010609090b1809010501030318060f0c111002070801061a04151106070c14060906242106070c080403030c03052a010c0c0b0f070c080409 70
    0x1c0380520905050602d03404505085925103070040c0000c54000124105440310003000003107000500011401c010036551012910801101c01c100303800c40c05400035030680b403290740d0760b8260105070b484100c00c40d4442d002c0d20700464000212950220f205029008480b4061540078204c1110440495410031540c290f02c801604802d905002c0d042003401580c0060603041c1c2240391000c054003254409028034044c0d00700144840310441c3d4030038810800814603001d1001500c07a03d042000b030140c17524907410012140007003079100c88200f000b00496000c0c45031541d00050092955032008013411004080441000f0400c00011031a240d2a6041005174492802e0326460802003c003c3d003901d4084024100c0301040380100d11400054480001d50b000c0b03d0341030401035070300d640c949420b40d02030107482e4012141c250307080840300c2d048011a2003040c1c0d84a40c03d001b00301c105e0078084101c540380f0340700c0009400ac81250f0b01194400b40840c4000d40c4c015103e00d44610100c03025660500781c1e0344607503c000c40302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 852493129 1250 852491879 852491881
    0x160b1e07030b01020c0a030512091908010213090e061302031e0c1819151823010b07140717030403030206130b04060c14160b1308040302102105 63
    0x256010044400c0800c1c00306d64402529256075a1541d8481900032800440540818070440944a01140011440e401b4a403c1d09142d101c42e0a40e000703401044a215071b00800710000030740010765101d1880c40340024409000d00b0341d107550701e02150701c003186402c0340c140c400d820305000d488040c0c00e5905484100440a0120f0b00301c0082044004450140b0504410301d0503804e20504003070703803025414102d40c401008203184c01c0801c41a0405450b80d408110b40d0a1030418144400020742d01c07802542d040302c7c0085620340310301c8445207042e890900074241c288804010f80e0011503018900c030100360344090200c0b0942d503101c0401411403404480f80d180e03542e2011030184101901445426441130840d000c02001014645a58140410280025250540d9150302c6036400c0d20607101c940000b00080c0000341d0701e0000e009482501c603010300301903c60150140103e14a00d0500000500c4140c03ca10064186400c5808001c541900040711030207000640444400413150480104a01c2c90301200000d45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 852494379 1250 852493129 852493151
    0x13110406060f121820030a0b04052415130f0603021008070212030718030302030c07090e0a03140d0501080105011a0a081609051f020d0203160b1e0703 66
    0x86402410243d003641d5040c10510115290b055502e00c0c0455000700d600380c0144003003070046541502658006815008a200c20310074400541c004501403803080040741e0003451014620525001c800000c0e05040b005000800d10010303030000d03400c64005006044d46d000c1d249031f8152100305d40401c000741c1002c0d40c890b0010025880c10402144160342e95040051051410301002511740b210b00d0358550004030044040b82c91184101d004807030792860011010b00c02d54480c00c0c082e5994004243c050100d10640c5404143c41c0d4050240c0c92002d1a401c0041048402540d41038464070740e00c42e60115100c07410301981c04003c21900413103000380f140c0400081c1c65414920600100200c070001c0071626001088130700c1110303034000100c075808130840f43c0a05583c030010b42c040710701c0e45665202692049800c55140c5031703807814840490040340d80ea0200c2d94500841d90f016600d032300a200000091208103004036020400c41c1d80040d0b4001500101c450341c5018070b006008800e00d0a482c5080040e6841e142244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 852495629 1250 852494379 852494387
    0x17181603170403030c0204021818090c0d1505310201030b0a05090406050a0b100207080c0109230105070c0e070e1905150702030a0506100605030f13110406060f 70
    0x341c89000205141c6829518080c3c000d45440c24000d0181c0d60004071406142d50140440c030039210010302d003549034400305c0d80c0c6500c0c0c0c9200f0707640c1c400749020710300b203611061900c80303e070b50340b490352100c505170a449a400500d8000e11008080b503101d18960130105c00d10643d842c002c640c41141e464000000708100740001003c540c0b0b51502c0e1030195010910902c0343d65505040c1c1a401580207c4c0800c1c55644c08540f04040c080c06e4480310740050009505205c000e0700404c00f0400d80386c4130421500380c205000011182c2c90740510403041015100613403080c40080412501c2440745040c1043c0d4909151540c83e4204c0904030350107484508031071010310000300c0e07100d00000503c68003129402541c0400001030300307450119110381c61141002e000b00d0b40070700b10460162808150020706071140400366080040e10340204030b036408880c501003400401d001e40103c1c190390080019103207400301035469107085190380780051410f4030309072800340109440f03648030b005d2440a0812a5070704030074503489802c00f030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 852496879 1250 852495629 852495653
    0x9080d020312010314010f050a06030b0c0403080f1e03010b0714120a110c180603100e0a170d0603080d0c1b0807150903020106032117181603 62
    0x18215007041040e10760604882c420207064079041030b000743c542a0820701c02801003a04006001c09582004100003402940f0340c0800d080700d0080e9007034026650ac44000224a10550000030181c0e2020301031400e2034502d01f00901980341180c00c69030740c010004000106150001d0344a40551240081c10340704004800c408041414820001840030300f521180d4a003441c011001060204624040c0804001703408004410905101030308080d0b0010b030848810b10808000c8820b280130384640c402c4402c6c0300d011403046400c04030b5a81d0251041c01541d42e01c40c0c1c40b0007841c424010038403201b03000c000b04c40442481000000d61090b03040d030303585242330351034507003503035202c0200200b4000b580c290000e54241c544104441c04d94000c41007941e840d5286480e4181c224143c8544006900d070200e00e030200b40d0154014420b907030060380002407a41694100dd41d180d007680388224009492100c440c442500d00d030314590b0300302038a181021650785440410502d40081d140081c0518819a40100140820400c000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 852498129 1250 852496879 852496903
    0x18100e03280c081c060335030112020d060e1006080d050f030601030e030d0b011b240b030d081902071a090102040902031512010e070302010507060f06060908 69
    0x109440340c42800280100c02e007081c1c05030070f0400000d092411440340c4040f80320409030404d420080c4a482e401d1541d615003030f6640b0210101c0342024440684003081c45000c90302040f03c0d4809145030309026030f03075032003240e8090100d8000c031212141c40002002402584003900e4054020000e078441148100c0a80300c0035484280590484130701c00c40d11540c044101d43c0c3d43c41c5918903441d901d4136500012001000b90961406442c00081034101c840685a0422900307503400340da40c0801801800450302c64504282c200401c4020b4500c038243e503002d035146045446940740000002c09440359000b09050040940c0340700002051542005038241410500e048c6020200801714105019942c4805880d811581c0000b0018041c0d80003510f000802d404a401408100c00c06545a080690603042e505141c02c0500e4400e04184101a10004c4144a581c004140744002040118515001500e8642c4082410f03909540c460741010740007503040c015a00206030350303507a200809180800d8542000b6000c20b071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 852499379 1250 852498129 852498187
    0xb030a0614010212090f0901060909110307090e06040603150209041407020604350a0f0c05060c090d020a030b0609130f23010c0509030708010b0918100e03 68
    0x61281c099a00040070703121100780e8200725035140440c90000e8144501d01e450581c0c00300e00c6000200740750341d10164840480300f06003c05d01100c80d03034154581d6940021518200010b40c0c46504008503480f880c250341c1c000c0c2c0007510010360942c490b22060700b2003103036080d9200003e40018040007a400e00344112454050303042549038107420302c194002e4075220041c3c40549060403d00702c541d551082c06038030b007030440b550702d65000003201400188001904590102004503920705100e014441c01400c107824003507400405060944d440d5200e1201a03000560340ca5042186080c0c0d402c010b03160034402c080a5400b618580c0c9841c64540100a840b0740c0040480f82020411070701a1700146800c1c42c0866211340c000c49400c1a600050251542164400d015008540c02c1041c5d03610f9064010005009135507064040e03400c0c0d42d80300d07801e140c207032a035072180f031500001003c00054500c05800d00c81403101e129281560032429036800214181c405c0d80040703040c1034000042003880c03105408080742420402c102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 852500629 1250 852499379 852499409
    0x2010b100f0e30031602041d0f060106032714030408010f02030f07210b0409060c031a04110f0c0712060b1c080d050c0903151801050c0a0c0317010b030a06 68
    0x41c5d1041e014245204c0240182e803034103504e06481c42000d00683c03c03025034a04031040c4030942c4496590f120300a1052802103440c0c03005d00e0400c01303510b00f0012020154201f4055040310316954400096224095824190006002c00304260500303009403107e03909445000750b00d0341415401d00000d0720003d801030040c0680d03a40026500c15144042031034400c20342500082e02d106c0c0c4408a0040c0c401c0700b2009052074607041101d444036800d40d012940c0c02c21507005505041e04108140021034008803015006a04140490303094851844020445901d148047e5590f05030380d98244401d8841c20b0b1030480d00e06440c0e4a4044160500440c81c1c80d40440181e80028464555100c0c1351b030f188565040c9541440d12440040c4010010a04891003998040c0884030f00801600090300034031800c1d05c0c07040f1000e072045d0310752446540c14014a805000141c40d410714066007c002501d030301182310011020b0042d1913205030107506c26503003a03500811070401d6032030303503440d110035600d04490440d00712459960b1083d0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 852501879 1250 852500629 852500647
    0x12071d0106110d050706060902030a050405060a0e0a0209040c08030c030a031a1509010905090a02071e03081f080d0903050c0a08060105040f02040302030303071e02010b100f0e3003 79
    0x10f010b1219030102d0503c955642e0b0039007004c80180c10250003907407d40380000b06110b114921036000302d12481c015026540641c403422404010345500c0c400c2450070364400c0b07009002500d42045000d0300680b05a428050700c40d924481a0304582204000040c1904041618022960140282c1c414604000140103a814075100020b81c2401c1100c2d4010000c0000f00700001941d000c1d0040601410700142104403902e4900010380107540511822030b141c1c0201c4400c4280182075001381100d82c4d50680707500e10305a84038090440984540500c042161300394041c0015640410300141c00d405119545800440d411414100c0c545070100307041e1070040206c10340030000c9a4020074401c0c107448003160702007264902c2168540190055030006541404008140400c20307070081d4454601440810018540c140e2a50059088801101d2002e4025003000b090f0800d0706e210b54141c2000701a07034101505484e1010020840701c40703810301c4041381412030150004102d414681018484800e80b0b0096203060303612 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 852503129 1250 852501879 852501883
    0x917070f030b22080406030b09010302090a20070f020933040213230a0608010302040513060513481a040e06060a02031812071d010611 59
    0x18400030708941c0d20b03000420700b04140f181200070800d1001000c2a100c03039084c281103595500070b10421001c28a41040c2e0b15070341c1040051941205d4000701805003580c0c440045401030030300f2017a108030304806064015890001e4102a040c0d5038010341200301c542c1002d00c1070108490004d0410000711f0340c201d40c000c0980d444030503004031441c85100e06891000303204000ca4045d005544220192051003c1c000c04c4e45070001a4045d5010403548000401c00211410300460340c030140140c01c00204034400501c00360a041c2c0125801640340b0503002c02c1c01d07200c0d0300e45034122001034401c1c810368200c071440403050010600c0c0e8410001d040e000020741204514007a850450260346c280000070a2420706115183d905d051120000c007600070040c40c1c0720400b6a103041c1e450340b040c081d00d0340061185000c900c0c141800c81c281c0700c4241454005510b8955844201c040c0811009a141d0b4030880c1c01030005c402c4002484038000034141420a14580103060000d60040e800582010f801c100f0000070842409c500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 852504379 1250 852503129 852503159
    0x507050309031b0c060d020d0501090b03030a0c1104050702030705010506120a23011509180c06030e010615030e010b03160608070908031b0114060a150509040c091707 73
    0x3c2d6a00000c0070380c440000701410602c501000ca54442c00c0410b6000b043c5400b07030014021025112030400041e0f0b2a10180011240c6100d15150117600a009600303186008000c00c107a140d0003400311840c0c3e2024500090183e404c00c980320001030b0404981141080742c24040c0540001007140d40c4d103102d121004034030b03990b064031170000f405a0f44c503c2040004e00356256405074030605a00c0003845406180036401000c000ca80c40381d0720035a860008400e004596805004403603a50000150389250f240000490103420000024205075503075050005207481e010098815080403902c4c0810001a2021002d0840ea120200b6a019400400d510a10500a0145e900950302c00e8105804c1ca0f49422104071012a110341021102d8840000e1205407400c1c68031030340b04072032107040081c01501d041c1d006940d0890410303030320079030800402c010600c03400380d0300c4101c1c400100d03143c6049401c14603c200014140d41d5081e03030080c042140d40f60140044007101444818801c5c5a40003070903202d19004407035600081c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 852505629 1250 852504379 852504397
    0x607090e0604021c090f05191101050a021929010510050c24060907020c03060105061602060d090b06010207180c14120a0c020a1106161b09050705030903 67
    0x42c2c0001c074050744d5800d281380d07103c005071461010840c524803407400c2011307520f4020b41500e4030320501611450b07000c003800120b40120351140210006200400c01501d00344c002c2d00031a400e5000300800003410103804004981c4d158000d002003000c0801c186144480507001d5104030484401703035401030005071030340303090b10042614500d022507852000e40714043c1080203d00118000c12100c0c11811062600035400500030a0100d42020098440c1242680d407400c3e0320b417032180c05801c003600400c0715240c00005801d100c8241c001030704402040b030740096001e60001d0003070b40129903584010800c0c400402c60050740032400f80002c1030030500f00051300c140214075804131138103140c6074400800ea6034807959003058540d240380586912480c01840c40da608550072100d40034824a0400300e040c1e103a03c0003030280710300b540050b401d001a01000040c0850341c0d1026100003607d0750701802e100c000611550b00d03c4040b00300d0b81c1000100f0b905151000040c1c0d04040c12140400800344240314543d0400300460b05505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 852506879 1250 852505629 852505631
    0x160504020928030807030519050301030f0b0403110d23030403090b07080f0304080315030c01090e0c09030a05030a030b0409150c020708060a0e010b0306040b0403140d020f0405030607090e0604 84
    0x100e040c2c00700700b1501c0019000100110310200d8007001300b40c0c00501030202c254003003000800c02c4011141c2210a40030034071010b4240c07031440494070045010116100d0f0418080c1c03410b03001d400b10090f8641c0c40c5c4000d054008000410340c08a003c0c2c1208040851078206040807100e515609050b140200b400c80c060194410107000091050100720350002125445030054441c543c4a00d0306040c41c0903260021207040020a440481d014500d19003c12110b000d404143c503440c145034282802050104002018070490341d074100700c80c00c1c4950301041901843d07032084000715550035503440024195110005028012802d01c00e08100064026080c00300f080c803074400000d00c15140b600103d02c3c020300340e840003400340500000c0c0407829080d0b40082e4000c9031150b0003805521011401c1c1542c550040360094110000c0390003080010b80714609665910200320f001131704003c100400e40040342d200360085100c01c40c002400f08600d08040c098690301c2a02410560f054a2420441c101c28040040040b4415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 852508129 1250 852506879 852506929
    0x709090305031b04030b2706240118080703022107060f030b0a090e0f0a050606011b080d0f0c020c0a0302040b040f020301090204090617071202010c050f1605040209 72
    0x601c00f410155002103420204610060520048441da0303491081e140011648800424450784000040d2140c054176511060403000c840c0b09500a80c13001010700c501e0304119001d0b0068001028500509004d88000b802410100d4a188100003e00d611980310700f100301c600f11400e882426021800404548580c10a040704403820131040b4004e1100011079079101a0050000c14000c003241c0c804200322284000301c5a140312051a425078442076850001d0140c1d101800241180d40f02d0030401400707840c0c1011a01800e81071346d81e244515046120603003105c9991300406140300c08207024000f00400e060024007207600d00000801c02aa8a500020740980d4464801c40c3ca1911240e000402143c400013003152079584802250340039510621880321094140840461540c002288100e80c04003008010308a0b6850103074007401c91440d0b444164140154640c00d0804110240044000c0e0072280001c1c0014085156000c6054030464000500441c030600c159100c0352241048628285401d050301442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 852509379 1250 852508129 852508171
    0x1020405010f0f210227040e07030c0308090616030e0a0f030b0420030703030e030c062b020d0e150903430b1005010c0807061802061b070909030503 65
    0x603110700318010640711140044500b802007414103035070711146e04030740030f000c1601540c906590782d4205010281c510b80e9482810030009a200e0700404c0704043c0601a28280185600c03102d5070103000c58402c2d00031440d15404007480f40b0b02031200d1400380c50040f0303007c24501e00f9074407000da51043c0204020b2413881c8546402504000340721101c05001002400c5409061302c0f40740c001d00e18166801014081d100d5180103000c0c92420b5010395004103007030b840714251001041000d824024195611001041d42005103260384a83c2e0300803c80034110001c02802d845400d41f0020800041c001c0c01040103400c20b003c00c2d25000000d90182c002400902c02268915a01101e07042c000d0801008e00d02d0019241c074152001c0000740c4001c144900c0a03c01c6c0d0701e03046503030f5100644005011500050250340100500070000d02c090740440690301001c10001e070008001c0d03002c03860076030240c0030040891a40d10100c03580b075030041000700d0241039000c90901901081382d4025207140005400300d4580d10003a642480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 852510629 1250 852509379 852509381
    0x10b040e04051c0f02060c0a0206070c06020720120607022515080f0108030c0d0309330609020f2b06090b10051620040e01020405010f0f21 61
    0x2521203c40002d07000509000d140a82510101d0750001301500800b4005141c0280c0c1c1000d45180b804682c010380095550810100c80007455039400300d81e016824072040c404514120303c0d01801d8001e40c0e2070705460b4105a420016140e103081030250042d44a070040228040c9d020400000748025410040403400c0200102952188180c000c0e090308420940d2a0012030350100307403a8054010804454000d90b02c03041400d40324441d81c5c0c020241c50340010044030042c1d00ca64000b480d0076029500c9600c6260400c0d408682d07203c1030075070045102c16580d6840390030520710f104e06001007400110840c0b402451001654281c000c185036070b0140400f10261507011b21100007034100c5921041c03010480c068032060000010171200440070b000d21f8a00704000b06440c09401100c107082c1d0490440f1505001075035600310191210b075168158003503000d25008043c0c0300d500a812501107100f001503201c07030400d0001818242c2400d00754041010342012500400d4003c54031a0785514001c045512130301101183c14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 852511879 1250 852510629 852510643
    0xa0c290a0e1e0405040f0c05091b180d0c03120905010c060b06090910030c1d150112111801030219030b1813020102060106080c090909070806090a1505010b040e0405 72
    0xa6000f40c10002003201300600320310051421071040714502d0286442d1070a000b501c580844e0020081c00b10030b402012550207070340251450380b140000309503c603003070b600c0403c0648407129421288003203241000d02c00c2040401501444480c43d142c00d4aa441c98540020314070503a0791000b43c180c940d100c01c01001d60b00d803141102c0c070406010707015101500f071401000c40c00461510055840c01d0390208045000018009a4101c105403030b010001d1a4a0f000300a0046261000000341408050310b9014901d40b8240220380310480e03018101511020744145039003d1228800101e41003520411421b10000c0d4203d08900c003020310b519000030b180c144840440c03290824864280e103102c00b01e20400c40d0404405022840b118800e03403e0390156641e6080a898030b1005840c403d400f042c007802004428107040c4003265000c200e000c1259540c542c2c81c1a4582442c0302910342d4080c82e00710401f00c0c0180608101d030b1080005520704100300544c50f1a602c09858040d078041c0b2514200480c002c41c0910001f00310311 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 852513129 1250 852511879 852511939
    0x160c05070305062703030720010b0901120501050112020d1205120112120804020303090d030509090703151703030402040b120708030903010f29030a0c290a0e 69
    0x1c4041d81804d070f140101031055141c3e41e1504000e840011400d142c0c020054a02075a955240d41d00c40c01414142100619036440c2d000c2d070b85650311000d06130582e407642c0c0124020f014081d6030350f40f150964100b140c00c0d10030503002904048500500200181c958a1040750010340100c00745000d86c00103181200c00e80b0842003160120411070001046407444401c0c202c0001d44103810306440c00019020a4900c02c07012100a540b60300240300c0281603040c0900312610840c42032030080c0c5042254000210400c90a440c8000020394811900311041010210400036141a18821010700c2c0481001a960720005000074056034881741202002d403503400c0d402c580400d00e8010f450003d91180340c5103a60340c0141e109103104c0c2d824210f00c8152030f41288990070305090741ca64051311340322501a81c2c051000c42c5118507601407146081d4000880d0320078107104054031410b2195010707502c040c2e182003002610120b82c5001c4038000c014412065030040b400c030011030815500080a101803040c8075411810149507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 852514379 1250 852513129 852513133
    0x70c1401020d1406032a0102030708190e031c0509150703030c020d050c03161b060305040c0e01061e0201020c070f0e1303090b030a06030c0608100608160c05070305 72
    0x54020b00007229003120701c11a03050061a50503507180000c16030754810903000401c0306441c0b2038154112090390246036040100600489240030704590b42c0300c04660101c10005043c043d41c3d044003142ca540186903c4198004070010a400c2c1c01e10710341900003c0b0004114401d1000000305442c0984945d11082c4d00c444140e900140c90704002d04014024014030100e400050049040505005010b6400e403800510000c00460a0803044c501c54092500c0c3c0e0300c4140c078000c48411700c00144c4c9485024010151160360750100300c1c3d0030b0901d44a003600c0c10302e0304001550001200140403841e4002001c1d034040c40c820a1180040c0350308030060703009204281c000342c0c0c0340c05440360100d40b034041240d0032402c584c039000c4136002039035404074004080829104020000341d41351208210315110f42d4083c580003100c840c40014016540c2d5610030120403198402d0010840340020080c071403c0c4c0b4040640241800d09241d071991401070b2145030013a9091404205100055030542c05003c07080101a020315030201c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 852515629 1250 852514379 852514387
    0x27020304081209120724050c070b1021120215070f0e0402040f0501140414100e03061006030c080103021f020a0c08064618080a020c0414070c140102 65
    0x700000070450784401c07206d081005142198462500340301d0244940842c0c01340b142421100d640d4442c0022020b400c42040d480f4113600800c1403145178110949404070340700901405105440c0c4020300c1b0b0445054101950080c24847c403000a1400007141d10400a140402155844480981d500c615229619820601c080383c0070400c8100a41c0e54001c0d07030f400f42c861491005914405802c644184d00070114450b0780d02d0140c07299800d04200440218200d81843c141807000000468500b110442d5554244a1056010042ca503018861140410100c2c03030500042c0d030454000c00c80503110312100b042d46003078070013500b4035842c8280018001d00d030b44010f00c8446990b0380d01e003142e650601558001c271036079101c1c5102925030500030325503000e1400255601c060019515842c2e201801020045500c05441d21003c11601d994801d1681c1c07064030a004580e290075000e03000071324054000d40403902491400c0c0b503880103003903d1106103038446200d1905407101c600500d00f00c4403012001c80402429030000c030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 852516879 1250 852515629 852515633
    0x4050c1c06080111030907060e060d180b06040515150906040f1a1207080c04180c1b1509020d020a06050418290a0807270203040812091207 61
    0x28021070126039244000f8080a280c65810591034442912002c85983c040801085154082e0080c6410481c0042405042603114030056080c1d030f150b207110072141c8081400c00002c10000300700003600150180c0d01000b0901d000822440b000b6103010040c0d104030740c51403400300074094541c02c40700c01050160510361200d540381d41201c07a401c0b5070300410300c0d4000450b807540d641c609108181d07000801c03c4001003905407204081504d101340d0180c442e00340c099007000081011080d01d4010b8441c1c00444030700046030050074400604010340400c2c618903070210b04d0340c62400b04403021031842c0006100c9800241c40701c024400a00441c0d540c00009410070307201c840003c1c1c2140c0001c0600100d8154100c844a88015040e855007101c540e2003049a000a6007281134101c94101c2c120045864070140c1325100307450321251700b14501403413603000c1820401185000800a00e500d002c036584807020b18000d41c15030400303954541d618080e1a071071000c904140070020303038481c5c0704100c840c401415801505076209194 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 852517985 1106 852516879 852516881
    0x605030a0209070c1a090c0901151202090a0e09060a050c12132409031805030c221103151807051e1303200108040204050c1c 55
    0x40485e4100d070102c0a090a00402d0320400a141110202c03040084510050700500501e480c8004246203031500000004000e002551026031940201d20118184440984c0200141250f0000b0711680c19804280e0a004245603d0148116031f40c050360b0001e2440f94030410307110744010400140d002e2080100070070142c0d100c0d50804401d41120401900381c100040e582010865699111104042c5c100c1c0401d203201001c60701050f45c41d460140060b0b203501d03110220398058030440d510f0440600045d8410102d00e00c01250402c000c1d5039401c41072000783c00031500080d5014600d0349500c01d40c07070400b01d03c00c125644982203d05580d5a0541241e150300041060681703c0c4c42d90300c10326803511124015180d074078403210a40038228034500f040004864800d210304554650015a0f4000c0e0344e10122159219405031004a10785d210030b501200c5500c00c000c4042c403d040703481150741c044041c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 852338129 852517985 := by
  have h0 := BRFrame.cov_init 852338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 852338129 ≤ n) (h2 : n < 852517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
