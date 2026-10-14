-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1835
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:10.57999+00:00
-- url     : https://prove2.me/submissions/d41b3918-565c-44fc-b8b4-52b085c865fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 329856115 ≤ n < 330035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 329857365 1250 329856115 329856119
    0xa0302040c08040501050609060112020706060317030702010c0e0f10030902060d0207020301051e13080c03070c090b04140619030c0b0a0f1b120c0c0b130602120304030513 75
    0x480380502090740110391622159818180b8000c0c0c00d44000a11603401400305100700205a03a002e4082c0d001a014800c0c01a509c040a041140c00b80c40181c0018084042c0d4645003102420300c1c400440c45030040b03a000b0815044110022140c0646000d03409a1108c5140700c000c0d65460071004030030707201c0802d05000036040165804a41d15800400c4005000b0380e012a020042d8242802900d5000aa5082402c980010a80c0485041c2e101500113001405882494030810103510100c1e190742801c031048075169030842c5049440d0a403d4000c80c1d5909084c211158010309150040443c050b1040102942d2aa40e1806204144612800103040207511610010100c3c01c0605d095010b440c0d4032101c40d944000c0544054050b03068095039904101c641c4000700740007035004240500c2d069024a0150b0610403a150444000300642005000c00030b20980c005800105200240840c016103412248001d540b4101662181510441c024082c0707401c000090000f03100b44002d103012030382038182c0c0308025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 329858615 1250 329857365 329857369
    0x31207030209090106050d0b0307050d0f1a0f0411030a0b010b03060103091b030201021e03160f061d060703230901021905040509010f0b070b0c190e121c0e0a0302 71
    0xf003079120701c0105000190600403196640180c00c007956055004214161410340440c101c175070080405864150004030340303020001695040c20420201c0e0300003141c142003080403001d0415060307500b25040fa240b1002d01c4200d04010510b0b00c08150001060050350b86403d1a00c0c006074070042407581019a01d060050024803841070800c00390100e03200c8004c400d400c40c4000f80c82c11001448049107601b0f203003110814841d0000c112030b40c45064880600c007002042c035000e1046213100600501003030511040142c4040c00300c44500d0704588900440c1d00d240c4428105504480506454a01c242c0c0c0720002c4160a07c0d900400700d41107506040014036105085001c010401301c0c0c0d2140c03030000f81c07000904200342c1c5041c0e20392078050103404484007007003440d042ea581c42d01d1242680080a21051000059a8010020a1715607070703c1c01075001c109401b90361000801c5025000d420503c2105480f140d03440051001a0340c00c4000c0551754a400740c10302401082c0c9055055951440c0c2c09591603002000503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 329859865 1250 329858615 329858629
    0x61206141e040b061c0506010525020604091b0906050a020307061109121c02070b09131e09060f0b1c240903110f0d050d090b010312020d030c02031207030209 69
    0x4902d00404505d844248030400940e00c0240180b0304205081c814106080f45e07540e03454125078812031b0448080503462002c076401e03008541c44900403910340304509420102c004a80f4025500903900e861030541c4902040c0e5050152044880050344240005000501c0c660701c0120030f104070b1318149080a14140015040e01201004807450350090101e0000c0843c0302c41d0a01695030160024249290500820301101e000b1282403d110310604a40040c1a031042d5101c2c03410303a400151545035007140038600314041c10b100c00040356a10b02d080c4000601c60000d02c10201e0b45200100828900703482103c80038800f451031501030b0361030640e030500048101819103080030120b030410001725000540d420f000c0d00620383d94804040940003148100c8141c41c010075409407640d164104262200c2105507170300000c14004000070143c040c400d0000c4107110f0204041c2c40b5800490f8202c0d030000710f00d100118141c59510b40100096481400114000c40815101c0c60788205603103001400c11000400050070703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 329861115 1250 329859865 329859877
    0x506090d0e270c0702030706020d021b04090f05030405100801031a0402030f0102180114070302060105100e040911040e0706080105040507110d0c1403040e011a04050604061206141e040b06 82
    0x442e0f8006070500841c10244403120061840303001800703e0300d900c604040c0d1600f104040a07070711014400d51001661b0380320340c0710103001c681061107424404118608240d59601501410388254100042700d4405441451064160ba6100c400c40030310f40710040814009150241040fa0305005010400707105200920140018050701200880e00c505d510002500c0d12070030102c4140d0341d2a040000c5404603400051042c1129000e5404129204008004841c0c4280c141c0f02d842e80705040020304024000c1c0c100c2074003501300080300d040005444079195541c0d1280184500400300308110010040391410f680165031120f1103061112100c41e0768600310342044c00150040340400ea1601c01c1c03506010100d180e108050790360000a40c03601d818072001c0c0051070340512071181181c55000c803096101c4005016503004140c05010b6076103c584940d000307084900911040c0180c94074140000902403044c040011400101130001c1ca0b41003080074075505900608101e16410680711000442141c80d07500c000c00f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 329862365 1250 329861115 329861131
    0x7080c0c0d12090603111602060f0a110c0d1e020f0409031106060a1215090507181107080406030b0315090f060603060603030a11011e090506090d0e27 66
    0x50b5000d56401d02414421064000404041ca022a00140c2408000c00c40d40001c105040f00d1607000900d2001401c103204422082d000441c0106481c1e500300d40000003503000c0d580e0760094941425103401403003070940b60f002018044c1d040009115103940c80c642d5124901c640080c00c90345040d903551010409403010075400f01d00240d0034045564001c68148559030300288200c8050000307525151000b9080b01c0e0000000d840075800c00400044880280d010441c1c880d40b02c030607111503c6d81c81010a480381c222005400701f80c0d040c43c0500f0b04020ba410211642da40d8480002c07810241001c40403401007081d03d06050301407040322141d83d141d824202945100b00180e0b8000c01c0d40e6642c6100440c1030003000b52140c0d000e44d00a0040c00810781d0044266440c031002d030702c0c06144194000d2072450240207a245101d0001c844007040300e01c040c025402940049002c1d4003200c40ca520303015406c65542a080c054500080c110300c40b041b00700c1c948260740b601020126541141c086c060100105011001900c1c0d880c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 329863615 1250 329862365 329862383
    0x1f090c030c030218040809011413030b040b07050406021f090c26011a04090312050f01050126041104061a120c27180405060f09030c0307080c0c0d 64
    0x8515213072800d01003d4405420904581c00c141e5201020b5003c1d0030341041c1804841e0110200450a1200f40c0d180204002e959a07910365580c10901c480782c105035001da0301e001c844000a0041800f03141103504071b8619a00501d4035421032181e90085c0403040d078144603460788802412000c1520601600090000e801914020f4840c0000d0314030281c0800e0020252641040b0b0290101802161025445441901c001ca01c0c80041d14044815403d0024981c0e48245002d060259a4034844502d81c10303544280c0f6000320341c211500e82030002402d04c3c2100044a981303040050005040c00d032140030843c3c005000030030724989914056103240c0c820001c0f403403800400318003003105021620119402900c2c40e124640b410007054404034240e0001240b80d240c85410620004140e01d0319410421511011094080c8509003868880e40f542c0059445002082b20503020405805012041b01c00d001c0b081b2004601d003001d03e540f04400d0b45c00c405120141d9004401c0402200e480f5482c064142901c155045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 329864865 1250 329863615 329863619
    0x605040c0306021b0115120602131706010e1311120708010606050316050405010c06020f1903020904061406040e1b0a0c05061003020d061508100920031f090c030c 71
    0x4e402c440c07044c207541c1c10540340161304006d0452202195a0056041a800360745c502a80312020340c90501e0380d02070180c81c00500786c0c0312105800411004d050b542190516a65070700c454400314813403d0048000703000591114500c10080c54008d03038030344411642c60300341d030718060707444410030700315481d61b4058804980e0010810021015654103010100d2207401e0a0b800c0c24140340008054594190005110550001b45140003070070310400c0d00c1c440d900355142e5242c815603494000b070183d04040ca1180c012401d08101164003404511422000c032006020603040914024a58104100140658010010100d810940f540d082c1d0014113a4106503103e05071400761070721342507140c400010810304010f0f981c43c20a00c01603491070741707042c8280d80000c404100080440303c50440c12490fa880005144204d03001f1041800c40358101c0340c2c0c4240242e172000070050b52f01707681102822060b280b0329490340000c561100100040360000552054103c0d0024a154071a81e584412022980007542c680c40c900702d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 329866115 1250 329864865 329864917
    0x106030e060a05071e0210021809061f051305030604030c0c080609120f09040603060e0c180402240c01051501020a11010305070c0209040c080114090a0605040c030602 73
    0x11250001d162500810640c9000c0390300070176101c40e0781c110b0010044140c0030040e42ca4400c000340c1a181031001e404654410a003843e11104200b10b410450250789100c00041042c0b40504400058a85c1e00341010920380340042d0446250f8000c18515107416500c00001c102030700c0401007244540e06c01d85858002d0780c44d900f44014180710507408410b0035400b0340200001c6c4200882d04100040c800c0c0034003900d0381c43c03250351900d240c002c054245400c64507004000051203a15009048500c2190003541c1080c2400424000403070040c0100580384406880860010300307141782c841d1014040d800f60340c540b03034614244190140d40060710b54459691148144181c15002800604100750240007d0007101c1c000d685052159000c180c65505143c1c0e1000010180c03070058160001040d8020440b0701c40d0316042c649400c04202ca40030b101c807590310780542844040c568131b0072213009801110007060705103500d6852102600000303104485521252400000091540c0081d0544e44541d1050008082500c85 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 329867365 1250 329866115 329866123
    0x1c090f081e070f060c03030914061b09011d040207050a050105040218190e03040b1c061a3a09030807140409050a0207020a0b07050c0a0b0307260106030e 67
    0x104103001d0790412281040340500c040c0340710046801c5030401c10740801060030b05400800200a020308280009120240d02c00008210280f02d90700c1c4440c81e0b0140084000d02254500400c10201c1c081200c0c10f807000c800c0c0c070780d400302c05840040040c0098a008a0f079903e250801b070030701c0d804a030fa582d1284203200852900102a4240c0d540b07403500d5582ca481e010807015088021603c449c05100d40c2e610240c8409039051080b2009000d08100c0541d03540461121a2049202805c8000c800c601e0000b020492544440002411000d0b1401441c2080b0901003014090740c4801d403015295002a66100040554002950301c1d00c0741e16180010303501c1050a0140103004010044420412021244080c03066520b040c0c0f403e41e040308000043c10359410071250001e10510300301961018940c0d0001441014400040c07481520940503205800710a0007440701058103030007140e03c000002d0001a0b089072040845186175804102902e90300c035881c4019180e00c103404c0c2c1050300005d840700b5600020f154104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 329868615 1250 329867365 329867413
    0x30409180f05030a17060d084902040501020a031103040e070e030f0d020303132603040c0b090f011214010e01150507110d0c0f0e07091401021c090f08 66
    0x1715420703018586100015821550300100414210003c12440b0f09500b2014001819032005880004e60350b0b03030301010003c01c1c18080844001182c41e41c1482094000307500980c0d04862341178000300440c1ca007030350b01070f20b660700441c0e00b905141c0300c140320000d41d04098040e21402000070352504041d011f0326000b41800c0c00815408081c16074858070251072381030f500100301d03a8007140b8155110000c000314a080d0445004441c07988228800502c498034104c88882c0003503010320b10460000200d917030f41d14500d02060040c1104036900c03001605040c0455405894038060006070f03910000307030310b07060401e44e11241d4000381c003d209034042100050000c60301c181c0502c40c2e81e000f00d08200d0309019650343c0e00140d141c8a403080600655220f0381103070402c003081d01e003880549003e03240c0725001505e401d00071100c0300c0c08940e4800082d0140310005000041000d001048440c10390240c1051418080c003102810740e280700700f000300074590703400051052103440b280b00076090304005009039a104c2c00b105400c1203070003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 329869865 1250 329868615 329868647
    0x1412190e24030c0c0303010e0f011703040b0d1116050c04021309020703030605130906060b070209070e0f040207081309021c0e19050c0306011502030409180f05030a 72
    0x1191000030521005018511036403101110399241c0d01d9003040c100300c4c0101070700d162003848003000200340c6004160728140300350540d080d01c44150381e1b54080301d0314029010080c00c0c1a504204400c1c030001a16000074040201080c01c0420704180c054500d1000c0c6c0c0c40b18000701966070760420b801c01003100500c56000000001c0301c0950072b00709091100e0b144804684564800c0c944d0014400d820076009400c0f101c01420001c007034501c021500c40000001d801800411121a4a404800324506171a4002c0d0380d2a281c01a02452030355031602400d803005020415002d60241c40d042418100c0d03a02d60009041103131140c1113464036441c031060304070711070002c503000070030307a2401031000980c0c4aa02c22001c4a031345050040200e41e583c0358100040c00c250303a600d044441b4116890461090000028066212200582c00c480542c0e0340d9001c0c030500300001c1c1c40840c0c016003080104200c0c3c1d025a4201200488000c602e0080110003079940090030800b81104545c10b400c0426140c1900c0d42025013035500c4520 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 329871115 1250 329869865 329869879
    0x70507060305010f0506160204020301061806050403030806130603080c030711090103050a030804031b08040509070c02011e140d0606122d020c011a1002010603050a1412190e 76
    0x40400034104e400c00ca02810340103410201e0810300c50000c0650010416401410465495071180b0004200c040114008014032002075400202180b043c401c60f004c990300b48e62103114940b204001c21600280c030b1441c4600198980c040400406c01c801c1c0207110b610300c44001980c1c0c0701030514110b0b408800c068000c5200d54054401040032440100d4050b862580c1345c94140840e951300d02d400d507101c082001e00c21480001e480400310402c0241700042050315000c40310641140e440b9a401c46503041c140b0b100030300261845802c0ca4415417651800c1030109a83c0c1070103464028040508900e070f03009150603040003520f030101048515042024444200f240400a00104404621130501d100c28883e0040c1c4c00c100d003240b100c904198980c15180001c2185000340302c0d02c4101e17031140071104203ea81c132622030407208a1800c95180144154801c40e60302002a044121040c0c07030315840326003401c1e0408400d00640c229400c1140405000302031640c44c50640c407401d016034141c010501005a00c010b0300440e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 329872365 1250 329871115 329871119
    0x50c0a1e0509010e04032a030302071a100e060d0b0a0c03061d01030813120b010f06170c0901111608070603111204050102041a0912030405150c01140c07050706030501 73
    0x390381e52005905c140c041c00c0c00c240703403c142000000703440150340300284403011085003041096459001000c841c0c0c003940f200315210ba2401c100780d00000d001d4030305464400c840c00c0308102144511002c43d5105600030441001c11405480b084840e48003180d102c4c4403242e8410103c0019134052098102030711140c0c1100c0c800d424a64861140880180030142002001040d501458010340328860040c054901c0d600300d91405500d84909030410a015904200301490360108a09200f1a08080342d0f110764012150346440e6446d0b0030f4103642c0100a094100302603d0b0340c1c41c0840100708080070a034200a4a0400b01511300012281400c55641104082600f01405c141070307680c860081e03403013500d904002e41c03580d500c96180044c0280304591081d10042c2e48040c20300746070415030014118401058030703149104c0300b8101e122a100e02c0345020344c540c0480b100d0400c99a40340508050031000710b06200006841280c01c4030501019401c0301e40c07030048c41000980b4400c008041c804240240514142884254 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 329873615 1250 329872365 329872379
    0xc18061802030603010b060705102004090f11030108060703050601020c0108040b09160609090e010606050406080403111209041406090105101404080f120a080112050c0a1e050901 78
    0x265800800031040d4010010415941d0294806054501c00416150b919042c80c9051503d8a9a403907a6050203890130109542004880034845a18205240641c2c9401d0520081030010140000050415070392541c601c0e000c955140001d50203041100014095032800c0c0c0c2d0010181c0d500188050304541090300d01c0c41459801c900d1144d009980024070160640d19108030038540081d0100d1015100c00781000040d495030042d065105689410703070700b4442036507044078070b90a80e002482107800060040008010982c89841e000350001c1c800d00e4144104404141d0352440c010840782078000404001410703150a28051054280a1a0000b0070a22501d415400034a00301c0b014415140100c0750341c1c01c42220680316079a511011681607074070b140c80d40e485240c001c1c1d50b422070901058042c0310364020f8200100030320080d0341082d40c017650b07000c066030308007001c0280c5600c007604111030903c618151022640c1c1c0305140b180187c2446103c00000071424082c4070b0070318000740d102900450180e00184014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 329874865 1250 329873615 329873639
    0x1020a05250f08070f050604060c0e010c0804032a0603051e06180a14040c0503061e16111c0912031b0c0512030d060902041512180c1806 60
    0x2ea5000542951200005e00b4400c000500c80c1000803c1c40c0501c60802c020400a984052258442c9a48555242d030501e801504c2c10031400381c02801c0081c0030b201c01c20000e00ca01c055581495140c2d000945005283c5012410300485a0810780c0440e803184208440506402a021500b004030b102401403030030441c000c0b139241400b2100070341074560a48001006462250059481e000f00d60701324280916140c00c06090381d61007805442d101e4000c0034089007020500a241c40104250913603031004e01c0e05c034607460505000e489404001800a0417892131602d085c1840000d4000c056a02620601c02410b44002c1402e1103035040003019201e4501c00c44042603020b1220501c000320401c00070000355450501515500c0c0303980c1b000354083d0110300b46002c0c810010005c0c000a1003408410b00c10a40c495008100b603000300d01980c940d0310318480800041c01c2c07080b00c041004082c0280001841b02102003200b00880581030203076200d600303014041000b880003102c52102c454a03200c042203028181305541480e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 329876115 1250 329874865 329874893
    0x302100606120b0303131205061b031f050a0608060108090f03070f02130504050312070e01140306011701090606090801151701060807030b040b0f0f06120304050301020a0525 76
    0x4003075540c0320895400c4c2c03002c2040b10750b00351101d403a00e06115134840f043c2c034a21740f60420469003405000c000c00d004007010841a010320040c14010b500315601c07590004515107081d500d800014450060015140c0c5807422184041c0605075034220303443ca0310800240c03200001804080c096444680b070f540070604003005030b51045501000761206115140001801d2103600c982e44800d6624000500c010840c0002c02000d45409003039807003503140e030f4030f001c190391400c10108450f000c0744502000385080000d14004660168050608000e482a45500c85240c2c1009800c000c600b07503601e030300500425030030805003c01080150003d001c00c1c17000552041100781c070343c800d00b0410420105001e0300301c8801e4001c0e10250940303070111b40c81280d8a040580985800380c4043c0d40c842610400719100c81e1000c04802d01c603442200002501c1d071108018440c0030006003404132440c1c04207000c0841d0503a0300703000400c091015542c8071034580354100d00104015481101c15404503164041007000945e0070102c03010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 329877365 1250 329876115 329876147
    0x306051c06051008100c0309080a020304030c17070e190c030b030729070c08030711090a18020105030907090510030515070c02130e030d0e010b100206040602160b01060306030302100606 81
    0xc0c040f100341005501800023801c0041200c0d00100d0b2540240781d002005d0310881780a942d828502a0b03855002ea440c1c45100c48003c041a00303d610107102613040581515040442c07007101d07400c0e40c5c48841481c0c040352506140701c030000f42c480800300c44500c0c0821111015003840c12010124444203110605a4100c03007100c6140c103032001c1040002c0c0007084022800074007107002074a03581c500074506281d454407003250a0344546100c801050002402e48501c0070000319114400d005d0300038540054aa580004041c2c1c0c420340b0503914089030a00450242d2400f0302e151507854210b85055141c903908203154401e04101000d510b008102002c2d40c0903e000315842c3e01503c0c60802500429440006031071403c18001085c8030008802134079407203030f81c0240396001001008104090901c410801d02c95200c0183c880103a10410204012440c20350080103084800d00c0702000d94622a9a011001d074026400700000c60740c3e4a004000341a01840f40513400c0c001400100310150401401415004009280007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 329878615 1250 329877365 329877371
    0x140708070c150e0915120d020601060305070309030509010c060b06070303050f13051903030219050a090603061805090309090c071407030f03120e061005120102090d02060a0306051c0605100810 84
    0x185c0e0b1500c0305070130700080080c0d000c00e54210251414001e50f07961003c4c0326810011345044002900341c1d02c24465544141d905941d05e91408460358011281c400144030b00f6034456030f8405060881e40d0390078000341a082e2007502c01050a03e042e648a402d9018000c01c0391581041c94925180003c41c045103518142002111181c3d609a090804400901848203441594400c0030301400a451300305026103030800141e07540800c0c6544401d012801d403141c0b8403582200241c0c1100445108405030002a406542001100e080c03100440010b2100301003a00c6840140e040000c0318414071002c0c03c05480d000380200020074030a032543d6241c17171900320750950140800c4000038132800c4035019a0071840c499001d00c03007182c000c0d041c811b17400000aa5a0300c40c15100c0c503585207130302c2d00c50301e010700071b491382c00100520503407109495800f4820b9590002c0400740400d5910040800c0341d0340c415104071141d070503250b18404054050b1800008581001d80400100c0d0a0200d0410240301c00141c07100c0d545004074004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 329879865 1250 329878615 329878651
    0x3071502150106030b090610080613020c0114040201080912030109021b15331c0b04030315210312110309010510050901080c01140708070c150e09 64
    0x101d003400100490301e4031160103a000007034220341c59080080201c904490400307454844c3d03800c00c80f458101c0d0f00440081401500001c900d442d0410700e00700d110720103203009442c0c50782c03600b012800c4601c002401c96015403400300740f005550f40b01880d10b52100c1c00741c00602076980810306801c4203000500c00c003c0c4bc00d07000140c0c60802e41840c0280c0102e48001c104441c100c1954081e0359034855001c0300d407480b218620300f6002c00c41000c1070401c6800c0c1716203e00b5100c404411201446450040b2082400c0e0848008100400150001c0300d5a803142d40290760000d043c140750850859900c401c0d0340f10a170301004c10b02003941114540804204190760500f8100c4041c00304002210141000200c1047c640c2c0c0d010081140701181904124456040c5a04860000d51190200455001c2c28000e160300d80c0c0c844500c00001354040d079550807882c60b00d100f800e41407511507a121120396110410803900010399007003c2084409071200c1200082d0701c0d0420100c011025004952840002001440c802e041d04c0c2e07072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 329881115 1250 329879865 329879867
    0x8010f0b01050c0615131404030e1804020d03021203070804050706080103050606010810080304031a0601020d21060f090b0a060201020307120b04180c0e07020304120b10080106090608070b0702030715 87
    0x6c600740c6102c0d00c2006005500b8150801340d40000c040b1030a80c08120401c910710b1080c079002140b03051095400300045d0444d1506d8003404401f01c1682070443c294801c10b10000c01100d172020184d80310300180d540322041c81c034143c80c0c40343c00e10b07583e5403103001800100401440018004150103600550038a4080680da40702c0041424851155104407101d020004010050050110600741801e128901c2440940c03916801240c1d6804001c4400d0002003a41030304035060200450440d0301c400200f000410b0644c0c803502d4802205200b07074071280d0701ca90f81d5901440c4906085000300001c1016000071402c5182500d00078180348901c039400c40d0102e91f50300c2c0d814150394859000f0000340e0848403003440c851120f441d050b043c001c4507008041580e45080000740d41c6610001c101c0f0103072440c0f482104200783e400ea44582c11080050071105901404404c0418100e009200b07900007482c4500011440520300002c0c50704091407a0003980102004120000c013503200003410104490b55a403810290310b0310a00c1c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 329882365 1250 329881115 329881129
    0x114040c030915090611090a050d0f06050c0d0e010b0108070f140703051b0102040308090f0f030f030d11040b0415050f03040f020f040504022b0204050108010f0b01050c0615 76
    0x14009081070f20b84181c0b052000c00b01d901091005210b02d004010030503641480030100e0080c001035aa006444040c1071029040141142002910076408411900c0041e913840c0290341044031880c1404602061012181c801c501494960300d406600800c01a80c4035000202030343c0300181880c0611010b02c200002040c440c079191344d6070040041c0201e0301c0e5417030740c075008025522500024800f40b84240c0b154254100610880302244d91111580d4680740d824000c0c041d440102d00c2c0c1c42035000300322180719041920113124103000040e4070b402550740c6500103107420045851a502500d051401840140a0030790300d4802c440aa85c1802c19001100c1400c1504443e039116181041e00c4139403000c020b02041024012f04424031901c2100d800d06a842c0140a100031141d0440d0007941c01320081004c03905040c228640010584084080081c0d50010b5401150030340e042030340039070ba0030f80d90b40c2494401c4a04620903035a11305c07001d2800c1d5240c002240001592540d01900c5007d418402d80040c1c036090ba0380d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 329883615 1250 329882365 329882381
    0x60f0f030a1106251a0f011a0c03070605060301050a060f0e04110d050d0e011403060d05070909030e031b030601090b03030405041b090f0b0714100203090a030f080114040c03 76
    0x250b0f40c0394100c01e0510f01a1101c400b040201c4002c0081d0600305d80280f0350316907440c4902c0000c401284107a203440304900b49018511021904e142c000c012001031070350b0a1001713080250090341c011440381041c5040c03500b10382d0020410100b4501d88081032220b1610310100b40115203440c000c241998035181000c404012a071113800764450600e036070b40c1e010403402240c1c50b24032070000d8403039661603561480159526806041c0d1041420800c000044c800d14001302080c500318020f400302c400b450b032078501c420101e5444074070a0f00402d1982000c842c0616080003040c8480070f4500080c191882c0c03403408240e0350001030080491031625242400d5860b00d0400540e0b00408000f0828402200070001008411002c0454040010807030140841c02c60a00c00c407003801c40700d4035011030346005465214040540714400102c0d25500611080c00d294180d070380091806201c04101400320030703200d441c02601020005142c47d050021603c010003492085243c403581c004810380700450b08140340c0200302c00600a40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 329884865 1250 329883615 329883637
    0x60e040b12160e0f0601270806190f060302031f111b060f090d030f0f1b090e31021f09080a02060a03200a08060f0f030a1106 55
    0x202d80c0158094030000b42422201814030700182c503140c040c1124a80d81003284c10358003059840b80216007050320580440c098500994001c4845600c9803441800e04506031984100c1c1240f5015401e15609640301d00c0030b01c11443d81040100e00d186501007501c0b8070701402c2030142c052000f8030222002ca10b642005c2032007540305c00b5450f900c04c0c480d0445000300c506190406410700c01c58000401180101c411a0701882168000702003400d290384003100546411701c1d070481410340302c0049810040160040007000f10600602000b0380c9030300d0074010802c9407140e210ba0688000d08e070901102c41c141489100c05206a508907500003002c44074510902c844040c00290031403e6140102012030600c501c02c070720181c1c07641d40c08040c0d0381c1c0c604003155200e0b00000081e5009508101c1c80c104540030354482901d28542d05040e4508440c13400400343c06422a010010209085c0c0d4100042464405188100210100d03140d20015106c800400d1f076400e18404000e0407100c03a15000c6403da40e803102920038240c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 329886115 1250 329884865 329884873
    0x90b150f0706020c0d08070e0f151b01060302190b070206030402060910030605030d0c03051909030206040909060b09041109150a1e080a0b0a05040f1406150a060e040b12 74
    0x9480140e5164130740e005c0407000500a1000c18000c41c0b041820507001c0c00700030403034443c2c2d6030004100502032018410814606008003c0000c0614415900b4050801c2c045c0c0002020b600c0d40c01405207600741d00c00311034400e640d001003d200e181d44420075a0b05050301a580e280c1c4a541da031001c5034903407242d448800d9020581413621116981d240c0c000000350b510a40c143d8003100d1031100d090741c03900c0f0965001004158140004842850b030b40c8800700c0140300d41c0c40c100700b600381d40e5004902c1c15407240c0c0080d45031301c0c1c40f40400e000b07220300b6015940741d0742420384083d82c0310700d01619889031058a021031580300f180d01101240003050039240010b954140289020411542d07160050300310045c5c0c0411503088500c400c40081c1540d0007003144603040b80c00c4034400f0a03565802810500608000380120f848520449100c0d02141a50125034000d0000800605003410320f048041400c0303600306c180d24401c48c88400c0601c0312903803151642e56948030032f480200365020b035030000500e29a03912200604c07903c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 329887365 1250 329886115 329886127
    0x408070206040f093c091b0b0a0201141e090a081b07090b101b0f060f1515030b010509040f02030609102714010f0f090b150f070602 58
    0x88a54018442a019490320440b50719204e40b8042a0100525950340c05c1e003280003811281c84201e4000e1902c0c0e134450758802000c1c0700d400c404849602c83d607810150135604c0110b2500d42e40d50b0240b05104a81a41030602034107880c0410b811a40701b07144002c8040e20a1540000c2500c4a00400000c02001c0d400040c403525000340081c02d04841c40001c0794070302d803407003031000010350545684549130141c280034000e02080301c0e0840059035038044502c0649000e0648021801c08240c001c3d03a221400c0b88550404a43c0b13a00d140d603884140c80411031030f0100d03010256070402128154a000000d158030310b0070007041071040000183e078180102006250003500706201880740c90080e90096218130422503608100c0d4680844407184090036000b85155103462a40d140580503040b5048540709000d910003041290b0858809400c4103401e170b00c2014005020001480754a003071203a00e00c041d066040703082140640840001e050b92001c0500d08900040c00112007940e151a80304586031141c20440a640d102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 329888615 1250 329887365 329887379
    0x90615120c0d060617040b07051605070e090f07091d120a0f09120f0f080a020604021c050304050f0301140c1e030702030d15050307030b0f0c0c060408070206040f 71
    0x140c481c6910b82c1d56985880030101c0d15a006002025010320486904296a0f880d50b642c001001000b0700000103204040c462036441402c0710440c1c0401d07500c1200a010882e1508403410742d102c1c000f40c400c1e04160441c52244e464510300183c1401181d954130b03c085246040c0c9160244800300c00307030a01185c1c0c0200320b00141c104409400901c0342046558446117004d41d140d4089034140018050701d5403e1224448146c0400c2044540c1050365000d101011072048469881201c0750f070048138000d01507000101004158904080040640c125102501d400315006503602c0d0346900c142c1c0111881000348985880b2191401d60190382569085040e4441c2ca090010040f10310f034100c018541000703a0600e0844507090344007400d403809540c040e0021800c04020328001d501426040405030084c144e001c400213455682000700d034000394040c034841e01c1039043c00124043c801c0380045c40003651103010446140a04030004e0f41c160300c2030700200c0140d15080d0a1002851510855000415034451750350081918 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 329889865 1250 329888615 329888617
    0x311030f220b010e0108070617070504214b050102120910061202010309020f03060703140c0405150c011e0b0f01020c0303030a150305030a0804050d080105090615120c 73
    0x62800004c4440040c0e070f0701d842c0a5030703900080c024600025400203a0400d40500c0054184d08400541401c90030a92180b89075641c426000360001e8000380c40d88403c0c400c0c40000c0c411401c0381100400b05101d180710001460700900c4d02420000f00c0310030702d60740d10703541c840e0182103407941300f030b88040250360b0f50000344568252480252050301050003094040440400e680c4510412074080c110380300c403000d40c00e800560007405503600590f0402007807210441255403e0000307074822010b0380c03030006161220f05514608101c0003040c150064808000512256591004d400034901c048444903503118224880c030b40c058031460a200f0020360790040d82c1c1111900e545c01800355010244c6600c00f554110000481c0e59004003103d41e9056001080401c1ca82c03882608032232802450240c0c190b4030542d8035a1094615884919070f04006101c030401d101c1046003c4c00390980d152500c4c580840c0d103506000025a0215028150074424250540d0165061442c6c1c000c0d505004003440c400d84a81c47c28150302005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 329891115 1250 329889865 329889869
    0x19080708010605130905070201020c07030c0618050307410f221109060301140411071a040c031b06020708030f0f0f190504150311030f220b01 62
    0x826440030000c03405078851000d4800d0a1401c404070b541862134109003800a0002418000441d5020801061401c1c820010180114400e0070800d181c90300e0407000404418484503600c00b184c0440504200b0b40c0c0e00000e25400762001598001078000814240b04286100703950049400100441c003070111002c1c01c420100403510542e80103c0c112506002c0050821000d0080900070507020380c4107159410390ba00030b04201d8001603034249010901c0b800102d90380c1003640141c0301c2112690303102d4124100340c082d01410510180105007460b05071344e80c2e50b68103101e408851520640b20000101440b001c40d003c074004603000403540300020700d4403141d0540c1100d00d0146101512500d94001800c100000803601c5010040503000d06009039526006540e0340860320306c2c01129002e02c1580d07014150410760b07070310442540d103403940d6440c54450b409141d2030f081008801494540a42d40000000b0441103035440090000e040a503641c03004919000c41800c94075a000e00d2220b084d4200030461007240c081c1c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 329892365 1250 329891115 329891117
    0xf0a0308090f010c121110021206040f06030b070513051203030f0c04080c150c070b0a09090507210f0c200f070b07030203090402070c03020916091802190807 69
    0xb203240800010b41e0480d940d0a0003e1102d005101c000e000c013031080402d41c160103d00001d813001c00c0d042e0402070040c1d070000e0401c04074020220b01070000c0c42c5014807030f08075007a11528040c0710851030f40d00c2d00035907238000600413030a20100051694040407112002d401401c0028840405420203011485d40d81c0c00444034a04150f1101001c40d0440041c0005d0740c1c00c881ca402c000745101480541407010381d0a54608918111906020109403c40140072400161004101950b03c0c2e10a0020040c4400441e6110b2a0410f10341802e00ca0840d80c446004100382c0e0001d000132000310014070808008290896817500440d103868a41d00805600484d80965100351542010800e12040009620f4607940040180103500c01ca0041100c41d0080700a000002d0280c0127981c10b0203c01c001060503039100410440303919100023024401c51600c0310413150080c2041d0008126168140390260502e00715004410658101c4458085400c8160b01100c0c00c0e44100706031780c514220702c520040c00b119800d866440c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 329893615 1250 329892365 329892379
    0x4171606150e0a092315010806041704150e2403011409100608071211030a06171018050a0b01050a0b0c0303150114031602010c1d040b0f0a030809 64
    0x40c907610084c040c004c500d83c0c110031903a00e00c0c5030020b040b0701c1e940e03c00500d5100d01e003d040d4440301c60798040c60200d4000e05e40000509540e14041c50080545d0450003003040425900f0700042c01040c01fa4048009c51030f1050514078540034000e0001465000e030380e42c2d004607000b04441003040381d83c0c2401c00703035040350700c003680c01c07000d01203484200040102c1c11a1444942d1350100001c012072842280e4443e0040802d0a0920350000e070b60101c20282c800e41c0800107141040041072107000901440f4900003041181c0f0a03813060740c4060041c80d120071800b209038803610b41b82c0034001c80d45800c0c100c030300c0c003000c0d0b01a00700c601103003880c50b0805483c803091003001e00c1031550b030030001064400f1008030745c8500a0500034501c0c1d5991521100c2d00041c1e02c44080d0304001d152480c821114003014001c60007140c0c41c0141c1900100d00d03030381c000e0035103c03490340074009c1001b8444074201c1d003980c6100440640e0780403200421160507060104003d203141d044640da0000001100005120305e080003000d0348041a00c240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 329894865 1250 329893615 329893621
    0xf080408100614030118111903110f0105090907120f0c0c1211030f0309120a110c19090e03090a230405060d0f02041b0302090a050904171606150e 64
    0x25080746c1c00085a58020300c41d4540032000600b451181c44022003004200543c011b00c0203400412508058100311020b0050300109101031416102541052009190203850700c03c032840070405801014008c54207100344d01c0054454a079071a0840c4030102a421420002209070000040240300803440590f001c09000c2284480c6600c20429085410b450b20002c5180050542139107140342c1c0002c14075425400303403150041d905010b0900404180e0784503601e18200099a00b20300e0f041c8250002000e21030100c803a2034240c071003000a40305c3c040360318036080020840f411002d110305504c08d540c40164088040900812840795190003440a13000c94041c08812002510500044035130544950394825090b01e01440011414001201107074805030002c5000740f020f59400c12001d284c14103070301c0400c0e008520001c95003814290480105421a0807071543d06040d111070f14400c0d950010042d21520010380c1102041c00c060346130090701e03840340040000c2c80381025445080400f50141450f510100004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 329896115 1250 329894865 329894869
    0x140d020913030908061e0c040906060c031107060f0f02030d0c081b0c0a1515091b02060402060a0f020a0b090105150415090c2001020304020f011b0f080408100614 71
    0x101903c251b85141c02c4910a000448000b01043c200074590810140704020208610200707010380030081180e6201c1706803214680c9005004811111f992080c640d20110080082c42d901000c03894243e071a5003441c1105d0b41012504a0640c03080205201d0074070305005211060992000b00684100400712203120a02c80b400031150385c0b442194404000c0e42d0100c0450b00215481064414106010140028555400c040d0440316080c07540e009010039595081c10000c6120840510701982c0c1461016007898602030340080c895002d02d107000d204100c007182c64108468001c020300040c0300d800c411192410300e81180302c6800b81c41c01311003200003030001c041111614101402a002c2081c07040c18a41c1030142001d254000800000d5100301c108402c0d602c485007420800110114007500340000940d4a14050051150b89d4840c002c11904121038605a048001840303141060b400d80d05c000240c00070304981c1400440c3e07000341d80000409002e00b00a090021115612130f10460f03859440b80a2000d4103481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 329897365 1250 329896115 329896123
    0x2210c0a03050d1b0b0703050106020d0207050603010308070f0b01140307090b06221e031109070c0b0a02040e191a130e0f1e01150f140d020913030908 66
    0x21000b0304a9029840c2e500281d8020001440c420201e80c816000d6075425481d001c5074168203642c0c2002080d9160014801d4607414030543c89001d9050004140461030032010030158441440007408120303020503410100030004030240d0300d003500300400312100e5866100381031150541e1100c05120b4490418001004030320750107412001032008240e1801c1050240458400c0801c0301c20718074101c00c0a403c04542c2c440c0701519420901c82c9041980600390071460400700710703082c50032000d00c566550810400c0c41503000d4544900d117070f88903002c40c0164451810803000b070b020316044140500f90040801c0002c1d62010b8031040079034251042440284140328034401c00d102d910032226001040361400049003451034100c2d05050714000c0071500d0150b15144e40e10306010719103110a0454101a50300b031417031142401562010b010300d185000c0510303d848e81a01092100d03100300640440480b40d000a1582c415400d0040c041e00500b2211582c40c251690b04041da0116004030082201c070301c004107110000007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 329898615 1250 329897365 329897369
    0x7020306041a150a0e0a1409030a090b131703090d060f0513150207031e030509100605011b0302100e01020a030e032502131125020a03060b0a0302210c0a 67
    0x244c0300049541c01c00407181d555130402062801402e0f2206105182103200ca03003454403a0701c00d14007030b64440380030100042c000200c5170b0256016003028061700080c000941c00355003c40c0c0d9590351813011b40e45002d5400e0f0440c0034201d41c885c0d101401910340c0050019680240c0b1f81d14062210800090b51002000300d500b01403043c010b02090842c441ea8141d9911a9005020310b40c002e0905c211800038103205124666944210b42c3d00003a210000e101c200902002981c03c010007290007032100505280c0001c1407140110080e50340080c0282001c403d00d0700a000c20940d40b0202c5400b40b2030014884641e5020b0343c0200038602c00607181070b810680d5008040144c944201b0000c88100319900b9002c1d10707078076040301034200341c0e07204045010086000d40c091080c0b9686e80001e01d090340d1a60304440c00c54a4082070400102c550101040700c82c00169117089505e0107580d4440d07030014048080d040454103150903a00020740102c4810302d007007040140000c01e48800752255040300e02c0300c121502800940c07041e42c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329899865 1250 329898615 329898619
    0x80607110604030f20030c010e0601170309040f021204120207091a1e09040506040201030b01090312080c1c140a0b0a03060e010f0204060804110102011e0b0607020306041a15 76
    0xe11112000c40f44107a142e0006000d245c10130500d1020310409403800e40d070041d04400d0045c0e42d65001110480410300c44140101000b02d24403485003120354545860b172082010700f92086a0364544141004003c1d4140c82062201408071f100501e03062070111026104141300340054825918001154001d070700420202c2c003060404005c0482100c01401048081d25041e0380034035004c01c01c2e4190340d1f112101402d10403406000142141d0815000140071a840c140503181008400882030011840038009160720724003514040065944030704418146015190810909041c00e60614114000a400c0000d04010f00803d007421a158284203a044071840104242c2090f25120308001041c210760080c001c51060741300100c1c4146451041c00102d90054008202040003034050105100d0071481200c03103001c0a0008000b4900385905052242840c1c800c0c80c8500c0741c40700c0107203015407212020359200c507074007508540c581d00306071400f9420502c41070b100088400490001803030301a0700c20032103555140c0c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329901115 1250 329899865 329899877
    0x120c04060903030c080c01110414180402060901111c1413031e08040b07060506030a03022107050a0311190308060d110a141005090907110f01020408060711060403 71
    0x2440c0e0701135400e07100c0810240d901800031b214402c6044028000d003003ca65203d41090303030ba01d0030844078142d106158881580100d510702d50140a2000304c0c20550b03013041c0c04036556a111848440100c610f0305c0d442421080600440035600c101c46c9580040740070a4065031904121101c100204980e130340101202c142040f06d211804001160000304040014600350302017004071043c3e034554030743d80c3c0d1050b444464140000903021061100c0c81c4191a0000c604030007030414400c4584009541e0021558050019a2881c64900a0803442c000320381c121580102640c00303a0400d8200500342d4902030000d44064014600d0b241c0780c010848094100300ea60507280c4241944810003444050765042c001196040032081315009140c0c0e4058841c801860131401c55400390712190140071602111401041c24440c0501c415038081e0f40d42d862440c1c3c4107c00b4076207090089081e000c0303103203048600c0c1003141c01e951001402042e0302801084e4680710b01c15944a000c0c0b5490004c2c402603031510210740280020301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329902365 1250 329901115 329901119
    0xb09090601090c02030c0307050d090b0304020f0f0102070320030607090e0c0a14120604110c0c100507021e0f0d030e1207080708062e030314120705120c040609 70
    0x1c0702d54040711044400384101e0341410700c4010345d14a140e002a000703503240e5014074849600d6560005550300540710a00569040d418660301140d810b4140403010f9100d810040203103030140e4400c0000c0801180c01c08071200151801c2850300c1c011801001c40c01d8040d001c0d400004d8135a2707000e051140200c1c5c465405c007070b40c20b6689030741741c040301d4101c985010204011548220b0010a901c009848024160410f2980c00c0c144001040201d8010000c082c104010a00a161f01c07007002140c400d130754400039100c4110010110804564030722425100a600c00a003000d1039508400d9281c1d00f418042c4242c0c1e1401d41e000503202088140c4d850301c880100000d00112840c151410546003007001c161480088880294680002908102841c1c201d094250b01400400140b4216600000040f50b602e035004400004140d01c5d042c0b5019050001030203009165448071044803614084501c03107a90349621500c9410a4000185140c0c08004510880c0381d000c2e0100f0403541c004011941140d101e5210b081c4070f54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329903615 1250 329902365 329902379
    0xf090c050d02100c1106070501050a0509120906030604060905011203030e03090a12300210020403020f090705070f080403020102060708060f010c020d20150306010503131110030f0b09090601 83
    0x24a43d010840340403010942400705c944803000600300f460b10940000c18a07150480d04442201c40047c41c501c3e0710350180c80a541064000b900300d03040404d0035a07065650342d9441c004038002d001c00e41e0100f4880c9152400011ba041c508d8038021481a101780e0b810320030660007200c00c6035240906201594010804035017009480302a5800389040c61003281ca1150112aa40c210b07a911401d40300860424440403590241c901d50600071a01d0310380d94070404504050551700840c12000d26622003600074030942e0003041185004034152007000f40d12036030000c0601103524103260150071a1004a015116440c040703020305014011907403190304090010707086e903410600110340d601001ca00030f03604121000003290200e00440c016010042c6c490701c16441c043c82c2101400342e81d268541c0d0420440c6010300038805503030ba00ca011290040942c401e042070303078202405e10400450260b000c0f6688100c0210040c00003a0b0940c02c201ca503500c08020411141d0700580c20710811403000c65018685070062030041c0250 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329904865 1250 329903615 329903627
    0x10e060304020f0909010501050301060b19081803130e01050420031305010f05090d0c0b0a2d05010e09120304080318070b030603070f35010f090c050d0210 68
    0x100b0700090022540c02c440601060b03202e24182c400b4032150b5151401801241000d00501c801803441200003440c201241001d02c08174041c40804004000640000c03e03101000307440d01c420041003440a403680c078109030500d02d104611900c208900310100074000500c40c9824401c01d00072401101c061170f0291050014296560710003000c00c02c1d000c0c2548198030205109204200701c52000000c0080c050606070001d0f4503124620044404015803210103c00043d40800c04a4000c902d40c0c101042e101030614801002c00081c42c1c1124004000700c40010748404c850700824100c400b01001043c685d1150152140ca4410a00100e5100401000400c000a00b0400215440301c140840103415503a24103003541030110940c4018003c400c0803081c000c1901c1d09201c441d008005030f010301c800d1285444030f0652210b038040000c80c000d0076140460300110004403081d0262000400082040d203900c9a8200010441400c6c10b492030303d0b503d0808500c509004440381840d9400600b0781e5844407030704e0012541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329906115 1250 329904865 329904871
    0xa060311151c02070c090e031204020604031502090a060201020c0a020d02040209030601170f0316031101110c07091409070b250311190804090c050c0604050d1805010e0603 75
    0x2103800104002c0962100c0303400b098003145548000540c1d41c18079400c0c0080c44200c81c0c1c100300d0541340b030848075503803501002007190803c150304560081c01d80c1e2240005941c5000e60341c409812a41c0088825240c1d5807030340d008100070340017119100e04190b212401203080303010308c0311820010307401001c0f00805840d0000c610801e6a100a0000d482c00319401c01103030034406d00780c0c010401230b426114500303a0048148070041090030000011414512210320310f18059050100180070302c890f05102003038400080d08802c001800c030424080e40d92011a480d607581c0c030f02901c41c81c00300b5850a5a0030740800500d1032000c0c05803105000174114181001c207003d0140c0d010304c800e440307074032841d180c1c418041c40c2081310319668a0090301d5494402040260680c100346000060001381140300091000140040096509580f00e90b140050740c0400c8410640342c80c23044070f14168051260030f041004000300062644040f030b400b50780307141044120f01c64a5810004500860303011071408038801105003400c5000d50781c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329907365 1250 329906115 329906149
    0x307110705040609060305061b041502030706061502150103170c19050303240312030a0b2101360f02060a0c0b060f18091f05040b0a060311 61
    0x69015607410008040fa00543d00c80034206850700010014480c0a02c1426806064100d012084881015001c42107114900410701030700381c00c2500300102d52082041d030703000c83c0d8404000c000c0039407502000d5041c0300640c10560010312440c0410401d02c03603e80401030480ea0b00000811091503556450b051780e0b000482440054401c3c50f170600301805001c2144c01c940e6010b64080c5076a070404042041000700d182003500e03101181c40b01480200c3d1800650401d04600443c00c01d40c49484014a1801078040a401a580000c80d00d9103c4d002101c102e01820924003000000c07c8492001c3c2c3c3c11080002c00e12010a42c03d84030002c40d4807078004c01d400780315503031840703051a0500b200107035001a80380d41021041c8000103941d04540da0410140c04000be4101400300d0390034201c482a030380010440e407070003888901603501d003030082120688100700345203000c01905810b62041c103111014000809013281c0036944100c0c00c801184c006c4805210309001d4a8001c00008400c100d0001845840b0b140050008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329908615 1250 329907365 329907373
    0xa0903150603021507021c1718151c0504140a03020318090f130203012a120e0d111e15060a03080403030c0c0b0a02010204061e05030105090711030d020a020d0e0105030711 75
    0x235085001143c02014001c240d030401f40100b85502d01481401162040350f61642c00b803c101c4440b400180c0400b210001e4001d07a0b001c2a039699900d030035194100c1c00340c0c2c0040c03144620354480c0304054000c00900044d200320040d00c000c80210a0420034a5074094a032211a8454903000c40c0718510249603c080e081c0c0040c0c00442c0d652000c00f084040700c00481c0505001070000040ea001d40b80d4070025514040e050b500007407008002c0160810303129000a036a2106101069010442c0810b00388104003001c1200808540d001e05c10641660711040e00150042c00d081740c050005070b1a190038005501130703c0c0c118059500701402c541e01502d03805200e0009940d114035030b034070018000705076a005109003c07299002588862414001a1241c102500348110100304204142886948801a60b04440c0c0440d00301d80d003616403403004e0f5806148102e011850740000649045521a80c1d0010b2400403020b03400c651004080603170844104400305030b5140011020400b04540c10300c605411480e0030301c00c80a035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329909865 1250 329908615 329908643
    0x5011a06090915091e090706050313061103010803070b10030c0501110c040507020d0f140702040b060c07030813150f0302030a060806011e0608100b0a0903150603021507021c 76
    0xc913201c40444080c6005050381c240f4101c40361110140c20b40089140e0300a160142c1440405461400000c0c000380000c05002100d000748800c4e5045070038204c1e03040404682d01d5071101081512079001e40416a0401d00010128907a50301040c0c1e5a02126006044101d4107814200111000341c20607030a03001e03d105505901c251360783d40e80300d2140512110340041010040d43e840141101c540b00914006000c0400113001160000d0011201c18a41c11500000c10441540000d003260191500f040e0f614805d404e0088100081e5000070031202d1940004040c0e91a500c0c1688207500c082a50100002003030f01417100c5000b0700a07006160071040320f80740441c000b921a00000d00c0d02c2c40903400703010281d0001e0064140038801441010141c0b440e0b1600c0501c41c40c00301c8030104489070501c244c4807044c0b00081c10149061003103440c0d40c0074680c000c507100c520010426540b005407805000c00c0e0700c01d40b80410100b1400307800c1d2040b243c00c242e015265659000c400e40d1500c04034500703900309a840c4188007400e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329911115 1250 329909865 329909869
    0x302071814130210021902060708130b0403110901060f030b030102090402280c0b24220e0309130906020408060403050d060503060105090a0f0e01110705011a06090915 73
    0x1a104622544030311061010034010080b0050f4084041d00541d0013034107140b00d1ba180311031404d000f0190159200780c0d03181ca00e0b1130300c00d100340314500d01c0703003040c48042c4000301740000c0c40c070300500c101c82c02508440d85816844003007040002e0280f2585002c80c10b81d800e000c44060098010445d82e040040005040c0300c0280c021509a0b0300c8131800e01014207030050003110056400600400d62008d628100c044400544d130355a2400c8000341c00a442c10700c0381c003040100e403c07000102e8030b05004050580c0240612041d080714034803003800c1d81d4400311400e000859030701c04000020b0b0340c210742d00101559151744040d54120b00030480c4400595000d41c0070000400c4003d0700f040f82d54040c2d446030352070554a600c943e01c0c2608548a130340040e4443e400c49001000030b6610200440d4001c5c001400001b000400034003800018078060f0131a074100c0d42403c220300d8004500901401102d03000d80000c0c40001c505003481c240012680601c15444803080c072060303d0302d0600c140707050f0307104405a03441070a41c510800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329912365 1250 329911115 329911151
    0x80a030f1d0418081c0e0102090a1e080d08040212060601080a0b0111070b032d240a031b0504090c03350a12051608130f150e030703020718 61
    0x5210304078a844540c20303c054100d845402d1031b0905410013181000c48180008082d10054821000c101d0030540c06842c0c0c56508100442c000c00c800f000322403800410542c040e00c0b003042268140e11854101c3c0c41d003400c07801d020441c0d6116060503981ca40701aa140002040280000c44525041008000629542e5002000301030040c008903003150384c480c941003807101c040714031145006115014074103901c80d42039915440ca07034100c0044000c90440d600c00c80800081902c000f0703200c41e44600d185900005000c07681403580407240c90b1140f1903814613110030521007542c1c14208028401c1e00400e00400c04111074a40858400450165007003014404003001e40c0086010b004164400c0e00c005030f01501a5001800000e409903605002d200d1440e1911303c6c0610a50000420303401d03c411000014112160020300301074039580f0402c0e1041414030750030185184004030b071868441c14584449500c205000109441400d6030690041c05107604141100070392401d00b601d003949075602d4450030307071010b00522 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329913615 1250 329912365 329912377
    0xd140f0c03030c0306031e101805150402130903050f13050a0605040f050f0f1002030c010f0b0a05030609030f0c0c04020a0e090708132307080a030f1d041808 69
    0x4030080c4c0c990601700101424a808070f00e94101d91440c80714000042c4e8400318609095820b00c6100107007520a490050790764800d2958014a24001d0109001e2241c43c030800160082c1d00a60342d0080781d142011301c03a02290515003014020601c1806922407408160000b0f1203801d1540005400d10380c0daa502051842c45250841c4012580200e0300740005038040c45004001c00e400c884d40710003000c070100890071054580c1980e074010700c3c850341000c10190080085a00441160008001d4003800755901e000803d008910188035480c1111700240c54680001d410303006480e141c0196107000c1a80310400300c0d5a2150400e1145400307401d841c05030030713070740da2024003079041603500c2e840915080a4200454140010084030501c174401041c40141022002441030311648801c0426104445490302d04c1521210040218507204035070f80420001c00100303d950100e072207901d0340346a44811320000d803042c0b45078440741035002e4402e9400100d645400d811000c003100150f44800c1010b051901c0f03c0b102c0e07902c45 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329914865 1250 329913615 329913631
    0x90402040b15030f0a0204230d1b1d010509061011030304030801091404170f040e012c0f040209060f0a06031d0109050c0409170a02070501110d140f0c0303 68
    0x100c00c1104401301642002d90055503107404601c0c0030b04154000490700111940d40305140d1007521034156030344903428000802e580100d01e480c003045080c80e03004824880b5015601212865000340b401940b80f1881c082d0503078000a164210580d100307000e001752007600c00101402c0000390800f040f14414240019805140241c6c2c540d070031981464070810079100340c00036140e1040090401c12020501c0b94851031040072500b4005680c0f20043ca021905500441d040700088180c06c0c400000d10310040b014043c0c42c2d1702da40340d50804610220050000140d0304807140c01b46016040300040062a01d2040079600080040c40b40d01d04d6035040d030102c0c41010307541c2c00c0031001c240d84003020030000446940f1144102c61410092103180b0859031020703181d0b07800d41100c030300854403807441c8810043c6150402003403017080310032182c50b080c000600955404052080a000c40c400c41d80c10701036050085550504028291207081c01d040c040c442c6a100380c3d00824023140307645d40070700c0101441c2078107000541c016414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329916115 1250 329914865 329914867
    0x11803060e03041512050603060f01090519020d0b011e0e04020a1b0501091103190b070519020d03050a05011d0601110f071a120106050306010e090106030c080609011202090402040b15 80
    0x1043c5d001041352405018984a50b10100c00c01c9002910b0003038441c15a24100b20119003512060101404034070103400301041c4500100d1b00b2651207960364003142041400340d03112214030030304001d5082c120586060103000901404406803481c20981c0080582c02c0240ca0301c030b851060b050f400c10011f045181d208a461b65146c0540800b482a000c47c1c0460f9054114098413800c03000b462609210000b0482c014160fa00d41000520042d0282d816141d030085115241310000070650700003900c0d40030b00c2e01d8280120749030102040703443d012842014142d43d8880c508107071840d0410284889104000c010504002540c6407542c0c40503003e00c11011a80301c0e10b001810400d040c41c00a080100c0001e0316010b560106005c2d601d00010600c402e40c0c1103c4071030506543d00e8541a0048035448564203a9035000002da000003d02319900d503000c901e00541c10b83d03444040d510340310200300941c10217200351900050300f0301203100585010f0a8141d0068401040010b90b102644085410040f03005001d40781110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329917365 1250 329916115 329916137
    0x112d03070309050115080d08100314030406031104050609010309020a0504240510020618070816080d030c050a0e0402040905040b07020f07030c03320c0f011803060e030415 75
    0x21007402000c80c00d4583c044083c5881c1d051030041c6651f1803408101800b04400c91003c10100013030742c4035500140d07800102c0c2c3d04941d0100b0b00001e503280d000344210780000b440c20702c2c6801545a01000d890507540b00408061400001e00011000703004001400c0c1e80c020f400210009440c0d45512802d285200c2204441010071019030003001000030319405240200c416807600b40c80300768003042c096030291007028440f0780c0b0f440c240c00710b51508044d03400c003000034420800c1c5d02920701a030b05028000ca40e040c40440c2d0042645000480c21754403144090004101c0c1030020402460081002c181c1c801c0340070f80014180369807910808140d0307d0594007620f0700e100c0788003840181d6505001031031784007000d04020324855107182c0d103002c122072180c4000742901c017014030020789019403141c40542c007100d443d114204051a100b0501e0700d80ba105c425152040000d03101014441d4007451f040003c5841c04500805900c2c035540750140503149090340a101e0740001c000100c0d00360b41e0b072080c1c0305114840796104403541c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329918615 1250 329917365 329917373
    0x901090b0f030105060901030204110f16060557090108010608040b0c0a03090506090c0307230d0501090b040303020406080f160e0a05040606050702090109112d03070309 74
    0x704144949802030b41882e0801000d40c440a0105045079811360340021480710703030f031019030b02d90180c050341070058500001c1c0d0840720500d0400040d80c0700d000d10003c01c040d8031002d8441602015200c1d90020070762f201c0003030058070074100380034a0314031030704c0e0740302d582c03980e1b03031000040001c0d505c03110700d000c0844001c12044005c0d688140f00901529840c14002014141910741c44980000140402852900081d40e00031540c400c1d040030b03c4441d4040126010381c11710304000e94461807001c00c03041c000e02c10002d0004ac02ca845010014204100000c1e9161501040701805102180c0707240644041d0340b64550b1000046840303490707038803c600a0b5030040c0c5640c2400707402445000c010344008840e4030a8814840c54a0400b1404240100181448483c400c40c42d170204080d045a036212650140c81c02900042298024000b4016148210b45807410b41e1380341d90180c0b01301c07400f41070042c260103800d0141032010350785080024800d05019030050004c03142c4204002150703001700c52020000b922103580d00c00304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329919865 1250 329918615 329918629
    0x405072105010608010b010504140f060c0a030210021303020f0604030b01030b01060801090b060d05041a0109020a0230030c07060f09060e0606010e04110403050111030f130809040504050c0901090b 86
    0x280c1600c04c001d109101503d03000038810b000380e0003980040c1e2100b072504035881d035403101e444c05281c0c40070300126100d0083e407404035112013154109501500548110071503842181c42201d800c0103400319040e840d1802c42d02400310b8080b408401c181c1000b810040030020540c04030318117008610803070348602c0319070400310300070310191303061b4070000c03a40e4100315a00e075003540d03a41d05940b51000c00e600d00107003940e20350070840a4040c000320140814000b600010a0351045034004011040c3d040e022102d0040c20741c0202805002030740c0511801c418000e4400032007007032040003960040f1b604a20b4906041017500c82c035048402440c4032104c025521000c020070000c460048a054468020140500d45081000a01520101e051743c921031540c407070b007a0780c0c2c0101030b03015100a5a00303d402004410b20300548054242c1c42a1a08400b441a16000450500c01407500760005540b00d040d003806c004a1400380b001a140142080741c482c0601c22050325242c6032201707803134000d002c08040800c094499400780420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329921115 1250 329919865 329919869
    0x9050115080309031b01030b040c020106050f1504060302161b050a1203080f0717091b0d15020703050903160f0b0a090311010c021504180603050a0b04050721050106 72
    0x540081c0b01920441e94040744002c4a01d080c5c0c10f26608544035980100c00910018044580c81071815030055801a415409002a0791003603035081e0400b032910302001170300304072809003c0c80d20f2030402041c4407542c480d1300646040700c100076a02d45140401d5485400f400342c40c500c0c0d44444c5940c01000c101915140031a840201400308440092540c13a0310004c00c03420004007e408510301c5c0d1408500c0c0709105400d00560022184106012410201301480d1039a8150b1107204a88045403400c40051a0681000c2038a035406140b4000f40c90800c40140060342040740c1c2942480418080c81030b0546060001848106103c658080014186905486140c030a50070011701c000d8240700d80044250000952400d80350086401d05110b4090070041380c003814159402504105501217180307045110074050400d956501c4070b00300420400e25802c0040300e801d40b201610550080c180c0340042502280d4240c0c0090250065034007594880001c242d040050075051510104160241741c144078083c490000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329922365 1250 329921115 329921129
    0x90b01051c0209040519080c0c03070b0a0e041b0807020609072d09020c0601030c0905040c2d1e05040501030f02090702010b040504060608010e010504030527030109050115 75
    0x5041c100c0d00c10681c1140c400424000d00840045003c00c040c00810000c0d1400b841d41181411208803891800038000d4100341c00d810902d1040003220825440d000c05c05a043d10011980c0a04140c80480211902d41500c000d281d041991031180c909101301000c86014004072507150000e990400700b00080c42c080005010030107a13001801d0610240081d4048000030703070b42c45040902c008004007100440307001c0c15401882c60903c006440f0810707040202e01c0a040302d01424140c031040e0358500c3d00310305454048030002d004c070044800900282c500151040c4060701788040c05251030500ca550780f980a155a000061320f00400d0801000001000e0350590250800b42c030240003951641c0e840034420b180e05030009106a60780400298124400d611441007420010010b00c414106400c0081c0100303614090700b215542440c142c28001342c014000c460042e5495035429103000c4132442a00d14503007007181c0d5944440d445400090b410359090081e40165170150000081b89407210008034a0401c0701d42c0324030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329923615 1250 329922365 329922379
    0x160f030e0108090606040b040b041d1c0504170c030609061b0708090f0315010312090602030a23090a0b03100e01030f06022505070e0a0204050f240706090b0105 70
    0x40f01c8210041852500518143c4021950f04120b400150181c840304c0c0c081a049490221409400c0320354540306200f104101c0140e40d04108003502e48402e11681c1c44001d00401c40400040080b400c0e440b491001000c864001e89030705114850000e0b040c80c40030345521505911803030500c03140c04008a058000320903080446840c040072541c95181602403032102c6841105040000c0e001520240503030850803c00700710407a6250307140c2c50402c07640001041d00c080016000040414420300000c200c0303001c00216205c1000040036080f136000b98050500c864168074800780001b01064555a419201030b00540d040c00b40c40e071800c09040300391903010303610032514610070200410101d650140001038071900060056921610b00540381c1880f0501840c3c100c5101364018200c0c14000041026019103843c00400b41403238682070212401d038016406665404040340c000c540b070b02d00d80801440e41c8030380c040b070045a01801e02d82c00940b85810045050b1900e5407101c1503281049881c5071142c4c0504001c0307642d0703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329924865 1250 329923615 329923621
    0x20c0102100612150b030a0803090c0f0102210c030c031e040b03130602040312020c130c12020322150b0102120d0b031e010c0318021014160f030e0108 66
    0x95003c1804400b03015010307901c03810100482d20709a030411a01c1c00c0c0c01804030785142d030880c54000031980c02281c8201040c0140021800b443c42d00c04c180e0842c11805900500e602c0c2244100c07100400e490148080c1481000c224a4803070301c0003030018005585004011b5616181c0620000c4205004042892603004080005211030041d20082d80d030040070141d4844820000d0b468900001d00c51031f04080d0968454440301c0b88c61907030004001c445404140c03206d0480846200c3e03010181d600c6940044c0108180c900310240c050300b29800f541d80480c0480b01e0711751403800450f070314180b10040001034807140b4842007081d85942141c02a29088031083c4001c00601782e50041c0c0740b00c5400f0f038402607040c0580303d180314501560100301419072100302c00d1411205901c0080030600030f1100c2c0450b0004a414044400e141c03c1a14040da46a03a03005800c1d0fa083d941d400c1000c407200c2e41d002c884444540070901c816510700c44030014060186101340ea040010078100d040140c4007254082a0b1410401c000d420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329926115 1250 329924865 329924879
    0x2010e060f0301060c0c09060909020f09250e040c0203090108090f0a0311010906060b130602010207050a08090307030b010e0f0f150922051c050a0503010e04030e0d03020c01021006 79
    0xb128111029840c003240d4603492450080e14141c3d880e84408803150600c138001c1070710507450380044145482243c0380d244000030f038420b2041c00303141120070200d40ca00c0d8801900040c0d000c501ea03540b4456940c5003400540c140040004d0443e100c254180006a00200361300341c80356001400c0a0b0010209401000c40540c60144e041c0d4400148d68010b0420480540007044100709401411040354403031014400951114602c0d4445e801c803d101e01c20b013200300c44000a0090041c03003201c3c4201c0d045006080018142c3c0c48a61040e400b851400740c1500c1841400404202000f130200d01038100d0014000b00c070700306502d000d080004080e22200d03841c1611030034000c034142050300101c1d9541c002d03100718141c0e60740c1c251281d803008040c0e91446102d03011040c5980401c4400f06608240409070120b0f44500395180303c0494140c000d07852400086002007005000c07500d004041650b000e44249040b16610861001081038240711131011070160f4403203942ea00c2c4a60301030119000002200744104181807404403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329927365 1250 329926115 329926117
    0xf09030813051906060918030906230906071502090102060610081609080304030501150602010c090902030a020f1b01060e090706120216030207031e0209010612141302010e060f 77
    0x41c5062414403842c80c1e010041103030000002806c00c40010041c40400c1f84a10b100b540810a00714000b07564100045034050040e1001035111001c00c5006100c41e42443c017540743c0380d007c003200c1c59100b4000e106040000e184080348069194040e0401350302e03900c60500180c906000506820321400c06c1d0f0034481001640700000640c015081c070541c007209000044140e6002e03406030411101c40c000003601006012054120328010450050f0010480f80d03981401c90880700c1658050b0006a8490030412886490341c01840c0c21017844100189002c40f400d40581d4103900100507090b04010500790300720030203428402c0c82c0040500300e4019149140a6600989070742050155030240300501050f000001002d41c117a0314800c444030700070500d043c002c2c240039640e0310080c80b040f54040140c600c0c5442500c00f0900c9240201e60150006180340d003000800c0d2940d902c060350f40311546666030f0155250204002c43c003805001d201c10001c5030050640001050086901d50703443c0610000c0111035007a9440d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329928615 1250 329927365 329927383
    0x14010e07030b041407020705010909020c03030c13090207151506120f0b0d06020318242a042c04170c0f030a030506030a24020d0f0903081305 62
    0x481d00007404440440010018443c1402140c0c0c00c070718a004000c0304980001e540340c25900700742c0310101c01a40e030b01d000700264070030005089229041800402c070300115800c0030b04142c03010060190000345c0c80c2d420749801c903040480160780c0d40c410501400c003212501d200c0d640300e0010382d000f150481030a01c0005890101d414050000319541d0b08041c0c1c0c080001603102c4003064400400501c0481a0790800c000a50015142c029032072280325001d100101c0001044209401d00c0c4d01400301100701540d0040300f00c9001008a00e151817440168419501880403650070804a500e40c03030381b11818116903850300d04043c411000300912141c0603580d01550114010fa0244e8800c1311030040c0290b040001c03080307021f0b104503010181300b0061010b8001201001806620030181e50402440d5a50010141e03a00c64181001d001601203171084590440131040ca0802003407840c5006d46085410b144120446885445480030161740d520f01000301070340001301c550000140242045109c0366078958984a070340b1310b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329929865 1250 329928615 329928617
    0xf08040b0c0f090d050c03060619030b0408040504020c0f0f07060e04110c061003020f0a032301180c150905090a1808030115090603110a030203040512031914010e07 72
    0x11591804080b000801c85a25110207820040c0d0355100340380c030a5503000440c041910074043e10002440ea4140305850060020141c0e4030750022500d076450303001c00c005000e48255018042000701045948450005240841d130507001001c1e0041c0b60b040d1141040c400e20340044560f0071140003008907039401100f52000500c11180041c41e4822054580160711400e0f00c82e1a19002d218204401480091140d404480c02507030460400e1083c04100000241d090200034181520340146410030400548604401600d4000000700c00014284844032081c4010b800c41d058402614144a20f40d0703010303980c11000b40d441c10b24803181030400b80010200d4070020074071010141d441203100c1c64480604c2c50b0700d40e80c0e6040700002d692035858029441d88005013070410800300380c50f6407000884e28400d108061041c5000200c80e400c20b0340740341d4100d01951001d0420750355846074402c100391031000c02c001540601c1d980704a03c20901100100c03078007956102d00146800a5181004120110b405590b1545c001d03a2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329931115 1250 329929865 329929867
    0xc0d0f0c020309120703051509010507020d0f0806011103130602100603020f01050f040e0c04032a1a070210020c1302090f10050c10020d1a100e01051e0a0f08040b0c 72
    0x1415104a1a282450b1b001070a1391180d180811186481d18000e640203180442c02030083d0781e2002020380c0d40d03e000ca402ea00c00620441210102a0700c503418081d08070b1014034200c0140c5074522052440e42d0000b03010b4840b075011008040000300c0d01041403d068134000c180a1212616503000039030102042c42602d410700400003115502c619041e422a00071340742c0ca210b0300307070541050404008035400601044a01e070500b00c861035140c043c21030403105161200c03c800319501f4108a654401c0043d118406081d495082c401c003401a0f481c06180d40e03060440e540100b86406802c070811290748400020180750310710401507440c0a890f00604280d2464040e42d0700e100d02001820110741d14491207246030198003c00449203408040342c0c00608800741e0001050090380d6840850f400d032400207165030303a401040d010400c120140030ba551314010207014104682031040721b1028042c03203240050725015200001590b00c3c240c07070304240c04079010aa1490140b440d40350aa0312804c4070217000d44021010341c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329932365 1250 329931115 329931139
    0xe0303040302121002040b0d0c0c170c03040801021206090705030103051209011b0516090605060405040b120601030303050919050309091005060703080105040f141501020a0b0c0d0f0c020309 83
    0x20b04024800c50303001301c02021941c6603070f0f89090340c0380d0340c0011641841a50400d40210500d80c441c445296550b50420b050b843c65248460100c0200d90040340b260025000501000480310020302c050541c000c0c80300c4416810f80340400c204450008018548420b104091006002007030300000c4140840c44680f010581e00c2d101c05006070b131700010700c0314010a503c008000c1c6004010021a440c0d1070781481068500040d62546081410798505005140d0803034400e1004201510f01a000841d00d80d0029050314500d03050b1012803418078000360000c3e40460784032001d0081c41141003007145082d11f125a0710701d18052050381c480e0780324410300c04058404c0c026000450810601c1a02410003450001c08036903030b451545c50081c1007034030309120742c1d8480e80c40d2040040300b55020340265465602c20b03655051540e9a500507031a22007000541070f40c1140328407d40c08000450504800340a510407020250300d81981c2801441a6000c82070100b00c031900703020340e6520854000040d240210b10484441170028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329933615 1250 329932365 329932399
    0xf0c030219050a110f0f090606160f200a05041e020408070602010506060c12031906090f0e0106080c01260705040305120708070623150f010e0303040302 67
    0x1a0400a40c801220315001c041000c1010000d041502188900c04a074407011210b010441049841540d450704003840d402800704915001500039800440101218148015001c505c2200c84403a42c0440d200d0602500380f10074841d00502d666640740842e10004035001015000c10a660900e01c0b0b114016900c80c1c820007421102c3c070040340c2d160011000210b407540da888601595132011485030b18055480c000104850b8280001110049038140004001e055030106521101e5030001b01000b403487c9088140c070789140081c1c001e4100030102c0210100c1c980010655000c11035490128400c9036a144c590304006d041000310f110b1184020034240390940844c2002039601c00460783d0300b0018590031110400a940d41c025001e0b00036240500100c49081098620b480d0072446022030141c20b450052011200040c4141c02a003c0e180308088a07403014819402103048041060790081c40314580c150038202c0c0da08100411411000c0b0034a0500c803401c11b500d01207a1244200d01010b4011400401006010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329934865 1250 329933615 329933623
    0xb161e0c0309080c06091e0d0537141c1d0108060a05131d0a12020304030b0c250f03030b031504060f02090a18202209060605030405011103070f0c0302 66
    0x155601034a808c0c0070500e00d24205440c1c01d420342d0b045640342c800c0344060110701d011031400c0e140c00484446204031b286090326141600c0c1182c0714501401c0c814803a4281c001101c216065040195949411411900c552070411034101d0700d0980314108031003141041669910b0b201d0500848905403440341106100c01e030404041c181c0950828016000280310130289800002da84074464050740d03200311001c44010049841707208910001c0c2a03c40c4000101e0b403010700050040c0a85c00603400c41b2140d590b085417500b0844004030740c0a441001700c5102c410141354160241006110003180035100c00e5000034280c1ea51031001400240419645030103456025000368101c07526003000400541301e050b40d52545d0740c0302c507620342c0305019200d00f0f20a038144d43c3c408003e5804944034078040c2075400d0400301030700090340340302c404100154101c07440e80018510f0030b00d00c2014054a542d070380c4c281da24a002d050250a4071003039200000d420404008000c1c100f41e01c200c0030301000d0300c01d04e005900142107040403450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329936115 1250 329934865 329934919
    0x100b0114070b06030c040506010c0b0903090406060e040f020a0504060320070c06120504022809020f09010216031e08043f0b161e0c0309080c0609 64
    0x21100300184150511100180c2140300c2c0e941102103901c4540c01e0001c0c8815110700b5540300340400c06c19214800003407554181c40345c3c08240e550807a41440702200004007602d4440d032080c8040b95403480f588415003080d0084017000504010300354a094034100b00207041d44150303c189020550340f41d00c2001180c1c02c401c0505c40ba12900000e1546941710380c200340581502e03d220b80b13000b20301d410401032101c10503405402e1281c3d400030204270a809092842c2e000241c104805d059914048080200b1b40c0035881c406030081000155030b040d15011075600191811403415040402144c4126007080003c90b82c07030442c00c01040c500c81c00c3d0000030380c41c07610200c075000303030307000b0401003c40c2c21a10307540e61241400200740c41d006002c090440e440188010741034000c0150f0040d1a01c000040016420010350310787c007440c203c0e00e1428031042000f189584400302c241d960f40c080029000301c804018190302500880203090340201400c500000c10300001e80f18410803000a0150200c8410381602d00c19039418400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329937365 1250 329936115 329936147
    0x51b0102070c03060506210a0f06020c01060905150604080c150d0c0309020a15202506260714070b04030801080d02070302010206180703020a060206090c12100b01 71
    0x4507068407841e1138405890122911070140c000c0c40e01030b11100390349468020302882c40f040a4000a00c2e2501d0f002c0c0b01c0200c944083c0c3e2400d0b02040801591f61091040500401d1650000a0f550074200135405110348240ad8041c8034407810301090102010200e24041c49050407a405040c00c1402c9941c02881d00443d8140300e03000d4602001d0a45030364250300640c85962085492084043d21607111222420240740c00304000342460580301c0d0141200618211140040c4080350302031030b07803800310304010a1b03004550b0311a150310500c10083c49801c02041d00e60f000a610700c94038075098a0100004840c00204503108100f000050340074203d881c0001c07a40c082d50040c00d00710316854141405000040c007031284009501c120410b030501c032840400e0681c00d407135059010b410345855180f250884200d8003940d03e24213001300716000005a440110802c01442640c024020510300a40c6980c01d04002181c5d03070b4004c5280d0040040010310115040d21590000340e00000c0e600c3c04840129590380100c61018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329938615 1250 329937365 329937383
    0x40b03250b19020706030c020a021e0d08070210080f04080a030603120c11010e06040909020f03030a0206150a050907030207050705060c030414240f121005041b051b010207 75
    0x304603910a0300c0980302982c00340c0c003195005583c82c0c400300e0840e40c40302410401a04021128001131030b0001c01c080b0b03410043c400d00e0f00701c01141030004201d07000c06241210030410015010045050005a02c041042a428903c41d0780c5417148485501c0d500090008100c031900040c60181903003e940506c002e0760304042c0c461907515401702d02410042d400c00d4169082009950a204607611074881e40c482c1302c84c05400320742840c0c03500300a90068041a0001c83c1d00012404084800d43c904001404004440303038010075a50400f06e18040c403603c02404200e0084103013000c1848642c41d40b2400ba038118100b07140060fa00e41e07031030501d46c0c203050031340d00001c1d4001d2001034114001b000c008068800d4a00e01c04076a840100440204107090404203041c4c00c41c540c1d1092078503115207050010703240c10081c84010524100e4035009101503100b0031070b42d1441003000c5540500050502c0c0c0300b083c009005100b803004180004401c081d2882c0100700d00b508880e07102845400481d0030a40586203229480a562 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329939865 1250 329938615 329938627
    0x70812070309030e04090c06230a05130806040314030c13030302030306040f0608070303052508040f12031e090806010b03250e04021e16030e040b03250b 67
    0x1c01038500440164001846601d0740303c0d01e03103860301c903171509203521034000c0c01164500282501c00f19142c00248840d40184600f885130340001d82c000b001084c12540d996569507c0a000c0741c242108990002c20300e030b5200b00200b100180d0003420300725480c030300d41d01840c2d03c0380d881750110f0089100e00c51441b4141440300c28000b00300340e00000614015002144e082c091401400e0549048a00790b10610301c01798414542000481d002d02c004007442d01c24000c540f9071700c0d401030301c8549030b196820038102d4001500003010021000c01c80c1880c0054940c0052120358200036450050442e116044002c2241c80c10b158610380303460041e20f0364002800008280e4900d52f80d260700e02042900111040548004a40e41d0441d9029160b070001025114503221510503000f00024003000b03420030180e15401034139502c0720155102054014280041043c0c0400e107400320540790040c203690b010306526000718182003041e40d199402040d0b862051500d0803424910040d00201c08101c0010b41d448074140403000030300303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329941115 1250 329939865 329939867
    0x120b0a0b130501061416080903010608060f0901060609053a0803060307050f0d0f0303180f15021303140109060c021612030801030b100302100e03010b09100b07081207 73
    0x2240c104d81c40b070380301d11865000142130203407584240e481403106400346d41030020008418101400810360043c0000071160740b0f0b02c141d9072070490b05603005006200e40380100981d04500b40104400fa01480c50321420017840c14020a01030580e549010713040c115406440361500d0310501e80c007040c05c0c0f0b4159521180c5c0b2154101038820358019031b219070180c0683d10020826007403031940028501c501400300030464132141c44140415402030030440c00c151715401e51440342207003d5031415429005c0c0340b03002c1a0f200c240c41c203c082c000c490103070800c0c2a40103006030505400a0303040001100d400c0707544860305200e658090f90040c04400c038010081407030100d804284950000382c0d10341c02844d00e030b000500d580c3c48400829501014150090008000000600c00207500403041c6811509039044521126100e0f80000c2c6803034050303018a000210305203a0500700307150074040c40c0d640150a503014125400e1004003411400100d000d5203408540004000c020000300d00103c0e640c1c1110092040118144000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329942365 1250 329941115 329941121
    0xc02040c0c020f180106050d0e060c090102010c021c0f0203040806010e01030b01090506030a1101030b120d0318050c0f011b06060f0605031e0c040b0712110304120b0a0b13 75
    0xe000ea016a4548607101d001d4200311304141010b0100000c04000b43e843d0041c111459440b5080c2c10060540b01e11003040e10a10420241e401490040744a6440e481240c0009084034010694181198083c0c0320514803000e904643e010b0101852802045444001209a10398403d50307021542038428070000141e003110301c0c3c4005043c0e81c41002042e040341d9032503030010141c400640b14194036410100c038202c0002c4090781ca442641d0010f05020490110240000b240d0940030301c003111554004181649102d68184200034168a4000100000d0303d515110190ba031000050f65500072034215020f050160b0103480c455403c042c9400700e40706c00180900d0101301500e034500c03454141b103182081c046106806170060340d10480c80f03040d2007030901c0c0000c01403480010026002c54000d4408100200c7e1441c0c0201c0100038040c0182140c40c100869400c000f80340551130304e80f640840e04207000920000705000600c204403500303c81400c802c1d45860290000810240c6681644480580054440341715070350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329943615 1250 329942365 329942387
    0x1204140f0712053304020a0e090a0201110d0909021b0f0706121e0c09261b0607030e1c1a07080105030c06160803090f060709060504150c02040c 63
    0xe54007181d004030307404080c540305921301d5120082c00701c03001d004038036070f18240710b038040d0000701149410381e40d41c4140b078080d840c00d0311860304a801c4920900c00b5540c100105d00707448507041c801080640e60f0000010000c1031680511070704d95030000380034141d5644413241c0002a01510083c2c48140c094807807525030300e061f03e21401d000300d0810400714031f00c14414410512400c0141c02c035800c0e010f0001c0c201400610b540300501050064924021034200ca1442000164180500041c200f0080e820040b42c9031803621b4000f0402c1e03201741d1703034440c0040e00e40c0c40581f04035a5140c24056855910300c0000b681c0020868081c020760030300b091071a07081c801a2400d0220001c06401601880d48a40c4011030700c000023409a950168000011480b0606102000708610300000032488040c52169480c1c0d201644260b652600303640c031000c00c484d20040148000c40e08982d080c1044104103242901c0034089005a208130307100071001d03458040d01c1900503609105500d82c0248100004855040f010700942e9140d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329944865 1250 329943615 329943623
    0x605090d1706130c0c0b13060b09041a0406091e030f0206060303041a1e090a0e04030903030305070c0605010e070207120804090504080f040605040e06061204140f0712 73
    0x11080007856801a400064000e50000d031598221900d072052080180204852600412003007039250004101e2040c03113140941c0178110b40c80c2d15500785d41030140640309009001d92161282c1e005110000f41402c2c40b0096060301003682c194580d0311400c044c4010004114050002402d1a410404a10101141c1a00705101744c407211000c40d00c14008a81e100d0702292210b80541c000c11050000003900c451000c5201c41c8070704801c1c94110b02c102c1602404004405010200c0d0f4085400d0b840d902c3d050005401074040d00c104440c4624054130020b1035080f01d0b20010381819922008951440d01c69510044840c0c0c125509000a5079103618150704003c2c02c548480041c000e5105c0499040318034952006020780142c01982010b042c1a001d03c000c002c050001c44212000700074514040000002410040c078264942d2a151392816419a0504a000b404580b007004100a141c1c080d42c03803400e00c240c0298008035071005801c1c403240118501071a680071030703c0500c00d4040c00107568107140b041c0c0ca20b0500c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329946115 1250 329944865 329944877
    0x2103070b0f090a0c03020603280b040b0102150606030c07020d12030e03070317060f031002040f0504110a0e0112020c0a050c0909030406080702030f0c0321240301090605090d 76
    0xd1408442d21a08000002484e0034000c1e20304002514003032001d5038000038551000c42c20350201d1b81c408410254801c0c03800700c0c150b499850400a81c501880382c1d808103602800603003040d020076090249100c0f00180003a10451010002c1041d00d03032148155010554003030100ca01240743e50404210040b0389041103000a4206074001d66904e201005552410b5815203445000480c3c8160344400030034028035a0390404001c034034017800381e07038104500c43d43c0c0e924070f083c01640c850800d00100750b4180290016800382e0708012400c902180d041e4101c400729240340c0303014000c407201503004031000780301d82050080c2c160002c6414410007001007100c0d80f40c240300d80308440c0e10070380203402e00035104021151503c50760001d12040040d2402118503513409240c0c0d1059070301c3c051840700215003540090352001000d03480841d60111300c81e46c6501da0450416001d400031001d1825011030301c0c0113200701c0c101013000403030034243c4001758909400c0007070b4036a1f0158040c00365150006450750740d0301c1010400000104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329947365 1250 329946115 329946121
    0x318060902030d09064503050c0409111e090a0c03061a0a11030c071508070e090105061b1b1302040f05100c05011b030608031303022103070b0f 63
    0x20066070400100d8095490311480540e9286140800e18503140c048400361150300803540004c00301b0f01c2c1e44100035500c008030344150782c2141003240c0703030440b003149140c0160b10300798004001c80e2100a541c0310181e07048901107085000c805000300c03100a00c5d060b03107800803420024812918415049510070b4551b555007001450390300c400454180702e1103058000c8190040102568252003101000708400384402141c0c0380591406900d4a01003442c4d11480c9401d410030005010340764072144203900301a00345447d00ac2201040c2c001007059006200c1e00d8428080040e694803119091080000c2601c803c6044d28502100361906c0541481c5001105115400220f0301e030000035564420385042d241403904070380b201420700301231042c07400100718048140300000540500040c3c2c24041c0900c4013010140c01005481440c00107015900716412200302c60b0814448030300c41d0b540c0482524103e80e01110f080149504091a4100c41c80a5800002d0b81e4040010301d801030200042c40035005080b400170000d001d81d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329948615 1250 329947365 329947367
    0x20d300c0509010e010806090f09030403080712031a012705060c0106050406050d050c10110109030f181a030c09030601030309030b06100f110c100801030b0919060c0318060902030d 79
    0x2060441c0d0090303100e0342c0c41d4046064562740c07900d640e500c5095501180e2800e03460351940d000c540c0201c24111114850040002140ca506001d00c48024040c1c00102c50f00c2c4405400280c031a0f00121070641c06416001400500345e00345142d59001064007425040c1d5038a0390340030881c06001c45015681c0154144580060b00342404010026100d81040203031005030854401c0100c0c0c000ca407003c2ca82000144207000700c0180342841200c0e0294880d85526048210b8003801411920049107241c41d80020008100070b9010004804000c000100b4441c90b520740d9220342080803805824042c41d010301c10f1400110405810101c00c4043c0ea000380410f80c0303256107003400c0048404084101c0300001c0d001c5451a02003074003601c0074003400d42400050b01d92a100420114036a003a046c0d1058001440c0c85004006112140d08410380101001c409007000780c469500b2000c41d00c3c0c0300721000740b030280c6d54021500e0080c429400b9070014a40c11009285030606030402d10081c111040083c0d11038020200c82c10285 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329949865 1250 329948615 329948627
    0xf0603060801150518070905130e070506030907050d0213020f18031b040507030b040c0f080a0203090c060a0201060b27010c2003030c0706020a0c06020d300c0509010e01 74
    0xc0d40010001c007039040c4c260f0b172480c150701005030000e024003015100100d05540c070300c005c80c1c00f03500380b0714000210118403500c407070b1400816901047c040d500c20818408450300214205041c6d9900b0380e2606001c9450f4030100e403604207012540c401c0305101245c00140070204c07170014100001e040354000c210749a4002010b13207400000204289001e00310364021841d040c02e03000a50300c060300d81000074145102c0c0300460155012102c00e0000116109c00b075555050b044800c843d040b02c2e0484045065107084440c255840d442443e010f449114040b039140c2581e4400d400c054041c1c007a000c0e00301e8903107040c91a1083d06142c150441c2e81c80d03041507181052154031031440c408001d5040a100185404c01500c8204ca140b000c140e0342d501030200f0400368482076000c000c0e80c8020034460340100b454441d18140101030900c035421200864000c5003880d08502d500445d11301e8040134120b400c1e00c00718408a1f000ac0000c41c40749003804c5481c2804600d04800350094084c0070744070304c20389410029a1140004481d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329951115 1250 329949865 329949869
    0x1b05090c0a050307080601031805010506190f030b040f0c060206061002010e060f090703020901080709060b040806010501032a0206040201080106030b090a020c0f100509010b06160b09070f060306080115 88
    0x1403018000144c0340c030300c901701c20391708100107050006e942840741050f014440403c010039602030f0744070814801c940c10112004030b00c40c2803040f00003208030309000740030090030b44c603100c0608001c00410102d014040b0441802c87c500e903004400d00b81c6140e40b120042c3d00e5120850380c49200c0c00b03e18801e64541801030142e0310103401030902401c45a40c03031082d28164808050000c882c2032183c3ca2010005071140600c1324003800c0c0c40b100416040e85080c0f0344a080e52201d40200268076400d000030803600e40005038850545e030b02402c0c003107074481c1d4042e0003181d25401c078584a0210511134020000064010507114003460003030340c5040642c0e0722454141d050340c0d118442940c22090001c00104011400e901804001d4075410603a65542041e880c0c9500d0300441490754410140d032031040c004c0c44c000911810100c2c1710140c0301241044c0618000c008110103418004d44a0322483d00002c0b100442402034034042c041d08401c8528040e200c6000038001e00e5a030007007804542c1b9200c0c0a01e50910800c1c05041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329952365 1250 329951115 329951117
    0x110c070911031302090403110f150106030615080604140c211e06030f06090f0106081605042409090b010e0c040b0f0d0615081005130209010c1b05090c0a 67
    0x140c602e0b1207070301780710b02c0e064014019001c1101380700040302003210600441030302000300380041008100481c0700f8014100d040e0b0203802407626142040004e11050912500380c1512414a07a68966442e00800c2c058003102c1c484600c01007a007000c02803d403074104e0182014680a404801030200c0314500e0942522007a5442031504140811050300a011403a003140c1c03240014055030040c000b4a2146032800c40d041d0307041c1c0b8503034000c180d0312080b929003407044d10010003208006048078000e031004003880c0549409001e02035512098001d8407131110b080d00d16200b410b011140c44800d0b540304c8489009141000080302d8840048000140a184081c8550700400c441d03020350749441c2c91b01283c80e0301d5030702099140428100030300c0f800c11060030034800c1e40f0040040c00030740401e12640c894018041480241b040c3c0c00480044070600c425154a0b050304182181c0c3c0000696a540d040e0041c3d039806141c030402005007450400703000d502d01864194400329003080e5400d200a0b11a14200304141c059040341c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329953615 1250 329952365 329952391
    0x71e05061317091302040801050910020310230904030e1903170901091205070f0e090628090804090b06030c030604021803030d0501060e040911040b04110c07091103 72
    0x401515015008201c2118001c0c1403544036101340400c034050360419406484965941e10030807104280a000d046201082d1000451451504681055440c0510f0082c80f01c44040c26241a40c1518400fa81080c000d000030301079031044c030f02840c000b054900920803050207010404020a162074909240900392a8000141003282d007454005114031b8010450b020b04108000c900005c4010048192403407481c01940641000d41c1041400c112120715a842985202ca841041084006000c14842e40155000f07031254900e007222604007910720302c1442e14a01203441c1803030003010814050010030455901caa424002ca903099002c00055000403200070744d0400040000440501d40342c1e004008000c0e0340340030000d9010107440840e1a40d0052980c603010702d42d580b0010320034950081403100055000312000e102524582e5110600c030840108880e0040d42c41d07039015049540c407500144841440416903640314402d02c0000c943e241001d01c80c45441c18a00708568203842e25010443c0d1065001c54212 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329954865 1250 329953615 329953643
    0x10c0f0b04060212070302030402030c06030411010c061e0e070602010c0507170d0903120e0f070e0a061e140a0b0708090112020c0a050c030d2102071e050613 69
    0xd00c59518024011109a5400c01a503001000030350201c82c0540800c0d58010385130f02d058818103151460720429180304900500030040011103540c40d11000c3e290a19000c104014a0300d01a000307403003d1210300306603074003d6034921400300da140c1c48090a44109801c03101b2040d03540d02d003a800c0711790600e035a00018030108030303810205620000c0c85480e00400300c001854480403005010407074110303040440000310548204c0c1c0744038041d4000d42c00714800c0300020300350300069a80360540e0703107045124010708410b443c0c000604208840d80980014840c0100c1c000b0b01c031502c070309882c240105a0041d00c5150203d10b6182000c0c2c02d081c01120141c8694100700382c58858a61aa610709802c03140c42c40b8100020810700c110400e100340050003444015000a2980500514242e4140300d40401c03001e000780e11a110701c140450b80314180312902001c880e940e107031202a8104c800060310170098060100c2a030b08800541a40c140341607089158090030540708a03032103040c5c1c1c505a02c11104005010b0045554203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329956115 1250 329954865 329954873
    0x20d09020324010b040312200706030911090702030307030b010203070203010908030105090c0405030c0402070813062111030c0a1707021e0c0a0618050a0906030c080d05041e0509150a05010c0f 84
    0x214442607a40c07000f4080440c2313580b032103140c41c0070401d80000c1c0002e0b45650880c0704101c032001d03110841101c00c40d01600c49107441807009651b4000200303904105526070280300d42c581d00910880d441190040c0080c04984421f00380003146501c02e10031240074112a60014100312500000c1c0c8054900040282501c0341c0301c8420040a03400030340c000c0d80e21100801c000c840030820f0022000085c581510317007401011102000060040940030764800361814104180340e40387d0000103d940c42004800c03600d44540360381c40111102c1407040c0b0040f00c50003841c024041102c0e0001800030017664407095009070003104a100d19207a200002005410810b4040c041c080c1901542d00002255121040101c109544d1000034030640059400140c103240e440d0410310500080c003a9410241504000030440f101200c90001c15500c220300c00d13455a0202c00b00c03e0704113130b4080402c480c014400200042c10600384000000e039410002648140305001200000985501440301890301c0c070340124010143e4201522 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329957365 1250 329956115 329956127
    0x10e190f1502040b1222020d021306031a0a1a01020307141207031e031515030902090a050907140303040b161403040e0604020913020d09020324010b040312 68
    0x4914814075809201c040303060024040a8020030b60003030751401742400c041c1c050328801c1c1e1000303c410f8020034102580c0d00241e2501b0a40a01c0b81d5410b03510a0321101c0040c0041d401000d03160070081002d060f02e00703000800b20340c040100c0c1c001c000f003141c10020000e00c900b4441d1114034407602c3c0d0740980c1051100b0703000b10724069511200341c49143d05464140300c04400507841e5600c2224200c000c10f800650014012110010414007400c25040c00c000014164101402c260020710aa4009885030300c041604036200c4d0f0009044260b0207803102005040c410042c0003e08011210300e411441045000600c407860117903c040d4128004e006146841e05081d81c09115900c81c04008d04e0640b02ca40b0b41400046c07071680310301d543c0c03031408000e162207a007001c0600215220141220b80b2031030050009202940d01e4a044514179144140e0042c3c6d41c44408004070f014041c50395010350305005110320270201c0845444200d48030340c00160402d10980e2580c0c1c2030b00060155000251404214440c49601140164 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329958615 1250 329957365 329957393
    0x30a0f0c020a080f0307030908060919050c0303120a050609010303050307050a0903021002061801021e071b08010b0f01020a3305240d0b0606030604060314010e190f 72
    0x5402d4150141e1038054840c9000c616140f20305017507100140d2241859840490360001d8040407002d07041508012001c159030f00c1c400404414001d210385406410000204003202c8841c40180940e41c480d116401d506040e8001182c0d02030706142048005415403a0403d08c8078142c0e949600c0b205d0440d22685000c83e0507400101b4440705110341503e0200140c0c2d907810f03140c46010450750042070302d4500030903c110b9801c514011075041d60b0051200008a64140b44109107501c182c09250751542c41768142404100a214580c500707040400310f010555030010340143d48900380075942421400e100c4001260759102d0700c080504045c0c4d00d4032060110703000300904255814502038402d50b00c1c80c01c01801408036070098600c51203100304d8900f03400604005e00c9200f500740108440945046a054441d00000d010040c0750b58801c00c00040001c02030741d55640850040d40e008035141030b00d0301c00c90540c1402003295401c691101c4c0b0400300a045c0928074901c22184080e03014000c50f20240e00e41d504d12016800d13030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329959865 1250 329958615 329958619
    0x80306031207060902190602030a260901291c0c05060c01090203060c030c07060506030f0a050a0501060f15030c170a0504020a050102030a170606040801060e040b0603030a0f0c02 78
    0x39400303a0850501060203440641c3c002d070000956040180304000200c18000e03c2c640d80443c0d034141c100130180e001300a0703581d005000d00b010310040040642900d21040407826a250b2008110309200445a0548c4405a84203c98002d217518000e82122080448801560b01e5403002220005180001182c040c81c100c2e14400e9440911711911100040d955401c107224100c2c882c1e546a5201056160400517641c0080c01070708083d1440c141842582d04900c81d10340058569034840000c1076060f2820095036103448242c0c000e90700d05a01c03070700e00f00392200425030b000d49541d03003071a1002c41c0703942c40301c21540d04994110500d0210400c0c0203806078043c02c080fa08da6414064441d0005c4c004d503100d10085ea00c0340c40f40302400038103494075204000b0800000d811440c1194410300900100315001078802e0b4198000320708980c490383e21000003400c40d00c25508004029400c0c03901c0014000c0800003441e014600c650414403681d0f50308010f05980e030084541c03503000900098842412207000ea40a44001800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329961115 1250 329959865 329959873
    0xb07020411130303080f1b07030810081009061104050a0e040303060302040213180506010807110a05030703020607080a020a02100c11010c050c0c06030108070b0c030d060b04062a08030603 82
    0x5203044840c140b0303459401500400c2c1d03d17504100504600701e005a90101d1380e144444064071412402400b43d004051004041c841104042002c0440c3d110145005109075401c8820216034204440c000c0c3c000396004803040c80c1049544190031240c442681c05550002e046c01000510305649290004405842501410798885021016840b43d0005185c2801100e00348156031345001c5100710310301420102440304911b40001d1007075907a404401c05400040d01e1400d05130740140005338078146082020010140d100001740a810943c0129400c1d20a4201c0d0326a0748880c0e888005040c00d030300c507400700310005030000398070001c1882290740041562821445c00322100c1c140710060508450304210940f000c070303001007000300d0a000b040005607489481901c1250455140030f040c42c1c0d0300c00840c0075000e000c00c00031400704840a401c00907150b8420001c2014044250340e0500c508060380b050294000084100c0c1240048903d4070020300e050421401c0f517540e060469403101c40268001400231070385806 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329962365 1250 329961115 329961127
    0xc1b021c151a09070f09090c0306051f022e021b030d06091a0d060c020a120804050c0901060519050d0603030302220302101218030c03180b07020411 65
    0x74a9104039844100032100031039440c600c001c10000e400380010510020806001c0154540d15404500c4e982140c2c800100800e00c20940358081d8003401150300403540041600d0441310005101065115140c80309400f943d04069580c0060101b803061f03442c4101140044141490750751040d5030052011001200300003506443c28806542541d01c144064911951144820700080e2220b200d10003074801c070040340034605d51044001c079519002d002c81c05400a0340e1520710340100c0d4002d0000c0003007194400e0502071a150f891501501d0300308140d5050b40c0318400c060350301b0101d091090155041c0c0b84c0688405040414802403d2010b100c1240900b080007030500c80c0e290640480d0080070f01941c031030b840250300c40600e40c441c45040b003601f41e0240e00807031000b0b00400158403080e409e04210041880c00c0c90040b080f070a0b01078003a10010180d401c04c03051b5541c5601c01d16500100d4032801c2c2d0300c00d545a6118a0311844403030200c0c1400c1c003034081148010031010006103850380c080b01d002d200004289081030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329963615 1250 329962365 329962403
    0x9050f04020306360118050c090112180b10090c0206040c03020d0203120309030a020c0406030201170a020412030c02010e01020c090c0d060e01060507050709230411030604060c1b021c 80
    0x4c10aa01911544161495070741d084410742c0551a0700c042e151500508216640e80001e050060703e40c0d20040c81039a500004c41528500b140c50035240760071261301e84040c2801285601d5051240c410110111b1400d6001c1e041c0c14070102d1080c2c00383e0740081c0314800f9603045400300200c0c0d001c0f40c1022a498401c0c40000c46801c5a40c2d800755101d081142d003d10380707a2000c4a4040d041c04400816203120b18074011080c00145e0b00b144000e9041c11030000340324086e55581341d2540082c801c0b034109200ba83d60001c0402c007003607481107021518038400e07030b03803e0040900c1c403006981d200d108000050307006803100300180141402601501d0704024645010442d10f80d9691482c0d9003090a070441c5002610000340041449400c01c0070000400c1d946500308142006081c2c24416035070000e24050810441c1c801041c2403041118038003803141d20041c151132036401c281c40d000c402031040c0c1d5580c0000c40d10083c003c0f40440849044030b4500c503005842200c4075500201000e13003000701604100d9554514451400b140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329964865 1250 329963615 329963719
    0x30c09040c05040f170d030203060a03050a0f1a09070522090b0f010f0f12150c122909090f1b04360305091009050f04020306 55
    0x81d9a241c6555460400e131003003a070141030750881412006010540d000884c80010520556680b5242c0181c494030b40b070b40004c040c800d169101034802d00c584240b0a00307010000c585003c16510840c2c1c10f52000024900134030506000300c440452640010b40108001d04083ca0001d03440c01e60041904500100a91500100c5103102c40981e00d035030400007081420070082d00c849014040c000600704c809850103c0c03080001202e80503450f8180380000940c0e08221218a04003003280064005000d10006100000c2c112200018107480a2b0306210000003c00c8028812103600800442e2817450f009100050005000c07004c0d041d01a6803244411b03c14058100b80640c011668010707544100325990f41040009648070140391040c98041140c000701408104400340c40c104d85007040e50000001c2c64113081d252801000385440d00f001010f82e907041c40381d500100002c2641c0080b0380480c0840d0400e0706000032800219a03085e080245030044907001c4424040803000200441419240984500b03100104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329966115 1250 329964865 329964881
    0x10311160c0b0c07080607020f0a1e0602190801060f0c0b1e13060b03070e010608060d15023106050d02091809010507021b0d231509070501050d02030c0904 68
    0x5504a5101031101e1202400b11b560000f61901c0102020007980b04202d0b110103158500a005030721700740555010540740403d81c04080d070000d4045450b00f5014450550040c030f10002100010060000802e0702030103500704290481c2e499840c0100042c659403586040100075002c0c0c450681d50700c6c4010207002c440d907072a6104842040c00402d81f0038491070004155070803001080e100340c02c4040e080c0704120349140322604403541443e1030791290700c0e0b4601180b200f07040100041d201c002e02801e101c1d10008990002d0154501160311000035152880c55000ca00c407941c0020312000c800c1c040100032151080d07004c0c2c5500b11000c800146021604000a00c80c4690400781483c051409230400c40800828031445034440c0150000d0408125005078014820144000580c070511a016481d0700b0704c40d0841c4514000204410b000142c00740c03a01c00e159030785001080c0369001c0404003001510802010449404444068403501c1c18804e1540c00f9001941000f0030b0301442c0d441c14401c01406035240d00070141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329967365 1250 329966115 329966137
    0x150503070b040815090303240d0c060f1707030203040212060a050709140a09020a02030c060c07050d020d080a0f0b0d030c1727030c030d09060e010311160c0b 69
    0x1940303503d030803074080c200101e41e80004d80c8840d035901040a10140442265800344c03440890030200002c40290280c032071012540d84e074006411011860030025920140800c0e07402507219149440c4031100110380720303000f4030b0a030301c4c0740c01640c4082204507000b0780185400900c006d080c403003010043c0c055107160845c01c070740c0c14008945030020310802c00d80040705e1a018002c0d01005200c114820804240d07030429510235012541c0e030000341c0408040c424420744074494506000d580b1941400783c171009098101a0050703941d800b8012119407200e0000501d4200314100e91501000c030f80e144080c050003059428039405207070f626010340c0c1d815a51001039034900a4442c1d22807a81344000ca00f03204102c2c40100d401204d280304208466070600481c4429a51081400f0a1f0b680044411102007420f01c9584c0b0f02041d014071803103021282d03142e0042205010b50b082542d800501c610500011410742d00e080090090b4400204150081c1c010700c18214240c0c5409110f54910b45039890010788107a03030103180b56403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329968615 1250 329967365 329967367
    0x509101d0f0a020a05030402010c06020f0c0a0b09030405031c030213080318010305061503040c0503010507353d0f090b1c06060510050c010c080910150503070b 70
    0x840588010750301c4a40050780c454085080c01d405240c050211701c0040c1000e0705001d007100ca01010030a4070b8045520f02c4002d00e07812a20f440890400680d20001240203e5050100c00006400040000160b40460744024014042c500180d0102040f44d030304080c1141c00c260b020030400c4030f00400824941c0051200900556642c0804900312010420318404181010b084ca001d0018680d2040c1c840240029400b140540e07075221032400841c40c840c540d011540650a190400c031505800400248a06100d260014000d04402002d908600c00500090b0030308410140803407540e08907110441c0020600100e002d01d0030007403400304020a8420300031001492031408042c45a40e0580541500400682c1c009100381c038100e200103107810f600034955808504540c845d4a06000c880d400c1070300207003006410388001c1459410001d0507030307102c400850f001d03600384504920742d1489022014440c8801d20301400a200c00c41d0028000303000d80d02540c02480040d41004605070f0f509016a00c004c05240c4922 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329969865 1250 329968615 329968621
    0x3070c061e02070e0705180904030819020c060f040302030c0124080102040812250303051b07050607120b1801030b010e2806030f1412130509101d 64
    0x90711603801c85001e8078115080b500f400c028070b44c41c601c040c9802c065542803a580340c1c01503881c0d40440f5860007007083d5204551109020034140c200b000c3d14080d0b17000480c0c008030b290901107403505a218140c3e100b5200c0d406a8002001a200c50324140d400c14031030300c1aa854500d1400003a406d461703288000c6548540c040b19880b800a00d00c121400040003108001d46c04d0601d02502162a1810913110085041f80018485100106101c14101d00c04200030003031480002c41c01d005006090803911101c3c107400410004c035100c00710000b40d4881c1035025006295655909108079080d856203101c008034180c80d4814a04140d980d9090f2000600c4010301c107801661450401d418002410b07407165000c1d0f148881407001c010b00e0040f516101c014954800420740b1440e0000b80c0082001d47c0c0082e110141c4e0710051010881c1140801c00c031340110340b0403100d2550420000840621034030f01c0d4400c0c4d400c1400c2040255041c07074200503a01c5000f0304c5820440c40c1c2d80ba00c40354450380300707114600e060748840d10070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329971115 1250 329969865 329969897
    0x140f0306090f060a090506010510051e030411010905090a091103010218031603020310020304240b10141602040902030f0d0801080d051b0a020310090501050f10060c030203070c06 78
    0x1c1d80c0c2e03000501c4041817040816648405484a03410301842d400380110242d41c40c1007034001e4007184c55400c43d0300d01c003400c404408500c520140d041602c1c101d0741080f5107071402040d907115015010607100020416400c03034860120210041c416400202c448040f02340c88020995021320180000560603043e00c100d148520082508140c2402d60b035191484403a80f050025880006201e007102c0741b42000107a403a02d580c10122181c00a5003c000b83d0700c07220345817180745d85900740c0280c135001c0c000751a041615540c03518141c89115524174521048a0240210112071040041100f4181d002410009580b0f000360042400d1106000d981551680038950384000300d40c0c8514030b103004140c800d000c1c0000108940c0c004190340f00e182440d14480d42c140d50902906e91080c0144d03005298001d0884125109001680000c0d29450905840651800000801d0305281441043c4100030b4511001e440c00e007080c0060381d81c01441c4105a08510090098000146040c02c0402c080c10040d15600314031050104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329972365 1250 329971115 329971123
    0x20a0e090a05040f0b040305041e1707080c060f0d060902040510030605030318211f1104032603090a0c05010309020a090b0111060406050901060618140f0306090f 71
    0x40d001c40ca24010802000c00c50b01d84860201640c400320f0540075403183c0c05e04403028004c03900015030080300c4030b44584150300110311030812907000e108a00c09101c00e00c80c01a03181d11042c4990340e15078000051a8005243c403800030b000d0030384000070305810400300c00301480803148190441c4844a9000400313000c01d1511403501300c5050510f00d0284021400d0201207510b84c0940c12081c0c1c1d4441e0784101d0340c2220354a09840100c54020b8803003c900c1e40d02035031146d560315001418080c0d0111070700440380310000d806010f03500107881041c541790300d818515982d022f0a0520202600100d168240c581003c215041c401107024114160040c900c50b5114189403801c140c2980c4a541414070300820000140c0707a03801004229144600d000810f88603520044c1c40140715941250518000c43c2d007000108841940954000e03240038000300302d6903171a00003c0d900d0038041c61000050017501e1031308210503003940340d4048a00c400a00100300880c68103010a2070601c05444540d001c0e003190100c0950b00350204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329973615 1250 329972365 329972371
    0x2e180903020c150f030a090b070e040606020c030a151b0306030b130308150402090d08030f0c0c1225060903030b0105090f0609040b0306100303090b1305090a060306020a0e09 76
    0x1582980c0082141c4003c0748a4130a40080d00002c90f80440021191072299002030100b58200050402620304001d000b400441e003601014403035890084042a014400540e024546070b000d0300402a1203030b80d440301e030280c00758540c1c03a5558540310281002c026101c4030740c3c0c64408006843c007143e034030704603c0c25201d4240002c20204000d0341010307801002c87c0e0f001131740c03e8010134a40007003480a8120000b003006841403481c0ca42d001814200172008000c1240000c40c890700f81d400c01161030b40c0f94400c3c5a40b00384183c2003003640560200380c031408aa08150020019080b900c1c0c20507054400c0c1d100b012902d0040d100081e0388090351940d4090600d038043c0180e8580c0302d001d2901e140b8181c11880012108070039105864003865020038000d45070380740d03948036812900700181140c10701c0c60002d05e40e400d403e805003c21000101d403140c0c009041c040f908c043e58520420024482e2045013007606200d015040144844082078440400001240ba82d20051140450968400c0c4c0340d07009080511070180c2000e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329974865 1250 329973615 329973619
    0x1e0603020306090c07060e0d11070b0406050f031312030c02010c09180e160e07110f0606010f022e06060e0a0504110c160e0603062e180903020c 63
    0x10020400b59949490038542d0005028001d00d88400c91401d161004000041440d1454400e030601d0700d0300c9540040788007101c2070700f000c203c031807598945000608a005612800e800f0070f009110081b000c2c049c010145600554168091178010215122003921038403400d045404241d0364030500e004940d080c0514250010181044903103e483c141e010340e01038490500d00700c0c2003992040c8100d4440001d00c0b6841084a410300d00c00c50558480d44404001402615280b001c1010301c040350003c20350100d01802440200c501a02059442d10700644000c80d04203a020110302844d0b01c1541d150700100d0a0700300804032000000809205070049004580e410f80042c0e0034004d1244400883e523890700d84001c10368100752404603d1802aa034802007a006103600c14140340100051a5404011500f150003103403040c45503a080380d1501801d15454540c260f610030045840500081c104440454240e184501000c9613149005d80d940416203104a18004070a611038450100034141a41000400165407007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329976115 1250 329974865 329974867
    0x3130c060e0901150e040f0e100c08060907050f130e040c0303020c0a0302060715020f0a03021e120a05071e0305040c170d031509050103050a211b0206070204061e060302 74
    0x88008050002e00765144441c2c41b917501d0f01006185054903801c4166000e62650448038240728540c6a080900000e05402d0000703071802000034814649498020700540c0b0580744c1e503141a18280a9403000e81c409032804d00344203aa824001201a036003001d051149000e0700e5585119400c603c9c00074103081d20105501c0c418000e6060610140c5e440400301c1c0d10550780180880d200624132103801e0080e0007101c613076032050403010680d01311443d00b5030000c2120003d00c5250140c0010351042106940c0a031aa400d00024203100005000080507031145801038258100b445d0240500e0400c105296036620200c000207031283d00f030204201c3e00c055410301034078920610f4050030309000103007aa51403401d038000c0101525481c10031075007010303042404080c003c80035007030040c0d40c0c4034100a030752aa801041110b45c0b0301c1c07441c8580c00841d200c1303a02020780300c1d2035039a440d4541c80c81d08030707800d550b500d90070b081c0d902403020801600160380354481d51b002019005501c0b101c030941001140c40d18401544000d09140c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329977365 1250 329976115 329976149
    0x1080303070e041a03031b1005011203110109170408011b17100b04141e06030112030905030a0c03230705010c140f0f010b01020c030601050603130c060e0901 69
    0x6003000b682140e10200b540c00168505203921050b0b0007003481003965400d030100143c038000c4403018000140c00c241100e02100d50f041c10680120080390024407800000401d001000d1001900c101c255420401401d4000329002c00d1a03200d108a400c0b04c045000c0c0000c000103010403d016013030080006078045003991210443c2030000103481c4081d0300007290242c46050000034901c0c12442a204003a1101c503914648483d1030358202142d10402d49840f510448044178440000b0b0102100c4003803800e00500380f00d06591a0065694603540190300450601c07041c1140803600307132800c01440d00494002e0306070031401840c505000c0f030100c0d000481030008100b00c6030302c040d0750303500001d0f4142158000e2070180b03900441c07421f051008170141080c4901b98061412096503a00c0c002806410302030101c4000c000803240c440069a82d0b68242682c5a0540c000d4001001946440701c05958800325600c2c1c0a0150382c411366a42950001036007203000803412100324480c0d207082038810385014041c2c030301e8511b501d62 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329978615 1250 329977365 329977367
    0x40c02071508150d020a0b030717010b2803090f08030709050612040209070c08031006140c0c0d110901080304060e040c0507021201060f0311130c05040b0c0c06210108030307 76
    0x742c0e40d207060300134010b40b0034900864441c601304800070254170941540303e040201000f040380c82c0340300007021440002c60011419298000c1100c00e680403c203001e03c04d45d1301090805280c4000d290300c910515a866500f0400708604080409200344590151666481c0a01c4090000301250304102d000b00703018071420050442c10509150010f804540014143e51002e030101c07082e04c5108001420880080244807030842c40c1103140302aa0865160807a00540c407400c0c849246c0524005c0722074540c407901b0b4509150400c4810012814055a038910030000d003000861085002079104504035070000ad420401294045024000320030112002d1084188038400103025010b8403002a00c1041c0c84485040603410952010008068040b100d20a017a83d0382801400645103140300c0b8011000034040c16100030782d0b4400c00031541c01540351541018104000300801e500f21408880f010710074680143d2259540c0805080f454007a4006010719401c09038500344010010f034003081c003c0e030088c02803050003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329979865 1250 329978615 329978641
    0x10c020313060e06091f030e0105070f030e030405060705060f070c08070803130c0f0e0a020c070303080a090c090c0f0306060203030a0e16030302010b1833040c02071508 74
    0x110340c43d1600c1040c0d5403100c3c0019090f03114140b10349901200d4109480b010f0314102c0584010040291410020464244040c038207a501c00c03940e10340025500750110401c540294824204030000004803400c0c2915031020a4480c0e00143c006d0714203512050410048460402c034480d03110031a45454010008240d88418841c003852400034400000400020302541007040001030f00c81e0000c5140c1d20495464102041c5a0028003078203105035022400550303da2424021a072208062030020b003090f625645013203a072110064042ca02c0142c503448040d000c600000d48244c09000320080000e0343c1d0448010103058640581410303006d0606101080040540110541e0341c0440d207600007041c440a6241d1041c10101c2d8003992600010300e803070020041c10741c15400180603036000d49140b0303102c550036440320b0340c0c1070400c07500266501c80c0100b40b030003110300866406c22a10900d96080c641491881c0005050307a0718140c11030011392000c0e500f0000b203c00130071403444001c0c0e6406c02c0c191500380a40c5070120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329981115 1250 329979865 329979869
    0x50f1b07020d110112110c07060c05060a0c1e020d0905120c0108090c0d05012f0d09082a07090c02060a090201020c2106070801050d060903030e0d11010c020313 70
    0x42c0b04140c8030703008044e400350070b100700541c0442e44100145860714034100950380001c4845804da104030100821460300500c02144013540000041c00300703658078000ca1002d00140c588501c00c21104140811301c000d0031552214040c0416005411182302400c03004082e880194007041c0300c0d118070342c0380c1d440050020030001080030f020b01c2c0c9035981e999200011407916040503581a004840303030104609000c010b60015000a042c0020440f25010a2504003900740d018100c1103c9020b08100c406541c80c2039500c01c01d050341c81000e119003005800404030300078822154070810883c0c01000c6c5400c1e040028060107001c1e0128140801c10444805402980c50030002c20b071000b41690303108a0f100356030003044440103500c0003e1001d650407204100d803e5488000140c0c07650079210384030228083e01c5c0141801c40c180c4201602c111044102d584641d00900380b88442039041c10b94840080b0214101800042c5030004a40c40e2103401072880203426003150031031403404046404c14400036448800c02003400341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329982365 1250 329981115 329981123
    0x813030e091f0f0f050607020901090203070e0d03080a0e0f0c0d0c0905090307050715080a0b240a02100903020c09251e03090213020d020706050f1b07020d 68
    0x90590b9503607014401c2c1c0c0040807115024403601c50000540c040a80d030054107450000070f800489a175258180202030150000c02980480e9040060149001a03409190302241e01c1c030b1700491040711100401c415101c0c0c1d103800d8000a80c0030080001c1d800d21805811940c200c048010a61028680055600c507114411071130f20640ea009111014807102d56032803c0a8403200f43c0410070350400308407547e034aa2050000300c80c54010b21000060300384504e07981100310310281d16403000b6942c0320101140104014032030039510103100340b4180000200d440c0c00f480c075108803010b0307550360380c06603200039190141c2000ca00500f6030034003c04200003070740840c0c06800880152a04103483d114072024122030b001603410440307814110009041485ea0117100410344640e0800e00302e8503050440001c606440c0b50703c00107034101c3c440c40700c0c00c1260b0050781c2c0106543c20030851b00504018082c1c8c3c0c2d001c151303002a141c404c0ca50804c1c405010541554010140c1d031542c58518180c50409194040741d034040342c4c01c9003e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329983615 1250 329982365 329982379
    0x17070c0e07181a0a18120314210403050d050c03060a080115030b070507050a0c03140d080106180503060c03060f06030411093d060c0c05060d020f18010813030e 70
    0x302040c1c0103080d20600c00c401886031880f56521a02d691b411022203c40544c0020715801303440c4d0305100075204660404c040e28014075440d081d10707503100d1000000038008804000080000e80b1440580b445a2400344d0072034542d5607542c2c14020104415003500f90004082d40c0d2402100702c01e5840403001c1003080382d9008946d803903e076803104002e6440d800740941c054001e00a140c0341c50200040b11124005903403160084600c0d03034030540c504643d01c034007a56400020402540040c081da500a602c40403078000c0c0c00c141c40d90039513282c9001c603007401710603605170000c000088203200035403130074820404094206880079400c0d860a52070704100d050000c43c0050080b281800421003690001b010603020700604c2ca40304d110124001e24030070503034401012071045800040d2011864511444039021642d4000f114005014181005c10403242e000280b00b0702029030030400348020a000c040501520000e542e1003548030301d4242d0000d4490f0100410321801e01c446400c0450000c0c0c0c01080600b5040005e513280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329984865 1250 329983615 329983627
    0x6011d0d030509150a030f02090904020d15020a020304090615020307030c02150705060f060f0f090925060906030605130902030f03030a0b0a0506090108010317070c0e07181a 76
    0x5071424410380d14680d404c440340b4940b446031030780b02c1c40c0181518020741d54104881d0504180702c07400c074004c10350340702e52252400012a0251030a08140208a070180124000c00503041034201c00700e80c422031443c401b40c0c2001c603040101e5481407040300300070100311034100c1d0030b54504a0000d44078400c540008007840741d0a1000b40c1035440d54003181c2c14400700b07a034810343c2d16281410043d0b0703507040444502040e0701203140090f083e410298007004e80340300040d0001c0b40602070b040c01c014207500024291051885440407030412850051020018600040482c808040c00c10900a00c0450703143c11200c21b02d41002010411500c4940200885a80b10341e0000303400683c47c40002c3c241004c0011100140c4404070034002140c6041d800840d051204a68181c512030740c2d2810b02040d40518a5100d000c0b0340d4600c01040420401c03c102c41c0118902d5a4062078440c05980703c01108505800a00c000c40d05201000842a0000d480c061a8602c10f20351520440c0b03448550426800125103c0d0003406021a207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329986115 1250 329984865 329984867
    0x190816020304181104060503010323060126010c050304020315070c1502131e1a0307080417070609120c0c0b21010305100b06070b010504050403090902070506010e06011d0d03 76
    0x210449481d0513084a44e125a101e00c0140160003c0c041540c0c1d0f8410140f284040a1000050803004016800a8800340e0300e0b003034503c9032014088031900561117414080c0703407881c88207120b076000c24952030310f032252a41810700600d454041403c0c2450390980c0d5510610080c95000034542c2c1080780c0c040c2072188101c9442c03200902a0261280e031003880c80038580d0104103584400c0c110b2108100c0c40c0003041c0a1680c41849954803c0c0510b07404028403010000701d0011841020719560103406288400d0140e0b19061003070040d50311601e02510101c2d6512500f40030007000540255508901e0b00e0320606408041e242d64501c0300035031154100c07040b0700152112142540b4124155031400b0b04000e1031a96030340303080464443c068441407101542c40e2508014442c80c1280c15220440d421044040b0968280070522000300741c080d00076000d0012035500000d620f10b140c0018076070b083c401d42c040d00c11545040d21005d00744401404242c10310156030142d006500e041c08452051a008603941c411a21043c18 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329987365 1250 329986115 329986121
    0x11120705090711010c0e100c0f0f020a0b030a0203040318080c01080702100c0c110301110301180209060d0c020f030a02030f0924120a14060f030c0619081602030418 72
    0x2800c3e440380d420510803074103441d0415044100d102c4247d41802030350710009000c564098140c44014480d0424060303034004110300707008d4040f641d44040d000c9c940250700c2d9410711049802c21100c200000344c0000401c01015030140034243c50002d00300078003d8950909000355140d241d5a00054104408100010703c0c3c00e108010950034290f10303100400a05114032401041da00398140300fa1209103d400c01c03460382e42030510540d90000000c0030b0031811130342000000e030000c0b0400104148219028803900070681ea0342e130300900c00d0b0116500c0c001142056540040d0501c4c2c00720341c1c060300540050000f840d055801001710b6910800384445c859445890b4030014280d4542c0001e22524121000e0b41d00d40c1c1681d070003004100000d4401c45c068041d170340d035012000541d90b9501859403418186400704805090605a100c1c1c1c00340014140c1ea455034444000c5030464100c0e103040651070114030902901c107900001d142e6080203001101c1709031103148040c0a0340d01e02c902d1141400d403240c1c80000c184865a0382e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329988615 1250 329987365 329987387
    0x10e0612071a070201090b03060108040f060e01060f0302040c08071e09030c2606090a030c02061e0409061403060114130501180506041407031a091003111207050907 72
    0xc10402c940b00400d582034440d50b0000207040380402d00358040030802058210a030791064505950784040c955451351858140100c0300c00c1150459150720044407046030070300803940900a00320902d003045246004010950b016010341500b40075980d01407003405d0790320500003a000c403940c0c8a003031101240f100040721504042d038406403444070044400700740a8030030f42c0d14103c0030780aa4440c03500b01500c011100e07250380041da0b0b0b4004c5507005009440010f0301415104c060a80000c10031030034001408124032405041c1c00c80c050348640005000d0200d685a40300303460191031801009215440640d001c0390752084c06010b1041c400010440c451403c0d41c428000510010002100b13100d50350390303501410b41101102c0e01d014403140c2004001440c41c04e2510a28825040e0100122440d8680003000d03401003100140c898200b24030450b0704042519005089405034162074079444000f0300c1c40c141461210904070105100e20300c54280703000440300000d50b8000faa00110745600d516110800184e5050a420f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329989865 1250 329988615 329988629
    0x3030e060405040609020307082401121d0106050901120b1504020c0d020a1707030c0b180a030215070903080301030305090102010b0d0308040b0c0309071a0c06010305100e0105010e061207 82
    0x70b0000b00d01718455030003031400b03000c10342c46490040d01da10b125400840740d00c040107070b5000c114001c01030780d542c40380b071780350400d1003450000240f0341c00c81c1620100342c4043c40d00e41026580d15000104040d0034074050203401401c0080e491400d0251964450702110005015880301010f980c001800d0b60b903850341100d44880b84007007165410154020003a4a8200b00d05007641e62420405805041102e40c400b15518590305913500d000b550415500c1c03901d02a000b4000d81d0a288424054800c02501000f8100b20940070303400038003104040c1150120382c40001024001000003c0c04104002442c2c10103032810350782e050800319102c03000c0c00300403801401c1d52158698404185084402031641100443d80038502480301400719079100c08044d40c1500c802c1d580c10680783d222010401c04c1d40c10341600c40100b03d40146044d07180103098812503107013030320a80050300d05800680d510040075803984036081c903080300301000303120940c502200b10303403040700050459010314020b0403900b038441d40038010000038140c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329991115 1250 329989865 329989871
    0x503030d110c061f080111090d060902151b0a1a09010f05010e0708240f060705010504121814040507051c0501050111010504050a1707170901030c050c0703030e06040504 74
    0x3d03800703d40c0300441c10001e9078030181360394101085681c010300400c034100307032141c0c000c91030407039507800707100c90103020010a46902d640c50b0076400041e81c903d880d25614011984100f9100c42c82c2c3c41001040e034421205240a030360140d80c4400002e120070001d400d00c81c410084a079995550150303554050061038000e40e22031032500b030009c034a8186109a00d40260b20503541d6203241d964080808034400c11080e142d0300d19070051810883c59142c00450000312140c0948134a003410503030342e0740c1420354906070b404641c80144003a0401e1055480300070030466200c02810103003401c0c42e061811003041e482d140030f2409180c540c000145400d0141048030014004941041c01105860302104000c0800303010305400600344120607181c81205014240c0166089000b410309042071f99200340e1100c00075030303030851510014448440412040d04d442c8101104400400c0e94864880c0001011210040e0200701400340501408034080d0740001d050050760350504100300402d400c0c00c00111603020300e034412540130b81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329992365 1250 329991115 329991121
    0x1636080109030507031412180102040801092108010e0a0f060b07121202131205120a08010305070f0806070f02010204080307051005010e06030a0807020f1c020a080105010503030d110c06 81
    0x360043c0200342c12806a03039908043e0615003241e01c02d500c5580c00c036003442240d180200c2e921500c0046204010921a00018a07103540c5030207031800e4a840300c2050fa0326001c101403032040882415a01803842c111850000490340c10022035581041b00a89044089699801c6500c081d0b10a0362000c1d01070b01d6982c0302e96444a1445c5003c207002005440303807a00243c00b070540e1504910007402a030305c804d08001a1520040d00380303e4020500e46c803d8006807500e201e42c1098040c00344c100d0b8001c2004211558510110b9815400c0075880d203e0b0756440010310b110984000c01c60100041741c036079003002c214906034010508210040740a030085400c440c060f80000503208040001c00030b4090005080903800703110507a41d0328807884850f06d0480e001d50f019004803184e00d0000d03161742c00621505100401d46031054640102181075402665140050040d0849c500000d501c1c00f440718900030000301009104640c100320200e912401402c60a060aa032201108651311940c0c500346e410300c0b000b4030308444080ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329993615 1250 329992365 329992367
    0xc0d05010504050c09070e0609040605041e0605100e22061710060803071209150512130215090607080c0607120b01090509041e050105163608010903 65
    0x101003500c0c03c46103441580c418201c1400c1c0481d515204440c0d139200c001445803d403007800140e620030810281c0c040d42c1c444010031656641c0c8611003403044000300e402c2c5190314a4083c0c804030382503500002c1c070079260114160b004030741c0615036904140040e55502000301c0384a000c40282c00c1d941e0f541c4813905050234004100103461100d040300001d0940c044030b14110130044500b0403a144ca00030030089820811203400441c00d549084072090b0b81c50300d04940d030f050f07031001004803d141e02508040045e40c000780c002801821141c1440d04a8500586002a45d2640d4001005860b5407030303084050b14000301d100101070741c0d4801a5407100c1e800c00002640d03500811b10680e10741100311094030104880e890a40d44d185190f110300003a80310182c40f0607803024244410081000401003040740d01400f0b070741a24035110030485804070701c54440c1d400401c3c181401d2a5904000304880300d00020006038110b8038044200441c0d60b10039100250245440540000c10442881042d07500b111490b0360800740ca4500705 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329994865 1250 329993615 329993621
    0x504030201020903010b06190e030f0d0c020a1707030b0a0209061605060714040e28050a110a0c230a03020703020405010e010e07030b030f15090c0102010509030304030e030c0d0501 79
    0x900228000c0042040206c01c00c2000d00a01e038442c641006200d0080c4006409568102c8400f40f005044641d02d0300040d003107030318012610b1882c80000750030002900c00c5050240f03244000c0e00744901c400512505928101e40e948010784005400c500e9698003103030800000f176040f00e0103028060315031641d81c512032060f905014081e66040700d05200701c00002d400c1078454801350200540196031f1601d040d20706000b0756207002d0003400c4034400488900e2030420f0454a0068224515105c4601080901d0038410210460300500c014012422080120b030136034039440b90b00c0c01101944914142080b0906100d9101c0c400c45203040c0c0c9400e4899070851009040d000102c1d01c007140e00c00c54081c04140c0e2204100d0407044400e1044250302003a10f000303d50014040e4108003440c81029049407214081e064040d85400c001482072400c10031345070f09001d0791034070911441c21902000e000a0105007800306000360350b80b000a00160030000f5105000c000e5580034441201d0304100102030300c450ba01c581c20702d2070007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329996115 1250 329994865 329994877
    0xf02090306070e01090905060a0506030a0c122007080403020303070533041101030f021603140c0607050d0b03030a050c16051309060605130b150f0301050d15050403020102 75
    0x4a44a604001151140f244650303a0b000b42d0103948908040740741c030219030040e15020342426072040c01548041001d485440145200308000d00001c00c40c804011405031540304100d81c003070703038041c20961106a020b9002c803081c1e80320110801441ea40f0740071030504035030768083c80e08000d505000014503078003400000140b032801e41001c40c0381d0b1440810411680d04d000c1c1e07114000d44c4602040ca100040c04070744000803103030b82c228060401003111005144124101d030310100320640d41c010140041c8041c1540100001c45001010b40c546183c4003e081d10580c3d1188010000c0c41002400180c2c6048199250070400ca8900b02504813900e40900001c041d01c01c1d000a180390809220b495003c8851000c0034025000711b91018124070785000000401001520b03100c00c1c00c0d15016121440003445440e00103450354080781c0c003980050180c2c4240100b20703a0408081480b1a5844180703e6840300303044400c12203046a02c11507030340711110002d20b4120300070752210044401a0340f4000170801810f80640007044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329997365 1250 329996115 329996119
    0x102180901090203010311040c0e030105090f1005040506060415030c0b07031d13020307020102160506160f0909090c18050103290a0f06030b040812010b04060c0b07120f0209 76
    0x10242c0e299040722049000911002e0304043c1490a0317200305081c47ea1004802066a180c01109601e0100110b4252003040c0d0b5643c03215840011000130000052010354000000c20b181800103046c039466143c0c0e43e240240c42a072046a0b11441c0c1250304524100b074400859000bc2161981a590300381c1c24087e400c0200190081107008120001c0700038a0705011480d080024840000180b40c08400002508001c0c08103007559405c10843c00484000da0318024020710400061010349001032880910307584803000f1741e05011030748140110007038000d0290f0090720103542002590600c2e5050074192140b0704e501244074441d400d80c0c1010360360010b4100b41d060301c1c041c1c11800203803c1140094415913030504085000742e00120082003a4821540080d0340d000d80c0032002040b065260f07100e400015400340c1c2c040315550000980c10040c0803601003020b00402c11400c1440c01d00349045c1c8043d201d1500180003c28040c901000109190f010301111861840b41410800440030485401c100950200350024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329998615 1250 329997365 329997379
    0x1404200a141804032a020303180a05190302030d0e0102060f040f0b0a1b020319081e07080a0b03060c0706150e010803090315041a1e040804090e07150e030c03010218 72
    0x3505d8101075194410300e54040c0003185018000041c15a4030000320340360940c4449641e400003442d6031003007203c000800d6100142188146103104162819030001007103801e009801c008520b060383c01054180c1e100708546408441c65071540342007a0300b0104060010540000003007070015184039907200d400034a101007030280d003542c41e202e400c0e81e50340250a200c5000c0380d81c0903d0016040e12138000c0350741003848150414244550b40302c00c3c1591031811221180000c29880402c10222203601852000d00c01c198050190303801c00c42000320b180e10400e0400ba101c991500b501004100c080100c080090404680311620b5584440c009500c962041154038030900c150132058443c00404144039018035030040710408c00c400e10306840000206d0082104001c401c103022000d825980b01c031070240c413681c0b1882902d0390780c0d410a620700084607201d4940c494950f015082c244025465510004049151410444003000700700c00081d1400208041090301940041001124100480011000607030210f1b040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329999865 1250 329998615 329998667
    0x30d0f080906040506010b0a020a06050708191503020409140609060a06080c0303160c03080a0503060406060203031306020c070b0403081306020d0e040902131404200a14180403 77
    0x616582c00c01650064000e40104004009642c3d800004007040072160064810707680191307c825045031001c540042c0460244010080e28001803010500015402c1200704a51f8135402c2440c14165101d00009004030360f611030f44010300c0099a50391001a00180445103289030501c0c00c03540706c09007500c5001d07940d4140b520206010401181c803001c5107101400850902c1444001c0f919600c0c001a0240c0d0816201100480800e0b10354005101c101b2082d11455071b0b03803c19078188803c8a0050703000b45c0c1150000e0050002d038202d5424400161038100c103003da00ca0110000c45070600c1801d502c4020310f6240011300108010070500500b140a0910018405280c1d5030304090740c0b900b95050300c040014040003410301309440c09500c900380749400503103e400c1c54044010160112201c040300744c812113030180c0410007040070040510069003090850001d41410b0740c000300c0c20684550250b881107003c4c40c0405115610707480864902d1081c140500ca0b031034102400c01920306046404c0c0c020401c1c0d260a0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330001115 1250 329999865 329999881
    0x160b0903041d0406020c070605031b0301030506130c15021b090112030c1e0303020c21040509193201030f0803061f030b0a09050906040b070e030d0f08 66
    0x5403400c60386100303035503551080b041901c21a6010020000c40e1045e40c2401403600d006c400b00714040207460a91a0981e40782480700d4003003580035800950070030132841040140001034022400c2500014155242191181589801c084528660b008002d20210040390341b88503503400210115090018103001072031040c440d091000b104400d01a03514401040c010100000b44903450369030f032450042e25050340020641c1c400a000001101d01500066004101941041d400b407000c52501680540d1020745100c060421fa000340c042e0b0b2185600c201c4441e0b000440382d0410448003041e8209180040003065800040000c0d01c0004181440344d9240c000380b04070000b0301018166059075001410300c0001c240b030382d4030480c50340c2c8000c102640010304504c0d21040b1740c0e550307042c5103080031107a00e000c50f015005100303028043c40c280d40964800386c28034040c8140f241c2d0100d03869800c44d80021541207150b0320900d040d10100505801c258061241c0d0717030803941e03040d0301a0040315034034002d07503408849460b611a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330002365 1250 330001115 330001117
    0x90304031709031e0102160c03020103151404090804030b25030204051f02010e060f0106020d08060609060702060418091110021b0307121406010f03050c101202160b0903 74
    0x2062036003562010321200c0c0b05185046413100741c0e1490100244c070303041c206043c1d02407488450904840c0406000c009204640e0540181074068000300f028132109071501001d41e50011070303030380f0150180b0780d5200c4460900143c4401c403005550051030622040c145240d07041d0b208880c090000c560b0040c004100c0780c68078401d008450132590300510b1880400301c3c9568000040d0703440d404001c2550740e5040c2c40f0740381d51400e101151042da18000000d0341d54ac036010000e170074110b008035410204000c213000c0020541d00c903000e846820304240c0b1540d490740070300c0c03020880740c2c41190404200c806102c4100005000c507074220b41c1c00948101c01070b6489a12100c05d204e07080c50444520009a0401072000c481c40b19103004101c81132200908403000c4980d5040c016501d860908425500314082a0b80c2c80210201008241e0041c24511001c100141c5151a515198100c1d144036070300c16600c0c03007400030315070344920108008220f003440e045560b600c640c3c04210344080f40000481d503001902c40050040b18000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330003615 1250 330002365 330002377
    0xf03020411031b1305041b091a03010e0709051216060302120a0f181103010b0607050607030c03020403120f0807030209060906160f0b100504050123180903040317 71
    0x105080c01d01030141d8002d54980c3c4c100e15049103203600c0507600011955900d0282000c040340301145000342c2c84259000400b5500c15800409070380680369004000360340210200c90440d04030950549041e2900d90040322000c0d4154001640659180e1100f80780d4940424492103003e008085114019610780c0190240e00542d0440c1d84070707194040001d1501c174502e130054007031400040c00000d00070b107000c202c0b001c05900e600b00c20307035441c940540c6002c030a050074890001c082c8011a034481c10000940d03603040d500d0302c00034034481c10182c69007092456076000390159009158020b1490801010b01d56006103031075420240580001e244070086029103029108450b609440034203001e15102c03107202840010380c41180300451501c0030710001004034403003441070107540d4070501c1c1d90035443c10042c40f813408041080d0000c2c0c4c4140d161100400101c014100c648103c140c1d81400c80300560a03503000505110740c04a0f40d02c0c552900042088412107000c401071060f00d00c640c450703500300302003596840041e0151b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330004865 1250 330003615 330003631
    0x2030d05090c0f0607030c050601060c020f040654150f050609010507140a140f1b0607060c080a18050a060b1302070c031a040201090e0c130f0302041103 67
    0x24083c400c020341050801024024040c0c1044100703d401c956400d41f520100740e000340e00003180890b600f0114034044401c0031081170207c03801e21403641040813580a14071143c070201a0100c900c98003c1d4400c080070f810001180c89000c6071200ca00c05181007a0303100002c801d03203480d034130b181140800000c00e039160f860701603070f80d10030704d0a62140c20318040c03007456404110784030706000013445901c1c00607009401c103a10038221000648408100d40c43d10030b24105c41020580e400d0380002c4582915104009008070311170b194944c1030b8001560746008204603109613407002d044207080c00b094410391500044000d0069583c8401003264511894009030515096200100150008001040441d5280d003000700080001800c0104400c82580c1040c00c0740d204071000c403400c828141d01001401840c40d80c4c0190808110249071075483c050740024403500ca58040c507085942070300d0100d001d4010103410f0326640b00b4a400403c40d52625280c4030b003200c01c04c0d07103c00c034071890403c480f20b00401000c40a80e0702071207207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330006115 1250 330004865 330004879
    0x2818140616050c0c03061602060c1213030509060a0309050c010c051f11040f06030501060311030f0c090d050708070501050f0a08070c082b1506140405030a0302030d05090c 75
    0x38100040b541c6074040342641c0181d1192410603038095500f40003143c014030311214000320401c00b9080190401c207008081003c462014044c0150000002039069804404c600c80c03110040395515081e502c600403900880e81010300400c40103009074165000310302441c000c8040303400030703800000115100041500028400e8005440e240030029540c1c0d800c00e000380400344085600034809031014126002030348415008030503c41c0c100203450f01485141d000d81030394079080c8004860300d081640701c1d10020300103291103100040003405c4540e01006035920541c000b40381e081b98203014100569102c656003d00c50040c051590005980d40c0a80c2c2210101101a10180d0602010b0441512280d800619041c02e11800e001c0304c50000700d07210700421070300c04085118501c07480c682c6e0910010081c0f505050080358602458401320b805141c6d044021100d9515001d004000f1a020a0881d0300481d44074a815200e00369406041540110150003e118004070130040e90344c42d1401c169844400302115900103c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330007365 1250 330006115 330006151
    0x20a18050f010c0f0f050d0216060c02011403060109030b0c0909310309030b010b0d0b041103130204140408220f060c0503070b07090501020c0a080628181406 69
    0x14061444c4100c65000d0403081c80003451985986040200400c110f40c010b80020b6070b2150210b071596640300140c503552603e10142c024550010742131803589030004001c8034001c0000741c51684584880406980e02994501c06402d1010040c40310350000d040091142d4101030001d2031240d05a0a14031031b180d0700741410720300c01300c414010080222101c10140c0401c5803010300030010170780d01030040c6c0c0280b044c800b14680da070305801c080404842010101314480d07410300c10010060f80244054a81107450f14624110802c1207200080050220065201c410014135080200340303c0d690b0081d062052110600000403c40d25508110a41c01030144102d91081580c6c140302103407007800da84411603c10380c00c884c680402502d0303814000b1381c210351003030014400807808c1c0503d50741400f01410a01040d5198040c05080c00398850300c0360801403402c41c84180e441c2180c3d100a60380202d0f088100302d47c8000700114032210b0740340700702da02d501d00d426560754031124484404a000021501e204101c940c0107000505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330008615 1250 330007365 330007373
    0x60b0d081b0129120a0b07171b030a09140303150d081602060d0213060e060403030e0d0201050403021306030b15030a060e030415121d0a0311030d020a18050f010c 71
    0xf1042214864000d5a00d840b400f100c10b004002d010b211500895100a4928205500403c3c81c0616280503003408120401c0c4520505450414203041c2c0c0703625805074890ba82c42c10014001d000e6184003500c0c98140a4180804400200086005020184010403102d80741c5091160170507517240c3c014201d034410400748841951103c6944d002c5440100002d140260a54812040e03070802d1941c9000b0081203002084406d400c81d600000094058071018289451030300c0c060092120209441e001d02607415a19045a02c1002200d000d96802018032800d10310070921309000340110700048400000c2040407640382e003003008010040c0715000b00245092541513803102c003c0c241661106191740300c05d0001044c840c4003401c0841000890b40d03600b0301c04410002d07044058131030805540c030444d036508a440f41a00d0020031152201605401e00584841d48070716034524603c0b0710324078880d420348045124580150301c00046a500ca007900c0750341848607212400c02c1154500b6207000c43c04280000d207204005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330009865 1250 330008615 330008681
    0xf090f09050d052a011b020118020409050705040c020601060305091524060a050d1406030c01051308101a01030606020712020a030b0f0708010e1306020304060b0d081b01 74
    0x4515124100351203480d6403008010b114680d2105000390342d44441310004c44103502601940d186011f44020f10000207501e80c00c1f411100e02c0140a8000c075100c0d032aa10620a04211500042502600810450300c8080340203456010a0040b007000a0500c400b03d21540c90029002e503892080d890540c415440301c48148401010320880b0501c0709602d0701502d04140d031400007070030f0103003480d07211b050b5501144c66481040300c580c0c49004000b501c45600340501503c0c0040c04010103002800c1050340c07488110740300aa00c01440c1e2150060348100011600040190782041920901030012a49115045401074080d50258082d8400581c0403140400c100b075900008446024005003602a0658481e1101003810000701d440000c107206000500882c254804903040c0109035841080c8d0f940d0034100301c2a07030080c5101070050503a9030044041400e004059100d4280610010115500d100161030302201b943c00c04c410030703115443d0036211300c400c461041c000c12a00580b0000308a0310314071000704110030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330011115 1250 330009865 330009877
    0x614070c0b220614160c0b0106081f12020a05094b01061b050a0b0a0f091101080109020c0a06110f040b0d110403051917040f090f09050d05 61
    0x403156a0101c1007000c541c07507218802134403500325085626454038494a51a15015441503030400200308030003808140300000f40e40c1952194501598035441b0144175010b2040d0202d4038403c0d05400f9040080d25049081e40004200c0c820b4070174070800d40d566420011028401c91358010701e180c450441c03120580f000000703410a040061182000c100c92950414120321034106c51010241030180180300441c0c118090550482079007048010078102c59850303c0d122511000c2c002c209054203c0816410141500130040f42041c2d000100a000344c1428805140c030b4600c003489003c02c201800200c2c1c01302c100e0003150f04040301d6500801540600d42d4034a0003c1481c0d070548104141d09116000c80c1d0300140d00280024954039a00544502130107c3c50011501041c40e01e400c101d00810040000920102e44c2d050401c40b20101f09185482c075041030380690071240402104200e001402192040041c004403040d1007864004105e28081c01c1c10318011144505000b43c00d90340b0812044821078071982c01815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330012365 1250 330011115 330011161
    0x60102070b25081905040906052d0a09020a081e0709050d050102211e061e0d02040c0f09050a0b070f050316060b01111f020706020f070614070c0b 64
    0x114240385610300c80843c0e03103844840f1300000d90005040160780c200c0c0c01480050070302140c41202544050502030702c1a40c2c50b281c80d03044207698901c0d0f24180c3e524003501000038a80504c0540d914452440c005242c9075049072520800f07001140040036034405030784480d2069106807120b14420f801d1100308840450424812640c03517400b044007020724070180c281c1158241c5110030415a50404803240c00c2e030340e0711601d0000105401c40c41044081e544d0101c1c070700845042000001ca81c00001e81c0031405090301c1c00e80c0607400c242080210800c03a603003c10194000c510640e116488640c5039401c0040642d50782c0318900001c40c0610805002c9034004410948040c0f1503401c41c1d24201034013a140c0c00e4003c0396079003070b501c0d160b541d000040c49580207200392400c00f0043c4042d004101140000320f0383d14280d40c8034040002d901207004000c200040d81142d880c03c50491070300b81c40b030310545000c5e4050480440500e80d000015000b0500440c05001c0e2000074907444100c04485955600d0404103a20030240314070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330013615 1250 330012365 330012367
    0xe0705070807120c0b070804390b0d060b030402100509030a0c261501060e04111b120309030f030703090b0403020703030e060a02030409050604090218060102070b2508 73
    0x2040c1d26034103002c2e20b0b9640c1311581c68540d90f0034040700212000b88032105100b8084100000a0341700c0c0d5500150b042c0c80d110380c2c0a8500d041c80d0450584206a0f004100041001c1000c1080161b8101a01c0190408401070024545818075005107000a884c000e4201e40300c500d409400034054006401c0154000c1c0403114a4030850f107644107624a2588500126603100c4054001c10881c12411000144d4210040910b00d50804007410100414802c0c03804218003c1012040f90f5034a8022141e884400c0a507c2d40300c1d42c80c0c5c0c03d40d12018026074002500780c81141d050010130394841065a10418040c0080c42c1040b03807680c04d070081b95100070310110415a50722a1800012440010103005074001d074010400301c2d040d80b07400380a051042102c50f101d400203114096041e0707400000c9030b081e42d8080e400491070b42c8503140407a002d884140720003940402d56542c40406092800d007000d11441d0300368203c82500c2c0d51900c4102403845020704480200160007000140399140c0e50415603041c2c41a0161 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330014865 1250 330013615 330013627
    0x7050405060d0f51110d0605030d020c010c11030c120a02042403031101020c0303011e060305100b0a09050306151206090616110709050915010e07050708 67
    0x564075100710f0801120913078038110700060050089007020034601d81d85203034825030300052100d061500c2e41040c851030340d80b0071005040c035443d80150040d43c8045202c0038502c0c2c13030310b601e8907100c00606800d02640d4001d105500180c80054400100d4079660141030311496841000313515400e042c1d180d030b140c1403505880f503641e2610705911240e41c0e1241035007030040039004505292040109440a0041090829181d107a480825031030701c40313041007103a9050a103550411398130305100340a0700400703010040d10302000c000098403108080d1091200500c0d16002c1c01040d03107034801034049440c2600c6180c4c84203000b01e000d0000301c02242c010301003c161424001c1e40c0c16592030000340781403c1207030210800018541213400504000d00b2401c1d42c80c4508020313000a141c08103026690320700c001c00743da43c180440c03840e80030703a00d010382031a20f602c0760b4080a84081c941c4400c04200508410399842095106a03140d08004621405120f030599008131110440f036281c02804640e95006a00c0c1625420300030000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330016115 1250 330014865 330014873
    0x60b120c0702130c1e0207050418020d11120106060507060915060f0801060f14010f18080102070b011e0501050a0909020c0c0a06050c070603090c030212100b06070507050405060d 78
    0xa4040c00070314040d4041490060200001c2c15914400c5645e103002c0c0d2484224982180c01140e0f00003614030035100002c0010f01d020048038a0907045101079088480c0925200502c1a498000b46030b010303007607942001040c1a0701c0c05500302d8072030744601400150280070090000326503400803e1094010305141a0b80442e41710403100315407459100c4d509141c0c420100700107485007801550000c090b52425868403c2c500440f520400c04d00d070401d241000817941c000c0b1038407405000c1c406151501d000540c501a0b89601d02c4070700035030110906a075851480c01c00064050070002c4400700c9016440e0308560341503d003400540b565046110780d007042c46105500491034020b1840a04440314882c402050203100d15024841b04030010f401090400208001c03000c80044d0000d8000b08946551074009483d4805061402c0c0d1042250070080d48088403000c4100d441d0000a506601c280081d00200000d4502c03200300007040c8280303c0c0042c001c1d00310030020891440e0580c4416130101000c1c0000800c80e8103507179 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330017365 1250 330016115 330016129
    0xc0c0a031707140d0206040c050a08031b010e0d0f020105060d03020d0c14030706060f060f0903080f09061b0f0c0a170a12050403150213030210020a0615050102060604060b120c0702 79
    0x4113540043c0c3c032003404c00083c4040703030994034004c0205486900780301d0305210382c3d2516031142ea142c807004d0f60412246107094107025840310b813505080c0800d0b91140e03540c0314001400f12081000842c0103600303003404039080e498103200d00002640d02d07400402d06002031980c1600c5080001d0015607200000c4411002002000d1000303080180c4038400004206080c94800ea000d024542c11400401010701540f0002c540c02a1701401500d0708500700e2a01d445402c50001218800d0041050304100c000c5802c00005404811041c80701ca404170944440c040c900908641d0303030000c4a020707680240b070b207003040101c882c1d121a0007400700a40e01c01d80d810751000d1307121900c050a03000c100c44005900050204140601c040209180402c1902c0552601c07800000448211900d40006482030ba9400641250103000f004007000d920360100081c0012481e1300901c2184040b184152405405041c0010b0703d149000c4c4920380036280d1214080b400d26100c041003034a98a00140240320840c030411004bc05650303111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330018615 1250 330017365 330017383
    0x19090e070812040e0a0606090b0f0d0207030e0306160807110a050d02250803091e12010e0d170406050c0d0608011506020d02060f0601170103080c0c0a03170714 70
    0xa0842e980e00ea01e49018100303900f000401401103e132400d0303401e00055500c49580802c4481c5200c0c10740d2907106100c1818214428010f03040074943c0b00096000805801c00c011b020b28150450580381581c0e201800f54190074048402c0c40000b0300c60748000740000d400740051032105080701d07049079000401c41e5a1286040e101e0203029026070310620303507203041d20302450f0780400d0483c4d4201d450600314540704001e1764034050101154850380d40c3c9184a00150843d00e00441a490000d014104800c00c8a4000b8000e2030f01200c10300d690b00074960070a2a087c00f0b10f50303036584060040e04140f816900e5071200001014050710200031100d042024403c40c090a000710703009410f485c400000c40c091840d0b107800007441d0039072150003550824984052015004261b20b544001c4882003a1081e0381e62a0049491040701800e00c002c550309400040180111000686580500041214003e1019108100c5440c07a944030051920510400c00c08001042070013070021907100d20980c1e00f004030541e034680c1c01e0400103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330019865 1250 330018615 330018643
    0x20d020c0106081903030207140a03030b042304120e030a0605010501020c150703080601030f0614030721060216020406080c0a24051812030a030b19090e0708 69
    0x114440350080001e00c5001d008001640051180c40055011804550441200a018154003282041c203124020691625010b41c54040d130307098040c41c1c50054002c02c2107211007030180e8503080101a07401d21031a50403244030400c0c800c0104035500d91f6682c40e02c000007400d84104102c00c034040e020650302e0420205607142c0c464000407130550304020009107421166101c2d10b200d408840e44000500c0300001c112154560945403115065071070340d0050b4003400b09940c2ea80e08651400c0c1d400107401480812618100d01d040b416100301c03035990042c4140505007010150342c14000c0b4102034000030302540c01004281c80404010a01d03000580004d411107495030310a035026084100401a07910f0b061050a0107007201208109440448a05044108000040303020074051b0018040e200d040c6071518010580600800d282d1481000070615912a0444c000010109040c9590b41400345003040301c40748000d03885200c4e4444c5919028038900a4114102520283c3c020000302044582003400490200805 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330021115 1250 330019865 330019867
    0x1140708090d080105062205030d03020a090b21070c020a0b0315030f0d111e030406080106030b0603070c061b0f0e0306040c03020f03070b0c010b0a0e37020d02 70
    0x40141c50741d05000c0b00c14660000c100420f401806681c0c6d606040d110001c0c018134410344400306202411684103880e4000960510841318540d209584c541c0040c02c0c0032510b582d407007681c0345c0d66010311000f5004644007107000084000c02d0b20914090b00c05c03ca64419014a005000b9185a8001c941070103851b812000c00c0d000000108002500d038881c4000e14010181c00401140100e0f040310b80d200c00045000d40104032141a0003141c0f20010000160170010f0448140c0c1403012001c41c1550340e078018481c100c007042055000282060283c40303200303561a8041d14035803540e0b80e1841d08440000d140c0e48112005036403004441d104c0503c10800114014464440d82c101a4410201400f008603041240c0d110350700c03000c200800109420320040840e581500d20207440441280041d05060241d089000002c0000c02c505900303113415000200c1c4980103a541e040c0c080e4a40802000e4000c0481d006c044504080142c2c0710b06054541528400070382118000e0162400c150031203040c1c0c0d116041c40304803590 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330022365 1250 330021115 330021121
    0x30415020318030a0c032418021c0b0703050a090f050105010306050a0b0d02040203091c1d120616021e010f05010b031b0c0a120503090f011a06090301140708 69
    0x101c0b0710352030410702c401100185070050351556050a00952400010050843d0f220290b1100c1d46d403074407140c00110746101c00e101c01403100100c4040c0d1512084103038031035041c161100d440d00000c1064a0000c503040410480d0b1a55a01d8003a0302400c00a04030540321692400040c020a000c03000c0706a02510640c000309865245040880aa0b140540301540b56850450700039600c3d034410120702846c541c10f850168690b0354a600103414a410001c15540c0b00c100e1a8540b981a035203c0b0700000200e0300c4e500340850880002080c01944068640c040b211640007101055021128002400c1a01e038140704450510001001e4240440e05c0002040103680d107416040720300c0c600c14007641d40900316800700b860441c6840021258080750344580070031704020010b40f00076008410701c8200440c68001c0d05a40c10b400007000c2c0102140d00c00c4078500c00794050b400c00194a8030060207000540e400b00110748030200300c040304019680e409900380d01e51544d03071901c2401001d83c002c0034141c0708070700c65110b07030040d49 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330023615 1250 330022365 330022387
    0x703020102120903160201110102091c050709020a08015d0305040509040303020d02030f0a0b040b1e03030d14090d020304030201090308030a090609051f14040605090304150203 77
    0xc0d0780901282d283e90130601042c84070f8102c02c28420f0019030246420400c0103035614645009119807070300d01340c102540c2902e1440010f85d00c2ca0211283d80f05804482c90980d4401d1241704070b01031074200f000004e07103120040206000081401030100c100d51b03000040c0f501403050200d01c41c05a6196078a90482110900110109000c0500e54500e150066154003050995004040340302d640202351080e0f9422000c18103140c402c0d1b0503a030088c000d90700115641d04000b00050494041101c0d401807032400d100311600a810f103801090369040005c0c04603e200b03199803100d000b040c440c030881c01d070f0180300038000441c85070780b07034095400007404880d448643c80c140300300b206003012145508c504c00c5d03600803c005c01c0140d91013440e403400c4a8024103182e031681c5918080601419144d80301800003802d1107205401e0007030105850841030008041600290070046100080c0d625013140121210740703500010f00450b919801a65120210b142601e280c80c0c1c0314040d00020f11010054800144c1c8080380c041014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330024865 1250 330023615 330023647
    0x3060e01022a010606140f160525051c060c031410290301060c150507021e010c0c02040b030703140303100f0e1501090b042903070f0813080703020102 66
    0xa4289840d1000140809945858079031040f900109640500051008051a0440f10000d0040d521906a43c0303101e180b820805072b90600400488025071800c83c00050500d8040080b4107031813500c00d05011158199161a0000c159400c9090705050300c81408014200a441036103124005072140c403013043d401d1080c0820305500e050320050040d101302488002c0c4a40c1c1d1000d40b811109240340008054104d45804000c90b625101010816400c140900210540200f8448035840d41f02030245010360740d00c030056090700ea5410700c10010078030703030034550016040c01d4001403c440f2001e022107200308d41d01e60762444280c00c03018460b503141c0c00c048207200c100041354542034002c1011a1032010401c0c18aa000d5540c050054280c0c40074900d610b00074043c1d40d000b80c81400040070858a00ea07202d543d11940103102544200c41c10305802c913806201142c020b070342c02c00d8900032203080c0c1d01c440c4604000c8a040c0d54072a000b5281212585026151500280708800102280343c4658005030f1503011401c04240c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330026115 1250 330024865 330024869
    0x11104030507030b010e070512070513060324140409022e020609010b010f0809011d070501030e0a03020c060d06080303180f1c050f040906080a051507050403060e01022a0106 76
    0x6d4001e030a040c0804c0710782c0310003540d80c0c0c045840e80301c046035150b000050301c1a110704640c5080d51545460b00194494160780074040704c2c00b13103158070408144a425082c004126074016141d05221010314002141400d5010b00721440c800340c440c0030455800f86031405214500c4000302c2d4071000c0c020303900100c03980c18003440c1d802030ac032040240031403125134001030a07100c2503030895070800000c1000169690025006030908401c00e880c2400401c1001002c0307500c41134140220790209050100d2000100320000e12462107503090f601500e108840f020402075203a02900183e0b1002c0e407078440c0411070007000c2c03005600403600c0c0101e40810307201c08d01a540c18185e461a2000640c0c00050790401035003966417684104072418a00980d0b140120000034840380a9a00051a21454900046503099000800038240da00480481710072401d00060000b00000c2203618200103401844108001000c9030408a20380400b00c00140c18281010302c501c50000d8504041c203403100805640100c010028030035800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330027365 1250 330026115 330026129
    0x80115200a05070e061003050403030f0c1e140d02090d0816060f0c02100b01050c07080c010206090613061107020612040b01050307140d240204031b03021f02011104030507030b01 78
    0x8021725149000400860a14001606050316107001504040c440d43c404240742c1d400b8202004500d00c1414020210a4003501400c01c00c08100d151090190141c1810101c120fa00c900661600c10441c612038065041800415040341010f40640d001903d214040e10000340b000c00000e01381c2c0700c0f0b0300f0880143c034043c840ca60100361a0418403081a5800f003034403d5040c1d030008000c41d0303841d41c0400403202882400b61184890040b0341002c507038004042000520f00b4026421200036480e40640d0300d440348400e076000d0b4002c0c1448161340002130b103103812001c0a0307000e600c00641007601ca60003180030303580310804902e208039601d010407040000022036140500b40171740041001e94100300c91202c00115400c003440c40795949245078802c0240c2d003100001c8081003440100300301520210f015000c2e4206000c1214040b1502d00804c01c0080410f030924212a00280200600311454070110791090361541d03864110b541340c41300c109000742c0c0e1500510042d03200e18010142035103141001c410030345040c1c202e91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330028615 1250 330027365 330027389
    0x5090d0306060e0f0a0b0a080604050c0310030b040615060807020d030b010203070b041e0305130504050708010618210501110f0f0a091d0a1a01080115200a0507 70
    0x201c42d03998094114200d1242c03d442100301c41325800001003c1104940c852214010009412014503900883c414001c810030386c1e0a0055480f80350400181b400119041c1c104822600010000b09111640168200d402000c00281010f000202098500555000040818050010300200720360401009181c81400d28080080c1e10302d4000003500c0b44610340018021000c100b02050a002c0b12255800c1200410900ca58200c001e615016060340c01595030890381c440c074210001407508050050f684200143e42d116a81c607070805600351070796018252000c41c0603000030808140e001c4030b0521090a1160542031001d43d414034500030742590781140b019100902c0600480b46c40404144c180d861800e1100038681d25247c095104540c490460b0b4003044851103e20b00c01402040c50600f1140103030300c40d0200340101d01502d15416241d00e109079055001440d49001080f2215081101248120340341c50040320404203c1e884a800c511140c680c2003030b9070010511a42085400c1240310010709001e5401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330029865 1250 330028615 330028619
    0x60e0117091209030114090d080109050105130e0102070c140a06050c06070e0d060501030303050a0c0c1208090c0a080105010918050706050f0708031806091204030f03050c1005090d0306 81
    0x2180c0302c10110000c01d26076400415021001d982c02e40102c040b0b18180c40340200c0528006d0307691643c814103600c40c100480d03c144004030f4900c08074000e10b4103882d0040c11002007101011039040c01080d094103c0fa0700742d503007441454002803d44100e20028030807600300324403108a160420003489020361050040c810104040c124460010502c01d90210441c24021002030391135011a0044203191001401e40b032a080000c8200f68150740b00f41e004d2000b0342d800300a203000c0320b00217490401c1c0e140000ba00c102d01ca4410081c03043d11401c02c0c1030303200d0100429a00201d403a00d01249282005400000c107603510b590061005618074400c0d00c0389800700e007080f248941000d885950b00c50310715001d54000c100d00050210b80c0e07a692041200c484603070005001d03036a480e0442c0701543d103041d2500f1184440c051100401c100140001d82c1c41c00060b40c0b4030750b04e0f150600e1980d82ca0605440c0810882c140a03080c0809041d940d0705001801c1c040701d4407140824140740c00d1201e02d091104841889082c1450a101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330031115 1250 330029865 330029881
    0x13050105090c1e090103020f0c0f0705060a080a050621060a0e060c030c0304061503060905070b03011a090d0f0c0f0b070f11010e060a0c0201090b0c19140601060e0117 73
    0x40b6032001e0401c6a01980d924134000128040d1103003426200200c034000960b0a100140010642a804840e2040da80506d03250000c0107401d2050316a00301c0060103a80110722003030526406a83c10120007020000c600d4440c07402105a003d103102003403000c2c1c206408102e102c41182c01401004a00c58010344401d182c210821403481c000541250107061011000070204a250762009072070417500e4100c0502c2a03130b00e10b84000a0b0040003c11903076801070810000b50740041c10150382c181c0d11408440d111012203502ea000d2143c00c500c2e030441d8440210902c0340049190600791603906070290303025441c86810505404401e6400b0390004245040400a06012540391010111059800401741c01c2900c2c0d4100121200107001d4481c6922010000b00c6a40940d0000350380450303603101307895203450696180b400981f103003c1d95140100641104500480742000e400c40c0c10040340c4103800341240001c580340350901c3c10034240c0105012503840100e050003076800010ba49901007081025118a10b0f01c2d0603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330032365 1250 330031115 330031147
    0x1e09150303090e130f0804031a0402190501080115030f0c09082b0e1210050703060e09100b1302030903040501090b0a022505040e031206010507050d050306010302070213050105090c 79
    0x917203c800c55000103010010700e03100310b500841d0030080340806604541610592600c0564089100712084021050f80c10035010b0707101c1c12100c0584420036260318020129041c0701c0d250762208101582c400da9200009910712a001d031907036269548501c05424031110764501910180c920640c0c081c1650410542905100c03003a00b50149032621183d10100e0318040f034070702904c2c01d8401e02640990340301000c40a000340d1289100c2c1d201c6a40601400d40e48101017903600000707542094490708030300c1521074400e0058010010030403010f0039010300c0c59124540b020490300b0540322202e09400000c3d04122a40e03201e1902405000c1c0b07041d540349071114540c0c000c1e680b8110344100003222030302c0c84210030156020309107000040c88094014400d201900419540302d50041d101c4611000045022070b070194400e0301581c0125a2180c020710b070281001d203081c0d8980d04010aa00d04041d02000075000580f80c21189500c45101e442c800701b403a5040c40c04000c07014100400c1030a115000340700466444203144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330033615 1250 330032365 330032401
    0x15170408070201032309010c022401030b090c03120c100204060c1101020c221503030c0305030c09131a0f1302180d0c0305070501090605041e09150303090e 68
    0x420300281441041000717403c080306002c0921404400c0c2e1040001c0c01c44190031400d0b40d03040d00d6003038803003000040b140303040907161072001c1e1881080c50400500003c3c6662522030740000250084410180310f92001078a0b20600d12540003c002c008a98090308110801c509140c0c0140441c0030b505043c1003140080c610015000090010343c5030005240300d5900a001170b128501000d0303c0700c21500a080a01803c0219845040f0040c07032070a00743d40096180c002d514000d5a50540d030302c6e0942100741d00c0445a540002c1d148003000b400800c400c044039901e00490010400301d000011039240c4c4c4038140491542403110510703028502e00340400034195070f0590500d0203e03000440060b1642c101d9541c40c0b203450740807210a60441d00c4076060809002c20680c80c80304483c4240122080e140d100c4004488001240c4940c1e40405c10503c000e0040a80100507049240030b2482110b45880d81c481000c016204401101400302d880d1030740601c01cbc154802c01010107000070050b070f82240d040140180c090300c400d40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330034865 1250 330033615 330033617
    0x14010c05121306141e0a0209060316020f06101716050d1505040602070507090b030d2006040303020417070513090c15020601090b0306040c140307080715170408070201 73
    0x20701c45400300203c0c0d5100c03465501140728072424600d032800c3c909400e4030341c062641d8078420304800042c40c00c00c00e500072200e01700000350a00341523882d02c202c40580180801a0b5200350302030300c04900d03d19042002003a200e0585503241440b4145000d0b041e81d002c4001c0c50b540e5449411200c805010712034405481800c8a40c25100d0012062081c206021082000c0f480300100d541480700380018801c254010f00079007805103041d00c0c034150f51080140704444003003680301c0e095000b15088240b0a40600319042e800e0003110044003004080d241c0c2d0b0ae003440350468044012079404103062000100c652941c494410b1500e00804d4128108000190400000180701c42c1c2552651803507820030601880c5a0010004442c5c6440b03060070810000e91511001d000305041246400e00e01c51562500048081c0106e401c2240030300c0607401e10000f5041c040601000c2d0b0307010300c6a40e00c009002d201c1040464018425002401d0103000c5004000f030401c0026500c0c44d032003510181c1030201140c002d400b1a48020380c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330035971 1106 330034865 330034891
    0x120f0c0c0317090d0b040b06010c05030712020f120c010f0603020d03270303031a10120207030318060b0103062306070503040305060414010c0512 64
    0x1508202520811011804102185041901904410a902503503250911a42c04900500d410b9901126809219400c104c1804507000c0050f4010000340780000300c4a041d030300c0b07413a03503805410000307801c04c00710201c2510200d00070088541d8100c20380098540301459940c6c5108150802000000c0550810783d500e40b03155254482c8100750b940c000e041600804a03078504441414204c00d4100380c01c0d0107018003525491070114024010f510942d00030540c042604000d0b10b1414980f0901c50140e501540840c0c2e400d40c118103001024680e01c1401603c810319814220042c0c07c1110071044e811041c0100d2000348101c035040f48000031000c0e00c0c2841417135910b40c01d50001048845522269414400b0344020318544600200501070051003203c0c109a1241c88040c284103040d202122100d2801c081c00c101c50a0a020345000184d65090a030b04002d240500d000d18010300914a03580081 = true := by decide +kernel

theorem cover : BRFrame.Cov 329856115 330035971 := by
  have h0 := BRFrame.cov_init 329856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 329856115 ≤ n) (h2 : n < 330035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
