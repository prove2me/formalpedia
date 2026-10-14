-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2614
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:13:49.681818+00:00
-- url     : https://prove2.me/submissions/5492fd27-a1aa-4dd5-b5be-22bbdf08f125

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469964028 ≤ n < 470143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469965278 1250 469964028 469964039
    0x20901030e030c190507050d0f020111010e072306030a150b0f03060d2f0a050609090412111b0405130c211e120c1e0204020c0604150501 60
    0x810340343d02c0403000000e0580321075008031840c2403004104c003c2d64076200c2d85074009402e40b900c124031070246015181d08104401c0d5400050f00315440800341421a80c50320700290b0740f10001207400010781e4a440301d8002041418600c002000020510f1554051340000a000302c46810382d00c060b80006099030385040d01c0d50f42c1c10383d01d4140c6c000d285d811300c00c0c1784c0b0400c0002d02078540a00074070111485491081000340a9420702c041c0610140b5020220900144604115140c000c0d40c035801001e0446081c1e20f403c448101007034155401900c020240c4100074001f0020318003440030320403a904250100c03480400d030703449050318685608007900d00581c5090f001ca4042c2100700c1280c0c0e5440d801900c00000c0f107203419600006140780941080713456061090342000100907452180c010f550700d006000c00160241042132810303105411038014000d086c00d000000074112221500782c00310703030300f00c21000c51250b0010401078861020f020640d4003c12013008200320b42c41c0030300c4400d0343c542813007001f6a0380c0b0303031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469966528 1250 469965278 469965283
    0x10e0d05070b03090f0607051804061509171207060b01020705030d05030a0b0604030201231b0f010609290d0b18070f0b0702090c070506010602060915070905190305070603020901030e 80
    0xe0700c00c00700250080049c100700400740031128501c502c01800008100750341e03600301440e41d41c5040054000803024482007008400030001102c2060203c0080c2c04036074205003280d10a84944c8030b0007440701381c031480354110982c000c0c4090340081c08083e09803036154144400c002d0480d03004a4034112a00c1c0342c1002c0621341d04142c1c00b03960035243e06840301118400b52007099074804202c2c0d85403a02504c02003101e00c80c4600c440c070015a030400ca00c0e00074420300d0107514800d406d48219070016121645010051a503040d421540325650422a0403280107107128000490340b410901da401030f2203004074606120060580400b010444005d8000780d541041d151400e451a40806110300e800b071000c10b200504c0540b07800501107411041000001d4079041c0180c0d01c080c18660700341e00c00d501581259040000e0381c1024814030b03c0700403194140c0201460407070006400d5901d00e005542c00b4030049100c500306210310361200006150080101c900240d59807000401a43c026000790b40041c0c2481c0b4007600b81c4a00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469967778 1250 469966528 469966531
    0x2007090c05190c1112070512010e01050f0606041206180327081e16060206060109091404030503040201021f0e0d03050c0d240609090b061602010e0d05070b03090f06 72
    0x200c0e04001d00c04d550f1040012652000910780c140c0e024401d000600d95a481c92801c1101c4148000030440944400c00142161001040d00070001880020000155104000c44060b52103007005010f080d806400c3c00c1000300306c5520350282170164040e1810506030048105810454603401032001c01e0b402503000d000054007840b41c280706a01c159070f0384801400c402420300d0143d86800c01c64800f08a21602280c450305994024405030708a181807088651303024031b03403501501a6400c10b2080b000700401c400e607490401800a010000301202060071680700303221403001c000790000d4008200188110300401421481c009200c58860b6181404003540a8090316201c5d060700840107060100150a00c0c02401c80d040046500c9292690945110f18803215074801400c003540d901602c25081c82c4480e0222107800d01401c1c807549060111015600c00c000c580311000b41e080c0f82214402000300b020803c0c8501c0c1620041440c0120381001c9200000900a140704210050454a0591201c20039507221b040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469969028 1250 469967778 469967783
    0x40305030f180d031d150f0f0411060a0e09160f170112020604030503040e07120209061903020d020403240606140a050d0e010903030b040501062007090c05190c 70
    0x1d01200c000350090788400b041c2d1450540c0e0700b09041d522030105d4100034540d01c400342030702201c40c18041d5006000001c01d500219400345004035060540780d003420b00a50345c1d000343c49240006000c50181d0721452980704e101c00041d084048504101d000316500b404150301403000a881c01c3c1c1000042840b482c01904000000702919400b0390824000d00c010180c4081c043c0d030840c070104030010019004000030b0005002c40345a42d002410508002441c10401c942004202801442111201c0e520b1100300c8403c590020700501c40884401c0d01603000c6d01402a0384180341e0700c00b2070000288101d058000740ea0010500300b011201c090040d00d941100e129009680000d0304040010040d00d03900b0005240c015102d00f0300314140000d0ba0a410203560455040e01e5140c1d4403800c0000405415010300050f80104407000d209940c10410002e00380d4045036003d500800f000364070307204130000501040c405400582c0c8240020501c19001030850741c040010b051000a03c08108030b44a0b1007094200f409a5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469970278 1250 469969028 469969033
    0x100b010f0905061e030f011409010521010b03010e0d0e040515010c030c020306150913030206070516060203041a0901020c060406050606130f2303101104030b040305030f18 75
    0x10b04180501540f030b0812071440892103d13254040d5046034800c0c0c05544291440258140d1a41c144886841d20100843d1042e000b20100da006000310b0b9110f00a8400410b00f04500350740c0500c1e200c500d41d014103118120a90507510303017484150241c0000c070352030303006007138030344600040c13003592010312048642c126402040c00c8ac40030340c0c050725584210105603480e8041c0c500751950301402d07000642000419110f80e000800c0c0f141e545800d07428401c00d0f00d50b202d800c0c0036107110115140d45000c1c1d100d800041030082004000914610f225044440c0441c095070010f40442d240c1c42c1c00d20b040440c4540c84c01b01c04120350500c1000400807441402100c4a1103c4100907002e25240d41d1703201d101a10016040580c8400144298080203040d024600002c0c640d610900300c3da54501405070480e801070300d00000e0280740c00c1102889507240001e00d111008145400028810650900450a40a180c000501b40000c031802d03c024143d1050140d4087c00303030682e0b141e0094032092110326054049401c8500146c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469971528 1250 469970278 469970297
    0xb0303090607020d080715090611090f04052d06150705070302010503040c031b05120d1b031e02060405120307020607140c03040303122d020315090405100b010f 70
    0x141001c04d44450760900c94a040707418500c45030394200104c10401349180420f680c80300b503881440307824050180c0c1c1e1001700c82d0551800200b64041220310040e43c1c201800380d41c9940110300100070b40c203403014200c0d11819000c0d0080042c404105203444040d40c8080c4207c1c100b0211170030200d9140116074505500000410100c1d14550040d2020741004209480c1814000d200101048485550703030381c811455140811403030700300750420880b0381c500c0c0081180c81d40304900c1c2c02c01050b00840381b0780d00202c0701511030004170000e1400702e403541003161f2910503803402100b40007242ea8001440c6d500980c4034205445045084030a041031030b0108503607410050b0704c6203004c155043e020700d90400c410503080031038600e009401c8210394659402503108900082080c10a40304208061260f081458480000240071f03200c50840c05071003004250b503a0b183e081c3d0000104840c600d00a0013042001000b03407003101b051400d800d05584907019103140100050402404044640c820010700350043c50988810b201c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469972778 1250 469971528 469971533
    0x12053c1f1a09040c03050406141b160203011b02060106020a0c1401030e030c030a1115011e090603150f060608011a160f050d0207080c04021602130204090b0303090607 73
    0x8a001c40001e09040300d80810010950307440300e00804d0241000d90700c001c282824240703062000c507515031045e0250724503240c0900c6400c540350003020f8118042c0d00f83d10307a103070103400b581070a05180340702c0025415842c0c4100760350f02c441c2451441c41130503910340a0702c0660f80c1e03800043c2e03111034404c10020312162501d1014010340b000c0034040782d4541c006240025401541980852459000040a0601da03002190400105a2000003001e804404078050040c50041d0700c1d150850800c180100b00760002e071540f038190440302105070307200101002d10003030103c1683ca003400e5007440640e500c03243c503d5003841103400c1c9070702540c000c110072580290ba55949981c60314a001c1d280c201d4224042c4085a802c125080a224140d00792288460180703006991007013107031504501d044800b194000c155080040200120703040071a40d800003520641c2c01503171b80c14004604840e0b224443d0402940302086c6150700e890a11681e000d00141d41e03004074200141d440c414101540c81c000d2030b6042c0d03885402004103800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469974028 1250 469972778 469972799
    0x121707020d0b0702160605030615040f050409020d060c09240f0e010c0501020414100c17070f14010e0c04060e040f081207050702010e060a12053c1f 65
    0x3d0050061040c2c407255500d8003d4559102c50f00e51120b80000c1000c01031003024646000810301000148280c07600c0d0503d00615003000700d00c0d510401d13100700d9451a58105548410020718010355000c0b00400403006045005801140c5030301801407130765102c528810b448240d8442c080016074090f11400740031100c0c901b003110f048400450302d0341006621100040007480900150000e03200c601c000242d00d02c2007a09015201c542e9211400800903107038032000c0804c0001c2004503e82000e240700640e2003909040618031214441030040c0443c4c0344107850302c00100c040d8010300381400402d09a50100d90300c081004140c84150051810502c1030030007280014038080803188440f40b0400110303003080d040943d0100104000c0b030700c003008540300140d4402150303803082c001550404122a214180380030701000030820003450300f035003003240c2e582c10108440022401340d84103034210046500402c9200040c1a07414209506904d100c65904840803a20038010340742c107543c030f41200203060483c0d28544480d07002c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469975278 1250 469974028 469974031
    0x3030c0309021f020f07091d1203160e060f070b0f0610030905070e0907080601060201020f1b010f0c050408100209012f07030b01082506030e010b0406121707020d0b 72
    0xa5200e2421242517000c0240300d9040103082400e00041c0025261140f146422160300d012180e5400200070003001280f07210a0300d8000e0f41f40c246414102000078400d443c042c40c04500b03160304c41004101070036407641060062851b0f42c49042044100d0300c440742c1c00904410183c854962202e00100d01400b820710030741c031910a45000b08101e50708180e8400300d03481030030000d84940810b40c01541091005100800c0060b00411080c03000710325000500d00e0008050203000305480724603081c00c105042c4d005c02500044894a20b849040001116106001c4c0082d4090f104104081c0100102c0d20b8102c0d1881c4280c8580201c1a100e5006425001c0c01c1041e00c4031000c80e1246039003225249070300b1080c1d010013000010391300c18045407141e0b50416448601d02091580394644c96400207604181c49140700500e4402c891850601080d440c0702d6408144c00350000d011419003152408400003942c400751114141750b14091910125081c002c00180c000f20311030584044e40000c8200aa03000059000780e405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469976528 1250 469975278 469975339
    0x90804090b18040804060f0804020904030806030109150506040605040608060604020c0723091302180a0b091311030a080702130b0613030c0b040602070e070c0c1203030c030902 77
    0x4409007401482c0c9001506001da070281c4003940081810300c2007a401128601c00c261107414161103038542a4001006100010001001c100b40000070880a4900350090703c03455078032907507000c202646900e420b00140402c07a80c961040381000d5002400c1c1c00c041c450341d0255054400540348a6940201380300c042d52115100000074429108001410155076200e1540c1d5800c044405030348810140402c20b141c03030b0191007048464114200100140e60b123101185d04080309014407941c0c0e80d100f41d610002400013014a903000b4a0310402c000740b0f54004c0e240004854850303a80c4071442e80100c810b00d0b0b83c44407411002000410108008005440c02600c0c0b00c0b8100382c5808017061056049004c9052500510180c1184a41c0c481003441044002005a070140c100c040440f4186403401c00c0095880d40790344260b80c0f10180940c04034118622810342035451301d40007840200396075621107134404001240202940040d160030b0450440700e00ca401280001c0340c00030803000c00348640b650b40d80c0040b0b0702181030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469977778 1250 469976528 469976539
    0x15090e0c0d03090b0310030b0105101b03091505030f0115200c0d03050d050903160b040c0b040b03090d0513350307020102010b10020601120c0b0d1a04090804090b 71
    0x9081840040118400c00c5803900989050340347d8980300c030707181e08107070012842100c9840e02d90074000d50000d60300d4261041c12541030303078055850400303070b07100005604082260000170340e41c111515000070055000c3e44016840000e03036039032071071143c080000b604c8410000420090780d9200092040c401250810002c4040c0c40c041c5120100003019200050411008101c0129500c02d5100c024428603a0001d4a50080c51500c40c030314604014201c02518020300840180004c24107010303441da0044007911b15111415a519241c0301c0390101c5400441d03006110780700300344801303505174450070a0307070441242d42c1d080042c06400c3ca0105040e1030310404240107201005002c890452420317410900d6210080006540d4510003400020700755a01800c0d142d00407200e401440135402c2c2e0010b00141111081a0396640742c880519000301903800c698400303d46200c001c43c0b900e2070360990398800b0180c4080c481020301c2d09052207082c4001e4407200100580700c02400d1008020070300b803d41090311700ca0001007a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469979028 1250 469977778 469977797
    0x70303020415080402040b1219060b0607060b09090a031b14160f08010b0d0204051008061005010e09060d06050703020c0a1a0708010b04060507030c0f0615090e0c0d03 73
    0x20401c81041d62448200043c00001840254241441414215003040d0b8240d20300700300320301c034180d51030031008001030010070300c0011041404815803181c401c03d0f0004080554814031403c1c003401a103110b046651203100701382e002c190074103000580150800d500d603d44100c00c008442c2900034000041ca000d440d0410130f082901100c2d10240400d1040b01d00356095502c1050500034407641a5815800108176680341a5103d034465849410020405038104c9001c121580d43d20144490901c45da40b203060a842840306010784c80a0b00e0b43c2c0142601c00030382e100111040c10408100f940320050364034640040001e08801c1c085901500301c0ca1788680c01d818058a0120f08051030341c0b030031142c0b0100303488081c40c1420007448172007103014440c0c0068803494032080950500744040c42c00e1080340300e03007400d10a0008083c420903010b0000d5640711500804420200c01481c200340c0090003c01c1207d00c80c04604140c0415840307214406d40e01c6ca112010010646030040b002800a000c0014400382d0030320801c0712 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469980278 1250 469979028 469979039
    0x10305150d0b0405100c1e021c030207051902130905071802031609030206040b030a060e0114040524010c1a160305090328030905062e080607050703030204 68
    0x4401e40d0701a44140c003000094034283c280300e41440c42144901c0b0402d41850314680c245544190700104200c002c03400703181c6000c0d80352021380c549186010100c8140b4003011903110390f0703a0503601603d6484d000c0c0c1d054030704090340070a900d404085c2410700294000c814124015500000782d0003000507500c81c20031961190340710403002c54244080902201d080c7d40010400a4011120300300503d00c0c8502e00341a1086030a640c000340e2070380207600400106940c044002108010503822400040404041681c2c05c3e5845603559104c00341ca4644290080c0d00b000e02040300103414803c41c403000004d9028403080c0c600c0130b900440e0304552500007540d4041900064982103503900d0300f01801280006500803501310801f40103420f40b0402070510199410901880c11080406070040c41c1201020880014007100c00001350010a01280701802a200e2101001003000242500c000c5080041c40320b510b800c54a19800038a8104d9130198001d580c01c83d0001c64111801000a042e00f0340c400d01740507003040d0f100c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469981528 1250 469980278 469980289
    0x20903070305063301090b0a030b04021908090d140d060812190905030a3201020409150f030609080c191103060f070e0d050601030501020702190608040201030515 71
    0x41c2c2d201c900c0c030496500c4110000e00c0e855801c13824115081c884600c0103030b4207000601000054403554851a00014440d800e00344a60310980034010700410441d00d558140a001c0c00c419421500813011551040104500c100c002815402e20f110039903849401e070500c0c5003448100e0304080008080c60380c90b00740200d1546ca0621801d4134403c03448803207a4840c200120400e4005000d0001c40302800709011051015032004038241c0200d54103d8044001c08005100425400c0c0030703030811005840c030266543c0c1844806400810441e0202007060041e40e200d40c101088142c201d2044042c807132488002080094401d40000d520a070003000820f09210b94514400e08110413a001048021450000601003002004001c00c8401003600107011910340700b0095030f04041c1c05820f010078000c280c1100c400d60b964a443d00c500031540301050b01d140c0d581d00d10f4140d020350481c1000b00d2141c091107900b04034089542c0b081800303c6410b90780e050311640792034005500400d409444006504991110b00c1a01c1e01c2d20b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469982778 1250 469981528 469981531
    0xa06060602150a0b220f0603201230031806060a23062206030f0902130b06090307080f060c070812070e04050403050a030f0b0a0501260910062702090307030506 70
    0x22742801d1508801c2c241042000400250050b2240001000c1c0038484400018107503c14500b043c020600010007820092005020080c02c00105c00c000007000300018800410001a803500310440b2001c0c0c4a4400708500200c19000750700010071008241d002a845042041111311000340a16103412540c0700c61102060702949001d894046d10038003006600d506103d00c1e06200c5040c1d400700200c0420ba03001890790b102c0190b12542050302e03601c075540282d8503042241d00090006044441059907072005c8c9031120f10a0010301d0130742c01580c00140c04000c4440c2140c420b41d502225151600b00011410b442031200503007da010040c00c04e681c210743d51150b1068130300880c0030340c48550b1128801c0c5401030030754826090700041142014441c488c107483e0000d009059641c2400c0400c0e25101c0c0c41c1c6044500705509030721000c1510340300d040c00710b454070118002d030382601c8a200038006940c40e9030a0120038508000c41201141a0420310607002200c0c1e07004d429030040040076640b9041e903036200ca91a0020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469984028 1250 469982778 469982783
    0xc1c02390a081c0302181905090915061c15020409020a05120a0608030a120f090c1a07030516111003060906080f07030b090a06060602150a0b220f0603 66
    0x10a0803140200c03240a20f40c240100c0e246000e51030f007400585407110410814088a004581c1d0100b40f185800312440e081b005080c0140801d4554540010700da40d542e070341609450034103184400407410354140300c0107103500301080c5110500a260f4541e220980707201744284003030403c0c1d400d000100788210540002d10031403040340da5107900c410b03102c4201040c40c0d002034020b990140c40c1640800807040e0100a5810300c5082e8240369100c020400101000f030450106010001c604c0c0900b1302040048201041081d610403006042d00100c0d0203000392458442c500000e0007090303003801031781403c000d903507090807031180309101000c10003c0c1140170910320440c100241e804a03031034400174400303074003103101d90001007420100801c01d004c480c1c6800d64a5004502000d404c0f00d1203080050303142041046003208071a03109030104003203540c65000070b49820005582802001300507000c210104000c0c003a004508a0003080c007542410b00441d9031409900b00401c0c414441d454a1012045034079500c00e0380000c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469985278 1250 469984028 469984033
    0x503070c060801091e02180a1d060108100e040309261207031407020613090e0d0e0306070804060e01020a050c07080a1e020409080c1c02390a08 63
    0x2801c00901402c0301c40140c000801241c506400c0d802d221903246904c1c04014081c100059903103920b0b141d20540301202c0607006406c0030301c42c00006440c800181c0c4035054040080924665916032074011141d0f5202079960b603c08034080e60082c4080029004c42c3d91700140700b800c10002c0d02d40d0782c8a0011901650b058803a1581031103c41040000c0d1081c445501072600f174550b43d6150110564002e004184403a024010540012495208548079002107074506031003490b00d982203d54400f500b41c09880358159803a400e005120821500da40501c8981c50300c500001c001e80342c103503a49a802c4400590040c410b550164a8072039642d1500d0080c401044407542a564441d5a440489261880e1051603406844158018042d49000c02d0f48078150000d5080050980d1a05040c54000103004d401b081401034410040018402420740001410b0401420303101a1003052201f08034040e80caaa850440e5901040c0e0301a01000202d214000b5010342d210920200d6000302031102e0103d1441036554020a490b07030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469986528 1250 469985278 469985303
    0x904090b0901050402040c020d0926010204080706020d0302120a020a120c0903030e06070302030306060a090305060112061415060a17070206100e070507030c080705120301050a05090c030f040f050307 87
    0x11b09143c0194141c3c60001d000901144189030743c000d10054181c810100b80c101c00703020000822041c4c0000f0020314000900070b54446860301401070315010580300300c1016215100c030420030b0382e02900035642d140c2c8401052240e036980b0380901401a43c04494601c080003280302110207900348034821b810108645030749600041d400e40c138002e8a0900300d00300d0f00c0c0c401d01007401201e00183c0d001088035400401030340d4031911102d0b1000c05407200c0c44d260300001c006d80620b100210361070900310003104407140079034000d015403024400c2007001c0010981e180c0303481000801c0804003e08141c4000c0190b007480e843c0126001054210480000400b61413801c0107130040c100b445188034851141c0806082c51a0158481d424941406051403064078002414807080105541c2440b038850152807106401200f82c1c1e42e26070300058900038542c001d019140c1710b040201c1010641d420641100d52082141440c11031840d01c81e0141141c4540004104807525002c4844400020304103002401c1c216102c1c00c42074120 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469987778 1250 469986528 469986533
    0x403020d051009050c210703030c0503040906031a0a02070b0105090c0702040906050708060a0f05150f120403020f0a0b0606090402091201050a1404111504050402130512030f0403080904090b09010504 87
    0x10048401c500b440c409011503001b401d50ba001c11910102c99140c20803c80c5c262040c6451401c6000c2ca50000c801141340141c0007050011018806080760f0519004c5070480d502c1200b810102c2c0110703003014194441160061101d8205013210031341020701c0484040c10b089890780083c040d00c0251608540e0701d5243d2003030003482d582013180e07160003400440c1d03611043d60815100f0703281c240091040c01d126284481d00a4003040030a0201c41d10410210265503968140010440c06a1800d64080f4010310a581000040d014082070510541d6070080c1409501d440300c608101e00d40e0016101664450360820100700c0540d00d200c0360600c070201e101c0011440e840c100900030221001d80b200d514010f01c8803020000004ca030203643c007001c140200d4a03c0d8110030020302c64207080c001e80d0442600240300181c07003000e010400b020001100c20444003625141413001e5100d40b079000300c21a8413a4007105000a00c00114540c02800c8089000b5000140395a0396440310450103c06a441046507503403603050200707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469989028 1250 469987778 469987789
    0x9090f050105060f060706050c0702040216140d0f0c06140103150b1905100c02030d09050406080c101112070605061e0f040207030c171b0c01050403020d051009050c 72
    0x240b214084904050f19545000845c599200e03444000b0005a03652001884600740101620f1126801400071905c41c0c8010311150060000c40e54190344403080b9242171a01c4030000103034100c0d1404036556070400c00c09040b006440b00300c1c0c2400d048030b0081c4c0700c18088400c000754056040c001c40c00f03020240924402546500700b1520038814140c02042c07014005481000e41c5c0786e40800300c51003941e440c000a0840c0384101c3d40a589a94002c1d81405000200c40c0f110703500174451410b0360000c940401031320340e030f860a855039096090380140c0c00005070301d034103070301240151402c489000c8440155401d020303c42140f1503c40d07100340c00880c0e41d01d940d40284919130030540400070111138164030740c644141d824000196295070060196104940003d01102058414081110000d0f880088000f10040e021210012600420404030500d0004184e0744283e8800041c03800d00e001068541d180340034110703001e12114483e1103030192454402c1c0040500c0030803c51241c3c42589000d28060800d0328501c208000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469990278 1250 469989028 469989031
    0x806010f09050603061e0a09051807080a020913050607080103031e0917010608030f0c06061c0605042307050f030102070809040902121203090106050d03170604020409090f050105 78
    0x40c20400001001d000b291a12800c517038004004980e0182d00360041403103000a01456070595422680024001862031080c6c1c1009000b08080c0c000343e0080072540728141d51710303901ca00c980c01e81640300350071030005820b1503981540c201038040861102c1d209952100f41c5011000e80b400000141c8001c010020306a000c0c106000d40c00131114403d03901031401c0310040c4443c65501a00c8880032140c0240c44c0651004d5210703000602c0544140d03601c540050003900c82e25004020709035018002e25000510781d203421040d5001521600315441d89051050700c41c04020840204211900c0100d4050000061a40240d00c484841e40030002d007500d038100400c0c4030704a005100600c0c0660300510100001420072816a040800e040d80c00284800ba140002011410462004190ba00503641e11a18414448004600c10b001c000c0003030245666a1003407205007035a4900103400500c0c041c00140c10032001c980400d03045580203002500386500c50009100321600c103101120b04200c010308034000c011080c041d65 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469991528 1250 469990278 469990307
    0x20c0f062508123909040b03010e01090501090204060f0806070309110d080903010e030405031009020402130e010306051005090a0f090b01080d090905010f031202070b0f0403210e011b05010903080601 87
    0x255013404090107451960b009809180d403056482d02142c54842c2c82c01d5110340c60400e5520000d210780c075254104280206082c0342d081e4006da04000700070541c2c0440c098001d003143c00c0b1900400709035440140c12001400d0520048440040d00c000d418465501c64007000851405454000d0343e441400381010300311a50074441030882e4006001c104101da40100d00e01d032801d00220310201d075480c01c500c0002d0091083d4100c0540100000c50003141140d05001030030f050b42e1240b201041143c4503114407000401c3d052196991148034940020302041d03880d040307540900f0491030041096001a610b1042c00703142600040c44036404440d0205039282e00411510040c04103400801c295410b0600c001c0000c180c40c0405000011031300c980e580b0b418807c20061000f000240006502c461a16078031500312b510900c800d072011842480020462204800600c4402200b5214028141c08a46c01076400007190920750f2107100342c0755010808503e082c020001060f200c0d5403214540e107008400500b580d002d00310349 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469992778 1250 469991528 469991611
    0xc0210051c05040b0115050c03130f0608060906061c0606270e1b0408030712111506040c090513090512070312110c0d020c0f06250812 59
    0xb804041003040842c13a064644055040c0f90f02401d10344180e64503c160300001000d40b00000384160044400f0442c1c0702503c000700c83ca5502c15a0f01e40301100d20040955081e41d00440010110343d25181440040100000d081010700f0070702054640041100d6080d4403180c003080c03803240c4c1041c100c8000c10060280b1174103120b40e02042030900a00b890389080081a1140c004200c050600c030084000007a038000304401804c90399218201c0c40c0801c0d44a03209010340300031599680d601c00d0f1411020602004800e81450449142d50b60b0720300700005010749030040c6043c4102e0000c0426680c0740c1881c6c001807000e14020108000c0030615116107445080d0a11419241042c00b04100113640b246d40e155100c0045803000c903c03805000c120355403600c40c20442103503500c01c80040141c02ca40104481e01901000c44d041d042c40c50322030041c0641880740e40c01103405000002000300c03010b442400c014032105e005810642c20010791070341e1080e030840d05850740713030a1a40f0128440e0f0502c200c002100222010481c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469994028 1250 469992778 469992781
    0x109050a1e0b011502010213080f07060f0e130e03180906040207020105030a0207020a0b0a0f09470705030c0c010201090312230c040603060f061e0c0210051c05 70
    0x882c05600c800600400c0d20741c0034a509280c008034402d40650742984441303203901c0c1c2295610314105641d00858103010b0050301848000003030307007030283ca80c010800c400d40e21400042d4403241b04210484801c1d101c07210850341ea881d1642400c5908001801d000c00340d0b4003120040c030300801c2c01c115110f0341c0241043e2245004109400041c2d03030101c1980e802090f042400340c0c89002034070004020701c03241c2d00900110000800c80200040c1e21003200e80c868541034440380501c42e113408158420394182e107054210503082c0151401c0f034088401d049a852281c0152074400400c000c6030909180c2e0000c01c003038500d90300c081040c2100a100780030692000030240003c00096034550b80180414000c14104031800ba80c6007036869140c0e004141c01264102c50342109551490b000d04841d02980082c0a408000703403500c400891515008220241903856588815127161203543c00b4a00d8804043c40340009c010148d580d20006072107415881042c100302c6d0300e0307180c0c079903100e0421503480c01010241714841500f401c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469995278 1250 469994028 469994033
    0x110111041a041214030c060a0209040e30090a06110f0a030c080a1707020102030a15032006071403120601030915111201080606010206131101030513050109050a1e 71
    0x440c3c46103407640c071138010310310082c00790001401c5004881040c0c0c01800b84074200000180e0650040070800c1e0120740400c800015101065520302450014030a01e181e8a0414406d011550300f86038140b140100c10300e4603212180d004a8240051603010a0101c1e003500015202003e040c0300711100c90345842c0003001c00802c242c400400da120110700261802600003141c501441c40345020040e00309020b03280014071300b41850024000c2d0b00c100ca03044026882c0c001c00e900c1145040c100001140e0f0400c4502c800006162030554005444103400e96021320108580f00008181c80940003034540804047d5440e0703840081103261407003004101c1b5041510f004000304c0040c4410300e9034141c8c19641100000ea0b5001d48118044030321131144845100c001c11000000c41190014100d4414002a82580c1c0c091b02d0b2000784441440203060b00601480c00c8500691440d4480d60160b540a038489001074815a00c603201c16003141c4443c0c5040c1d58540001c15090705100c00c456612580541108400b41c414510f034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469996528 1250 469995278 469995299
    0x4060e13080f0c190c060c02030309090a060302150406030501060309080d05070516060906200d0b0315041220030a080606070b011d0601020309180403110111041a04 72
    0x628000c040640224020701c60040c0c05041d0f451066030340c000c55448000d41c0618412240d040c100403240c0104001d000300c2e04a100d0340d031002c40c96038042c4c000c5080000140400c0150800140005a407683d14000000540d4862818054000d648105241d0300c5081000003000e641d0b0582005c2c0915062070900710010f9085001c9803240d0540a800180341c3e124103004540d81d1080038001d4010102d603914080c02e000041e842002c0243c442c003010449400c030160405c8a08181c5594880061410700200700030070010740100c24187d10050680b1040616042081c8074640c00b80c90940350321140c410a12009500310010b0192102c0003000e040b007c0301c5600204d40e80780b00340d403990300030030401d540425095140d44065a41e100e510441020880d030710b030011401010540040b11400c0b100b250081400f0394004001c0b65080c04014101050f91140c580941c504500042c104908010b00d10510340c1c0c03442428451005180040c1941503941d52505502c001e0240448076040070719801000200000200f6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469997778 1250 469996528 469996561
    0x16090b0f031008030307090f05100c081c1506020105090c210a021807020601060306030c030f0f1a1506040803041a0403060203040312050c03090606191a030604060e 72
    0x880d01901e07926590300441a90b409041e9001800c02e01c030200910103c16001100c4d0015600410a09003400c0c4e6100b04000c0c45c0001c524480c004510825415400300e4a10781c000d2417000040c64030704206004003011182107d070080c3c1121440d04400100f445031030760a01809030030003d860014450102008000303109000752441480b5200601e6030880803540050100903045c54000f400c20b001c402203051143e0540070104d40240042c0038400010403154000e203e820706494004000c1c1c0c50840c00c5640b245842c1d6660102540c0000403110180c2c0010a82c0c000c05108040881e542c1c100c90828041036050600300400d140d1013004148010b1064050001c29502140c607450303a03581000c1e80c66120884584a150409400f181c000000c100905402c0342c1d42240c83c08003071008100c69079610090031103c0c04183d60b0b14080342c1044002c01c03510b203800d800b404107690102400c1c4003942d98442607031800034811001000da031070000c0100901c0d803816101d414010038001210104501c0c01c0003000070310a11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469999028 1250 469997778 469997797
    0x15010f0605091e0301060f0e01142b02151603030f0227060405031608060105010f021b0109120302010b100816180e01080a110312040308030c070605010303050316090b 73
    0x1c00382c415042d0b40940003d40100b60410640e0000c544482035083d0210090052803c0d01c0c0444030202b80d2800c1c030313541d86e45668607008102410000204107a4140c030615403016a400f08800000301040120751005103584036660186e0403c00c0803602d805815a4102d200c40b184032441440640510715402140903445100d00c950799080c10a1600040c000340219000b86030141300d021010002012255070940642d03401004403a0240e1343c0e00300440c2c0500d134031a000b00058201d10f0204c9810700c240c00c5032030705011050404801e60764503a03240720141140c801050700144e4444411102c00c1c100702540c0e4050007071a140840e80e130721f01040541601400b81c1c0300f02080020074032601010b5034001d03c400d8064620f1504000495035151619030f95600c1c1010305940710f00900750281442d28001854a0a10b524101d109040074070355241e41d401504004c0801003c02010000e810001d102da100b410302852013520707003540780c1c20109a075004140c041d9200006101c02c203001070002441000c1a0303105082d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470000278 1250 469999028 469999069
    0x60a0c0509120312130b090d09090c02010b100f080a051006210c080f0604062105010608030310030311011401150e09070207170102030c0a0c0302030c15010f060509 72
    0x40d0034003040c91070f42c440c0881828901c0005814016a0200034010360700e5140070300303000f1403142c0342d2807111522501c0340341ca41d10114800b4001040421040e411103500304000340000550510090089002d2050004526000130240c403602d81c1c285400c0700c400e90300306102d0182001035162900300c0c2010f014050196200303001c2c01d4800c407000c110400b0204d4500804d842cec002c1c00b0710b420174000501061001e03100d1103036151454001801600b46885454203c61091030705c40032084240302100241d139032000096449540b1901c01003031031403080006602454410b4049840d036455424010b010280c0342405240a03418400c091003010102c00020b8159001d8001050501d044000b0569400c02041c854941040c0300300100f0040c0c0d038021800c907048031407200056000c082c014520794205d02c0201e818801c4a54103000c00090540315003c60780e1000e110340110b03482c2c0203030301c1301c06840c1501c0c02c030118105041d0240140801c01e03507007040d20010411400c0c054105214040050820710388184c1c90b51818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470001528 1250 470000278 470000299
    0x9140108060d0c1d0f1005040506010203040b0c1c050a080411010516060c110304124137021507051c020d05030a02130b0406020f060a0c0509 62
    0x3030b66410845402c1580c08921254041d54440340c0c481603007070021071a01007000041c005800100400d0180c4c0c854610500200c940700d080504020040001405440c1144010700c00460360041c1c0d82e00401120301e01c44000c2106105203045000302031000c0380c60004000c01884240d500e50b0708900b426410907405100c5100703030200303440101c03198003c1c4014445000c4043e00b40e4000d012040d80045e2416503a951401a0007054181856a900c1148900010540070745038000c046149030484c80c0960490a0302c1000010940c45002548401d200c0c06000412004450a0039403008005041c18091501e200789007000c484180030400c280a101c4524940081d002c48508640c0d4010080c2c9041001080164681480d414101d582c1c0d054199807032001e07510290640000b500004411405000e5507070760f24699030f15210990081d40109040401140d038100c4c010608503516000340015043c01d07401801801070f00700c109807514002414000e0f4103440c11500e0220103500c141106c18014042e02e0b480f811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470002778 1250 470001528 470001541
    0x20301120b0421030f180203060f3105010c0503090c060c0c06033d0e0a0b0616020f060f04121401090305070501051807120c050d240204080604020409051f0608010c09140108 76
    0x1a102f254180302d041115111022520f038209441e000c51050140c402000381c08004003007070f00e40d03210a85001c410340e4000d0101107003600d00800102424015042502d42503440c5c440420b0483d007041e14a501c420031200000400603038400c200602c019010920011484009480c06126240c2c0c1e01844600c0280500010448904d54005201610001d4006035440c922070b41382c80300140078400b0417403180e00301d03441c8140f65141c4441500c0021000710f080d03a2078149868981d9a402070a401d04607941c0b9004d900c170b0f01c0c4a020030300c20030440f24001e4961070342e40c200703528285086410080980038594142003407411001d100146410aa030114040110000c1031400c0990266130f082c2c0c03003154400a01c24100b0104000142d100c3c0c03505003a80c104c003c1d003010588001e0268000ca01941401e9408500001e000d03281540052203924001c8042d1050041da0340d5104002060011007000c4450316003408100d180001d10a60030001d00c240303001225142010b603407480d021004442130b0704018410021651 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470004028 1250 470002778 470002801
    0xe010e040e0c0d140c0a03120e01090b040b03040b0c07030905330403050d0f02030306010c06020c1b011101060f29030702010c080a020301120b0421030f180203060f 72
    0x70380c101c00528442004030686400d04108425207028100f40c010b0505c10285414400000416603910002c0c118220001220440f0920301c1c407040c140c100541c901c0005402c0c042031000b80041c201074500d1381d9807494241041e40300c00354098214030404004020791008258800e4a1809444040b2400c8848080c0f1744c44922440960750740f840000c0b102248403261212408004004891280c420345e5440003c44105a0b0708866505541c2c0c096001000040e055606c00c0c0e0240742c1d16481040c0040c10406620421443d1103040c2001030702c4031002111011440d03030400c4100d500e2056000090040074100708103040b03d10510b100f9000925100e0400608410003241e8541c040c1300080c002584a10f0442c200078040c0c190784100c0d5001c10081000700701618010b0084a0696060b2100f4140505442d40c6480d15801d00800507244c490300b081d2540408450041d440d1000780250f5008118050b4180301c0400700c4141000c41c482c2110051500001130710040754883e4030030348510303070410240c2d111a0744a6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470005278 1250 470004028 470004043
    0x60a0b120c09040c180605071218030b0a1d07060504120f0618060f0c0801120311010203070e04060e0402010e1011191e030210200d09120e010e040e 65
    0xd80c02420071320780b46038450b03004510403c411142c012403140150346560507140d9103e903c0014007008540c90fa00031280b4019800b00c0c2d0080d640083c400c0e8072a036261140140941d003030742c0880c1c40a40380c1050200c2132200441968914803c20081e01d1190f2070000050143d204620074a06c410050075040710901c001b00c04540e500c960407403c10701c42c21440c0f42c00705441548214044441c0c0b80b415608541c809254824181a1182c6884100e083c2c1d0030315000507801c022000c811030820030f496007400070b13040084c0090360088000f9217400c902d06400c08100402d0b1103084d040000900024420000983c0c1e001d48101400b130310130760f2200d1407160051000c48a45a80c2e0f07a500743c8603c00c1030070b0212442c80c1030800044080c00f8002032001c44140d14045c4144c80c8448002400582c0130203006136540800703602c60002d032030304c00b0849030000c0300501260203280c10124440010f00e036200e0b401000e20450f10340c00c0c134040600c4c4c0f9100c4540c08142c4000f81001e50882c640600840d911400f00507111010440c80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470006528 1250 470005278 470005297
    0x106080615040920030609010911010503090109050106090c030c02010b0a0501030e030d0207080307030c02060402030d05030702030909190b060319020d0b030114070201060b16060b061b0a020306060a0b120c 90
    0x30b04055040e483d000c2c01c1c10304d0a0500078040d1169400042c5003c1d1b062141000fa1548403000030040c040301001140c141c0c001a041b500c0655a417000507001079000d10803a8010701e8000740205000058010160844900c90003a80640e41007003139032540b594440c0b007544e042d42c0003400c0004007060001102403071030040c0c10401c40f08910002e034000c2806400c10107180701e0308180e0b03170900900020840490300d41c0c1068078002d4056001102c403e1506015002565201075070340304807400c00500f200007070f5882c10700351a60840300b8584040c0c4464070249006680d4618002e40c0c0c16450340c10070440034000c16190741044096558041b8100c0d21011142e04030f5001c0c5000100284105640b07003100190400d0103440c031401540c40c000002400c410700600f80c1da00b6440d10404070740006403e49800e00a48450b000d10f690180082040202c0c02c0c4040580340210130001c002040000281e2040c5494010081c00451240f0fa0206080110341c0e1400200c61948401102801d82500d81074400d200d10700851802 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470007778 1250 470006528 470006543
    0x11416090f09060f0902210c09040c0905040609111602131e0c02120f070507080d0801060e0d020a090903020106051f080a270503040e011401030e01060806150409 71
    0x146680b80341d0005001d03901c0400c00c0384500e83e510000306040784100c4200c50210000c0c1e003405150182c08a4050381d104001e01d0a2a144c441d0100000341100c60030000708011130540402440a400e0034410603018140f0201d042010f0401084080380901440c070301030500c840e03894004000c540300c00c100d51140040c03000080c0941d640821200072902210448003168900d1310010b250454800076922102c000c05103c803c0c03425603810804510303075015101c269168828400000b82142040025a8514000d0760f00c0b0101175050090040440082903811482801c11003494000b507501d002509040342d1034001c0010f13400085180507405000316600850788041b1410700882c0f0a1802c44007030682d441d4598400c5510b6272404c40c800e003107170f11103041624001e4645200030281820a0003d009403400781080740e040c41c1d51102c20549401003608404004240740c03240d9140e0303580600440c1203054000c002840000d0400c11003070760b50500100741c011201c0068800c503920b61074a46c045c1126640001c0d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470009028 1250 470007778 470007809
    0xc0703150608010b09070906050c030f0c01020304050708010e0705060d0e0a05070f060314162c0915090a0f0905030c010204290f07060b1008041401141609 68
    0x21608010a0244980c1080d54240842c2107010f00d170602c1c00612402c416216900020300703214040355160007040702c4112501c4201b10326401c6000c1d003000b50480d480110700250341e03440c0a10f0020f0034115142e01440090b81402e4003c503080d00040b43c11811f5440540d600c9884189521900020303050003400b041c018024040b8000511070b02007040001c3c0c4030500ba501000707a58464088003100e00c21884031510310703243c602060040d5492003241c00c50a10a02c0c0c9214018402350a02c412010804044000500f480c00c2d03c0a0b241440600300d64000f0030703180806510840007000c85e0342c2c0030004100b112034135074401001d204034455921040f040b1b60440105ca03260b011941526000354407034091908040c1441003048072082c00102240507501180310302d1070405005002410301034020031070440b0110b80381d01c50410303c4d4235000d8104000d102c043d030b40d60581d41024100b4210106080c0c2650425034107100e820303042c02001c40030054015205040b40303140136006640c00c9524404940000b07030030728901c1c41e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470010278 1250 470009028 470009063
    0x5100905150a120b030f070e01090606050c0a140f030a0305011712120603010b060f0a080c130e09150c030906060a0f0308090d020a060909050c0304030804080c0703 72
    0x2440000e4400984045001c4050300c01554454054072000000180c20801c01e00100000d0360488482c00034007800f10780d4401d4200c2c0007541450426004030030300310300d03410041080c0e00160045000500745401e2132441c000a03450420303118858110054014150400d620402180800882074096590804d8a0f120800100020003a05085c420845034030350228070000a0940896080540201d00980c0c515000580700300c80010740b00102800c0d1b16540c3c0321010801038a808004180e01c071055080665105000440a0544000030302082034140c014842210f84c150498002c009441c070030961960b4075500e41c1407551800000320a0140d140c21007170f041c0880001e10001541c05082c140042d5007660384c07507105000080049100c0d01c050f12034440360405c00300d01d84030010550200003411a5841ea8104e0300404c4401e011a070002d00000c0c0c981c24108044c234410705c50650480d8030440b200c0d1541c101624010216000a400582041800640350084c0281000050011503000340104130300c11300030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470011528 1250 470010278 470010287
    0x24020f09030c090f0412120606120e01092f060a020f190b04060c0302070212030a1b080306010521100f050306090d1b17070c05030f03040b030604060510 67
    0x416074000c2c0318840c00c4034030703501d0043c54a40c800c0345082001c25030303666039455190421100704030031024000903d103020800c501d1401641c2c007400300768a550b0381040c080c03d0010111903407004600210392411214030001066170303401540f0759110400c0d050b290307000000351701c01000d0700454076580140005101c206048c1c0202c2c1c40c101c80d400583c01d45040000c580c450700500320b1007101c018241103100c000130740041e5895000d01c411200f180350040c00c10405601007144066400629115a030001c2020b280140d40300241103a903d01084440f018505299039000f0140005400d0605200e0007050711100d03000821202d00403003d8116540610342001d109000240400d070180b20700c00c542684002c0303030342e0030000f43c0c2c140100d9100000340603015070301404413a50300303d0112641c401204034070001c0214405a44000c04541c40e0080749981c1c2c41c2e80c3c1340c103840c584019441507000c0d4209421244c4682c0c2c01209590446030200b4000785e80340d0350718001074010180794210070762000c007a9042042e4207901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470012778 1250 470011528 470011537
    0x5040f120204050907030b04020607110306090a050d05070317041a0f040605241909060306020c060709030b0703020306040225050c010905150c0708120c10090201080424020f 76
    0x1d55041103d92280c5a04a440f44024000500100c020b0340119005061010003031140c18003580900c00101c805500003404c1c048107940143d804d51214079103406000d828084198a02d1142c10203500d0b01442c0c1d41c0290004880388405240d60b044000045c0a2000d074010341c0d41034030b18041c500c480d18900003200010741c6d4003c2d1419545d0a240500068800c60203080f61800803901c000803071542da0180081148800d034909007040300c03100c0344d04001a00300703417801228060362080c1400350311103000041491a1400c000d00c0a000c001ca0079804001144041881d04c2e0040340c03c5c940980d0341d40d00c40010501a10510041c0e08061858845480c8005001d130000400b040c03080c421f071003144000b8001166046001d029895100c507081c0940c84030a41968018680030b00c802050710070341d95031038141606028000d07124004c44200060f0541e240c10f01030044a81107903552034100122032036500001e043c00b1000f1b0005050301641503116240c0c10007aa014020382ea0021303030540d540c00c000b03081150b070742cdc00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470014028 1250 470012778 470012783
    0x3090a0606081504140a02040c030c031103060d080a1407152f1612080106080a15051003020903070305010f0e0a0203120703110703110109240f05040f12 67
    0xc0c1c4500410525404503450300300707403840b881d1103800361250340700c5000724107202c001040c40d0301c04e0381c0034503006071142e0041740f20480e200e48000039601d01001c40a403c0e12121090344d00360306410010485144e0b2000c1a10713106a03040b048494807402c072080c065a40303180c44031006044c5d80022a8140401c540024982c14941c64504140a048a03010545103116015012482c410b0b0000f502611303802540b801a1a8405a02ca506004001d141d151007114a90414855000800e00801809082d8001c00d18941083c5000740c20007189200020314211a5010b009051213605003100341c824840c842d4040e5404107100400360303404240d403498021700a141220005190034104881e4460790140415040801d0381c0140c090070072a012844c4c40e050f190b0250004405005000726410440b550410030702e40070318440c2260020080b07800c40050072500d4290301c11a52150840c0480c21204110210b03c030340c405550030b14045044503c42e040c4c0b42401540c100322211641c000b070008044250b1109119850f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470015278 1250 470014028 470014031
    0x90d09080102090a060503070c0803190c051c0b180f01080106230d030329090a050411151c0b15030402062d0307020d0f0905010e04050411040203090a06 67
    0x40e036030603055090740100b244080d4001c01c442e804003d80f0313006000855024507075140c01d1400d0b00d0b490f9a03917050f50b0070036220241c00e43c09210400310406070710303c03d20f450a8000d080840c00d103081d0343c3c01001007180c0c1f100103c9644d43c48a00b51140c603125078a07910145803201c0030035441450207800c5040840c0c024400c00c003c640c00c00400040030708d1407012114018034240c82591005085c5014450420030701c410032401c01d070b17442200c5801082104181e1801c41c06540543c1ca00a488008000d17203644080c0180c2100723854881440000303107070b850b04804184000d681550500b2040a80d0703007164000c1c001141404028410130b640e2103601039101c5800341e08110351b10b1100c0d210000740084240001c42d0b00940100381001906c091402004c0c5400000d5031507000021000d2090034142920342095a984d400750340203000b0300c00030302d800003851500c0700003a10740049500c0c50b080c0000c19000c800c04005024607625400709040c82500c0f8210500200058415596410f005011a0b692440000b045e549513 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470016528 1250 470015278 470015297
    0x13020d05011a0d150b0a050a080c040b070b040201021f06051f08010506070f061b1215060f0c0b0403020706080a0b0d1104021303110a05061611010c0b090d 68
    0x5815802c003a040344008901e9418240f109020360010094211030401902102e03100049074151113005280b01c449a0b038031a501d856a030400a45030710720107080700c070440d1400d00040c498541c1c6081902e080942101e11100c50b601c1d20700060b030800e0040030441400019211110350070700d10312340080044607825160811000d801c201da0000c20381c0c0ca50340000c0028078500040141c1c0c602400030f801c48600038105914164a241d903807104551040708001d002d0081c28512240c0c4a0700258031007180c0800d00c0060101c80903414561001d00c0e1180142003e006040b0700d002a441e2040c401a00a10741c884103503400c078185800c019544840341c2c41008001426040012505206809401451040034042000b00030f0603689500a090b865031516410603803e0003040a004030358101240294042d2060207003a0403000b00b804440031950704400d000c0d0781c040001e1035240c207425110341d40759504480030700c00d24268000120303065410f40340082d14081c7c00c5800d201072840c1c003007002d00c03455800e13072640c0c81e80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470017778 1250 470016528 470016539
    0x60714031804150e06130f0b04050105120a080a1103030103080c0d020f060f061203180a06170103140703050717010609050105010f03091509050102090f09010e01140f13020d0501 78
    0x7914403c0502a0501c80e16003010018460341c1460503410601c0100702c4d04110b804010803008480707100d640c0a4107980c56940c1d1306840c1c200307440b509001d00f0003030703a002c0c10b40726058010950b11401c20f140100109400103009070305a1040101c111540005005daa66a50352400c280300c1c40d8001003016241402480490f16045000160400d01010024042c00c400d40d122680800c0914008110941000c80350740703c0758003080144000e0005c4400300b0250b244400a080600c443c1e207090ba0000401e126000400070301c2c140070800c4150440ea480b001400465008a10250401030580d0000f0640c5c4a0303448042001a903801c3d0180e29040c40300d0003001500c0da640015407d46000b071081a01150700950110412403203600142c601b54016032103c0000006032000d0411074401082c1981e0b26580498038401c60310302028034200c041d804a80500c1e555041c503a440003280c0c010300ca1039601c44003060003031109072160b2001e1040310400411080c4007014002420011f0350010205445051400300003155 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470019028 1250 470017778 470017781
    0x403060c0c0b0c03040f021017070206090c120106030215030403170f15010c120c0507150906230a0e040c030e0d1d0909030a080708061509060714031804 67
    0x7016004040122140c848080004803030703001601c10365281c5540254003025071078440182200e812181d0350503410003050b0000d210720b284007400c154210340001090140c1000001520003464004541c10b00004285614590040420758030087d080090025404200541d13040510b02c135a001c1d440b030681c00e0032402c031141c2c49604219215030348041500045034113000c0b1426035022039001814010146810794580c0b042811183e0740000010b0248035405080040134442c40000701404009000210280c60000c1c117020306c1800f683c0c04000450203640480300664050501108168a030642c0e40e07848200300a20321070f843d2055600a40c00d003480107604601c2442000003488110000d403086810260303044602c2c8100e11803510f83d09009540b0001c6964404034250f008200e00001582d807034500d200041c00740034004203803909000102041182d01d803110341500d01400710500f509030b035856500340001d04c54007540e04050107244200101c09044c0380000004d1803071341502e4050040e2107100d1400c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470020278 1250 470019028 470019047
    0x20601060c030c03050904020c150603010e0102070b010b0a0c0c08061b030708040204150e010902180a0b03040807060615031e0b0f1309050604080a0e15120a020c0a080403060c 77
    0x800085031060100086449117000e0140007200500241c50720280350811860a01c925aa43c04515030b21420b005241c507091041d1040031880e0700084d4206601c41d2500098040c0503c00c1380031080d0f0001780d600360244516100e0032080da1002000000540b1030b400d907030342e4a40807500340070351500034424440021214000d50340f05001d203a071038031100d0b92240d00744000741c90b07441100c040d52601c02c2404270300c080d00007a83c81c0c042c190241b0016143d04515849021030840c48041900805410005000d00c4000208907644581c0190710540c0d00c25203441d040d002414542d010f0791011000f06820240380d036040d002620303801a03a40c4819900040003610100311001c0c1c006941c1c0c4140d0070a200c1c400703414600303030401305001c1441000079000c20685469051240c00c443c11145040c00248000d407050b0040a8072802200a0301e1100c0742d90b07200c02881849104000c11354418000d1503002802007440303038040380d06005100041e07034040704d070f82e140244113034001d800116406800d00d4050070595200b040d240e03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470021528 1250 470020278 470020283
    0xb0f060c030d0c120e0a1b05010c0f0206160b060108010f0f03030e030c04021c15051005031003080a0f11030306030a02270c030610020109020f01140408071401020601060c 75
    0x4528180050101100030f22550210f0814003081141c840e1941032a4815482d40c156610050305008055181c008144d54454110811440036814244100c0c2d83c0310b00742d00f000d10303408074120300800818000110740e4040c00202d40403c41c0b01c0b40070301c0b04005041e0703550350140900781c980c0000c690301c84410550000c01401408000c020549040010a224210041c0c68500140c1660700008001010800342d1b804004c1a103000599218810274a104510031140381041d14034206900d1400e0600189170b880070b00c0c1c607003070401c54048041080743c1c3c0401c0c0140000c641c401901039580004910140031880406d0300c800c0415507000b00c2d00e030f8803280402200d11818004000c0d000000855080040a00304001800c034901c00d03c0c00540700034240340d80c0081c020b04003003003c0c58803445d2010030840514842c1e501d039011641001c80e59401a1103802042a80305070908284241c486000c10018250203642d000c1c81d000d100f041000255025401c0c905007044000782e00341c03141c41c1c0c1c0b10700f4203881040c550300c0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470022778 1250 470021528 470021533
    0xe0606031c0f0302041a0913060f030807020f040609051f03050d05132111010201140a0209060d11190c12121b020d031505030a06020a1709010b0f060c 66
    0x2501841c921501200490300014100141015100c1c0d540400c2c0d0010304400d00c400d42800901e0340070600d4822403419010780d80f2a070901c289418244800e140304200d100042c20030201144050456507030344085036030307503101500805c50240d465040314080c02e429503a1005d1a10b410f000b2910080401c40c0100540c0c2e0008002d2070041400c0b4030882d920740c40f070101c0ca03034003802d404404565440522140141d450328850324a00c0111176007442c9040c601c5140f00c00e8103682c50306403006410700010001e0b5502c4152a580181c5652422011031034500c14602c9041209103403244200241400ca0064000164001c407841203503010f61106913258081888081c10707401500300320341c465620070f41d4021981d994202c00420703501c00000ca850f0110404014503005030300421180c8081942c0b44c03096a004990300040041418079150110b521102422009043c00d900043c1d8490524000c0300c10960703150968044101c03610f0a4402c3c140200600c40c0410300c1030740c019a00c0c1e041c1e4a8a0425184a00c440502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470024028 1250 470022778 470022823
    0x13020102071403010e060f0702071d06010f0e03070308040e0a020307050d0203060d080a020a03030b1504030f050c0d0c030308090102130528090b0a0911031b040b030a0e060603 77
    0xc28100c1000b0000b0554550340715040314502c100c00784100c0f405400c0005000030345041000c0b0290070400750360000000c581e50a8400101c2880e0f04030841d4101c0c000382820000440391010886004086a08040d01480341a40010800481d50006d00031184000c041081503200d181c1405c040e48001ea5040c00043d000f4005114a00507a500079504070341c00031300c4604008101c1e51101c1460300a8040c490260b0400c1c4160700a254250048503846a811100d490092200c117025607010300407804003801d00c0102e4901d4004100c0c04210042543c0b90060032066021580d180c0305460268a00044000a801c10081920780c1014000e44e1140c488400b4015075542c101010320440b008420032003410ba0107800703ca2000511290303030700c40180c8442c0c00701250000c00c2c801445000000d680c845803c0364540011590810400415aa008688524520680e000300c407807240c024051070308040800000041880f12060095010081e0307080358806690003039841e081015103441c500100d4581e80805000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470025278 1250 470024028 470024039
    0x627140316080f09030a1505060108190908120a150803070317130b0405011a0303091e011101150509060f0d15111207020601081c03020a12050f0106081302010207 71
    0x180c482607042e11212810300030386400286c070f881106e150a488502e611011100800358074060150b12190a08007030b40c85041c0b42c8524550b09004100e03002c0555a00e8a0300341c06c014429045401a8410002d17000750f50920001d50300c020000d101d401c4143c0c0151100c001003640b03011080e9004190180c40f032142069a400c002d9061f00e000a0664041d81c24050f0144005a150344190380164003030b4000007201401c040c07000c00703e0480b4011640c8240e106116070602c2c0e80d506036404c07850100e0000004100004000103039012400603480c00000c0d42003e2007001003440a00b0000c04135081101c03260455103501e0148020b513000c1c0c6030380c0c940184c08043c001000c500081d10310580035015140004010a9413594101d140c1c00035041c9d004000d1040b400c5c000c0d4280d0420900f80581154806000d08144803144408820000403a0b2401d2540100b01071048030b008400d01840000d403090140401d150202e12040c885009000c1c59010034001d030040341c0d04440d80f200443d40c0e564180c005240e540d081a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470026528 1250 470025278 470025293
    0x42a140307120e0303070908210912010b060706050a0b0103060501050a0f02030417030c01110a0f08190207030809280602030a23070e04150b070627140316 68
    0x2003a018a481d03d40c83e441d00304200c2000254480c4e01c1641d10079809034100342c80705062410501200d604202400c80e00c42d1080029801c03a10300c40000c503400d181c110700c1d46601c103001d4004030900751f5220a0100e01d00e020f002258000510031005aa42000300c2c1c6041001501280d4481c0105400204144034526a49026000141c1c61000500441c1c2c10182d90300014594000b6590401c122600003055540d00d0385400d00980781a2250801c090b400c00303103010b00040c0b032086044848000c0102d450301007040240340304209000c48003032040555540300a810060312184064a2942480c480c000441c2030030b011808400d542a54413509554150780e0350380303501d0041e40000c3c0c1921081a0350b200349502c2d03100703003204041c07041821109421103842c15150103009800c03050461401141400144580a640380d507d00050300c4803261000d8440840d400c01200900003641010319110203140900c41117a0440c280780842803081900390316a407025009952280500000e0300c0755100d88800410004881 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470027778 1250 470026528 470026547
    0xd051204060b031212010503010203070e0d150f140f010f14120a060605130204050901050607030c050d090f06090f09020705030c0607030605120a0b040b060303040302042a140307 78
    0xd218049112002d0800090034610070750f0b00840b40307020001e0804441100a040c5a0043c10110000c41c198608268040c0500030301c03496141c4a0680512440b003007140040503c103520303014500c01c12010049000f003600030f1080b80641400c02c8861000079074020902c03002503042c4d030b41c6142041101032408410400360200c0710031080d80445890080e0798840810030101e683c80b8000c3c80041205860705003840403122074120380390100b07401040240140e0310340303500c03240c111042a520150b459a95003801c642c8030502d00e00003041070141c1c0d020182e0156100a0040513501045ca00d0a821a80d910064682e040300780700740c035400801d65104111070f12482c0e0141941a000380305891a000c50621042e0400004423584000309554100074411424a03201c0c031707900310303445200602c0001400e4440c100245001000105440d4440b00001e4168030180b003540c00444c2d01801c1400342d099142004214451090314030310440d00d0749200407254921a071a0603034140703a40c0d00c1d42461038035081011103071200c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470029028 1250 470027778 470027783
    0x6020310080a1a09210703090e0403021504030516050c0405090c031b010e0a0602150106110604020409060605061303020909210702010c0c0b0d0e0d090b03061c03200d051204 76
    0x510f05d42042100e04040207a0700c010914000700c2c2d48008624003d400300300160041d0201d0f040780d50030040003d40009650b0101c48901e100710340d4543d507a02c2c0403115445206200441141c4102d2440100070300060022149642100c040c031095840010b040c1e0741e014a44001945070784102c0304071840031403003c4808091070062500100311101d00c00030414030744083d48414010b0784105988044030212100484c0503000c03928080f00c9800c03607000100c2d910b42d000350020b0f22640da203035424010800198031020041070060201c60b100c4c1e20b40d00f24581030000e244400d0380580544800524100404a1004018800f5071001d4001c0040384015003400d400c1201e08905100e4140ca060b40401c286448200c010800c0d0303406075a4803241014004240ca003140c1800e201e903404107004601c880d410181010030b940c00081980d0b00e9548100002d00c840303420750003211040c009010008241a4004c0610148001e644a45042141c600c0342a5645908400c44503000031400d0168040070b0901c44c0215401c0760 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470030278 1250 470029028 470029033
    0x90303040e0709140109060807030b1909060305070e090304180902090f0610080f0c0c0c041112130b073b1201200703050409060306020310080a1a09 65
    0x140c4030000740c00030181c20b544a401103000c5000401445500c00d0b20151005801c0c078010f403405280c005e0103407039841c010301b1442c203150b240d03040c2c424181c41f14040060394280703000100c9191940c0751140c100400b0030380816501802045400b2070900d5070481d12502810003600258a0b02c1e00c0c0100e078030801e0f182d00c40c2c0280d0326903d6031030f420b0250340c0756031f281c2d0f005403805845401e650405608001c014881c07071203001e0520240c0341c01c110480b230045030141d5200d200c6507800f07680c84040021a5003040c40820481e907115142298140320071101078040d03d144880d0f5510011766882c0c60918841104102d803000f410400440300140381d0b207108042c00603001500110506490b1300500c3d0b84a500d0b0400124100d064000c0342e04510b1500d030540c070085452856200030841403a124000741b4400c01070810b49070803500e0001e114001c040c8540100c400410000404002d00c2d0349034a4040082e6009440040500402c0711010a0305034000c1241c20040f41d0008490343d403400440c03c499625900140301003180d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470031528 1250 470030278 470030287
    0xf03040f0c08011a01110a020411090402030103060b10090b0403080a111504171312080f0f030405010605150a030515060c0a0605010e070c03211a0f0108060d0602090303 74
    0x892140751400034082c000d0001c9000b440c2d156001e000f0a00300742015041109001104000c4d182c01b00d11500016010f0b80d0100c2d180500309903e103414411305500c0380d000b61002000000303110040d0f108800104003100e0110240300a45804c0b2a84d25003409108204542040b080001035101001020000c601d41841070721568995045800c010958001c25086030303401c0c0400041109c00d000154104104601c0d05013042040c00031402035001500800103181600360004050103140000c0c0c0c0d407140c144551240d541d4040c03501507846134109035800caa0540c04c2c00c001103100e15200500c801100949a502810020800002ca0160801601c00380001040041030a0243c03944801011250b00761030050240103014035000c412588140c1c0702084000b03100d000c2c40703012036106a426804642504e05507002c02c2041400c000d205203480000e42c2114508084d0b20207880d11411040e02c06a41103034102480d014480064030481d408541566009074205483e81c0000d0190f80600310000b00601100e040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470032778 1250 470031528 470031533
    0xb0a0905040608030901031514040f0e070807080601090911040c030f050a0902121b010f0909060e0103050f0f07051504080a030530042d030906020706020705060f03040f 74
    0x8994043d007103c112508001210081543c0500031380c100034011000c1c04401500d00314400c0d01240c01108024825511810020305001880c1c1200305640c03d020143d40481d565003001c60307590034071841084d0441c0102000090b180c690f510a075800075070003240012084411008010003050300a03006424580c1e2000707494107159030347c8603080c4120b01c0f500300000c4400b024010000606043c401c0c0001d02e6001e1080300715021303003030464452109801e0a000104449122702580c1c4000c0c10307004100c00904c3c090b0009040301528042e141228002c03401e82d141c00c070303a6a40b410384a10303d010203a410f0364041c040400503410126003000080c01c2c0390500b14209901ea443d12410020301c4d01007038001900214140325050b000c1d0094001e45809192550f060048455000308240b00061010380124050300e181007410301240d40340c404c1d02c01600100303509182c892401805000882c02054014810302101240f280d00000301403080e02c500410035402c256040700b040001d070b0720080049841d1030510068000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470034028 1250 470032778 470032781
    0x50f01060609081213051915020607030c17060f011101050a020304030e0a0608190f052401030b06040302090a0605060a0302041a030f04020f04110a1701080f06010b0a090504 76
    0x40c1c0308650303418641c0c42c58844a0382c5400444210400500c404005140d10024075814130710444500703071f0700b0714401c880c048455a400c3c3c41c1030f80726038681c1d600c02d4804080a41c0c0400d0a501c80d00180e141089002403400c001c8900e40e24040c01301c0c07044a00c0c50081030407403812807100c1c03410300e00515054041d0741d0f010540c6800e4400943c0c110001540210901c400c25411055400040b0b85c10f0741d40c0c0c0c0344146090380041280d04042c280e03140300407803e8003e8000001d0707a0000006c1e030a65440900072030500c04254000246000b00c44801e50a80050f0045150b2003400340d518511030052009082500307617001c02540d541d0141082c3d510640e10703840000c0540b030322006440c2002d603d480041e251403501008408000100f12070b407030728420410402c1015000b1a09075500550140d0300c003c000c03034825000c10001c0c0f800c0701076403c5420020800e2110340d540b010303052000f50b440c0c140340e440590380d4448c5140e840000c00c0042c040c0b40c21080c0140040071002003c2c0484030f2191503e10402a902d070701240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470035278 1250 470034028 470034041
    0xf120106080a0b0901020c0d0324060f030b030303060310050c13060804060c08010b0d150b0412060e0307050c0127031a060d080d110d1b0807020a03020a060504050f01 73
    0x30150b04030a140c0c00c103004a6100c425440804040203516040245413503580b13603902111000c0c1410f80d2005616803205030801000420000095030810207900c40b00080e1401031132640b80d10021b800d05081c1d0465060101c00d503401140c01a008284107021011028058140100410702c4008280180c90400a02d084031000812480d101c1e86140e0410742012420303a888010000c0c244920000100700c5c04006404a40082c8001c000014010301088403403050400301e5071020304034840128021072003030069107a02030107074484c44042180b00d4403003040c0e81e2240030321070f005010307070300001540305080d400b56004c0061041105a60450700300c9201440d0004201d40c0c10599450200d0540040c64100340132003182c00010803510358000c111a0740c0c5001483c400c42520115081c0c51341040b0010342224029148418400e040c180011018500314585901022410800181c140808110700c80e0001c1101c40d10540c250340075107030000c8961520300141c04042c000b1603091185c0030720324000e50070038032428 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470036528 1250 470035278 470035289
    0xd050a1107090e120a08130813270e150405070e010b0d0606030e0c0111030c120702012319090902030f090601080d0507232b050403080304020f120106 66
    0x501001000744044ca00301d00c401c2d1441d402481088031400d400d42000700345911020301940781c1c2d11000149010348080c007840109511158000c4008120361500c81400380d440c6460602102502e445030384208142c07500c401c0758005c00e800110313003840b13140240281c050340180100c0c00c4424003950703210440042807091344210300d89040858008942c07078030b50040030000d01c49803805000480c80e0305902c985984940c42c1c2c80d0b041c0300c032490b598202c0150a100343e941141503642030320751001800030744c00110750186804030b0000740546241d090128103096010b0651803500040ca00300480310b038030190b0391170318421010184544008001036604840c0011880344440203040071080c04d000000c0d628048068000c1d8000760004150b8580035a4004281c0d00d801d504948071074440b450622000482c3c0f00c03552070b86103590042c084944401e450505120350701d0f4081c10000344d40752414080881d402d015600000f000c20800700003007000b520f01590750808041d0001d0103071001e4800c5c45640c41c216012544070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470037778 1250 470036528 470036531
    0x7020a05070305010c12020f0d05090f1b1008010609030303020f07120e040b01020c0609040b0d050f150601081003020409051005151309030f110a05010c2f0d050a110709 74
    0x10751000c1d42d4420800382d0580c6d0307801070540c24080c801c2c0105200e4000c0002c108181683c034000a084040c04100c043c0b1940341e52400d5500d00006000004000700300c009215014808141c07000c0704451248100314102c841581c0d861190390b007140d42c110060b5010040c90f840482042c010362002c60070f907203050300901209481d80c0803080c0b815400c2c002038811641c0043d0542d0844060000f050302c480c4111000c080040750001100315483d0005441c00e140224098218070980d800951400c0c0000b480c030240020521140b40300da510000111815a0120350000c520700c40900100014200380d00044e20305480f0700155a060880b025401089420440d0606c0001c1148400b8540c5400c0c1880d404080050030f00041c40b46286640f400303000c0e0b143d0480c140d01005041407408540c58000c0c05820340e00e941c010000e000d00552030740d00400516010840140940c801d0003980760290551828041d1030340000b003d8402c000b41714009039440d40010741c1110a0005e80c1c40007450021040c4280d901410f6860030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470039028 1250 470037778 470037791
    0xf030a060602010c090f0611010f061202120f0d03020c011e06090b041a12030d2c0c0a060e03010e01090b07080726150d0b0103170a080f07020a0507030501 68
    0x1c0003030075240c18550070014411054414852407807050154010740310769003008544c0c41c42401207180103041d03100d4030818061030310b000410404866404000f143d4022640182c58055808003140c80714505140b5244c164000e800d20a0720034020380250011028402c00003c0180e2a010002d54000b0704e03940c0b810745182d4840081c4480207940c860078401400c02e54007013084030400141c5014007422841c80c18460b401401d02d4000d06c0008004941034440710a10620148003031001140d04040104841010349900f890042210b590006034503402c2c0c84010700000d042c900d00031050b584000120202d582554039100d032024401c42c24002c0c0104035205581c3c0358003901d090300300103100310405000c0d0402c0146103a0710440289c14007070080210503011410ba0384d01c2e00c643c1150f10f0981717050340c00560070000340075510050102003030869040380c0c003511030120040001d43d00008580b04045140c00410071010102d42442204042d00c0e502801d00e0046807000c3c03940c1d845007490000b050b40708580980d11182e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470040278 1250 470039028 470039039
    0x6090316050405070201020903070308070f1e1e50010b0901030314030705040f03201f0c0c0803070804140f011e0c060e01021e07020307060f0201020f030a06 69
    0x108451344855544000c500313000e41c85001945074032145c400070300368a602081d10800d2043c41e5007403001c1c180d440100101c48082400c161340051400030402d40b11030030096102c460b0842a20ba03503445950b8841c1040340403102428454482c4a490901184c543d12110807808001c140000c51050320403030740e012418002044a441c2e42900d03005041d2074010b401001c010000650480000c610300c2c028180308076101d54030740320201c5041c0601d602034000b0510b490300003c1030140100300800f0414034800d00c01251a040010300250b904a01100b10040c89042c040341c0d9140c0c0b2034111034003054400c1440e120a5030350f0780130880c80d42e0083c00c81500c003460300082c02c11003a54103000c5001125415914400142c0e0140006010a15440c00200304043d10000040449206020565010f60300c0042081000c0808500c81e0003504007407680c0c10703007003180302c05811aa0428400c2d00e841d182e00a00400100b42455022581e0b0a04911303110150342d001d0000c01c01c0350f12040c0181d0b01c0744841000000d00c00b454003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470041528 1250 470040278 470040281
    0x30903070209011e050d05010e010213060210060b0f0f0d0c200d0c0b0c071a07030609090804260105040308041e0c06051803030301031b0e070c020906060903160504 72
    0x40c0e2040c00c4c14045415001c204942c0c44615070100d4008842140107003025081090240514034a4000305500c0000d000c200c0814180d00030b425184664211400c00b40c05140d4501144e802d8040e10040000c24440071041d000c1c01c500408840ca9107041141c109404421200192449004400e01103400045c00750220050701c98800116012940240f890212170303030001d02007031382c0c080024280840100004600540e14021220142d900440f20106103071084c014891a5100380c551130001303401c02c82c000401c00510300824410b03640003030146281910748266081c3c1c0342d10380003142d42d03020010040d000b034820003849143d2086000e5240d60140b841c080c586402500312040c0000c00c0c4d0f01090714403d01040081d000711003070320308609010b5070322900010000142e1102d550003590603c1700100100c100081054140c01e0001042c018005068446000010042048540c023001549010518025141c20b0f00170310342010024040a2030311400380c010a0802c02c0c1d03c490484910075181c402c00050415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470042778 1250 470041528 470041531
    0x90b0105120f04112e0e09040c03050606030a050705060a02010b060f090a0504230c0903030406091802070b0c13050d0f0b15210313060801091407090501120b0303030903070209 77
    0x101c40004040c5c1001121a01400541201e0880c14a1081c0d490000074055203207103040400c02080844030b4a054908051000b11b07601084406010701404240b0710309001510b21380a030b60110140c40b02e2404c00341840441e0b002030b403880301150340714820082c9513120070000300b1a102d440340281e40e0300c907000400e00c2070401550b03104502640ca000600202001d440d120b80b20508032100a1843d02d84038030b8800072031401603114550f0316001c00200010389540000814086030f80c044801e0640588001c030005c124065402c000c0d1503800ea40000a100c2d24000b401405070740903117941015040c2d120408501e051510460031283d56003400814403e00480ca13550302d0b4003100b15061034115800076800705041c0490030040c2e542c2c202507488605014207050068407900c007000f175400005280d03508002000c940d000c0c420030300d060b0b142c0411444200c17030000060303102d081192104510140790900456450755a114a210a19680d0404440c00ea0f07050000394010403d0340015915800c1d540100f00c030f142d03030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470044028 1250 470042778 470042813
    0xc040515071214030f061201051806011d1807080d080712060b0f0f1209011506031406120309091f0e090c010809030403051903032301090b0105120f04 66
    0xe0a0030500d031000880b800304d990003e00604204941d4030b854020502200c0503501d2504154281001c029a0750011100b50550342c2900049641c640d9882c40c0054030204200c161030542c0450400051100c0c41d003d0114400b41c00c50710868054a80e5221450704108886251f000058140301c00c1c05100f0354800418600314108843c02c1217014504001404c41d1b20940300b89504c2c920b4003090003014030102e10f041e13900464950742780000b0303413501c0c02805000b4850309082c0034044520502c0822518424840c3c10742005030440c281950342c07100c00400140e5200080c0c810101d210400c404e82c142d8a404060601500c92064188001c40391282e1042080320346401c03024885080c0ca081021600c400146112440000e080020103a22103e01b0a415403107250400b6040c1d20654109040425000c2500141a4003c0c2d8082001c048002c3e88021b810440c0701010b6034100d00301005103c50103c0e81c0c00750b44178210504100e0310b42000e004501c070f40b40200f00c80d8240000365080c1044248240313500b40345010342 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470045278 1250 470044028 470044037
    0x1090e160f021902040b01020a02190603050f2a072306010515120c040830070b04020f0321030405070603090206040b03060604090609050601020d020c010c0305030c0405150712 77
    0x14400000d2203c0c04015100079108585a5070800010390080c0300f200e0900360042c0180840c0800403100c0280e8810360700c501c000007842c2c10000340c400480f94030420300403a84035001c0c942c41642072107100035000d118001c18070301260810094002848480114203054019201c1d40340b202c90714510b06080c134205a0100d80665215110250700200d420b048404000890400343c030280c83d0f000e107814181c065504242042d214079030860740c502c0c1c0111016160b1010103040409042c480c1c1e8060796550140e00001002c498400010500518261050800044024044030201c0f544034181d80d80d11003400d02c8207000f090f0000240402c1c04404c1c81b102024040c20f04040c40706440d07550118040c2c0c401d030f1060b000c9004000c03000c42c490350380b20400c0350024015544144859611600c002c80141400d5450324050310032034401c900e40d64008522080c882c10141c40700c2d0400780319910103882a6000400d0307142200b10800c404503032a59a99070b6a002c0090b80505a500c4518902e440b03610fa00d1002e402c01d0910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470046528 1250 470045278 470045293
    0x2030c040b0706090b091c1404080d1701050a0f03120201110d0b010206060301020301080607050a02100501030c1e060816030212010311010908061306020a0201090b04030e0a05040e0a08030601090e160f02 89
    0x82d20701e0040c3d403c071f21118644940c4507090407921080714060354001c80c1e024001c10903442115940000f900301119090944150716076039500400140c0103080c030a4203103003401c011080011508071507034545c40800c280004100c5100c8031000d00c0184d4000b4201c02d64290760391020340e005590400030b030b9500680950085266504005805545500c02066407003008000188055424403d101404000150a10602103942c40307180c001e05840e024010640c41c102c940141020a41848480104507100c0341c803807442a8503044c5091416000b9021803400303250f001c10080c00350214540425000710301038510b032181e08602034001400d0b042e0f250702410040d80a101801404ac8410b03240d1000c00d640880700580d03138810040e041c1c0c050304695a003d48249407490401c018160030560b41c410281c0200c448001d001e464600304002c8907420f4000b2080d551009500000155400b401107420400504100562075503c05807026030039811a05404418401c0c6500c0007003c2c0c01c42c1034000c0221890010b080e10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470047778 1250 470046528 470046553
    0x50907060305041e02010c0501092d020904061104080604050d1b0b13150203090d030606020703050a061a101d040b03030d050703110c0c030f06010b0d02030c040b0706090b09 76
    0x88066480c489200002c0e8813001c1045a015004604003a13520000900038603003070341811503050711148c80c0d260503001800a80800c90581e450b58401d050b9000300402c00310f40b03440d25800010a51070910001148003008086100725003003112074451442500106140441800e00030001440480c1c03400c3d0500b44580e1002c000303a12403d45507400440503240507078444450520300c00c0c0b00300c400c1c01d820070184004140800c040d800324031040c1c24051501c040c00655030307032003080343e640b00c036440301802e15044480d01d00009002a0002c2540d105007000101f1109500c800248014007500b500c400031032074284c1c40b0048400c0078154400034000448040240011810100380c4900c60030803203110841da40c5002503a0940079910808003058060307040f98440291070000c90740c9d000341c030041e240b0034800c150b209134803110001040b905039060703003000c0d03410034042ca0300482c080e40014140c0c4200c41c20500012070403035001e001500e04640510b0b004281c0c0d241d06e040229640350b001e00f00d0a425044040c0d142c54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470049028 1250 470047778 470047793
    0xa080102130914040c0b07030210021b060108031306030e030c060108030315030703030c0318090e07181505100512040b2205030307050c0a021906091401021b03010f05090105090706030504 82
    0x451b2000030010b0342e40c4016140403810300c002d542180f804280301241d28025129401524014105010111801030346c0300c100861b170701d0040000c03554450b0b0b407c01d020700030280720f6005401c0042210b001c803410700400451990529400341c01000c15540301108221510b11202d210486140e02034000d40005030442e20010001000360301c000d41484855141913a000070780380130a2004040f041c0c0200072103840301c00000c4d04c1ea140e81c41040c40794150f03000207440c0c082052003401914140c000c81e43d10f00d40e141c0810300110b514040c0c07150003886001d0080b0080810141d810907c41c605c140310003141480c200c0ca540070100207890300760030009203420410000038400400c45c2c2d04680e060418640321402e9440682ca42614030000070b42210282d100b0800d04a500d034161003d4507040e8507614115038864030b921070b00c9003040348020b005902480400405d1a40d04402c454490780140c004182400b6501241c0291a0305807514407660395144200003000000380300c1c2d50007400d540c0c9810300c150300f07054403042c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470050278 1250 470049028 470049053
    0x30516140d060b12100506180906041e05010609020a09060e220b040f0c030b09160c060e03130806011d0109020a02150f0f010b030c180a08010213091404 67
    0x1c02c11559602104001d907224020481d40340200400c540c0903c8080501d1400303410180ca07001d000e485000c2030400d032480c048c0c0c01284a61803a50080000d03503a43c5d15850140310010303410700c0c2e2005810710103c003c250280a109c0142c0041c40d40969943c20b5500005c00026965108104020f00000b100302c5917a10b04003103103207545030b52a1802501402000c608001c000c04514154020715140d07040c3ca062040c0d030040400e040039900d040051145190a01c02181c2040701c4500b24191031042c10311455000c0da00321000d190069200180200082400600d542e000c03050b03940007055021400c00512008204082c003400b40201d00c00d22500074894140c01500040c0503150746241c0105000482034030810500b8a000441c103102d400034101410104030f81802540d8855002489034001b29214242c0803c8078010344042c000c90b458490000780746194950a102d00c10b92003854002c0029010109002400c1c1080e5455817500849280c000304004031540c500412054001440401010035000c0708030700b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470051528 1250 470050278 470050283
    0x40b03070e03030f220906030203190602091c02150906070f06090f0c080d080c0a050304060603330606051c020915030402120a05071a0408010204030516140d 69
    0x1003503075803500003070300718002c5000d043d20365003000c101700941d218034030004129030b00521000b0448944030380751b00c02658018000a034240c2d015510310000075443c03106100016014400050900440303a000070004180c4a0380f03d03007810305a150410a6140414024080c0030451000d41e28191608000c940710b4012910081c040c410300e04000805c6c00241e8100c41c800326403100403030766120b02c14a0f105032080f42500501515202d1401c0c1c078506240a10f00940c00742200041083c14220306d500100d600b5030000703004071801d82e15594000002100c2054001040010304490810a0041c4080c4224003500300c8504c5222420407204010b210303040421074810400d01c0518500c01c110042c4407c02920802d80c2558000e5174050105800401d014041d500491080315408081c8219010160707031001c9c01000984141c008076020810402d06803010150124410600f40c101030343d40039554220382050b40207070b9480d008186106c0512031001080000303440400d1040d4120016003011a449a4682100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470052778 1250 470051528 470051537
    0x90509060f1f08031303050f060103051b1207170c0108060f0d140714010801080c0f10030b0d050307050d0203070b010605030c07050d1211040302060d0b0612010609050109060302040b0307 82
    0x49034024001c84081d000503000f8102102d550f003c405e6410600051948010342d0301d4042e15070002c400d084041409030481c0e030050018041594800118a52400000c62072a4400120150250061401e121041c011301c46d0100903800b95902901580c10f001e41000c1843c10045410200041a901e0740c2e034100e14608151238120200c5071f946003001d5480c07490100e40d400792040500010700c440d80c07074046101d190070a03603501813182d03607400741d40c0c2c0d807882c0114400b94481000d1043c2059403c2c030280c403c40900f41443c011401725003505c0440c0564034500c0056856420003d031940910038200a01c1740200344a10040d8903000c2182c03030304a01082e06015a208201002000c03c0c0c038600c1240540b121a5041015111020b0400002400d0720705640142800c140c1000800c00425180c81c0c00d0310100e075006040b440c0f40c03010464480c4000c040302c251240e84404140011614056860482b50203003c0a440356605907050000141464046911520815004010902034158820152904400c03641030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470054028 1250 470052778 470052811
    0x302010525080c181804120e010c030309020406090911120601180c020120070c0b0301060c030e0301060b0c0604060f02090d0f050c120c0a0b130e040f05060709090509060f 75
    0x610f42118510005144e205007041204a03500303017403901003400b6620445110070308101e52082a04c3c014109218180030417824491500824005c0d0442101c1d20f100030000501c3c6c0ea00c0c0c0d060003048400030341c0d0954800380080c0c0500900d0914070380c0410190000c10003080d06625111184030540d0028210f4240700740c4540100b21041c0c001d400900b0400842000000d882e80880034010a0360810b035826549886080030004030703401c110381101d05075842681e40d102816040c0c3c906885110600394007d4040d035a6000019519032114054202c61107494080c0c0b0300c606240c2051010359841e43c901a9085104101d40e01140c0d883c7d0300b80f1b4004580c0140d100c1d20300c1c040d904103141000320000b01c0e071782c1262020008020100c00416284d0204e0001c0310301c0411300e919040b1070300340703030041c8012400442e880e09000d0105003018650f5682c054400c1d07000c019403030100c2d602c40c2d050560545002c804101030080a01c14200709014080e80050500020714103454030300e02140e4010000b820f09080c42ca02c10a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470055278 1250 470054028 470054047
    0x3090307230a0e0f0a06060e01051b061806010e06060318030912030c07060c050a030e030a0c0b0409111e030603122709010f05090a180302010525080c 66
    0x5007004803a6000a1111001c503640b6200500c8081d030484203070914070405400150040e070a84913200c161a40d9a4074000800036400054659900c00d100c83c90111258628601c1089000c00400d803180603d030034122041d030f154440d05c521348001a0032001c50b60358140d0401c007c90312a40d0549030311054164600302100c0c00207039102d007180301d00b201c040c4d040f1545052032501044000001d00192540340100d80046544502c11500c449903000010820340112044102283c0b081c6204500284000c041d51800c40c0e9a80e9031140740101584980d00c0b203200498200824100361040c525080303041d400203446c140038143c00303100042c100030030b0b10300c1c4d1070020001c075045443c04c010b00128440c00e48191540d800610043e2280c050b160b840107403410303114402207019801c04180c1c01d81242c1c031f2220900012410072040000341000140a07940d0986d031004038040821200300d2803807009000c3c0d000000d4a0501e405001c07162105500f03410346614002d070140148944c00342446a01801c4124425202c48004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470056528 1250 470055278 470055329
    0x1c020322080d2a050f12071d040e03070b31030909022d1605010902040e0f06160203130e1906051003020306040603080a110c0d031b02030a140c1203090307 68
    0x2003441c0d19568440404200f03250f500040c00407010720418040d107281c00c01e231100f0482030790003600e22076035181c20600003000052008001c00e0703001814825004008841d50440319440000058041104440e0a10030700516401c40c1d000c13005000f070088190700c1c0c4030035910031001c1c040c0c0c0d425000c0310000e803070740705640c1c01b246c20801c0d1801d06160b00e00b031900c0e0a01c0c5050087c0640a0a2002c1e4465450001681070b007903000503c05e080014503502a0801741c0e074085005d00c070894481031180950100f00311501c941c0038500c2c0e2900241a141020182c203090089101d503205e2440c00d500310107641361900900450392040900910411a45005a50380ea074510100d000343c04a580002c010728400726418080e0385d04804d0700304040c64003008032146000244200000c290310000003a011403918298540f0845260101e1910301380040d085584501e52566441d50400f650341b56803859070000c1c44001664a4413500400490302280000c2d42445800320009896104611900e60150b00045a03903d881c0e0070b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470057778 1250 470056528 470056537
    0x604170a110303150102070b03150603090a0219081c080a020903100e1f02040302060301120305070c0825080d0f090b07080301030b0c1c020322080d2a050f 68
    0x1841039a40341e062115082c003c0b61402c42004d409030051640100754610500181c921416890804110280c03000090103819072000c1c08504243c000c1c00040401340c1c80703132104843d0311444941c0f441022440c1612842c10301d21000d9140090800b600000b00c9c900d5440010341ea04074010714401070380c1d88212000645480184595a10507a0508950030b0381c041012804c0c04c3c50b5840789907203200043d88640c2a50480c402c0d408000c1d4410414030040c4284400c1c0302c50500c101e40700e420300ca450060541c40b00160000c06078054a02d40e4058156038100f0310741c280381e10141180220000110504210070181c441000340607080030020070101d41040c80340f117007056800500307003907140a42d19a2641802c16aa500902044d544a43c0480104040a1341d4400700c594026801441a01c1014500030301c00203035001400300034214049083e5204009414050340110920800110ba80ca8159921441c00c1d103100d4905950024942c032514009251406804d00c018196450126516510b03a081303200503014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470059028 1250 470057778 470057807
    0x30a020d18030f0501020a030c021c080a1e061401020a0305090f061b0d09060923010e100c0213020702030d0509010c0b091e06011a1c05040b07030e0604170a 69
    0x30300501c0c3e40c0900a040d4014108000725580034051300e0844001a44d4504402084201205100c0c2404402501c03c013441354100c4100100402c90341601d1035034030020416025050744c216540c0c1c0b410448840e10502e109103050081c00034000c0c5048544010303005004900640c2e000300070030850103626680340d50413544402e5421580f840364244183d003081e5104103420403038010170703842480031440c07034003490008045520302c00404030885007900082c800310403283c00c00d1303052051689a80d0240d940704d5072008030f0705020b42d50305c40c0b041c08180100402040014050300029104000000140e14045020011050f2500f401d55443c28030744012944043e40803000340452140c10b0a10544400208807011400407110650a03103007903003190252103050038030480d0f4205044100080c06010204080c22425042344403100503403804070410f41c142e40080720304a640c503440300100300c001a0148a080e00e0341140701d00520151400365507004c500508400c80a842c100e01041011036188205172001e42c06c00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470060278 1250 470059028 470059043
    0xd0506190e060d021207091512112d0114090a061407060504061409120d0b010e060310030b0f04050a02010804020f040c0e0325150c12050d0c02030a020d1803 69
    0x4805440544492140c0074105981d4202004c84054865602e1864152403078081400506102e681d100d08ac4c190a840700203030040c1455600300c4190230b10b125a00303a8100c24011141440009a00042c01c000e58400040b880d04001e0156000903159210740da030035100e0301d040261007070300004c05400140c09046401001c160070b01040004220740b64010074040111600e550000351524a01a42c03203007420349282d0703003080080c440f81c05801010b03040040040c17010b040c440410b04500000c2003a0341d00490710540f40300901f210400401c0f07410103001c0c2c0d1002e030780422004241000c1d13803015107a4000c038001030304010700000840c003590344023812140d2800006108021030640c0810107052032004022240c480d0240c0006203900d640703400d0440315401003034144000341c5810f04030144400401c446650042000740203852000806503030203c8502c030034540304c054a8909048081c0c061f41c0f040e400c01c404641003400b0710250160000390b164804691410010340e400003055500d460078500c0e5102424030b2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470061528 1250 470060278 470060299
    0x11061603063c0321030c030209180c071407140a0303020c150c0a05100b010f080c0c150a091e03021b130606170612032205060705030d0506190e060d02 66
    0x5100c02a800e0300703000300d072014418032104400171f500700e005043c00541c011402e1480101c030070070101659513011640800e098203002c1c8a0312510124120508640029440f008092090100c12104404903440131660304080d541140e900035100c08182029a0243d045108408a0041c6060540e0412401721040b907104400c6400d0850703a480c49807500c8c2c20520302e020110303841d651050074503200c11009a103442c5150b0300c4046001c842e81d4803100c04040280100381d821007002d00c45a440ea4001e0143d402d0109080e0b140b420650304035240748128882007901d88200741c0c0001c0d00420742c100c840c6008411400030005100208100c841c00007010329419142600101e0800c1e000000035802d00b4598030800d52950311441804400580e40545021591040c070001108991141c98103540007c401b8031000789075a6240400c210381c0203004c04460a40004c208034000c02c005100301d6501003c01c59444001a60452445a0f039603240d000b440300d2401c2e000300080031074a0f928601000a640a807001e00705 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470062778 1250 470061528 470061563
    0xc0d051009020c0c01031d0c120a0b010f0e0903120c03100f0f031403041d070903050a12021b060409090501020c03070602030f0f01030809010c020111061603063c03 72
    0x11828013019040c003285c41d202103010074601095403150b03c2e9203510000c0011039120400c00040c0021140352040d944100d407502030000c3d20780d00760503000303101300012441d03a81d042140300401d03040f0060009202d0761050141d600918500045a41c001881c0808695130791035815080483c1c90082c0c00400d40075003800b41c0020b90f0f046040645040707900540b0a00000352040c4a40b40d201c4c0300e83e10891221003e02a4075940644290000d180c0195960810079807031a07507644c0391820080c002c1e6054404001a41c0c0e1280318030f030107001c411090740384100e0a2082100460020f40c16001f140030b8024000d5603040ea072010000c0950444403040481c20440340c50700d08500c0c01001030b50003191824424010800030074161140740c800781e41641c1c0d12104c100d09180398000111041202d00030168100080400c80c1203c1c0c10307003400717060b003d100d031154080d200d03820f404405002d03184554041d5040c85090a9450345010780b07408140c0c21400b212403042c0d1051100d204041c0e41c42000c0d000a0300031242c014080c0e81 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470064028 1250 470062778 470062783
    0x9050606040b0402040305060718090e031c180b0705042102010906171f0b190207050307050f150f2206170a050406110703080a060506030c0d051009020c 67
    0x410201107030148412485038080c04282d000c0e501c00140305602060200e01c015000310606000b040d1040420301c01180e8807015034060318a802d00d00d141d142c1001429002c1619200030041c1401540b080500c11040481d00030700300c46034040310251011500102103951715115604560050414440c040748102c07044190401c010341403031049010494101c000561540512080382c411440c0348462003550750b401c007103649003207148501e10548d010442008103c1541d0b50700605008440e00c1075280b42200c040710080e182c03480c0b07030700250711a80c0100c004212680d02c0c103401d00c0e09100e00740c41c0e42800244180305805c96014002c2d0980741c1c1c1401003140c100780a0404260301001d003c150854040550300c00f0143d58450088001d18034580e541e1000a00150180c0c10a94100b48102c8001507100b5140c4090003142e08002c008500080c00d110030b0003114200da01030b990250000320f0710b852a60404540e08400c07445150300d00e020b015120800030325120140000c140044c0301c41c0d42c095555007501801c00f80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470065278 1250 470064028 470064031
    0x3070506010807090603210207030f0303050a2906070606030f030809010606030c082707060e0a0e0702190311063111040f0209041103011706040f0303050c0706090506 73
    0xc102e846401400250010b240c0185011290420700304460321503900303500c5601d180d0a1040a003507105403040000018075004035100703245d0099600003002c0c103201e1603903000e80e00c1001d483c9038114036065043c0080342e5209a070008039003040300d98a94880c0d0720b00d041c3c07001e04001d1303001408650009410006040c1c21003049071007818003400811403203460300d400742c01b10356441d02c1c1140081c0c06800000d5031001e504402c6480110b00c6c00b84145600c07100103140b8a00113107034100c40c0c001a124421030b21507042008005001d0692410015014600100c0080d43c80c581e24103c801c10040c2840040c0c2450b028501d04100b4114010030303541503160020003001c600703010f034201307001100c0101c58403d82085200d4a00808960203a032409080202d282044080d1007000a14040c2e9075003001501596581c0707200d580b158043c40300310141c482d80741402c4880180c40700600b42d500340e0804000c10001035041e0550560715903241c01c0006580d118005103642c80d014143c40245218034003000c04c41401800180c26 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470066528 1250 470065278 470065289
    0x90f0f01020d0c0f080d0504140706090b0a02160605040f0806010320060c0709090201171302011409190f0605070c0b03071202132918150a09080c060313030305090f0307050601 77
    0x10a1242700c140d0b58113030750712000d01c500303c00a001820144150014480184034041d4644121210100c118560840c0c21503282c1c0105e011030b00c0020100007049400100c1c02c024034408018001a40c99600c40010b4001700400303003244101c2c2004090304991707400d016a080d14503050b08682115480b01b4142c0700403c12514164081001c040e07400e42140000350760b0300e22540000044008401066006648003c00e901c44c1304101041884107801548400f403000030035118459607209031078500101c040340b0158903040241008020004900850466800f0508a89480004c0ca9076903480110440d040704001c403002e8109400064500240ca401c000c41e01d058441c2051400c492980f01c0703140812641d5400001c50040f030050100c011880644140c00c445035501601c42003848038800b0007496642d221a0005020030f030304100902014400b0003002e82c00c034101b41c528600c0c504140344003080368900510002c01b016203d40010344191424050350681040040480f5100c4c0b1040c41e10a489000c24001c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470067778 1250 470066528 470066543
    0x50c0d0203070b250f03020c1204030c0602060c040b0c0106050907050c07050405091f110c060a050a05132a1401021207020a052103030c090f0f01020d0c0f080d0504 72
    0x1040d0071300c60b56018400001c400c000c1414560207a944c0035240c0400445861060650901ca0450400814001c8500310301e43d08900650b80c42c00c51600d05400b11081e0480310441d40960300300043c41440900b05c80c01e440812110301d4882d56242282c0e409070005d0342001e50066100d40030b2282d21a0060050209282c4010540d5002c40c0ca0341c041c8400c60b00201d4003001164410807810a800003041a01461540b18100106140001014280e915804442070a506500c10030070400100300300d02ca000d80242103000117001c43e05200701003240080c1038401c0038240507117103d4a401070406a003c00105a144528005250f030354642a9004070600c0c071741c6090142c06108104c100341e260100c205c07081ca950080000b54514146402c0c0180010303461000d02c2c20340217290f01c103000c88200700061486001400e10103542c4a80f24400d11184908000300300d80030b00f0010750811030517030300402d0320070b58030341d01e0f241c1020280c449050040c007090702c581001c4c00d4848001030b400c03031202d003a4000c2780c81039009150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470069028 1250 470067778 470067781
    0x801090b09060102060601110a0204140610030603020a0b0a1803050c01030f0612230307060f0612020109180f02070f060c050c030a1b0203061e070c170703050c0d0203070b 75
    0x501c6400a01111440d0068005600091040d800f0700d10a560050080d401c03a04407004c694049411603034a08080e0781092240700800400b45805c2c03501140485043c0341c01d1040310314560220b00b800c00c007801071040d040400314281b12503034401d030340d14600901070040305c0100f2039072800d00d90b0715000954103a130f000a0620030040c3c0101d450b070180d80129800340ca00c40e4000411500c80c640602d2440311003000402041213160f048800400151040350301a01c0c0000f07440c4d000b0501081125070541c0030155200c0c100e00e418001d0703030704000488101e41004240406154010220700d0043c03010040b0038621510118071402805002421130a6062284204000c0301d03120000694480c041c3c6003024500c1d41c01004040e0459100f40d116a5180181d032512114607907040e40041d00384030703040350100242c02a80040a64104280080c5a003200741402e000c056150691514650802c440c142c101e5100d000103500070804d841802252020b08003001555040000c0a0b0020f481c2d1b0b100180c01c1ea0740351510700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470070278 1250 470069028 470069051
    0xf0f0e15031b1906020a0206160b0703050108011b050a0c020f03030d1406031207030311040e0903070302010b011b0318052e0311070b07091703042d050607050f0706080109 75
    0x1a43c4429111250000d040c0307142241d0030806503900034541c3c070118414074805180002c00455040e801003400341c070080744660500010b982150030030540c180c54111038038101503500d50400101ca0a2141924140310040500d00110390345005001302607426210004100e0380400c0030754014850320241400054007521414101903070b64080c41e1503822054000c015101c0000e0203039114003094814440c21a08240c0e46043d10344070141c08841e04c4019400008051007010750a1060075040c08007400e002c0300c068982d07045d00e122a40004c1004060209132080500c0502107540010001c0100400756040741c5c041c40c2075080e041184590080c04400002202d010031400fa0180d0b42c0703c4000c0f02240c80c01c0c08840d8442d4800c07640090121003e00c540218041079982c507000e0030300703004601000210780d601d207009003803c80054803043c0034034024a1034284212030790004004004640c0111101512450303a4142107040c1704207004410080e118100e00020159048118181207e0004500700920034108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470071528 1250 470070278 470070319
    0x20c070f0b1c060608010506130b0f0a080709140d050c0d0302010b010f050f0a1b0c090e0d1806030509030f04060e0109050102060f06060c15041109010f0f0e15031b 72
    0x20b00130000490800c10050102c1d090103005000c0e54136001c0c241c0c20003141c0d142007035509a07000070000048a580004d0340310980d41c0058241c0d800c95440d2601c0c2c044145400c462000d00d540b580310091045902a408809100d4100b04034140100c006151101800d898030b40a80201030103c0324038003064040034544640ba000700165411035030280010b40c036140c0104411148109000008180184000c07420004204d8500f403400180c09842000907030100204105890880265001400c1045c45070051900c55142218803003118180d00740424203454810385203046000310300c003074074058801240c0000c07156408508a80100820b881d01117490303460b44012601d801d003ca0b0600750403c0c413080400c013981440c00c0107004140b02401035402d410305d840c850806e04102544c055034071000c8060200392b00e140520f4020f004020000c0c100740510700d031035800d048114840c4958000940c852001401501613282490704100300103080d50308003641a800c200504e00c000380a907001c1e01c491210a020318481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470072778 1250 470071528 470071541
    0xf091a01050a0e0403021504020a080f060a0b04020f180609060d0c080705030402032a030f01051603090c1806050d063e030901021b061609031203020c070f0b1c 70
    0x51b030181c1411202c0b0611002d000c030016100704d03009003032440f0000340d8140900c00010041d01a001070301d0142407030a401c0c0151040103507640c3c81148100328003040707061100d045803c000500c0b08d10740c00b1710f400032001400500030441515084100080c0244402015038003038801000d0948480301182c448003c1250300703000072540250150301c0031102e4500803407001001a03c488800342c00000f5058100c0203c1d0400800c3e4403042196074582041c804180700441002155000e185420091003040340c1350448201032034400d035801d8240c1c2103c00c10bd40511394209102400c0702030b110944028052410300d00030081d201c0600e02c14640c441d24458942c0304264003040d22080140c044072002c01a210204e120303400603143d03c1c031540d82041011401400012400300045104006c3d000070f1800b005100d111180200d103a07002c1100386002400051507605440241c09910700d0b0042c2c031a19244803981c5464010781080c20f02c9070150b04000b80703d000704030042036040c5c0c0311181503007134080460000c1d06030740c070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470074028 1250 470072778 470072783
    0x305120f0d0e0124080c0306090607050307020102160308010302190e24100f080c03270316260702060d020c031615050106020d0206010501030f091a01050a0e04 70
    0x4007003000c5a1203003165004002900080c600000d0150035a100107810b44150b0180b2800791091448101700390407051048180400040e4042c04061400a40e008e0b2109002489501801404004502c1003413007513054070032101c0058502000489035043c0903200710b000748412032040c41d03a4081c0c0d0309410803c140810444000c00d0420011f5107400301e030401c0011030543c9410a4031945254003c06540d0030070500140c1101351540e48500e0750180c0000c0510303200a2580b0b00c0e4030300030001c1c002c8880302440c0401a01000300540c244c00c100084c2074606600c00d0303c0d01082c09968103070555080c400308440d21140300d08120104807005149408410180c014900302030743c4004280304000c1401c42a80090052084c5901501d180c64490a108240111080b4040d20100328450303501c2000c204a01c14207000d0002c2c6c0c0001c0072031200c0803c00955500c0d05024040c10140c841d119003070b0b00d0840f41c01418800340d100e52102685940c40d48081240c0c1170034800c0e00d01c80c034074814000544490024200e409240c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470075278 1250 470074028 470074057
    0x605090d03030e12041d070c05060109110c030d1a19091a031b040507080103050606010e2b0c0501092105070e010e16031b0810080303010609030512 65
    0x105031002e5004200d50461820316001c1e03100003841d12009400204060007454070207408010001c1d00c03100305184005c0180c4240039140030f0030804180c00003010760440d075224401242d5440781e8158aa15401406c901308507510000c60010828002e94010025540045203a80c06800f208010032400c030801000c80c4078002d80f058001c0c800181c84c2e4000c42001c0810448046000d80c04a01107807801104a10001c0207209491074044c1d1031030240102c035000f42280c60042c03015410341d11000d03280c41001e00030a05200d40304103252500e4031040888441c2682e0040c1114021050721410306801c0782c617000407500040b8045005c1a1907000d5140c0d202030301c0001405c1d105a6040324412088510f100d001035130703644039445c80098007008182c6498060305003842940b8450618401c846003070b611818a203c01d2600340f6403444540380c5114017202c0d80700403d142c21005501c030941240d0701c0c0100c135000315400e400000004100c554100440707400312889a811260840260a015010381c050321034030900e0b19 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470076528 1250 470075278 470075299
    0x20111040f03080906130b030412080606030601030b120f071d04170309010204030206030c2502010228170a0f020c0d150209130501051305061c1a0c13060509 69
    0x2d0340c410f01504525001030700c000d2034991210034481c001c0300300303074400d018400000040004112902c0030100420fa0035081840440c00c120300041c01c540402880c46040540e507002405141d95010b40c0c60b0b080040c08000d903142203d030000c80d0790b112004c502805600d18640c2151404040300c2030481d0384115009108500c034100050800d000f25032000c1c10b802c40c259002c0c4404070150f5a01c100a600440480d40c8642d502c101000141100c5000030002c4404031103c1e00da0340c0c0240c0d03000300341d600491100c81c050382d000c2c0900d911900318825480780b024040107080c0300d1810300e403c165001840c5101540d211500c044c4c03461401281d5036050350800e00c0d08081c60310b030303004005032400080820900c1c6582001d824140c4500100316072809a0814580042d115001084541060003d08120500e949005c0c0a185040c1001c0750381103046100d007142503142aa244001d0040703034900c080103e2880c02c0301d40c02c0c505080020855903004000c100810300000034001404a0151040b46c2403488090040c6646 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470077778 1250 470076528 470076533
    0x30308060a0f060504090e010b100f030e0f060703110304050a020904020112050f04060b03070e0c070501060302030709051005090f0a0903020f19152f09060c030a020111040f03 77
    0x180a04480d8000c4044140492004038440c0e6150140001d9030b650358a0b0b0340340803500001d440030800c41141c2a41341500c04256a105c044024500a010742401d80072414422004c400500911604c21001c1c00383c0241c8403009140800e41c203010b5159550188250410b40203152145e1000f80c4005165038000041c5500504262a5284d071060050600c0c034000350030301a009083e14000c8821342c03240c0310100c1c100000c200083c45a144c50842c240c00500b1810708001002c000100081c241040403600800c510080007002d41100c0f000c0c43d40034090b52142d5036101254400f03070105170b541c6000c030f000e02030011032a82031030070b01c1e540b04000c403030500c10b075548428407440300820351385400750210f004880c000f82e0400700401c02c2c0085000141080341d00c41441d0f00742013031601400407128034402e04040458a004410040704035400d00c0c40089a208640b03040e4500d461803060720103161700718101050318140d000011000c0c0000c81c1003600280818090017690085a03c0390b40074441a01d86070403022b001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470079028 1250 470077778 470077787
    0x11a012607020c060c1c030608100207050f011401030b15010806060a030f1e050c1206011206080109060605030f0c130b1203032509050d080d1806050a0c05070b010303 73
    0x400c801d15005540460343c084000c40e2141c0c1c005c20750a00d80394043c202610101c25881100316468074140307810400942040c04039900c507040c0c81c07504201d003a004076100042c00f5040c003030a8000070311100200905601d0b04c58040840001b44400da918140100000c1c580f100c81d01d40c0200b07480016501c85646583c0c910400c181034000314810002c143e60790003e264800c11500c58550454640c2c101220804a006c03542000d460b40208140361082d000c1c07004280040880c00e81c580c00c0102400c1055105625442d403030020101d65000c02c00540c20061a0014011a42d1110003920800d4040c2e80c1c410308000071a07030782c1d40c403400310341e6800c0203031000c070484140307000c0d841400504c0d001081c01e4102190041d6140c90b68200b82c0740c8010560481c0803003c07035402c44440350464a040c506154800ca0300d413a00003200e2101a0710b010344103800c0001c2c00c1040c4030540e2700c0790448150304800c8441401e42400c06100502d0f0031290f81d5001031908144040290040c819a8206640400b91031075680c02d580d4100e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470080278 1250 470079028 470079031
    0x301050105070f0b0705030a2f0f0c010219110d080604180c0b130e070e041a1e1005091e040b100e04060b0a05030a0b060f040602011a0126 61
    0x40d281e0043d890018001000e054505018403041d0f501c1079101c0c10040288800c8030040c07403070000c56400200c00c0f416010807a075950031000650410158482000d0090b10b0000d10641060a80a5200040d200a41029840b042c1da509800365161610940c1d1000219600c4145602020200e014600055280e141c560040300542070b60407410521804140c3c2d494001ca001600108140b040c00b0a014009004011510000b0001d01001100905000d140a000366040c007030800d028507251925403480141807243c1c1a007020010304000e9100c20881e130f40d05e1420100c110b40a00c519000d00f02024410f110744240d0303c031000300030841a0700001051405006222101c000d40d0420b40b05c0b215119940d490100d44280080c142e01e4060b50700d035030b6104110444840c4c0d0800c140c595002e1002d296034690040030340b54003031480c050000f030354140b24002808a01400c11650300d1242c0000340491816030640212440007a0030041000e22510603006440c0e010355103a10b01040c804511841400b0a11045003d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470081528 1250 470080278 470080283
    0xd03020c0319030b102606061225110709050702030906130b04170613110105090d05060c0c060f0106050703050a0903020406090c080a050c090d050313030b0105010f14030105010507 79
    0x10490410313004900391450b039054500118442002405101c2841241b01010850282c0c60000e9850600000350143c060100c4170050712020384c000510303290900d264502004c1021520003a0b01a00703103c0200170b191000410111070181400000344040c86000301405803145401450034007441505011968000b0071080c0c14802c0d070030100241c00701d401001003000e0024170070740081808540d85c2c3c0ea441c0c0711000d00440368011401d044400401c404c090507100c0c801c400d180050340c80065800103000380c9141d00016007540100c4d1f0038050225a224000c00c0a06001c006541c885e83d0782c034a80340303403102c0d01b4442d05012420801041e03001900c10001807031968501e0a0003825036485e60081012510280c010b518403550720440f54a02c00c0c5c008000c5540102440301c01c0c402c61034141c501351a580961002280a1030b02c0c3d0381007030200242801a2102c1003034031180600480e0b40e9040046451100388505808200040d0310659440c0c03150310601e824002d0b1b882594610307443d010044a1613440788205 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470082778 1250 470081528 470081531
    0x10050f0d060c03090507170c060d02121920071b090e0c090f071218080d060e1006020d080606041706011e0f03060903020a0b09010606020d03020c031903 67
    0x10341000485500c501c09849007280e50000700038603140760180c41c102003908022042e09908031070f048805000a121864001e090303800903210001001c1c0da1002e4020100f0403c5811400003c00208000190408402914800c828480c08071141d0b503170003080140c4c04111402c2e480030130200c400325040c0103040007040d41c40000c12080544c3d4003414002c86043c0311000c20103400041e02020035140064560340c10180381d0701c080555082405001e40b1502c82039540141c050b45550111300b02414980c100305000d41c01c0f40300316603034a03a5084a24000d14640c01072041c01480d48000c40c0b0b6441c50a0399a5040d039109800900468a140c40c05a540c031900414003540300d4010000031400b0302c0070242d0000c045000780d00400855040c40050740301208100e52100681c11400020000a103031a90820212900f0a100048000e61030a040741000c1344070b0300241c40d840314001400120901548240c04480c27184c0d0130340c1e800802d450021000d1784139034510181c00c2c0e4018004050f050030410a400180a903a040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470084028 1250 470082778 470082799
    0x218090903040f0b030108060a06081f0213030b061903023d0807020706081e06031504080717071104050601020f0f03040f15020d0804060b03030d020d0c0810050f 71
    0x38241541d42c02c44d00034040c0c4c01c4002c00104281c060402c1000e403c114201c030140251402c01c1056561250b02c0018480f818002c49030b010806082503049404c0ca075260101007801686a007040700c04101c0c26500076008041140d00340e103640784070a8201050300d5000f000502d58640604990000800041464000f01c03042181582406140b49000b9001d0300c064581c0344051511503806414042960301c480207100c00e450800000c201c4200d45810110552a40060140c541c000424070f80f078000344669030762031075450500080c06800c0b40681540b5108842941286103952969211802494402808403c14540c0d290702450140c0046a00134418411201583d0001410350324140e1010103c80d03454000090920014407c1d03040031020b05007a45022011503452000295640000400141000980c0020a04228958000016040c4010102c945840c5250702c2c0c40025401000788113031480c9440c0b1032543c01c0b801a06194440c21a211403960303c00d00c0d200c01e00660050843c81903500c0700c510075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470085278 1250 470084028 470084039
    0x203030919080d0c02120c011b050102090604031412090108040f11030a08041403070308120c0c100b09060d0b0402040209011202130501090b2701140c011e021809090304 74
    0x2181c80000f1594407107520300018018060130320062100c440c00e580100f80e0103502c2e0b036081100f10340c1081900201010801c02420194028020508110b07809400018000103000c08031014501c03402e40c6605544040c254060200183e204a00794107020480340b10008010640342c201c581d4280b07000e2408200e220012400107806d100c0840e1041b82c40c402c02042c00d110843e015000700d40320030016002001d103d405c1d5180d822680c05045100c400145c07202c00000d02d0b000c1c0034019100c001d4140806c44001c20305440c0350102800c025004103000300541d00014001e4030b00b003a00c20840c0c0e03420a0405845440725000c1c0000781d40102c0c800c1d0305000c4100011141000300b480100250f06040c005211490708110006003d20a664030001081d0310070b0000040e400c165580f8044410204001021005801d00040e00c0e8044040d0900700039440200f404980040107401080b0901101a105040302c1c2c0483c160340124000d08a004200c032606a4400e080780c1414079406801098141c1101c0c209070740c40c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470086528 1250 470085278 470085283
    0x7061b020a12140706170f1308030a02070510060311042004080609010b0d02060d0e1f050708090712170405040c050406030f2a03290109090207020303091908 69
    0x3c50740c08485038411002d030201400000c001e01903618012910a441c10061000c0c084003a0011b52850252004900c0760050010700e0002e180d80311404a48a1a040311450029040700c3ca00780d03641e000e40c9414451103080c034030441042d84d622180455a291418003400010421408084000302603502803c50513400300f00907000410440004140c00e180545000d400d46000d203030781a000b04801100da01c0103941c0c13041030b5200304004000003d03903e1050320324a85402c50762180f42c0b00d4410031616481e642e00103600007c1c40395501d6124410b403030b02c410008640c0e0340801e12401609580901544000074000c4084141c1d07284112856400e01d901c44001a04540104001c0300c0850700004040000713980501840c80800344808007001404600c00900e09444610400c00d120a0f4900343e8071101d40d8085e90044020107044403905031000d0b00500c0c141c070700d001200512030108240d160001548070450080300c950f5a40640075500300f04600301445248914400401900c104504002c607220340704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470087778 1250 470086528 470086559
    0x518010e0109030908160e0903070f0809191a1309020c03091314011a0c010c020d0e0312040909080c060405030403150e0a1202030409140109050907061b020a 69
    0x200400041c800b00ba514025010110a40c407070065a00400034090039000c40342500004c40703103081c06002d80e0b035490540f00b0f4107510902c2002410389031140804000c0c884040040c10011000740d804100b40c040741d0342c070b0903070f003110911544026588401980c00d8074040e4101070f04500010f510b040488070b4880302050305a07000a101020a0350004c200729007a880d011800c3e8000001141c0d04000c4012403000d500c025207014003400207130498100c80d071145180d1850403507140d42e0200c4001c1284103046040292110a104844000500c50f40c0410b0740914001c1111010f20f000081e042e440c084c500004d0902034000c200d402d5039104801c0c41051440b00d0107005142c4118800c4001d90359a500314640000c03800c5201ca40c50382c01d186405091a4000c1000401c841d1a40c1c1203406807070f1845a45100f2851131050340c0240782c00b94141b007103c0c1c05112250604a043e0351512800340541c0c0d540080d2160382d241c2d1446030304005405002c0c96201071006280b8450b1142c000b401c85000700d034868450006c1e01ca01e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470089028 1250 470087778 470087801
    0xc12271509350315040902010c020613030605010801020c03071b120311010612050a0213060906030c0e0f061e13050702060703061401020c01110c0424050a03080d051801 74
    0x340405074082c0e1002070704029650644440300700e8154142000c030750130440c05020714140100c1d03840000e10300f03588c090074544010941c02807405940340c0e028010f90a40f06120700c0202c9449003000004220080c041c026903485a508000440c24580c150311541c4a49070603a07807121040881c0c80001ca1010150f40c81001c01900a440e0310300250b20685001b030840750a0361210504400310540c0ca800100c0100301031074100e4040301d010810b1360600c40040002c0001da4044001c8602e4241c00200700600806040100e900c0c00300307510a190344040d203003410003030308031401c550000301d0050303102e126412441003149071900a8800e00143c08407200c000d04440081d100480940d0160080116141d4107010f0200501038071100d8500c10380302d81c0d0010703541c0d20344220041c2c1800300c0c03c04070340c03e2000c0400c00115540340040c014015007500d01042003c11507400d007441a40c00340c412012a860610485501c100e95008103c00d241950740818032008240280502c2a0107031103055203900800c003401800082030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470090278 1250 470089028 470089073
    0x40e0102031008190210050d0e100b090c07021507060b03031215151c090602040b1c06060206040b0402041d1c081306020901020307060c12271509 64
    0x9040c00d0b603c3d03107001180940540840c8150740000c0058650741004100030080d0300740540c540c10281c10b044040d000700c000c44081d40c0305481010390345c2e060540000001c07680c01d03a600c502d16154210320031414410000e020b07400020044684908502da86c00030440d280c0104c0e00000c40602c6000002c2c00c542c040303500d102d00764051405008880e094000440c06e9540b08a03001c01200880100d6444c0c10302800c180c00c010004000150954210560404414640d00000071903032075807181c040c916250031050112501134030801040c044403070944a0351003500c24a0f00100710075a11580c641100c010000d204903040358407003814205c501945040c000101c030030103002d007015070030940c1c0a13280440d80411841c100113000050005103607401d24020300580d040310000d0b03034459404005074910f2145020007050746103062642d4505503441100030000c052039100500180065041c6154949038480d04071160504520341c443c00a8085d00004070000800c0070702090b5100203494030189008851032559450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470091528 1250 470090278 470090311
    0x30d020403111810030204180204020706021806070b040b04140a03080105040510051c0512030c0c010b060903250f0602010b2e030906020d060603021e03130b0402040e010203 76
    0x1490a46901c076143c001140410007640790144400c160001c561001174040e0342d5642c00e035006a41200880044190003600955480d800b40c5001c400035032003044006038000350b111906600d072501d001261902504240c1c1c600c02030300e0366101e90040b0f141c068021501c081003000f842c50b0000c02401807541003400382e01c400c001503241c0405d2100359400100900c000d0f54144909220603a185105417051810300c842103440c1048500e4132519000b2420444100098040108076003082d152000f0b00749091460000d005903900c5409000f03ca0007051400c1e03600d0b0300007a4403459400d00780007005141c144403d00b0301c00041e42e1155051555025900700c41c006035190114004542440880e8003a060444006aa411202c1c13018861000d10030241c44402c041d121564401070010036015220038007500320741004590781e50708004e00207600c40e040360000000c441204504c10b4011a050b80d128104584640c0f100400c03d958413800024005e1007240e010f0703038541c0340710442c000034800b85215480c0d021030354051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470092778 1250 470091528 470091563
    0x12030903020c041521060e060702070905010b0f090301060e0703020a1e0c080a0302121611010c080c07061e05180c100c0212100c030c1817030d020403 66
    0x207100c1d0351203009000c1d506051080c0b4500210490040c105d8080d00400602103640c61101505107602c0d020150440b0306000c944940e40300c0200f100c0b07006046a40896420b2907031120100309845003485000003d01d0103203d48444115000020501c01c0d20050000559540342c40c29103001a905441c08000a17501240c00d450319900840d042010880307103e980345008100600c000c100034106207004240c0c0b8008580d100000e4040d4040c0c3e240e0340c40d81c10700d68100d4074080f4061800d0303841d00c00d01c460002b0742c14890451400c80602c01e07000584c0466980c01100d40c0c4074100040b1a6100440c04c585095803951106d8040c2c2e118480c02c9814061820040340721704242151401a081d22420010150000e040c8240503544004014982002c9810500b5010382c540c0001035001070061076224881c0521181d010000807031354800403516042e074a0800c41e034201c0390b03421624005100c81034540000d0042041c003110041100b5100d03002400021640b500c240003000400340d8000b94021906181c0300d030f154160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470094028 1250 470092778 470092783
    0x90309140402070803041e0605010603050f07080601022509240501110a02040915090b160c02130207140322090911130204120809040605010806010f0f05071203090302 73
    0x100c11101581080e90b2611594074602c0094070003454000f01050040000811141074150a038000700c04010560b034680d00903001d00003c46041d0a52140c0f40000f0b00224050301e0710500904041c0d000b8401203071940042c581008038045114a4603020110000d4104194041d2640c606c0b80c5482c4800103000462045c810001d05400c02418844201641c0083c038200203451030449404803404118004142442c268080141e05007800003400c0903403500a000a140c1014060141c031191804904c1c4640ca08480300c6088010083d404407042c01c0000030700c0d20319005000b200e4010201c042480385046021071440e840454045003518900716691540f80032800c020004240d1100c5c107001c0c1c2c003100e070785260003109001c4071300b07101d40c00314110034203045000c1e41990080e12003121952864006800c04031019004080e4051089040a03070118603544224a101c1c0240b03010b864801e404015440309407505110180f00d603013088414002400420003114498444407040c1d02d0002c2c8009081c00c0c020f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470095278 1250 470094028 470094059
    0x1002160501020601061715090f19020310060507081621090b0a05070c080601170c0a0303020c0d21030f0b040608070b0a0201110d06080709050403051b030706090309 72
    0x207055400c4071004004c1d00f50403105080384211411084c07003540e56006100542d01c6414580703a030308068500200006103805000c0301d409082d018640c8101c01c18080040c0c0b040e40b00032070380d50386020020101000200d0041f009402201c0c840c0b84250b0410003580380024200c2446482541e001c15102c0d180e410492044c0c2c404400e04107645041000281003105c0900c50b4490000710404003d800980d010901017044000c40161041c0c0707041d10841e580d01c00345104c18039001004901107005152841d4010310b80b16030726104981d459006410401c4007030041014a204424040d13032030110310040b00e11001c020400481d42015251000038041900300d000404403440300900038000c0e80b400c0001e100007880020704008030f400848095a0310460034a040380540386803080030009043c04140c008d9409070b180c1000c010b607007084080300d051650b204905070a035081500c020303000c5074080210504e100d40d010f0300e1001904140c01141c0ca00303101d641e50107081303604048095000415500c0188a03020005503005e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470096528 1250 470095278 470095289
    0xd11071e0b1021020310110a0f0e0901050f060403080c01050a0e150a0c112409030a0512070e0d05010905010b0f181803040b040807050109150804060b100216 69
    0x8491905103204050760041c1a9000f0922500c407030940001c55504021780364044400140034403600c41c214a500969402c82e01140c03001c00d264220f41c40c1860300c1500592080174000344210a01c4e40b802e0305014104444418458001004101c04404654030000400d10080f500c00002a0380c940035404d00308903111998040c0d20f0f40c0280401d9160a0224064103401074423a010010f4800400802a501d03c049481d9100544c0a9010351507080d1002e8003003030000380c40020740b090156a840320225160720414207810042038040c40a50030300c101140d11182d02c501c0030304007180070300b58203c002080000301d070000f201c3e140e449403080010031200f8021103a450b00190f588041005101c00001c8008008140c007600f41701c92140020040072a1000070000748403c03c0c1940d90b1a51600000106548107004a10300c0303100c1c036600040d8551049400d10121000000032010841c1110030889004d9000b43c170a6416503100d410040042e0b5803c0c00d0b098140349035800410084191400c403030610348040d44203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470097778 1250 470096528 470096551
    0x30e041d1207110d0203100e0c0319051c1209020301090b1801060f12080c0109140a0b011e050402030601030f1104210506060126040c090e120d11071e0b 67
    0x8440046e100090140162642d160010409980c0300e00802c0c90255418142940761050481d90040c41c2988c0041e660030364082c0040c6e07640a00b01030828040600350084007000550007288240b5208650ba220340240c40c401000810381851035110390950080c1035a001c40e03694420321120408190920902c0c3c001e0800448084203103240180300428215008070140c4000340014144810450070750010442c10703800200000003c0ca0f14480360303035518000c0c50480b40d0501c9200040751452540c1540440607001512101c10103003401d0910010390000740c0503605154440c6200c43c10204c03035020b050400158002016156854581c106a0291001c510441c004011400603c085000860301d194020030a08000e2880c01911a111031503100d80280e2443c503612010602c010460040c9540040383d002c420705016441f0914031413600c0c0e10013001c60b07424a200070000e030071500d0015001844000b003402e00e164108041a181c0300340d01040c1e0401103c406203150070300420480c441308004d0b00304801440c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470099028 1250 470097778 470097799
    0x51603111b0c0d0807050601060c02030a230727060e0c07020105070609060b0103051f03032f0106150927021603080f0c07030e041d120711 61
    0x1100d1540e8070a0a400c030040584200403640c0100301041402080b102c0640030303212030303245818504d00c01d40091004840c0d131702400d800015090710442c503080e1025001400380c00064240d0392110707051080308400148a00c1102e0b0960032020082c0640001013a1840080e00144000e9104012203080c0030a00b0a04a242400c10301c2050314000c40c0a038091892081c0c90355580c041d00060b0703010b000c0c20340300415440c1804a060204081a00540315011382a01e0070b00084c0c03203480905071300002030b19820215055101c2c0c10000f1138800d8507026614100c00080c002c486d201482c03c201c0c2d0784070351900d0910981d1142d804000603050906031180c11a02850b000c0c0c00c203410114500d80d51413560203084059040040e402d000c0c44110350407545046540c0c400680e6940b01071a0180c52110104d0700c2c5446000c40d0300002e19030745661001c0344c4645a040d62a84280c4110a08220090158a0020050701d0740c90342140f0b11030b030f000c010184403114080191901d0360b40740c0c03034030a034a00e5404403000d004480202 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470100278 1250 470099028 470099051
    0x31912230717041e08280c080304151d06090f0706170903040e0906100803180418023d0804150b0a14010219020a0501140c0709051603 59
    0x1900070382c0103540141c0ea03040e03840c074541e4885501d0402640107801491700142d1020500e81180c80b0f9201c08018210300d0183d0840a1015548542003040207402c1c03403420000600058040000911070105020000401019441c3ca118401c6120031400780503910000034046044c408010300030620070341500411142c1d0a0100082c030750f100324454a8010003012010581944050047d680a8249101100030078a4408941581c800050b0781c0b09400105400002c1050b0401200304e900002d040006e0305084c0150b6001d0100400a60100302e40040600e040d45005a80c2ca103038000c25600c00c3e2020603418090341c156480d90700d0121522404c0080328503403640c4015001186998840d030400c7c669805c100b100841038001d041080b44030355001040010100d40c0300c0d021a800da001c014283d0880d44400105481d5401c1200204000313075105240c5c1c04100415807040501c080e0710010a40b07001d082040703000300b0500d8031005030410359100c0d844404205da18400503038100a5100680303014031601e620310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 470101528 1250 470100278 470100317
    0x210c030124050603091c050909102103091a030103021008010302090c0c01021603050d06170703020906030f1c1b20060f1303060b060c0319122307 64
    0x10702c100390051a000c0b0000707490103420700400e01d00f4002c91000c05040024600001c00c10751141c592a17100c2d400800c041040150100c114000750b82410807103202001804d86010295801001e0460800c444060003241170f40c40d10041c0c4440c0340030300c0c44049c4c40b94114030403c0120710455809604008030f0b00010000341e5241d410f9190003841c5130145540d2803800303a0200b4013a1040c8101011036160242000d400c2661110041840424080081081a40700c0c07410f00c401c010038800701066548080c00c14005840c204a400380c0206009048850103143c02d0049411b1006058652160070b403c0541c00300c5054108280d4481c2000c080c251220b0404182e640002c00d01703601a0910200c1800214681070303031110300490303401000854480d074544585040a421200c624001100c8140c10701e810023a82d81840c00a652044408002a605001c40b810348081e00c050f0103446070301080351603241561004298480ca5581c50902d10030025541302c0c40160008000010b0080030811a200150030490b0005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 470102778 1250 470101528 470101601
    0x5030307050c01030209041b0810050102340f0305060103031b030c0b040201051e03010512070f03060b0609061603030e030307170415110307110c060a0c02210c0301 72
    0x1d080c01030f00e07a001140800d0041231840c500140303400c888608224025002007441d0300c220b80035481c0c1480c917a140d00c01203844001703800a0060b08240c621606402480c10102000380a600840420030207548520140c52064254001e83c1c050308440014401e0641c0404a090f054691803c00440400b070780d41c0007008840d4001c40684040403c9000ca01168420f108680c041c42c84013412072081000042d15403001d40c0b00380f00b190300c41e62101044403800d00c030105e100002c41d40f070f0001c1d000c241c0b480c544030100034000d4503503140d5000c803040102c0c468580e00c44000d0462001c0900054400880c90b05c4c020f0111030148100813810340c41482004049944a20000101c0c446149091082d8407a440c0800764401c45041d0001d440741400411140c80c01803a0185100e100b10f550f0f0020b140501c45000360711103640f03928080e08402d08000c01c1001c5802035200e01500e910103400008040d8404504540706002e400841070540c00941c010a240c0c6024000c00755109500102a00345040c03150080004226 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 470104028 1250 470102778 470102803
    0x302130b16020306090312060d0201020616050706060909060c0c320102040603090c0927021201051009150b03060d02130905030a08090f060406110702060d0509070503030705 76
    0x80019020860001000000c6a02503003e0101c40842c240318005680726000344d200d102903007113601b00081d194508010741c800c5560701038000c2c01c1c0e10f445891440b402c0304021816102405010000c002c001040703842214010440308000140068141c07410741c0aa6000c0181001040784030742c90080840e1850ba0741c01d4201c02440f035009221031350209800020406800e55001552012400040e029016001103d8951140c090884c516484102000c212010710341148905030506507041c001c2d1111444003108640018041c041d5a041c082d14142581c0084a0352007162010340c0d0100030301c280c1d500446a000441c65069481181400380025490000410b81882054541300300d006540b62480070440f181c034960028041c070000c41c105550350fa4490741200d00001c0804002039102c075030200381c5050050784840900f925840745d86603103014005c8004000107162040000c4001a51000000c1082009011011501c0d103070440c00700f414084140d203c64026002008039400080d00816070010360308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 470105278 1250 470104028 470104049
    0x80406050a0b031e16030b0115020d230c0109030f0f0905010206041203110a090e070504080d0c022d13090305160606091109030105150a05090a140c0a030606030213 72
    0x4c1810206501e0203004110355086143c8103070f0084180600d0904490583d207140c0ca940d0010840700e10226500c0700103602c1180040c00710f030907100400641c00500c42e41c41314802081d906003000c0848950031120a1a0101d02184000401041c00c580243ea4480010541d00b0000e200c1458040081c2d100c100080c00205038540510b082c0340a14001e40c05842200442400e2070b0321031407a00c00250010280d0f000e414440c6411358000f03480b00d8812001c6409491015003e400004100c8005480081b00418101d80c04800704582240030b00c0340c051850140100d040c00c84075001801c0c02440750509081c40d50640847c249240e010100f230300041295100e07610701455040035402070501200600c1960011560f103414005000c2c40c5d0485030010301602401140200420b8803034251030300c3d805404120285e04401c10403010006842c020f201e4a6000750001408105a045803e11120304801210f06903440c440c00724504081d198140714030005840d032410700314036260031f400800d05100c4443c403644030141b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 470106528 1250 470105278 470105323
    0xe120609030a080a06173703260a061a0a050a140d0203010f030b06030f0712020f09040308010602060c03060f210703060209180c03060f010915080406050a0b03 70
    0x3601e0744c1c0c041c500030440050030b20382d40641402e0654440e04d44084010301c60850418115607401c0e034005901070203a11040c00180d00c1f21955084c1e650300034921420300b54003200711811281403004e0341d030144a01b56648000035000c0c2012480c00114a00c005011400441480b50140d11030304442142c5d91300f14942003020342c00152074450011391144042c7ca07a681800840000392402020002c103082c0c074460300038080341c0c0d660301051699403004c10348150007075408a841008040d2213a45554403403030001c2e0103000042d00040104115400c2074808800140e90840104800c03076041c010150000b4030b4400c160320b1410000e0002e640044044507883c466055400c00b400030121145240c40d001c0b20090580d5841ca6603030a00e2002134222683c020700608100d140040054002d2035518030400d0805401030850f00ca9a05011030045079244060600c01008804a07005100204060380346038180d031020f910b89028074154007524030240088000741c2c1400901d48884d9400300321410f0700c01100b240c1042d807 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 470107778 1250 470106528 470106541
    0xb1c081204140106030503090f060703081b120f090609030a020c090c0408011a130e1f02070506010b0a030605010c0f1209050d0305251a04210e120609030a08 69
    0x4003610740c04102e00d158a8882c0000810401001501c07009608441c245034660200c4140016440b40440040010300c02c0800500881c006041124001491400c0c05040650000000401180c1a286590351281580c200502018100f0010b54440300d0031000c0d41c2003000454001e9980d540407070502d4490601d041c0065200703a50002a07500800c0150020702a040c40240b00c0140308200b10107184c0110340348a641030496480c3e00400c030300001d40d03400401101c508404c4100b400c00804205052040e0204000c0000c0744040007841e01800846012607540c0750203c0340501107803996440241070161045c14a408220841c599948082d0000525008140b041c03004071054189504400d41c0003101c00162010f240d403040c083d0040b9a51142042101005640081c541c4400a08020210750000c3c0c40001074060300030b9540d0f0014801c41428003d0381c8014414104815140101c600048002c1c14603451490b02001d5100441c499101400381400c0110f1b0341512441500303060000c0c0219031010911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 470109028 1250 470107778 470107793
    0x6050c0606121b1306060f0f020106060e01031e0c1805030c0a03060b0a030c12140c060307050703031e050402040f0c02030f1e0309010c170115080402030a0f060b1c081204 75
    0x20421130b091040100384d4071400050110f001443d003010015180014003031900d0300503c9008203403031280c1c607180702080c0020b00443c090326024030305c641c10140009108196138841c0c010031228806540761004001ca41e81c0c68100c24103990350080784030b40e100300b000ea42e003034a83c4003d40084c0da8000c1c4000c10003c1842c0042146035035507902c020212140408005014032000b42480c40c01c0b881056000c4403a044c941c1403607a1201b940780015031000c01000454405800395005141d2948a03080120300e0310a00d29400031110049520241441d403500204000c506d071610030361400d040d06080070401900c0c10b0744000e40e00c1c0607044e80c15002e602c0004001e155102c03841da031034544081408046c0d560380381400300203000e00700761104040450650388034040d401c00c1400905043c2c891885c1017980e451190801103610310320140040e40c040c040d0802d440c0c0403841012511007802e0192a0100304000c00d1003e0100080c040c104100701c01d40004002ca000540b0002110521503046200300c1d000d44981c104101c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 470110278 1250 470109028 470109049
    0x303050a0e0a140f040e070e1008101d011a04020f070f14012007020d080c010c090f050a12020f011b1202060c0a0507030f02010f020406050c0606121b 66
    0x591003540458001550f0214025040c0c0c128002e031644100160088140400c0c4c484820a44003d40c0006000b400240e614008040e44540282000708009507560229401c1c43c201a02d059680c0d6150b000a00c00300640039a80300c807042900000308021031404180b1118001f4441c99944129000144042d95500200c1981c11081d0058101001518289026407031103007280400381040d400d00d1f000c50460b9054030902c04c508411014070b03d28002040d400c02c041122060404c842181c030905c61030221081c02d02c1801302010882d1035544c0080e0521203104941c031040d9000074400c884800c030510020301d80c0c1240a076010340c15201038a559007900e0041c2d510f00d114440c05901215105524028000c0000b03541004c864503401359200b40d15443c031203040c203125a151803c007040b0104801300000744511192028158240b000040d6003480d45118001d03039200b54031500c009107002c50320031105c020a00c41690088000c444814030b400010a030292907410600e607101da800050400c481d5280c48921481 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 470111528 1250 470110278 470110307
    0x6080619080d02010b09090d051e0706110c25061112210105030a02280b0319060902031003140c0a1511010c120903050405040c02010b010809070f0303050a 68
    0xc80503240702e80b400a000741031000125201d003000d1000301d1040300010902c0c0c00c000415680b05460301300c00b000c000f11441085150000c1c0d00c1801c0211102042d880e210300700c411301e0028445a602c1306258640e03440c217a4841208600104c0401d0150400700400c8842001c8481904201c0310041240419500340701600303588107000000041d0403600740e03044849880c45040b408040030b28503620f0b10241a540d0784205402500074400c03008940502401607510300c569189080500c0e41d0300d1f1201225480d0f03800c140c400040b010100440041c40c01c03102d000c0d100142c07124041c11800e500c2d03c01080b0010840b28400075000d000154a0300c6000c9209204140d07900d000903124403041942e1307441105d076000c000c03d030450010f104113010303400303101041c0a505401c3c042961000c4018241d03003204d40083c0b01000c0d08806100b4200030000c0d5645582c040e1102c000c8d5140c00004074207610710005412600028009a0310782c1241030709200b640740c1110702c1c40643c0d4040c90038580301c108407a01501c050543c4400c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 470112778 1250 470111528 470111533
    0x906010c02063c030106020a080306060903070605090102010b030a0203030915040e040f150903090e07050d0f060611210a03020f1204050d030b03031903021306081608010608061908 79
    0x1480790040f03401d5800b8800d0020303110000e00010380760203a90785010a00a203030050304007003140c40200d0701440155810007402070400345070a01d001c0019260034185d9000c40040303040032032085e05070768081c800d680c03c0000075805411046100da000a0300da20540d202075103d440c403e042c800c0b440014006580103002c49403591b484508041c184412007440c0707020121400d440040c01c03c00130174101d00803200401c1e81034840400d110300705080c04101003030043c04402004400d002611a50405020b0500c16007034040c00010311905004000340600d091005a10306548032482d240000c0e0380121220b0a10071110b401c160700c4505c0200210045e101b860010030b5000d6000c25050580380d0300c0d00303201e8025440f40d0103c072100d40041609806030b906260f42d5560541040c070020110070896a09450500b05510b0010318000303242c00c0420030244142c209100140958080109500007040d40c0c800c003840b541000015589804170081419400070000ca0140c000c024005c0d0048040e4000314000d01960b905 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 470114028 1250 470112778 470112817
    0x7030c140a0f0f020907030624120c030609050601091211041107140c121536010c030b061605150705090a14011403220b0105011d0906010c0206 63
    0x244200043c58003201603104814120100c0d412034028807039a000c561030851b40140d2047c203590310341a001f4117400c0140501c032110000080309802c0b0705c03940c040c0c854142c400180c2d080c24100c041040b034500900c414140203074804240031000d4110b20720035400c0d80c030174601c0c1a80c3c0b04000200380509007207080440740d0400800c10004001d0140c0152600003902030803a0340d0100640100702c0c0e50020000a540e968210307690040130100000321107075000401d44c0401c120041d070b04600c0020b207200007424940d8020b9003080f5000e0881c01703020748000582640b43c05d000b400f46010000d001442814120b200a0519101c030100700700041c403841d00702400300c20880c1218503140d40c1c0685944d016400f20b80c400c2120080100d11645950030202e103d8006030b51340c11000c03a50340b80400d500e51000e0103000130a540d64551006070580f00300c1c0c00c84401d210300300c030714040d514001c005807082e42c2d6100c0c1104082200010000b96480e1032500c0c545c000340c02d10741516103290310300205441d0721035641d02c1101d07a80d1920 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 470115278 1250 470114028 470114033
    0x30604060c030f090c151704050a1e02010503061e0d0507090c0810060305090322050a0e1b03060d020901030501141f060c061e060306050c07030c140a0f 67
    0x6100201e0584151014011041d2620401c4100d070050ba81c01442d180c0c03801d02c28048806110350702024010b07a400e01010500803840064550b05003150221101e03400044501c00b00040300351000c100c80500608154104510b40c00a0701e240002005a4044c0030000060048540482c8144030030080182c6a541c1c8a102820321640300c00c186d016441c0e0141c10702c0f41034010305114140b00d910a2443e005622105820300d04114080d00c009880e0641c54803040c0804800394103d4040711801c01404020103540b43d1404003480401d0f080703030348a1440c040807482080b00301c01301401550080600d1042d96a6241e94800000d200761440500203500040140008402c01405500c0501000761403a0b4412266984141701954618140413000e44446441c1003045010301a4010180c6244141404200d411500541c015400c00300d0800c6545651602c0013042409114030545412000c0205254684255038401034071051001800401610303a9038140c114a10080c0554005941d100850300002000ca0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 470116528 1250 470115278 470115281
    0x8160f23060703201b0d0302011b0c060b09090c2206120203151e06131118102307050106060807260f06010306080d1d0603060f09130203060406 63
    0x108074132400c0100e886681c207400a142502d005418500c08007403080c1c28140080522601821010740d03480c0d010420b44410b0640488119900540e03400114611078200703082500d007112401c1380a28070410a002c1c5809001c6014400352505403090350f40b081101041d01060040340d00d44541300c42ca4800049507403181003604c42c0505000310300b210b2501089807003484a81000f80c442c041e040d044901e104e0104601c003818141d108000500c89480182c000e0012002c1e26410001d1110801001491041a80100035903110061081c0c5018415081410000c1c109040c1200c5400901c1d60a241c10402500341300c0803503c020394050028010319540d4100981403200c20b69016005c245241481004400d00813081082c0b40f403296003000c0151203003440c400c0350031409032059040503120a404500c404042103030000c0c4a4050b550070700039401c040d05500e60000b4040405102d0002001446070580d039103510120a01411140c0040c55180d4803210205071000720700081d01401a1001c10081c400c0a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 470117778 1250 470116528 470116547
    0x20a02010914120912150c09010f02070f090e0f01020f214011030c0102060405070506030705041203030c1d03100b0a0e0f0108160f23060703 62
    0x640b584140c51001c08911074035804281042c503042c040a000512440c9020b0591002842d820f01c1510015850000c03140550201200c0d010310031800041e5102803540d0241c402c0c1d0b8400003d10151000313a060104400d4004070601c078180302c080d01c5001401008500f4070102241a901d0402190386140f80804041c080d080034402003500c2d1040b003481c50038031040810040c842e000402d54181410038460f004a1001c00b6101c0152260580e0010b400c441014040c85000841c01802d9a1041c11200000c241c6003950141210741150006814072001403000182003054400441c2d80c181c481d80ca00c5803c0f641070040341d00910050080d08851001d05805600c034495802d0785903200a00c201821144100c80101c2e900b07800d03019840a4072402610042d03900004c0c2109008000c012419500c851490501038240c83e5105610703107540040001e01400c020380010640d9100328500b036980b8021007031f510b4080d81c3c4203044020b030301d011105102450302c00ca05100e10400401c220303110036060800600d20842c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 470119028 1250 470117778 470117783
    0x3081e1f0608040c0e040602071b05091807030f050a05070603052205030306090613020a081801091e030201140702160501030203010b07031101090206120f0a05060f040c12020a020109 80
    0x40c69502040a5200314032061040b03401054844107146041c06554104074020400d59540e5400d0100e0800140c1d41c1c1004001e031740c0c113182100c031100d040c0070030001000c0e4042e182c4201e2211024140066080202e0444122a0054040200c004d45810b02a042410220004000303001d01c6d10046507568044c0e104a000b880e0038480350701c02c0c4004030700060241040b0310001c0d1003980103100141c46464400e8990340e000304043c1c203d42c0a019010710700300c240e0f080382d0500340100c4e11003820094000b00d400003114207900010700a10464850351209444882c0c00003605050004250a80c0140350003500034030300703e90840b4082d03005460700d00002501c602c140c07400f55040c1702d400800011198401d000303480c140c60113401c0361840c2c01c5491f0743c19a02107141e02d8501c1602d54880885401503130345c0501601c82000004425a41c81c0340180c0b600c0c2460300000c00e8902644d140209000e030742d883d00e010890030160251800544c0400c130602c1510002d040c000324100c8a4000100c4006031581034112105052 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 470120278 1250 470119028 470119081
    0x30d08040b010602150f1305070612050f040c0303050703030b030714010e19060c05070801050c12090d05030105060309011d030438090d0506070905120a020d03081e 72
    0x262078080c1240c80d080300784e030040003c04200d00071404004040300e06c15041410046001c0e0040402da4078142894442d034414004114030001c4021600f070940240c80d440000924440c901d40740c6660303000c1c4c1500305400042d0402c00302049080800d800b0303502c025200140101181c3e0b10300d5031003155800d0080080003031350004069901e0072070113007840c5401030809110010006e02080c02c00d40c0803103540c0d6071070109580302c1c40f5064000030540001e209060141d40c5044002e0b507110240c00d26031210403006000c01a00798081a804001d069001e01900e055480403503c203a902d4460041250141c801d00a1041c20f544100c0c51225080400000174000c540c81100600c250785008203951500400d026400c51012250004100005908000404e40c03c01c000748024403000c0d80da200c80c1d00e410b10846691000c56a000c10501907480c140e0342c070700354000b4518010b01d050242a4081340902c0c0142d030b07006081c0240b0201040700e108000d4100d184082c0000c0d0f100185203001214000c807092941ca41c51b8401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 470121528 1250 470120278 470120281
    0x16080603160b0a0e040509250b1c050619060f140307080603010b04060e0606030405010603140102091f1b0c1508040b010504050606071407120f02010228060906020405030d08040b 78
    0xd040038011b051103203030301f000541800221555210301e0b1450f848001d5000300c840710808508900c12030041d2031421120121120084429098207080b6480606031510071302602400003202005448c4c0c5400383c1d0031600d4412039517600c1e4482038607488003000100c02c010102008100301c90f98052450307841044100c000b400a01c2c0c881c01880304954040c023621034064007640006d00d0a0811a006603005032040f000041c540d03035681c841c02c0d290040c2c0b1610b2445e0b6500080d0150f281d00e42912244140c400641c8020200c1160910180c00e500e2050414100b82c0450108903003400002c0141600078800a21102030708a84d8201c0200704100032501146e2080340c0c4000400c1d0307401e0601ca21882608003512507460806a0307220010740790108410b80f00640318088d008a06c9085141003401e170036200d1418011402c0030341c80060b082c01b0f002e506803500b622400e034100240007541c5681c03414407a041200000c80014034140403000e8801c0350480390701446001c00d24040ba45c1c1c8150403620490090700250101d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 470122778 1250 470121528 470121557
    0x62105060609090a0308130501050106021c031406010305060d150f060b0a0504030b04060b04230a0b0a090b0f0901030308180d0f200a031206060816080603160b0a 71
    0x10110300795003550782039010382d10113000a4081c040d0305401c00c0b203041e0f0500c2c0d00210b5644550944409801c4a401a0017903500c444c4540034465030145105186e04050000e00600900c10541810080c455410035407070b8408526152a101030a410442d004940c003450016026051805882c031003002441440c600080000c0c40fa00c030320203035001315100380d40f240c0c5094076545813401c401c1c070302030800e48800e6600c0301c401c1000d80e50b621540115030381042031341c4a02c0103407076403184c1e00326002825900c181d4101042010641d81d030300203450a0f510010790002c0e001c40180085164203448240458001046a001000789500146a03901c0703489885807064080e400b444c0700703544401494245034045407805002130405802005070144a94051a81552400004000134940216000107602047e0902903560441038903004c3c142c040d00c036900b440c1c0d04500f08414101c80e5400100d0311a01000000d10104000e543c00344100341401c901441320b4201c0716103c400300f840c240d1006505c0c1000c103c07200381074002d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 470124028 1250 470122778 470122789
    0x1903111002070503030a03091b0305070e06100221120109021305060a1d040b0418150e0309090c0c0d0e131109040902041e022d030103060c02010621050606 68
    0x1901c0300600510f0501205c1c18058002c8c0001100454901604c840704d490003030354a0001c50015405800140141c52400780d6001e104070000c0c0049028804020418141d503800150b65003890441c1e101c0c41008414a00b040080c50040c00f0f0742c0760381c880004000107041d00701c1c0d0700503005400307510b0000301c81d06940d14200402481080845408a210485500c10544c0700b0541c0310303006080944013003680011100050221001000401840c141040c160402d004691103050702c9031141030030420141c00a094000d0780e0303010b542c0e59240301c0d905c5c0400040034642144140c0c3c000001c0e150403940051000c000c00762040451003103403402078201205541c04203607640603091840c000152140d00c3c02c1e03100000c0c8005016208030030790300b0981790a40c0e08010182d1044d26110015849001600d59840380f014105048007a1840c44e030b907100707102c259003124079548102da0440b40e00000028001c0801da109078050b091590011020040d9081501e48446240354105074042c8110f003039840e0343d0344000030441c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 470125278 1250 470124028 470124043
    0xf0604030302102c060a0b190308131d091014011502070e0a1508010209060f03040c15111527070b0706090311060705090d021903111002 60
    0x41c010b0f0301508200303111000700e51000c0d01c50211907000408030390111688400c22407490000e9440c81e0311200401c40c1c486030340d103d08095160201d03490740c0740b119444514210781466001c05404003400160b10002c44914801c554000c01d11030b01c00000301140013265080c61030041302d07059940e002c0c544207003e40119611403818440110b48013a901c990a0100f00400d0001400b900340c15813203038603004600c1d0203e182d00700348110140c9002155280540c1c03880a5504240e5004417204e03030042c0910b071801c0c0d5a41050325283c4080320b40d490744130340c1c646c04e02000507141c42c2d020418103800f48030500d4850742d01c083c800c0e003c07582001c100c2d002d0010015808091180445002d0201c0c01d813401d6040c881d2181c45104480c420391102180c051075100e901c031a07400c1c0d020203001c0301d0044c3d99140f031104040d006948410f030401c10740040c001e1860304c0f400103841842114081849200724884010840d034130701070f0f8074209258125240107103544a14081c0000c00c03404050b5407091240d085000f141e5480020981d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 470126528 1250 470125278 470125283
    0x4050a09120306060815180f060a1212140d020d090b011211040c020106050301051005090c0a05032205030d0510080304081c050403140a020f0a080303132d020f060403 73
    0xc070065031001d001054a86d4001402d5501005c903071810881041d00114250041c420607920a14130704050003000801051540301c0540900c000d400c0c040030850110404000034803e09250281401203890306400303216801650380050310120707110f143c100142e0300008505120b9012813186903200d107070310903001c01303054401070080c40e00d2281654603040c5900502c285880c41e00021420303541b60800203095510441e070b0344001c1e01d0310040400c964034000140700e41020200b402e852070710081840040c80d500c8014102041489000007070707140c005c0345103800d4280a0b00a0140c85d02c410201481e000540f00503600079a26070031851001c500020040112012114403c009140c008204c010f201c00c0061858621030500c101800000041841a1540004034689501134450071000d4410402d030714860681c2180500c0c1000c0d000d129012000003103c3e003102513450384038900d010f00c1c130306401032400b100608240290f0110380c5410403580d414403240668405c0741c1f90600142c2c008140982030080b807101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 470127778 1250 470126528 470126537
    0x10801090219031d0a08071b0515070201021606030e0d0813110415030507030501200d0b130e0309090108060f04020d08040f0312020613120e040b04050a0912030606 72
    0x70024083c0a90301401e216081c4001d00c040c0000c8100d4980d050401c81c0409075242e002c002414010040c000c1803100001052040c940340b428182000309110314290300e000c04c0c00000000c1c28105582c000c1103003030009801c2c1400c0040c07031034540300f000f005082c2001103414144964507a440d459401595454030030000320001c0c0200c0c1d50b1030f464011040b038042c030700250001d9940355034403406e410343c0b00500065030090006041891131880c009086400c41083c0c6487c1503100d002d403512500b0080200c913544010201c0202d48414080c0c0003030042104010880210b500c1c041c880c9110f1040800501001c1c40200c0f03079404103a07641d000c81c40e203d010403510720388202049800a070051070301ca00c0c00c40c1d4443c05560a00c0c2000d40350814a5068403558006035020481d115642e01c0c196410413800e0781c054030b0180c0340c0320003c00a03654034040488451680051041200c540081070f10340f54412508104010018000d9040604000c002445280b80c1614600000e07168001c5550081c000e11085640980d039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 470129028 1250 470127778 470127817
    0x303020d140d0f09021e01350403050c01050a0b0a0504050112060908070b090114090c1e0f030a0b04030f080408030105100e060c0f3c0307020604090b0108010902 71
    0x2c01d82c00400480a200c8031140d030b00c5500e000503032108000d91241c0182d611900c203155400c44005000c808101d610000880d001034010302d80213034124481c00160390f0f400410b5072241c075945000d0310140140b89000d1031542ca00740c02c200c115403054024050007101035510960454a850610082c1c078402d0288088008a543c240000210f80354011f102d8140540c059030b052031100e0b80e03803202c00e107410745154429039101c101c203218103130440181c00c3d0800050700040c2022902031010408090070031802c0c0c45042408120904c6c00d171119004081c4a200003804e031101d14815107849180354906450a400003207030030749480c840c82c1c061491389000b203412880050450b03180004000c6000703001c9241c1d0041110804180c0700319121603001d012040070201c090061303400300d0650946407044075200090700100034a80030003008140c5d000c0c03c0090300798117295010344072076201d018614841c0142c000d40040d80014006034a450940c032440b61704100743d03244a4183d99405401c81617004240700e80c80101b000d03d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 470130278 1250 470129028 470129047
    0x190909050a060c031a0f0303040e010303080402031002160210020f07080f10060501050f2203202b02060708220b0f03130f05030313050c10080408070c080d05040303020d14 75
    0x400141c481b500202243d1800b511402411a91030081e84101d01082e062418002103160034003541110241000c0b0442c144926082044201c1110710300107409000302542c0c16401600c00c2c400354400610f1801180c0d00d45903a00320080e6108040014020103000d148900309030f682e2180141800c85105944080c01c0501034400709400b43e01280d03201d031542c0042c81038800340c0300021102c000158011441c5070381540310030b6205480b40441c8a1603600c2500220400075004400906040e00c8028207148025041c00390b02c0803c44500c589440540b1000c004541d129a000b1070005000000c805005088840c503681d207003801840c01041c10030200c0308414000a04404104458605414061401d001c5100c4007a00e41c541942d01c1a6540c5900540d220352210a01c801000700340e4030f14100f624010069207204c1001071800030003900041048134001514030920081c0c14114024050000035648ac8000a8801800d540e100e0f1004401501452120000960082da100c0604468175002c8519006500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 470131528 1250 470130278 470130289
    0x1050f180306010303030912022107020a08060c070309080a0201020d080a0b0d050c0f0a03020904080c0f0d082217090103230604060f030302030702190909050a060c031a 74
    0x118600840142030260a04056a0810503140254001d4600190307412580c28803106a0340c020380180155413000150b6070036101c1020301240000b46038025141c4a4020b8130025102c51042c2d40401c080d4030822084c40200231244e001000e40f1803081d120781222944d00d5a501ba01c1e04040d42010f40960000c00d50509141e01410f07070140d1000744080000f952108200c00a07221110861042e2543d0b4403a400c0420745082803407055140303460454580401510b15800501c41c03243c0108001c0180c030700810329412804040003080b0f40344903503005480780c12458282c018900728080b62001c009001000c6c0440c03415444000511001b900704411f440f401084071640002680000034680c100340c4e44007244840400d40c030000442c400401c0301c091095040540403c020340c0c0e1540c12400083e44503003c00c000003038001040b104101d5054491080e254202d09000900b0801540152040f50801e0300e9030040200114a810036903103d02404c00c00d410030500100c04407013540448090103003008428807400e1410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 470132778 1250 470131528 470131537
    0x706091a071a0a06170307050322050909151608072f1f020f0403030c02210d02120c0714040f0e0703060624210e0c0a08010b01050f 58
    0x10311014180d21070200c540c50410802140e10031480f6a8610301800b000b0502d0340c0840503a45d01c032009500f4240e0b5a1282e94592090001907040c0121007884240951004480b0100400008000d0340482c905980f4440d216582c400e04100d04500c2d10001a50001400f600c91034480400d83d6002e015641d03550061f40d42038942c42e00c448540140c03648044280101070b4208903a028080082c00d510007950340c2c0e54010514117018980c0e07550041c800c04c0521003501007940d0403039415281060b400c61450011945000040b0b1200416041c0c20a10020980000902d05001ea210754211000901c0d004034600b864003c04030030444940240e50100044841810f075820031010040000640440b107903003000031500c1504000c62660004101001400407900c980c00003810700b081103042401c40020070b1042c01e0800031a9034184440c07810030744401c108901c4908440d8000c01e404100050760f0038405641c9104131030781c0610541180070702150301c18040c028540711440686400c0d0400380d24103041000d9411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 470134028 1250 470132778 470132783
    0x408090609220617030406080403120b04060312020c0f060d0b01023c0609060703022a0304140411092b0b010e0115270503031b0706091a07 61
    0x10b0300018907100000c581c600b99000c000011000648038603007804034080e002d4008285030303290018001000307415009101d040d80207a05103401e45040d004410420010221380c4181508685491804070800c2034144070200c09490035000c48405c20f00010070000e00151006185820440c00e01c403180300c001503504612542001401505c0c42480500610504508010300c02220009042c803091800d22030307507508843c10101080900200e2a042c0b20781c6540d100d009d0300346802c141c1d000a060604581c0c1400f03144000c2d5070603480400000703464940300d6032070b042400b0300000007140724507142140c0f074140300c7e141c0d204602c00c1c8800d00301120001004a00c4048221444141640e003985295403032407200000d408a01c501c0141440e075042c4840503081d1103050300086003000820441e065101c2d04800c0c6800c0707088410603108107540100b48205a21159030b40415050311020031016030306100a00c45140301c0022000304c41071607540c1c9601b112220428810401c80c090040c0c4442e20b030158610080c0f00803070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 470135278 1250 470134028 470134039
    0x6090a091806230108030310031e0f0501140c130510090b12010e10031a060102010e030406020601090c0e0907080405150406020c070519060c0c05030102040b0403060b03060408090609 80
    0x354542c450205443d840c801c90380c840c8100031007418806103151525805040b10000031810752800c444800114411400081c141499420610824500048030850010344c00301c40034000410515140e8080d08900b41c45025246403030002684c0c0003100c0c02501c003042500c40000d8030040c43c040501c19010381e0300c4003200411144010118040c09518010161005001030599496140620f00b419900001e041c114054544038001c0002c40c40c4441c010342100044440b6840301d8840000507401000c251880d10244e0201003000162a900411703694100c0f07080040600c0130305210b406c1201c051500c000400e40c030a0904000c141980d20070010168464030480032915030001d001006200d241040b1002c540842e000280b00041090134043d004c0100030503540844403401051840d0600304203030140c1000c0012060300b910920003c00c11074002400c015000315034490310340303013100c0c102e50107400265030706410804c0000c02401c001540621550b048a8440d0401d00f2550800400ba03100464069111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 470136528 1250 470135278 470135321
    0x3032e050a06080f0a0204030b0103020f1810051201091a041401110307170103120f020106030605011203090f050a05040e03120703150e13060b030f030a050a0e06090a09 74
    0x152111206540075200648560f4110310f00703440405143c0e90b000f041503041600622080000940014a00b41901e904940483c014001c1c080032484078401c01d0b0302419030704058810700006008068000302a580207940d00c281c3c080320000d0060aa1b801c1d20300c010714000d8642d08074041c103c1380c016007580240c403a08566015441d142245400e440030541d0343d80600e00e000003070210513500041c800f220b181c0d0354070946038030358550f449000e041c401401042c000e100704140c072000e10034400e62054020b16400f4030108010b5031160000040d04041201c100c1c08500d441e04081002003c0d150b00c1000c48400411000e4041d0605040c40050034600c4400701c0240701c14096665603d01d80c21030306125002c375a500003032141c0e0700209001d401d99260702c810405456003040c4000102030140744094240c09c010041604503410001c0fa01e0202c0070071620b041d80c0070118070905d02ca40c0c01801011a071009036a2188001e04844c2040700c2d5114010040e82c1c0100c07590001c000c640d000d134200f00010215a004c14005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 470137778 1250 470136528 470136539
    0x120d09080706111306260601052a0c0306010e040f061d0a1104020403050a06150305030a0518041404060509160f1d0402010912020d02130203160203032e 67
    0x5850403041c0c250b5043e42c000c10b400c4602100710070036a0040410b031600e20100c11030700303195482011001c2846908880a00e0028955900400c1264262002c2c0c25403030390442c6102d840707000c00403207860551006001c0c802c1c0301c0c1c0c50740ca00000c0c6181603611505036280241c480e40d40d256017066100c003040714550303100c04101c0d40c5610244410540f5140b100c001c0c289090280c5031510b04521401031032407040744180002d0001c60000181420410b620002c0000c82811400e081c2e064604035520080203031000040401e24242c1c8100a01034800c0c800d0451100d101f80e40b030811003075800310076003030241041000000d004208640c000c0d40c3c020446106a8140d0981b0890200c01042c0a400400681c1c60001b13041182c86814400e1980c501d0110242c0c504d1401c065000078514561031040745002003a010480095645511810726001d500521040140070030388002d002a400c00c4400d5402c0d00049282c0c00c02c1c43d13001100300c030300c104d00f800407003109242144148081401e001895031001c82d20084040341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 470139028 1250 470137778 470137781
    0xc0114010b031014011418090615090103050916080304090f0b0904060921020c2419030204090c08010305010b0d03140a030b09040b180703030c0201030b0105070b180f120d09080706 79
    0x7c0c040c42e541c190007820044040c002220409030516001d40c4544480508070380443c0296519460f007440e01051580305c040b002440e01100320304a1002d140480d50000c2c10381c800100800480d134425400f0f000c040300807514201110341c001d0f0010b4001c1ca00314002000180d8590103014294412903502d00b403031a0000c4290b107503401035800d060250f8021030002e003940c0f4240d070405422101c8501408950a03a03030036040010f0141d00c071100440e201c1a0300010304039000341c05450183c00111030070403824201e5600140b1088080c0301c00c1d50703554a880030b00203c1381000c850b202503903030705a200c8190400c091035140a09911001074242050794440700c1e50b203250b988840407405180a52000c9a06003000400340c48042a011980c9181e03512880e070030030019400071544000243c09080c0010990316080050340c0c14416034100404043c840d40c10810410392144051802c14a401c080321001d18243c00800d64441d07050b88074452010003405803d6510f022078002040c0c15214408183c1840c669507641d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 470140278 1250 470139028 470139037
    0x30f0501060e121b0d0f120f030f02031519080102040305100b0a030302120315030a03020a03020106090216080f0c1005010e0c0412150605060c0114010b0310140114 72
    0x25400e102214110b25050410940f6499800d000e0301100c4001401d1620b120841e03403e05018151041c0d0080501154511056000ea00100750003041d102c0454010010300e4507500b2000030910b090702841c901640c51081d2840340529540541e0b1a00c81e1b4403c0140344580602c8182d41e0381c0f5203400101c1c0306402030003e84022741c03080d0001c0c06030700800d540c2c280648080c4030055000e400c09402c10000720350f00086510b08848034242283e540c0d03ea1409012840d100b0040341d035014030941640e14201a4006286000140030343e0003002166154140d0713005a20400500d00300249113000c404000c9800003000381060440e00807858907101703418100d42d04207038a0303028641d1815079640040140241082e02d2550101e2000c00f180d1929080c201002681c503045100906440c0e0921000c4410003401c0d4402c8001c2c00005080b55124003203004420b028105100d640541c0c01d00c900000a0303060a45c1040d2401510202c1a01064a00b0140004801c8801c14401c07030421128049103043e400c984c40081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 470141528 1250 470140278 470140289
    0x50c0316090e01020a05030a05072a050706030e030901200a0c0305010c03060501052d0c0f100c020705060a02011503061406030607081315060b031b0406140901030f0501 74
    0x404105103058005811502c1c1d10141c42203030f0f40108002c00c8502c3c0e00c0001c032035001490080004240c0ca8042040314540d4009080009500d480c2c842c0d034a840b20f05658a01d0514407510072201c080c2c0c0c803034508400f6070391945800040d80c2e00901031500d4a42c040c10302241e00f080240c820302007a40420311018034040d07540e9003d4440c0d000d000e1003481844030a02032419031000508003840090f1404000034600d01c260121240c511480d0860995243d14403404404881115141692504070703c20480d40c55182d400007250303052096079900c40362021a030040f02c0d21000036801400e1a03514103400c1c4010340e03000d840d0307810440d5a01c01c01c08520a4071400014041e5009840001b242e06940100150000300641307103074820391082c0204107110341d01c07400343c6503c1141802c009130f5004003032078104000b030b000ca250509032a041580c0421a46002409548100102e4200d000c0700c403240c1800e03200c0d074410340c012600041c2c1a01b84840503084480001c140c2c05406240000d07808240c6000c1c1001c175582078011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 470142778 1250 470141528 470141563
    0xb0f0c0d05070c08010603020a0e0405100f051005010806030604021909050112033e07260c120a110a030203010f090203010f020f16030e06040f03120906020d0309050c03 74
    0x8000c107000360b10310340d800a0882c0b136000b001a00d042d1340000d5003000f03051103842104408440003408102041c01080c10301804a40c1c28026401c4100c96040902811a6501c000380300c0a00001004d43c0f144c41418010703d8041c016004686031a020b00c24070100c03403011741d04036001000380043e40558030b10455000b03184510842007824543d01c0e00810b903107030070748405058010f141500070050111079981d2881003807421030300c001811178096150400109900c1104020541401f113411442c120030482c90b104d4506047d2408120320030200b0128590441190080f80d000701014800600d032955510765103a001800e818581c3d079241c2c006070960300c4040000e02081d88940808003141402d00078a030100c0e50010b001d5051a2580c0000281030251040b4600c00341c20030348103071703003494002c40c5414441c01002d84003d6540d601c1e4a8070300300b084160f1008903140700c10102c1e020211072140c038883c01924160342c09400541d840f41011009000445001c0d1911300681c2c44030f1045d96400c12503c141103440425 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 470143884 1106 470142778 470142787
    0x9150c03070f0306081605030d0c0b07050703021603150e031e0d020d050c1803030702102708070e0901090f0f110312190207030201090b0f0c0d05 64
    0x2601c2c003801106e102c1c01040941d09002070541e602a02110f80d50381e0806400c5400307844591002c1c0c15140c0040208003840c1c850001410709600030320481b132421406031607680a24549910484580805103204140c42d0b40c0d0740140440b00704484007541c1890040c084501f02604544a07070600208000340800c048801c540c19102183e08600c002c00c070610789401440403d501c2900300d03075110311010782280003915001044494066014041c1d800342548400140c400d10440d40c40c0a00c021004212150300c0462182624021b018500040080c10700e40301e00d0151410010b41520300c170b42d0414410001140c48207030a08040c44d44946104240c1d0118140303441010074141c0c007240e05000b03c44d444407146036400c3c084c103c2101095024280704001040907030b904d02203484001d010031040142040151540b40240044102c407045080c07030500f031260140c0c10f28030380c502414023103940440d = true := by decide +kernel

theorem cover : BRFrame.Cov 469964028 470143884 := by
  have h0 := BRFrame.cov_init 469964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469964028 ≤ n) (h2 : n < 470143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
