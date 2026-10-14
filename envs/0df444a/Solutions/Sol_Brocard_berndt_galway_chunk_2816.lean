-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2816
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:45.072716+00:00
-- url     : https://prove2.me/submissions/0eee81fc-d03f-4d9f-b476-e871f020ff85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 506294964 ≤ n < 506474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 506296214 1250 506294964 506295017
    0x5280b1b0408070618060c0b070e0402070812070f090305030a0305100509090705040f110f0d0b091005030106050609010c150f06030c030b0a1506030c0e060403231c 72
    0x4107031030f203681c0d45400c081c1001c02c0300c041c600600d0210b030000260f65400f94000803a0143c102d214000c0700c0d03503119070032140c140140034019130240c0c1c00d214101c04500b00d41c0280400000064002c2035070304048802401c480343c1c180c240000c2041d0442700348000f4002200355031390603949050100c2c4548652403040c1c2c0d44102a003007540c200c440c2c141088268180018010202c48040d54100007034095202a0f50680340304400d1100340c02e90402404c40c819017407c1c02050806029100000c00c4100b03080002c0000340f040c3c4007907418040c00078081c08145030a01c58031000f4001210110b14014003540040c2c4071103490000508000b0110448181d0a2081d4008958107000072504108003a04c81c40d24440f0b4400e20b000a49646445c400061151080c6100e094480c02c08a00301c40c00151030110228064103080f142e0500b00a00b030407261001c1e0b102c0e00090009035100f40020351115a507002d11122070034142c0049810741e841074a4004031304200c000030516a0301c9034500003440701d13501c1680c2c9040c1401038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 506297464 1250 506296214 506296229
    0x21c0c0b090604060510140607020d0506191a0906091f09090317280902040216140d050409110f031005090106030c02190201030b030a05280b1b04 64
    0x2181004901d40c0d01191062180e13124400170812600e031603c035240541070358060700450b990b40c440d43d010546010405040c03110b01c001c000034200c0440f95143c50814000b0340d032040c10702e210b26038458010362042c012068403010040c000040c51904500062500c04080c00c118041d0344a2404a405800b10309207040c1144000f070b0240710400d0355100c181c4003c02c1e04810540c005130451440742c2045c40780108040c09149840c10603884803009841c00c440d00002e20130000c003810380d0340d40d01030016101c40c0050040d41940b0360341c01a0b00c06160401c04011611000d003072031070781c00c15610080383e0f940040c2580c06490720004002a5900d0031502c0000d103101c0d01404182c011070110030032104000e04504842920300580b4901a01c5c1d81c0c640c0c043e0203583c20800300c440540c04c02d050f0340752050302c80c650402265005240200300440302501086c1481c40c00d450a07161034010702228a02e84a240d8201301907211540d4014000d51400d44800f045500f0140c104c2e4a0548280e41c0801c40398003800580d030240c1944d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 506298714 1250 506297464 506297483
    0x60b0909060601090e01080607050c031204083f0a0603080c1e070303090e0709030f061a0d1a0606070804120312060303051e0d0e0c1807021c0c 63
    0x300c000c0c1070781c0d0740c001c80700c950000300c00c40004910b490282d091141210b9072040240803584440c1c0342500e88d0341150011074a544003c0c41542c03040c0400c403a1090090f8040c10b412540e0f516021a215600d103420b10030620769031340c0344041c0c1f0360b0cc403a402c00a80c2d007207514026481071a12929030320780144c1030f6507002a0026502040c08801008d020580580c1c24808800c03811010342d00d41b0816480305807a02c00500402c18003802004100c041e081c159500000718648510380c0d80e26036584400c0e0010085007a128036035114108180084035064901441100300d55102e2401c00c42c0c1e1310704145091212429002e15021400304005858840030744000b980d00c103c100f600c4985401604410f00c0c6040020760008200c0380b181c42000940d486141d064a070103542c0e41c3c0c0f034600e2015496000c9110701c000e64172201c5082288410305403251003100c403000c0f510005401c510030988104120f40c2441d00d0000340c0c25001c0702c1072005e000e80024110300c02400c0424880e0b40b0030890141500e00e444540d8028100000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 506299964 1250 506298714 506298721
    0x3060f0123130e0603010902060703030209041d030304060b0103050907031b03060509211303030e12010e07051327030e03030304060509010c08040210050d090c06031d030a02030403030c060b09 84
    0x3078041c0080207945a500c40b01c00035036980d5017050f003616000b01010350090020003001d0b0100344280c0003044016000340021031240c8843c24640700d40d030410901000141c02c080240000c002c514000c1500000c001d103014801418158203194441d51030f8407000f0a00116900e04800c100007986450b401580c109504001e64600481c0035a1145005010704001d4004041041e40100d0b541059503250100031003100c0d81c0b21b045540075182042440c0240358004940182c0500544003401f0756880b02e815900074084103480c203c1072010720110960030340f21050070321100c0502640300b41d5100c1d000419080d004c11207400b00381010b0300d207440311400702501408000108001e102084e0040e41c02820981c0c0208103049165400319030051050b43c0003513000862010b60b544840c4031314090842d0150400002039140b101e941c0355600c5e0134581e4000c60120b602c864008640211140500c440401460080d6213031840f0410025205d2050303000050900091503100018041e043c0d00c10381c600040a48007582a09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 506301214 1250 506299964 506299987
    0x111309020604260f0307030f0309030504090509030c10201204081c060602071d06090720030c0c0906180a110f07060501031e050606060307030b150307020d030203060f0123 75
    0x1b400a90305401007a03883c04440700c254464410000300c10b030990744040c10f00d0308004503400900703000351642e00184018020080f10003002d000000c81c8000910000694645850007080c0c1180e000a240c0406c02e000c2c482d01d84078000100155074031590008002d5681c403038001c0c0d0001c1840c0c5c079048060202d4500b45000c104550000352a4051702c2510006e84e6200201010480007900110f0b5020340101101c0d000c114080d025000d0503458161030460403000000072a0400c0c81d541002c1038907541c82e030002104000a0a03c0c01c0c07440c2e00304405969031001e40c2c0010115610506014100710051540c0b82d0b146101c641c880810344842001049185076a0f60345410484082c040a0000340c50454980401010070b0b5200c401d028400b80e4020080c02c0181d41d14010020340c0e400c02001c00c018540c662a5000a82e82d03240207410b441120000080c0d180e08000c0c01c000d1403c0d601c4c140610600d40b040091107000c7d0307203003c0320160768882440c0007090518020381d4a4860020350a82001181c1d000c200206000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 506302464 1250 506301214 506301217
    0x1b0803040b040806010f03050a06050403020c04150f05011815020a15140903160602160804062304061b020a0f23040c0c02091b0403111309020604260f03 67
    0x4810f54422581c490340c035401429005051440014000e030b00c4000980001540c41c0c0040341e0280c041e0050751103021a00b00490103482901c1481c040310301aa402c18002101001e0a2101802c400cac80c02c814602185038590401002034000d21100701820300106455a200b04034605000d607009106105d135060301440800640710641c2e21303c40b000c00c0075001403c010320000a5a0f46c58001c90201101e00f403458891000030f5000800d03c860342d480701e100311800b207440c1d0002000104030f99529610038185c1188842c024070304640403246404402c00c020050154081e8103040381146020f03810401c0f910034800122504000c3d807050003000c400c00c0b03002445012038071801401e061032840c80c0c03619440c00c10400088640101c07074007000c00d06009001000d4200030305070690100c0000540f840800e14200000701c1500558402c40700f038840344107440f04500304900c004605240c82041803148420325400503850b8007441c011648024651b81c1d60303c1803418840300d1484c141426805482801c0c050712081601d9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 506303714 1250 506302464 506302469
    0x5130c081b070812010e06330f04080307022803120c05010c020106150c32160f080a020f0f0316080c01031104080d030b1f0c0c0510020a1b0803040b04 66
    0x3910306d41c0300011190704060032800c8018013603944050407400e1162640501c00710041484004c100240301c4005001903005c010000340100c4001152101a64410000c0341d01038040c4002505020250040c0011750064058041c0d0740d1010901d000b208010f60229100c00e240c2c03102600742d6081c00301603500b203070b01076200e1000c0d102500c0c0459030071344140030b05580c001e10500008003a03088100165040c0c00d801c1d4409070480d9404074001c0303410181d40c20023030b1420b605811001c41074a8903034402c02101e0f400c1c01b079500080c100300020340308000c50b540005010071001130100d0700680c0c3c84824031140703a80500490480001c45406007108a07102c030240d95484542801c1c3d9070200785400c45108019041e6400c0c2c9040715090030080c4510a50b00404a0203080520b006a41100204406402c621081c14a0003078184d01e9580d601010f51707003800d100040303000541c4420f02810451080000d041d501180c00c2c6401c0ba0403125850380d008200e0000c60b01c510b21540904424040403c0c0071800302e40b108010001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 506304964 1250 506303714 506303729
    0x50702010c0507110907140301060201020405010e180a0f06050d030c1205040e0403260a050601180b04230904080705010f05010e0f15130605130c081b07081201 70
    0x101c22001005842e5441900000ba105030548800c0e0000361814612259200702540341404601542540004150f0001e81280c00540d402003003d00407540d0003403895900d10300031074443c111142c0c1845030a1036408040c3c8a500e40755107400b4411603084043c0c000c00c008103070140010a0300c4c4014140240000c050810445c1c04c0004190303840e8075a8415810744040e03c00a95650004d5240ca5130152407400304071410f48030103e81034410010f9105c20301c04280c0703d507600d544041510b1600d0030004040b070741a0034402400c0d012507441404494900025101622051503008150844030025a0364100080c0016540890950200810082682e01801c1c985d0300c1038009004000345910703070f0002c3d01da0034080d54136050103080c001251301c480c0c1d00d81207030091014103090b1b04510340240440c140241a0000180b50340e107030001001b06045c031820702c41400c05210000c01c14801c0216005103542c20242400341448014400070f001e40401300c04644106903c404401c0d991040088603000700c5ea000d1040c0c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 506306214 1250 506304964 506304971
    0x1140a050636220e0303040f0b07020a12030207030909050403030b0a080f06061302120103050718200f04080114010f06021f0c0c02090a020c0c01050703050a0c081c05070201 76
    0x1a04100c0d104507038a00d500c0002c2103400c1e001503074828603d442c000c44480320103842c2c90f2451103603142c0c020f000a42c0158003130000c807040100380d42023080010070064088003c550004001d080460040c0034000c94410301e624000da542c00081c03c2c00c40b2700303204540101648a10302070500c8201034241d40035a1701000b0a42d02c0f101d0b44ca41c1c514042d5151804000900e03642c1c0c0100c2c1c005072440c584040d40c0740c0c1d941c401c0e040040c20804242009002c00c0000d030011180340d48411001c4c80510300c0005242c0394520b01d0135090190302c41c1c0d40005c0320900c0420881d0301101001203042441800c00c9800d54020388000c9000b0080307044c09400406071030100788520740c0c50344401d040c041882071022a004460081c1840c010340c0c1c1c0803410303400d0382c020b049a140030340402070071404078401a652031140c14081c04d000400503850309515900c1e6414003846400c00c03410f1180401020f00000d4012040d1104440c003803c0c0708801000f00d04044186200c0d11245400c54111144030340e0364402290721140c0203246550080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 506307464 1250 506306214 506306287
    0x130c0806090706180b0a11150109110412080306040e030c0601150804110f0303043308090d080a0f020c01020a0f0518040905070816031a070801140a0506 67
    0x599210080000981c4d0b010b40d584010b000c604000e00046c01e1804a03482e0400309490300030480d500306406508460b01c0b4500d420010018800b65008820250f112450810300e442d280c140305089483e01c0c0240105842804000030350703140c0d503036401a01c0898540b416039a44942d0b04058549a40c402d00522000b6640c000f4250202885510480c0c4a507a00030303104411038140c0300800259441054255078944400c0001007203a600e2100c0900c0c1c0e00080c5080c00b500c1410400c800048101528940010071501c00300700401d2000010b01a401c500e050306044015441c1d014040018100410070803034070300e0000900e082802c030305500a0072010030990b207a08044102c0c1404542c588560f010340703914400a450344002d03628056100f00c0849109a0450384010344d0340e4640c605001d010841350701003007181581002440040e4018003421400740e92004c5081c074065402504200041c000c5083c1d90340c40c070f0301c00300503611114003100c060100100a607071984401580c03000d0b40c1000c829403ca2070079162440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 506308714 1250 506307464 506307467
    0x80123130921050307120b0a030c12110301020903060105011b1a16090b0d0f0b0d0305030412030b03100b040e07090518010504050d0c030c0f0605071106130209130c0806090706 77
    0xb0b80e4011718207561000c0503030202d44021001f408840c90303029400000341030000001500040c0503001072804000d80c1da86c03451107080451038103075030034442400f1b039004105400680d40c011441505480090920f508404911940c0300e00c002d01004000303000a28210740c071a9a40141040f1a102e16151402c1c510042a11403048502440e20320407451b800c41e040c00070070300300c6135070360803015020700300850004014198000041c03048421100030350208000006010070700c00b4403c54400300034030300d040602010320a2400700390b45e481540215002c3e2340c1c0c1c943e00785515a699401104103417105808a800b80d50b22004124014038003a120210000c04415901c41800410300840e8402c40c0c00202510300c50081c00015941c084c3c198404508200119100c00001200c2146030b9400394041c060019003440d1060020f4440b40c1014045081c590098082042d015408512a6900c580c181c800a5064580442a50881600b4000108003000b82c410104405000042040c403ca0b0f0000c00c942c03400d50394290 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 506309964 1250 506308714 506308717
    0x60309020906040b1e030a0c15030e0303070203070219050409030f0e270a020f0705010605012a0f06022704051609060513090c0c1208012313092105 65
    0x8040d42c01040d81c000342e04256114903001105a0005400d0341c0c0d07c130100c1d5503007020450443d00010f0700c01d0103441c035446556905104034603941c10410001c5145061942d400707941ea008880001303100d034211801c2000000031031410f0704001c01c4042e0040c0b04c40400e61401400040c850500e103000919250950714140c03502602c0d14842007001840300401d550405244880c4160051046102c2d6408100e4100c40d40014070080a0301801200000741e0b050821000600050150f4000a14040160000f403800e0703403219a25511103601c0044c050030a4014a4100085d0003020403028007840780176100e20040d21300c1017412030030b00f004680400269480003500090301500c03001c0c1c5400036164807002e00506020b07000070181c01109000c503100c000d03520cc1c2100190745011760f41c20006000b107941d400812020541e5580d07000014280621250f040c400d10aaa94540b29101c2078469840c030903d542135201c0c0000c1c030304580014101804402100e081c1400316140124858000d040701240441c00e1920410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 506311214 1250 506309964 506309981
    0x8120a0f050c0409020d0207140a06062310090e151314060910180207060c1110090204090b09031b0102090306060f210c12010b030c01081308030106030902090604 71
    0x507842d82418204811180290001503015034003a508000b24004540341207e608410001003004100384060f42c80c01d40d0644400e61b100d109007501145c605410070700c4407451124503038800c2c4c9a000545184c810708807040c22856000da000312000d17501b40302010381a5128981e5016090f111007840c0c2280c000c1c1a0102c81c407982e007140712252040c000c2000f82c5000d646060300030380a145100a020346a1249292507088200c2a0301510760010b194010000365008501640300f02c0d0908030510480b0800e00390303d910103000452110b503501c010410456403503078001465103410400c984000d15040c0c001c5070381c1e85d004801d02c02c50569010106410010140220342d00082c0240c041e00c0162038400034060031151681120b6405102c001c600f103c4507a1082d0700c80500c0500314010f008403c240814001c80050020100c0300d01c2c1d041036589111794030300080404e0450030a10b042c0d50aa511480080900c1c0380550004182500c0003000088903581038015070141c034002c80c1d103800d043d02c950080004403410310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 506312464 1250 506311214 506311231
    0x1c05030405010c051006090207030806040902090705030c0f0d06060201110708180111060f04110d0812130f030203040801060b07240e0a240608070e09010908120a0f05 73
    0x411051090b035205945964080344294101ca604480034110b180c25900e242d000b1507960303a40030800d41c082c560702000050300400159010002c812a03500171440580004022806202c03002000c282d0400c1908201d0b2a101c583c1011039844640c20342c180d1b0003500240c81483c00560902511184803010003013200c13842507000c800c0e20b1074024040503410700c03034125503d00781c14407901c110004c0c951341c0188041c41c81100b01c1e0040c0c01081c40e052611092502d030144c0058040d04840341c2d0000002c45480464400c0441024030820035510000a85010030807030030300824102c000f4179030004042d0000054001c0e20b40c080000d110158440807031300b01c0703805162806005405420040491014800e41e04581c2140401000c03880e1045443c1003031404100001c2284d0f0704006840c038403030514001c0b034800a046008032045c00b58916001030256122158020500f02c10642000301e0b13840d000941c0702d480025030041109469402040140c00704201c1107885181c41030900201c0d40c1e2400b1a84249442000303032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 506313714 1250 506312464 506312467
    0x3041403040b1803030f0301171203162f1f0504030504120501060906150905060a05191110050a0c0f080a0b010e0a03080a1b031d04020d0e0102091c0503 67
    0x4010b00700c1c15071105082641d010f0108200031303c03506c48680300543c040d20f8450b0711b48618000c80342005240251000803440c14a1080c001c0c08038008a181f4143c2810700b0524012042d00507120f02c04000b06109c00300e00c0301105000005100742e1501140810120400551071000740070328003812011f94000b114001c00103101040184114655040d202e00024003074800041c0c01c07a00d0304585003c4440d103130000810b100c8581c002c03440081d4001c00c40e40203010143c5181d41417840740c0c180030b0510b001d01c0c00c0c503050000700f1448042102d44580d61501040440c3d2040f104541c0c00f0a0903640100b40503242030403198148080c1e4000a4041d840c80301103042d042e9a0340762541e03180c04c10b910007044001086070400501044030712182d5141b1030380b440a14010301d82c0554035100c0e8803029018030a002c118101e205103110b400c00100741c014401a0b00c40404100c91203103d05440001002441035608610181d0b01e050081f4841c602d0560280403010003e4807240300d15140b5808070b1084800c4014000e009170b10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 506314964 1250 506313714 506313727
    0xe1506010e060318250b0913092f1827160b0a020105060904050a0605060d02041b0e030102071106280c06060b04030506160509100503041403040b 64
    0x8008009542c4010070034013020600e01c0142a803030803d6210382112004855a584c148100c4401101da0b0000b405a0040c43d480c1c1a0440041a60320086860b01918140c0d03440d62101130001101051207a00c5104107941007011600c1040450007010084103405040f203007110b40010203030708100c00c2c001e20070795020045000501009420040d101c0d203481d035042c0185504a0000c0000800100c0138100c0d0800c00f41c2c0319040c8050003800c40e400204828801d400340700903c80420404540940107a401c4040401c0c95643d0384003103400041040e0000350800d04d4560401d1000010300600d43c49102181d4441c210b8041610805080c0d01501401030000348000d488075040b40340c143c0003480603d180418000c2d00b105030070f1290f41510f0101c3c6203080403c107001c07404010400f00e40715580280030304644a48c01c250464845607034030900180452074060305403082e0101d05015038282c5540d010014205043c803564403400a1a54005071822200c41d040160504000710000c42a02c050f0313004120614200038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 506316214 1250 506314964 506314969
    0x501090b210c0303070803041101020303041a0603150906040302010c02120d09150608030415030c05040311010903061508060a050601140a0302040f1410080601050a210606030e1506010e 81
    0x208001074001c041c441d6041000d0281c8090020349009070041c807465403285050700306030010310407051401d41190010401c0200003060b804080425031402115a42c50b5641d540c00b0903c3c14821074803081e540c410b508204800c2110020703005219600c26402030250302c2080c0000c0e6607600503014200c00b0544140085104101503511810b0322500802101c540e2508400e0418121400ca811488283e000010144042e00800128408120040c0360410402420042c01010b5020750b0000900190303403131250a48a80c071901608020b9900140b040252107030300740c4100816011840754641c90301400000aa8640042c415140b0806041e100c13040000612240032885a00200440c41816070922012440724000039242c00a0145d000c1c207400d0b080b0020003001703084402d40d1410b1082111103c02c1001e9030340d008003552012986d50910444519161001415007180340802c20302c0300740b50a5000454070b5140c0c00003500e1424440035075005020940000b221342004440303071030110b0803080f03003046a030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 506317464 1250 506316214 506316259
    0xc0b1b0114250c021201020403030f020c130203060102160807062319020a1416050603160807030603022718121c0c0c05070803090a121b0306050103060501090b 70
    0x2042c245409858071105a000070019101c901000f5010382d8041003e004150308513280080301843d500061540d503c02d00d0000301141c00400d880d00100350048041840799000300000700c10020480001c01d011500c2d0003903160341c0c298500c5084005182c203900700069042141701e44000c10345094606d0320b4400280c20000205005065a400714450f008150012650358101c45120303040440140400b90065038950101c0c0095422240c842c01d03003007092205010001901c0c0048103401d00b0138603410368900106900400c540d510103500b042c01c000e03001490703090360784100400c0d00d56a2074241481d2240c81c1e0b1030f0f84812135a04050019070003805c010210582e60000b400400040c0003040b18035504518280013a107d101d2012404681c1c4070038070340204181402000090030020004500704446180000c81614140c0710f1b02c1a181c455882d00c00a000c100758080c0701031030041c81c42640c4036541e031401038003c01c0244401d6505c0c038942030001c60f0151060041d001001030041107072030b021910000c0402c96 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 506318714 1250 506317464 506317531
    0x406021b0312030a050921030f1807061e020313030b040f121d030309150d0e12071208060d03210509031809010e04030c0c0b1b0114 58
    0x94030a111529040c1150714000f14400c051000c00802c10b400c3c1259546c3c0340c100309080c00310103000c40280840d95504404140c9602401840f0004281e44420071a0001150090312944031801110404a02c030b03500185801d0071701c0307120f0b0010080402051003c80c3c40e07006440b8400c480b055280c00400200d1500b05074503030000d00034459440e1503c0190f8884401c48403064406001c649007030620301c1a0008a468410540c0c000d0f4055031130600b150b0300140008050440444c0403c00200e07200c143c1280c2a40031244849054085864170f120300341100100382c0180d0412540035680b040c860050701c3c40f03001c64a001d0000070301007200000450360151420640d500f40383e00005650708480c20700c0301e224001c013400b5181c3c40c0065651030300760191400214000c41c414a0080c6100001002500032014903551310541518124940790301c14030309100310390244d0388031500e014000300314841a00c100480300342c0c8006081d4000c20034040d418880315466801103944004803d00c0b402d10071452001004030a54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 506319964 1250 506318714 506318719
    0x903021b0d030828050103110901030b0a090f020a06090e0115050901080405100f0f0f0207080702120712050c041b021e0a05010f0e060937080a120605060406021b 71
    0x24400f0800f00c4000090111886141511940108140680c01043d10b420207403d031400f03941c032b604580b92a5840c150150292880d25550141032003131209035204044000c1d070051010000c140da40c980208540124003c40c5895080d40380001036070180e01d020f4902049403504d0340c1d400c0c040d01030015039505400030420366107070080208505c490300040c801c0c540d01290380080081d000003100d80000888282c1e4041c685003a2040110b000403c07030000641d080c00c2e9040b101c030140c0d005144413007030410405034030440e130b0b021440b510340e003c00c100814041310a150075641040b0440c16070031108400c00360174a00710056000801120503515000c1d00302c060b2a80100300f12400c0c2045551001e085408181104815990359100300400c14000e22050390030210342c00c001c040001c0031604441c0c9603040705090307201104103140f8901e035214491003240724040c0c22001c003640744e05003400080c0601010a044000c00f13440d00340b000c180c07498030005450503683d00307500811440400c120310001c030051000703240784d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 506321214 1250 506319964 506319991
    0x110309061f0902120f060315011401090806090312250c0302160803131418060f06070f03030c0819110d05100e060a050f0907210903021b0d0308 63
    0x442d8901c50000f01482202000c11034801c0c5030000d600c40d0803032400740c181c920036084004a20a100003058419040d245154101445840944016161a4820741c40502c050151a080050003000407000d400469a600524580d9688030700c0055401d2110082c00c066441c0344540719609688100740f00c01c5840d10034012100f4218a55030861143d03280e070f43c80901c442c0d0000500348136040031078681030020107102c4282610350008000280e504100d5082400e142c0d907000300021410b03550540380464055004d064540d507210385082c6000760300da901c00281e0101c2e041c54003100e1414802d0f04140e01c921150380d8100c501c00d0018038540050030351071003d440241e2041c0f0051002c1503052280301e0181d80c105900c2640517140c100002e17691200106854403803040442c082115403165924200040c1c02183c015400c3d42d610030b400e40301107500e40e01c4862400d001e0180080511141d620960722030b4000c0c0c08403500014000c20201358929141100d90b0800140f03001540040d0003641110740003001c0541d40b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 506322464 1250 506321214 506321219
    0xc030f0509070f0b030702070b030c04030c0f051f0e0d060608070b03071101060b040306020f1207120b030303162d2109020d03140f0301030f06110309061f 68
    0x9025a0400e55418209820041041010658030004034006080001d441ea00318500b40c18040e4469459106c0c0c4604502d00100041407207090790111005958003414507001251071310822002c980c05800340743e0040d88001c13242464400c401031000780000d40d598810761169040e0040c0498003140c6042250581e45030400481c43c440140120320107458004941350f00d91800d40001030025521020044640e4035101d424400011810100d40580b600098056602d84491001002501c0340da200010512140c0d418070211980c080d044100c45507104000748145854081010703100d1009a0342c005200d04088000c4255500a00701602c252562000f242a0603412100302c100200d0905440030010b24030b0b07444054588500458009280b801d90000c00000440360301045002015200150070320544815800743c880f42c2108039601c158480400c25141c0d40c0d6072405128500782240125141d60814000201029525007a644901c6009005200b00e40b107100c101200b4038201c0c2aa90341c4070070058000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 506323714 1250 506322464 506322491
    0x22020f03010315180521190201090501110f04051201020f07060506030610031a0c0d2307020a0b0c0711060a0807030614060703030f0912020a11041e0c03 67
    0x5580218003c140300b01041d560000d0020486941c440124200a042c414001c0841c400160150f14010584c02e0408040039003000c41e007990140d1801c180200f0f4030081c04e20481681034004880f1144110000d02015841800030300441c083e80c0300741d44207158280030401c100d10705824403c4180011600061500d0418000502d080e0304c400801c0d140300392550140b2485080c01c00c24654000c00226601a49c1410b5a4802c8590b900c01e0034168040001c0300046841c081030801200c1c641001c1072001c0240c45d200d485410940392014040c100c00701e2031900000e02d00c070f00208140181a5008031100b00075500d848030882250013503007054030050301da10075480403074480c42c006000720b41254850300018500120000d0540c0d0094020140e0321569500e88404d42e2030301c10a40b580580c0c1803c02140840302e8864640040c9003081010342540b001d59001c4840d280c011460083c12030151072041144001342d0103010960390005500c42c0500a003455240d50602540d0104500700c04510300071800b80c40c202d05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 506324964 1250 506323714 506323717
    0x60615161118040b06030304031101030c092105060915040f0c0b0a2703020f0d020409080310060809010c05040b0307030b0d0c0807060309020d1e0803010b0d1a22020f 73
    0x2032035116480c18092000f80035071602d80617400030045001310f20f85030540d034520030120310706400b080c14180c41e402a408464019064440a4203807008400300210400744103039803820031494155228081c410218144000c04105401101140411003802e52201e41d030f05040c2c10000705080d40c2600b44010003040b20038544000302030130b40e25039a8004030406000e80c007104207800b48040035004550030200b0401600c1300c0d400018031081c102c81350560040b403070010a024180005d4010f200304000000c101440050b2820700069525554401015940e1303d0115401c82e6070f100b40703140101d00c041c8420002100c41e0030045a21100310314001c0f80701a1818049035000d0340a030002c50340411011414410080f0800401d00108101e28013031042c3e60081d000700e05601073304170014005c641e1304005800340903071140746002c0300c1f0b52001c103250392503039500c0c0410740725080703070005a10303540c01e0803506040c405040b40360104822005040301d414854100c2c040c8402120300141c0d520f019024002083d1152890b070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 506326214 1250 506324964 506324989
    0x9120f010203160c03021515060d0e0d0c030210090309080f0f0f0d0e0607050c03030d020a1b032f1219180e0702120403140606151611 59
    0x80090b803241040502d030542020105801400c00800380c0b0604d000c20b40c00188800509a00c0030181404d480d401c0030203144406040805401c41000154444882845e5011491441c054801e41e408072000b004100c6084d500d0400180040c1d005c1e41d1118150710003036001d15550703446420403000c6107590700c209904048000101410b550003040349540401c03400c1c485490a803045101421000480ea01d0141c2001852103026000d4075010070120200f00c81040140e000580081c02c880d21818640f01c400080c0d4014014240000d2202c0842c0024403050000303810610381c16200c040b00001030001d8100008031240c1e141c41060a003468200d1840f40901900c0608580225420368483e215101c42d44020341e40c40641c01004810302c009a0001c00c2040c00005450b60010004019110ba450892a2084100d800c00590200150000c204511707500803101400040054030455640d0707808002c3c614000040c1c40d80644010407102040b01c001d0010250340500c21401100c02ca6038410100e948018000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 506327464 1250 506326214 506326243
    0xe090a0c0815032a0910080703080903250312080106080c03060103090b0112030809031303023604020f0108150d030c050d02071a0403031b061b020318031b060912 71
    0x1d12140c02c0c10b0801d542e000d46c0c00703e403145042030b58601c2d1034003643c3e4510281c40302070b068103808120b110055500f0700c0700c81c6150002092034a105490019480a10090307403104030f411340c1c9440318110300c65000d0480203040701c001d45c4500f42a0b0f91070462840d22a40000c1c40b031070401d5518062040012450710350705010300100b44104d00003c10030703d0f020307042e801d02400002c0254001c1c06803400002070155440241c0e68103840300c0180030300300002c6100d05407200f60380c0c421030141d030941050b000601c1072040781300b0b600844058544180060040d141405c06440203e405134040d11005060308140c8000c90701903120749440c2000541076151715050001e00f0400b030700140c002d0003003009845036210241918030200c5030039901e46840c50b9806081d5910f2074101c00440d0503803039205000d003d0381e0b030b1003000702814103400448000b40b80f05000b9102d40c0320b003002400000b0003052049050a00040d42c510646031000c2d5481c45140314002c000460300458100e0381d002d4168081822200418000c002420200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 506328714 1250 506327464 506327533
    0x60f070506090d09050a0b07081c06080309041a0a050f0f060316080708190507030219090302010306060509030c060d110d1b030c02190c050a060e090a0c081503 70
    0x5243c0b009082803055445107100e454400020b200d074403141400c44010f2a4411003440c1d0301c600c0303941c00034600c140c500b2416082510b0304500048240010000740200140ac9404004110058134107401007e03010084075003000e00c1c14070620103070900c070a01000b0000d00070720180c413400d080e50028001e40c1c82115014413210000c178034601d4498206841a402800f107042290b1140f4004902c4260305003100c0399400c20300d8440001c50703404d40c000d50445942130842e410721a040424030b01c0c0600586c44030700c0104e0020b032401c00001002c1d880b0703030256841100010050710307100030f07564104007880d041084ca60100d15900e40c51350403030b805d540000308464039480300d0109a4219401c0f42403000000180d4a6050604285140c80d40942c003041a40e45540c158203000b1846a607800e010441e68070380e811031900012400400b14450b0b411012404100508966501160b540d40e02a5401e0356040322405c400f280e41e2002054140c00701200540da2500042c080701d4801030b90048a9003005040403205650b4800c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 506329964 1250 506328714 506328733
    0xd1104030c05030316062309030a020606040e100908122a09131503020307080f01060803070c0312030b04090b180705090c131701020901110106030c05060f07050609 72
    0x81608128001d04040380a54181700301000c007482403100302040200116601e200144284180ba00c0c07079000c10f1544000340074649003000c01c1d035039254090361845015100d0100014551314260050b2001d4000760400b0300140c0030b00c1000d54001e8a244441180c1c442030a2082c61001e20396059902c3c400c070300180030116030501071080081d004041082c0183d1201c010070042c25551202c1820000c4100304940024540d12200080a084002030b00029818052900001444000041c81316900d00998000304206559200499036032310941d24001c2640c8000c04e4100089880c086080001c0301550802080e10040140090112414020100e40868030041030204840b001042e0460115100c0d0003803e5441c00c010004280c1c09000b41100d0080301c0009000540410209500006054410020130401e0013400b601d400b03500b001c100c182c00200d0f804035015802038140030b80030441e81c01ca0034010a03c1c0c102010301c062640407810002e40c401d0100071070700028004010f010b10842082c03000e08400903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 506331214 1250 506329964 506329973
    0x516181d0f2112040b070c151505030610031202031c1b05030f010306021b0303090106031b0315020a05070f030207030605093403050d120f02190e04020d110403 70
    0x4103210341103200c181800040c003e00541400e0603000ba42001e0800c800340d8901c60304590303521071428003c2c00110b041500080608640d0003031700c0c07143c482c81c01c2659813945510038140d46400c22618480504501001000411100102c05409440510603646841410300e100c031081404458280c0106682d0306031210f503c0c3c40508030780c0201e941450481d00d942001ca03600c6400803010b0101070400e40e030000d990303001c0010400c0711018440d4100d059039140d203400300155000b8403251105030388480f0484c5059802c04920035041d01903c0e07000450524404020942c1e8009401824054091110801603170010442c0c81001c40030180c400d5004102e41c07415854840f0039994007620554031a44071100c1200310010312140003054a9510000746020702980b200c001030f03410141d00140c594003c0001c08101c42d5030107000200880e26034202404030004841c0100100d01c5100b4207a1a40071410048001103803080c00c450800e0200140094140000303d860a41140e204070404200780e180085c0800800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 506332464 1250 506331214 506331253
    0x5070b040f12020f010f30050108030309060f0403020705060d0f060501020106080703170d020f030403020f0a1212090602030c0a110f060402011116120516181d0f 71
    0x201003062505102d1025075000c991a0352010078224103001d403600d108034885105180c004401108000340314010312003c0c049005c400c0c91482045089400c00001040d007100c0002101d000307480050050031160b40b102080100c3d001702030021400c600504e4000102070392660080d00034112043c40015140600310440000c0700e21a902c02415641040b80410401401080c0c0300c040f85c0c0c000c03c11804800e94490450740070b2040c10780c00100380f4070200302d41c03060703000e4200034600c00d43c420707000c450440c1040c066079907071034007510070042c05c540504000c07915182c8111420300340a480d849005c1184440b40da54001a81c100310b941c0190110045554030200b42d100004000009080002c1c081507942d1119154942c00010b00203810300642e012400c031012400c01604061410014140817076548420382d610145454040503280c0b40305d0410020602034200f4a00301c00c0716010b41803107400d4840b40382c031070010b408031881e12021100300e0a80003414480034013980b80b8100c0a0350103015080944062403a60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 506333714 1250 506332464 506332469
    0x70806031507080a020903030906071a180a1e050a210903050c010f02070806040b060906042a020316121707080103030e0d022d040b06070f0f05070b040f 67
    0x1e00208000d01c405503420060359078000010a002696840041000c40d240d4420000215007001c0c00180d0a414066a44290072841240c00d10801040c0c948034a600d61012005a446666030040d645001c0040c0d9100d12225402c15a03145980b0200c440340c448a04081c522141510180320017050684991072200c0103403040311080c20905500c81c25602c54036603070000601d11a0601c12aa01500c009074004c200c241c006120160440d02c2901e0249000592030009071840e40c0240d2544c00803d40628043c0030700060070501c070b01c990306c0c1c190a280c1172580000860b450704040d03010805c20040d040c40c801e914011414020071403000c1548004000421001d0380c0600e204050806c0b0741401101a4403030022170450780c01d80f8000f000b0071000c0000031441c408640000b94400c00100c40942e000602010380c0c0c268046d410342d2201d007500d400b004d10083c0c61881c9101c6910410030440c590005003469500c2c0c002c0d5018001900030000340d41e0f07481d481d0004075040805403440107d0100300600184001001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 506334964 1250 506333714 506333743
    0xc030605100804060908040e01080c010e1005030f060a091112181b0a150810050a05010c0b0a1107150b040c080105042427051012081207080603 63
    0x1810758088000a0040c0300c0070304014011911080f102c0207102050040c0c0f0050403050b5420061940d5a016855a52011a540030b02013900c1808007003440c50004282c0200c15542c1d180c50389035940d0a00d08542c3d004005010f60b5015800040c00f150106a40c8a804200725040f9060740d50380e1111410f0b9103612000401415075000720b1020101821004031306103000c01800c001c1902c2c540928000138407140c10b5030f0000c8104071031041c17099001503480702255005201120f91030004075142c0062046640341c40c0641e1340810003640400000441021b1040da0081c1c00d003074000742c0d95025680d4000c0b250700880081e00e141d895244207103c070740101c0c4a00c21450204403020480309030f5505000d8034041051054500c199502c2e03408400403000f01c200440c00200e1b41c0601802a0303207481a00902c0c0c0811a01002c03680c01c55072407962500d22501c01ca500940d400c1040282d50382c6040d95a25403049411000c5a62240c1881120070381d8228a211502550035501c0e1801cbc140f901100f8507282060401d002030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 506336214 1250 506334964 506334979
    0xb0108060f15250b06012316050a0803100512060609040609050a0b040c06030e030301081c090906090f0b01030507210605090f01150503011d0a0b04050a0c030605 71
    0xa01541c03040c180a0014075076440d801c2d01e4041c10a580d40d0700002c0f4150100c01e540091080c50208440ca1070041d10a200c00d803070784000d072062070261346050310100b1a07400d00c410080101c003503024421044201c805120390211081603c1729034410700c8940041c2c68211030ba0300546000d006900e005203103030045150716801000c107840d00308001429900c0141c0090300642c0d541c00c40d0400e01c07005210510140750001503002d1582454640000806010300c46c14002901d0007000800b400f034040201e80c101c9900900520180c14000c580c2c9907046003407422401070081c8001e00042200080c0201002080c510f40005003110442c0414411750b1401082c0c5410146450104184250031003400c080c222120a41c003400380071180507190041219803c01d80e41314074030000308088240742c1e07000c02d4141c900d00c92000d02d84c1c1ca06040180d40c10b000c00e01410102459003a0042c56562444d400720350b2040c20b4400206011411601080441e40700b5900c4000e6030b51500d6481d030030140c1500410009180a0300c25a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 506337464 1250 506336214 506336239
    0x2030603011803020d0e01050919050103051503060f0a06170a050c0f011205090316110f010f0c0303110f0409090c0b1c0506030a14100c021912110d02010b010806 71
    0x2034846170a618030505120000304280301c0c59110300f007503038416440500704800c070030084030590341000c41078071035140001e09150021304c07810805060388134684006001400d06450b680300b0720960200042510390919514800003500d0400e12329076811080d02e03007000c1d01d480c0080b414440c3c20003103c0160030307000e46502d6002c0b40a0740d901070740008079203580001c00901510b07005200d6040d481501a0103d4426410214905024200c0010804c5000c1102c1440e0080084401510507800d40b07014800400c0f80709035034501182c000e401c07a21240e14200c0142d45000890610f071145070300640c20041c41d00342e40392162000c1000a4a5030030107403450985250030f200c002a00300c1e04000a8010009405458401151050310f00704031100007140c0c89101a1407048152400a030782e003080c0c4101944107402d00e2285060140042a0f07a0217050750b00c0810b0f030001045032100d0240403076003041d00c3c0030003440310b01c824031806042c001841e00740410b40c0042101d02840000400740720f0050282071203480c0f00c0c0e080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 506338714 1250 506337464 506337467
    0x80a080907061d04021b0d02030406180e0103120219150f050f0a090203101d060a02030603100b1c0c0f1e1202060d09050c0406090c0f030e0f070902030603011803 71
    0x203e4288030b40403a809a900d40341074840c007500030300c190b004c00c4044c40303010a80031129401002800030349040d0307038071540c09050180e1442e8008440388500c0d07807255440e00041c004035041c5210100032088500480b58800610f01144000000c4604182c41c40c62080101c5d540d1810b00b0301a28149004d00c03001403000341440005410145400340c43c2005403607403420071400711b48052000038408002100104110b0100d261008502d02004050b8000c40c02070706d0014110903810310907a401941c002e0014100c071058400e208000700082059240d01c200321030f080d0041040c6621080c0c5006210700301d00e03209039103440d8180c50200041d80203000b088800746c0c290384980180c41a40812241c0ea110440410031050000c909030f882403503000380406040800d40410304c000011811054141550f04000450b603039000001100c40c0b809004c000682100ca401010318400d400c44403075800a2800e640100e61003000741072800c4481e901072002c0517004030402416142c00e1140b4400c41e40c45401c05010b00c00996030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 506339964 1250 506338714 506338757
    0x108071d090601090f09090c1d0a05060604170c040b0a061710050a0b040e070806180a060909230f0703060e0102041d0a270609020d080a08090706 64
    0xa0a0007000307034200190042c0c4c4113889074001442c2100b4200b200948401603100540010a0180e41d507559140d80041e1000700409440140401d0081c021000c3e241e00300d0140c060140078216940c000814080801d81c04101e003440d002920a606c000c2c40c48032031007000d11003601d0ba00070110780302c1d200c5c1100801295822000c8030384400c0903003c98070900e544000813031b50034010b02d0300129080b0201d401c0101d20b480200b0001c0095840c15040720035295207141d011600311004655140d0856050300003100d0425510b41880e4001017107a8010840b60345420201c4119042048103a50848180704410980c180314025203980300d0f0100081d0900506110601d9a02d211620008140c4c6644100b0941640c501394113807005040c800b443c00c40e244440070020030550342c040e02c8004905190504101891441c0f21121070040000c07054940180f8407525020b0042200c458240e0708082091244800603e00000070a510042c5445041450401e0501107141c11016000301c41408644001096071420700f22 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 506341214 1250 506339964 506340017
    0xa0b0a11040501050c071205030301080f010204182d021213080f130308040303080f060136091503150b0303040e370f060b0304031b0f0b0105010807 65
    0x204030360317294144406585046001d520031221050320342c00c90700c2000008802941210b00e850116510303803800d28502402c0740b09510a140e10010301076821488010640c02c914541c0280720b003c0348807240504031025406860424000002c0c3d40055400110744c080c11172140c00c401182102c9190103c0c07551602001d1003558042e1950070b0020a40015005840c140302c4095540081c18613121540e0b4034000e07200c10800c1c1c0714414078201c404005003895100f049180304125000900201005000da0341c00340d100355046001e0801c03905000301203900b003414000c0030b00304144d540c4045185403840c03c010329125510075174107501c0e03820280d0101940d6000020344056454106403200ca0741c441042640704040000020034410b52890900ca103c3e4071407444041c5080c01c40c010030f1041e50030611100045a0050185d440b07110300500219001c244140d0304000380d44c0720314400640d8108030b5201e01d040000c1c2da100854501951034014070007940e02810300740d0486c01070706007094024070b0303440c40124000e22507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 506342464 1250 506341214 506341217
    0x30a02010305101a0306040609140109020f090301090c1d010f0e0703062301020105010503030a0503010b0315060d02040504060509160c0303021b0604020a0b07030918090803090a0b0a11040501 84
    0x300c0c00700d03e29002c2407415a00422403005440040001c441030038045800413a02c69105502d0715000080049640c0034498000c0c0c0060b401c12074076800d081200000350050350018200d58030070b0004a155480c00d11072031040740c2c000c800c074600103490407444a2000e40d65003150b0000030765a0004000a1450003494820707103150761403c003081d944070b4104800600302640030032200b040c101d55640c080c10f80002030f074415071401c1c0c1c000c0c0100c2e80c8071401c2c15604e22860050000007541000100082c0c80c3d128050354000c422000002c00d00c85480000910380e41241100700c110540c000f03410809031805104e144014003086da40b11a180c90b0850064160300c081c06580701c144440300110404052095048400c01205540322040c01c54030060400d0f40c50008980803401075008000103d80c1d4034419050301c014582c981d4846410f07071f003425282080030384d001d142148000d48034100503000809aa003d948201070000040c1944080c2c0d0070a804d00b00005042c1282c030340c0c40c191508001e10980e00071141691020b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 506343714 1250 506342464 506342471
    0x1b01020a0611090a03080c01060602122208030c0625090b030601090b0d060305010e0303060f010c0503040807030b15012307020607081303170310050d02130c110d090302030a020103 79
    0x32004a20b0482c4500d4000c184d115030205004420002000c003c2d0541000040007000031a441ba503050380d5072408080038600f01c0400384240c0800345102c22070141c501802d101c22441850386d82c10b42b17900d16046004804055004201041180700c0e05540700004078429a038000000c4500d01c1c0c000c1c00f907002d0f9000d003000380400040010b070180d000794031000040c803448207142d40c0ca0240300b200301d00074409800304403030550038100e00c0143d031040001545d00031003004101e0903042c104880152070190340420b040310302d804144800960307100d040c01000d00071402030120144034600310315201c001c07001850000341400044c441c210070281c00c2c06e61071441d001020400c0340d6205d42d03d00010b822401080c4000380203160008200181034180194030040f64420100c010440e10401c2ca204290b00080f116052001030301d4504014034540740b00107900352800980611030440f041403600054034140c40c20346c4007266007403654074061081000807240328003651804510103400c2d0ba001070b0312107010f03400c040d04240d00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 506344964 1250 506343714 506343731
    0x20112090318061d09060a0b0901110a0308160206270313090902030c0109120f020f091513060b09040f0204080706020c091005060a0305151e031b01020a06 68
    0x38082c844a03124103460010806561960f00401070340b0788034295004100040282c40d51030420785089402000000c10001c507041c1446000302907030b00144800e0381041941500741d03410350700900841030704501070750700c0385000c5c039281d28003080e100c0b64040c2c0390003154454000c21042418695072403000d1003031405054a09640381c00c43c00d00d140908602907240703001c40800000d40d2035180d400040d100d8800e034103545203910001c0040d03410390700c030344038116a015000800030005907140b1105104035200411800601030300401203030048000f110240c440103105041070201e49400700c3c0c0741c500852460003d01c112410000c21411b54010560a54080c1d600c80c1c240501c040d00d240c06490241410104441000e076a8150007940c64420b1400d0b54001c1c443c1d04c010400000c28600b40038152100038144c3d52408070440320413401054024864014880856103201c055583c0302d040300da21010846140a00303005100426007498196489c551820b0700c0300344241082d980100d500300c80e107504131200107001907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 506346214 1250 506344964 506344967
    0xe0108041b08070611010509070f031101021f02090102010509011116080403082d12040312111c050901020c0c1507050313150c110d020f0306160f0c0201120903 70
    0x310035049034902c0d000da14400301c1e4407980101081c071120900c00c000c1c003c6468140005484010070701409102c0d0385d030b05209001242000c055041407020600c1103450a03452041d400001004440e5103503401500080c990b8503941e130900600da0007110b008001c1140a41c88400c0314000d01c600b960710854120f020002ca0140310000d01600e00641e00900c071580c0e40d51041240104403a02c0d0204200c64134011851006003120303172030a41d540c1034003aa107048a55140d581701903951240d40b01003070100c2a103411890210390540000780507205160861009003d00400f004d5007500c0008000c00e0060f803060115461800f000114140c10b1038041d10781d10200010981000d4051084603000b8140d844005280c80e04030102074607003001c480c80c00042c00c11000c140101140c0801c21000041c11550280c02c6100e01468100c48038075203648001c020903c0704e10703000017003070408070112180726000e00381000d0b4500c0d5603080b4511800d00035151910441c00e00c6181e0004c0d01e0036060486015400ea61582d0f2642010b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 506347464 1250 506346214 506346263
    0xa09112b03051b010b100e030a03080a0213030b06040f050603030a110a0c030506160c0302120d140103050601030c0b0c030f0a0e0910150f0503151801120b01060e010804 74
    0x1d43c000f410f8500360b260011010b038060084001e4050040e9082203c1282052240384460204a401009014480070a440441d8500d80140000340b0345a0300300319408148090f83c20400c0107504c2480542503a14140c8200001c0f50405080c840010b030030103040106641d800301c01c96155a00702e040c8800ea440c9100c01d95841c1141520005008104540f00031041c0580056079520440100c8030460000c2800882200c0403400c0c240001d0159100c80c1081d14206a034030301500100e03040711000110303c8241042078660380004e0b0b00c140d400740c00442c0184140241c14020320003410307402604c5407500b401c60704090390342d00c11040c04c41020f990200750003008600c0b070100a4080031000306204250308045400341041e203c940710b00c03114800c0421150315107901a21941385004804d407542419582d50700c030707040c0017a8004a07031154040c1ca4400d112544000783c20f041c034007030151026002c42880c1e551600302038590060700018140243e014801d45176a078041003d950195000d110210740c09804c070328090b440c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 506348714 1250 506347464 506347477
    0x9010c0c080d030507020609420c042102100c02061e18062506020706022b05010807030b040c0f0f17030304020d1506091a0a090c08040212150a09112b0305 68
    0x20b010790f6105000d003c1c80c1c1c00000cbc000fa00c01c02c0840c14440c0c2d010140301256400f400c81e00175000865804ea00b20420f01036546905500d0020342142e141c901d031014440081d90801740034001d0b01d80081011098100f43c899820100c0a007030300e90910b8582c0342164001900285013101603405c50b50a0719108211a9030180c4e0007080d80010203540711080341019030400d0804524030308400d40c80703031749200f051a054050300e4129400724000d0242c0a042d6101d00c0c0c2c10080c0101b0070b48413040c0001d000a080300080490303078000c04402001c580c07a9403e1003000380e10340e805d12544c0b80e01940305000344800740c2e070303584c0008019980c0184880034640d003c40701c510141c5995444007030640d00c2c02500c080c20030007100f0040381d410740849800c624503490b807030a00c044132502800400050300c6800007d0041c101a000d907200e02148900b01d4000c400c50102420107200104c860401c0d5039150700d0b0352000c003d40902c00c0e142690040310b489100c50b40f8201040c2c990b0164040744c1e400f003120031810a091500600c00ca030070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 506349964 1250 506348714 506348833
    0x6070b180309060f03010306051e010b0c0c030706030c02070e04051c0e1002010b0a051504030609020d050f0c040e0312160c0f060605030c01020d0509010c0c080d030507020609 77
    0x8450540c10700c03944c000d4100b444161040c0d03041c500041c004042090800140ca01c00220342e03c0c8613402c0501c00c1c490ba811660030f002483c0708201d000794142d0344c00c02c0038078002c01c900c0e640400c0b84003c03500003c2c100880d40d40000e24440c1140c00f407200080c004501d02d03002c03003662403080b0301c101804401100c65100c0c0c064030603000000f0040029003d681034100c080f0608040e913010001a90720014045040c402e87c00017000b00d5402d2200340000781058100c0e00c0110300080002c40c10740e00c00d48855081c40040d03201c0c0d144680c8003400c00070690901e40a03c2410700c402d400598100501c1210385994804010180c00d0f02610203424440914010004030b150a6045000d084035254149480e000034041d502075103110b48a1340110790b1b0550b20000302612110103540d242c1d814140e1800055505089490040b55035112806000c02c070024100b0010710310040a5038003042c00d09040b400a410010040c0c000381c02030700004c0092a0300084210030020501003c680b80d12049215504880044050702c410700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 506351214 1250 506349964 506349967
    0x301180c0618030b1e070207050307120204020705070e010e0c0406020d120f1e0609060f0b0904060513090c0501141204080409020c0706020d020c2803080f1806070b18030906 76
    0x130050b01d0300c01170b8162020300c2c1c0d003910030103454500c0706998824491117025455440780c0300500190645840f0300607203a10250025017000d0240d55900d0403d5801d80003a040c101603c1c00410103d40304003601a0041d806281040c50f081c2810002510340c0500c0882900340046900c0d801c4842e40280c0c0701c0d00e5181d0980e03030108004440d01c1580055004115000c801d40b6060110225403240d4a22540d411205001d00d1080c58520300b4580e0100d40e042071010702d0788290b03245000078040d102c020325502001c03a03002c00010020814600b130111100c2a0300700c54108040411880c04a4580800720382e140c455600790035200b1b603594a004085031103141c03c42c00c84107002165221840c50001100416238500d0340980e880c203400e0724000c0382e0341d1260360f41d056030010110358143d040b9407003181501400c2510403201520541c44e40c840401580c0700e0744054403018000611b204c107840e21042511a1140c0c1240c1d660b142886c65110106206400f600e40e1030301d004141d0301855007980030400c6550a520181009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 506352464 1250 506351214 506351221
    0x1804050402152109011512061e021b0705010e0402070f1b05030709050c03010b0c010b1509040c17070315150f03050c0a14030c0405060301090b0301180c0618030b 71
    0xc00103c6400700c400c00380e00104401049464a060080351203c0703130403218104140c0d1900e07044411400e8007600c16510326541f109078511141c822020000c600303503034a1025984018044085600203000400c8240c1354205074010b000c00c0e03030b03c010400e0200c2412600903072200c0c50b509103c40d07551001c0e1402080e80b0b441041e220101905904400d04841003202500e035151307940d00d0304005480c41102c001011000400052041a00460207040c000a400f8000181e0507888400b2a1425117280d4884941000226050303440c0d00e418010102e68081529115062031201d400c0e10800c9403014011500341501d60604000303056103140e9510081042a9103551f207c2c1c0403190281c240d449561140e000a4100400a00c050741e0660803110302062540d0b50341e45850940e6030514490300050310b6116881001c110001c1e00390b90390f10145000e080b040600144034100d41c0100750868102c81100ca604000c00d144020216580503080c004035181802c18001418000904d0048041a42c00081c111070411052 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 506353714 1250 506352464 506352487
    0xe0112050c0d0926030411131e0912030b0a12240c02010f060605090112020f0f0d06090603170310051c030f02060610051602031903080a02180405040215 67
    0x200c03048441031612104134400700300300242d642d01c02201c019115080ea2a202106400c0c6510401d508010207000003c0e54402c4050754451200d04400f41501651110821070611040c44000b604072882d5003010058026442c1c04502c0100c030f40e1181c06000700401e01e0b2030781400010002c01d6102003001190401100310400300b00000d26440348a8401580b80561040750400d203486a0000c2c1c60b01a2152130500c1c02a0b03004403000403116407580c070f07445e03000c0c4030307280303a00604601422074000305903101c035116a60240240100d0f07003e90301c8440c8075401c1c1141000480c07841c1c440311151151038070710302360f696036a941d600c0300c0410964026900a4004d4880c00c1c91002c80ca95034000d0036119540329400b25501c01ca00720b81c3d07408243e4480317034401c0043e07880049072401840144801d0218841c3c03411888025000039052038903483d40301581e00d0080e040c0c0010181d0200c0d00f15403013140180c0c03c40c1400c4032032802e1204040081540707405140d41d000401d055541da214804840300f0107980055981c06280c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 506354964 1250 506353714 506353733
    0x3050a0b0405160e060a050706050901150b0903150126071e03150c0e060a0306080a141905030f0c210a09090e2112250e0112050c0d09 59
    0x1424400541c1340b801c2c4032058586442200c42e401400d5071443e007060740b242c40380c2c0002d1a029002700c2c00c940d42c0d07080007c0301c040310800d41d074020001509142e4a50342c0710401c1c58104401e8048413800c1c103d80f10010300c0717a136022256140c00820701c451f8080682c1a850b44a51a1140c40c2e000200040061002d58100003100000641500d2041e000b18908170140c03001c0d1070503070b080c3d500d41c2c002188e0080d240404034140140609080b90080c600441d22668407640bc7c0d08200034182d00f40c821a1585110600011080012a14203003180c8071804005215854903512802170014500e40030a001403038100003581042076994081d0248611035811010800c001d07080d1788040b4052021680000000414402e04c0c803a00341c854800e2000350030b07003001e428038110344808280c10400800209000f0240401411100d4078460603445540010708034000411500c0c1240b00000c840c2017003041e03110708110342d07070115001c03c0f00c4040460100e410b85842c040e0380740d030380600001e8800385840c2c050320b03006000d0b0004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 506356214 1250 506354964 506355001
    0x8040305270f090708190b0d0614180a02040207060e010c0201360b0405120c0a1106030c071103010b040c09030c0f0b0708090d12032004140103050a0b0405 68
    0x35145520104542d0500400e010b0032502c01011900840014240c40402c1c0341c03020000182820004d00020300d03000003545001e01c48000d5410954030700000001850541e40960000c5e4a082d02e04c00d05540140c03020758481121000034011b9401003130641c01c111443c1c0142c5007981140300241b040082c5110000d0003000741804010000350200031100c0c4000003a51442c0c5c280e045040481c5ca010542e443c0c14a0840d4040d000310b40c0b034428a4003800f508505c40b07000d401c0b0320103842c019182c00c0e103540c2020340d1502103040790300740318035000c006020501038210100c9441d2507201240585107204103000a004042d140c07075242d042403c01943c038200590011503c1d00ba28030a0008003011901d540500618902130301410100c0141009048042b40d025009480804002030241851a025170740c1e4a01c05400c0d150800042503c400ca8108030440342e00910040042c01c01d078841c142850305420301004d0312080d910034145a80c5078040344070440c041e08954074105015100384003d0800c518121b03581e24014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 506357464 1250 506356214 506356219
    0xe0102010606050309070605281106010e011809020301060b031e010b04060e1201060f180b010206071e05090306040503040608011d27011d0c090f070804030527 70
    0x3001c0807810038051400d89004010100040481e1410158161420b5004400300b050004924145a1200700b00c1e81d014085000665a0207080202070100740d0310b40141130b04a00307c00c002e640c2c01405030414800070242c0700e0076800e80c08244040140042401403180f0340102900d01000020009400e05500c5006465112141961183d03a656403210203140210b001e00d0f0005400313411001400d01c3d0004148005020b10000091034036901c82c01003030b90203c3c0e548002c445da04e4018110040c0e028600c030b040b21101080c0040d141625007c04001c00c01c8a244822501040141901d881c00a100300107481c102c4d0307406412201241040d0030314030741d2500b06100d0440002c00b02c00010500000c02240311030000d4030f440d15078042e6219484102c074603582d84a500701170311984080d44140c40409000d280c0400808442c0204503d50440c20340b4242045a4030300c038040d09200040c401d0402090210992240d810701c2c002d002500c85150846032441001d001c003141500252002d4036060b80440ca0710300e485000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 506358714 1250 506357464 506357471
    0x90222020316020606030304051215040c030b0109140f130503070b06030c01090812030a0b0d0b0603010501140306010506070503090607060605100c08030f060310180b010e10120309050904030e010201 87
    0x40d0750100e9440004440d011b030541c10074081041103040038000340c0492800c0700182c0d40d042e00d035403855503006c00c8221426189250f5222041040c401c2e208581405003200e51000d200c1400c2c54010208960b10203829600146811000507640b894045101e1080a031b00078140e076a20b140e40c0c18011500c07902659030030303c00c1c001c142034500150300510312030003259084800b0782500d086450355a25103400090a41382c40700c3d1516101d40251b0b840111503151300788039a41225445c149002070508482058200d84541e00b880601e5218039600014514110780701100e060f6070b40c411926043e4110f00907054500c0d00064085407200401040350491400e0baa070640d4005840181480112400b0709524006041484d0400221301c0580b00305075019407012016040321501400d0049007800c03152002c1c141e400a80301000d20030108111140744a005100050324826907043c091112040c100041c405c1001c07000b2180500310070540600319a80c02807a0080070229149070604024040400002049005528 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506359964 1250 506358714 506358751
    0x2310020717091503070c0209180c0102060601020a0b0a06120c03050f160510090e150406050613180e191401092604090e030a0f05030106050901030902220203 69
    0x1151816540400070041c2082480f4074880711411844e807001c1c00810420000300e61450260310760300500c0d8000e00518141d10386a001605c0e4060821650703010580c115041442402240da80c00a104155030780c009206003419146c0d400454020140c81c0d0040c400e800094007078000340302e008111502103a0044003507500341400040300d43e0301c40340e84101c0520f1094249000788414103003100c0745d214208450410354040b50701e8030030112004034215907074000c103159901d1403121410305020f01c0c1c0091038280d40c01d0741002c40601600f01100160b0044043c10380b1403000d030140b0507010750000d60609440d5001e46520b03071608102007150400c80c98003034508110602518072840414400c0b4100243c018510004200d040e140c0c25040312005800700b0180c0e281403101144080580c8070395501d03440c420005564442d1640001303452841001c24403000d115040c801000100c0e013240c00ca40b941d8900740381c00240012203100143d01e01288800a80600300e0b15100850100b050b640154001c4000621b401d50494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506361214 1250 506359964 506360003
    0xc03060106050301060c0b1801050907060221041512111917041205090306090a03080c040608060d240f1107020303071106190203030f01090b0d23100207 67
    0x8002c1c405c010024010384171034400305442c1004550407140b5241c0d01141d686d08607841600b03403030040d41c407207005401400c01080311580420a030301202c00700d5058188200c082891b0300d0880c0c042d5100d40e01419016005112415103e00124403110811980c2005880c0448241c50090b130010182e199001c40034001c008245030203440d0f5060303210369818075080d481d942c0da40d4480e60300e200380e4204000d019051080e0a5196414004503125441c07180041c1404041414020280320002d0a0300d40283c03804c000038001e140c2e0106d00305610541c15907501142c41141e11344000824400c4011440900014002c00c0100132950807490303200b807000c5030510038029406a441a04c1c032810340001d50581c02003000d030001664100145801031b10013440340e81081e00c480e0422890017a4848400e0040c7c000204001e40c1081c00d00ba060b02500314503404002c20950840418103240010401a02c0c441c1c001249604502d192214880070103000f00c1921102629000103501a4000030411140002401d03a08040507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506362464 1250 506361214 506361217
    0x60120010c0e0103060b07060b0102101404051203040f11030a060207050102270f090a06120b01032913020328110d030906050d0b0604060e011e02030406050d0e07080c0306010605 78
    0x6400a0141b58580050f41d60f40300010b00c4114186810340c0622404200d5824a81c0703c1e01c0e041600751060300740c281c07030b140c6820f908000b08400c0c1441001030030700078400803c3c1e01d010002450360303114440024180207a00000c0ca03060305200001c04441c00001c0034001c014041d000303445050038804075440101e01031b01c1a201480c1da020009a086800000d2400c028682141c3e51074001440d680c00281198444070302c035101e0502c009042c0c444909510040040011007104034210024850010342450600310b52013088000c003405001200144088500079075070103200b0440358190400203c96025040c0211703800f0281450400d42e0080d8036142011640e081c40c4800210b039030b0717150350341800e110f051080039120760300000203c551256885002010549810004001514480e10340b030051440a900040000e508140c2104809610808030442c90307400100760b5040d100981800c80d00c4881c1e0402c2400203110001d0390030514841c00c000003030700040226148807221003d0342503501680c2ca0756416900c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506363714 1250 506362464 506362469
    0x21e040e13051015090903020102131d0c0904140a060812070c150c05070617060613030210020c040612030206070f0e212e0c05030609060120010c0e010306 68
    0x19074000309401029001e041c0d00943d00410200608505551901171050442e6003c2c0400c4002d07030b500091001c1d1074198050024000e1082901d040300801d07082c0e071b924400b501d01600c0340d180000d01007404001daa0310307038203c60500b080105030460103261900303e102c090300701482102400e0042d070351042001c6c000c17800ac0300c1c001e070303088180840301504c2c0206280103101c03110449004c100f42c2c0101000010b1080c40810001d00f5a507950034a12050745075000d2019101409161107190204101088034034114031000480740c04550002007401010010ba040c4903401a0340f9034020320f41040802e611002c4100410a24041d0342140d04584ea40d480032380e000100480e5003400726110004052070340c900424001d0200900c040900d07680040c45090724a17100c1041c0382c00090700428100044501d90000d004c40c0b40c1001840203101c04441183c010b00b0901c0b000e46102e0081d100030002030300b66401442844400586c6502c010301000b4030100c06402805424000800151680c1c0041d5003984280a16000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506364964 1250 506363714 506363723
    0x280503030f04020d1203020d050709050d12110106030b0916061b080d0519200a08040f0803010803030a0b09160302070309080601060504210c18021e040e13 68
    0x40c5899003030a03503508907402070040368005458100d450000701030010b15051004503803805612019000050800c1d030340000c000808100d002001004940d940603118040c0c160000c2c0c05881948241004856003400707440c1c02502c42d820640000104401501074920901080c0300741c2d06a00400d0342c00629100040c45080c0c00541184070749400c2120707022584043c144075400151819803104103200941e00116048400a14510b40c140c41149441c0100f646207000c4036200d6800d115200110b40c0b003801440420001c12400f08005810001c0c4840140d90003500300466989a45e510003400359240d0045400c04000c1c0e050020203641390070004040b50286404041c62009124005400c41c003d410000d400c0d0200004a000002c1c41107061098501070301c01ca9130f480f0760f503d0900400803500844036800041e1511101d522001040106400c0004d03035503910848840c41902c281e031800a40540d1020000b40c0c094011b91804e90709901d0002e20881d46a0407000d4081c2c0e84140c00398007005a03d0074043e2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506366214 1250 506364964 506364967
    0x5071d010e13020603070507210f08010612020c190c03140106060207030308061815011119030f11070905010e0601020c090610260a0612080d090804030212280503 71
    0xb0014900340d030107907501000360700c1c185040c48d07c2519044502c600b001c56242c00a0740d88024005015030203c3e90202c5c80d816805c0080c0300d5490f0401c01840706225034100d4503072030750106113501c5000051101106d00e18820784100140945824140e0901c080c0748012115940741503004282e055041c040c46040b0f40c410340162101d80d203151001c0e100928000c0c00582c0c0161840c81181c0035002204586000e0030014801c01c00c2d4812490014041c5244030b10211207541c8900c0780710441d608240700008040e0f51500d000007582072520000e50f0200424660044c0c180119100460f070b0707601c980c6c03226040b541c1c2421040d86c0c40c0c0710b150069880d2881e80111740d800a5000d0001505420040c40300c4c02004424078148103400d0f40d01c103115844002d02c01d03810342c0310034103542406a0240d15010715400b410706800d4541c0c0798056552024000e10402d44180141511000440f082c040200181c5005540103001380c040721141e492a1600c0e101c04829070303121800100c05071010b10346012140d0101581c03200c010b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506367464 1250 506366214 506366251
    0x10e010f120f030504030b0a1b2d02010204030b15010f0f02030a200a060e060f0910090303060e270313050409020f03031903060b070210030e0a05071d010e 68
    0x500b00740064206030700307000040000100294a0308011403003511100000154850000140400e034000f5403000d0013000881166610b1a24904092404490010b0309001321040100760076406805a80d00160500d4002e504204c0f070995005100c2c1c0452109136614800c011500780c09807224054982c1c041c1c01a4403c0c040390081e40d01032140380009158131a0a44c01060001a000c0d15010401d081190095103c60030000420307410002241c1049407c904800d081c034011841c3d5545280e410010f4070903644a03400e150034980254009d4000c0c0440a04480701f5251119881d6260f4000d0092456003455070303141d9042203403001c4244e80352008080a502e0281d403400040002815040300145d0780100c201604000c0c0c0d640410040c0408400e191701080b1710f030401600a0102d420f03941c422030103418100308000050b030f41c1d2009a01e000400e420300103940780035030301c2c440d240c1900010010308500c41c0c4e81000c80c2c081044022040c5000e440040b400042ea242d4a01d101c22040907100c100303c2c1c003c4c02c00308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506368714 1250 506367464 506367473
    0x606030103200f060c010b2403040321050106051c060e1311090a090c090507140a2003030a0c020102040b0901141c02190809060412091706010e010f12 66
    0x114811000400b2514540800b0f80082c03105d80c811261010756079940c0d03502e400710342000c089000c010b104254030015841c43e910213070800c40c44010001001c100300e03041600345096614100300740242480300200f05035a1a508017520580c04010081c3d503200e00c6d1f80d50011401d5090045070305846840e07001c099191681c1c404450111541c07407045409810160350400ca903216400302a01c40d264590022500c96003500b450b4012144c540c2100720101d0a00082054198025007044188140703000119038940201e401100c0d40c40650042d904042d5041c202c50a4418001028600a5800031003c1101710f8030f02ca02079081b44654895501000000e10020380c5d2580620b00d005600488a4111403405009804914001c156401c3c4a01c60075130105801e502c06000647d00000307601d041c20700d00010b00302884595034544c00204010080411120400ba81601c100001d00040c150ba0100a40c1841c03002105c5171159401d001c0c10039008000d0000280d0440030640d51811141c010707031501b601911580b41d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506369964 1250 506368714 506368763
    0x4020d02060309010e0102121503071a0306060c0307030c15091509050c090106050d1a0904200402070c0305161208030a021c0504030917030d02032d040b0606030103 72
    0x43c038082d56849803046402d580078002000f0744000c030076250720746180800c800710900001ea00814020350000409105030304202c144414200d0316800015100d90351303c0c2c0081d86510884408031400d00002c6690810580c01504c071184841c454400110043c100a5002c0119414600054440c0d405a0a440790054540d0300c1005901e00810586500990340030115200311000c1c1d201c00000340340082c2080c0d90b200720340300d1000c81e2108004d200540740340c02c20024004003005813003e00481c1404503510080300311201c070907000880292096444981604090440e00114401070700d0500071110008401905041c00e0303015100c04849031040309038941c845503c10341006000c0c3d01c52030350821810442803c0d40140c07006000c00e0000104c0c13907207050b00d4010403051903070344086840b0b002c0400700740c0300714004000c1d504004601c1c00c00680300c0e5100c00d04a981200407000a60010322980e003075401030100780003000c0c461401440c400000d40c84040038010341d44400d00c00500318402400c420b0310054803001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506371214 1250 506369964 506369971
    0x1060b040b07020a290c0309030d0206070201051005010504060e030c10030e010b030328090b070c03140c06040603020702010c082d0712031805010c110712020f06031f03080306090f04020d020603 85
    0x40700c0c00c003030823800800d00c0d040e110034141001d81d00c0b1808024001c3c0d824024a5407200310248080d850601e0300d00040c0031401039014080c02e10201c280c0001c0d141e01d007001641d50032500202554005080240d01600405920864005030f5080200a10090a00008403490505180a00388411188a070284004040d00100e4410030002c10800035091311220050140e407405071004026181ca5882c1504080e90b031846240710343d8003e841d80364103a42e2a681501c0072a03005003400b5a440a803480121342c0e041500c00d0081c142035010a070035900425000b0b610036070103000050002c1c1e000b803c1c00d8105081c091998000c010034903d8448003c40351194010a8440c442595055240300c0103030380d50350943d00c541a07100001205035202c1d90303070284200102801007900b000c030b004009026070041210600c120004a0245200001040840440e1080c80000001c03c0d01594182034803484c04011a500a6809510908200d8085107002d8189161240180ea00905560803444240e09100050300000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506372464 1250 506371214 506371237
    0x207091103041403121504050109050402181503030c0d090f0e040f140f010e06060627061b03040810060b0904050703020f18030d0503040803070c0501060b040b07020a29 74
    0x1c0c030000d1180016412203030700900c440041c0201d800e414005020842300142d000b80c00780c504210034880580c541d0080781e0303c6299218a440c026940b10f01d20781200014052000f07401d8440010309c0a441c02c0b001c105590b032410341c1d42d03c00641580d07503d40c400904c629405441c96413110305010800090404043d02c04052095a18200d0000d8140e14182811006440c42a0913510b48940c1d003103540080c000c081c3e200740110780d554200b0010f4140d0141d050703400b6080711001d4200d060004119a40c030001e5540d4400d03410500f10a4040e90b03403405440f5002841403213074500c25202000748401413802030788103072480400d50303500b000640410000980340c050400401d2603401c1007000391501c0f090f4002c203040e0f4180700c9014070304002c010526207000108460002000300c05d0043c07100241e46001281d400507038030300d4032900040032800d0a60040280c0e41c4400d604141c00180041c1d0580035034080d03c2c94a003301c4103444460f03035a50200c1007403c5996605070203040c0e86c2401150a0060708050f20705551724 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506373714 1250 506372464 506372467
    0xe06030d030e2e0b1210200705030c070503030f072402040f0f0e16080c090405012709050c3001020316051608030c280207091103041403 60
    0x5a544510590382403075403102c810078040c0003021003001d68010228901e4042e141c81d100e2024411701c070b54035081103441c0f4500c40ba40303400d224401c0001310f250400c0000041d010031541c1e40039519145640c1d901241800505004078140018145800301c1a1502c0c8030030020001e140c40301c140e41c4d4086500c1c3d0410043c1c1c2da40101d50342104c1111040c400781c40544007039080503807081c0c2480f840220260341548040303042a0114204664510074071800c2c24070351954241580c0940300c2111306400d03402910030306034100d480c00c40009010314a40216540d1020205c2100e65a0000c40f01c680c4143c803078880b406802c80d40a0245002c03142450303c1d401c04000380341e8410030b0b0130003071909a1a03801c215007204100d2582d000300c140180d8000040340b021004499041072458080d61360368101100c5c4040c800034100980220009130911a500d0441301454141c0103849840707404081d41c030402030386030070940c001440340c01070118064501d44078810208141e5200c190550b55281e4550901c1100c1d081d1b000d080307000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506374964 1250 506373714 506373733
    0x130206071212050c0d06081b1005070b10060e062107031107081908010e0604020702041113030308011e230303040801060e0f040209060907020313060c020a0e06030d030e 74
    0x10500c0b60078021600c9000040d611040d017071074401541c1164004d40d0254110190006900c03070344034540e001210080d18407003400100340005907424010410090282c0024904000c56614404101400c0d15065110a088103203000e00344586030240c01c04d8502001c1c140400e860004c0d030300880300c4d9400080c6103400314841e01c040240300f556402540040b10112004038521060304030303001c00d501011034180740100040d13150105400d8103000241485000c0ca90014808095480700c0d000041080565001c00d45c0e2414603031810140035010344010307070014004800100d6220340c048031400c05110034020442e641c034240404a904c0301130901214002240c90f084c1480135440030b0001d00010f1484900005541e4601100c084950100804944a6200c24810800140d03207460072136421400682d00310b41681c1d5006026840c5128001078200100b40003807000030700c1584144c007044e90030701c25603120103815560a02404644c205944480d4160841c50442c00d40522030344c032515048044a00702c800740c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506376214 1250 506374964 506374997
    0x40b0a110f040f08010504080a0320070818040509030409050c070203011103012405071b091a03010e060106020a080304060f05010609031b0302030c011d04050f0403081302060712 78
    0xa21600c051400700c00080b904209081c000c002400c02000070b4002070245103000d540d00e000c188508800320f02030503514081240500b40703a41c16882840307a0104076603a0f42e441402c01000301d03003180c80f485600d41e0100250910b1030405000d030341c0c001e003c020001c0d4146801d0200000c05010700926130200c6180510032940075940c24014500641e50103d032241c0c0c0e13941015843d00c00c200d5020343c6d2200700031842e2800d49c80c042c0e000341201d0310a90850100341d0480d0148441441c2000b40c1ea000362000b03401c04180880072190b00318040d10760102203008102c141190304d0548d448203000d03c604000360300000400400b0540350300c02160701c90b128000000740e1680c942d602408880c0c00303800c07500028014400920400c84008101c21080c03400c00c603492000380c51640001d5a0351a4001414100803045100d540e1100c2c6004c0e40c0241030200800c05d0105103000d681401c03e020701141c09800040000d00400c21044103080404055034016280d00c0c9008901d0b01da0800c0b04040c00481810450303600007594204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506377464 1250 506376214 506376217
    0x12120703030912051e220303111513060903050d02030a05220c0902090d0501090503030a150b0a0507021c12231c140705040503060106090b03040b0a11 66
    0x94425200051400524101401c80903107118100c010b1040400860061005820040c1145032004403000d56400c2540010507240550410603080310201c040044201a00702c450541c2c158001000c03500c1440040c58507401407407003071303840500c88004100c0100c0491503541001848a0003420030520707002e000340b6948205d1b4822180301107001d95940c10f00c0098001c0140780030b000191081c0030b03a003001103901e0760100603c0510601d1039465000680d40c80c1a1906002e0225842e0040000c0218480b00e08003d030b2690700848032842c1e124503000c45140040020350806040e40d4110380401e061507403d5074103032403276030050000b41d07400021490406021074a1440310003a0b903100ba0a01904080102d9001d00b000241600c400b5510000100424042c400003080d641c65130745240315541442c00070140000204003205201c1d010076101c0080103190340d0444020001c699003130b401c490311603982d04000c82d1511064007408606110800200b0041102100c209030001070715000040c44048811130040075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506378714 1250 506377464 506377477
    0x6050a030b040c0b031e0403120e03190f0504090f0906020c030d0c0206060d170c01022703150105060d14070e12060907031407050607030c0b09010b0a051212 69
    0x708881101040308100340f1843e030000620b1103808217421810400400c1082d400c032480808034038155803000800b031605c107949951022490b01300800c0b0850f80c0d0b840454a0341e100c0c500d03801e8040607100c0740d090120300c00c50052001c09401e40e01d40d07040504200611010305001e09220914a07203e0b80701002081862000380f40000c140c100540c0d1ba03407485010002a603a158a403001503401ca4000c1042c2c517224003a0800c00160b02c82c0d0103450f44012191084c000703009800c44034145610104022500140a8040c40c590010342c0300980002c03031040040650310f000e16041241e0b59003560004104500b0840041c06680003008400325003040d40d038096610303034074089444c00c002940105c1c1541c05800d051449140341c88442c0007900300c525020100307603600d40e01440000e0880149071040c622030740c014400c2c00054103000702016981c42d01818020002c003460441643c61000b004041120544148070745071041001400c0d002501e8a40720030000f5010000160030490302542c001c1c100e000281d100103214 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506379964 1250 506378714 506378723
    0x40314030c25050105070c080301210c0f0e0f04031b03021009082a07050907021e031c02030615091912140a031b06060302090708011401020304050609100306050a03 72
    0x185505509016007540c0000d0000407c4c440f0043c4100042070100e0100ca040d58508043d0610940610124030041080f1410241c42c0881604010400803501c0c036450302200d141b4805140e40e92545000d00520300e0b4103440003030205603040c8141c0d00d401c01c0300b000c908030360740240159421003800001000958018040c104c940900018000703072502d62034030030500041160483c061009540300100c0383d4403c1c5c82e004191083c1e202000081e0007500c02c012400c00c171110128181204880c2c2010b2a943e03810030041c0011003110440014800046403007a40d00c5000c004200284c0e80ca001090400300790310502d41680c0000070000f40350445c800241c0c1d440024085a10410004651801e200010750b048114000b19a00441ca401c800300354444810038a0300c100500c0052284004d00c1e2182c0205825440250480040402c1020540d04549168102d90320900c15003910255000126140d11440c0581c0d40e00510900030f685040c100f90844820050050038001001c07a224400107002030000e0340202c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506381214 1250 506379964 506380027
    0xc080610080f030c100209040e030409090215180f190803030604140f190b09010b0a080114060d050c0f0f1b060f0105121e010f0b0603040314030c 64
    0x4103030300341048a0b10166500c1400340d0f0a08200c1c0d510b040c0c0f20018850504c100310b80203d5a40420b0356180c2c4020809449d4030103e80d925591001214083c02e03102031706034421080b0300308520030146044201c0301c800c40d88401400b080c0203d5400c02640c80c0c2512051070704410341030f80620003e034903010040e015214402c003c540b00d1a08104000541c1c006030389180251103501c0900820341480314a00740c0000c11740442118100d12076980100070700c004801070744d000c0310f50301c0000b4252806d10001c0407901c1c510395072007040703a8842100d15068000c200c40107400040400c00c1e500c0450542e4007031500b2800740071015281079034641d80384800e6080310030038944c4083e0002d01c0c01755554054881840030804070010b0019498068031341c110a0f60140310f0319000750100040020030301024052006403c1d4002021599000e40220490003000c0b03407551684040e02d40315010303055107410300a4070b00c1980e055071401c60542c1c82000381d1034142c0000c0e100c05001c0070306000d14a40c080f00c40800080701c0c49a9a01d40e03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506382464 1250 506381214 506381219
    0x111207120c110c120607050c1c0807230d0b03010b1513060e0f27010905010f170a0f0c17060415050405070501050c150c1201061106040303090c080610 66
    0x40d04192a210050344035080c1204d0388003a02d50046a41d83c0d10060318200746440d010710703888117803c2016802040340c5038003c1c82e40c444009508101034600954195a0729540e900300b103402501c29000b10486c85800c014140101c5507620041d4015451139800031f80049030000b00c21000c140c001884070305401d1209404540030b0070500b650300c00303040204001c2c5032084454a4034404150400203c180c01da004040035540c41d07000c1c0104016000c14200030480c4102590303510f0200b01d00512080c01503006e10700808600050010824010700c80000c110009417030b00041e2559020810180c2103001c4907114104440000d00262006072643d6041c11035001d801c881c9424580746048800400c042d1080305d2406080c800841e4001800009686003801c04aa491040001c02c501c4d180d800815041900c003c6e101b0030015004041c007030003420b400544a114240d8840c0401c3e074410150381881281680312400040100384a0381002c40961300075140d6005450700c03002036505002c011101138101e8400310204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506383714 1250 506382464 506382497
    0x7090b030102072a0e0a141e0408070821220506060f0a080a0f1b0803071403090406030614060402030112060908070b2e060c030e040e0109030c05010c03111207120c 72
    0x180c0d110160030300c0b82c08403c0c1d42350589403204502503c050503045002c603203801001b840c001100d641ca1103884540781099000c01c0a6403108000704e8448088814a4100b0b19084848581d00c0c014107500c036004d802c041d5102c3c03007400205114510030540c4240c07c41800039401c03400307002c03000ca05030081c0c00c21030780e0b5403640c104003c5c1007600c0c824241a29200301010001c20b032001c01903800c040e9210246071580054005290b1a500502441e940d001c2d15141001040010541c030200c40c0d04243c604049869603840100000c80c0404d201d26220303d1120881c2c0700001e000e40e40300c0c168080c855000e290400c1000d4407001a0344c0022141d001d01070100881404460742d900c2003030b003660040010741006050070110b00410304544004000d0500a02c107480914942d90358002c080c044203041d00030050a032050400074294070101da401c0e10b0039442e040380c030108bc0b4407078081c00344070310030024040780f030100a0007250390788010042c8040c081061145c00c1d545090130701d010b0700c0741a404a0707850844600d00c5c1c0a9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506384964 1250 506383714 506383751
    0x4110d110a170402181602070e1b1608030a022205010f0c05150a061e080c010e010c0615181a0904051603030207090b030102072a0e0a 59
    0x1514581240248988a03110b5408000101090962540c80029880760b1010420140b0b44d400150b00c0400740600b0407228018a81e124845420710b98211001c1c00c2d5110190254904159a201002c032407002d24442c0010048000308071000741c0d022500411880e5490300c1200741c00544e81c0c44001e6400007154003817540c024903010607504820240292261070440060005284d00007080c2c00c0c00082030851080c048144043c54503c000c085c0102d189241c0200500014402030107604404604046c0102e51803444400e40001c1e54916801800a0002c01c3c00540300d807034120702c5950410a54094280000702d081c002c01001a8405895504c03490078143c41000040c94120024003040c5006200e0003801c9603003003d0300c0342c10350650b41e4285540b41d904006041c502ca05401258800c510b803400070030141d0008450007101e1000c03c08001207280c0c10109820307440340359000b4011001b0500502c200120422100842c101002c03080c90400d691007103600000001181c10144072560341c00f100100c142d0100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506386214 1250 506384964 506384981
    0x304081606050a0206010e0c0c070b0d181707170a23072a0302121005010b030403080a1a12060406140402092a0c0a020a0609080706180504110d 63
    0x2032290030b00c3c150103402580c41005208003854502020041690034402104885981001c90151005540c545450301c4441e0702c0700d5a00301c6001c2c90600c1c15101c0403024038030075042c1a80b1502410810400d1200b01c0120340089409460130941210003045081208000b00b18000e0b850729000d5917081211910460144084201e82c81d0080c104003420019821040e0507140c1d400101e05000d82c2a400101010000d00310b400003900201485070343e00c0120400210b9114400705002d040c06541c1c3c8a0102c5541800107a4000307002c50090000700d05440c0483d00140e0200142003859035410901000295000c60105201905a00324006100512140f030080042c19210800f004400341040d40c089103104100a050201002050120051201003003080480041c80c02a865854100760b6200a03120035070030400f00d1103650301c2c00002800e58001e402c110104c440d00000351184078901032060b2084400c030010a2044032050718081080d81c0c0340e200d12034061540c10206500ca0305011004400c460526 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506387464 1250 506386214 506386217
    0x30e0108070801121b05090103030809101b050309010b060d06030312060b070213020d09140606100503130507030203030301090b1509060702060a032d0f02030615030601110304081606 80
    0x2840103105200d034544e02a00d400f40e100b02120207541925481104d0f0075042d130401540324401c0c0000000b810b50280b840b034041c4480c0010340d0308800907104070030112a0240415100c5501030000e48484a00ad040070790391240d107000010409072441c40000c6c0c010752100c48016401e81c0d4515043c018903030300c910504030b5148404000c0245900301b030411415402a200c0c02071044001c260000c0305000540c0540b907144245140c02d1081c0e0340d2038039080f00302514540d00c5020354814000001d0044c40e104440d40b0b9018850303201c0501e9030305c5690b00242e6141c03401c2020741c3c0c288628200000181c500b0401140241505000015400d51180401c004001764803450f1340045000c1c00690280c0da03c4e2822581c200e80d0448440d542c420484178140c014240c2d00c03642c0406170885840c80714140d01c1a482414641d58a00020412204c48414200880c0800e03a4015008054010100300c002d100d00000e5400203414105101615040c0402e10318541c4070360058941c0e5000070050480d14421107040c0c20251008e03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506388714 1250 506387464 506387477
    0x501030213020705070b07081206271b03040c0e060306070909050a11070c050a0501030207050705041d06011d0f0412030c03020c01020c0a1b050d060f06050d030e010807 74
    0x1590000340015000d84101070340240c0c0080d08104001040002c080100000e2812584030f0845040884460300044841010034900500092152070850117003481d4101e00040110317600c46000820804010091100d2104070480c1d9403410000700c1140a544524414248040e9050905000ea0740f2054060560340c0280e000000344440280c104e201d800948604c01400038543d500c401a80c4040e00e00d007000901605000101c10b800e1156448503001030701c00a543e4001160b58820045041f441343d1540540075803c40c40c41030200d403400381c0041412a801096840c3d0084003200e516007017420a034807000d44003028040400390090030540b010390250744000707039980510305610f4510071106007040041c01c045c1c0d6140000e0609009905481040c280c42e4000c44d21201d10105c015903c8118090540350b540b0075421084006500010030401d40c0d0028008402221096aa50028207404400d9801140c0c680c140450070780c5480030106541030017a80c80c0c03941f0819183c0054104c035800740850080240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506389964 1250 506388714 506388719
    0x2040905160e10122007030207050307050310050c1b030a030b0409110d210207050108010510141809250309170c07030c0f2606061e030604050607120501 67
    0x498100b03c0800010710301313003042c1044d010544c0100070003034140003401c1d01c02c010034000c580c1c003030f070700701400318a4485e400312036007a81c0b14010183d546c2c00c01d129099055002a40480315050ba0707401a0382c0001043c0074280c00e02190400003242107103000c080400343e900204c1c00e2250207a16020f03180c043c500641702001703600250340b158403d50803118802130203001d866038400104800580901e0815843c0300401024121001c002501c4000502c030700742c001202440041003500e000b8880740798074035290720341403540c0d20382009425054000d114042092510f44142c9502c541715140030921401c40e6252140e800f40171460384195203818414504101440d001c2850300049000c0d92001c24800300440203500e0301111840f841c070f0039600b908020090284001c000441041100225007600c00160030706c42c000b000390319928859006503425503259445030700428000c1c2804d500d0101283e44440950304000e0105021920b012f07419078044034660310050410001da9884840a422282404820300c903d51 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506391214 1250 506389964 506389969
    0x60b0306010b0901120e0a060e010b040c1407031404030c030b07140c060106050d18140d0f080f1305060709031e0b06040c020106170a15141b0d02040905160e 69
    0x1c851941c10b034171a81d0319085030b210100c081000d241e206510034002e000c9003a60261840c0a410b0100c40340c3e0007030b41000c5a054000c0d00078000125041443c02020342800080e40b001c9a440040980c00310a03480d0800c800300c0032403010599840a14014510a140c0d4100710100510b100c00701560000c4410040c0310b4502b07001d0011541c281111014901161103810319035044004003403601591043e20000c1c00c0c40004c2107080743d4401482030a02080c0c07440c82d1244071040d00c440d644004003000140024000401c65581c800c5016004885a00410302c11009513980c0c9190000c26603244011070a008810410040252109015541c4a201030907400c051030b50750000c0040c2c040d2815200d6600d420380042101c2c0300b588084d00800910300c15000b0b440c03000b02c0307058a64400e401d0a83d54105440070000798009180204008161021000301c682c3c2e0303030010b901000321a400e034030102214080201c1c0492141500141c80541113151002a031410301ca490782100100200c03030441400007207580700303030545d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506392464 1250 506391214 506391227
    0x5060a020a0801090203132012070306050108010e0d0f181404060f05030307150e0607080a05060609090f0403020a0b10050319030c0201120b0402040e04060509070806010501140d0207060b0306010b0901 88
    0x103500054064440a0307a020100000c00e15400c20fa4100b49c070085002c82100340010004100c03409042d0400260341c90b1074549098885600d03088050707901404058400c944a8200c0b155009000d05c0c0101d1303402040d94000781003031025400344080c1c444084040225180074070030348008015414540d96171603d0140801d80360301030010040c0c00e44d407101028030304490990300510000e8084030b09032400c0c0d00d80140050403000042c1d0303015521a1810b8001181400d141c01120040d11000b80511250743d1012005244600010400c600310700450001100148400020034051802100c2050143d414074084c5490b01e00301040c0701c2e13140a0030040038404260469680c0002c01e40a280c000f605c0880302c03040102525110115540052001a000440075284074559025511844c2c00b8413080d240c070050346903500390314051582c031500264010401036000b0280d800880704030000c100d0400e5100301882c012030f0030409050314070b20740760f440c82c00e141e2070182310150160441c1e0082900f00000a400201b02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506393714 1250 506392464 506392501
    0x1052508012409050604030b071205010302091303030f1d1002071104050c0f04030f0606090b0108061201090501111210061209112d010504061b0f05060a020a0801090203 74
    0x21030605070050910103110f0015400030780030103005569101e03a24640040c00320030444600c800643c074000c01c000960b0407401668100d90300100342800540b200c19015807440c590300030032000d0544c1c030840c81e0038241950080c0c3c1c21084071070a0115541034849403440c207040000340311188880c070404c400c070700040c1c100e140713030603451000d650002e107030f580740440301c9024840c081e0f9002920902040c00000c006502204103c094403456041c420944d80304402020760389000351031804a0305440000300a410000e04080850940c04004034132850151501403c440303141c8007051400c03c0000314250510003480450750406102d40703010241624010000f03000c0034480011522094840d01c8003000d0002d08075510030105401051440c0403000482488040b2840c90507003600c400710b447d41c0050329030040c000c0d1401c94a040e10b0303010a64505821011034200c81100c220740319842007290201145080201d81d1103192488001a03540310302010161100d00c059014050743c174010001c0214100381d44219032074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506394964 1250 506393714 506393759
    0x1020c100c140309090103050d0216030f121b0302031b0d08040f0302150a0207021504080c01050c0a0f05100b040b0109091508030a1d0306360105250801 67
    0x80004001990b14150700c24041d9079903002c841000080140000800c82210b103072505d4007111003401c40801c190318003032502c5c070003d4242541144000040303213a400c100b010341c600c6898000341c0b000f20700da0741c4031002c2c804040035030041e4400b1851001581410180150a010140c000c1422580b9483d004210b200010700080909500110f5070003014002c2201b58104110b204250b0200e2034400c40b020020f40102c40d00768480ca43c1c2c0c1c3e5a00e40ea040c1403508440c1038604a60150405521082c01580e032540040c142440d01d01c52040c075400450036100d13001c4001449072026044001d8a920f400f000e580d001c51845111340d141020140c007680e08031020b0821102d050a010822442c2d0603445000695180d2124545000014180c250b4950000d01050411001400c0c548129611001c1c182c2d40c20089510806401c480000c940300b90005075018002d4804820060050140c40d03d03540d0300303641c0203a4828041c00005a44004002c80c40f0f21521110015841d000d0010740c540b48a8100c005070741e814520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506396214 1250 506394964 506394983
    0x30316050c0907081603091511041e0e0901050c1603051209101a10050c0304030c090f05070206040b1f050603010b030a06060518040209010306210201020c100c 70
    0x40400c24248801d0300e4101005000e800307140341c80701c405000d24800321600c4180f0038010090b910f50078001d00c1200002504140c0034940c1c0030150101741c009080f5000070050750201800000343e60481d443c0c501540d040241e03030216003a880c12210300c22004000d02404000d9040008201c07200b10114155000c4490315415004002c0c01c5040036142c61040c142c05c2c01590041034200004104001b130104d41d14040d814003007209640b08004684600601d400e200c0d031240790b462100c0e41c00d41c4600701418020501c102030368905070f941c2e030340c2c000311f288158070030f180241e00c58242c04085250b9226159220640c0e0019100d645040e65604551040081411240c51610840b46c1c46410b40d907100c11015002c054451030f560f58486159500c40d400840d8031000541c20315a0200d4014814800d9030b0104059042c0200c220303000d0410400130790845500181019583c01001464000e110b405003141c03041b00c2200300c404541400020304120019070454040d002512064002c150b00040407260140c0081108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506397464 1250 506396214 506396257
    0x509010507230106030b06040e07030b060a240201060b04080a02010c11030102040305010b190501140711040516030e0102031e090f010c0f1706011409040f06120209010509060303 78
    0xb00c5118180c10400e030750254240b0080e0000c000e055102000784c03400744501d140704d41d482c43c00700015103129140711ba1440e000a541000000c01545d0740390b402c84c2c1d0007003214244548810211075000700b8003a00c0b812030145001c44055643e0284503a0019140b1240ca55203098241402e4075a0f0300700d0b24600031b0402c0354a191540030b004c071500428840ca01b00034001d40d41d03207940e030801a0280c454244000e1003566201c00e025030700301d20750a40404441d0180c6400034815255a80700010350005070098810034415440f001c407694440c4100d0340b0a0010304011a001d4510481c001c2c110307041a015003016a2040042c000b036000140701d4220051607808a0300125a558604181840c50442ea1100700e9820503c03190844c81d0050441203000616540d58001d0760340d41d040c807168010040d0f072101c0c040380c074002411500b00000001803076203001c040c1001c2801280c2c0003a0303904591050b4000003850380a03120b4a402c40c5840300000d401802d08640304440d03030811000090302da10420720518101410a88034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506398714 1250 506397464 506397473
    0x406050f0d0e060a20040e01030b1e0f071d0a09020c010603120809061605070b060d2415051302160b0c0301090b04020c071a04080f0c0306160509010507 67
    0x201030000342c4800d8400c1030810400500103030812681220701d802030f50124820001c0404103030340c00c540502c10036005517480e548030010000d1002d0440b00021024a1120850000e403000c854011b403c0c1c48440d101515150340014000e50800c00d1325001608a9484500a551207038040025148013180c0141d503900100d00c41c03801801e96a10041ca48900740303d0147d52641c00918080c418120030054074405e640d1000c130100f002c034642d080f000c0071460a010403004285200a051b07407007400507005040030030b06a20703904485000d40750610400c00d001014054080ca485c05190300425040609600d00d80c00c01000507400951a03c002c551035a000c03482c0400028010f45040405811045610490a140c4803052040c1d20034020b0600031401c0054008140c240384c1f0886070b14490310000f4040280c00c0c1001c0d4050002c020720000d02c245410f000120b07081c0010f02ca4408403000740ca00a000001000b0103160030000000e001102c804605c144100506801c50211010040300f4030b01955541d026180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506399964 1250 506398714 506398721
    0x150207020d12030204030b15180412031109031504030e0a03051005100e0403050705070506030c0712140f07021005040510080901020f04120b18030a0e031005070807140406050f0d 78
    0x10242c02d83d65000d003403115a03048181048c0c04580b00b600d0710a0818a043d1034881003036400d807401441003a4001001c079425100303911038660210701600d0a8a00071010002900d00f8241b036203044c00d071110307260078001015042844901d84042c1a00d000d4580c1786141c8403942c60714881c0d50f07070340c4210f030b242e07000106845281461240078080340401540c1506250900511a8201042c122402c0c818501d01240c1c1f46005001e132803059602c81c05007480d0241c00d076558003800310010700314400e1019485904082c58015805050300000c925102d0742c5419250042200c1e00c1a015021400d10008000612090321840120000c081d83c50a0010480d101c4141a900911903003054080070070002c80c0c04280e035081024100540c40c01040598620f46400440104d11144043c103510541c0c0200a18119103004489461284100030240d13980d0509400c10481510012100c1c0c40000d161b0204022050747c214140e810702880b4070000d60308103030506030060042d04c0340c840180b0081c000440c4400da4048181c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506401214 1250 506399964 506399969
    0x1a060306040207120c150b090105100207080102030c09090610021c210f0c0206070f0c031407230a110f0d0f060c0e0607020604051c0605010f03150207020d12030204 72
    0x913203441490600c0001d096a00305242241c0261035030105090b1081c840c040c1c410003000080007091f40307910b058200008035003840ca20500b076010f0190009070300c1c4000e202035445140d80300b10003640c540000f01004040d0b1801402580b00d03403242020b41d6000359001a2102c81d0b01c080c0c04506a84480d90401654201003000e00c0041c003e0784030014115201403071308202c2c1c1200300c2c0c0809001d5885240026a08e0312400c460000c000b5400c410032060b03144c410100c20310320a01a0400a44a074000145079030254003401c019200348400c00d03980612125007100e8094811100000391009a46594a03218805821400e191060f0305130740c940700181e55503041034017659900000000b00380341b040c03415801038542805501c01060b511385e460603841c10600212078030705500800561030142000702700b200c0c86c6905810340901502008007000003405910a10b0b020341641c0006071089881d514200c9555801c68598003096801030200c280140c482d5070782d802071207031300480252411824107c124028041da9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506402464 1250 506401214 506401223
    0x609050703050d0309030318050d140d09141212010b18040e0601060e18041202010b060f030a0605041e091434080d140906040303180503011a060306040207 68
    0xd212a030f2025815901c0854460700c01d88040c0300d030070680151110140d000810280103500074680102c05103110314a003800380e120241ca058180b0101541c14800c80724450012101c608404090520f95181003010b03012111b44551030501e0305240442c1940c40b07400600c50030760030040204441c0108401050300590144006c1c00411015106c1c1e1f5246540c2c0f002031103940046030720454854654140344075582401d610400780460591036554607074440c030b019800c9103c115561003c910b04160b07074034001484100c850381c441d2038881c18480e60440407995182c2c8058481e86c6802c0d40b1410150344680c41d09031150360a030001071028154241000c10441c1a042e00003e4015407101310135002460f083c0c1e110442c814111175500c41e0700c8213000000712070341e40900c01d00c552002c46050300091050343d040c41400300d46090741d4140070401021a03c80e4001e1b0704100c003c00c4154003181012001600d03500d006003001c078001c2c81400d041c000d280380074808c80c1c04214000d040c000009400317500c0f20b0301140c4605038007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506403714 1250 506402464 506402473
    0x20405070c020405180a02060c0a290f04030f180302150c06090a0206041e080307120320160804080706031416080c0309011d0c0102010c030e030304060905070305 71
    0x8a40041007520242400c912030f500d030034003280600382209102566600490300a000c014502d07000c000346034010444582983c07281fa488440003807010050b0240c55136040c0040100101c400c1d40007034038588000e0282d11902d05450410000c00e502c00c14002e00852a4103088002144010180b8424541e0390400394100310822104241405103100a0010041c600c3c01e07211607454440941e41c0311070050902940c440d906110504ca529070382480500b004030b40900c0c1e048500c2e0f80f050200d007507801c00075003504d5180c98140c60900391038160080290210858003a00d8060741100c2e038107061800303801e2040e02c0b00d0015501d01c01c20007040000b210090580d240c1280d03411940c1c1c20000340508603c4184000703001e003c8021072401c0b8280c90030f070b0f60000040c0d2070b25103e43da2824214007803900001d0114020350b4840408089e013413682144881244248000b8080102c0300d24000390075100b10444c103000b01468030210300d05000c00407060320341059100e400461007039281c2c00c1581c9844060341024046014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506404964 1250 506403714 506403721
    0xc0319021303080414040204140913150524010c0611090303070501020301150513061202090d03020c0316030309050d0512120417030105030319051909031a16110307020405 75
    0x35410b02070000c40321100d282074490585c0500b070000760b01a910809540d0541c1100c04e40e002c0c40c0103411198009a160307519042c591058032400380a0900000d00c0c1d0b6010707a170f601400030880110b80d00841c00e00c2d04140b220585c403081000280074000d501d00c060b00050b5160004180a50140101e50017003d000b42129102c048500b0554003e5100b0320400c240e40c41c00c1d503401e83d6401d00400c1034840070501d800030480f485286ca07030144c2d4016141827601c402c6941c00c02c4104102e64940c0b0280000c1800399009200700520142070518100e040740b941801c81c2c044031820000a03500c030188005032507090301d007542002a14600a8a44507124a682d0045c032008500c02d0318000003202500e00c0740d4003848140c071482c0d03002c050f680341a00c400c0c0602a0150810030500c403002c0031405050a008519140440c078284c0304180451102d4100001d41c400961400401c2007882000c54051039a9800400e01052a050150340c2561883c512a504414800103427044820900180141d910064014005201318503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506406214 1250 506404964 506404973
    0x2030a0e01181d221403070606090e0c040203130f0c05090727030c030321060b07060e0c010f111614030129011d030703030f08070201050c0319021303 66
    0x2030300b00c14143c610550400200007440200c4100156503540c0c40b80310045081c2c1d182c03800c0701754050742c42c20381c50301c810001c4200291052041720014660401c0c001640f55a040100e41424011610607119500510600c41c0318540460034282050780032040e900c2d002d4079071810000414142d803140c0d5108951004000d9001d4000c2c0400300b03403c601e00d24004100018600e0351000719064000980480d40440040c00028060140c41064205000100003a215030140c40c4040e03071301c0fa0708102d490b001e0103d030110401c50b1601468502d2100c4030081c0c103200742c200d000200314901000c2e9030310030000c2d02e085814030407809002400d1845c440402e140820b070340303415101e06112001c2d0101c5029601e4140914038400c1007680340d03130304180300000a02a003a8403800440d036141000d01c200e044940c401000903011fa40c02c101c08001036103c0d803100d000141d0341c010302030000f4400805007019a41400c7c1004000e400f0303c404c41313601c010708110b01d003070400300288103600a0041000780104800c101c8400720500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506407464 1250 506406214 506406239
    0x5070302190504030506010b0c031b16060819240306050708060909100b060d02030109051e040b01051309120905130b03030d09050a020d0c030203060705090102030a0e0118 75
    0x38006406021000c444440488161040d48805841764108000500424007064010540d0031307181021a81003441c0c044000c09510800c034201500c551080c00c01c0660405070000030001040305040a81040c40c0100c4030100e0347c014108a4a00300e6547c180c400c0020f094a486203901d030800100003000141c80b440c04000821041d11440b02113072090300040d400d407500709072840c030a02c0b85002400c45078000c811090040c200f0401c00a07400503042c403c0d0401240144003031802858601c0010030b650500084145600041c0080c07284000340004c1000b021a044403611411180155194100d140d4180a02002000304240040403d20b0071840f0500d92035101d422030b0309a401c100e4100705000c0079250070304101c0d04d00c1106d4941580080c00610078ad144180c0c4000c00c600e00072800e440c000c501550024059412a1400b15909a81140d06005508041185540c06070305428481d141411100010f5039900440041c0800c10005842070300e12a4812402059110f903000f00c600c6903c0d0b10380f03a13142c005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506408714 1250 506407464 506407477
    0x7031a060f2715040c210b060406080621011b021c11030c03040602030315060f0f03100b0a02102f0304110907031e0504033005070302 59
    0x562058440e40d41070310345403000301c010114240b48a25460000c0a42441030b07200100108410100e0030604582a10346000d280102074040d43c49461580703c2c42100070020b6104000d0742c0c4c81928194401c1c8098460408480603606981000301565492a000410344050911900c900b85451041c44003148015003004a003011f82003019031070800184022a90b4407103014131803902d011400d280100190090304214240c0701e0000c02c4d079180160400744985540d2040e401390340103910000800c5a9920003005120805d10103c81040c94a81c100415000074002c40310400c2c2c03180000000306040c2d11038441c690004100c18440301d40c0311a40c2c03100181d11015100000740c400c9061000c482a4400708211f1080314404a260307201190701d03008e18085450b00003c204689000798614a40603550750300012911a1000c1e80e40450501c61005009a0070b00000800c0c4442508000038400040c3e00101700c3ca0741c40110100320b58500000074441c840c0030205000801ca114581810304c0712165064004020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506409964 1250 506408714 506408719
    0x305030715050a052503021210080618070e0c0904060303050d1404020607081c05100306110306090c0901051201030f0c1203080a0b012006010e1b120907031a06 70
    0x841e610b00f1038482c15150100c5400084515509100141004040e80301010340b010b413130010b08000b4030122440c0500e0066443c2001d4258020003001608010081c0d00d0740b01c510450106c01c0c52410021007030f87e440c004e000e4115584856400108c07103144080c2602c00561000703109220f15652410068090761110f0606405c4900707103c0408032001c1c596041c140143c0d8060940c81ca401802c0d11010640d4009589401c0700100c030b101c01d03510380c0d221402254003d540410300380c40d1051452401108840140d031682d03910105c144200000c540d40c502403964003005c00c1203e16a24180340004071624030900050801216050002205024000d40302d5002103201d11b00300030301039444850090000c81040300c020001504600050b03066145500000820641030400d2460640d010041c500c2c181000b0300081c0c150761000700100030304d00c1c03c4105035410219a2910a01c1c18000c480e40c0311440c81450411100c1d030710590007080d5405010444040116080303c0e220250700d003510035618011000365003091 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506411214 1250 506409964 506409971
    0x100e090a0b04050a020901020c130204050d050106050f0904120c05070b04180c020a051e10020f090f0a0501090b07050c060a090e06100c02040c1101150509130218100305030715 77
    0x902c1801075201b02c9120400c1600208481c08103102003041c1715001079260301a1303075001e005c0061a912505102260b4902c00c5e070000c5035650a10b01804401c8811039419031040324010284004a282d5140304418040b440c0b81404a41e091401e0881c500b034804e40c00010b51420014000412840b40f183c2c0190651400030180701110b00d03a10101d03070340d404540014049803c4515115a106060744a0451b40c050010036a1800741c6003a012030200d03000640915080c1000064030701d12460207a05603080041c084880102150034480020508030b403501841000c1e031000030b4142c0600c00100801c480a420003041c0301d0307444a07141c4c4000c0a0600c03a1103410170141852000c1005841c00c60104465240140d03200b889840d1641c00300b0024124180145c405e1003110011514012002e014402e40503804400c2d00340d05510340024031003108001000c030303401c14a2515500380182d5508040004030100a031503141d0707030b40b0b4208400300600016440200300e4413000800750100070360000741801c5010218000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506412464 1250 506411214 506411221
    0x20c030f0d0206070c0c09090f02090a0905033405031b030c0a0327061d01090b120603070e0a0603060c111c090504140f091506100e090a0b0405 63
    0x165641c0560301021005600309200041240744220244504a80200501c0c09110b1f580d01e0f441080b2000c002087c1d5400c110031008900394184803c0e12a0440c422100822401500b0384031241c980c041c002155650605480310305a210380b030440035140c08500603410155404030340c03030031644d258800242e8040c200fa0016070746107a003a0220a9444580c80d81c1e01070002d04915a50480d10191703c4800c8810000c929203e07042d1041c00240345401030001c075101d003503068811800145000150202585c1000301c042010303c40c80c00100e06581d15030324001001c07026515810002402d2034101e8000e00128200c002c1085200c00301f580001c022280246001c106060249104503040071280200d1510b03940001a041355084401d000c01d100c0703407024540071801540300d40004058481d4004242c070604459011b2051078584440b042d5088040080100f11040c1681d500e1414800010300b42440f0f52038035500c024200d800751312081007075400100850101d180c00680d1310010f044801c04030b4011443c11002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506413714 1250 506412464 506412493
    0x20306060306040c060807111b0102070902040f1a0f071b0911030402010c03030e0d0c05120306150708090904050f0d020c0a0e06040b0a060c110415051c080a020c03 72
    0x42c0d004a400c681c1002816081c400e00303a0300c40034068511010050300881d1007075804414071542e20346003200740784008100c0c0744600082c81c8c07101a410000840b88100800c101d581c50b6902800c2c2102d000c0e00403d0fa651001841e15545401810240011b41030006125020040800d1442c00a901c42d8130310301f02e505440b50940e5085030101c254001d0706107400c0010801540c040d03103a00711203600c43d2070080761540000c54554102010b601da010089444001d043c010400140500a00307508080b944a0451030910009001c1c0001d00480502403c0c1c0002d07036006102e01982151420303100038003844858102454059980c4085d0305049000340201d1141ca404644040748142602c180285440f5000d0f08040c480f0062450282a040d406070780c07141c002400c1d4868880c0507008045c07684800c00c45556504203030520b2841584800d20071490124114100d60407480321006544c429030748048840c1e030340c0c00442c0950144e10380160100740081064418140d00007080740d880c420035401e1b9842007142040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506414964 1250 506413714 506413723
    0x16110c18180d080609063f030a050313030302190e040c020114070f09031403120a020c19060207060510050a21020d02010c06230114030c040c0c0b130203060603 70
    0x4400001c000d00c002c1400c1e1310b0640c48203500400001c00e805c9804481042d4280220301e0241e601440e40c07004088601540c1c03580010107180711040c0c001d10f00c0e11027080c41c004e0003840000e240a1181d04940c92170b00034544298160780c1000145404410720000e00d071009003a450b4841045442241402d8a80c40f1980c418002d658040f0b0340145a80041e445005e4142c0e1034000125030039080020001d000804103a8170490700c0001c4d4482c138059035035110702030440030018000802030081c0e64010003d0700a0750707000180c101d510048411300c40b440075006250250107449204806007070b450400c01486291000c1c04101402c990040752943c1c0900d541e450001c12803070f28820007404641c150540d503c05400d00074004029588145800c00040303070710343d5070718040303607961800d60507420300e1221400d50f51310480261901410002324580075907400c0e41e000035a5403100450141c01151500c1d21006140e010702a043c11440d40014445030a19050030103a000840320002070344240f1a6201040541c100442c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506416214 1250 506414964 506414983
    0x18062403031305041a030a08070c0503070b040b07300f02070b04051309080a05071b0b0315040f060b0304020a090509030304030c03050f0c2416110c1818 67
    0x2c1d06001601c0d12040100501c2e06241203580f54440c3c40c9000404d9600f4071001c0c5413984510b1085407210458100318080881c5600709078040c5d4071500f01804030003461000c2d0307000c90382200c29041d42d0386294600344c2c01520502c0389000c0501d06845801e18500780316030760410403043c6c5544d81c0c03418400c0031a0407070341c48405128038203a00c0780410007803004d4205100c2591059090070000b180160303155640d45070950001520100094000c42c1c0f81c0100400c690031308441c500c00c0c0d98800c030340c58181100f030320710746c40040c144005121369225801074940310b80e00002d00c0320144510070004590384210140c10b40d802201c0880c411802c0c4000461009580c1c800c05000d15600070040d0308581c1e55030b500303441e001c0d02d0f00d805406010050103d112000301103402440c00001305000350440224010030350005282049510440650040820039100301944134070b810031116160002401030001e540724100b0f06034030b050542210460041ca003100001621a50090140404c00392042280405040d00c0380400e8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506417464 1250 506416214 506416237
    0x1c0501051005100e0a1d09101112070918020417120f0711060d0603051b09060d08090a0324060b070303110d0e0105060f0102070f06081806240303 64
    0x16121251040d106000110484c04d002d0402d6010325103649612000c07020058001c04a10250b074100501524140040e114179580288244403600345041d50380070b680200c014004002c0d42810006900520500d00304006150525481006111800009019600c83d0040c0c100e030f00510308001c2c030185000242e40030b00c503c0c17903c100360610b6071000c040c20080e0300c0503005450112072550700d407180c0d40d5081e00a06440c1c0100c840040d5840c40c51800508200103024803141d440f580e154101075a884180001c0d50240044411030044411458282d146001f46a00c071034000e95402404401c00602c40c901846460b42d1000509800303c0009803001940c0c0b00b4002c160b40280b0501c08403001034041d420090214148060751402c20741500c0500c0d0841b0382c8440d480302d45a4580050060605000165408000b03082c805407007070904100c8804014501486640204845071000404140da4001c500c000544014143c5459060803e0b43c2002d10314206240f80c03109440050800d0341e0f1071700000b02c40d06079084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506418714 1250 506417464 506417479
    0x2d03030402040e0f0318011e0e1309050a0b06150304030203180a150c03031805070b0307020f0a03090e0606120601030e0f03040e1509040206190c021c0501051005 71
    0x1103900348000b81249a110700104c1c030800111080f540c500340050040305a10046444580d40880b00042106e0441c202d00e00160078903064450360f480e48001501c1f4489802d8420752109590040c0a00040000740307070151035030080132a003000300301100c00700320302070303242140c201c140803031664a402010304c41900e0082c00350740100303d05801d000741d21000e500d203140020074880c0b01d00c2d60740304228080c3c1c40f1040810300080312800100105500b5100c1d040214204521200c20f44070261b0f141035807003000c2e005105803040c02000041082d44200195240f07a58004140e800021b82c5180c05481105140204003140212500048243c1081c00503101d4081210350039100c540c4a13080150300522240b00030022a00404040910000702000184020201d404140d1030615200c65802074008290a855100300c02541c248400b41e0307502c9054a01c01d83c1c1c01d000003070404100c4682501d540420700c50094002840008003513402c0c03100c1608000c0140600024000c50340c84c07085a581c016124040c0540c407115 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506419964 1250 506418714 506418721
    0x40c0203120a0e0c09010924120206070c0b040b0c0c0418141c050a020616020a021c0f030309110d0c180f020408060117010501080c01050d02070b04052d0303 69
    0x255401031030300c075070040f4142c4510110403004642c84050036040f0b6568551180c124181c0c40c0b03159000100001d4680b00c0401c6c241c4d00300460000702c1000110040d108140c040785220612680851450081403043c40c03440c0e40751340e43d00000b0901c5d0848070080c1100d000c2c103981c800725418240103444183d18501a00300499100c1e40c0c441c04115090b4882807114403e400c4030b2941c02002d4540d04203860443d44a0644800f0000ca0080c60720300c4c01050f121038080c0c40e00058a6054000071004566941201e083c000c1c448a0714140d010304495090103807080034168518020302d90540e00204070a801034412680304c0c034ac0c050078888043c040748001010a801d0200801034003044281030a0448848000031840c03410b03100e0420260f802603045800d443d0884001003140c0700d200b451030000d6143c000003c0c0815071501040549560b8800c0751701e070601c80d0001c1d1005d1820105d07811070f111203078804400c0201e82040d0520b1555158003ea40800e0591510003060009056242d482900c001792001540385a6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506421214 1250 506419964 506419981
    0x403081b0a120b09011512050606250b0702030c01200a11030c100204090b040e070b03190e010b0a06140f03060109030206070c03030e1c02041802090c0c010621140f011109040c020312 80
    0x41104bc5100541d641e1444010005100c5007a2280551110f90046840f800112001402c4840a2001002012822075462480e481036001d0b14107082050034800d0256125501413411442081003030712450103060f40311254014298081c20549402d6641007040402c15000c0c0030071600c51003044805030340002001c102d540c20b0003009550000c003242d40c5c0c81d02e00550b4460321083e55038902803d1010b9460300102d00306c41c02c101c0700040052040c1d1504130b43e400416030000d1564850701c8680d0314910300c000005046a40903000704402164041e0985a88500905104852200b03070b0100301c0019401242001d0289400c0c1d980d0101501c1c04050603612100503400c12005101c10151041415044089040541c0d035408080f8855040038526541d50314044200e9400c55281303401450358180742140d84643d140045050858159000200641820083c0c810a02c0c0a0181c82c20361229800c2501480c8031180c400701400605405903818040c00d0042030781a41c407409200b0840d0b004030f02250000e40d044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506422464 1250 506421214 506421247
    0xe070c020d030306091508010c17070e0a1a0d050a1a1306030203010e0d08130b0c0702010c0804151e05031b04030b0c030403081b0a120b09011512050606 67
    0x4502ca42070000e142a501c0d5104003c1d02c1940090b4824403100c418100403041d0280201c854082d4985402108440c030071245800025006d80001c0030004030b80e50103c0c00b9160b031116840580b40c0d50920640381b0104501640082d4046902c241005003005c0c00f203004a45103008405000d1125003544260002c46400d0041c400098151403e00c40d071500400000340c0c50a04c55003030064100d00142561447d169006440c1e04801740c4250315003c215040702000c075100020040d040100181e24a595a03220b00040361414440400940fa45100090000719441c1080341e1050f00e03103d41c1c40305100e030300210880d22004c140d1100c480020400810020380300d018030010580d0f00c0222514220b09194480d20b901c280a0000c40749180110800003d20050503044503400c0d900581d4a241030306051080701c861010f6000c0c2d010b0440900c0200f001805080049070845884450042c144032942e41e9113040203054007804203a6074012403100451007079070800a005061240002802c003501e05100c03011a00d0342c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506423714 1250 506422464 506422489
    0x80a2001090b2b060e0601080708011503020c0115060246030912030309151b1b050f1c0206010f050f0a0e070921050604080901030e10150e070c02 64
    0x80010b4402d10f20240e01003441032001a044440d48060246801d20000d09941e50140c40076050200240040000e20782d0340c0301c1d0951a5006140c05602d034440f1895803400740080800da5a56880710304804034a5941c0081d03050b048003003200d241d42c2404022600388103144440d80c2001e6020349048044480000d0300d95000309014860b1a000c2400740e0b0320b1912403001c0341081c03000c800003503d80d4200c0c010301281aa04900c080b000076410010a048110000c81148907000043d042c008501180b40244c504420354051081e0040280d95050032100b40d000d40b56442440c0750050328540000b8142c0052000500c5030581e4641c4550401d00790804040100c540001d03026294401001440410131000c00750525004080c142c450440b0282042d080c4c83d890310040508400d03444030600c0c1100400d400040c01c84d041a00281025940d404820049010b040300c107010100e01c1c401d10072a1540034100e6800a13891480041c102c400c010345031080301600e50310175210310300080d03c01402c050141c5000c02c2c1411a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506424964 1250 506423714 506423767
    0x902010e09010f06030f0209060306150c010609021b030405010914060706020c01150e06060d0218121501050102011b110c1c11060a05030f0709080a2001090b 69
    0x88440c04001465091003604070080d400c4400c0e07001c0142682601807500800c034000425801c150403140410110301000706041c0c400e002081e0090200341d0300c2c80407201740c421807000900809403101c0c2918080c3d40849810728080c1204206503440820102c255810b4410581d1043c3c3d540f841e03c4059068002907015196001504000d40c2c1d0000d407a620060102107060400031030b03081d0701241c2e01e403120845640202d0b0140c060310704104440d1381d502d0880d9160b0502180061310b480001c0081c080c1c44d1210030806420030b0710807a1440036040c0004030160603d02c2c00d103188043e82e17203900049003031b90404244042c00500c00600c6c0344100307014043c0140a0800d42d4103c0707102d220860005120358084510135900580c51030322075400d10001d1411140301c98006e9544a02d00001d040c0c005280d031100600324150801e80c0b60200d00003510942c070311401401150110340120545040c001007a05031b0a2a242d444180c140d40c1c0c984550013100c641d8125000c810305541001c0b4070130071a6880b403520030005103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506426214 1250 506424964 506424977
    0x30c1b170307050f120601020c03161e0315061802090a03020105070f0501061403070803090a0b0903070e040809090105030c0f04020d110316030e120a0c03050421020307120510090201 80
    0x10700c584d41d102500840e141800341e15040d080c10340c006400e1626403803144d8040c0d0005c01c52000c1c2841130803403140031030b0b0318000440340b0245044c0341c0200d0718003103030001010119400c4095160082c260410000c1d28030b00f264890407508000010012403246821182d0408800101000958007420203880c44900444c81c690040d1440e0751040d003150b16940107139002e210a07000b0b4036400c0c141001400301510411000710f07d0040b0400c0002d4002c4a40c0c8070300c0c0316800000070003000c0c649081c000c50303009158241c02d0954a003003e2401c0400c5405c0314001900a14000740001001e10300020942d10401d40030b04502e45e0740e1501018040070354040762180028a4450b454a4820503540004510a00101a00400060103900000c045d18181104584180d022060007032082100390220f5007c40c172241081841d8200e2480e042e501401181d00480e00c48500a02d03403c00c10b03090424160810b40300700c0540d00c0b2207440f01c1c1d8400f04004c1e8064007400c1980003002c000240c64240e4441d0303401500504148 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506427464 1250 506426214 506426227
    0x60c030709090f05010e0603010c02070e040320011a06030402130b2d0319020a090e0705041d01110a050909100e09030703030b060f0d1e0c030c1b17030705 68
    0x44058400303500c1c3c035410181e5100c004015000007110381e1038210308120028440c01c141e01000a5541d000c50003140c00740080440441c04040c000e5280010100540c0505140120303490401c50091501c00703840c10202400d400605541d140083c103c900c035a9004000c032500c100304203c524003c2280a441c0754000050b10740c4071182ca4540c026194416030300031506d002c041d001c201071609140621421200003500540b1a07401643c0741c007050801e41d00c01a00010300259030716511440d00b4030079444550085e1901c0045110b0a00b018408440c2c00d90000003440419101c100b03080052040152241c00034100307028200c581c1c42c10380303c0142c1051700008444100340c1c881400f51124141030707950300b455501c0090325608041e0113001b418016941140c10900b88020310f5290185071142846185506640340b081c0c80b0180e6003043c0c41401641c819008224806500c040a40284402e0b8040c101041843c125602d00800c620803107002e15a12500b002000300707411100b4101c03a000601f140c400d0002c01d1151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506428714 1250 506427464 506427479
    0x30c030e01110d290d0302010b0a14100e0603011406070c0f1d0f040209060126010618080c090919050102040303030b0909060f0606040f080601090605030d02060c030709 74
    0x11520a1040c0d803440c10743d01c1d501000074108490490484000f074004050095150006403507005184500075101c0800386503c600d0f00b01d00401c669440035500036201030020661259080e94081725000640300080d103401d9140c0240d411491061080c1e5000f80e0030030040c08850840700c1682101e03c000f900242c1010703450390b0b074401700c03144940280710410740712542008110303511080e43c00b01402c0390601e0005400c0810007100520700042000c1d01544561000c0350040e441481e0f00c80d044500028515111100424896030ec03520078403c032000607411040c440401c00451143c8401c9440080041001079200c00500054000007051055140180c1e41481b99105032080341010b018814000107a44034214078000d411200ca08005070700a8000c3d100300850031000250054100074600d244074007035030b1004009101807107260480e43c2041d0132144002100d120005015051b10040401803092644075000e0590703643c06049154010b9004801180002c50b081d0011034025150346080c0d07201c0b5449182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506429964 1250 506428714 506428721
    0xc2301110409020c0d09060f0305061201140906150d0f03181e0f0b09040b030309060a03020301082506081317120106050408071404180b0907091b030c030e01 69
    0x410b90006030009444116810148041c031355a01c03180c00c00d9400d031820543d00601c442680300d030301c105043d6100c0129809a580484e4490b1040603500248200d0070004940d42505006840d03454092003410b0202d505241d81d00121805204051f200491580040c4c6509000030a504015424412108009030342d80720201826800350400141c149000070301d0414442d80c0c50440e600c201c1706081000424844a4034420403a202c501040310081665100035000a0070b40c41004078bc81c0d444a4005520000c0035019005507048850720003d9a0040d5800c01a40c01400324451030100040b040e00020300c00c0500505603640c01020b0300140403280340445e5140010300143d10300348080500c0104001031003285488440c0e0160080e40313405401e0900c0e02505039034912983c00355013a20005422621000e80780c940c42192048210005211030503080c1c1885507884406407403461070780c015031001013210760750fa0144c40040851110358507200c0320400c00441c003c1c00780c0081c0c0010983c0b1640c068442610900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506431214 1250 506429964 506429969
    0x180601060c150b0105040308180306010f090e070503030a0c05010b0a0f0905090a05100e0307060204270c050702010c0f140102030604151406070c0806090a020405070c23011104 77
    0xc951070407400003401e00042415600c0348642e600d5040200204042e40d010003940d04580d889501d4070f89400c81d2520502d03400c19100d450301e826105030400080e444030002c2d180c034222841980304203c0e60900c682441d845524034087c49800da48100000c00320350380b2a045281e0403a000b1000000c0c60840f600000f824034000707621881d04100c81000500607407c05106075900120000700a003298400ea50b11940ca401030812140890342d520103200984c00c0c0144102c0f64060ba0045003103540d991500c030440c4001c43ca24850244801003c1d40c5401d0030700440c0b00b10010781905460329420204581d004441060b83c400084810f003100f00c0d6010000b980e6620340c07000c1404c40030005070716864520280022160f6001840360b01440b80b2500304010782c0743c0d160100150ba4240c80c1156103122505125400c2402503001e640d251252000304903070702ca008150003100314400c0b2003c3c003058172000011540c02007140d001070080300983c4103821104065403042c0c6070b0744103860004030310010b02044408a0381c100d913 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506432464 1250 506431214 506431217
    0x21504080105070e01090806070e040f0e011b0f14071509051f0b0a0303080c1308030f03040302070905150d03020f010213290a050901050f0708070605090105130b18060106 75
    0x84c644071400307680200e80280070b800c214000b4030032894548001041c3c0420311621034043d603a0fa08683e9150030107034001c00b9110311140c00a101065414504004000310a120500001c60410340440c0e51803180e0340b50400068609000c2d824140182c07100300c0c04290001c3c0600782682e0725600000044c105001c004003104155040c0e0702c10312400038400050320480c0c5000d510038100b4a005000003034214500e203810141c1c0342c0d040c44d212510b00034840c0c80031045030095042032101207810305541c00c42c200118410b0344079500366504984c0c1c078120542610800c0d06c1c06007149480136100360841c1410008064054001c2c8100c074286070806000b5800ca90000e00780c0c20410080c50414051001e06a40110350070114100c0554201400011060a806803030410401c01c0000200c95815030721440070b490b000141034640303a60701c2c01549404000d6a11a04044034144e040c900011040c0c10180b00e00b6128980805500111000715a5491140f42001f8215100b00035184d102c03103480401002054003800c01c0703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506433714 1250 506432464 506432477
    0x2031201090516020309101d0d150605030703020a140102070e0c04060e100c02011d031b240307030207020a08011505010210020a02120903011e1d030304020d02150408010507 76
    0xb1045005a10b220030f00c20740540d441000840365030f40300e406400301d00010360f20b4240e10481c1403080800f011588217121942c4102d003064410300b4441c104010032030400b2401340410030107560703401303040d250b074443d00c0040d43c0104012001c1200041480090108580510503980c1701d684030162240c0e400e4007610110100312000c64184103007034219814505c1c055084962a4088040a900811240d00d14000a040140c0715000780b48c2000c00b0f102250006a000341605c2c1c03107401003040c0c0d5036691240300c1075512410103414403100520341c01c01d8410180c0703008001c09143d0b503140c0500750042e501410040380c1010361040c0008401c0020302c01c1c070721038010b5012a101007501c0c20300024039200c40030901c611203510410064074042e4002034044035841c400e949040e1034003518000280146010202d2404034074090b143c6daa010502540010018171140800d560700552248540e60380780003c9070700942148244400707201500d8081283e0300b0501d00c3e0700c08a850991240020340c2502c07001c1d1381e1000803910 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506434964 1250 506433714 506433721
    0x206030c09220f02090901031112030c0d1403040c03030509030703150b28060c03031b1116031e140708060714030723090307031a0f10090c020312010905 67
    0x1075034003540c1c0a07200f2444055060200e5400014000c0c2d00621008210041041c2c007215191500941c5c43d903480c0028041e65181c03010145016150101110b0417070014041920300c1c1e80100441c0c00741ca00454002406114450440c0da003aa05c0b640300d2043d0300e82c18420400000000f94402541810845c054280410031034131403800d22143c0c4c040058015016029600c000c084151250400c104030380e000d06d0018403101a900302074000745001010800da4900207100241416004201c0c200d2a4407600101e0f40c0640c0d0308201808401c50901000341080d281098103002c0d165800400c26901e03004400701c1c58036000c0c0d90030f2140740c003440b0b41c481c280907001141041400340c0c101c90312009840c140f00410b442c4d0b00d001d820040400080c80e800c1c4214010302d20b903030002c91200780160340040b84040c00719003016460b41440810302403240441050040ca1100140203421000e03500c5028511a00c10040441d00302031901313010f0500d0038040d01c118402400b80d4100b0901600c0060b0007060f010390700248908 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506436214 1250 506434964 506435029
    0x6080307030512010b0f1c0f0e1c0e0120031603090602010f02040302060a03050a14100905090d0206070f120501061e020d09060c05120309010506100201050903070206030c09 76
    0x182c140d112000740306050007000d0450306c02c0ca0494900c40d01d0101e0f80b6000031740c01c000480c020504900900702c001c0c50298502c00c0e1017000998410700c842c554000c1c09000c850000c0803036001c21041240c42c00981042c00d00064050000000080303007180105880c10000c00c03000c81031002c45080800d4001804500c07080000d41c1e0207204d0b190203143c40f04400e40c582400c5401041c2d083c0700e414038071410036540d1400105014000d41c801e0380420400c0141c01103e0800c02c8144103401c520740516080c0ca0f01d0000410b007280c1002510810700040c5401600c51581c0d0303c5800d171800300c1121200e0741802003400100c00704503010b01c00ea5001c1c08903031322401c890003503880c2c0b0010b00c116615101c900f5548054000550203401500020403110341e46000c040350203003403824904201c58440c0ba014819004000d0240400f010b400c01c03803080009484290050f28449801c03403d0b1a0203a403000b00c141c008002c800e025085c60001964802d0030140800c1c5003004500c00318001035a11102d0300080300343c3d020b2594288 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506437464 1250 506436214 506436247
    0x10b01080c130308090102030c0f0c011709060406020f130306050f070c0308060418060203040602090906190501080a0207140610061404050d06060e100f090515090a060803070305 78
    0x100c9a50036240c141214800c244403035005070f01010340442404942d10003142c2c03007041100d5185094100781c400700c0c06001c050030758071041c0006140c081100b030340740e84181d2007400e030940344108010401040a0380700d944581c1c001f54050100c00040c54010403401952824218880002303601c10980007075035140c440620fa40300100074003c113080041540c4440082984866015040142190005172111140c207011000b42c0701000300070192400401008244107030303035010b8010740c507040c0c410900698941040002e14245c00b107010140308100749d014002035228003102c5030f0101400100502e0011581c841e40c060004905002190f58400b10030011080c1d800e2400300c00030f0095040214004110b84c40710032a41c0602d0041e2402000070301090018402d03a900b19200400141c0204031a5080c110800846006c3c00c1c0240b00411301400d00000d05181c641c4281482080c5c0a140d41c0c3e003512020080020b1040090301040d1141e49403100170902c10340920080c03003050310075103400d0f640340001c4042200d003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506438714 1250 506437464 506437471
    0x5060114090f04020108070210060f1404020c0307060513080711131a01180306020a0f0f0804030903080705211201050901030c0b0f0d0f0e010e0c0a140a1502010b0108 73
    0x1c0c000315802e000310107070702d458100d80044d070900b01401140c0e6500300c00c03880c00302021003a0b5250b03801c0480004440c5038040000e01070300e18000444a007180020144000c0c1d20909010541030746c4104003250200301c135644060f400c0318540c04050b079010b06c140c0b540801c58114940517147c0484480e0703400c0c0c1901d4408000308060068010912910102c959400280b034081c90302c0364180281c0c2c00001346001c0703182c01d52a000d968004c00c215265180b121008150402e42c0302440c010600c8806412245802048a903124940c19a030f101d80090460b51095240d030030104040700c45100b1480407401420718403401e240c3d550304005500351034a0580440389003080069000600230f6810b600103201099458040300b00340e41d88030300e4040e40e0307840f01445692988102c06410913a9441c040c418403800c03007150407000d41d00c02e0303190003407041c106188580d545843c120000070350b0180340d00c02c00700041c402c0a4480d80c120b0380d000703101b03000700b0740d8520561940040c1c160246005035900c081d00c603030f41e45e0030200c030641 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506439964 1250 506438714 506438719
    0x90c030501050604051215090109030801090908030a0b220c170f0a020309070906030308161b02010e030a0b040803160c03050d0b040e030a030903120b03070e06030304050d05060114 79
    0x80e0351505001c140c03644124003501d4007804403608600540441040490341c0744803a041150340c586001d00045008200401042300000d10000000616004d10b00828800030b0300640c2c610319545a0340e041200074004d4101e1603401001507582c1d1000ca12180342682243e0f00c0d0011b0204040c900124000e00404608035640d480708141c2040c04410b400742007070705138032000070000180da9446060f80d452510069900c5074074581e080507404405c040d0321540c0c0781c2c0601d907201c1425400c0303e1624425151030744944005a86210140d0b00c1a005d13600c200b9442240c52400780541e1020303c20f5840d0103110007412034044c0d42460000003440306c24810003101e0341c890304042c03400451038a070340da030000d00c0c52090208000c0b07803640791040342c0f0b07480d0780303d40c0184500c4215038112540ca40c001c1c18060003900c10200c0580100b40e0340807080441000c5401b580740c080c2c1000f0080e200e170a04000c00300e100000040c00c400e4151100784404140e0b601e98500b8601454081c1c1c000b0412589001d003851801d41d0210321860 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506441214 1250 506439964 506439971
    0x14010905010c1e1e0509060a09030b0f041110050d1415060a0503070e041b020a030905010f0f1103041703040e09150402091504150503190507151407030306090c03 71
    0xd898079400090410142000e09000d25a200030050864179805000f4035107030300c00e00020b0420300841e0000d45070000c8a10440306800c10b591082002080c8007070442d00513001c42c0003041c03803201d81c2c5461306180806001c0746c2456400c110386e00c141d4004983c072000f178890140c4091000c0c00601200c144c050001880704840c41860a00c0717104000340709000180c40f03181442842d403140001584c0d00e80241042407005900f88198810f6014029500c0300703504019000308131921000700316544528041c05019a031a01e0340c05055020303403000c0301c1110000c3c000e0801400180710101e0046c45900f5044000c000080045888908210f00303100c9900f006807200c0025405031181c60b20440600341c9055110790119641061503541c03107003501c02c03da4402c452541c00303840d01880001d038034a190b40000903108240d04568400499030050100d030501018064110703402035101704504e0201603811103c0c184a880c10b00b1523015070442120b1641c01c00c1000b200441e465072024400f01d01c00e07128121003100700303240a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506442464 1250 506441214 506441267
    0x603031425052103010303080609010e01060c05031201060903140d080c0a0e0d140d02010209090f071106010306090b0906040c2c0f04050c03161214010905010c 70
    0x50703030304001d0414600c950402601c400c06101c0188050b100100314406609440b020401000f0a2a8424002140407442c500302007031041c10f0803006141618a145a40301c0580d08104040d10500310200e41200c182c40100281400c000c0b1050115000b00b480d9102c05991500754500300c45c0f000c014440c580c3d03243d4800c419113401c140e4082c264a07004000a4100d550f80d1744810808c59101d2142c1085c140c0013052a051402000740ca4018165105811070983e85640d2105408034240d1040008690b8414400c40105070b1403130380c42c016180c00080d0350034070021714444c4204240c107199090f441591526500d5400340f06006100400e5a80561200054005032030540d83e860300e101c52501610340201c1403901c0402e10501c20112048540803502c443c503205180c10310361080301400489088401e0b000b0340000e1100da0800040c052000050000c001e9001420f180c58400c0704800e812080d500a5400c0c490050400d00c00c1c03141c02602c900070701c0080384809201801a107100e540d0700b80310710403200c4900780 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506443714 1250 506442464 506442487
    0x15090515062e0813050d080610020712020f1903030e01020706030603081c0b0a08010204050a0602030426031213060e0628020417030712170402040c0311030a06030314 73
    0x3811400c0350302d8141203000d40c440303030b66004440602200081c01480f4204802100e1500114894855001104c00394001000c0b02e0f0300300d858151034851008228401c104403070051600758203940c1c00d400054484140030030a01150200700000707a0003500424904c0c5200002540c0c10f002410160045003002d1003c5455a0798141d8544202210000c2c001849205148441101e400140d901c6200034030080040e078031509024000e5000c4c2c07107000d01c034500900300000c0d11800071081d80c0172074046101d101417081c0c0184418000b00700400600400740800c0001c0f8070b01c1024100424010080766504840d01c10300c0707107404011594580c45488541d03219408000722140841004001c070000b01503648005501c186c01c00000c1c3c06144c10200e09194a42c900c46681013001010300110342c01820380343c0101c03410324016151200d03090542452650002c00140160405402101101c6814030300015081e100c9070701c20300c0640064807c41003d64446100b00b007490f60040c49114a403c10b18410b52611000303041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506444964 1250 506443714 506443789
    0x60c0606120210050313021f120b0913060b030d050c0d03060b0906071a0106050c100e0d030e1006030602090a1d06090c070602040b03060a08010b030601031509051506 73
    0x882070304100f00000064000008900f4030314100d5805428050001c0d99054200003440c0c0d23058018000038842036081000071001d0040b50802e68014048480d2a00c45022801e20f01c1a80740b400e49074a41c0342d404417143c6480421001d0071a08895507110380b00d04d4100c2403d4102031070f401440d03041600b800c40030300484416100300c41c0c8200c012a0500da803200b0724a000c800749805000951810896880006211508000104900c8a500041e1110b01d0540b8007030500b110358800d0b00c1e00f041e034016051044c8841c040c1d4080861800d03030744c0803505030021006a400c1a074200c0c0e08100c0d0402c1d008130344038a550402203040300150101c842030380510001842050038050009280603c10351020002c542c00040030000c440c00c0c0c540048003956200d413582c0b50328109a0080d140c0074001d1785134400010b038111061081c1440600b0040c050030355a481c41c0c580d40310f44226181d14046a654604000c4d0020b0300c10420300041100c10080b00c1c07418036006041010404215072180c0b00c0502403409198507100117003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506446214 1250 506444964 506444989
    0x25030209090117210a020105070903050a06050a0b10020d02010513020d02090a091e02030c09060108070e1c03030608060c0702060a0311090d060e0c0114090d1704060c06061202 77
    0x2c03030007446183c403120789401c460b104030f210050301c000c4081e86041e0001d001410900340302e40007481251201e540c101c030b090a403440068a1604880c4221002400301e801554000038140380c04500a582c21001501c800322200105016078003200003001c4160b028060b19601c030035120040f803401c5000d0340200794100b0641da4024030990b07080740083d01c080380380d0340a0500c09400c850560b0660b00e098800800001c10b048060780700388160100350641e85030509460784102c0b0103a6440000b41c0f21024181e400d2100a200198010090203111000e04200242103c5843c007d690104a25180828103401c000c006811510305440c00c11200002d45c40350700844005013003515000070f6a80800405a006025080c100c40d07006001c40c0b00d01051204541050151100050a950003021044019504d1070040000c00700c20560502c52401e481c640760781308c1c00150303009810418850341d503038102082c20b50081c0c220001165100910b030090201c944540301c090045514580c0f01c08a00382c00140340000b010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506447464 1250 506446214 506446229
    0x605190912060b031501030c08070902040b0703050c07171f150623040e060102010f0506030712030c141e150c2a0304090b030114070e120303250302090901 68
    0x21508501144c80400200105002d42c580d9403080d96101e1916804a02ea1131040c3c400902c2008404502c00c11144200e408072180444624507107e0b2641d02510141c21044403013100d40038030303030b00000c104031820b40000d008001c10015014048140e248451030701e510000e000d1107680f4003403414078001d8818489105070f0b611810b040e50117034100c1501301d580f00c4c203005020034a140d000c41d002500040701c1c0015400f41c8805d130020301801780c4501e80c61041314130445074240c3c1580401003c01a8490250f500c42c00b15000b450aa29840c07482c0d00d50301e0105410313401c000d40c2584041034070402c401d0910b40d43d880f0700320000007503c0d041a078101e0303125240d0001750100c6e400c4c040000da4608800030503420700907040b040c25100035a20185010140d107d4210b40301e014030042c201103100205260612880304500c142c8110583e440d03c444c941150303001c001020385a040201c0f07041c2d002c40340c5420005144205c2115081c032410103a61529015001200000e001c14140140703c2c03560a50398080280c6e0640d03812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506448714 1250 506447464 506447471
    0x30912070807061706100e040b030c1503010602190c1e08100c0906030221060303070510060303120e1504060b0a03060b040513020d111801060519091206 67
    0x6800508000895000044a218000d400902603801040d5204001c040d40c2d511003042c1e60700c00900400048440d0251b0000303041c0010407407245801d0740701d0400b40304050704685580e08071102050b04400c40c0b2200034944034010004000069040054017408802010102100141a0350700144a58140500f0744211840807540081001c01825400200000c80c11611142a42310400d00100451a010000200d111201084980c001e000f1102035a01a840c6805010260b17200c0f103c4408001c0c01103a45030108000120215004216240841c82000c2c4005665451480c0140102d003000c080b44004078201070840d60b800d240410f1140d070906c1d41000c103c0c21581c5501c1c06c040100070340401c542e80308125940100600a590b40140ca100310203030f908001988421400303034400300345180c00940c411007441c01c4000040310f28003010031006010301042985a42c4258602c40c12400f43c11510015502003a485401c52120711f0041140d940c07414000c00c800d0a16024802e40b40040314094a8a0389 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506449964 1250 506448714 506448739
    0x120a0203030a24031b05010e10030207060603021f02101b0e01020a0213060509010503011401183c0b030d05091f030c11010c0f030b040b04050c0307020106080a050309 73
    0x4861000034403400007440b0384000c00c0d450f450b005c12281c0310000b22420720740321a100841c0d95406011000241c003c001d040310820f051740c40040b406984a01d50803942c240c1c0300d080020043c0c45407002c2c50010f40c4502d000c8551900c8101c030007031900c021440c1360450541001461003641d03106c4051607440780344c6d03072501003401448000142d280c503140c60b9009400c4110f414040841d422140d2100081d514116520761070b907640d030f004241c00c0c1c8580002c65890310700700e0001041000613580e40fa04c1a5641080007040184130798050380e0044018078104501c1d88090782c8604d4800c01412800c00840c043c04600700b10049035000405e54648942d80035006102c00041c106881d07a844603080c0440c034110800c0c80280d106403690040c0640203030304165002c0750100310088a090341c180969203140c50580d5070b191316030b190320000b10080c02401b48000d8016555800480c20350302c035402550300c201072081200c2c0e0f0321304003180d0003804c50f842e540c021900364110b00e6404001913004004c89440800c01c540c3c140301142d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506451214 1250 506449964 506449991
    0x15010f020703032f3c070b0307180305060a050c16121202130e01080d0e092212121112060a08060f061005030702030d09080c010908030405120a0203030a 67
    0x1210040410040c42500349010380100b860480310301180f6000d00414003615045405041100017458815880d0045202400040203080c051030b4000362610340a0501a821141310062555503007040c3d9081d0084820400c61420a019540e005160b01160b0b61400c8011201c9075852441a40010b08980b1383c100c000c4445c2c1d11560020540c2c000c1c88000315070314016445400100c1101d80f044419035400d0400001e500d03080440c0790310f29000c864a078881c00348d5a1100f0041d0401c0010215851600880c0a4900c6114280315207001d00e445203d2462103604101c4001d08002c184060241109007031071641d42020001e1400c3d204e0308100d1180c40e2955448190014a1018040e00108080e114078010010b000c00308400032802120241c8106a214640d182d048466210480f40900940d00804c0301007183c0c20720364040305e011800b415069080685120fa000d00b510001d6106850000c0c2c00310501c02880020311601440c1601d051955141c0300b0303420406500d900008145a00c3c65030380704903454000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506452464 1250 506451214 506451287
    0x11062104151107050601060302030915090319030c030617070302041125031b030f08100b04080309030c0d0512030c0408060c0c0c01030507050306150d0515010f02070303 74
    0x1c451a100c184400d0800c0a8010015004a9002c0c1c0b400d103c2c0400000f0018000d200b101c0c0510700c5a07001d4084282003152181d040100a0603615441c4010000e102d207142c42500c0310a034060480e074021451040c620300003030940b402500042c90007902c1c7e110000461800180080071a030381510f0201d049003c41c01042400e01481101400c90b081c00c40c05801841224020b2880c1d02c0d03c2501c40720703042c40c040c5240c40031010301600014081002940c6a0201c0b0b8000d4103416440119500480d0341e40e6291300586506412070f52080040346d0020840c000d4525043c0141580d0200549016071000810b8440365566809500101c12030200080405d150380303034030401c860190030b00304112500d905150726080520707400b071900820785001c1c02c2c15640666100c0d0261078040c80b007a0303403544d0071074940c04100140c88015528900700c5030002c105051a09000380a168403c01101c2094ac1c1809503410014042c031014868900c110b42140d5014400a5000b0030b921002406408000512044008050120 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506453714 1250 506452464 506452493
    0xe07081f0e1203040b0723070f1a061201050f07050a12050c030f01080607020615040f0905060a0c0206100918021e030f12031906050a1211062104 64
    0x1c80c0903054042e8079032440c80c00150f009a204400110259607250001c590154000e86040301c2e481c0207595010300c0302030307940c054907045010720155440d180e01c82d41c5d85074440316407008a1044d141000204001440c0c050100c00240c0100d50080c0028030b49004411546240240507805200b404160300d441c50340716101d44000030805c03d004108504200c00c0310b40c83d9800c00c035004070700004080c0c0089400000402c016001d4022a00280034a442703014207094020783c4000c1c0300e50420b50300d00c68040c90403032600a00b04828040d1001d400c4500380300c80030105980343c0c1d81004c01558031880c144881c05074450f14010403200d040f04001184c0301020408403140c442c4500c081d50210801d280351702c03821011100820000421021500002c003c8460b41c0c2d100d04c8204100460750009200080d084581c0c00d6031051010324010300080e20a881b003001400500c0c20703030002c0f2074840310811100200100410f030a5501c0b08116079040c00c240345100541480700d820042a00c501002e2004601001031102c0004503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506454964 1250 506453714 506453741
    0x6091815100c02182e09051e1b13030f0b060108160507080f0a0e03100507090b0c0703020303030403020d120b0f190807060e0307050906090606070807020618040e07081f 74
    0x11045d18004000e0201c01180a195940340c41d11012030b44604482403040800c0d41c2000102d03505039a15000c551240c0709204c1d1403100103604000412440140f44011006948a80a1038400241a044c4400e040f0001481b0070706100505040c02990750480c102110a030741c4074605250b07a003020345420100c42c01149568015800085091011550404a00c1ea401d038410b9084031190f141e545010030075a402540c0d07050116846540070301681801c07400402c01c0300540002c4031300c01c903a40d501103482e55004440580c01600600312201980d42d02072b9071501904040034043c030100e408080001d580000e0360402500c50503984001d0301c80c410780300841400401d56882035038100799403202c3c047e0103d003082110a00c41d014000c80070505103490710513a4007030180a44480b040e40e0f00c070300502c04103a0043c0790a881c0ca0505210600040e030721500180315010301c01c0280048442c0440a00003a28400050507880340c100b40341c148041040000c2140500d142c075188212105040008c100003005040860207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506456214 1250 506454964 506455021
    0x10260a050a111002060f19090b010902130803030610080403180303020303091e190201020f0d031d1f050a15030804030c1a040506091815100c0218 64
    0x400c0c0010038a0b42c0e80000700c2a10b002900744003094003240c6801c0304580034120100c0c1c030000b04029110280d030582c601c54046d5800210719000c1d03150300400541c00d900590407603400240440b00382003d008001d004001c010011819070406400080005041d07090b00c6040082c4140000c00703052156041d5044c030140e0142401c012500c07401d00a440341d00c03c0301e8840061081d5010402202d041c1015480f060784288040c114030400725082d12900e0080d08016411846803100d05080c201052222213090b0155403000a0543d001300c0c4140b01501c541504011150040c2c2481c40700425079504020101c448a4000a1603a407010072001c0200a6040451509140448088100440c04c0000d0040d80e00690b45241855030380c110411204988188501040c030007131108210900707104002c0c0c2500b0303600529202421078041c2c0c509040a00450f45901c180031050f0852005013043c0c0410289043c0e00d02d0954151607181d00800d4840b80706281d40c3e00840203100001d40c1d04003c6540d4401c0120f2034200d00c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506457464 1250 506456214 506456233
    0xf0312060f191e08060105060a022805120a0203160c0b12061c02060a1101060b0c0a03030e0d09140604030204110c01150302100815131410260a05 64
    0x40d8840018082c40f0070300c08a0103041c4100e00d85001444040303038424402000143c3c01e04050081c6500806069000d611504035042d507a2169611490001992000c1c003804011550408038600000f404000302160401c04c4901403807980401200da2400420001d8101049280782c0b28a0b150401c0d40001d0316102d010500600040f02d06103602e02132041110806804048a51081c201641418000358045402c010200d0904e020315030700702c50742d20002c0000541c285e964003862209d600009603a00950480d100400c20150507110728034400014200400c050250f902001c1c01c625218001e090540c0f0400450301a29941c110464003c0d60380900103000a1200c1c101807400c0c2d03045010020003a500300340c101001d1080305852031044031b4006004c21886142040103864030364024180003140c0c200801c40580b02c1d284c03640002c403150880b90000500b0725503041c0300c228411001c1d105401880428204001511500c0500301c2c280020341a810121110326441520300f10312090010035034056140c54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506458714 1250 506457464 506457499
    0x507200a030203011814030406021509070e01060e01030c110d03021b191509020d02040f090f0818062d130f0504050903030402010816090f09021305030f0312060f 71
    0x1110f4018030406c0340c07242d0326803404100c94a0340101d00444005134800807841a0040c03115100d00d40002081003038507505502e411403003007401c90903040309022031242e09a444155906119500d030803101c1c0c0c600030311501c1e61340808a440b042c1040f0b140c2c080540105012944c0d44040d0440e5050382c0d0400120b0f00c0d03001c0c03207003c003a03064a005241668401c2d1001c000421985413402807240155000b840c104441c24241d080000901100c1072242d0141c0e5900400c8001596052001e01524000c3c0042511122007994400743ca100107aa550700071070040c007000b89900b0101c20301c0b1156100d12001803120b104107013008213840c05103009580c1c2c44808050300103204604982030105544007035800740225518a0400746d500d100c15507009000842040000e00e0b54000b100321003c0c1c0c56050310313280d00481c1c0d4640c4989a0755075a030b040601030540c0001ca14038110500c030224001801c054000c4c02542490049654980c0110700c2c41040a4802c1c0b000034259690718443e066040070010104400d001c4400c49 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506459964 1250 506458714 506458751
    0xb091903140c06190e03040602070303030f1e051014060f030901151719020f10020705040f0b09010608010312080c13080a0507050402040b090f0d140a03020c010507200a03020301 78
    0x203113050414030b4810764424203540442210b0075101d041d0000d0008600c0c0da501203008000307402440080590b80e1b080015510341c0b014042912103103a250210351030401010b02440702010358071404c0100d290340050446a15060141c603204003031100c81e241c6950700c0c4031a42e40500101c42104400910019010171601e903c2c40e41c803408400100101d8030210000081c210085101d40d00196100c0b0f0304a08040700c41c9820901c40035248100e02c180e950003a6142d000c036058a9484614684107600c0303d5100d002810804556801003107940750030034003545035032600040b4140f40d0b919401003203000400211042c0c20b48044071800031040d040c01c01c1c081d5032841600d0300e5075041d09044410703000350200041e01d071905000b07039410f8480c0c41c0c010500d860a0841000440303040e0480568010f90011114008102503041c000b10011108020300006100c0389030013414168091005414008284030380400300e8011405100340c507000242c00f1a03019000400078604801e250700080d0305600303001c000d0003c03040085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 506461214 1250 506459964 506460001
    0xf040b0409210203090f130e010507050d1103040201080c070501060509100602011811010f0e0a03080a091e060c1b270209030606041508010c05070b091903140c06 71
    0x6a0b81e1000042c800c02241c413841204002980441645640501c42c0f500103110001034110600004240a01c50103250a440c41103a040c408a0000304000b1840ea60341d000d0340b8021015040c126281d03140590000c5c01101d000350004203550404504042009000d5005c44054a4000c280a805240c00005030b00003c0b22030060780019401c0c6a4000c40384003043d1020701001c1d40c007401000d01007401e003004540c070811481004007001894031003144542c071075807034140103940507515540d81c429006102808150b61503000021070503052058040d4011912071140507641c59152882070000241065100040502084c0c0301c0390008000000d1400c1044400e01b6138007100d28019040800d06004000482c01050000c82e0550803800c0040e1503460030f87d000814a02c51004445501500c596502d42160500c40040000c180c001130b41c0800c2c00200c021003603101000c81d000b0944110559a41422481c01200041c01d00018094135400c2058540c03d0700c50100355841110001c0c50003100002d001311080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 506462464 1250 506461214 506461253
    0x50a051005190e1507170412030b011701031506092f040501170601090315020c06250309020103020d0228080702191110020c090a0203090c0f040b0409 66
    0x8141100c040459070140c014902968009070242154000080700014002017440303003009100700e05440c6200310504194002d41c010f1248482c5544c250704064211582c40e40228180481011010b03038203a00c85025505581d48042016040a40040c4150181a16810006006041a0324030410740091031104002001c0301c40b070f400d5103c508070391041c03080c49940691400183d0200001c2d000b80c40c03a54010ba04002d041c5803441c0410b540e62545944409c0803074402401c180c000403142c4200004100f010782041852000c0c5851260445e000c0f00d24860910007003080c5502d842424055a0080d4181c4a03a00720329070040d5a80c0100c4002c640e03800f03964130140590030601c0c00c05d8407010b501c100fa660b441000c89400415011040c0c1c1c01306d03c1041d03502c2030102e6078500c00c0b6840f1042c1d0340300e50307141040c0b1800580080010075030000c1000440840142040a2544140100840028001002c00c1181d8050381d100600442000214001c0e18020078460b40150402c42c981c070401910480740e0304100b009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 506463714 1250 506462464 506462491
    0x2041203080a060e011406070c0b0c0313090c0c0f02031e0106030c090510050d0c0506040306020c0c01110705061305030d0f1b02010801350102030901061a030103060207050a051005 79
    0x640341141d000450a005821b000070b80e604004240d400e10000070030601d0f0041c014089420750382d11442009038010710307100183da0004a80c0d51009501e621110000d00020340d01070003500c80f22031006001d5202100c0103480c1c034880f0303802001991010b100300041504a81c7d41c8151110b5407107002406004c05220484004a9280000440d080c0d640311341c40c000c00345075060a800c549404100f04c5070441c69642034940d04c46200c00001c1640e61600107000451080801580b02c00c20510101d080c42d140309070003410300a48031000810383d040131500320181d58040781c80030b803034182c5000b005d0101d00d900c0c0c000e04d4062054600d00458142c01000400ca60180c6548680041c610b20b020045060166113000380801c419000510091025030005159075001c0528111511060400c00302c1b4500d45c400b10b850386960000500108050078021080641181e4101e8481680c04450307110f038078401407201618160b0701040b18010080c1c2488102074158010040742e8a031042400d80a00915081e9800181041e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 506464964 1250 506463714 506463719
    0x40201051803062a0717300a110a080a02030705070606380307140f18100201020708160609020325090614151902060103060e0106050d120302041203080a06 68
    0x12840c049030300080e1b21100074081c010b40f00442464a4000ca41c0307070008030a4502d580d407400110b9114006400c01c040031040898140102072104441c40e69211040e602010803850720003640007100c454000c0000740c00141d4036541e0007001c540c03500945100500203420480e0000b005080340141d2225080d1609042006092444030f0604203c1004030701a40c2040500000d058240608001190942154100303454000a0b03101c9904540c010602e203030f81100c191a060501d8182140625200c002e1030000b1450701c80c0985550f2910700403ca050b000408507101d0300401c001d16900407104299002d8121031181007a80b105a400085401c845000000c80310030000e07080303200b809004202c070025010882844c840b607090009481d0751800d1528a600d04101c901071b62792004485800c030042e594040c1005506504d80017040e1041c501400c500c0d68100300c81842541d0380e4010400c01c540d4481c1c890205001e6140b4241d019005070391088441c0794905ca480d00a00d81c1142603681b040300c83d00c004101941c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 506466214 1250 506464964 506465041
    0x32a060703080103050c1f050c01060b0c03030a0b04020a0c06150503010903020303010810092004060e01090204030212010e0706260a0204030519030e012d020115060c0b04020105180306 81
    0x4041c0c100340c403628401100c0000d51802100101080301070000003042f01c6844078900c00807a44420b003200003941c800070800042e0705980c815001942c504076010340ca4200c481c40d008000307076454078010741301d90fa41d0444210a91080c518100c01064058000e100c1c00342e0500b0040d48940092041ca000c2d0b007c1c0d8030f002c0002c005075104140c98594400c4d15220500505d04100c800001d01c4000319070040e80e1090003141991005030528003c2c20180f0001d66074074194030501280307200701044200142c1c10f10380e4582c280000451a282914654600591404c0c511081c0e400400e14000074640780000f11740074010502c00580081c000e03070f8000c03021180b49045041c1d006140b22082e00001d8006a0b0f100c1c280d84840d845208544414613000442c11661590311030710b2407811a2600700f043c007603950341700300c1451016141480030007403200e4140341196028545600412000040000341040710000742c804904004a0070001e1210000c0c08813090752910041c07071840611042c0318030500320305100d8150b5052 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 506467464 1250 506466214 506466229
    0x90310140f070f030e010b130507020c090f1317071a1609090c0504030206030a0504020f06071709040608250f08030906180d03030f0614032a060703080103050c 70
    0x214290f0b0340d03050300c900032124201d0051400310203041e0195214440b045c0560b58410242100310440a0005018141500060300e07190000180038001d8101204000010791042c4e000d550200d00d0320790307040c0c0e403080c5481d1891411f00781012050301b14501049140512031044031302d9000110340b014030582e40d02e841c480504452100c401d00c1e80007c880b600d080c00000c102c0d8212a0900c409420900e05042c0c070303540003551303d03002100c40d04800c1d0f070380720200000d41c03a0101c00e20702030250940e0801d240a621351a0860202114650f4440c0000c00140744401030729640c1c0840b00074180001524412028420744052014080701000c050807a03032040070404100c1040c640c4221003500e0b00451400210005115240d00b1003100382b1010901c3e542400b01c1ca40701d403010844158480c0e500001c00300c041d0050b01e800c0f01e01c5d1303801810078104000903502c61524000303403003551088500544200c91001c044450b842c0c5000d400034540204000c1040070415400500e40381c16a4403803000d032441c1109080512652 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 506468714 1250 506467464 506467471
    0x1b0b1b0705030a0e030f0a0b0a050c0702060f071e030c030216080703020d0204060b041712130608090109060c120e010902060702091803030412030c020105010e06060a0302090310140f 80
    0x90b400411198900c50701400031281d5080f0042c094400c0061130000c1c107030403e8009001074a10040340303001c0000e003030f00c1803055583c010074030480141848000e4000c14168002d60b40340c004500c0000422206200350b012140e0410540145001c441000034030f4000c3c8000034000084004d48641030340c1c4002603005001242c10346082500030581b0620355002c01040001c0b8039400d9800640d200c0010400c02c2a440041000c1c014180c0c520500c3d4003130b03400d07103860012071420964095205000012001001d21402411500c5a2078120b13002e4469032074640c018990034000030402440c6c00540303c502a0015000f080c403001441042101c1d2204107180b41c00c0e100e24201c0254841020400e01006240050a290304010b10300d12800c500300c2140011455a0300c10b45064540d0988001c031103080303d9040c00780c290b00e604184001d002a501d0540340c07084290f000f60409105440c040340c61028981b29505a601e560350003000c0b100035003278175100c941c020507184c620030390400703c4400001d80300050703000540d02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 506469964 1250 506468714 506468723
    0x20f16110a181107020607030f02060c04140405061f0e01030e06040f12020304030b1e0a021204020105220e04110312030a0c0908030d0e0d0207030201020c0603071b0b1b07 75
    0x89250b568401c030307001018241e80b00041c2c3c440500c840b1001d41c4815000d00340307051003926500007007010394002903c0c2860061400141c10000c220501030107090002910700030405980105484c1c40324000250700300305007500020b4050401c0071000c00305900c12200d61811800307880c100920324072200d089480f10b400f04e4001d810f070202c0c1581c0100080c48a04624002c3c000ca105503410b017500d80d43c44a6540c40c06079009420141c883c49041c10b03a401c1c101d407164001d02e0b011021841e050020141c0140140d000741701034148480400c01c01c1407400d00071200c04084c80c1c1c0b80c1c1040d003800d0315920300d00f44121060b101510003414024031a2403500f00025140c1860340119503040c110790764070703020f14060f100365120001000140d901c0043d4002d802c0020b0302c8011b02020000c12210b903074814a915085403400c400045501400b01080541d0b00460504840601a542a5a00c1c2d507400f00903694110b4070444804c24600004000c42030000030100d45000d0b152486410b0b2566070b00c5074401d0064019080d010b1b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 506471214 1250 506469964 506469989
    0x16050406120f03090e0a0608010c0905010c030807050c0d080a0c03050c0409180209093f0717070f060b0103051e0603010902030111090102070f06020a080a03020f16110a 74
    0x1c5118240c042d00003600c20315141d143c10740c607144c22041e00e00d402d80c0c5420b012600c403481408501000c1c02510040f500034036043c540b1f00d10700f9000030081c150307003207005d000d2005000100c1e054078482c1048408440340482141c00c040d2206200a00c1c1881c11501c00700406d00d0014000c400510038000c4601681004040c2ca00305420001c2c070301d00030800c0b03030701501d020303076151411300300503210122007e00c04c4443d0070140054410350200514044140315410580005200f882c0318122000802d50900c80c3d100078443e5186c4c021403402010b01808168850f2000d4408260402000f51040c2c91030b107014850700080c1b01d0303000300400540555500b503660400600428800050441d03004070380c143c1c0290f00070b0001c207200070079070082821140150030b04031002200282c2d00303400c3c1d6010040721004010211410080500c0c0031030003901e0301c08000e0001c02007400000c000403110721075015a070710343c1616103d040e0743d43c00a1084c040c41c0307000408122042406100d40043d0340c90002070400072038900b900c04c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 506472464 1250 506471214 506471249
    0x1050c09060f0408010906020423011b110a031209090c080402131b0e0f06030c070b0414060a0c0f020a1a1b041d06030d0c02010c15090516050406 64
    0x200d001c2e044032507600709100d002d02000070950400d005003210035020701401a031326801c2c2008078041520b00103100c1c605010058002c03d06d030761300c600d6000c440600e8800e040d151200d145003124038180040c00d1203510003401d031270120a0066150404080c01d096071581e4503582c1da00c2d0074040036a203100c02c1c002e01145502c0002005030600c940c45c0101c10540c141d0020380002c454903d1001c2240c0c1807000000144910100300107824076205034220243d007102d0301400d529188000f0032192003018001480000c80c130000ca001c1100b149040c4889424080690341035241c10080d0700300920f80500c18170001848444880b00b164008601c02c1030554002e10105540030803289002460800a80403203072542841c0340302003104005c0805003020f0320040030540164503c81b145110b0040010740243d210341c100314035101d0b5164002d0301c00070f5015820300b00b810325404181400007201024412101c0b01604181c040c5080100200b440c010b220004180100c144c0c0e11a02030000721281401000310554907040d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 506473714 1250 506472464 506472469
    0x60f09120305091f0905011d03060a1d030403060209041529040b07050703120201180f0f0b0708060102060c0c0d030f0b04021605100b0f0423070c050c0301050c09 71
    0x28400254060710031800360103504d69981c0800d00c0501c401c80052240c4800340500d40c0e02540840990041c000070400080c1e40b613000035195000a8811a0507a596600c02d0320b0a8000003040843e00443e502070701c1d01d42e82e07070303040000207548655081c61050b89000305070148070002803074180c00d03189550005010702c1416980030041c4481100c0301c1111110030b10000074513010b001d00418003030f0320030405030a00b6803442c90714240410a02002c0030559045c484032014142c0c042d03d982003507a42012240441080c141090700c0000f000c500c01600f4040f10340104042541c10410300d6001e0503080e4212408c3c2e03503032401c2281c400c1c050078400b8809500101003141506209803c110813400c401c01002450b0039940000400702d0b4403295640340c0404041d20030b001846414031440501808194052200d28000d0001075204d0090182540c810781c3d8580c4c940c40c100d03e14003186281d40b454501c079001d01c1e003071000001e0401d48202d0012182c5104003e00e03070429003018081c60b8001c9544001d0b075800e00b51075204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 506474820 1106 506473714 506473717
    0x110118060f02090f190302041103181506010309050f1608070e151002010f0f02270d062003010e06091602071a090a030c060f09120305 59
    0x40743d0a9840b01c070b084d0812602c04030350a00080002140c072501403845500080e40003850503070007441e107a8003640107501826802605080c100385509000e1b40e02c40d0000360000101100d000880d00f203502a0b00460110703441803040e00c808007e4042c00a01d4084008408100d040d03031150100400102844083d01410b6180321a0f0345d5403604031501007030b402c204d0f14418042d2011403100e205d45d510039400440700072040c0d6000e001a01c22020114040d410212070f1003498450202006090b80c0c1c200314030908800c000c0d0120242c0e19039038a40b4401051118089a14200c11805800f500310a43f00110301a1802421041003401d151007840f1580e803005014a02c0c1d11140c4880b914525000144c0c1003c0b82d8402182420101084560080601419070740507082000c40c00b021040000141ca0201176075070941d208603c03c4800d02d02142d082c00c1900c5072480121843c00c0c5d9002280c803460 = true := by decide +kernel

theorem cover : BRFrame.Cov 506294964 506474820 := by
  have h0 := BRFrame.cov_init 506294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 506294964 ≤ n) (h2 : n < 506474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
