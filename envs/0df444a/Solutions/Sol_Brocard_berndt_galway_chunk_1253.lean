-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:00:47.298328+00:00
-- url     : https://prove2.me/submissions/af9740e1-1b74-478b-928f-fe94812776a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225179856 ≤ n < 225359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225181106 1250 225179856 225179869
    0x2150a0f020c0603420a08010b06030c300a0e030c1c021e0c03010501050d030503160c14060613060b0301181d010504060c0e030a0212030c0f0a02 64
    0xc040092000d400c00c01c4280000820b0b5000142400c0492020004883d20703041c045c048005104040035202c2410000182d018049184052135a40c02801986d80010702150305000d042d04501d03000b040e172429541e07095203c16003600001444400c079034581c100702504400135506403901c5d800c2450807802d1490005c0c0c00300c1c2590084404024a90320070842a40c501c00d0204950100144043c00c0345551500d04200f245002040b0b56034130469100701c54005000040028000d2504805400a200c9680d80f40104038856102000c083e003c140c0c05c200180400520481c2c100e4001c0f103508242400d052a9129400101c035088031a2816a00440c1401580d15106034201c02a44002e0030a020540c10010039550303d0206105208403541d0301a4000c80803082c030780024181c5601c160340360483d20640340d092806080c050303905032000780c60164010001071250010701d0190030050000d00400c2c5084d802c1c050041d40c0a1140d1055010034801c6880640080c484c44208c841448002d00b02d21001d030041024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225182356 1250 225181106 225181127
    0x20d0b09070f0605160602091203040f050306220c030b04030305240112020c07091401061209081918090c020f0a1713090c030203040b36030702150a 65
    0x4031416414040080c584c0c0702c1c04031580415184038079100c03043d0a1038080d001e4040c10944591050f10280d00078145400040a04200c0f02002c40300c0c0150b42e56407091688a0005441ca11104090141c091014038a4565158005403103000c030302d0300c000d0b0380703846202039080c0944044002079283c106000709a0503031011b445041c204564001801c11a00300040d041e0080070b14800e0040b6004150154000e40600c54240200403c0c074081c4046040c004d00f2403070104090088802140840c08846502101c0d481008101c543c804202352078070301d59818006444c0c3c080040c0c002003052086a42d10450031002c042c0004100780140402d4500304070350040d060108000c0d9600d01035000082c5000401c040c00b00500401da001c3c049140c1d02c0c8403481c6450701e5a035264105001c0c1900341015215480d501d903006500c01c90184110200545411075101e440c0000140544c0801101c068031f40310403000683c2142e5404401800c0386e1030b1448560100c1e46251041e807101402c22008980d880015802220070700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225183606 1250 225182356 225182369
    0x503090c09010e160c1208070207091e090501090f080a020c06120f07092705090a03020703060209060405031e0114160e2206030201030614090c0304050307020d0b0907 73
    0x1c0d81015a0442c815038020b28030010b0f40d44c00710882070700c03500480000e030308942c001340104080b1500079030240c04880c080c1c4026005100d90180091414100c1c4100e5113500144444221805254584070000e403005902c00d5400d5540c54481c0300016170700c0364800b55158456440c071512592542002380c00d142514010038044c2c01c08101c6a54031000341603805134040c250400c02d00c15038851600403038121444c0d8010000c158031000d980300e20351040d000303450360b4121004030078003060b074883d64816200c0c0f000b81c6000f400346c0d02109060000072031036005001e1a04020b00760754101a56200040d2400501408010708a95a5039070f8400c0c0f16028010130070281400c07589000941044030080440404026101003003004228540070195a13903030400340c401e06420072104030148150b000d00010061444104d011910b812000030342a088a1400b4001e460000c258440c2c0b6611400075a80c0c60380018000c0b9001d010420414005036078540300340c05181d00400040e40140b0304908081d161901580203613 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225184856 1250 225183606 225183619
    0x103060e0103020405070203070503030a320f1902040e041109061e041404030305180105151c02060f211504020a090302030105090d080c04060504050d110306070503090c 74
    0x40c0314022055440c103046a5050318001000d0b035801320100d0950041c0c0c40c000703106000c00818171540010f5604001c0455603c00c0c6280286103082d041c040050700358054010140d54044e00043d100052440120761040c50407002c50607208050b00550100d0340180c1100030b2003164902400140704112022100740c0e035064034241d804d414002e0001d007045000780c43e00604076052110b083c01d66181c0b81c1129a00c11f4021500740300c2030429181c0079020f00070484104440c0e0710102c004100c440c0c01400703050301038080341166402d00389101044c08052269001e403000b104100071004401a203c3c5001001703a900c0c450341c25034031880c0140c0c42e4201d01c43c0d8800328004580703040d0148101c4c00d070310001101d580d00c022a00141c0c0c4824415041c0c40e207041590020354194a8502000404030003c40d86100488541d60b6a44c59641c03000c1c140c8000d40a6802078900040091000b40050308101003003401d1030b03005400307000080202d940000e140c4482114541e00103800801805445401000048100b10044440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225186106 1250 225184856 225184859
    0x90303110310051c0206161a04030e010c080405030f0c0901060f0801060309030c060e0d031103040b06010503250203190309020f1c15020c06130503040909060e030309070e0105010306 80
    0x561142c80341600039248262902e801902c2c2e804503802500c0180c96010f010a6140d280e40480098241a207600643e000b410180708081c1c281c0e400c0000d0380c0b0440c0d042c0c80329031410348007000454119445840032103d000d002c00c404201964104032030804040084010045424070b001400341511040c0c1c4500180b1010204401c00181c00a00c524191001480c00160a0503681001c8614104105000c0c0c81c0c0e901c2c180b4801044200031520220401e820b0320180300d640c4d403c071440b042e144030446020780700d0880e550100e14158030840045420003000031190404100074140700c106600d03215034050250f800020503003a0b400280384801c5c0015142d007010000b4815540204000d41c645070b075001d2060100703180304070520a141a240500c583c00c0150104410341c980180c00c000e62003403211141c41e04c1a00b0001f0f04080e0014001541c269204014504240c6170003046800381251803401c8542d5500c443c04d44550802c10409544180c0e00b01c0d0042060900d02900c11025440c1a0030060405050031360 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225187356 1250 225186106 225186121
    0x307060605010819020a0903140f160803120601020f031204020307090212060f0a080111120f090a0f02030723010306060f020703170904180b0105060304172a010903031103 75
    0x4c10000440d00360300942c1e0b600558004441c0e00c2d099420042c090707919003944031002d00e00024540841c0c841e01e000c4600c2b00c40000b00e4010000c0071031044800716441001503502000c0c0d0040c08a030080340c107004644000100000d0582590442e4200c94401e10300102048150f1804122000003006070b104d046190075100303400b0840380701d4002c0c20503000f260103c01e0034840da140d61414000400c2d44000810815000c04010b4031180d0094940080d07031b105d8103006c502e612140f030b40c59a001c1d0364074100911204515035100080d8410014040c0d03071600603000d001482d40e12a441d002c482141034001413000460300c400240403215550490820030400a50b0440055000030f100c506807a00040500440b1600c81c4006409224115042d50050b04142124a4840944d03548281062090380025138907a01c81c07040c00300c3e03400b080760003070105030720401c03a0080b0300007100081c600366800000707020306031f50340d102d1310003803000d0f10403020240e40e40d0780904c0c909050780b42c03040148041c641d0f000340d4a036050400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225188606 1250 225187356 225187381
    0x120e090403080910050108030d050114010f0c0606120b01091d1905010609021206030708060403020c0f0f120c010f030501030b07050307050d060303050409140402131109060c03070606050108 83
    0x3030000301030020312400b044811a0070001102848503202080c4001e40e1512030080d126000b00b900d054915003014004200381080700c888041440040c0e548080c0d0550000044600c0641c44805032800c2c0c4e41c071030b0042030303803056100102c2d03509003e00c00740c1c40345516021050b0200ca41034a41d0a40d120410908500c440c4d8004c50400403452440d030030400007040c5401c2c914014021640600581362001586040320030035640b145200342011003c1d51412030396858101d84421080301c0080041c1c11102d070105482c903100d1201d1550100c007400b181c015000d1540414840c84083d2203800d002d40c00f880c0902c100d0f40c2d20000d00200a42d05250501c00c5526664a0109000c406080c21080c03000100004200e50b125038103071007a9031183d48050100035640d080107096603009010300035146080ca01422100d41440d004680a036a010b000204412030941841340244202c0401088584003007001010a5032118082e18441c10000013850307a0f20750901c0e210085450550044e81030007402402c01002c10b081c0c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225189856 1250 225188606 225188611
    0xa0f120207150f0209040501081b0307030b06040504030c0f0303092a090c0201020705070b1c02040e040f0503130303210501060518030a0b0906042303073c120e09 71
    0xb40008244030b140c0300d00c080c01034010103080300e07005880e10b400080c00d541f00190000b50341001e401204140040001415121881400064241e10000c8041600be040552102d640709000e40750451124009668858601a00c1c0c0b03002d80000b0f4440da0000f0620142249071a045180d11311501348200305003201803060f2006224100b4400e5a8204030b005440c002e4044481c3d103a40b2200382e50380140c81c2c2143c5c0d0380c6604288541a12000500c0c416642c11145200b11425200b02540c1a0042e07601c6944040221140c408115014081401318035140c80183c58680090b41c0329403502c1960481015111101c14034408000030903604000040103581d40101c100e45d6504481d042d550300e2509482c0100745000044d050040c14200d046082000c040700101d07001d400f60b8403811030545200d210b0410a000e0598034012400160810000740c400520a100d001d08190361050b1251050240e03c000025041d007800c13000c400d007060b07080c40042000500e046424143c2040e0401c414100f0784030020a00c0c80000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225191106 1250 225189856 225189893
    0x4020903120d06091b0f030603030813020a0b0d0e010b03030702101202070206120a051506041203090e070203040303021624020102090904030f030608300706020a0f120207 75
    0x82d07101d00000070390446400f40082c0302c1c0c240b080700e50100c19507040700e41011717981001030341d4801c4180d0b5491180c020403085075010740e1001c4442c0c0307444a140c804032039421000ca911060100b800258803c3c4074000e0001c0051050001443d08075010949080d601003c00c2c031417084d0000c104c0000140d030b4881e80d21a1a50b1a4130340700c0c802104100e1858028804e41070701a40c0032002103030100c0042440501144511003421050001c1c1d1613001c091844a9040c50780e403644284c060005001d22510041b011107000d010f464120f40319a41e0324001c505d54001541c1e01e00044e00001020300903d6010004a0988a5411403003000c00345401d240e000e502d80350320074030010118031008004031580b0035010380b000210300a0106445041c40d28018081402d007803803c9004c0b070308050f000140b6a10228221b03660311628124082120301c00c1888030f900c1c0e03000a1421101200a0040360b020658500c09031494208a440e80003d0080c00e0700060310380301c4960200b200303050040104800042c10103003245040300c1c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225192356 1250 225191106 225191143
    0x608060a1d0c030709090f0506011119020613050a08101103070c03030c031e0e0d03020903031603021203012904080a0b04030e0d0602031005090601081f0b07050c090604020903 77
    0x1100ca100312003d140d1a4071480e501b605014071008100755543c002c502440c0c2c00d898520703949030b1414042da02c8544080745408040c024241300005824030f00d0041c4040c40740400040c241c41e0311030002441007101c80d0000403140c0e0203800c070304195815a11542d00d41c1780714018107074158135003200700520040d0100350003420075440b241c06408250013500243c2422030207404100c80750614082c4000102050030313843d000ba202d6520100ca41a02a2003280d24581002d00651f01d4640034083d1240d0040f8101d04c00c0b000c40c80b07030090142061400c10080e5001c0d2075000c070010025900140004550b0b1001c1da107080040d0b230f040004003c0078000040903102554405440f2405a42c1e034182070700c100c03082d0b4020395082004000c2c14002c010165000318424841400c4a07459191640140034108508075225400300d03112202240c00e45400700c10b05c0c1d01800c4001c1428450903180c0c01c23510856000720700115004c1e40061a40070281c608200b8072540181d09440440c1800c5e07940e00025a6601010203000500c074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225193606 1250 225192356 225192361
    0x6050904060f0e0405010b040b01050f03060a0e181b0d02090a0b19030203070f060c020904050a05011509231b0c070b040305060a1a06090303130608060a1d0c03 70
    0x31a2500614010008110400e010a5079445a451030b100b0840d02113445e07500e0840a1890741c60640706402446070b041e901d40d0b0900781003c1e6040c2255201410b0b10340c3c4589003050004489180f103180512038203810000034030751404030041524105072500c940520720750102003c84682c0314541c0040b405901141c000f040c82d254894501c005254010215400c11083c4001c040164030402c11001128800e50407903540c5540c42641c0c14440c3c00300c1c011039000416038101e01c00549802002990854052400c2d01e01050302a542d2030b0845039002011242d00c1001f8400304008041c80c45203c04000054801c82181012204181220040108010f043ca031150441445071a0888156101008628201d0320410740718a040c101982162108480902c20a000216022070a01030120f90011140c01a410000c840342040717140c1e0000d0348610b0b01440140300300d480aa81c0d070340e00a40100110b44504800382484424054088410f030840800c8406540411100d21000d03d600c0341c0c429822182e0a40700d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225194856 1250 225193606 225193609
    0x70c0f050f060a0c12020c010917061f08010510030b0702030703080c13081006080717031912150503010501090b030a0209041112030c010507171501030605030313090507020f07060509 80
    0x131024806404125082a10083c0e035400041c072242507242600c9422461f5520580c10711265030700d4200c00b195400c0340c1f0100f07404108503440148881c9199070728100490700c41e10303003d003140c4048a41d0201176803039a0081051008070b2a80702c2c0c00000754030207940b0b00a01a01c001e840100c014080f01c00d00c0400140004940e00d04680200203001020283c0b0418603a43c2e01c004041c081600540c940340c0500d003400940c442c1451400301d0f00b0083c00010318101480398144614045030055201c0500800b4060901c2d400e983d4445c00d1042c1252080d4224024145030500d82180c83c1608040350051030000340c200103560004980d50540e81c1207034400d880303a45900d481c02100303441d04882d640184143d03a051859807404000b8000b030390345010013040103966103001110313860703071130b00000c0c05011240c000b01e502402d00c08004007140c01c043c14042a42c41c0da0b4004039241d90710500d0441c4205802020500558845e0301401d41c0200d4584014880c0152426880351100240e00c150410312000003401090f5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225196106 1250 225194856 225194867
    0x7030c05070b0c011e0603050706050307021207120e01030c0518030705041104080c01080f04060b0d0c1710060b16060902100309122c01030e01090503070c0f050f060a 73
    0x90041001c215440f01c8907240124040c1540c0350300c4e8444070380300e41c1c05043d00c1c40c1103200d89400c50760414002c0241c103103040b4041e205640040c00e401e00314011030405c100301000820090400034482c203150000c2c40da40d1000200b0500044801c1030400d800d1180c0500342540c400183c4110b45c0032400405c00042442c00000d14250190f0301140d006824a42452919140440a8011038030940152100030600c1e070011a8070350021150720019034203460100c0e0228400d82d0044900600c068850440790829840c3d08421142c180c2c0100c50710324580c100303841e01013001d00c02c4692040c1e506205000c5d250030038940544502501003032425003400703a40503105120080d0814510036030090000c02e9007001e030300c80060140c404070206441d890114040180c40920070500740500114510340500c200600c52040030301042d05e03000160400d82c446510005d907560a224184800c1e10070402140e4682a6142c8400e25050941c003a407441910010f0030400ca0312500b41d0850300c036604481e51540c4a4002c18150355 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225197356 1250 225196106 225196109
    0x62106050a0303090807080c180405010905060a020d0c0509030703020909100504110a120323070804140a0f0f050f060d0c03050f062407031e080103060c03090807030c0507 75
    0x1031111540074004103050f003201e035110a07200007a003598626601ca4290b5aa01d20410031115003024404200304141c04001c18a580c00c0352183c400807031003001c5501c0e607031700d04403091f038108404d40c2c0d00203141c40d00c40300e4511921000c0305090501600b020410340000751190402c2c440a8003c803500310004031441002d100f029244542c120040286003000c0c100b03440300c04d140841960251100302c60118050a00e444680902d540c103903a81440c0702d110340c80214030b030080f43c0c408007800c407000e100d881e000440f030a010340082c0030000705c6402400008400c00c00030111031b90002c1c02e046000b100502c85c440140f0340600079501c0a4aa4030001045000070070014451080801c041c185001c804601d155815040b00b0b000e0061080a4034460700c03103004203c9040c03401d8900f01e5042000001c421009024100035000c0c180c000d0030034000884a1018800e00e00d030800c404c040c0000e907030301d0061040148510032402040168a01000104002e0b601c40040d0701c0b07001c3e07024041c0400e0035403880402604109410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225198606 1250 225197356 225197359
    0x2150408090a0314010b0901050916022103060301061203140a050d0f0212010b034b01030b071706040e010902060d020a23090607110907050a110706210605 68
    0xb00003641c0c03802e2000c49915000c5645089500304801800c951410910190503101c0050805815803502e4200c440c2c840d1000c1404001c0d40182030442c0240041c060a102c1c40c075041103c0b0603603070300c5c0080806013140c8441d0030045007110109100c0d404070364003032007803200c2c0800e08103ca40d035480c0000041d10b481c000c42c00d4001e00141481240041d00c800c41d00500f020401c2100c040103640d80740c04003070480307000417506d0612401900b10200d00d0070550141c8248040f02030b0400c1c5400402c600f0050001b1b4a0741c01040140130314103001002000002441c05901140610303000c400800004c18080b001800905400c0c441c60311100c0c2580c0298082d402038070030542c004c0c0b01c16541d110f510301d103501035007280200c0b0004c507482004c43c0068030a0744803250131806a03290103900d0002d0dc0300400907150855202580d88002101040040b900e50001003030007a0030b82d0f02d485443e02c1c00210000e258010f00f96130140d0a8220250810070f054000a0003050070118100866400a5500d0280b0040030703642c1c0b00a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225199856 1250 225198606 225198619
    0x40807120e0d0f05010e0609031e040302120304030507080c011d120106091e0b060403021009030501020708030402100c0b060f0321030604061205070302061e12071206060215040809 79
    0x304484603c00308800f0340b0450080c4504010049106e440350303803c0b1047e400c140c00400060701c864421141d070200844622042c242859203a0b0003140780d015080f19019070743d43c4002000d005000003040303074070001c103202802040d4014041000070101c00b000502040d04e2a51140034000e107580c1c01050b84580c0c401f042c020803038956540882e8020300101403003d07100d011000d500803240102ca02540c102d1000c0034040e645458515402c1c401c030080103298490420124110200c0054000e00041c05018040e104c0703251642018010442c240743d0707140c044410302250807011030020b42d111400e01d030701c40d00488003459051701c032802180c14126026040c3c21701416250207111a5140b1101440c05280e0075101088410703101d000610b40c40c0f0107190041d00c05d5104000c00c10040c5070000080055070484000348401d0b000c0d91214140d15005107211145c4c0380c0d520404c01c40800d5200c04a0344400103080c0052115a14028010352205d0121034841c4c4207071840c80004080c85412811680d00e0207015004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225201106 1250 225199856 225199879
    0xc1203100e0402150d0605010e150301030b1f0303020106091404050a02010c17121503031309020d0b09070e0f1f03020d02070c060203030708010905150607020a211a040807120e 77
    0x80c40000c110071f00900b4082007107030010002a0a000040c0c090b902410981946103909685403010890300040450754081d00d10746c40b400945031010021001144a50004205030381041303601030170b8600091041d03000401d10000c00010510004500502e5602030130103601119032810b2191003400e4500010713507071100c0007075040383c9645103241c070341e1140c40d40010000c0101480c02c100b544a00c0344001e0b6804180c040c0c6000c0c001d1410303d81c010700007414200000250102c4134400310308605d8045030000040340d420440c003500c60609403507640c49410220f859550000340e00c04410042d10603d5284010141d0118100c0e01d0258543c0c115952550451100f1966a40e03404000399654403c841c4e00c8002482d0030000101d07040240941030140390040001c242c48004074051242d01d802c00a000c1c0d9224514040000c4c8400c07000155000030303800f821301500d0000850030501d103002201e0b0a00d0030116482d00c02c000c08070b030041c400d4130100d0b6488040ba00d03600300004c00071144a001d2066666000003208003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225202356 1250 225201106 225201127
    0x7032003130212030d060b0702010828110a0e010f09060c0f050303040b181507052b0b1507020616140d020307030305060f0a03060e071205030c1203100e040215 70
    0x1600044205c804180441c41c0c840702140c1c41c6000d074540090203c1c01540120350400315480c02003501e0b001d20304c028031140039078109960075580c11860705116400006001d1002550100380c048030124223013000200522244001843c00050f846160100881c003000c1e1000c0000c020701034005c1940020403a07840e0b04142c141b03040642c01c00e0f50b09804a400c16038403905d520102282040e4020160110540749a64191f01558141e010900008281c009840ea03443c821444c4200b507a0708030300c0c001c030014580d0748190a1100d200b005292003001050280a0f44006a503084212280744070755200d140c0e090303686860614020859481c07c000030340034100090100c581c0c000083c1044502a64043c06280c0f00c000030301074000f50403e25150015404001407020035a81d41000007050b8003c030448071000e41d80c0c500002c550418500c01c40d00c0703400011700046651010006e6100b9860b440080e180385060200c6101d40080032886a901e071380203407000180c00d40d0b485500b0000c21100e02d03d000d42d44d622842c003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225203606 1250 225202356 225202363
    0x604122a060c020606010c120e0d0605270708100e010603022716050703030510260708010b01020601090c1817010507030c1b05070f15030507032003130212 68
    0x1c0e2601c01131149400180081d80304904507241d5681000319918590030305036081707441440b03003c150343e08803c50002c084009030f0584a001d11410001003e418122a40445840f44040c4400a40026403159005103c0c03071502181c0d4040c5095140e20019082941c0750045000d0200360f403000c0d6012130841c98035241411078200e800c0103480c07402c110b50300705c2d6100030345d04d914040c00e0b400e200c3c0007807020311955000134040d40c85039400481ca20700540c031030b5544940c15045065000c40c550560301c046003080c19208000c020980c040c00e510402802080030120000359142014490760f210350f0744540c405402180500d4a4424451f01020000840c0d0349503000c0030304d1000381240c41003c642c0303001c0010342c40754420310440d121000581d40d440d020010050030b140c1c00d080080d80c141d90601840d0b20000301d21455690040c000c14031105c0c0b0500301c0420500103821120000c00d400d00385402d2051110064181c4460410341c0804002144d440303803500690721f0701801104d40000d4210f200701c01510203082001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225204856 1250 225203606 225203621
    0x604050706090902160201030c0c05070801021b010e0a080d09120906020c1008071110050703050609090106061418041d07060c02151606050a0606030e0604122a06 71
    0x5842c0c42401e00da0700c4010f40f0480c480d51244c240d0041c2110030300001503100780c100c030340d07214600e11f40006c00c1862038441d0707401c0c10700681c00004540c0d070020b08407521140b00c1e90301008079580170008000441036500724549070720181d50002c02c0c41400088040f080d103810351020721a10341180207d80f40c07180e001030142ca88091030041b070000d8403544220700960b1400c1c034460f4a14074100d03680c0742e18035200c0d49025036914900054a9203035024103c19500c221041d80304103481810b41d0b0340c01161a00f800001d010380c5060141c070b02c0030301ea41032420900131030742c00240b1444d10502443c03001c1e984034440300a002c030700c60f510001d041c0c0c814240030074660300400c2c03800320308a503244e55816501c05c00e0b600c860a0340c100b120b5010003500004041d81101ea0380c000700010700118203100c02c0d550068048c559980c022100100e90b00581f0a90345c2c0c00910650754035110360aa15104900105210304150300d035031008900d100020402c22010494020321040840d401807901e070140c0640b4400c0351400e142002c05040c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225206106 1250 225204856 225204869
    0x201030c02030d020a08011a0a0e01120e0f01021b07060206010e07050403050a0f0318080606040e0307050d0c1a041104150b070c031403030403050d18080c24100e04050f06040507 78
    0x4001030b04030304107c803021a4275445203500c0d45980c0d108920010350707042594a130a80c0e441659502d100384000d00c28803c0340400c40003c000141c0c0d4400042444601604403001507180e94411802881110303000221541500c05038688080300c1c1e42c4140080711280300d150001822402005a11810030001c0c0710080252403098840d064004960041c00701280114400c0d1442c40e40400b011400b1420507500041103c28070600b640e00d0403609403211464112002d14001c00a140402c524041c845881141c000f0205100700c50701403814035484030310a581d004102507100e9661008400440c002d000c08000090084c03250b0252621114103004801003910710003541c100d030300c0303960f030001200000c8100c7e4840c5a05844103030601901029200080c010403103001d003403182c1ea402d89408202c840c4054040c45014100904038a0080742504152610341004200c2008041041c130011240c801c04840c1030702c001c0f071113407202540e6900b0b08601d885801303c0441c40781e0041c0d2050109000021038610281c840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225207356 1250 225206106 225206129
    0xf0d020c030c100507200f030f0d1b05040e090a0c0b07151104030f1b0b040611150a020c010f230106020d0801060f0c021002060105040b0a050d0201030c02030d020a0801 74
    0x20301d01030f060354002c50317991001807030040705100d164404111029101e07003c00c0460f185419510401c6181d54450055150601d001091101c0d00c00d1803405204000d18030003034210b88803162141c0190260155008407200c1c1e003100c80001e409041c040040100c0e00d03401c110140c1d0396941d5003c5641385603225900607160a5440b44410400c4c4503140107041110100b111001e1400345151903040c507070659100119808503c4031211041c00d2003494007074028003001c0c4100703035941d480d0800c0a001aa42d90900407841c0e0408a01d081c503c4250000b601c2e0300c0b56a4090240c0d580d0b141103d500d0042c2807110302030810500c0d05510361614100c0250041f5100280c41d50101c050b62142c0d4103903540c969240007500000c08200041c04030500c5000b606050324030b10704001400078a564000340343d14050810346001070380104010482480c29016215081a05845003500c441c245000301e044401c1106001c1d040c1500c40c0079101d00b052007001100d681101d12070046448881d614030050010074284180c015428 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225208606 1250 225207356 225207373
    0x7020a060810090203060901090c11010507020c01111f02090301090f06150605040e0c07020f09070c0b070e010e100504180902010e0f010e100504080f0105090f0f070b0f0d020c030c 79
    0xc141300f100c1c000c8000074038011700703a841c5c1740c10403028201e40803502e0200015242c2e48010500240216070054081da0040c1100343d0a450004110301110010901203a10a018103c1c50b03260a07003800510111182016075158015000300c0d01500038100028514010120881c00384205584003252900b424140805155917690048409005501500100742e81080108a00746103072002000800d00c098000640e0408000014403da002195408081882805100c040020748180380340e11524a0410002c495450b000007400c42c0651980d00e03010b550f18030035140100e0300900c10749004081079080740134091487c101c41c030064141f5103006c0f4003180d00000c1c504103030b00c1c0c1402e24002c65801a904c02009a4144042026040c2103581801c1413000800000c502201300b03009907140f4210203070000c2800c7c2041c04c1c10741d24202d00641e4040042d00009000d8500a50226019041704d51a01c2000c0d1540c0220308110312038401c400c00e420101c1d100155082c420302000c000780006507104029243c02c074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225209856 1250 225208606 225208619
    0x2e0207051807050a1b0c090b040617030412110901080a060b0301090f060b130c0201020c1b013018050d0c080a0c080c0f0105060a0602010921030207020a060810 70
    0x106050b920100030820600c0b08004192040d40d080d0411a41c0301800c0401010360788840c1500301840c0c008800750ba844600054007420300340a8100140000d01200d020f444c1c1c44c022068490107640282403800d84c01c1c200907420300c128842410f0f5102002040f020080d40c3d18450540d6507100c2c00350403035420341081c81c8981d60345010700c030b03043e0712541043c501902965140d8030f02004014080c6a190b100d00900141180d440b02440380003290741c0113400042e0341c1c14061105c0303864030001c01120800c800e40c402c801481a41e20040d107404060380c12010b0000712244c45039003010140d00b032031f81c408160700c0c280c0c124035118806120071000d6805003059403c2e100752801c0440e0107084114000c1c148403002c002000c103642c469100c000303002e030140c00c82d2402c1101b0030207020705240c070844000e00240c4d1204180042444d1910030708000b403100c3e0008000c0314525503180e072041c000300107111450303408401072400598000e80465001ea507000300b0012003151501c8018002d02415585194804032181300444c0c44c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225211106 1250 225209856 225209899
    0x3020d090602120901020118030908120304023a081222020609010e09010b09041b08010608040804170114060a030804141f0302071101080f062e020705 66
    0x79503046038064044501d4001d01002c0f42e50004e00200e04540d82d5040b0566000350b00800d130300c5120700c00d644008100b0314003444249000b100c01c821544916080007404011b07560008d04000c4400c43e071305034a4002407504051070075280085000c41040c90300c0900c2c5010005014003e0a08a072406150b2903c4d0f100c42c005c1d00300709d101c403400410b0301e04500c00c8100050700d0041c0141c02d010205152144800f003049001c2420002d0a80c01803044031030103c0d003081c05141a000322040000002d60114026030b002030010100300062190744140110360300132406000600007282d014215048110070010a10341c0580d001380345042d084510b01a030040801c0d80c0d07181002103c0c0860790880c054608060800d00200042581c548a150744204010440301061825004640103410700362001620f9003145d050400034041e11800490401450300100b02da40900000b0b440d1f04070105899100602200ca50000040e031008407a0440144900d2019090340d42d00041e00c0041d5002500d84540c65482407808154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225212356 1250 225211106 225211109
    0xf0e0601080d081e18010219021005070302070305030f040201020309090903070c0501050412060b060706180506060105040b1801210c1403040b0f0408040b070303060524091009081903020d09 83
    0x180c1d8100f00000c20503417a20001100c0d400d0140b10001450504e100c5c011020b0146016240e4015820030741d0903c50030740e01ca104aa030300001504055140401070782d8014010710008060031219407170b4030007180542e442041a94000f56010344810b50030b0074801c0100f0b659801041c011104000e6082d4046540d5100f0700c00d660403501605840135035031110f0382d80d03400a0320702841e076590420310030b121800119040c2e00a01002994904600380341803124148282040c0004100c00c0c144081080700300f1414041800303e8a9207142d03030034240800c070460340040307501440547c5015000d080b03900c516802d1540c10380c00703612100390546649424105040700007009000841d40601130a4002000600a040080c41c003a84184660141032030309403150039a09803a0454a02074000a82d943c00030b001d40d0500e92029035042d2980b161031011000524114a1140703d0141520b01074001142c03505400c6024030740780006040c030306058031450b444004202d0000b00305000d05800501c91004e040302c045001d00e26560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225213606 1250 225212356 225212401
    0x15092406050d0209010315030f052107021e0a0f0807060809030a181203021501050103020705210c0a050d0323012603161202120d0f0e0601080d08 64
    0x40c1030082c1944000c0c025009407440320b0605454a5040000d29100002080917520404000031250a00c0c10040c1c549100c46045138865101d401d00414807004c1c110a070361005504480c0700750040105190180128561500240c100801140100b8603074105000b200582d000c850465800f1640c0b4103048070011019142201e96800400c00400c020317200d845420182000380e940380e42c0d00d40c0d45203460880024000b00603001a00320644d102000210b01120b41d004041c04d203819818010f5903241d075516140a0f203d641140361251075008072044d0031400f501c00303606449060381c5940500e414039a44640342007a0000000cbc0c5020b0154040b441010012071a40f40340c0c0e415071520b0383c20203090000e000b80c010102c40100007000014000000d040000748059010f500200c01034144074500580d044584443c03c6041d5044800d1819880d42680241c9640452110012603400100c2064000404c000428401d041c02000000314194070001540300d05015950342d0070106d035942d078000c003545951100828 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225214856 1250 225213606 225213617
    0xc040b0d08070302010618020a1b0b07033201090b150712020a081b06010b0a0e01030207110a060206040b0a020307050a1d19030303050a15031515092406 67
    0x1400400d10041c0500b464912a000010754181c07a0903200d0141c4002d840ba0561041c0c0004001c80c0c510b5204080e5200148001840c44540d5016640c460075034800820f510101741d610040d05002d0318118610190008070079400000480c0e08009034050300303409010300c1021500f8401d0300c6010781400104040e80c20121000941000200d0380c5040f40f01c1c0d209081c40e0300310300c18294078401003000840100b03c0e040c460404101d5400410200d0bd04201d0168480005503809001c910303174141d0065503c080c181024640160303112907510703200943c6413210980750703006442d00c03601090458002650303a001c1c82c00b84058840c590b5134407246806a00c000c80340c1c100003580900000001500502c03c611030a44141d641d84d25000f50440070500d40114039000112401d4400002c000f8540c041c03041e5500070586400c1885808018890790545035014032004101c12000700d010b04000c00e40394810000790742c0d41c0c0d0545110950304d500070b1003e004c1c2c03020495591400400406018440b80e910142107900b60b8940 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225216106 1250 225214856 225214879
    0x601230105030c07080310090507020607050d1508060a050f24011d10030f0b09130b040c080d0203090103060608071d0406120b151507080a1b0f03020c040b 68
    0x444641c0c2014103441c3c80280306024000003d100000a14881c507210302540c2c4481d17150040070000e6905c017402c2c2400f9900705e0b02c00c1c0540c0c103901c0070803503640030085640444c1d441d11000e800510080340d80c0c00b0714014001d4009019442402d9046680070304a48580c4e04600d464940c1c000601c00780c200a8803041011a250300902c070b5025034400c004084030740301085214549000030406843d01d450308880001ea68003400e003020600c902c43c0769251039040e2240e1a0900e008a070081310310714041000380120703040c40001010452100140300191502c2c2c0c0903243c3d4544846000b9540e50422402140400c0c2005008102d80d845081c0181c03043c44d00d40c1d81d1004440203104400702035071021101170341054a0304c00100e0700c5a002e484d0310b8400ea200390300d400100d01d4060700f000c280c144440104e40c424100360030110812080d41050360340e40c2d60040c0b09180da07550440070a950b03a4078540d1a818021a41100000074840c1c8010103070030040c080e809864012040104100468018001c8031350710000d143d2030b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225217356 1250 225216106 225216109
    0x1315081507030f09061d06100f14030309032407030e0d0c0809030106030506010e090106030c0b16020901060c0203060702071a0d0b03120316080408090405071e02030c060123 76
    0x100a09640c5043c0020305040991586801d0790790100f009811412100400c00400008000711a401a0340c855142d021074202004581c44010764810700128105450504180390b405004842e00740b20002c080390840c0c100100400d009805180024040700c01e0040010426400b90180110185000d800f80a290611500565203081c0c1a40161000340090102908035102441180302950040008044070341c5006040903007c00700504030b26050f41065810400603204440c0700c3d0695243d003d0090301c0f05222240d02024120044000e5480b00d6884000900300780c0014101d010b0f18001e5098417169900c614050303070340c0e185c00d124a0641c420403003140e04591020001919005104480c0820240c06c1c4c14000303440d01d0340c446602e280d140000024045071503990b5040050000e0346080810b15490035407542a10f500803200c850340100e86030000500c00b80d20444881080180c0c0700d80b201c4016441c200d009580703400405004495228160001c20070f402040c2c5440801c21a2010b1303040604464070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225218606 1250 225217356 225217361
    0x1302090a1806060618090204061b080c030301030c03110a03050615030f0f030307111204060e0f03070e0702210a0c150516080c270609131508150703 65
    0x10512001c0c070403045001d40000c031103004080081c0004e41e100c3c00070600c1c01003441c4050410340d02c50120144100030400c246500300c12805e120488a0049420107403a034280401c040c40340c0e800d40c42c4540400400401008500f21040d415a8050300c18613000038843e00601c003011240f4000907001e680040002403942e00d000320b40c016140005400d0380c19076084860a1454000d09011041d001d420100401401d00c0d80403842285010081c0000c0024062a94031510588030b0740c001c14041004000103440c05460300b01d582e204924019045a00050755040c80b0b441455040d111080180a0181c2c00c24244401150354400b000040c1c0d00a03140810001083c0d40003981107504981280d008000b507294503100d4030565100d211603984458100354403400080420100800b0308003100030602c2002c0642d0b200062548500400722441021740b140035000503250301400c00301a9020007999845039051ba4650030000500308030080480d0801c0d02c41800649600740c070050b00d0071115000f0000b502081c07003074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225219856 1250 225218606 225218621
    0x809150f04031a1521070806181507080720010504060b060a0203040506220b190f0c030c020a05060a0306030204050f1e041704060c030801050103051b0c0111130e1302090a 75
    0xc241e50000c0c417590301d8000d080c0134140e480865030790801002c0202218030b0301c018007100850380001d4034001c4003200b4448503074030700682034004021103400000c042901900184401070100803818409500303c0d030401d070191a04903000c0f0381841c24501c3c42c049504000083d241c000030950007841c2451701303090a018203502308010450039a0103008507942001c1d0a03103511800b51504c1c0b10099541d01c01582880c03100c96107010302c00f0420a090801c4000ca69001141a800d558541b801401030002d80c00000e402940ea6001586c0c450000200c4600e0301e5003644c8210100c07482a20b090115694914040c984104211003a0202c0c501c9440c0da05085c40c10040c1d1680d1040c803030b912501005448800c1c4848541180c1c100502084154564200f456004400382c0d00408003440c060003586072410462100c03451100b101e49a2041c0820741c0e650701002034006008454400340010703210416640400c4804840b4802c0600c40d00b841c00109100709100d00c0d1002a031034010313007456029100c1494100040c10b25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225221106 1250 225219856 225219889
    0xc020105030406090f12020f0a0b0610140331170705070f090504110d0c090f0209091f060f140a031d01020918130809150f04031a15 58
    0x12655140009a0780d0300c0d00305e900c03a0149980104006425401a10f4041e800450b5881d90f8451540103001542c101480c40e4081d10903940c900e2081c04c40202515840300c1507c407507100110100c2000112403042d1088014299175254522007030980c41000f003c410700e0144064611203500003480401c16000b0000c0c005248240d007203442595892401307040b0f03a03c164210713681d030f151500c050205016075102014051102111344203c0b038031156071807268407041ca1142500c01c82d01c40c0200031101c0010340c185e40800700b024010400c0d0345800441e0711502e80324120310046404540348081800d510070000494003890b146c0b10080b40d10095181a41c0f182c01502e020000c254581c45407048980c003a24101e82caa13400080056101c9500208021000000d01c1500342801c440708104000448520f254801d565040800180c0e2101c02c1d40c0410114209103000382c1c10080002000c0200301c1601000b00101c80c012030f0711300c400c240f03442c010101004003070b030784d603003018186000f00c6502d407801500c0c01c019070b4031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225222356 1250 225221106 225221111
    0xb130516050313120e0112050609180c09040f0c060f05090105090402160c090c020a0201020a08160203030c030a180b0a181d0a050c0a0c060b0a12050c100f0c020105030406 75
    0x601360356a070500d0781070000b4040011000d916072034a82d41c0007440e100018080c04001c0c4094038144001c80e407e1000242045140c03541c00342400009078060089509011001d00410450310301802d0040380c074a4105011500c580c5410b10003d44c0030b2048181c0c00e83c00e0700964030a4680b42c018801141c968004030750b2113501982c20007100c1c042e001c06040b44918140303d25540007440d03103084008412654110700031800d5401400d590030050b0303400b00b6140c00007035000d0349440d151101120384843c09040000c0c000c4d0148800100311141001c0040613084001a9030b582400c1d40e0604051100c0100a61056171000311081c0103003000741e0b0043c1440a0407040080d0101c40007541c4901c0703244000124549410134454034001d0141b0f0074200d01900c0d501052480c3c03401d02e0205841c0d0000d080c0400b000c8042c140e0b41c0d50b918a0740060b5900b440000c014120f6150381c40b5061140d0a0003607c504020b0540d9108014007110300555501414000301a406141c07540542c4445980044d40e050b40300034000c9075280e6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225223606 1250 225222356 225222391
    0x30f06020d1d0f0601060e09100503030c030c01060602010b0d0f031106240a05060403080a050729060a0501050318100905030901021603020a0603020a020a0c090b1305160503 76
    0x7456109014500c0164529054030b6145903200c2c03403c0210007000d124198124100510095401c41180d03111181c003036804a0150b62038030150607029a2980105a06000c009507488140c03100201901c0500b44c0c0c54000c1004a0395000141d00722550842c079181c0019030500ca00020030a07000441540c00e000341041d00200d501c142c071803170620800321242e0411405c800d0b0351508003200c08800b03050424040d504a50980c0c109400500103020728031000300b90241c00208400000c1c800c50075107050b1644000d004d10f01c04040d00408482041603000e0031000d003c003000240c0e4a15241d10004210384040e162149580c0750000800403015011107071925a115008901810311020300c41c89158500540c040c0d6100c0802e1b100090400400d0814480403501280d030074805641c500d82c4440403180c0c0b60400503074a60240708282c0c103124040001410801d0402d600060140b001e40040011503000c89210410b12401e03122030040350819101c460b604c04000c40c41e1034130a402400159040140c0c40513100e503c0c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225224856 1250 225223606 225223627
    0x90908160507090e0f07090e0a0c0f14040902280806010816050d05030a0503070909050f090106060c03050301030209060d12110106060306030f0b0a060906140f060703020601030f0602 80
    0x6a028400454280c0d0000030100000503c9214501c000000d01000d003a0000790842e909030380d000c80b4000c8011882da181d002016400c1c082041c40142507100558150341c87c0c0c0e40034800041c0e8003a101e2100c600c0d1041051088074501842650101c0e41d000b070400b240d0080c0c810580a0980300400380211150100102007801e0303004021440c0207289060081c50072807a0401403221050141c3d00840c0034a602d020240300195000c0240c0355402410701e4003903142c0d0380b91441200d49000991001d50064980400d014000152401444c070130390280d402071080756586c0000310b810710018200640024001c0c001800107107041d0310403942000303004150500801458940c0d00746018101030190214004041d01b2000e07010038041c0c0c00c018803c83c2002c2141c6417850b1210841242c0800000b840310b1fa84000041000403140c0c40640900340c0c400007003000c40e0700d64440030104041110308a1040301003003802c51aa00d003050032148020b41c95409400c0b580d01c9d56807942d51103d0151130898401f40c0038070000010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225226106 1250 225224856 225224887
    0x30f23030f131707030b07090b071406090c0d0f050c1512070c0221010f0c020c0102010510052407290f07051602040e01060906170102040f090908 64
    0x500c1e0250907aa0794800c0450388900001c1a81e1040f500c4820281c040b07082e248001c20002d007200e40000302007945548004084805141e02e41286040c1100401c402c801e00503500d4003403002c81149021201c16441e12034800da51a21045102541705d041b46a803440021041c6a801032061b20610440e98185103c3c80090762502891801041c0341d040400d9002c403084101b0805500f007081420504503085194000c580c02d60b180d01c8103a035480764114910144030900b50311807100801001340801c40608034020003925040c12441880c0150b00344400f0500c03241219060314200c5100505128036040c182d40c00491085011175070540088060000001013040404200100030901500c001e80c8810000c004e20320510140030780520220344000c12162030b401004a41c05090390a8900503032880c1d41c40018050081c40c05507121b65420311000240c1021141c202e03a080e110b00f041058490308810651600302d008910a040142e4038090302080803840ba03501100815000c7c041c2c1c41d1500d0805501c0f0940c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225227356 1250 225226106 225226117
    0x10050a02150a0e16050619170a0606031d070e0405031201080307020a06172e080c1203070309050d032d020105060303090108040b060d1203050405100204030f2303 71
    0x20010f8a075150521410414440190680da4411145290350300b0000825544d008034401d8010062070301075196541d50250b2070041030589010350710000340c54002030a2002d82098890100400d041410b0f4841040020740041ca03121118001031002c186003451a26000c00050800e071b480c0c0c001002582100c226105015020b08000c0008641e644510b10600141d000c0c203502000405c5421442c0340c40400c44850110340100010507090300d203504801203123100c20703018440340c6000d4103078480000707004001042c00c0141c10f41c12200100741c00c00e0310780c40a449218008000300041c03110710060141d0716000d280000894001c1c0780203062000503030b40424000041902800e0305805841e0b9180710540e09000d01035202e002a0081c505003100c0d840041c01d4101e000e070000b8841d400280016a864a480703c2a001c5203411800c10f80d482103108001400a14043d1001d5410b40110740c900d1060348910b0088404407548052040b600070066202c08001c408200712450003401c0100d14010b0300581000a8074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225228606 1250 225227356 225227371
    0x3050405030a05011401060c081b072102031c0215090c0a09020c012906030604020c07060921030f0f0c020a0603061e0e1807090606081e0610050a0215 66
    0x10f00c10b400000e8200c17041005a0042c4104910001d00400198541c0160b4401810b40a12014911000f903c1107080024079045035107808004009040203018800f04001d001d030003502918080e4091900c441d90310710074500e50001684c00040a8050b078404000465806400c1d0001c0e00c8405040d07600017000c0d100340354408540b2a801050074a090030080c400c00c83c007113400318510311015000c4194680180050b01020b803007080c000c00040c40c16251501251094840041907440554035140064a540c4840c060400d81018050b00307900e000f40d0085c4071945498254442d4001c0020010003224698054103013201080020b250920068882d00700400c0a890b0755140414581d0070100044408444940480c5011608400030400e08421200360350b081410002c0c00700780b002c0300038011480c1100720352083c4000703460040006201a84003210398040c2c41e1004054041c003032305a1666171600803d0382c20303030760008414401144183c080d10040c03070950400c0c010354002007043c1d180c5548441c0110b8020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225229856 1250 225228606 225228611
    0x3020703020607030b0f0f04021204140d020d05030126071725030209071103030109051501020309010e060c28051c020706030906180f020405060a030312050403050405030a0501 77
    0x1604054040c882c0c00c0d8468103070714003001040326101c00030707a00050042d10640500000210f02c5415241c0350100c40b54194001e140f480c69040901e8881541d080b0a4940c6005000344440b000804d0720202d002e00c881060703955011b0440e42000750300c0c01c012902c035607101040343c0010307a5640e204006101c190010324401204041714068160000e007020266145034003020045043e0f10300c17016100d82088203494050301e440440381d803086816a400d8807102044882c620000c40001fa2081d80d030b4200a01c1460b0051040c0758244800005a94070300070f403100580400c00c3c00680a01605200d0090007076500d011088030240880e42c03480e0202c04000311049406203100170204003c0c800c0802c144587d0340e81100f45981c0f000c4d442c81c5c0081d10303403100b80148800c05844114000a22030590001c00c00c41a03002282c1620312203525040720001c01034607040340a9030a150009503d85844a00c080450f5055224600350070500f20714038004140051080301401400d00001c40c49480c10400310076024881c0c2c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225231106 1250 225229856 225229867
    0x90b1c0f0e06070e0117070315140a050904020d0f110d050618210a03022b050105040204051003050c04081204030c080c06040303030c090503030f12060402030c03070f1b030302 77
    0x10300d0030b000c00201500140250306100a840380d9200b413244001103548104001140c440c808114050980e0300c404a03400e02c01010040b07208640da84042080e0a002c45080b00e00079560014003080c0b200880340030794807211740034841005c01c1070990090b0010307204240919002004000040a00c4803000044d42d4a6101c1c0040200041e01d50100c030f00c01144a0009090f0316a4480e4501f0b181007032031000100080000c80c4c0104418041d4065520703007484280600c003c403c1711421850000540500c285603503081400011345810b09108550513a039000e056150100c1e05100260b000d49409051122403500401c0000f0390a1000d1224162802195500c59a2189141410743d4145683c1d0000045a0803c51084400e42e5844003181d003100d9046c2404503070720004800583d2a940340d039000341e0305800300188800c04850150000c0130103041e0010003084d107403503240030301c0200d000840c5c004558503400c101040d8980c0c02140786401c995210304d0103529900250980d00f60b8810124800c41c0466000310b0b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225232356 1250 225231106 225231131
    0x1b02070e0c03060d050a080a03020315010f092d0603020909070306050102070302010e0d0c0609150509030c09060312070308040308011d07050d1d0c0a05090106090b1c0f 74
    0x44009025008200300309003000c0315401124400985624401c40342c400035042082000c5c04569080c58000b019252100940100500079500c00c6031160302c00382d0f004c031101c5400e600600c3c034a18084001c0d0b99a0a140c0d00308034036001d04120050885401c90714041940e20b0980032810711074060b00d40f0340e81c05078480e060b040c18800155000b80204040c5420940103001a07640092101c0c2101e409281030502070798841c1c0400e0000d1510040075103420320009011410a800059010031600301c42d42c0501102541c001c1103640e401102100b60345500402003000c00d0380342c0100c0c069004400101130b18071006100c5c80400742588280821408503006000700014550006502030042080b280a111080580f88500040000081c049001d0203000320b048950880594011900800214065248440c10f25083c9560f08150290f0600c40c10b60f901000ca0b05080c81c8500a04881aa498038640c003402c080001c81142c200d03c8000b0110707019240488403d01c01c0d0700031000c2201c030b00000090208040030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225233606 1250 225232356 225232363
    0x13090204140a0e0712180f121701121e05014b02190c020909030f03012c0103030c06050106050306030307081b0a03020f010c0903110904060f1b02 64
    0x10403441c811242d604042000c50081c1012641c45441840e00006080c0708507200c100600303c0d04000c61003c00c4d51381c2c0602c00c00403888004040c1e94028540240701a910b00411581c0c0742c01c0c0202c20b00744400c4600100040090513140b440244d10a00c10368003441103102e00000b5005400c2000d480d9a074441404600c0d0403207504c03005d481240c864100d25000b28403000741d400311441d04c18583e07500325110851407911691650540d45680705003142c003000000e003400024106410004187e00c5420305a01003031030b01e07800104031a000e1900320080d50850b0f1a004914654034011260a40c2171202c4041c480c00141038120102e0285100c0d480b041c0310b5100c0b40c184103045441c16001803051001c104280001980d0000981e04443e81c0803844659922151b0b554080c441c80e0000311000502c5006613082c00c054000c14004040c04400300204001c0c0d04040046510030304600c13003d8082654844e10a120b4101112541c0d84035008a4010a0301c0c203e24100303000321000a400210454002c400c07424a881d41031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225234856 1250 225233606 225233639
    0x50904020321041a0702150306040b03030d0f1b08060108040303060333090305040b0f0d0204080f16030b013003020c100507110609120334050604060f0213090204 71
    0x113039440e4201507666000c11613030005076030f2200c40c4000201c0007425641d1a5009032440b4a0f024050320740714800c002162016001003100404010b04080010843d104003010500c1c903500c60307590b0010207440304801529445000b41090b010151070f0000840441c961684c000039914041c10840a001800039280304a56808603e600c409400c05030000d010a41c02401d0f18240c80c2c43c0700c40c917583d070105904a10300e64030500d6005000e40b4008078001489101c0490394503200c0e8541010713980c891030703004030086106c0801c1c00001e1150100700010300c03118041c44041c00c0200310f81d0500344032030f20840401007200100c000302100143e10164030320041341004400c1c0300f00c1000c9814110b003000216590103445600320b44056000e4140440da202c030569486a801c5600000d82d4140c0b50394440c40707841000340003d070b4a0b00301000740540b892a1030651001411504242d04031000e03013226159030707560708094403884e00500d100344d800388400f00782ca503c1040903100502c29880c0c0181d465241610188000000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225236106 1250 225234856 225234899
    0x213060e0315060603070c171209070b07120504080f0d1e05030a150e0a0f0c05070f1407050a060c0c0f0f0306020307230307080609090705090402032104 67
    0x72207210a0500e400381500b682154048501e10f407240e03103880e42200e100c01d80c1d80010345031107035288400040b101907c0c0146042d0074058a440c01d40e0f550180d0642d682d0046100342a2614800c10401021495200044141500c0d074640300385016550f607006403500401e0300c280d0f8240d4004400419046400142c000c9201c0e0442081ca03d00661303499000d88240001090b136051680c4840498260f0318003c7c823800041c0c039114001c040b0780d05058040b0030003494146944540c040c035041000e00c646005030141c2c3c0e222a0f01403035030b140c0d507016035a582400103016150366100d4818035901081e9551000c01040c0501070076500e00303402800c01e00741040365a1599200040001c40858140800d1036801c004200362500000051b039a0b0711140400c40300000c1000c00b08a1301c09040000e100c505408500560042425603580e08450310740004010100c2c805445075000c90740481c10400607420308040050f0300500040542c1c0d900751070100791070b080081d14203000802000c009001c0c0440c030b96900701840c4a004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225237356 1250 225236106 225236113
    0x1020d05060910050d0606030501060b030414121602031203150103050a092102030c160e0907060801090f06030b151e10030b19060504090c0309020312030c0d0213060e03 74
    0xb0060f002c080d0440c0140241c41c096a8074031035403003d120040d04203078001d603032140c002c0240d9569040d4038040c0f80c0040e541120305844440e902244800b000070752070300c40c1070806145480c1c50702c41016081d078080342e00802c9030180100c1382d4481c0042c0d000c03030247d88a803050034019030840381014001000c41324002c00140d0300318038102c0542c3c041500020040700d0a440c11503982070240c8103070426407440c0030380f807810041485070300b60b42d40c034402d00303600e441003102c0c1c520b6111000d07a25140900381c0c83e41d842d80113038800100f04400401c000000354014400c14200c076100010b2507a03c0c1e41ba40b2040c100c0417154450303141c4500c0769024080c2400c0181c51b03610b45035030641c501e03041c0c907030000501060142d01d06a41013584407018603c4940d140e150100610703c0d180e00104006589280203485a0020301c100624686450f040300300f10b5009015400026900034050141380c2c001c8540c01c041e50b00050304841e070002c41403000a217043c80c40c0c4010506024200802d418003803410301c1c000e0884014034001c038003030740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225238606 1250 225237356 225237361
    0x7031820040e070b07031e120c030212150a03020d1109010b030411191203020a0c170307021003060e0a060503010c0f020d030905030c070b04360902010504050d0501020d050609 77
    0x102c0105000040d22000c2502c0ba544a80a060454250f650720b00f224590090350320500301620b4000a4003002800402c2c424420914140b0080c1c0403802071501440050403442c0c00200358000300200c0745080d450041ca0381040135101d4020540502ea0385008a44c001110a842c4c41549003230500e007801004540d180c0d8aca5403516a03540d640c60301c40c200d40e40b07000300344901400c5c40e1141003000ca8070207040b192122041c40790b25400c0c02562060804015241c8103c40740b8041061540400d0881c005151440154a450115424084407058144401c0201656807201064000b141003001e0b0081101c9d0b200460380c1d50030b15041508480000704000103208064001904540c0c0109818007450b000c0e090005905010b030501906520031565000320601030031102003200810140680b050320050320003045115414113091440181d0560003440101020001c01150f13a003035004121000e01c189003290420350b03582e0100d942031004000c101d81c030741d4010130841d034884985e00c0784030751040c0d080740e0901190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225239856 1250 225238606 225238631
    0x3010b090c070318050612150a050f06030c090405101a1305040f0f150303020c03030f030c0a1b060609140118110f030108060f100b030a050703182004 66
    0x34031407074000030305002c0015080080c14104149010003080003030070659589140d00a0303221f80000448400310a010b8140d0322602604206001c4c409594014141040f4403031741004006042d04000d081c199410010004450240c68a01495000b50701e000002000d05040024a9402c1070004071030102081090240d000f0025504100c0b10803140b041d6800500f258460350300300c02410b0510717680d25140e07080084014144207a011035408581c0250300307481d181400b0004240e10303403240002c3c10515150038008a410300c0516030040402c440c2c0c0d800d104050f41010644441c00c1e5203100c10030b030b4440d030799000704000342e00c424051161840a4503041d9002581450a0180002c41160a45807019502c840c0c00d10500e20032001c6420104031042031546030b41e5a2255155101d134100c5451f4500900b00c0003003060030003080b082d402920410303c006421581d404042c0001040c00403d441c08242e180c010540c81400e81300480b000c41c0f4000c4e455004844810008203118aa203c0f8005025614003542c25900c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225241106 1250 225239856 225239881
    0x301050109060813140f0703081b1515010c1203050414031306080702070b0d0605010225120201171e060a0506030406020703090510020105042306070804081309060503010b09 76
    0x14140e0041c200005d0300464145107141c00c030b0b0b42110038401e10400c0070100c24031400c1d03c007030034048910842c01d080707241451a030507407180b004400c00b01c0113400300030200d0100c52191000503040780b418581400c0d24052b640300d0030940b40d0301103104004039507660144002c0c000040114003090303080500642c03401580480b01c0c00d80c5801882018104400180485c003210b100b48000c000801148220300d403514414002300000b00828400c00f8050b202c0e20355450114141d401130641c468280700055520b05180c00780d48548d000d00000120f040005000c5500b21031700940d220140a03031862500c8241d1528642c55420300104098481842452462801c2101e0f503140822280e10550001e00507072641080d00c0c0a58002007660031a55001070fa2004950002c0d03415404144030382c2c081c48007a050401003c4550034041c0e0620554081e541041e80011401402007242c142c0161142d10014a800d440040f8100414210303003100640e603444450421081ca001d005184020000b103843d10070a080c05000000b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225242356 1250 225241106 225241141
    0x3050709030f0b100f08010b2407170409020307020c180603070315020d0905150a05010b0a08041a130203100e07051516060c0314061003020c0106030609050303010501090608 76
    0x32682c0f00c08002034000c28400c41040c000c0001d00300c100546a03d501c03449010346550210300303004601d480080c9c00c4014a41c070b511100710040408082ca0403545880c0ca03501052001c9403051701c0c0f0800c0000007029a403500c0151320604261340603007001d82c00402040903070155500b210950015400c00e000440c1d82c082001000c9a6000000030314214800c1403100c040e006200300740222900d4084020140500825030002002e070120300e420195807858126001c503802030082480e00c50003441290841c40c01442c41d0340c3c015001d21040406626444115890ba400032181810032803101c18802c0110300301041184d01c0314214820501410f00300c505599a650b542d4420b2034814ce041e03508102101a4a5080760240080d504074410001d94074140040a00305842030340001900d0081c08607484180401010702490000b0052030500036800401c6019400649440c5140c0d503039a00004000340d503034460440021312a1014580304d44c54080003414a0003030340e01c400140005202005801241c4500c0f902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225243606 1250 225242356 225242363
    0x70605090f010c0e060c01090b01060305011508040c030303050a02090a03080c0d0e0f100c0602030a1e0209090a02090111030c070602010506030610051519111204051e030a0b130303050709030f 84
    0xd403a10585c00380140940000000038242703903441d000101301140d15410a0341650142c2c820340d41e650604400480d072658049a015245c0e02d0041c0051000a111750000c41d0080c2518030094188080100007030b103d00884c0d40b04a03500c0400142220b0b001e1801e0050500510041c14500491901000400e0424406065840c815030386090407511090041d0390b000b81c0d06402400440d224908410f00300b00801c0d030b07114100000c030301c0b904c00c11040520307500899640007000b070900ba41607140d514400d030284d080402070038140084012003241030075040001d4041c5040040007000303003924001004c2d01b15a009002c15000e50454400c21095a140c407802c5021204151140b984100c9059407040c107500030303054641110040c90b038400e0000c5d0b40c061f22041d0210158401c0d540395116030074109085204500c1100d0f0080c0e083d03580f15840058001807084008006829510480104c0d41c0302840c0c2e100c221050034a6006084050382419418071800781d01c0f000e1400d040c0c103800c0c10b5896401d0445580742005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225244856 1250 225243606 225243619
    0x110304180509031b06060415061205071412011401090807060c021528080915060d060e060a0b090c030c070203010b0306090705041a01270b070605090f010c0e 69
    0x455040b4104101c40713900038400c500b016026614400301d03890300341c2960600e21071801c0810754a02d50080e81c0450f0300301c03200358039082c00709041740c0341c0030f03000d020028102414000c2411200c1300350021003006048011401000701c0d001d6052148890429842c140c4490401c0120f0a0030311222800017210720030703160b4034104100024803510004402030555074440100e88004103003030b240c400e20348018120076021101c1c2c0441030200702000701c501c82c0b41143c0c1e40c81103900c1290044007081d204c1e08007940058002e801c0990900300398403210b0980d0340200d4803135415804002082480c4840340b04003c010305d411211511107003444104840705010140021811000010351340c011580d0950111007410809030940300a4030304080c8940d06c980301d40c40303075074007490808000760410300c1442c10718410040140c545056101d081c095881261014800030107041c00c40315400b00c0c10807100340160004034820030780800c413881d149001a040c400288121a07041c0c0c10169044a0140c1000340ba865002d01500e21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225246106 1250 225244856 225244861
    0x6070602041a04030201020613020109060f110a0317070201090b0105010e1c05010209040b180718082e0b010f110106050a0801090b07020609072312010b011103041805 73
    0x4000d2040741c0c010680d0402007500d850110303070b0600150080f80c1c000d800703552403a038681034039090107a40c10b80001d0000e41040d105208a84c011020301070161020714111032800160301c04d03149004414032094005c07810b040800340b61000c8015120f0340c40800e45c80203210456080e030302c0c0c454180c410b0042c2070600040196020480d25200e40060428040421116500f4402c0c20464000c0d0f2045070703903500607420569241600c2c10f00c6414a10310b003c3c420044602e0303503120f0104949280403d141c80300c9003110f1450000346031004000e449940008a07200b540107a14061f00f10307000c110305102181e01039060134450380301d0382e03000001c6500310b2840d0b061143c51800f0303d0000300d004240b290080d5500099421011841c00d2055000d0a1100c0c0b09490030221500c4084040c2e81d82c80c011281422203a10460050040071504a00702e10b62030600103d034032030314071b681d030008420380740080e2041043d84d0340c0c00c1c0402c0f083d0381c4080c40c00e28030310524010b1450541840b41c0b03603902e0001450f90401d0340703865001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225247356 1250 225246106 225246113
    0x106050906090d0f15020903030403060b0409021f0801050d080d0f020d0c02060f010803070b04080a031b050c101a060903030702100c050606011704030804140f0706120203010b04050607 81
    0x4584080d0b00040503121040600d140c1201040310079001075400c00c1d00502a082060742610880d880204001d0045052500c0c698800b40601810f03000c468003d078a0315031032401a1101034400e299480d001c18803851480c0710580060661a050348882d22404011076550040703003a1404a039000c00d038880e008900d101180d903484001c2c0c8648841012020721704004024001c0e1b0120381c0320300a20f038000303508210342d03178a81180d0f50320301600f24064041c02440d000700d000203030300d4001800b80d41c03000e0902144841e240b4001207101c2c140c420119010500002c1e17211000360040c03041003068000100100280071b1000b144012100341d80700d241e406800e00142c180c2180d0b86c01c1080e1072201d40e000f04141c42c01c00320054010800c0b42d83c0801141c442c0b003080301084041d03029404003038502c0b0303014000106503074540e14111840030003d00207569003425404440c04d03550742448190f840c0c281060040080342e1610030300611030540e0585155407244184018005801290100d03000c4a00494002d522042c5905 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225248606 1250 225247356 225247369
    0x32909040f020a06030204080f01020f03011e0b0f07020405070309110607020d1b060906080112020d060b03010f1d06010302130e032506050a02130b1803030d06030b010b1201060509 79
    0x303940600f410100040c0d0316415001841600d25500650f41044c03407a011060071703802441940014810184014400c4007003402400800d2008400c0c00798081d0360ba0040f000b9203030711803080c0034540040081c241080d410716004c1ca5410030054078042090310010744600c0c0d609183c050b0044c1c843e4000094420035076489140e070040590300041003c0d503004001e60294a0401c0318400c44012940c405000200140501541812170b0030014075040e003000d85500708075290700424412180c442d80c440f008101030b2024072500c4141980d2840020720340d0300c0708040058020407424013005030780c84100103100581381c1c05159904084007001c041420300c0141200b13400c0d030103800f903800c170303d4020040d40720440341c0e001c2c2d10032030818020b4008004507141c0406000c140e1041064182c0165110725040000042a0740107010a81889110000a103002d00000b0b00b103910500e40500001c1e1625014020700c000f400e442030044c946800020310340421a50841d003000f40c14400e0005001004c144080f5944424 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225249856 1250 225248606 225248633
    0x504060c050c1506011107260d05040b091c0f0204180201050d02160b0403020a120801230102030c01020d020304020f0607050607030905071a130e01050109170c040509060703290904 79
    0xc0b030690301c0040d102e8030010b0070a210507260008c403c24070b030700c02c855040021446804140041e60764900e02030501440c1030541c0e101e26915a0021031102a0140104141ca0070007a4107100742d43e02ca035143c442c1e004000584602c80311404040180c210b0b8500180e8108040340c40901036401d025840d1951040100100b910440000e02450140000c21080603808501044000c5c810329220754000d10000c41104c410109000e0f190050302a16288001e0080c004018082200140f04892505420780d50f02030980e0400c040741c50055401205000c210300c0e1801c03952410303c03015143c0c14100f24294440a99a850281501040c076a4441400341804020f1025001420310702460031030310304004d000c042d0390341e10028460748448040e141c046180400b40c0c140c0703812200140e4500d5011410f0030041e80c013041186280303000600c03801e019a00030707840c0d602400e440b40c009500500400d152002010781a210100108024101e00c02494900e041584100a5680400381c440c0200b03680e507403501d10801400c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225251106 1250 225249856 225249887
    0x210b1009020a02030a170f0c0310081c090b07030e2e0f1710050402130810020901020d09210f0f08310330030504060c050c150601 57
    0xb403003620454000004000c07105442d614a00c201503c09503d03c01c80c01e00750303603061040b8000800318031015903000286410407100c051150303101d0380c1e0f07000c04c1d440c00102280d0050b17100421010202040e0708042d400c402051000360103450508690383c020309001130700055900c501c0c04010386001d074040c01d0101040c01d800000d01150018850300c00038141c000340c0d01c0118002600c84000750150030f80b46000f01d003d1115008800180c1c0c0c01c3c42c003040080e40240c81031865100717043c14000340180e010881ea410209030000010394071000f99000904007154284e0100a200585c00300300f0031140801484540295105070a10f030300c400ca460041111f400020029003500078140b001c10030310050308000e008040d080365100c01448101c00310b400c005000fa980c840d0000202d0314041002c01c0c1c0030928001c00f40440c407038519103039560000300c8180980d81e058503800260346030104004c02c4014440c059a001041c02d00d2400d205100ca030142d594011101002071a61203400401e40ca41d0040c034014807c2c140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225252356 1250 225251106 225251111
    0x412150e060a0e0c03062d04080306180702060c0a0302070506281802040e0f0f100b011b140c040204080f010c110714031c030506010306210b1009 64
    0x14040d5181d541e080141c420080003841c0c0602810700380d00000f8042031049001d4090081c503036031468000c5880c1005002103880001c2030205513071501c05000807a105510540320640c482c2449018000c40d00c0b82005071000010801c401d0111054001070026401507070b09080c1c1d56104008082107001e4000c1140080c542d00c942000c1c4000502c0515416403844c5940800303030003040ea6941594140ca54682050308540f00c110700d4100941400d400c0948044000400c0300c1801e4141c5800c0c9251003110740304482980c001e03140f4081d0040c1301b0b0062030b005880074038003049140488000306072151821240100b618081484095540c00d007403003461000d000c0100119140c9546020403a102d5910303841d82d0486e035181c0000440035600171035840c071070040c0b031500810030141000520042240710158040e070621074660a032a0201d80f02e100300900c10602e644c040740f4ad080120014040e55074075000410400c01d94210030306071944a00003840d00ba80c000b40741c4805900c94051703182c440d0310103810010740b0303e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225253606 1250 225252356 225252371
    0x50919110d0c020d0f0509010507020321032d010501030e010f050c070302060c0a051210030b07030e0c0109080d0f0c051204030c09060503030405060a02030c06010602012f041215 78
    0x281e090344050b00d5491030b40c09584044584000031169101a203900300e0100c0c03000c1c04868840d510940140088070701c0a03080300c4400d00900c0b01001d080003040d000c02c1c481d020000030841e030b01421001404a90710080b644c2e03040c191000d00d029494501c1401468101580c43d03400004612094012070561030010800300914180941c0c800400d84c045001940980326242c08a0100351100c4203d034506c8850342d40d820705000401305820402c007070240c06000c0a007101c0a0100c041050000d0300b9018080c1038400107141a0b20040050924000d000200e040c0101700300c081000301408a400c10303613843d0030316198440310b45407142900d1140300340740080c0c8148030f0f490008944a08210090050324000d084000c5045d40c0d0f40c0c0e016081d120240241c82d0190024001000103051181c01740441d40c0003801540e00f008150500a03281c880260b000000503074603001041401c480907000c00c1e112000c0114040000040c49002460324440e13803090f00e4004075180c0200c410f00400444180015002142c01d10519 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225254856 1250 225253606 225253627
    0x3030f26100915140d080f0406050d0b0f03150612071503270602071707120e040b010e0d08040b0d020310120b0a09080915070b0903030105091911 64
    0x1070a50141c411818506082c0d1a80f049101d24180122040320308048010404207060040e850501c4408980042c02030040354050112080a00060001a61103d4441c1210264201940c901e0b110160183d40e025544d01103c4c3c40120741c0b1121440e58840ba01c0c81ca0b1180070110790601052114584540106800071031650614002503984d00d01e60340c2c0c18003111a40d5204801c04e0455032407034100840003105840b000440d0780d005003070441e0041f40c1c00303100050220321500f415401001c084403049400c100c54401d40d5080701c3c07078445212040e14104003a03528480041c1c0b24100c2142020302c03401507010443c00700407a440889000e000f82e03504141e04c901400c078212020f90020390348100300600b400c0002c55000b840b0302d0703081d00c9150800c1c1d0101c0e040d101c4c128001e000b41200541902e200404101d114280c0c0c0f9201c2529966414100d8070560344c1810703051240c0046030140150102e900100010070880d80c070002003d800c501520700450400200900700c2004000040c060903043d103022542100300e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225256106 1250 225254856 225254881
    0xc1203040b04060e030d26041a070c0c06140d0b0d020607120e06090907030f060f0f0303031107020906090a090f060b240406050703022803140403030f26 67
    0x840c0700364106c401c0d00e0650441503d2480340c00c02000c3e088401164511403802d800d80a054001e8083d04a02c560110000740f54101044116074480110304010034407000c1104e1445008020a401e113030400001458155401e4148586002c88640503101c00d28401191b076a070080d40f40c441d50080c02a0359886061400000748000504044d0100b20000030303100003030403c0011500f499600601c001c1940d41d0304401034000b05540e6400008060b581c0c00c0c0828155000301da8140078004e651908070b6600c1c0f642c42e0042c10b407925416550040d010500078900141c9034011040c3d002a0112003490541d40c4134000c4400400044802402011207501d0940038808940d1000d800c40070191040d00141030750950302c03e5441d0f01c01c411055010310400007081040c0c421000f070400d1920a10560b4100c0300b0400d54030b1860b00000f52080400001d0820700c00030035820202c2c448818452403401802c0c903245403809445a0220140841030103003414154109100d4000c009001a20362030a206580c24124040c400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225257356 1250 225256106 225256127
    0x1e09030106320102061b0d05040311190b07050711130203090d0203130603090f060f1a040209010206070305090a020a03200a03030801290d0516020c03120c01060308030a0902030c10020c1203040b0406 87
    0xbc50040002c00000d80752081e69400301c0c3c0d60080103041040c4c03507040c400c071140c0e400351006564844801e014005e01e6660745001000f12039a01c8130143e22803c002c080b850500100040110556100700841080304c8030101c41d5200320b0340d040c240020242100d052111040900010007007041d8680003c00f03030f039a00c49a102d480b00b51150f0104885882c002010301040303104401c07140303015030f01c01c0340000c1da554480e80045510002003070a540380029181e000ca100c0c2081030b08100c40e04524851400f020750034083c00d420f42034100b10341c2018914615100500050310601aa00c84007500c1056034030220384005082c50026680c4600503903a407900540b1400620003038441145132246800240035413880001c0324601000014042c01481c00606511000c5910505c2d00501c0c03952143c2000010520b143c0c003461048079005000708c0ca40c6207d1041500b0320100c0b420451080460400e01e0903100c4c0e0000e11403610700e80c113030ba800c20401d014642c0285540a6603014002c0d0180018011851079031050b0100c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225258606 1250 225257356 225257387
    0x304090e0606010503040312050a0e0109030c050c03120403120e061c1109131a09010e0f280506010306090f020417030c031e09030106320102061b0d050403 68
    0x44075502c41200449480c801510050b0024920301da40699032000c036881550080840f81d40020680b1001b804282540d28031401900031404c209160814024107001a07884d0203c218050301003c00d40c01480031302405a0301014014504981080c1d4409018401040d2011002001c640d1138400c0c1b0400012000104141002801d060008030101e490300b01080e24800300c002003c002e0104402041c0d20b005050000c056010803030200c42942e0680c0f9442509806858240e01c0004c061905064004145038003a0030342001aa00d2070241e01d00920091803022140c18561020542c0d40ba80c1c4012405013203aa00300c0a901860311030f40501c0360106a004104030f800c081c01d146041c1c0d04038240c407030700c0740144030200d07400b07030810030041c1c019002180b200d8640f0424110f042e4100100c400210b821541c02d50088601d42d10307550840c42c2030a140f9458000f0500c45038403405e1800c0c240500003500d400002d01540f101d801c0a05020400d00c80b40c100751900303045220700820440c039140c1401014a02d030914100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225259856 1250 225258606 225258613
    0x608100203091b0f1201020d060801050612190f05240703060506040503070e060a03060c020a031e0215070c1b241d06040801021210050307030c0302060703110304090e 73
    0x21000d8440318001c10401800003481c44d84400c40d0b207070034003965401d01c07206580655400c01c8203400c00d900602c11803000d45241d030000141da1078000d003401070440f00540504059403043e040520101c000b0210120f82c40c0d801806402441e04924100749092010380c0d100c0801c4031180c0382c0c00c6a41985040d418814045030f03509100165451043c85401c0c0b040e8000c00360180c0103690103001c03455250010395080350024060b204207550b2621248119480c6064800c010380095540300141640900d03400b00001e034403411b480f11501e030700300302940e43c482d100d1460b035000368040b0000d030115000b038440c080009c0d000007408843c41140d89642c0d40898140c02000d080c0070003181768134405d1680540240c07600000b620340d1442c0209201c44203080307454843c0e183d5441074082101250910007800501004a1403031013038112801c0c032030307503803102d490040c0c015500035488118104040b17036010340010100da806944195490900d8241240d007101d85540c0c0744481d22002400040404d900d1740074046446403507054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225261106 1250 225259856 225259873
    0x20703030b1009051e1903030c0512030f0a05090316030801031703010f0e1f0602030d110c0d030e03040e010803030106020d02070e0411010210051503071d04080d060810020309 77
    0x5860304006406200c1d0400c48041650b41c0400351807007001d28017040180944081200080c4014141940d500114000b039003004801c01000310800030000580200010340d030441c9807000140d051a1801484065110b0b03c0b5004140d15000070320881d0182140f0003c452060b0145080103044208280700c00c941e02d00340c078450313020480a06c40079641680c5900c040e10303588030b00e0402010b440c41c2025003102580075031046d8158001c42c03083c3e6030f01d00500950300595218400314600c00d040324052001c986602200b0801e400c0c1d05c01010882901c11005414002981e1140f4144503203140525008004403105540000c148550004055412141503500300c1c0d51100740341800300e803204280e00c24550314041190210f00000c074800b01c2e003c6928418811038100c0090654070f4016038009680306038091040b0510301c01e16003001d100310700152410a1a2100c00b81e8031940f0344000c0c02c0000c2003d08001404516182d003600b032030f04040000e09000d412640f191440707000d100001d52082e030b4060010300c00d200c20b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225262356 1250 225261106 225261139
    0x5030303090706140f1201081b010905041517060f070c02090103030c060212070f030e030c03030a231e0a0c020601180209043608040302040b1201020703030b 69
    0x110303841002010080d1240628000342a0742c2c00c0480b0a1910145409004036a0012040406001c031542446082c00715945420f25050405044182107400b4103c00040100581d80090040003140d100343c90014000f40d400f001c1d00d181c001680c000190050414420200d014000100580114800264070b803854442000540c0c2d90009040c009412642080c01000801c2c05000001c2c95140100710161a0107002c981d009082101100c0140200700c1701c0c1520943c40394144906204255400e0056207400458285980c1d40d000042c0b40c120841d442e07448450555070070345102c18400c0c800c81c035521064180821000400751b5003034102e4614146200015903041c0c550302600c0308024440e00544000d074200550018140c8840130a04080c5800700000702e02600d0328030428204101c1c0c1e03007044154410300710100c15802c100c0a01d98004c0071400e011034000c18103101c111000c680e1304a8000a80100003400300d903100007280c034200c5031544081440402c3c140c01d50400000003e007128003a030089140d85 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225263606 1250 225262356 225262363
    0x30a0603080c0d0e1f1b0b07090f061110020c01020c0609030a2a020d140a08070203070b120a0b1305010b0304112209050705030d120608011e240f06090503 68
    0x420101da82c4090307105144820340078400e030440000d42c03e4006800c0000031f403681000e010090300c0d00000244d8080d02001030f100440505009441d007850305003104c010080026a48240a2021800342d84c0e000800318120f040075411180810401001e5039268a425000070351250130020180c8007184440b2444002d101e0040340040c445400610b44a0041081e03800b80407590807080400c40b0703100c442001040c2400d208002d09010284034111080d074903500b03407041c1802c0c205203510007822400280002074914408160380c95200544d004009800358800001440030480e485880708a140746c100045070307040c2050300841c403460003031213407191025510060107410201000180207100005c1004c404116182d088154903501070411a86070589400000f82041d144600b14404610184448000c10301c150103600c2c010981e64008000c0d00ca5192145003c400303c0c41d00780280360f0f554440c107a00368038007000e21102c04407415005d090b04c03a460340c0c000710040c0c0c0c00340600d01c0030420100300042d1901c0c001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225264856 1250 225263606 225263629
    0x51e060105040920040e01050a091103060618040501091707061401030b0606130801020406050702030601080d02120c031207030b240421060e0a062a05030a0603080c0d0e 74
    0x1201c5920840c1c0f452010101c0420804d00c16580309844546060b0511801d0003954000c041c1054000b4003001c035403600441019240d22518000d8000004000c0c941d901d219490243d51950120700c6283c0e5141c1c034200c0c0c01440b4030400204820701c08104c00008180c0100a05080c030b00c02c503000c1100721060f02c54131041c20340901c0300900010031200090701c170b8104003011b0580400032450342c08640d915400c400d030980e0816080500013410200c0c0b940d055143c1003001d81c2c0105607103006850b40100e8000c000351280941482e000301500c001403088c824501c204201da40c6021491054002400e2450f0020040c06110121038492440e9a044075000513100302000c0b1510200d0041919240c0303040007404441c000d0031800f440b000c620a503408042007180c0214119441200040c0c0302e0701c40d440c50009c0c2211048891070008801c000d10174803021341c0c2d000840f070b0f010a0340d05101d83c681d602c28881001800031908010105500460070a14041000616154451103030710344500c6140a04184544070001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225266106 1250 225264856 225264863
    0x5060411041a041d03030109020a03111608130e0f0a0c030e0604110102010b1302040320090609100f26030906340f020a06030203090a1707051e0601050409 68
    0x820745004554034160b40408030704c000c008164410340e4000010b040c1943c000340d1000c1e4000350000780c0c0004166140c8100b404058110f07000d641031501079120700c407803800104801000d000b00001e030f403543e541800304841d0060100c000b5454032468413103c07080c0094401d88803680820308100c030704044c03540640540314408507a1001013149a54035141c20341c415030701415182c1555070b130b0f0014100c0344d2100d07a05454202d1040c60007681d03c6145181048954400100e40083d0750081d800c10300d02541c0306103056410000855442996031110703088001c0002d00c80d4000d502c4402d04003400161520b400c40ba80c0b407070351080e011200103201d04199440d120b12440d640503038021010008116002c500c150320010242200b4924105080e80950181052440150a8a00b040140300c01c0c0110300c1c00141d244060300302c48c5019400c41c103080e400540d0f03030440c511005100b040320300501e1442000740415201c540d90408204c40c010b004824043d24280f404042d00070040c0100c0001040c5810f081c00342d02040340c0d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225267356 1250 225266106 225266141
    0x2181c0201051614030a0906090f0e04050106080f0a02090f06010f0507051009030915020a020a150e030109061401060f0815012c030d0e1c080d0203040506041104 71
    0x8403580116810380c0614250002a41c501c0403003c08100011664035001d881e15006650310f480c4101e010304000302e590722250070000507000600c441c0c1c8a06038148202d030725110750b884c0142c41d44d185c21405861b0a0b04185103510507000e42c7c0e140c500d00095a10501802034071540c81d107031252070038910020000c45110340402c03540503444240f41e00c15002003080600990903600d40c1c1c660702058a003681ca418078154000750302804213200d0b8020000603080d00c3c13a020700040c4100303115a4080749407580d40307100e11101d140100d0280200207000c0c0b02d40340c0c0c914000400804c1031540902e0104028100c8000156003501c43c4c00011414900840ca4061114420b441b180e45130341d80c03030160040441042560754100144c0f80250700030f10201c030f404a890080c845001d1410082c80a0605280404d418003140030000e0303164000e031803502c070305000313001111801c2400184803080b41024035183c818800035002d0301c3e100100b00003c1c014003103804c5000e030f403040d18000c0310040d02d0350800c03090361040320103042d2185 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225268606 1250 225267356 225267409
    0x7050304051002072103120506030a02010509030f120c060f130b06041e05010e1605180a050612060f011409010810080114090c01030618020310050a090218 68
    0xe0110602c80041d075982c0704807220541c840c3d100139906249010451070300c40511038003400300b50f04110305084412850000b04050320341840040d03515a000803000e41409000290511903440521102e110394080100311a61400b440c82c0203002a172003041c02c150540203510100f02d51109041c0d009000b690b0011041401d0301c0070b5290611007010240c122a40303d580c94a41c5290303102c0c551110b034280d00031058000780645c0740c03840740061003034000d00300c031030580451269842880d0400c00b0b580d013608500c1c52035002001c4610124501e156141c200c10350040006c62501d0301b01061a41080c460541502e00d036100348030340001034030f1000c185490b0004c001d9043c890040d1a5204030501c0b43d0210002840c0883e0f140d43e241d03110708440001c0401150707400603108001d000a0100440c0040d42d9081c40d04200c01c40c82c0400b04143c035007200c100e00100c560000041400c1c09200500c0b10082c1030020700c4d0346031003070751070308404006c0d4017160786c4901c01e02c1d4003401d0340c2451070210701a01c01006144ca01d403603c070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225269856 1250 225268606 225268609
    0x3060c030a090f050d020d020106061b08040b07200a05150a09090e0a050c181f0510110c0406030c210602030103050d140301080304090b121b0a0b0705030405 69
    0x50300024401d04050340d580849001040f440120603608a00072006071151030801c1c01d0013800c081601e603d22007075a04019007040354540c00030001d40018200c4200309100d00591600918a00c981c1c0d000030b5003600086240c40610101c0c0220ba0818007030781c401118004000f8040c8010720041c0c0c81070a500c43c01e55401c400c03100c940600140010355162901c22034070ba4555040f2021a80c060007c0f00341540218403180070000100184019083d04807604884103070b4038680c21021660041030303000381204ac9100004100550300c40c00000d403100070841c0d035454600540c01008520344a0b62400340344075868800601d403d141c4207500583c0d8004d80d80c5a005400c0951222407030341c080310900e441b07605018176903000c02c000748060343c040c501c94000380034495110540203118151010361001426005c01c010426400c00204980827a4540500890480d184000040c1285d0b5808a10341c3d0901844491129410740d8011844030083d00b142c24441e03007500c912001b8503a010310b84000b42254020402030010303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225271106 1250 225269856 225269881
    0x100501031a090a05060a0f080607050a0c0503160c0905090703120e0406030b06040506190603180218061201020403050303130c0510120b0405090c0d06061a09040605030105060306 78
    0x300c1d54216880841c000c0105100b2101103900c0b41445944000b8800700c3d29050001c20001c0880c115203140c0181022150350b203560002d031804052101c0050051400d50042c0488401c45030040107417600c500b03001e08140000c0c40c1c0d003031040703c40140c090030219100ca410305c20240078030610002010761f00e09607074581441e00300740080b4206100031032440310782c26950f40c06024055440307a051340c1d42d2810140c06010986401414441c40b800c1c98680c03d400ea0038035050400200c070145e02d40440c450005098108060044940207500118841c200b402e40c0d03600582c0050080c80291101c070030108039203100500305c2c0240d00006284c0d1304100085800500400d0b481b0200902804034045c3c0d090355600054140f940c1c825864011507040c0640d00010241481440c5003400251030038082460005e03251511001004c070500d1003441c00d4940c0100b070010680c4103e02400c102d400c2c004072842030484c440420b40050f80c61038840d90800001003140e06043c003915000340400b4004000a4440d01e0340c4048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225272356 1250 225271106 225271121
    0x108030318030c07061d0114072004022107050309070e060307082a010503061003050a110c0c030f0a0b0106050304140106030803180a050606040e0a141c02010510050103 74
    0x240c8820700c03004400340d03414014280200707280c0c1c0f112080b0304000583c00c1810303034030706e03520078148000108081617800b0b0000846903500c0e80050100319101c115140210b02d01442c020054015102140b4020340c078003014814901895144010040c0340e40f0007104484c3c0340320031034144105810500c001c015030840c0020503a003204c0000d0a440941d03403928101c03032803e071940107070187e00305c0c010240c0100c03000c5524282e00c80c0300e02031070401d18500c2d0182c08581ea820801c84508e041503503880c00988103404070b0740010502d01000d03628503918042c407501a944c4105030382800d8404e00611481c0c1100c2c4070300055000743c070b6900440065560707190a000b52529000100182d418082c11500702038038980c01e00c00c02c00618460b00840f900c9040c805c1407980c1001460162110707e80c00300003a607020a500143c0c459205404680c0070801d05070200c4c01d5420404040001014920b61030815100c8100214000d904840005400304910303558103800ca00b6203100341c400c105160714056041c8001d502c6a0806ea0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225273606 1250 225272356 225272401
    0x506041b120b040b0306040c0f080a080a0f020a170a120203042a0803041e120f02040213051309050111031e060612070905041118040216050307060903030501090501080303 75
    0x804c030500c01c4c0480d06211045500300d0b010030151800f0300030b00642c1030140c0c01601d9200d0081012080b2540da011007445102c0000091001c00020b04088034802c125103441a90b1008003a81d00380c042c00340f0340780143c06c00040000443c0103019040f0540e11180700f079905c90354010010800b42d03c40c030010482c0396161848103a24105d0342c00310106039050b003040104020994008540d18000440c400c2141010a80c0c00c000b4907100240f110402103001100002c603080c2d0100c400580c1d600d0380d540001e55904031544696041444041d4480004400e07911070141503024400a012428401c0a1000c09100450b2901c100741c10681c00c003000b01d50189692030340020060400c03403600c803003100c940b80c01c03810468400002070708490050020742443d020b0040381c0412000041d05104c06e1780030402d0314903003004086002e15404691400881d0a01080b02c00690b080341c113403582d42519081c80805800a110280c01103400d14000042c5001d01d0700c141c41c100c6d807204014500b0b5850304200a00c5400b10740d15143d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225274856 1250 225273606 225273611
    0x60708040e0f04060518060a050a020d0c020c09070905030717030d050a0b181009051b0c060a051501090302010c14071412010203060102031c0f0606030506041b120b04 73
    0x1c94060341c4a0205401256521260025442c051900a09a0718010a80e00c0b480c2903400520340308001c0000d8944e00002030007804074003641c44100f004000e0050f101e01440072800c20f48003107046500800d25184090003500e02208a0343c410302c1c1a904220203201c0d554041c1c1c000383e8100036108030318602c6c10103030240320181c0307243c1000d00ca0300c0001d41e20103940c4c2d405110b40d00c0f101c1d41041d1800340000b0911080318481c80d165440d00c1c14408400c1c404500c00c0d60000b03620f83c03000035005200100c00303040d00101c0480031034503905040ca1081e51807500321207190000b0b1400010801d40d0220303d080040840050307541c031440c1420341e0700448001c0b040b103e0807500c440103118444c2c034a8100b88100c0015002d05d40640000003101003c04c115003c0100000c0f106074410405d1000c03699003c000c48102c1d01c00c19100c1d039840b01c04a91000000d1444006148100d4035110340400c00940c1600800e020b00001c607410721542c070302000c01b2510f15075090306a8001c141c1100e000070010b01c00340c103d046103a0006000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225276106 1250 225274856 225274859
    0x30201020412150b100f0f0e060301030c0810021305150d0606031b0509030d050c0709050106030203010906140904060e0f06010902300403120b040e0109030f030908040506070804 78
    0x41050b4011061021903004400c101d00540c00c000078400d000c2c0c0d00300c084403a000c00c1319440d100a0078201c0001e2541c410090280980000076005004200c10010b000d0003450740d0350395030705004003200200c0c024001523009008010100d20041d000344c40703c00e002c20360b18a0f0b120f89000c0030481e01400c140c080303105c9254144010240358141d84a014010305075504c000c203c040c04150140130404040841e074082c40801d212f000300035140080ca031103026101e41400c41d030368055459040e03d03000c2c040e44050103540c105400407070942e90680145040382d000c18024007820340c41c0c60040582d540180c03030540e040032a8000160100e4116001031810260420545608016146e049810000260801600241c000494010a2910020710442400240744070364014040442c54401c01601070405800c100e040b54113030700200519800317000540f03c018400c000b030180c031030091400380c0a40c24059001c2820800c031030b00f44a009004401d006584800d4241c54942448100442c54101d0300040c3c5040c10309000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225277356 1250 225276106 225276119
    0x40b030c1b010e0c13020f0301030609060b1903030905120627030703180e01061d0f120d0305090c130f0e24060301090f06180206030a0c0305090a020d0308040302010204 74
    0x542c3d1044420100a01806001e0f541804118009240c0da1100d05204101e00004110050248c0c1d05503a800703103004c59603001071b08107000900074080c4526880f40750b030186001820440001103049034429151503404555560800c62021429500659182c000600041c890324120f1051140100401480241c64941d60310f0b45285400a0400700d000c5a42c00407490f0350781150411880041400784100b50456050030030081103980050040c1c0a80040581c0400041e91600300c0760b510b104001c0c0a102010304082a455a2010656800c0b000f03e403422021554070800400c20201c00b950142c810020110710218640040140c0c0308a151101e940c0e4240e4001c85c00709100d11401d920b462803105102d4031411b002c4071141e1002426040c0f09a1400c010140001c0c400910801d5440d0007110000300d1961600310340c04130541046000394030100c00010080c80d40f2469010754004110ba640c100110f50710702c0382650359008028006980f04100030181000248900b40309070782b017407203403001502f0103070f43c0c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225278606 1250 225277356 225277361
    0x313050703060606051c0903020a0221100209010f09030b1b070c0915090606020d030b1201090b07021506090f180307030c0b0a0b010e270a0b090903040b030c1b01 71
    0x108141c0024000082d64006d4040000c01e00040704000f003010008000c0aa9020f0754528a101c0000d0140026078261042200e2581c5a4050281072000741c2d0000d150b0105a00000d601220704c3e507010400f505500da02e0710344160300300c0041e00c2d40306040c94510b460340813054110584d1400c0300085c4080400c50040003505502c20040180004c1001091a510302114800044080d800064150f450014200061a4002800721000c207090900050030718580010a5500d403185040c141c05600b0110701d40100000c8085881c8075880c19429604825141e82c2401c0840909a0744a540004810040745c141c02540103203980060703090548041c0fa02060101c0d87c00c640043c0f00a4000c50080442e610901a40501030f50b40a40300b11402c1041140784c200103400240d148100354050100550020341900714a540d4490303164842c1050141031a000e0f111401030b0042003c064083c41d24200401c0c400030002040e207080c1d4030210008c40c1555920780b601e8030f050308120080705518200501d1a0f98038002032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225279856 1250 225278606 225278609
    0x9060616141509030409050a0608011b030b040c090b0a0309051606021516030b04060801060b130b04060516050114040308070206070806030705010806271905060603130507030606 78
    0x46441c21088204820618148881d4281d4030301c0044500040140050001c8200c9041d5201b0200020b51515507080071070003030060341c2084406601c0c120700c000c1120140400000400c04555090240c0808041404141c80001d54401c0100f9450b0000340014500d40000c0c05e4100014900040c88140c5511850301d80100d034a142144844c010801303001440e414070602c6044d00340d0380702801142c184400c041c02c80b07044070703004a800c040e91203521008aaa45402400050504800901050380c03100d0f843d103065032144500140c215402e035130020713095124105580442c2d402c1e8075518207040078444002ea0b044141e500855655580d01d441306055440284c040780070354000e0f9103075040340c9044000070b45860400b80202c07003880750700e1080000380d9900141c0e100c15a403003807812644640741c08000c5030481d50f00b04012050301c807054160710010b46001401c0c910541805001c0c1d01c00301e80302d9443d40c00302c07001540e01b550468003c01c0007841d400c88424900ac8071611034411110040e03525203820b0102d8566 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 225281106 1250 225279856 225279863
    0x40b060f031006120603020a030f0203070801020a18050f0f0d140105070e0f030f0d03020c0c03061503150c0d0209012c041406030a060e16061218050c09060616 70
    0x7010b4003440700da9844580c0e440704a01c440d03010031025003160000380240751107110040040340401040800c545040c4580360060105200a546031403501c5e5020b4400d149605020401c1703050054005070a20340314602c0c0940400182036020720440c6281030003007402072200151000e040884518a00840920850341704042030341c2c1c3c00700e00481d80820041040070701c0313403130358447d910260310034043c0c0030007040d100f00a208a090043c0c0d110001501103083c03080c140101036250103030000b0050310b100a0380c2d0120003a10121305035640e185c070400450311030385000e452003015440140000c215406d1181d00800030200305041c280e001e000035000381003080d0380e04c1002d905404421031001110381030a00810f66011580020034102e464000003090707a1302c000120141a00b9102c2c1c0c542c2116080502c14030a08484d03d441c91024281c41da80d0250040d07103496140c0b8501807030035803a500500782d1051350200042d40306010b8a50142031104016401d403010b400254031050801041c0c24010007030034030703400c1c0520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 225282356 1250 225281106 225281131
    0xe0714120c0405120d0801060f02190f260901030207080909180d2c0409080304080c060c0c0a15020d060305070806070e18040c1d06130c0509040b060f03 67
    0xd140a22204c01540600240c543c2d0020348441c8103150400b0000c0d06540d11441c0804030044070302c004902e0102d24100d021800c0c00c6100d83c44c010300800c3c522007815a030142541d0300300003062800d1070f4982c60206284528400051001c48070540c46500102411030081240c5414494400001900d94005071441400800c40509046415806208041e54032080e400d040c1190900181401002e65024010702d0203183c000c1e2121582c1e60b5035a000b0201990400d8030070b0740342d00d400e00d4405466408000d5900300743c4034001c00142c0c03012070103044802e04060a40600f8040f00650759102801c010103141d0a040368080c05825103550315445040020b43c0503038014031081d4a0109c01508084020341010200031014000c41060380b1007030550306540401c000c0a504640c0e4a041c861301c0042590042c1002c1c10200803400c40c0c80d00010358003809030b841110000b10300c040208141c022035100c3d80c40100400c07002c0c00b91001d01e140a9210483e40380340a001c003840c2a155806441d000e91007252007450051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 225283606 1250 225282356 225282359
    0x10309080c0d300e010608031c150b0403030c140d1d06040501080103080307030e0307030306050f0d210513031209120807060b010509031605011106010e0714120c04 72
    0x5a03c0030f540d100251202c1042c3c0003061050b03002001071900c00b10340040a0f13840d600c0f40d10483e5001d6010328001c6c4041021b90b80c482000441a602c514010451601c1c5e0070f0518984004485158009600f10f40a842c4018609441c0da5000c0d1646203640380705541e52002c160b0360010a0000344046198032000750798107101c4451042d05585074118450328035019040c14441440140d800c5000541580e800508407a03c0b175a40f10030840103003800d60b4850250340408542c0e9000c06416030030400544404860000d61300c502003041c0f00c04540c41c6080a81542d441002800c20348050b8201070707011701c0305032801e64036086018112181c071040781e61044810510350240207852a80c022840300280009840c0c880d41c4403501c1e21811043e0142e144040c08155403030750741400da42c1c0104103d0f59000005001c0d140380760b00124843c03078002070901c24107000c2041015038241c00741010036814180c4a9407030011b1425102c00808581070400040f800119a80c200040c0d620030a40d81c005178440d80e440d1000e04e45d101e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 225284856 1250 225283606 225283633
    0x1e060f09060b0405031e0307050106060315090902180a090f05030c0708160302090604140a0b0a080a021f142b0204080604150b12100e07081209010309080c 68
    0x440381c69028401680c42404280550345c0c010400000b9003c861150b07899a5032903800c1d02c0d041d480740303d200510a40c40c2840c0059040e805400c1805941400d125143e40c0d0303a030354000380f0155135100b81c00a61142c0701c01c0c003207103040c003041646540005411400096030005941c40418011911600351559400800d004580e041c0400184000c0c0040d54040e21048480301c00f0b02da162002d500000b80316166880005142c0d032500d6005019a2b994006100104e00301151910020140414654098069a031001c19580c80c0058a0a0700960107490342d00e1901015480b0f41c00c040c400c1c401d080402207804800c0e142a03183e81c000c0c14625103034450f4085491020950f8060401034107071449101030050004000c0c0c1100450b10700c0d13000390482391842d0364248820003032005043d103004d410352240c075103040c034205007100040c514800d0781024010040c001352100e05903566841413099120f103a00c0680c1c003d020074902c40c0034016241c010305010440d10300703650702c4014581040307021415581c0720101348000b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 225286106 1250 225284856 225284861
    0x51f03030507020f0a1a0d0b09180c151804020d0207050708070806070c080c0708070902090301050a090c061202092d0411030106031805010c020102070b090606060d1e060f09 76
    0x485004031800b08a1794035000741d2030520404125120010311020454401d2985680c1180020003001400c216403480d24003054000c6601c2c14a04c501306110b8010b010045090424a140c3c044204250340c0341084041c1c0c8400041030b001104040d00141c0a0010203010452400034000140c4900c000d0a0326906090940b441c14a0315445985168404001d111000c1d400141c101801d5800c141d81340ea41d140c040b1026403802d4001d81c0301000511401c4c100243e48859540681040782d4203e000748815110808208155a80a48050b0082c9611036041014601a40c08d190300384200300303409414940c0d030200160306c2c1c20340070140d0b64210b120b280c280c00f0b07045004800000c80d800112420499083d614440c00c44601050041105040c0d9035000c0c00ca070144100b001070499070b030000091100341d0a04400a01130340040004444009d0f001c00450703818940071425910400d8060216401d0048059082002e04460415250021080070020610000d2801740e40e000c0c003c60410080c80d9403420140408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 225287356 1250 225286106 225286129
    0x140d1415010f030b0d02091603060e010803040504150e0a0c0905091311030a05060103150e071a070309050607030e031b010212090301061d1e01051003051f0303050702 73
    0xa038808803400c004050b038100140210045840c500014020001d2010031426060000302943c00082d00041203600c49490ba0600340e4207003e40d4060000613505c2d4424482030100380920b04043e00280010300260610ba40001504400030740107020165565078041c1000300150303060850302d61601a048000c0350801010002844243c07200c18851801c810b05450002d4440c0000309030b04004a03506445560410038031640035002001c0d0381e60b650b908e10700345100c82000d10a01700c2c2c9904220703415124501c00f24004003112800c003030b0440300c0041c50880c1c00d216032102c9400c03800e0014070140411b281d140d543c054001944a84c841c4030380d0b007158008145ca801300c045d8446c086580d030451506960790313000c50f4080089840136440ca0303c0c3d40c011302c00a4050501c903000005211030515030821010030300c601460003080d084900c180c0d04903d4124501c0000070901404ea0880f5600344141c003141e10a5000c590302c42e065410405000c03401850b0f0701d501104c140d1080e8005500403c03580258504000b0411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 225288606 1250 225287356 225287371
    0x200c0312060a0605030f0a0204080f0102030a05010b0906030a02131805101a0f03130f050a031103030708010e04060f2c0a0c150c060606080702060f2203140d14 70
    0xb140792070004024260b11000388800804084007012400c6100ca54054070041c0599200341d850144034440902d00071b400071220380c10628100400028800500d070100d5030b00c85c2d4050030702451541d40c805004080d50001001441100da10f50000850344080780340800c3c0d07100c4200011559040040c82e41cac8003070402d03401590410700c0701c4c0440c08103450b0850460b070300065542c5e8405c0d201d0f95111407103004c2260040001c0c0513a012240700e8402c102c0c02059101c4d4079442616010710100140c8826903990000f00e03038000c003141ca8100140400b880d502d26050b44140f00b0311004c05d03441500341101c030523242c81c0080910084030140202c2e03280072414241d07041c0b61940c03000030204005a9180c508180f051446014201c02441c50a02c2c540d40c803807011040041e4110206200143ea075450003030100c1002c03180c4e20014001c0c940452108000500003a00071041680c200c02070924503040c3c200441032211048060010794241c0701c130428001700c0903004000441c0710019031404011014448042d00070040d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 225289856 1250 225288606 225288619
    0x5010c020f07062307060207050d02060403090909050322090b03030f0904050c1e090405070201050432060109020901110616030f0204050916200709200c031206 70
    0x749030030031001850304110340052070030101c40d0b0001a00007014100c1d40441001d002000584201880f000e50020702c2168480d108803019120740040407a26130100303450040000f407154038104050146d9401c84604a4061001e4038174040460b429450312401c4551414402d42020f041004107204c14421355603107140c1600514903021543c00d41000611801e40054804c56a410200c0c0c00d40b00e100d41921a0055500052072708031242040f6440745802c0400240c0c40b03a401c1c04002202a0f106004540c05103500039888028207207440c0c8172461508007401100941000e02050060a94007004007038020301200b02c0c01680c480a44000401d0504005500076141e4402820b1180d10700246001d041342181500d03001450420b8040144040d124540c0041c0d48280124248651824162655441c80780940c840da24211102c109144107c00719041c54581074000741401c00603101e040d040155402100403a6518428201d000c1440c9030300070320315410307456101240c0d807440300310700c0500c45410030302c1100d45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 225291106 1250 225289856 225289873
    0x1b010509010503190b12060402100e030c010e03250311041116080706020703020d12180602030c09090103140609010501050a1203090e150405010e04030507030f11100905010c02 77
    0x10b80035103c090602401031103840500c100c482d1440c0d01c400089040141090005080386d5811079565009517020380c4070744680c803403003400c2078064062800d0421000c0d003d460460740c0307900199114074500c40c3c03c58060140c451000d50a180c08001c0c02b01164541d000020341c0c80c1141056012800342d400c041380154603203000001e0241501c400c1d50710603040c910529091030500d2030301c0300d280e01510348001e000038004640b003070070960040703aa080001016526485a00202c42524050321071900115824039028507001c404504c0c01e800466201e02c0101c0441d14248404003ca402e600c000d078015109c400300e80044d0103000409020107600417100304001e00c59941042c0004100d91424440d14000e80c200c451035000301409052840001d14088000c1705580c90040103048203140c540346a80d1103203103894004651841c0f16043c49000b80d4055031180d081c845030f035031f09a1f440006a0dc00809100e0501600d4403070500400004e41d82009500b00840d5040c564900203082d00c40c110252410341d00710501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 225292356 1250 225291106 225291109
    0x10605030c03030415020f070b040509060a030b0c0906090901030302031909060905090406090c0e06030f0303040c03020613090e0a020405130f0803070512012301090e06060319020c1b010509 83
    0x40da41a101c05d65401000840481c1040c1c1c60b00c49081c04c049105d014014000584000e120080c0007240c60640707074011941d0700e60f010802c1542050000420011031140841c0e030a4007024045c0c641c2ca40701906403881d141e01a07001030b4220409a004600580c00090311001c10a80f0032500c10036a00182041d44013141000c8014040d00500d00401e4051034440001809014250f000003400a41119100100944468000d00000d004480c6e6134003d1041c24541c540905000040740d02ca00d802c1504400d21608681c01c104d40c81c0d11964560000c4855184003280e00f141c03500c511110810100001d102e2900b2034418001903980080500e0003071031480d0706080115414601c881c1c1410b6001aa540d0340c0c0c0c2c2e42c0d01065525001e0070601128031481e483c004107802200b002c0240514008861f581041d250181c01114902c1032400b980e0b890301d100300c0100c1c000e400d00b8000342d6082107200e00c146007650302101e007001c201c3c4c105600703003a1320b40d01074091401d8480150481d1403054800b80b82c66460034281c4070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 225293606 1250 225292356 225292363
    0x3120c0b0103061e020d05060a051012020703170108060a0501210210020f070b1b0304050105040306020903072d06020106080307021e031516050702130e01141305010605030c03 77
    0x2c00501415181c01c64450400c51082c8100c41c0304007480d10454071440c0c4c901c80c5070000c003000c03620381c1c0c000d07030304041d0105903031070040c0001a00320050f41d9045810001e11100f50080d42100c1800c41c1840f6100e1b0000b00300b0070069154a01038641d440003442c0300e14110005a05a4406a105144040c07503c50f000903540118040a0350315601614041a520a204800c80c90300e90b40168400c81405880400318900308100e0080c21468000318040c030070540c500000350380f680300d0341c460f050201c0e40030007040000440341d4018042c07a090050548507210381d00c04400b50031a070036803104282c0c0f981418504c004c3c094010145c40241c0102e10081152500b001c21803503991188640291080c01521200b1040c80c2c3e100c4050801032402806480c00e080c840c007441120480c0c1070b110100e0685880c40c2c1d010780c0b03a115030203440343d96800411440d001c0c0314040d5030b10018042110f03000d1f12552104018440120b610f000c0502803610590390815000d0345091090854140343c000c51f01c07940090300c0524150340c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 225294856 1250 225293606 225293609
    0xe190c03021e070c0e0c0406020f0312220c2606060306130f0204020a0c0c080c010f080c0d1b020114040b0c09130519050105010e1810050d05010603120c0b01 69
    0x482c1c80715512a4079050100c000c900661080b111400c0035010054a596050013074021510a6021100c0309140c0710210740c0c80c0d004900400b001c60100d140055500c03040000c1001000c507041950010f5030381d031911007800c07003111a00414819507100156113480062640e03410110034640e0301900c96411b015000a07200d01d405840128007540e0454140107110740360410411007a40240300715079403ca02c5c18082c00c440500e040a4031200f5541c0d10000d04548086035500400c80165100d1070001c03442e00007503a034070401a2400350501000c3c004040500644c3c4290000e03601075101d00c043c072603a10304000303080d601c1243c00c100808800f4004d1100184c3c0c480c1c0c84076044040601e0303842d141d40880c40854103000c91091050080703030418043c89082e80000480030408240038030306002c10380c1c1340c00046d80c402000d00c203c240c0052240e040c0ca45404060301e01e050300100c0d054004d08035259940300040510380420819100741c2d540d41d9081081015400b08404100b81b14202401403405079114850940c905 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 225296106 1250 225294856 225294907
    0xc0108090a150f1811041d0303010509130f050604051b01020a06020a050918040b070c030c0f021f0305010e13021c03021005150a0501360e190c0302 65
    0x6462903184030007011380200900038080f02401c200d81d11141007011031209601c02c981d0069207000320f0f405001480384898100c01c0701c080b00a624507480c02040c840700b001c00404e041e0508903244842400a000a044c03801b01030f000d82d004046c0e40c1030506106040c50404100003620700c1c0c400c0f13280042a41c01103501603019810980060b110014007505803502d107d000c0c000c9920031140307002c01147d8440c95500c60702442c02a54205481e5503a09010f4454080b19400580490f00101c031400000d120f11b50300b0505144064800e0ba410f000c0e1183d00500405401c0300311021a44481c018041103614002c85d645c00711590003001014449900410007060010940e91840c0540c6021740c414075008001140b8400082070b0100003900d002c0303c011092859040255204011001000900d07602c6040e580030722841c5500c1c043d0004808c1424070790390900d140c01070309101e5806000040c201c50a500c00b20b200d690385400c039002020600000c030089400681194050620602140c10380056100303510700704008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 225297356 1250 225296106 225296111
    0xb0a0608090a14160501080403050f09041b0509011106010510080a021303030c020102010510140d14060907050a0e0c040303030c0507140d180e0c0901051b0c0108090a15 74
    0x10344040d00d908242c0b141c80082d14a0140c0000000384240c0012400000042e8107581c50406031141c0045a426809640240000c2d406000760600b000051004001c2100010000a2079141070462412030b80a01d800768400320b540070420018039600b09000e130f0f40e600d4690014015a44c1000d0014403488100415401005600740005e48240034984c101c0d100e5171148020b50905641d60f01d40142410003c04080780194201408242c14189060b440d0f0240e558404581c640c0094036800d100b200702020000751038140c2c80c80030020100005000e41030141e01e0060142440c1402d00060003100340c0309905c801c03100d20802e41000b00000c1040162020359600d441e0101c1c00710301180d030864141c0102580909030a6a0114118462000086090224078551100200700c0015890007550f100284113004548480c3d20028800703402d2103000b0401030205052041c201021038202038200c0300020002c003100d80c13101034841650343c0c207c1c800c583c3c0310400d18002e09045140780e407a0030180c0d14121042040d2034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 225298606 1250 225297356 225297361
    0xa03150b0d0203040807051b01030c030e120d0204030c030c05040c0903030c0615030b10030605090307030e190b0f030703060e0405030703030c2007180608190206040902070f0210030b0a0608 83
    0x405007007111110340e0488108c8030b01c0346d02c2c0c0f484101495004130000c2d010914002e90005028001d0066045404070320001e023070048505004642558044040001035a50030000800050401b01c00d10004d5805411410941d6080c5002c0c401242c0104940c4001c0c03004101c010070000e41e00441d071400d0946d0200010458807100003210b08100c4141d00001e1450341484200709039800482d01150840b03000b14402c0c0441c1d00c1c0c0300103158403442103250190014419018030042030902c6c00301e846200001d0440b040c1804d41c1c80c120503035103800440c4d1015080c5000000d000324a54580103480140100c000403415904103507a40941c0c030b00c20200010241078644400c091034138081d2030ba1002a10300d007141182e03118600c0400c15107900780350080c00b42c0c506100008051800b00d0744110303c03e40395284000c140040300848049892040c8041c1286c0c460f000300030118142410740050001140704100700c003444401841041003076070b00382440314201850302c00306803a6070351842131510481d40c0500b426000c54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 225299856 1250 225298606 225298613
    0x503030c0f250515132a06020d02010b040612020907030f020c160806060a030803150402040303050405271302041d070602060a020c03040510230a03150b0d020304 71
    0xd0003000d00401d1040b182c906070910401c1e0860160505510a005640310300c01c150841004125003503c81407040707003030b900412000541d05034011841c0f10220f6100300aa9204004c07145111415822000040c0c0080a118000c60303024081c1030b803100e900315018000d4504003000c0403222038000d28041d2107010305801040c142c901a6200883e0003500d210255601d4104100eaa969001301420a0b090b801070b801c0005000c400114441d4050a0000d10314405a440d50b207442206410281c23805c00f1140e0080300c00746955407288010001144251500e6403a64680f400304960402980e00441000140e45c03048008075010345001d5900c0007524004042a8040d070011400070a8045d0003d9800a821805810640780005900e801c0322200d9084642560700c141400013139018001c0c0f11103050340f0601c8180a10328040184460703006161801c450001d8812400450441ca0425507c000d01c07c001805200660f060090740100300c2480c2d550300031649042c036000701e9441018203154506a0110206081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 225301106 1250 225299856 225299887
    0x1602011d0405010906140405010503060a02031e07200c010906030c0c15060e060102030c0307170c1501090b0a1a030c0f030702010501180c0c02010c0201200309030c030105040503030c 80
    0xd2060191041180d0f40e1034070000d0300100128090701685045d1892a030754540b4241c0240750607980c0183c06040326444201c400e401940020b000304002c801030a82070141400741e05001031007541103035211110410951549040341d5500b040010b190703003080c143e86580f66002042c040c121911442c1c0000c00b505414012140d1004070752000f0604161a0013a0340c0d80300d45900031134203a503452100b01c0c500e601c4440c01a03030741b07100b520820b040c15002800703414085807090096901d0640010300042c42c02c800d03050b442c0d051108c030f0030100c00f00241e00f0006000707544261080748038a00040da50b04120300e051100c2c019409a2071906440840800000203d9240300c0c070b070076100c0344900010925102d0801c3d50b80640a040b00340a0070000c0700310340d000f12003911810700818412500d1740d00c440300900d07602e40044603a01440785050341800404c0c03580c0d81441080d080d90903c1c80f415100a9501c804840c42054100042441ea2500c00d0707040c5000d00011800c04401c494224007250030442c2e550440e010741428 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 225302356 1250 225301106 225301157
    0xd150b0409080d050a0b1302070c1205030a0e062a070801020a090305060c0f070206180306010f0509010803041a0c0a06020d0f0509120a031a09070e090c160201 70
    0x20401d0908424604100303404000e041c1d00b00d4424414440d5943d081c40000c04c0b910391003229a07108880d1030960040d01c05650050107458024414900031544441081c2c071036070788050301214158000560b5019003a4400c00d6914009000c5582c58523000540910200d0700850305c552090702502c2e051302c203500003000c1125000030207001c002951a501c88072400740039417909100c01d4403503001d400c000580030b600300000c89010568507101c0074144005a001e20020b50401c00048403406c0502c051688250303410003103e4002c1c1076415403e607804e41841c050095009043c1d0003652198024003050054180c0641040b201c008007400c42034440d9240c154807407400b0035069014084520000c0c108030189026009070380d10b11404401403246490340310001d5601d60814110450100052101c03070360181c442e412044100d03410700c01c00035258411400044d4007801c00d86880000c540c1d01c81e25512076007080140301d41c0c4a0f084103107450602c00301074841c90203240c1c0c2d20b2009040040401c0180502d0411040782403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 225303606 1250 225302356 225302359
    0x5070e0f120a140d03020c0a0803071206180e03131a130e06010306060519080604060806130506160207060f03020d1d1006030c0e060301090213020a0305150d150b 71
    0x510303007201401e02120000600c020588280904d038098a8440d00078000ca40481e07440100030003090300c10303890703413041d9800c05811482000b011a900051100307060180001804034036401004031001504110102d179541d4141c0b2040c0c0c1c10510100e0601c40b24444808102d503a81c40d40614000c0035200104240d10500126100c1400a00c00c007182c1c43c0c0104040920440d4281c03805c002d003580300c2e00e080e1210b0140c0036803110b000280401c0101d4407403203460210b8105a01905c08070b40c4130340b150f500f00e0808404407202e40d184103c0324410741c01d1260400c40140c0111540340c0f040010441054020b45400c2640940380078000f89200c42e004041c80b990480d00046003060b01000b000301070440c0481c41c0b011214240060b80f089d8040429000321600c00c00088941c4103401c0c544141c548046511112001081240d040d541c1c1d00c3e40d80090307240c4003102040c8814010300107940340701c442d101030202d90016181200400055041c851140c849089203200541c01450460600b20441a890003400c1e21380544da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 225304856 1250 225303606 225303613
    0x60608030307020a030201050601050306061b01020c0f0a0b011e03030c050a200109090e031e07120c14070b09042c0a210e0d0303020c01020a0903110405070e0f12 71
    0x40b00358049041d5084038400e900900c000d44581e401101d80e80002d40e402544644200121408603002a40d20040032447e10009400c120448180909003806c2161f084400e4206075800010000305c00e1410380540f6440882254254015416102030320003800010f09103e12140c0e45024003c0c10850741038040d502c4444502803082e03040001c5215651128a140840c03800e0602040d11a04d42c0540e01c001c28442008600f0041d41c15104c0380c60020081301030744000350400810011880d940703c611801c01d402e8650000a50343c51910382104201c8500f803030a01d4104140c144690325041e0100c80e00c0041c22100450910318945508403440c071000da210a2460030340c082915071000120b0200e2001d4060041920099000b406805040745c40c8036074640000e031841883c0c00c403854106402d0003014081e107001420140c483c0070590032641722041d91808a06106c0040040200745003101031401800e071030038009810095070160001e00c1005a0030b00c41c004244c101009902c1d25210150071010b4036049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 225306106 1250 225304856 225304861
    0x304150603061e0e191703010602010506030717070909021207030b06040c020a050706050c030c030c030d0b01050c060a020306030316060c0306060207030309090906021b0d02071509030f0606080303 86
    0xc280103143e8040a00d101844102d0440c3e0b05024510a10942d04c2c005000780c0810b6144030f174403a10a40340300004413110460070341000c02c0c1c10030f20005540030b0a429000083c6600b00030003051f141a1048c0d01c008400c00b032007500c20900d5040400c4060440e0740fa950041191811031000a000107090301c0c8404a40c800c1010000030b120000c00814041c101c20f0f5410810795174651001c03a01c03084140d8003d80a9401040304110381c620420050903505440c10035241410301c5c448483c0d056a00c44100d610340f0340e102040e07001d500d00440c032565031122000d080041c504142c44490031b440786002041280000c0d400701c001607881d20300340103c81c01c0d12140d070001d0324001d015140c01c0005141e40300c61240002c0ca8800c01050b000c0c0002605010349401d621402d40c06484c4c03080355001b40c89060400ca03a840d4007170003c481c40b481d000d0070900c408002135001d02907030035801d10000c2c42c020b6164050b1700c0502c080d0415042958100d0f004a0070360390441c080c0080050207003030420262400d41e0144071280f100208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 225307356 1250 225306106 225306113
    0xd020705150c07020616030e030d0201060807150f080601090512100b0f01120213090912080a0b1509040603170c0d0804112403100f0e09120304150603 66
    0x1829040891aa9280c00d081d0b12918212040340c050350400079000349042042440581c8000d140c40b80c141d00c40c2c64040301044643c80840e050000c0034905001603034481d0000e005036441800243e020f04054002c0041409130080000c10f03001280641106109000340820160f074855100ea0f006000301800e601001100e03824442d43d0703520082c000d00304092034104a20342c40d1402d008480740b8100141d441034401510307540c0400c001d6208050390303140082c510600180c0205980100c20805008108100c150201960b01600d0114001c0c69844100d14100f00608980c0d40c8412441f200d4400e00e00c81a186e41c04d86000c50002c04040d04054100568103041d00b80c582410001860340c4207940054800c0001115001e982855041d6002010708a041e200032840d0708002c2c16000d410070004100918010741c0401c0c82105610a442e200b94600350b000b401c0c0703d180000342d803c60007010321082c15002443e01c0700004e6201c2811140e900c00540000010609000342c001414205100b13062081103526900e24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 225308606 1250 225307356 225307363
    0x1a0a0f0f0215010b12010f0503060708221101020607030603050615031f0902030708060702122b0c0906020a08090d03090801020a03021315140f1c0c110307050d140d020705 75
    0xc04440c0d288417100103e444030303109a12500312500580240125110444c0a8030315080081c4560805010341d40580c44c801444059111a0350040c0700603100881000e00081c2050070041000f801c0c141040801c100042001640c158410100c241d1b4000c5041030750b00003410000c0d407034822103483c0065074501880d00c00e142d0108445510031012a04181d94a0000c2d54440300c00b141e5000c0940c01450710754040710a008020402d80c0d0fa040a449010500006400243c41c0e1400c1c2c24800c02d42d5800e000c585003034000c1c8425010301090b000900d403011943d9500c404511034102810b005c0c1c200038500204150044810340050820417000350b4a6008001e0000c000f500405105200c00400103000181c0c03103480500c0708840203c80e03a900040401440d49425140d0014241c5011000b040010400000c1c0500ba100000c0710a414042628028104010400e0003502ea010031340c0d810400144001610006103a2035468040c141a0805401820000c001e40548106114501d0000441a04128020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 225309856 1250 225308606 225308617
    0x200114070b090712030801050f01050d020c0d08010f0f170a020a1d01061106150a12030302070203120301060f0c050c060a020303100b1614030f0c03041a0a0f0f0215010b 74
    0x30750480b514030340c1c0e0b0484d1200080c0603000c043c010401c400c00510450600c403c10080d03802042c1009450011081a10022644440240131884c0c00c044400202c880d8060b590314010a4a00c00c0000c1960034100a03000135080c6109403042801190751549040700140529100180c004184103061680d80c0c10400071004611f284201e000389660012130a24011711865004c1c010707103001403408e5031302c07503298040700c4074a08103190b031008021500050030f21036610490410b81c840c0d9005610385110388141858a41d08100001b442201800188030310355112a22110f41d00b8289840ca1680c2d500d801c25501300448014550340100002981c2015030350000011401aa0300c0650030304080d980f441650101e00400d12003502ca035489035588070108103d490606802c804039025240b030464076603602c0c0030b940c1c1302a07182026500040b8040040792510700d11070f403030f0116001d10703640f40101c0c0250042c0091060288542400b0540304071440851007003020070060408561400c140e561118003240070354004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 225311106 1250 225309856 225309871
    0x304121103090303162618010f20010e0607030605010e0f060708030a09050111031801050c0919150e01110105190504050345060d050601050d02040308071a04200114070b 74
    0x500b11f509182d5403140f800c1c0410050f55658107403c29040345941c820040507020380390465902c4420f9038080d24028450300740180d0060310001803452600740003401107101e24004500c24040054020040d032100e1040b541c0f00c0b58000c15081d0b6a81d10101800e0042c6920600544603600c4c2c55100315074000c98030000e42c042c501402c024941d8408600ca46800d81d0422500c019100e80288060350850900c00d840c881481101070a03084100d40300e95058907120252168440010001200000b140d42c00c4499820314452400080c0300b80d207040001c465000906200c5109043e0b0381d0400601032050900c151010118400b503c02201740e0200249480d43c0307200ca8080c1c0e50908007500310b40c00c0c00d041c020250010000a0940d50400b40460198001410700070f0280e8140441000014003a00b2144001d00245106e0f80c07942c0d072a0704040c24508040d061045621891821240034480401d40e0b00c1c0b0b0000c51003402d43d060b000d841700801d0040742c1282d04c25040c03e02624021402d44104141c04100901ca40780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 225312356 1250 225311106 225311137
    0x1c110304030b0f060a0e100510030f18060c08091f11030709030b01050604032414010306020c1e03070b060a0b040f0e061903031103040b03041211030903031626 70
    0x1128100c100b100081924007c6103506121020071044c24203d001056220740c60070300284001807120528181c600341114008400010984c1c002000403d104642000b24035240c404403a10303000620340e42d1544c613260311070300b44c5c04c01247c0070030303000d49a8000848445d0384405854583c1040f04c001741400800d03020072160b89500340004a618101041510110390700704540348103045c1c50703811200741c20380000320340c40e41c46455105d0301000a58007052903000b180314082c01030355201e4544240d814034816200e03100351101c4156002d618071f40000b00390389855400028460254980070000f813601011076024400038031010a0018405140c1c2d0310181c01c90780705000c2d044441c0d90705810004083c00740b450304810102100c80a0000c00d01c201490042c0c200c030613003124509900c80c0054503064008403801c40c0e18200303042c07030f42c0380c0e184d0f200c02c2c801440c018400c001c40c101140c40700001d0320790040c0c0d100c1d5041d054000d0700110510240c0310070805404680340e03010740c1c6a103c030148141154030200400140b540c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 225313606 1250 225312356 225312359
    0x207060e06060a1a071103010e0102030103210c080406110c1201020903150f131505040605070e030606221b0f021203061008091c201c110304030b0f060a 67
    0x103000c000d031310910a00010352131410106590322428505454a5580c066603100c115001c8400c092008501131409001c1c1c0307145186000e451070705151004102a400c02501c84248d0300000c030001c003990151041e038103143d0f4840c0c100790101c0c0c1c540b04407e0546070380011002c101586418065000340341c104025001e4a140340540803117100309000c1541c403102c03904415000070301d000c551900d40394403442c03045980e815200d243c0d58000741541c01c203403415a0b03490b90310014080700340d070480d0214503140010f8014102c0d40c0f600c903000032030004e50400c10130704060201030302a01c0000240d01860841c61049004140340400000080105801ca000b02001d481501480a412001c3c201035074468100100300c26009202c1070011241e40d40094000c80c454400c103000746003101000c0315a04400304065641c084801c06a49008c00561110045030450ba0044240c0b851007540100344a02c00b01c1e00ca0821401d68007000760018918441d80d0700140481e80c3c080c040c0600f0b240303014003082c020001152180186d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 225314856 1250 225313606 225313619
    0xf01110423061801050409050c09100206040510020a14040e0106020111180609040605041b090518010e060d020904030306052e0309020f060705010902040e010207050604150207060e06060a 82
    0x181c02610358070b40c1c480414041e8880c42c07034407041000b8050206141403402c040d582c001c100e0a0b070714180ca0320030131201c010810401c242001c00c41c5450b401001e100800440c209a150780b034640b1113480c011100305400042c284410345c0151491030328500c4680c00310b0340d6640d5903c1c0085802000f80500e900550800300c982030b48103a22000d03502e100f002a8101d54000b00410304100199200c104002d80050310307142c000610b81c0c1d541c400c40c2c2c945c5069542c1c01400304d00c802d50052280303206030421482403090701003184032954204d40e009e06480b561482640180c030340c100040d52135445200020350020404080000700344d03168202e00101e84050310808541c00f1000c1c045244159030719020583c044003800c0c4034801501c01c1d0024281180060700141a07152220085178550340411401d4400717a4407001044214141407007a40c0800542000850a081c0c0c165540c1e0b84801c0041e0001d4401a40c000000c408003240d1b80c100e80039180d12031820440104002c07042d03601d5210450380148204410000040c14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 225316106 1250 225314856 225314909
    0x1103060601020d050703090b04080a0201030506010206270c030d0527130f0905010f060602060a090b070f02030904020301032003210a0201090c14130c0c030806030f011104 75
    0xd450141c000d003c0c050742d2050200c890790060a41642041421032000800c0e90103140108003901c0c0d90000341c00640c82d140005000c1c0c1d040a0484e50465010740c04004c00450001d450008051950210b49002001c160016140142c0305002d20f0303242c007400c1406004243c100f0000d1401c41c0034000b481090700c1d41c20b20500c0c0000c684807c090b4208035600d9140003024400d07407040035010441600044c000b11a912060b00b114900c0c840c0c1d0304c0750750b0f4840c0d09100321a010031010b036000850400a104401c43c9030340d00f00507014058444828080c500c0c41d86c1d0103d03030092045e2422040040c00440d00d03517a50341003050b0460180844007012840c0022005010304000c50b02468442c002c070419404103c0399180c000b420b9000098880855589000c0800050000750300c3c0d00007800c50041204814000908000103024044180d5090500d82001505904c2e0003410558189815040010040d80c480011a05080d840c184070031165280c102c0d601414032901002d4429500309016804401c10389010011300f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 225317356 1250 225316106 225316111
    0x160507150e09061f050318071206050402060d1802100807020d0e190b0405040e070f0e04030323070e0607050c130608030f03040215030127060b0a020a110306 69
    0x45a00d01c0c10070040c2015512240c00400144c0082518281000704042d040400000c0100240000051040e11304080482c1138003c42d00b08084c0a41c1490f041043c04862180c820007803c0a0711800000c0c15540d030b0006803820241103840502c4041d03602010360911120b04401207208114487c0c41601a40c4100c000a2007030300340d500140412040c8039405e0711000d00b144e0351035910600000415000d501040f859400801e010a07210303440e5420201000b0994503041c180080c10760205101b040217030540c461500840d02d040d844042c040d1640d0404901601c120b40803040c00702c04511010401d81400d03050948107074026550002002d280340204600c520031242c000e4215441102e010794245420f400140c1003040355000081e846070340e0215181940c210380360403031140c90040304000c00d6040202c071604200801c174140d14078560414481110400b10030791180700c642081e0354030540d012000d17402100030b401c208031007548880c0300d824000e55810b41c140b4202d680c042c1c0d99004801a0800184050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 225318606 1250 225317356 225317399
    0x7020105031f121506060c03020d1d04061503051f0603110c0114040c05040c090b0a030f0216020f03030708030f040c051f03050f090d23160507 63
    0x900e1500c900341440314055070000c450003100700001c40083c2c006044907000304014030130200d1418186110300d40c00704444455000da001d000c1c1c00300220000a6010840d03c1c40c80190381440c80e134503c0c0c121840d102141c04001c0840c0c01034501040411302c040e408116105a405a650502c01d075031300d5001c403070030707420000718420310480030011309014943c06508004c0c020903001c10001e040c0381001440d0b600f91070380d411002d480d20b4050b00c02c0c0004c0c80108101e00015010980381442190310515000740a4a424403900940301d0000c103581207158440c1d04111100c201947c0300f5526000540382c524401155400201c1c860f10704808228154140030007504c0226400007a0b0600b1a0f440d050310008040f0000e004641c50020300401280075900c401040016400b1054104010721034407401500300c1d0b4000d0301c0a00142c00c060200981ca134000101c00900b1644c6140c00e04001c1c010b100c520041d5584110303482c1035800d001c200d9000141c8400e0324890100d004400f00e521196503590158400042940c1d02c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 225319856 1250 225318606 225318617
    0x10603060314070303093f0c12030203250609120e010318020d02180f0f070503060f19090e010f060f080307060504021305091506040c120c090806090a0201020d05070201 74
    0x4110404038841030308040400c02400c0b070300d005ca54000d4450000554000c0d00c0c203000700c2902d02c1041c0441c0310b041e0230140c0140c03411841c51b041c0341c4c0c60280d039900445d5a50300c100344054400315034154848a42c1d0100340e600100c107024082e8203203040542d1aa8240708400010b2405050070525842402221403c0c2c00400480303100419680074040408901c96090343c0250080007a40102061590080c4c480c1d101003000040604181950440045002e42420100304050060054964a40b080350b83c0b030050444001d00b100c022090301c8240643c2590050540310f00d0701045001c107600642010b4481e404040040040e0b0b500d90700461001d400030b00480400c0c0e071007440070000107461a4000390b001400141851545030310507070140c05880c421102a403081d0888007006480100e034108540d040281203400303100c2c038008150024039034958204038080d03541d01ca0703214140c0d43d4010213014000e44043c03070540e0f001d40707003603a442a555007084500320300620a0000300c6189910038825a0314166050792130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 225321106 1250 225319856 225319859
    0x6010e01091415162f01031d01060915080a0c060c02030312090a02150a020a03030216020a0b0309060c1204081e0307030b19030503030f040f02060301060306031407030309 75
    0x1e07003003881d00d042a941c000d0540d844007603031034803c10040c00c499404251848a854454508161705102986101060088030552408401c42c000300143c0c0d0500d00b0300e40056040000c030000e652074209028000d5165103030100120b40c4099582240e4886040c015110505c40e50307a030040c9a4503080440090a101e440d01c3d01840018410f02c40b0240060000317044034149080b01c80c0480d0024001c0d1800d4455500a136401411030030503184002d03103054103a01050400305140006500e591030040c000781011341c001290601c4420f001000e0313182c0c1d50080e1400f02103a0b250901e04069a2040c0c501048500c0381400240314580a24100d841d05040c42c18642007079203841e66110f4a41c0c0107003804140f0034048000b00881d44504002440c0700d03090f5a43c011481c00050001d10403840c42e611001c5040460000307040c4041203000048035003110341100c43e0b0b89580c0e544d00b480380c2c00b40241e50000350f01440c00400040c40301d5040e0001016640210000c1c8005400540710654400e09031000a01140721403c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 225322356 1250 225321106 225321119
    0x170c09010806270f030d06060305070e0a1e080105040b07140a0207260f060601030c0509240c07080a410708030c0d02010c0504060806060304030e030f100506010e0109 73
    0x100c001e40402a0340840301c1051803254040d01710b07042000c1d01c2c0b40b20782e81c80380108400c590501a0a03000011810b2211f58141401d0118060314400d00481128080c0e00b107080c4e607802047d03801d80c0001c0c03111300300800190409203080001003106030b40501c0018000c100005a1182d840c084030800440341e0020000c1e14a031000d40810148004000038403139900380b403400319220b41880200c1d8804403401c060101840d1400015080782d2404100c01d04101040c040000b085d01e6100449000001d80408005440000b04141d806403042444801c41da00440100081070f240000745043d02c076100307202120000c2c2c102082081c40c8034408241e407900001c42c00425803550805035800c03071680f852a0540b0045521110024519400031280b00419482a401d003a0103d07420320514800250030319280385403924140c1c00400000d005004248503400000100d401c041c09108284031112014040c0e51884c1d410380842a02c44160746581c00c3d1b810704120010307403150310842811b003e001e03050f142e06070300608050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 225323606 1250 225322356 225322411
    0x6090c0d0c120510031211070905130c0602160e070e010e0310060b03041b06090b09031c05121b070605040f050f03031b0304020a120c170c09010806 65
    0x1001c0740d0902076414602148031440e4059280f0803041000c0b03002205107503150407000c00c0a890300d908100b00c3c3c40140e4003841d1a01083e488100d600000d004100d5841d44880045041d038030000003012a062003a0000b4525004175003e0070108450251006035a9100170a001240041b10140e0020712603942c001001c2d8091035080b046408050203e0b50a84881c04010040b42c0c0143c01425180030040204410031501d915a0005007039180d84103c0b0040c074104025280c2d01c045c4c02070607512180403540391103a4a041004a00d087c4000c001c600b081810400b014120b640801c1c0008075a24944c400501803c070603223060360b03002c80441c035018a02201c54403410010040039008841d2007485040c0280451401c0094440300b107070450185d0f80d40c0c2040c2800004c440b100e081e260018070410303c01c10015030b940000760022101070f030aa08181c41d020f0300d8040303016000741d00404502c106c8500750400c88800011107640ba60000d656851040e43c84200640e5121000c940f510362489041d5061540481c20b071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 225324856 1250 225323606 225323621
    0x8030106080411041a0f0307030c03020d150c0c030e010903030e012706030203060913080405060a21150e060d140a0f030807080c1204110a120809030606090c0d 70
    0x8890043c00c600c05400041d0549541781548882100b0004142c905403800c4418a03070080c0c011801820154515503441e01704040b01c0c84003a01c180034080031380051080c0041c0d40d403941c40300b905003041914050f26001d0400c030305801e030950000e04d40f21004c80031035006282800135250142c81e80f0268070700ca00011500c2a181e103500081910030844e02040e2791000307106081c0500f00381d4401603100d1a10800b405107004001344401c00d5528411112001b00d866030089506039003050300c00d641d980780c00042c00d40d101102080f80b1000a026500c80d403030450784650110161015541c80301003400e42c0e0711010720800d1000d0392001e91040d20482c80000140c03410f030066040f0b101c96001d542032003240d030b142c1c00700d0210782d510180d011520300d40801c001303280e200070343d25804801c011402c2e00b49001865418070100c001000203052400450000b2443d0b6200100c1100802c42600c0d000e00840f80b615007480035420050b140340c0039200f41c2c801708c0c01c2450100c0320305129150042c0c0c6241040348079180f45000d41a00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 225326106 1250 225324856 225324863
    0xc0807020a05340b07061103010b190e1c03080903090a0902091203030106090302030709050411010807032711030c011403041104090f03080604052703040506070c170703080301060804 80
    0x20340f00ca4030700c2c124640344070200410301081c0300e60300d4543c0b0341084c205640c1c1d01021004584001c20046c00003020f8807080d5940d481285007010042011000c0585003901070003605135200d8014500700580100440d101c090f000d2003659008100d0329a0150243d49016a2401a6000e502d00d00300340560401a4050662124014010407140c100d403a001402c40e8801e8008a000814248041c015410108001030060a030f404c0c0030481450261203600c0c200540382000e0781084800c0b40441d8003030384030b50040e074030300e84107401001300d4001896514a5558005072085508101076080320900c0d29010400e00c5000da01038484c07010b40c04524640013807982c030040c001c59010780d503601080000e480f5441491450362080a40c10031001d4a400d004e030420340c00414040c030450800c0b04004ad10001246100918001c0c0d1141c07015205c600711401e4103501864110b20f0b0400e80100303206040c440d8443e902170880d11450300030b003407120f01c20384455100d41032070001a0074600c0802c0108001c920400406510500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 225327356 1250 225326106 225326173
    0x503060a0f060807030608030a08130609020405150a0e0106080106080702151306050a0603020f0402070201050c120304020a060e030a11061309020c0d17060420030a0c0807020a05 78
    0x3101c1c0c01c0e07141200003940002c40040c900d281046112a050b100d401d01901c1107100131410030202e12030040125500410010200d0360b0030094108001c0d503034004800155000b0014811407424014980d01540b507500400e02c034401240001584403a41c40704d0398103a524958915001d85e0900e00c0c00d030f48010000c0c04040462150240105101a181c0f100384d0107080c0c00c0c40042c5c039182240c10404107460020700004007007440c12000700016075450810003c14002683c0250300c40900d400103a1b024041c1c88000c200c140505082201c00952010003035118a10894600701010f031600c004449000c80c0000040e0103611000507070011441d484a04030340180000c22551070315818070440e0b00d80032419484810040c0d0041101d0304d1100b0140801061b201c4280741c171845040c0603220b00050240058040d501541d80c841c82e04103012615001e1145250180122503541d0900c20b000c5002170080c01000400a480030f004543c000b44003040c0502400d4200e0b00038000b40008604040c100046010754009018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 225328606 1250 225327356 225327359
    0x4020a0e0c2704050c0316030e03090d06050610080415021e0a080a0c0c030c06020d0213030803011401110a14070f0602010204090b0f0102030f1c0e0607021018030503060a 75
    0x1021440d00c0304a14036412a08164542c0024401aa54041d007039044c40705052082100b0000d660510f0f860a108034540440c690040c3e0380c20343e05610600000603000303000161000c0a001268128500819050722601000d2128842c200c419002c00e4400403c500031075420750081a1150b00a01010054443c03440d261180803001e0701010360000c0d120b407000c00d6881741046103006c9948102c4820342c1c0103060001c2c0c400c1d0180e034000c08d02c0044100061900d9408a148140030542d503054442000405030309640440d203e04003200c00d5082441000c2c9084040b80f1580000d510480c4030ba501180414000c00c10f480260b41e482e80741503103103030744902c444c4030740c074000605058130320301040007800980c0005075941d040903120402d0310440000301b80950320440c480d0031941d900004803420101c0411915071140c140b141d00540b881c2d1805051189503060281c44664075802260076805240e80d13800700c5403e50b50304282038050714080d0300045054444106c0f550702090051000b03541c00322000788182c02d4039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 225329856 1250 225328606 225328627
    0x2101e0203090109060b041503030c08121306061a0304080d09051f0e0c090c0309010605041a0103141005010c030513060201150806040521090d0302010c120504020a0e0c 74
    0x2a00220b9074091203a450b8104003003442400d01c508948000c003540c061190500b0051783da0b110390121b110040c200242d80d803d000c00d01007031005544520803c15032212030717814010000c04214448850035500185060300001b90f04035200101103844e94070a403601d0440c1c1d903130b131961401a0413100ea0301d0740d41e680782d008840004005001d019402c500c1c2c05d4880440c0501520701204490000307001031000e41c42140c41c080359035a0001d145130b10004031042980c3e242c1c2d80034603040c0035000c1a8403154000c1e091082413070a411100440c1d0b8030340142039030704011001c00e1092500c409002520150851038143e03200f03204552049030480103081c0242007042ca000070180018408581c207502000c0140d55448280728103140142c0300c01c004081010080c0703d103003044e80300c2540310316500504050107d400300d4542244d003003400540315000d80040c1003800c0b075940c50801034040d0404440148c000b0304d4a10700713130304844a1846040e0140390098181c1c4d1805091401c03140c4003010241444212080a20010201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 225331106 1250 225329856 225329861
    0x702220203011805060303190c080309010207110405061302090d0b0112030e100207050904030c140c040b0303042103030225291513020a080907050307050102101e 71
    0x560104040040c0e80b50314000040014030b8840c08548080f50812081c800301303603400016a100c020440e000280c00c01c007041016103141085503401442c1007800700030000d03042d0065000c1d04095024100405000d5032500400c4101e440c2110f1003644444110004403a13180355a002d4040480c020f014104040e01396100c800d01020241d00c100d603070782980801031040545c070020100840308103032003010b514454010065100c0446000d842d00541403900020b06140c0300c0c40300880e805810a2040714918001050282c41d02c000011481c0918102252000541000030440b0b00f16203034400c18a070700c00f180c05000070100c01071500035400c058091000072010000c1000000d00c80c690100301040d072100701e18040b0b5002207228601510300d84501140c01c80c00000f06401648032074041447c02c48413500900041c00c0045088031603d026101240352415140c00c9800c07d4010420401241c8039550780300205075640c81c850061500582041c00c0c0c050480300190449050420340c00ea52140f0f1240031243c0008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 225332356 1250 225331106 225331159
    0xf1134030804140603010f0b030403031e0203040203070509160806300d03052202030109080c010e060901090809010f2d0e0306010302010203090d060e0604080705071e06050702 77
    0x403005400201080390341515001071003d05810b942c241d0442d8501451856804060f1203a04a00c201c00000101018803e81c0001d40500c1c107800009110404c0d0401c060094004a90803400f03481030840200b0340d0301e0005d18544c403176143c01c0825960044510011101640d0107400c094200305219038840301c5080903180c1c0c1c141401d20f411441c044400c21301c0142c1c41c0000c0c11011a0604d4508028401ca10192601550614603405d001d41e1820070309101107070042880c418042d2007908041803840d42408190081021084407408507402d580b500c600090803100182d5004042003001c02c043c01a0354002c0d0440b05018689017400c1c3c038040d841c060000c144000305c0081081942c4150084e0140c00d411540203400c4c4041600208040d604650010b99644140124070348074a5100c440b50003088078540110048140035401d5950301d040604e03018049801c24141103d01c3d02840d840498858000e41c0700310480c602c1d140d000e10072640350002c15034140e0f20041041e604000340b0020403140041c1c441da080c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 225333606 1250 225332356 225332363
    0x606180310020c07090501080a03030b0105070b0a0b010f021f050705040e01090b1f080403050306041d0607020d08040b07080c0f130503070f05030a0228030501020a0f113403 76
    0x40e61014190f0341c0381d00b05003c0d6000100707840d24113001801034600c000741249255905040c0090010400c000503609030040c4480140051505010410341600d0707500210042c01e000e0b240c441181d885141c081ea10703a138009201803401c074002c42e14a4002c0f00c003900600c1d0480210b003482440c0a4a64403905030f8100c3c00d80001825680702d080b0705803a0300384008041020200c82502d0604e9a0812030000e085a90241000e410004084040348180d520b59000b107003034145502160403400c0058401e941ca40804030380e0000940a80e50821a05501403640180300b698081e04040c102d540300441038840c0c640140c9000740c1d51006100300c0410024150003017120003004c24078611500d03c1c0c02c01b0103261104070740119455103c0c90b18200000d840002d8005141541120800e070b0400510044052108036000000d0441c245480000309010040d030043c2000212a9a0240385000f211819030310740c0d6201c40c4c070714000d40c020648000c000c540440c040303042c4d0009544051a090b2010711010300280d1540068 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 225334856 1250 225333606 225333611
    0x50303030f15010503010608041704080d0801050418170711120609060a020c2d010507080a14061c11190906170a12020c030105100e06010809060606180310 68
    0x220410402e0b550414010200340380071491507050110052501c0005480282010400d06021003100c8900c0151000f800c01001100d568004005e0020981c401c02c3c80342c00d00a40c504685e42c540320001502800c2c21641196004005400d0a40d8908541c0e00c1404140d0704c140c45119003c2e01c81d6244504103903c0840d00c4000d11040c01c0c0b06c1851400c010002d80800e064920400c24112043c1000c90f142d4081007107030042c900e6a8070280d00307200c038103090202c8000c0c1551814003002075203908451054020f0801000410089840c103802c2040e41400b03442c01684401001500307021f01c03034988295001e0342d11400180120080e81400b061700ca00d8843c6085d400007140c200e0a108600b00e511518009008031907441c0b03003000300091301e15154001004081e20f5129031031015240315008100032140290050020403092421a401c005800c585000351588064040d010961642c4942440c5018074006000b51106441f0300081002980c0516540d074000510300c140d03214136a03001c4c44004185105014007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 225336106 1250 225334856 225334861
    0xe0601030506010e10031e090506010812120c0703050d0f020d0b010c0f0b0601020a051f230105040b0316180b0d080a230a02010e070515160c050303030f 67
    0x1405960000340054100100419044002d0380c400310110103910300c0e0f084c0062200e00420741952a000d600c014400d01f1800e1003464020400005034803412500100705940503000315a40400d400c0c482e01401910b03222002020035150f0402e0002884400e12a06042d4a4096030b00008030645d840d000b014111241d01040c03200351060385020ba50b150342000d04c0c02041400055076004d407603125481d0041c1030b44250f0f01c00200180d00030490501c68a41000403100702c401c00881a00f02c2c03407150014203583e01d00313240f080000c1c5510341e20807004200034903e104145078201001d120003411058075059041c40b0304444001204203842241e405005c2030404800101c05510a00d000c3c0c03012801d41d58050401d00c1c0004001c180d2880503034011400130300d00103600411010003851000b900d8418031301c81c4e05001500100040c1c05520101302c1e24001c2040c1c500440d903540401036005100c1c0000220a8420081201034241c410542110148a0960303a0811a10350011a14641040341c09418441e00d010a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 225337356 1250 225336106 225336109
    0x50105010303032f07060b03060108010e0d1d0405040203030d090f1e08040909061407021606020601080d1b0c061701230409051c0c06110f0714160e06 66
    0x180b03440358050b00605000140344400c030040c04c1d00f0844805842e12a003c04d40c6010042d841e048080c040707000038119496075841d44040d50003000501d03450401c5100d003001c01e6080b180a1b10300e00886c003900020304c03600700300f56105100140500070070490b07250101300302c004510381d201d00c03480c1b5400e0701074034407803c03070f036074580703040c03049017001c04080441040032044960010b070211048806650300540b01150580301464a030010781207107408269051052020844216800521102240d0b0402e1400e40c0c519928101030361160350a001d150781c90f800c00e210000b030481c042c070b4421210f100c03600040300070300e01c86440b02481c0e4401500300ba000034040040c140ba5100c001010240504504103045500c0d440c00c00c41d06641c0c0c050400101d0003079841e40b43c900c090000500440d42e8559510030103441100c0c2c802c10007400340c0141242100c0c6d4610700004c0c01189040032055507003040041460307515089007500c811291604150341d090b00d91048034220390900c40848031003030041c540d034110311505051050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 225338606 1250 225337356 225337361
    0x501021011030408160c0929150c0f1e150f0103030c020f030d030e070f0f032604030507031205120a020f07021903030201060b030408071e0f05010501030303 69
    0x45100c600741800801e01100200000301c83c1c00c540d00c9200035580d030240200c04540d5035165000035001216580b00050085416004011052155401c078010600318554801c0c0d11440600616080080340d00f0602100a0f40c7c0010000c02000408817283c411034039940318038108080c03200c010005044002d00b464004104401d40341c40741c07038400d07044841ca0300703098140080c2c50500c405002c2024198620055403500c002c00b00189002030107888480b50b8194024014024071480d03034081380b013400310020b50080d209000074260b4050f9020894100e01e181c0311120001c0a11050106c011460184542c21407012130040008600c15409441715600d103003000f07100c2c0100c01da041c03428001e04001442d4a0301c180c07504076501c090310200060b1501d4002640311068001c540c1c00a40160000c0f140c4d060b402c4007642c956041b64841e9000b0700c04551103d2032000280019600109504828402e170700001d01302a000340d06080900385070442240143d00c0394031102d54117210660700e5940d00c00042c0140743e89030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 225339856 1250 225338606 225338623
    0xc150a1a03060408090f0604051003050f09030a1707050c061503060f0c1603050408010f0203090c0a03120f170a1b02030306100c0203190b0a2306040c020703060e07050102 75
    0x11000342c9920b103400c0d2102d01080c89441e6680c1e02c00d110421090030a651484292005071801038202d1641c695190400342c01044241c4181150111403400599410f00c00400c40f40000b0030342c0d03508164003504a000151040e4054218024000140722411114108201d035500c541c80105e61305801c2400d034401e142c103211025101c1d46090f80b1000411954006d800215243c1035000070700b0f005107801c9030500b182c00380501d800c580000d50030000310740104141900a14040e0103107100f601d00907500b0b0800c00c20b280556101c0140f01c085100106840300c0d0280f000300d5110a15410320306c1d40342c02000180c400d90380e000c0315101d40711640e4110101c852100003000d1403070030403240025413075401e00d100007840342045030640c00104011044100210345051000c10f5141890400b40c076145891442c1003c03945400300e070065000c601d4140e00a40414440301d0401d00d010003001c1141c05a00d43c0c1e0180f001600c20000c0c031005510803400000001507040c442c5040d0217408901900419007040002814558034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 225341106 1250 225339856 225339859
    0x22090c0e040b16032009040e0303090318040219120e0d121401030302032b09060912030b060904020d0b19060e0108090d08090a0c140117090c01050c150a1a 68
    0x3024005074a10380d004240308a624034240c11036445040c1b000c0010050008c1c0641e074000c074003004c0140a8943e038000090580c1c4014030786407801c05c103072905c1804101c4c0940948400c3c50701d001c0403400d000600541c20041f204e00c502601161001c203450285203002044006440000c41d101c0151351403440c103105a01c005640c00c1d8503c2219459510000c1d41e034000c82507102200c44481818101da0009143c0c0924401481c0e8030503c810340c0380c0d040c01002805d0903881034070411460000007003600e21030700c00c4208007000200913908120400f8180002500014501021540c1d1a01024443e581390460812001078101d03050001504243c802080c01c00c070619140c0c140700210040c000d4034040450b615000001e80e141c2518146e8901000c20718002880002403ea050030703640c003040400841801d48007150085c1c071149003d00c40c4a07510381c0c40c0c0e036084031001c80315000362080240541c480c00041420080d181d0440d005080c010300d80741c41d001400e881404070503654440003480704500500c85d4054120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 225342356 1250 225341106 225341111
    0x120c06070909090b0a050604060801110912070810180501090c080c0d0308060d1122050c030c070b04151d0d0e0d06050717010305100b22090c0e040b1603 67
    0x1090340d50080c210400341810752611b4482c0e000070956140c0f588008020030081c80280544e02c03d419640c0402da0104820b42d026031030249418a0540300094400c084401c018010280201445030010080c00c00c03c0104404108403864940401e0f003d000b0301000c10300402c040c80300240b0f00300400b490010080c002d18010590309007014003182d08003400c207a00a509a940070206a140c2ca004846941486c2c480e6900042d0701c0040c41e02c0610121001504040b8000d080241d42c4410051464034002291914403480040102a000961030071000742c02611400c0780d00840c0b0b54030700d40070040e00c50401c20988448aa020441c405403010000100043c00c1418800042d801050100701030401221000d8003ca845070046840a44180b003503640c41c00030b0080c0103845507140d10f400e9898049442c1d4004203181060100ba62900d0080c03104210301c80c4080d6240c039819102c151100c05060680401c1e11f0114507a44001041c00d00c0c024038910851142071010700b1482d100da0302008006040302400100f61 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 225343606 1250 225342356 225342371
    0x415030f0e01200d0207120c0501181e0317010602031201120c031e080f0918010509011e0306020a030b10110a08030415060e01080c030f0601090e120c06070909 70
    0x4a600c0d807002d40043d03601c01e00039541c0600c846280081d100ba40f40c014000c018000480380c0c084e13482625411501d100300024400109a160044040ca410140c0503003660041e0000141030602e070203031000b425109003443c00c8000120881e60b00806c409901c45805600005030030541011403d18860151081071111000c0d03415549441e4010041070000400c00c468101b0b518510401c1c0d000740880c459400007542d581d4103500d50344130f142500901301050140354204029001c426146890394140d400261600405078078002c21541c1c801444030b4600ca502c504c507000400803c0680c0018044543e0548021401c1c0c1948000c3c0b00e00160f548000e201002035100200c200c104001c00c186071788541080c41e00d622a1254140305820f03052076480720140a1030443e0004030190300800030b50407508200186c44a20f04817405140e1503d00d5a00c085c005074210f034006001540041d445840c10819800498888219041c107401481d8400303801c0700e000303031701000401c14425807003075070fa1010302404601400001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 225344856 1250 225343606 225343631
    0x608030915040e010b0c100207080909160806040c030905060406050708060d050706030c05040b03130b01080a05030301030609080c030d0209040b011d010f0509060a0e090a02131a0415030f0e01 84
    0x1000c0c10301840e85c0c01440018a4000f001c010030505541e81d0350400215620061441c00d550a58481d24145000c0d0701c8070302c00130310601c405103403516010f080c41e20746a00ca581c907070040000400c1d41e00820b00a042c0c1c4d07440301780e01144003001107a00c140d1140d8030020341ca0820b960043d01105005044038460f05254400c0c1e00001d4011a103081290b010b814003040000c18200180c0756405550400300301c43d031022040103119164107020800f80c030300030b41c010f00b00350340c03190460342c0c071040000c80250203039200308010130019885a011003a600d02800725035040020300562141580d10065001504a8001c42c1a00ca5882c0504c1080c101207000d00b8014804107803488001c440c81d84a02c20386050118284800d02e1440c00f0f4001c4520f101401444036607105c18450340505900c1c660014140104ea00500140500c035035442211380e0a480c440070051007900e44080a02000070181c13840150320814040040c6182083c4440d4000c00425180850710850003010501240e01c13502403405240c4c1040c0255819 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 225346106 1250 225344856 225344879
    0x30c030c21390602070503090d080d0e010209010c020f120a0803070801240e0d05010606021f05150907111509060a06060915020f07030602120a050105010e09040312060803091504 78
    0x30f41d00000160310340c55a0700b030150540c002c0e03072031081c1c100f890354410700c0c1040007000003440c6013480c00004000d0010b8448003a4200d000d04040240031070700c0300001c14050301c1d1451910ba58244001e252500715084010802e0422004190454080708003006020645411203030107030141c95107282c1c22000d1401509050800f426801c0c408041c401d04165020682d02c031614503401182e0000020f000c41552002e001b5501da40340c190b06503034000b1400507581326200324001d9034018455980360070340042c0c04c44100b1014841c0070b4100b0050005081d03040306400d4047c03003071900c1c600844c619403800c0e103010071740c03181003800c02840da42505252201c01d00985801030780d04820b0f2055030701c1000700c071040c02c2405c0e0f2801d04001140c0080d8854680c002080004c980c00402e0008507500c0c48800d01c0e242c803442304040d40c000b0b0080c540410741031144910f0314102032541c42e42c414028500390031110400c408410864403581c014001c15040003075004c079203050521740d1100140079014121f14151520884841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 225347356 1250 225346106 225346217
    0x30f010b0102100203090109020d0b1509164b0e280503030304060b010f1805040f1407020c030f1b0607020303040b04090b1005030103030c030c21 64
    0x103d01e079001c0003180300c0c0242584107151499020b85525840003640c1000c0213820707021111204882c100c504c5408890030100e4840b4040c0302501c5c0e0003180d4050700139096459500314003107032080341c40440d810b458070014450201220a501c0f02d900a240400c420041d0044040104030010302990314060340c9075031241e044100d8541101c0c0da05d025641010b0a505040da010f9138060f960500c008010300045c081154401c178041c0800340c0394580e104101c0c40c0143ca4140c5034101003445003549181c100f2180c1171542000c1c103410302214000031400189080c14003941402d0b107001c40181d011002940d4507040030400d0501e42004800244250300034000b29031000144040b50358015003001c81c0d51011501c04105071009041207094080d10781d910b5142210060070020b08040c810074152240d280840e020b58112810b994040d40c0e0b600f0007100c20b840a03600c0c00c00000007112929440c140000b00304000b05450000540c260b610704c0e960310b05c025403800c4d0101c16400c0851042105080101900c03000c420500e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 225348606 1250 225347356 225347383
    0x10b090d06020d020c01050a060509190c0c1707060c1416110324010f0312050c2811030106081c0201061a0c0d031b03180203031602030f010b0102 64
    0x20090000e440c1200c040e000c2d80d50601c80580c00800c0d200800b03181904424800c003002e0070101b000c19a90400c00c80741c01c4041c0e0304800c0509006250703503003440c00d42d08460745042c003504180c170042d00180e41e40341d045c2802c0c1c40c0007100000b000c02d14004011040c0030f2000761110500d844900d074044100c10319003500c101c1108040a418401d10301c0100a045240840122070040c150f9102d00060000004100b80c1404140392010b1210f0010500d814018411400d4942043e2261518000d0f000e00f9100c0758010302c42042c0b01d1045024426811540000107111200c0c0c072a0b07980b41d01d03031841c07030880094001322000700e21130b904106040c044030b0400a0200e44561002c010f03180d040c0c0c00c0c48810390042905400c4541419214044012451402001000403400701012140c050050320011000c0303c0c1c107025010400c0c403086c58410b840c90b00ca0340281c2c15607400e59454121202c01640007a2441c2d100715504c004001d00105105c080d49000c1c0b00352170482401c0ca0090081c8169440000d495002031600e84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 225349856 1250 225348606 225348619
    0xc0e040209010917030309060f0705121e151c0b0a0c0c050307061b030b0a15031d060405070501180302091003230d031103060904060b0d060c1403010b09 67
    0x200300c1d070788911140710040c607400480c80c62405014a038103460743e0048a01a089106a90100d418070282c55140c51081405aa8040c01c041c04000380030281d1030b0107404048165489084c885094200e00d03101400b4600380c0c42403408106426007030260031038403d40048032100f07000c80c1c07010101e4007a41407aa80a4030010001918060921090307400030407100000d080b601c004192101046500d500104a0716140da4001c2e80f11110480120242d410140c292508900c1d41e2070300700800c00c14401c00b101031140d0b5050219035101c0c7d01c4001d010815004000f144249d2104003400300780b10b010701101d4050202032802c110b40076203204c0100c14028003840000c0c001d02281c000200b010750a480820044c1d0707442000c0340c041000c040540118480050b01d0b06200f40107066403000420b0083c0f140c070b00f06812030007109040d50f546004003e10f01000034020385900362030b03000200b4250740300055600c07911311440e00050360300183e410041505000c50000c2017002c50810041c071a030841d810035503128010442c0d17030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 225351106 1250 225349856 225349867
    0xc020d0203120414120c070303020c2209290609010515030726070c020406050603070207030209040c0807060504090c090608060f011101050106030b0306150d0803090a05070306020c010b040c0e0402 86
    0x1130070b29141c0700c5c0c04419680c00000c140c0c0340e0051004940c0c0d0084a029900b2900c050b8104000c00201c422404d10459031041440c1001005ca40c554010140c031a005450000d140350095103004174480c901440f80c120bd218840802c0307410f00d0710322600c5014140c191081550312002007481482c0d03210150605080c030083c003c00804224054076103010086541c50750000604160b41c015244412006c42288100e06081d4080703a103060038016680314510342d500500c2d18516640910200038000b92042ea06441d14090110301484200310b500010401070796040c3c3da540c9081031a50449200c1d080c1c19041100d8035804005c019401543d03207030400030449211050482400050b1609514910411029400c0ca000001d2071a0103078055844c01c40d0030f070295006551202d00c03501b001070404c1c0c03025130302100c42d034100e00c0481d1700d2102456000003e4000c44010600c1612500e15000c1241c0c82203c41540028200d82000c3d028001d80c1d030841c20907101404005140030019003c1c81c42511580d0081d0f502248 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 225352356 1250 225351106 225351143
    0xa02250b04020d050708030f030f180c040f060503150103210f140d110405040b04050f04080c100f0207060e161509090203090703110105070309090b15030a0c020d02031204 75
    0x1e8000424020041360398404001c2380c1c2c6007041d00212603440054040500260740c44011000c0400c1c1c00038244064003180c20102e082000a1012601602442da910140070a4a45080010300212003101d810002c25600d5480c00001c00e40131010003113100c000d0030384442040c54101400c0071342085d650409240c49400780100008500079a449032801a05003200024203c0174000200140c1d0000d850074400504250140002e442c02030340c87d404030000340b00c002804541100050060400c1500980710306d41d40c000c0394401514400d2094070700b001c5c0d000903900100300051141d4405600094054409091010400018000d0f60300c611810f21306c181079844916031182404802526060f0802c54681c2000184981c2c0d0b000365001c211241c1c01c042d0f50310340f0150b02030400c2c1c6207916415615403580320304280214001e00360000180360042001d100000043c0300d0b5001440c45048802c100292440070f05070000c1c41c001940c0c100c0380554008202959684a600902c1a40160854103185041101c0c0c1e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 225353606 1250 225352356 225352363
    0x1509130b04020a0c1506031703040f02130506091b0a03050a1b08040b01080c0d03051e0a0309150c02030a1d03070f03050d14180112050a02250b04020d05 67
    0x6003055801031002401c2c2d42082c0d007094201400078040d00041c0380c0d00b503c501040c030488817180030240c07038480324500b6904881006001954058411400c8181244681d40420668a64000380c0050188c684040252070305041e864039a120004900d0b004180d1050405403031180316090f0240300301030f19030001031003208468010415101e031425a004050f00d00c0c15004003580010740e4219400c092280001400400c00100740002c01001003502c5c00481945c0d034169541d6202140c880c40004030f00d9070b040c0044003c0809003000207a141c401107510900303840c000d4031401a410305502440d20b082411080340c0e07400000d94000f00c0383c50415694682c0301c602d0039020b14003d00921503251181d6030011a00c2c00c0403009003412244030308111080c0e040140300648146101c80e030041c469001c18030030040741030405400c0301280c079018104004092001c1c1440fa0a41d00304443c40241c4940000e440c1039250460301020522442c20207422045040341e90300c900c440310b40a00b010784241c0c881845030b01805003e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 225354856 1250 225353606 225353621
    0x1e034305010c111903061404020a0b0309070306020307050405010e030d0516061104080114070201090b13110a061e0309020a0314030409051006030e1603151104030506090705150913 79
    0x14200b400035009108004184400ca000488246040102640a03007c54416040c013941d4000c0082e0034040c14808141c05c01d42004288400c54071881c0d80000100780c40344011401000c5980d20307140e4481c02c28002405c1d0401801c4250300035800f580729041440c2c5d1090640b80b0000c450040a2910705440c00d10b900641070400132816400400100014607403015800001c0c824208130b03c0580030741c0d482c0000d33800c031001c940015061003495000075003011080c410500c5154490801d81000b149a00080740780b104003508048080b50040148a910441c0c030b00c00180c2c464824901400000c50582c04508000800d02c00240020318415250940400a1050310080d00c0003600412251412401c1400f0780480c9200d000003107450b20000203010f803000704110989a00140e00042d09501c0c40c1d540041da86010740c0000e8240d950307401c0c11604401044014001103020708001d140904100c40c6450800c0d801e42d20803071207204c540ca811015400303180b09a80351200101d4201a00c0c540035071007140600b00e03070b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 225356106 1250 225354856 225354859
    0x9060604051506031618060813020d060c08040c0f240507050d03050103060609020306011e020c030a0309210201020a0602070204020f03040f210c021e034305010c11 72
    0x20041058803045c2840c0c4e000d504111380d030354914110f5004040700200e200e501031040014a240c000405110215210140741440a00342c0e1030f140600b4ac9490701258040406c1400190104086c0810710500e01668405800d480c0c21070b6405d545040000c138862045480700381c80315280545a8400d050044040d40d21081c0c212040c1c85034984e014030014010f00342400129180d03841c003903020604000300e03c241d074819541030711210310443d40b490320038220a0751300c50300400310f00c20840c2428036510203201d15605d552181d200c1c0f800460a211401117022451020410300081da881301601607a03001405141241d000800181d031a012800880d01910401d60101c01c000000400d10040020440d04481980e0240704d030803429000300317045100022905030304480060103450b9440c015141c182076074005020050400403450b505100800d0030b0200c4651b40510303105100000301b0f5030301010a1030204400100c600d241d0042012080c0700c1421009000301d41c1000305e8022044208030210700e200c0c00c850790 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 225357356 1250 225356106 225356119
    0x61201060e04030207080307030e0409020307050a06020f060f0f0601080405070f0f030318030308061215041a071404060e040906090501020301051008090303040f030215101508090606040515 83
    0xc650300384990011042c0e80c101c2c014458580005004900402681c22696150350340700c4e104000c076001c0001034501d5000503603040c081c5d1100000c440d541c03020440018030280e0041c00148903450681801e0140c01800312041000601c20055038800110915a116000f400c01020907241d600304a40f03044000d801c114410720303000300f0100b48044a0001d203000c6070712070398441c80394010400785104540b0461000902150001c1c2c04640c66180442c040e41442000c082203401c02c2d203050342801645c11007500e054130b000c8042d0051110300103420f020103a020020381880c4800f0481d4906041552043d4800c410400a5000904203c2d80c2c96070482040e0301c3e04010180100705041c03c210b4000c1d8428402c03644200003000080703026501502000348110207160186003182d450740c907959200d0903000d008804500078102642894407003201e00c80d01811900504068150034524080001008185002c0601c100402000050032000408035400542900d000c1195110310b04143d4101d05800c1c11141c0c080f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 225358606 1250 225357356 225357359
    0x130306050108070f060f08040210050717030f0f0f0c07021804150e0d020703330605010909020306060304030e030c1023070201020712021f02010209120c0a050906120106 74
    0xe000038100144c038a0702c0e0b405807010b175031071000f40c40c0314a40d00c02c13004c00b240d40d0400143c0549400000d59050500074101545400d450b0380c4d504050000050100691880110911a0038400360008960203444120b50380220704001d0018a40804020710340791903660001806030440d11070104a8060b2885407150000c94105481c240c07401000f0130024101c0a850220741300c4082d003001461866408040d0040c2c8005810754440d28401514002c00308070941d240031030303d0b400c0340a4103080c5031820307414100001c0003401c00d4001802d04403190300c5000c07150300600500c08607641c0d034001c9903002603040c2003604e8009050b40200781003541466000d40d00041d001c01c0301e1840c50700981040c20702c1d559640801c5200706024030b8501140581c2380b0180c01a40403120500c42d00c040503507049a01d500080c00d41c04a40c46c0303d00d09070b0100340c2012018005075004150355042d400c0c01891415458503010140032010f40010101e960200ca911a140c454451000030401c03d450b403680640740d80321102d00034001c0300e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225359712 1106 225358606 225358619
    0x1104140c09120f0a1a0a090804050907020c0306090a02010206100b190507120f0314040510020706090204020c060103020a060201110d0504050c040e28021003021303060501 75
    0x103110f101821815104100308101c1d0072445045102c50528403014941c070040005014940e4250501901d0070015490034103560a480301640c2001742c0d0b58542d403003285440025180c00303806000f0f0f04103101c056030011a4074041503000380c003110b41e030380c86024211034200c4030340c49403402e56481404898801100c000043c051a13903e40380c054207220161311050f40c1c0c1c0080400040200f9043c0c10b081341e880380c042c080c0113200d01d05000791170818030302500c50a4032901c21080341d6124071f44c0054070008100741c66200e1895941c000c0c0045490300320340b800981e9559020700041e807040c00080c1c800294544140a10041c154122043c1428010f406508a001d01400b0740121090300500720003000d20b484d9480b40b40101481030b401000118841c0360f050032000a415070200110f80038000301e4015844195610510500914005a5480406442c0c810340e5140e6000204050306002c00040c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 225179856 225359712 := by
  have h0 := BRFrame.cov_init 225179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225179856 ≤ n) (h2 : n < 225359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
