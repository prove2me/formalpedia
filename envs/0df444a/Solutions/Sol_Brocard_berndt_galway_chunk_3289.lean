-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:33.739984+00:00
-- url     : https://prove2.me/submissions/717486c5-d67c-4bd7-ba9a-7084b74349cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591366906 ≤ n < 591546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591368156 1250 591366906 591366929
    0xf0a050d0c110c0d05120c0c03010f02090a0e060a1a13060f27051009150c230c0a0618050a0806011701090c09020307081003111e19030c 60
    0x16400003840c0c0e1820f501c00700900c2400500d08000410204028204000030f10707460b041d40361202c403441c6903500c00d00300051900c254281035200182903814425900b40c02c200904102070185803860f01d49880340050085500710703141c00b0300498003000e1008664042441e0000311341d6913410b10079031a40c2210154000e0002c006800f00c3c07459078641d00c402d903070b4030040f001c840d5100c480d81941c8040090482070340c00960401220000409810740081d483e00403592100142404042918030890704c0c2c42c1ea012001300070a01c0e020040c03601400d11803c84000030041400c5a038500180c40004603c0c102c6540006c0000d8056110360300300300f03103104c1d10000a12094812045441c20850004e0716202c05000b0728564415000c0340350030945003504100c0c0c03441c1d0003804a025458450b0a05006540b089801c4c20120749144041101d4100c124100800c40b40c00907003080d001e1880c00e0822907044d10072100031a501040e81d40261684c4c0e546003620122246401c5101c0d0003d103140f92000f002d15450f0710a400652 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591369406 1250 591368156 591368177
    0x6040513080a0e12060708070f05041805060105160b0105010e031506040b0a0b070c0e011409010e0601210f0e0604030e060d110d0b030708010e030706110f0a050d0c 72
    0x5440600340c51160559040c88000003e0b41008159006424242010144203035403c0c052005d0308a0302c0b00340618056660116100e8500700d05840c503100d284210302020602071500e07130b15a0550f9202d20340000c01494242c0c40c200d04481d0b00c0202d0300850100395081119107004010961304845e040d0740621064016181442c150100030340000c000500c21801a0b07140d02c5084110394481a070080035103182c2141d10b0b00d901290030128901c1c0060b000c0c0043c003850842c000b01320380c01d44000c2003801050003805045c041c1e00741040b0f01e04042018151a0502c10b900e602c41c81c000081c0c1403500f08401c0d110000050b0008000c0702036082d6045000101c145410007824480425400f21a417041100c0940e00255915269800c060060050800c0641e9042c8041125035014646410030406548101d040310030041c2c983d10303410300b212151035540c9203590003000301100084984d013001c80c403043c0031070205003044243d500400650f030004d1203002c0020400502c001e15100d45110b9800c2d40c06052401c401da26 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591370656 1250 591369406 591369413
    0x705010e040605090c0a05090d0605100f03080a12020c0d050d18050d0f1206060807020606060a1b060f05040f1e0c06030213030c08070303020f010c21060509040b06040513 75
    0x40090300780408080c0c0046c0541255000744100e400064026145403401045d5040801c01000c0c00e5411850240c4488000107020700d00300d0002041e280c000140c80c2c43d203401e401040d42e0b4103c0070404a081e0b103809000c0c0c0c03103000e03000340003174049e98005448803a511108003000d03000b210491100c0c00280006044003001013000042c0301c281d01c2c640b0b07050072192502840400e9171600d400c801c280d0826030403d180410300c29070019030f0500410842e02280c00030f458200400005021744440000090703d160f103c41401c44000d040e43c010360340034410000c0e844010f022080c050381d60483e01036450728020102c03d410020b20b4101e4400c075080c480e145145400c515502c0c8440f9803850300c1064201070300840e0348840d064403085401c0c0110390203014184159528000c1e59242c0c800e45c4416005800348021700300814006014603030912502d42e854004054450802a01185507000084142580e13a140440c90362250b2441d00d014601031401060326251082c100002c0c3c60340246040c1640245011740c5000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591371906 1250 591370656 591370669
    0xc0f030c030912010b090c07060b2b030c0503030406051f060503010501031a040608014107050d0f1a10090303050c15130201030b01021204060305270705010e040605 72
    0xd140b01110105049203142c4000350143c2511548540c0c0001c00e103060014440b0442c00030181c061280e030052040000d00800c1010b51920b401c1500400c01c0b5034050703903603c2d5034488803040515104c3d040c5291502c0c0262216451900125011201740c1e503100f080c001c0c0c85851500040e2901211403110304a43c0c10404010a0340c0010301c2200d05054540d40903619000c0f0704c0e010030b400014042c00130018980e844100c94080c0030880301450b58480c08907407607048220200300d60070030144c1400c4003509010302c210128070200e100424150400106021404600078503004500f0000200c000114000f05c006218003564655010f24600c214618042180000d8204003444100e07038040c1080d41d01d035441c10101c14100f4203030b15079004d0300305420410000340c0300783c40224501c16070003a03030204100c80d943d800590392260f481c005030600490038001004078510035080f0720780c05134803190f811102e40f07030b00314440602030390009400c1d01a4006071014031403542d005458128003071088505200e040d00e8072010490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591373156 1250 591371906 591371917
    0x30206100315022a0c0f2d030109051606080a020406020d2003070602030411180103110f09190e03270a0503070e0a051605090405060f060f0c0f030c03 66
    0x2031581d0081a100c88013201880c080c0081050440200c2c103000e6180085a1510480c0e140d5611403440f42a0107051403c00c1000d640d0303580301c0c542510303407030686003440320030424400e00c4516819074031245010b0000e5002d10440820758840c540c203240a80c00c0a00261440340c0040c64040300d0391052000700462a4006403072481d0032828108000382e119031341c1601c88400d81c1c01d4003e01c1d02e40700000e031900c200102c55000f94452406040701c03950900c0380604209241242c10041d1001c0b440c107a0040c0040f0700051408001c05500030015402c0c00c5440001c80e00c151004c65982045d50f007001c0e00d20380084010b0140e814480c03001d0010314604104409440400e0308041080c00c8000104107041049480e903200440c081d01c0b000f8110f401c0c50356200c8404000074021600b183c16141040007148241003501d10803000d030f2405d5210903050650410a110080100416050b40400038451003d0640c171040010041c1003010b80a2565401c03d048140340340803030007603103650b10381c0c030800110b4403496011081d02ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591374406 1250 591373156 591373193
    0x1051f030308060d08040b0405120109030c1709030709061e03021f050d060b0a0f02030909010b090d0204110309010c02060108060a0203100b18010306060c02010905040e0f0a0507030302061003 84
    0x3440c5440e043e000c42e4130341c928030500410710f250004000c103000d00801c01401c1110000c5401c580b8038522142c0c424241c844a20005020500c0c680c10900040c0700000c5824069100c40811070030442da07040042d10b00425548202c168954600080c8101124141442c1084200b00c01c10501c45140d980450a144175016094246203030010181006a2156044501c483c3c0038001c280405612103103552100c0c0d2002050030089030304c1c031ba601010303a4008002e03185a03140007084e20b101d9a182003003040180e03114001180c2c1c040e00040c41c00d00141d0743c900c80d864035000c0392103006851b031810020356800c45404a00c036005540c0004010060b803440020340b1540048a0705000d82c0329150510008a2900702d0b820505a6030004540d07480c01c0c0c056085030605c090f209990610189a4900080e581c3d00700c00c0c43d0181c001500050f09101c9400c0c1034208042038810f03202118035814241c1f05450601c8042c43d02103c10b500218402c200340740e41000741c1034002480f04040d46039649117540318545410000d1910 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591375656 1250 591374406 591374417
    0x1c0e0114030f190e070e10050a06021221070f140c0715110d050d231602070b0703050702031e061f031a09100506030d0509040f150801051f0303 63
    0x3c0051031580c0c204ca84044502000c442205407120031482c400c450490b51a542c040500720300088602d840003200c0c2c00c0351415000741440500c0c00a44444981c800c002c80550015a448001307000c0b03051950071071007000e45070743d20b0350362084030034000b072a0516002d00400d03885410302040340b9000000c14420704456250b041200d41c030760000b400b5201e112141a03051f5090140100030307007032140c102c4000e2401e01c190709000c0000c0c050b00b10a29035801c10340c03140001d01d2101c0c0b50002e444440c004001c6500ca02042c01201c10390384c0d484840c00707119884090121300040001c6a000214241000400318054040d070350300e4440c400720702055545200007000c000501080710031000c607003600081c0c034a02071038000510b00502d01054400381089402030724405014452008000c40242941c400e150250900130050185800c0d018012076070340e0804a84141d00c07a03070b2403a1941c104800c92040b0b00041220034504001c0c50719103030310751342155002042044aa12203240d601d8101082c1b81443c800c0d2585810030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591376906 1250 591375656 591375691
    0xc100e04021e040e0702010e0706080c03070c080301080102040f0b0c0604020d080f0f1b060411010c060617010603020306070507110922060204050a081516021c0e0114030f 75
    0x2c0324003203055400c00701981000041c003082600e41c1642d0039208089940090100c9410090070702d59a2401d442a00005001180401d41c152103050084d501b00070f0920b40155072014940b607012140d8400c0e0311264140e03600141c104040c0f8007444140c0300429820740994102a00d2401c283c0e107031440240000e1041400262803000c01c4000c0c4103032850040b4000520384c032404051000b1645610075441321082466209500751007110004019100b2580b1004c02925800148015546080014011140207480b11804640301c038040c1d00d840c402145000010804600e180181400d100c1e000d88110704100b410082080455040c080f8051502001d03101c01045a8404007003210010010044589a003202c04541d03051001c03a4000e8001c0e944210392442900d41d40e060345607076030743c2010411403074842c0081c0090f000e40e04c0d1074649101d2030501e0040c0d6855940e0b540c03032241c00943c994140c0c1c000c1940850f80c8042c6507400380e8400c94162051498901e0342c00d060380189000c20004044c80ca100300745418 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591378156 1250 591376906 591376927
    0xc05011404030c060905011d030c0f040f05100f08060106090311010908060a05041101030c1d0a03051002030a0f0c0203070b041b08030d110703050d0c0519110c100e0402 74
    0x700d400440c0c210030b966080646501d4001c01e082110300c2080d0000b246840b45200070786601d8400d003901a4003d000f0b04900c002d00c0184410000040802988240e407070301100d204910a000f058400e001c1d0a01032a800d908000011130200b00c2c0b60040d00d490740c080380041c454160054211001d0f6038100c02c07080d4400040c007004032241c6c0603035001141076008d40810301001e40c2c03007074100c2c42c045c0d880b030000090384035610b200440482d10044003040001e44102c0b010314091000214021003540b001c0c01c40b080c61a180d4889078648080000c001d030002c0e5001080144078041d500c20f03a1410400340f00c05000b038002c0100c1c025601e00481c0c0c00600f031009002c0100c0d04100e01f920222551701d040300040103c0070fa85442c0c41c1c0d165045080001c4005082000030400c1d048604211000c90307074103032038a0342004440803c050041c40000300c02c4050040c00c104d0381c2c03454810f2004804e540f5015035582c681d1192213000407401d103181412154081d4881c60322041080e40c00c03004007052401c060b078005884501400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591379406 1250 591378156 591378197
    0x260c0601030b090a141e06090c0411090901150801050103110a032301091d280303020c01050a060501020c0315070f0203090a08010903080112170307050c010c200a0c0501 74
    0x2000381124001803203152030301c0000c01c4e09180501c038a50400351b8007441240403511144c00710341c140203541001105407001c0c0b038298085200364103203010050400040c4400300f640c60100380c000d08980150b1901050302c4940c8890803074090082881e0501c143c54039071704404803601030800e601052644030712003000b00c0b400700740b100c211a140d801c002440030759441c1d80560044c041d00903150045110484200d191f98000a030f118003400003180c400b901d800800b4000c0314000c5038000c00700c04041d001c01811a400e90240105806034001140000700c961802e0300282c680702565071603d002c1e401111880640c548031500d180c0d0300044506002c80240c008000490030342c40340a001ca5488a066000030680d040305501c9401920b10a456038540d990300c03111080314082810000605400c0e20070303401e0808084410180d81c04c225039081c01410310010344001420343c0c1c103101222000a0b5032030781503480b41c40300c944100440200303040946101a100d0300c88141c501c500380145410302840d25103008440c4070301c0703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591380656 1250 591379406 591379423
    0x1f0905040f1703091506060a20030307080a0c11060406050a20130e01080c060906090909100b0f0906040b010905090708070e011d090601110a260c0601030b09 69
    0x11415440182d031403015603082da00280d440c2c549510546142072a5102042c02290007048010841c5090041410040305e01c0d588010f08001c20b86200e403100c00c8606010006103000d00700c1600d50350300502c1d01c0f0318090201d400105c009000c0046150001c40c2d026000b00c1c106805c0740d0810400704160b951940d4a801a0400c420b1508040d4005170040711001c1c013000281206200050f00c2144503a90340342082c000720000e0144080b07541194144062501c0d0400c008c009440000d0702803800d2120308000541180400c46044103582c000040c6412159050f10403401c0d0118115401008120000003165071984001c022600950340c0b020a006140e0080f01c80da0000c220003040c003004d91500940052101c003003030350000c0c08103001c60301506048d030213090030b8041c0c0e01840160601d26030f840403c201e0b101c003000d4081810301c000c6180e0324091250501901c083d840c001c0d40d0303140f0000c03040c50804440c0d621039030010203a0f04050003104019200400d066045907049403280380340344c8a6104403400c05492 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591381906 1250 591380656 591380663
    0x1422051905100b0d020102030f0309070905130c090c0e040e0703050d050a020705011e05131e05091b0313080d02070303140f0121060b03030f0702091f0905040f 70
    0x856150041240009054100c20041d042c14000656040b0038441c03900d41d03082c002800750304140a129540400140030315031015181381140c0043c0d584605a4084410645103034101300e481d17010803c03e01001c02e010200400e601c4000b08811050003400030881206010141e104a458403002c4200403010440c000113103030002c0c165116000004d901610317540c0202c2c2c0d280c000d80140c6000003034941c0502d00c4801e030201044452211004200340807031711035006801001c4685e24024011070001a0500001a0300c81601c440d05080c40c100760030004c2c41c20740204201d00e514204403000311201042c00c1600d03000901c440602d44034400c41d00c2c06555a0049007940540c0a10109110062541c10b4010061907003140b00340410700d031a04502000c0380d180c2401202925045894000d541d01e0200c005800d4081c0194000205540d00e840020308660200303040c0200c03c00c001c40d10740d084d46850010150012068145503068409020720941c64100d248200f0741616650740000d81800000907605d42c50690 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591383156 1250 591381906 591381943
    0x90a0c03090b01091b0203120a05130c090e100b0a060c0f06020d0c4a04020d060906061b0210050c010207050609060a0b0f060a032904142205 62
    0x86036030f60413000300240c16280403034420907400c0c662454004021640f200a000f410601d080c0e49030b1041601510000d0f11600c41d00c160003402c00c0100d00c00d580080040e107003020012030303001c0c0b07068642d92032701e120940d81c9401e441c41c00d02081070030707912040c1030000ca070b0003814113210744003180c00c00400c08050640081c00c01400064040c0c45640b0036400710030241041c4d140c0c082041036a40c81132310400442041c80385d0f1100d603030601901ca10480700501b44d1508000814640380059040860287c1e0000d03008808038036110340d8180100f001c1c1380109405098a40780000101c00740a0310044800c0124070003034012554400c800c0d8019204a080318019000000203554550080c500265503200450784144980a5400031440a48241c0a6409014001001658040d150100304a078950200c50120706040d95100c0d03100c180501c140d8400f180c440503c3c03144020fa0f02030f105000684614001c00c1804a0120701005078031a21810f070000010030340d50b100c04441c03682d850b043d4038001c00c010501c409d028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591384406 1250 591383156 591383159
    0x509130302150a020c011406060d150b0c100c02060705031f0b0408030a0311040503150903070501140412170114010e090a020a0905030a261e07120905090a0c03090b01 73
    0x2a00c4d0001e1003004054002000740b580c0784030580c0c400e0101900e2040c1e00400c10450000c81d2155031b0401c200f1861190b041c2112659510080c04203948066000c1c2c3e21134020342061185403410744102c480c0102103001400c043c1c03030302041c001c245100042a120f400e0411030020162200c2c00c1041c00c000e81008400706658984454410b0707580e80003401e002c40043c3c2403005c0800152141029076044650181c01807400f000b0105000c000104010301c0c000d01c0e03100078090817010407024040d000454565984c3c52a481c101810020800584031003038000b402186460807c4010201050361f04440060b0950500e030044100100c2d41a010003003c258031420035014042c400300740b40d0041070384901a803a000304680e554401c1c5034807520844c1d8090840881030800144e458400001024240707440c080036858281d8241c6000303100e01c0300d80e0083e00c0e92500401c00f002000004040e02d100c1e401c490400030b90803403400300026074400b0003c0c00302240c0c0b07490707190303c1000794001d410020445900c11a401d0b41903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591385656 1250 591384406 591384421
    0x90901060302032e0e03093102040303170906180a0c0308040603181502091909060509061f0f090305010f0516321c0b01020115050913030215 62
    0x101c0d1303440d054240051440848098402c2a115200010788641c01545c100a1501c0070417000d2840d6840c0e000b4502c1c2035100301a44408007000401d00c0b0400807070016211811410010312030214082035450485a0b02c2c140402000c0025070f480d441424004c058000e0348164690505201e2035841c0200f00c4e8060000210810150030050000d0f00c2b900d6034200090420030303401c0c5040c000101405807402209191002d040d00301a0002c01c02810064144841200340880d80140708041e07902010040356901ca082c400d500d0651101c0d504404100c40303030304442004c4241d550100c10100c0c4060f0a000a40b074817801309600900010000f150010000c00c0b03132411100243c0080c0000b1281c0e60f200a01018000300d0f00e038010408509140b10101c501002c031300720016500001c0040d2003980031140800d100d650b15610203c070007224900d045180100340c540e200740c00a42513800c0708000308068204d0751401d10554540707034540c503800b04540b40c80c060442002c1c01e00341e00b040c0c04c4603106a40140700404201c40d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591386906 1250 591385656 591385693
    0xb0102061e15101218080d0f0b10020307060518100504031e0c0b010b0f03130606050406060c060501051f0324080601080d02030a08010303050703171e0108031809090106030203 77
    0x180e010f410f20610170705415894075889500b070f40000801d2100f080c0800400a44541c3c8040000c3c14000800212511440700084002c000340304040c00690000075000100199030003070540000450300130b031402d032801c41071031a202d908203040e0310900ca50b6680040d091520070000a80356030308003c0b030302c502580902d10050500010900a4900e0f01c881400019803103480002c4448200b1801c0043e030035a00d4402000e107060b4000721080d106a52503040104841d503d600c181c20090140c1d0308c484074600c8007860031005032101680702074424850010705072203e4000c034041c10426509450000ba001c1d00040160351007100742d90201c59520040480841e21401c002960f03416126854220b44600358542e404030386d2886001c0d48900003c0e582c4004200103800342c1b01070024144281451041c1945044404a240344100c640120401d541101c04442d0000719002e5405810614099031400c0d072403120360f62009030900c020a004508001c0054601c020030752103003004d07560080541d800791850350f8481e0390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591388156 1250 591386906 591386927
    0x150e12030c070803120105011805090c09030618070b0a120c0c1502040501090b030703140924060312070c0e25030504151d06090a060b0102061e1510 65
    0x882c1c0708081000c101a00000141c1c2d07800c80c003c2208116036801c0c10011030300d51b180300f0180040f000d0307482000f00356545c0d0341da0294807848505d0541c589070340300242018940b54029140d1811032441086503070f0400004945141034501e61010150fa4038184201151070821241012170f583e445c040b10603150b03650240e1075035841800b466084100c01411200c400803840b40e0301c11a404200403203001c00280d1984d2001d554006860305000440c40702e44010040c40400444480d9a2604070120110f50844c821a071a0713505440191004800e15210000c40c0e91008109001456803c000c03070480301300135882d0701d02da001d003000070007402107400d089180c801c60607561b0801810510107202c001c1e603514424881c0078882c982002d0006085a505c0a5910003801000080c03951309007403a104180900c0c08005081c051003000c801410140028142602204e625004030f90441d001202441f221341c1318502012007680700c10100700c017152103005e00744a84150b684506030300449181c89c555040341d0071091600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591389406 1250 591388156 591388177
    0x10b0a0c061b03230f0402042304021201060308030a18020a0e070305061c20150c06010b09090406020f1c02090307150c061505090f0406060e060109150e1203 69
    0x85618184e1122041e409451140060130000c0749000410703608441c5c0b02140c1140c0050030002e00c40e03200404140a02c17030340701c44501c0c00c401b118043c8011420401c280e83d00b0b20744c0280003000b0032811a900c407140c0344405880d40c450340c5c3d03c4035882401c410700e0a01e079902103a40107000303c1e90b03d5034a00d07410240311000c440b10000b292500c8005805410a02d0014081e0340c1c08259004e800c46207035503810b43c400b0421f0701d02c13a1480a21030141015803102d5180c080668101c40115803520180001f4510384035050f0070813402d1038014040340e0b006454080b8a43d8109512002c0540c403000010821001170048008207281c2101031b0001c8200c8091940c010042510182c080c0c60900b41c451607007043d03030601020303000002072280d41070324013003105544104890700c0c1030070103661a03907030383c0380060310080003902d00a0f011000030080c8003c2103080d1007000000d000841c100c1d4500d2502e0350002e05418014469010510f00055421040c0c5102e80d142d0443e10301c00821070203100c007860704036950361341001000f003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591390656 1250 591389406 591389411
    0xa0311060d0e0f07090b0127051027121707150f150b180a030803040b090607020a020102070603050411090709090b0604121103120a05090a050f0306010b0a0c061b03 72
    0x10a0007049402241c07402c2d0306c186c4030040c0c190345c40650030300304444030f900c007042d0402058001306e03241d0355800360603040d50794a603607080c3c41000c504062801d0712015242d81100c01080381c1c040049950f440428000740741c0050302c0c050091101000c034000362140a1000f4400031240b08240c602001c158070084450a0700c900401c54150031072038401c000c84607400b40019505040c490214a600c0365203442044202c05017040520303e903a5501c859903a00281d5086404014800802c05520300420055030b00c00c101d40b00400f609001500044d490b10700b24005d4a0030141c60b000001c0a004540c06200c1d070350400a48070036000c0c504804014070034110360150400490809211825034030700030098409880d000c4c42d8043c0e07002c010ba0703181103640200881094150281c00d00c074035a41d800b0600904400c1c21203485070741d5956400000c1004081042c1c10242c803030011148030040340d46000648905407070302d42e03010396031f105121300e01511460200700300105400d0920110103089c0a109219041c0458a83c806 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591391906 1250 591390656 591390659
    0x2040c0c15140a021c021308070b090405100b0906030403033c0c0e1c05030703050c190809010c030e0303040308040e07020c101209021f0e0108060a0311060d0e0f07 72
    0x30f0f901a0b11640c8202982a41240880e0002c4002a0300401c00b0750b9108501c580f405654144090600f000740e070040c0160207001c0740e0010b0078101406950340c0302c03984031501000c0a00b04030501c2d50500480361520b0190f41c010000404050003a801045100111701c00042d00440e11503035581c00784100000c00c010008030304108444900a80540d000c8007005445030829007400c04280000c1c2e6800c0a01429045103050005011610034002021210302a030b5603507a03a41640d85141d0f14205064406032103805d1645600804034031180203613007000c802460a10081412801c0450720340260840440d40350100080000800c100d00004104840705102c4903030f0640d440650583c0c4071400344074402e400c0348080d5186420144a0180540084102c450000b28141e65401145890811b0100014010400c005078107090350094072001c0240000d00e001007082c901200801c4018509100c000e000500080c601301c1240c0d21401a15145403480c4402c0144c02160f00700715a80d10f045484125031030148240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591393156 1250 591391906 591391921
    0x3020f0c06040303111608030903130806180a030c08070501092a1706070503101e03031116120503040506030702010506100c03020d0807030e0f06060307120203060402040c0c1514 78
    0x7510303403105100d002886c41c89843c0e1103d20942e40010b20031200d60108110b04111141e02c409000d0140007035400034080c40c0341441d41c044c0080b04c2140c1480e0f4503400b510008000030381c00b00008800070b600003240c80d141c54041c60000e01401c0407020060046a110034003a614070003a04800301c00c481001907003060660740b6298902c4030040c042841d052900310700300056100d03008000440d00441e022241a80b62075413030f036002d92180604805c611032400020300800c01c0c90390000300020441d1f2980c2c0074100008505c080314038094040c2c031503204034074100781044042c0403003401550000e00c809801e565803490300f078000070300030304080300c440b4441d07078030003442d00d0b20b440c4a24091380c09242c0c10b400030aa00b522801041d10313070400003410351003050f84078003034086c0c0d000080c440300360041c02c0c0500404050618038201410f00c0040d41040c00840c203960440c01c00742c3c0d030000e034540c2c0003601964000b03011141244100d84101e0803101c0074240601c0009440c80400303232944060751511006503d05219200c401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591394406 1250 591393156 591393191
    0x10305240f070f020703330b102604060608012901030b040605060a121b120504030e0d0b01030302010f0b1e01020c04140a0b04181203020f0c06040303 66
    0x40301c0c603048901140004090718010b2251254124441c01200e0f0069544e039139500f05200c01d0480b407a00d8003c507100903c5240200b80201c5955400801c05010024078080403ca1951115103242c1c20001c1d0709440111003ea40c0c440882000300030346c2c51454514250414102a1105104e0000d41c5d40c17038111607103070040c40103810324440039400810b100c3c10392150703004402410360b400c10f9035481595081d000403103948480062000c0700c2c440c0c0384c0c2401c11121000c0c030f000700c0b40c0c9154002c0300c3c0c40d010345480080030781c0182801d60f190141e030000200354039a030900301e903030380d0381c0031a42a0007007180446102441034004075113041368840e50090191142410504c010340d4900b1800c0c41e00201c10358000b0304110b078401030444403180b0610445404180b400300140071b40745040369103290381d107804091000c28816030250080d0600252814880f0500f9280d840c50400c1d5000805803450140c884521280c500c2a011144150800309200740c075102c040b100302c0e07250141540d040307021914003414190843c8010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591395656 1250 591394406 591394411
    0x706030c090303030e010b040c0c020306010519270504210c0209060f04200702090105030f151b0403060501060e0415060c030203071209030507090509031c0b0901030524 74
    0x207944240c000c5155640c1600506101941e0703d40c0355485100306ea0040d00c8520030410b0749031071543c410040e4003580c01410305080040c2c102e54000d0490304000203240c0c0e5091a0070045804000a546140c5d40c41c12a5403840340440601d00c85c1039050109110600114400700c0f4913540c1c0721170200100300814101600e19081c41e100094101c4003070300c005030300303854401c0c4110b2140001900104503104414000c0000c0c1d80c01c04404083c115001c0742c004150f0500300e94190142200703500900060b2a0a813015a48580c004800c5a1f11175881c030020b5200d145418000f049c203403113140041e8445071280740c14406400309006210005140b10503941d141e00d49030040b010030140c082c4022a005081c8030f0100c6d168280c03174a00780c3c1035102c10000c0000055098441482d8890b20b51380e211080b80c11882d00c5420422aa40900c1036607041c0400c4c04110000403007104c0a5010380804282900450300810001c0d0485007012076000b402c58000100784240801c0c03c406005186101d0110038900ad80c00c2c03003415005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591396906 1250 591395656 591395681
    0x1060315061110060b030a0e0613060504052104060305060f0a0302060d11040806090c061c05060f031b090912030112170408010b031207030e010e060d060e09070603 72
    0xc0310070400e86005032018190031500100795034280303207411000c0055030020350003844161000010400303189002e1181030f03074400d110005401c007420550310081495110003c05030940303035502d001c202003101c20000d80042426292000d0404100c80e40f070074540380c1041c46000082824100020302c9484c10b03800140a258008082c00316403070030743c1c090100c507030081908248107a0390713040307240c841840701e1010f04002d04900e001882c7c14a80f44d1521802e000d1600210b038012078051041c11102e00c0c82d90f4150440c0ca03808c810000c2c59503150f0002803101c4000000351901800707004000100c61411121030100803409841041441d1580340603140e4800c0090903402c0c84100c00d10042c8488200300c01e007203080e03a000d45c220090800c008202c820b0320b98032950000c5400d0b990f4071402d84060905102030401d0f4201413500710304ac1840d90300d0140c07103800441012410041d0404602c1c0d80740d40c2c1c030020b69800c041d0200b01005450b80750030704500d48410581340c6400360300c074000d03000900510030301400310201c0d40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591398156 1250 591396906 591396941
    0x90b01050d0c0908010f09120f120b01090e07110607051c05060a03020424051c0201050a020a060c030b1f0215070311070b180a05060112050c04060e010e010603 70
    0x110400c050000b010321250712002c21081d52000946030100b4001c2a40c0c07041c4040700040e456081d89009404103400540c007030b0500c00e5140d1300000c103a8004849180b60b0303860b8000460043c2c601c00040b01c003900075410110070001c0407418028419406600f4000700f484140449810741ca03890401c0e9200d0003040200001c0d1694680b84844500880e0000303a0441c3c005420a0721036034980c1c0c000f60690b00400c004d506240042c144040c425141e00041400518003520b080014582509503500d502d1540c00000c0e046c000001254510310340300300255a142d94001400708012444140024003400c800f560f054418120750f9507082c880d080b0f2400521440c05150002c00d9000c500341440e01c46054010003a009050340d07070405184500440004105d4540720f4595142e9900d894094014115619460301900d9408440b12400142d40040c2c600c2c19515490301000c84071146140491a04040d004c1864000f405c0480c0090b0099494902905845c1002459401c82ea02d03403030101c00700d41d0703150111036a80301c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591399406 1250 591398156 591398167
    0x60f0227062a030a020d12060602100513020a03050705130e030405041508030a0203120106020a02030a0830040308060108130807080f130807080d08220b0408070c090b0105 75
    0x100042e050340d080c2c6a041800200d4038030003031140c03419a00304010b210b0141e001820307942402079100280b0003500034001c20401019081003002561071000f08a401e000564581c0890a0341210000f142d00c50395005042e030450907202d2904071384900281c41018000c640184400441c41c10318010301c00591884002141040d10b04403c02000d4150340c004107400d4801c1d61404103280005000070058041036800a640d28000520501c0d40000c0592251085402175a0b6910040e5008910a06116084a21140c5405200841806041c544480c545880c200820b180460f12055111184203038043e441d00c1000d40d079480300549030070304111992950001000381d0140001c2c9135001800c03007a405000468201403808e450310f0300c10b5100300342d01d8107d0182440e04000e618000c020140281c15210040c042c250100c8001600c00c13100500018450a0b0303031015900326415042d56941c001e60001040440d904082c00e003a0b0740ba60003240c06031011031019a020802e0101401824582103069650b0351505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591400656 1250 591399406 591399427
    0x11010c120203040f0803042604270f0207050a060506090609040b07050f0406020f1c090501120e0a0b0a0605040207080306010e0109090c1205160905060f0403060f022706 74
    0x940c0001e1013160480420810b020104030701401940c41075200c2c0250100e024400d107068240d82c1e41c2d051144014100800091000312030a00c1d00ca41c4202d46004c441c011400141d218070b010f081030140c03030341005102003405800d01c0000110100e14a015031003c11030b980700d810522404c0c0c0b030201d41e82c0da0040c00c0d400c003180c002100c24240702d502c00d80a1800900b0302050030400c26071640300d5805080180d0000c40a10840c0009100c4442500f9082da005440c5100003040906001000d1241a0502015100b020001a42070b001140080d0318401a075213890307107038a405802c828061b5090031a042c038025000c92a03092520841d10507682146a00b400d5698600044954442c02d6503c03d0402910100002d44c010050048080c1413100303440d40742603038404148504c125140240003031a59142c0134600c50b00705821442007420b480b410303103815035169000c070400040c6106652000f0001860280c004012894941c040c01250320149440802080030b02e05030100f442500415661010040000c2d1901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591401906 1250 591400656 591400661
    0xc1e050c010c0303060519060206060108160c17030103260a0e06070212010c1e0915180305060c180d02181305070305010b0f1002070312031107030f11010c12 69
    0x741d12a25010460075221004540350b0b00307e10084048040032900140001030701032006a51000007883d007101c0514200712000d040360310350300d2600140865420f100c014464426542d0031820f4031020410387e42d594928060b0a01441c681c0c1c1d040794a0611240d0745041c011403401c5a0402019030344540702188404200076031580450030407a4043c8a44103800c1504d2402c0c0941141419151a000034071f00124810892484404081c10100205140e01b0701a0f090a41c5010342d40d114113140400482d542403089078a01c102c16000640180304100402141202000041c84001c0d29402499190003019080c0180350707509400007544805070741940c0b200d103603161450903482004090440b0764140b983e00c556003454090381041d101c5da51500c103d00003509004409041202c0b0035606c0e4980300c101003900948034a0780b400010714130000341c0c40c6114180d200c0e400c103201002204c0d07030060307846000380744c05801d81420010200101711005c03170b6030343e0b0103006100780400155680c4410030484083c0200a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591403156 1250 591401906 591401927
    0x1905070c030903201206040309120c0b0c1603060902031005010e0703050a0f06060302031015140304032006060108100609030f050a171803070b0d0b010306050603070c1e050c01 77
    0x2e100c001103a1013150354600c180400120070354043c00c418203240c28000c02d03000325030700302141c2c60301aa081900010548030000c1d045400800d82c3d5520303031445007101e90401030054401c80791149800d0300402071100c6a8030001078036108600715442c0d200c4100d624803d6038424807450b1a0040d0510002d04118001d0300300c41c1e03210403003020029004018168440465481d50420000258007108000702c900d801c00c0048040c003282d10360302c0c0c039640001e400100300014000c0c02802c8020040081810140074804d00307aa0303040440046140c2091528189950391411031b59103000514400108413120203210350702c810f41e0050f6030b40c5180c490864581002c03001d103480040b83c240c4108500c100c08a48042d040040340c9440044030f035510707d100940204031042084010f4030079040280104003101c206d504480304d170b081d2003001040c0c0d01802001a00244490360040c1d070410750002c1009076582d8020100b203021441009901251104600e88025a54a03500300403c0c0340e00640ca0241c0070741c0912000d01c0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591404406 1250 591403156 591403193
    0x100e01050c0a0f110d020f07090b0a180207050304030305070618020a05010c031701080c030d1701060c021f080a240608190e0318030d080a020c0c03061905070c030903 73
    0x52507000002062440d11010004080c010b130080c3d808a8121319042c0080130051170100c00a214503c91580081c242f9039991085120381c0088034000c0e94000c41d01c0d015030318603541040980340c41e10760721b003009009a440800c0850b006032404c030706921000e00080d140e140e059009081c00b544030303003804c0055600b250344080540078010042105807040d508512541d01904003180174082808a4a091628000d00320440c02e0034404440c614a0340d415482c50694111903181c034003203020039418001324050f40507500103403141d60390046980102c07507040070742213028500855041000000c2c0007103020900603c000e00c007068100c11102044510f01c12420030b908501e8100031280100c492251541c1101c8442c10305a006400c04103d124607030000d04041da00100e015000351605074181c04c002000d54900400c4443c445078049550020702c40100610406148040d04854503410142c443d081e0584c1c010103040701031428000080e211a02c00c2640640c4550f2585410020038203640d515118081e100c2101d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591405656 1250 591404406 591404417
    0x9051b03100e060121241409071103030702060114060a051606270201030c0302030105031e010e0706090e07020a050604060515130507030f150e0c07020a0305100e01050c0a0f 76
    0x456204504010030001e1064680c00202e07101000d800c21000445803a03c41c46c161701c03409041203015101d49614018400864200200c2e5483d01015128180501c1c079400c038922022040001e015000030b0130038103030b03207070980e10071011680c03c81000b0442c0b065040790000507000380403401624801d6120545601c0c07140c03001268507507020078542c83c4140c56556116a16a400340c0c3c3c00e081d56018841e0300c901103d54a010b515540c140700109a688207812590064a2410281800464029404194564140c2c1c083c2c07010f0360f0362a0f0000f043e0365500d01601030401903d0300800c2d0442d0000803c0420f140d448009403a469070303280c541c0001844010411140180328a0001c1940c0d51040f042844ca020070135800201401c000c0401000c4a1151440c0000301c0e00c0d00c20b4514100940b103200300c1c22507481e50030070b00d065900c03844a84043e00a40000a4001c0f00103c808410032a000c200c800c4806440300c41000002c12440c101801e807213080c1c2d00799002800c2042070f02c503814400d44070b4842024450504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591406906 1250 591405656 591405677
    0x315030a05030a030c080f0601080907030c0602010e0f0705030a0b0a090f2307030b161e032009150309011b02010b041d030a05030601090f09051b03100e0601 69
    0x1090a008080388112282e400008140b01c03a581c00d4859000c548045251121580c0350941d2074040c48803000e4103044c14461403c00141d2440b00070042d11010715440940500c400381c1d034a0380a40a4601c180095800d4000c1410701d40110100141c0c40c0100c6100600520084900d17444180358803c0150118510580340d60f40d850100d030f078901c0d1003584284a4204035041c15908103003c0032401d030f104044840b03130b08030356810400705059040c8590040405c85200c409c45429440c2501c5041a05003403061989a540a001071540c05902c64030900c0341d001485001d6950340d000f000322512942030700039030099210303014806001d0780b00007441e0300c29483d400010b415480408000300f00c1d00240300c0000140e448250348080d50a05000b0300032f02e01050908100c2c03405005400503100c0c0544a001c0041000203c00581c4680c8241d00c9000100303505038070030301920388680000010303090440303c8813004911039007100010038a40040300e10030302008103081103ca080c0b8010880d060401f811950401c4401f082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591408156 1250 591406906 591406909
    0x519020c070512150a05180f0606090117030a051b1905070b070f020409022202040303020606010f0e040902060d020c0a02032506080405100204030b0a0501080d050f0315 74
    0x14a000c0812000809a241c6841c0810001c1404181507980303603005034034500030010549080c03a4001304014401b240540e14507940400200212202d07005501c5510140b96012001241f86400b80c10183d030340c001d80d41c1c1c80705114008e120300a0201c00069004010704841c09109001034405c00c010405041080080300b0100c51600c880f01510881c0100000c00200400c00100081c4004001000c0818140500c54136088039a020b41140603000300c1e29a8100c07411941d54028a0b0022400d00e01c424282c1d401d50040d10740290003e000417805403140d41e0100d41258059841184c4100465551407540304801c810b000c09000c9506040303802c1071050010701b4103180c0a001030a088540e201c010300c04000a40105844c14101d01e410740300307007595070500c402c0c414248665041681d440d030601c4c1354592503e2814614060140c1252410a880440c2c0801040003455100e03024105070306050050b40d8031402d590742c84400d82e05032800401c2081203142d00750304400300a1580f09901941e2071a001c1c248030b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591409406 1250 591408156 591408161
    0x9050315091c05030907090b030a11041107030507110f0901050d14030c100609230903211609050303041707150203070b0114090720010f050126030306040519 69
    0xe01240200310f020041010b1000104941401000005424040700c00d0f0350b0042903c0e08001031015010400d14110031000c0e80b42c9410400b684113950003400e0b601c07041800e004110b0b0b080401c1c100d801d02211005e4044500e0004911404040010f00e11a01130f4a060104803082c0300d1114112410344402e500300b4036070a014030107062032201081c054034050080e040290b00301c0711143c2240c09480e1600c00c01030940740c0701c1090807448620920011080f034031040506403940c000d00b800618040e04040340a0000c1c1c007203011f40c40c001d951001030071800104030382040d540341701240206a0540d0040c401000b04510782c1c050a10b05003115000c1d102c1c8580c841c5104905141454a0440560f00c009601010000c0481d881801054070b004403492034401c480024001401c0944a03000b0044c010b034000101146044a6803403549002008000d502803501c3c1c81405880c2c00d116003501000007031020440c985180c18481c00c40740ca9100078516680e541e00810004050103802111014405509809050810b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591410656 1250 591409406 591409453
    0x50702040b1008161e0e0d060603081207030c0e0112151211010219080d02040b180102061506030103060c0504150302040801060510080402010f051909090c0905031509 73
    0x55482c40f03000c0c034007950b0008800d1800d419030410032200c0c0950240349005816015259580ca00c0e15500002e80040015494411134001410139481e20000004219a8100a11340000076000d856020350341c7c0241602168283c0c82c2039000f1070028050020b0780e40c441d0b62a1a40c513070503e00c0010b1300d144540c51070810407010340c0018100c00d1789003a4190500c0079501c2d180c50741e143e09100620720b2400b070200748142542a401d0081a000c0040760032064154160103440c081d100040f03501c1e0f182c204120380d00c43d041c0110100c682c058054440031816400b400c0300181b040d0b07040078081c2459a4616a01c2400810050b0304075401c100d030030300c800306424130300b801c1d1140e02001070340d00943c8403400d008849084500540c88944901c1c440052241c44540040b41c01c1e83c80303030702400c04100070b00c10f850003030355240306042c881c11034450380e003244102698025440e101035608004007002510001c500c1644c0000039030080e82c0d85175000d01c200c0450305134003601c1140c0c400f5844042d1000d102d000c80380c0c1d6051a116 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591411906 1250 591410656 591410689
    0x30402090a020c0109240e03161505041203063804080a1406010510080f100f0b07050c0604121401180b0115020d080a021803060a02130b0f0307050702040b 68
    0x44504444004845005c4001b0040b0590010040c03a00900c1d035180c0d0724840c0981502114a00340064014001c0b1403003009280008100705111500d400d20301483c0250610480d10082880c1071004205080b40e40803c9a28190f070310385199808100c03426410b40e940d0081108a0885000c010216000805009501d40070b0300c5899461001059924418102001604940c2c0940400100c0440841d40043c1e00ca4020140074555201512280700d41c0080300070541015401d00c42c555400106100141e00034280c841c0220140d820460200007002480e100f58400d44003000a803901090200d400881c1d040c66200007040005040c14000044518402590906407511684100104410744903000040035803000c51000e0702d044c16907010007a0050310080c10002c4e101e13038089802c21407000440e0420810308002008ca500c0b03443c00c51180c0000c0d5000c4080e140d1181d18030640002c203548501c0583d2465002c062195045a07079186007100c1d02e80010700241e90254890102c1d10550b1144074050401c0c141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591413156 1250 591411906 591411923
    0x12150903091d222108190b0a0e1e04110411072102120f0d20091e04051e0915011a07080f0a180506030402090a020c0109 53
    0x182444100744900402d603038100403042441041004a03418920700e0b81c061942100102c15501801c00504840504509820800c011001002401c0e00300c4e079103512900c0c01d0f14001080c00d2144034081d00340c4150010054020000c8401401200001d9600d954000460395501b1781c2d503074056070b483c40b900c80b003038405030f4000c0340c1d990007030319681010300951a01482c5440350620303000f581c1e0b941100d0303103d0713203980c031206000c140403850b00040c0309016008080c1d904070241d036103608810002040545c02006840d03c07a40c0341452450074045804440000c8060340360403603040c405540306021890918404061100c0142010194030740c1c0c99108150046503040548161140d54058000e91000d0113007407010300b0b0780946a0600354a01e507a82403419039407503201188800e0001c100c2540c180c0a417440042c43c3c1d000210f00700710402c2060000e007a082d0519544e600070254201d00126090180d800b406800100420001d40035082161000d6080b40341800c2c014500154a490300b400c40c1d0a40004540080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591414406 1250 591413156 591413159
    0x705010b06161118040212420c0a050307020705120109051e030915070206190e1509010522080a1103010b0616060b0d0f0203060a05010806011215090309 67
    0x5003d102c503c0c03070b8100c02c1d00c2d0300007140310301d1201440c0e440c40104000d2003010341c00da0b500c414410500a0450303501c007040403185da007603000c070107601c050800a0020312210515a504003054141060b00360142c0602060589020003500d822146548014403103c2540725000e40003d0741d44940042d401c03441190400000d4003020740c504035040100240c8082d08070034003210384081c441800302c1113a0140b4400c65502817100512605e50409000e90b00019500040200d1b2825407600038012904143c5080d640e15103080c68480c0401900208124880042d40000d1003103503050350090000b046031050113281c2d02c0713106000303440703258218481d82c00134400d68200c00c018400300f00090291050350101207009010407038140000c6013607800f03948490001564031070880d2090015a034001c132104000030f4956404c0c000d141c100102510003108041f4060f10030900003490701c0d0094441e450503911258042c00c841d918158200d88000c3d8010019038002100007505650020a0720900380481d11946941300c485 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591415656 1250 591414406 591414413
    0x91508040605060901051003090501140921031006110c0405070207060f031e0902210a020909151b041805100e10091505130e01050601230705010b0616 66
    0x26040a40991300a40090700180619030780d0301d00540070050280750010f4416034030b05055015024280a203100c13101410300344400c841001c145200d41d4525070b0343c0328900143c1d1450219151000b15080c00c00c5089400c8280030301d6205800d03001c00500d50f81d00710703044140340100041c103d6400340c800e60056480031008120070f640007003500060914030305080241c20f00c80300203030002801d8940e00300c0d0026915035a45c401c555a881c058141c80c0580d01c40d00d00c0b00d0039400e2485966551412040c0e205148660000f1100c5a000800c3d43c0e114550606c04152921402140c0e09800c0c0752411007508464107020202e110070780c05150301c44c40e0250001c0403074281401d9003210070042064110340c004640e4031003001344140e510043c03202140c4010000041c0362004c541482042049904441d51055401100d104214025040110b441448100820498030380d0300c010740c0d18000403954038111180601034500d4030b40341e04002d0000d43d0b001e2000480c5030b034003020018249074025120b600b4603d60200401050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591416906 1250 591415656 591415661
    0x609070e0114031015080609010e0c16023c12071401170403030525140313020405010e0412031406060702011101052e051f0915080406 59
    0x8050904806034203940d00000d0504507228141c06031948004041811856640c0d0000020032802c0314035110a404610010004041500c00c0c52250b81c000d00003041118850b2081c0340668400e86189143c5060204207070750071040c01c0c1090b82c0c00030010100104001c40440882c403080110005d0301d480145080c0c803001c030b2141c0c2c1d0a01501803e03110390184040700d4005810004d54407004015022800d100740120740e00307540711050740c00307400800c4144030030150581c000a0240b090400c1704084107824081c0700058100c208402e000094441e00b01c1400035030380c40021a04141c1132400742c0b43d2140145c000c00c054800c284c0c40321b500710b0748100400003404000c1000386c95011661030203020803508903101c44400e45000d0f00541c41194002444002c583c09021b1070340d14050080f00902041c0f8240100300307890940701440940c8150000c8424440c540141140b500343d580043c2003940201c8994a038500d2107030001c070740d041030001050001c50a40401c4000d2402042c2c1991800c40ba80361901d4080203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591418156 1250 591416906 591416911
    0xb07020406120201020c1203092d2e110312072a1211060a0e010c0201050f1f0b0309280c03031101060b0304081803060403050403080a091d0609 63
    0xb018001c8029a00061303034082410042c1c104200e0305281c8840d61500710710300b188241c00d92070364820380104080b921268404042a064003003207801001c034680701c1c81840038443e40910400100080c030064041d9241a4035002550040c2901d0038084c2000301242c4280765502c940d24111b0741a03001801c011020b5072000b9400d0b0000e074102e00060208440451a00515400b400010800802d5044003403a240c401d22521a81a402a003159000d00700954128001c12141d2900c911650800d40303030380c80c61401401000d01600d40d40402c070350b1950f180c40c8114541d0300ea804150305d00d452003d5000031600021400b035805500d560029209650308000505a4042c540d000825940e85551354400030403240e010308812aa01428085042c2e451030f0040d40c010121900105c0812101009000031f01400001800c505081013448081d40d00c5030500305a607032002154000c00049080005000052500c2e01030702d41440641401c00030540c4034000b41d200c012000d03a00c43c9190415408010740c41c60813070304c0a40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591419406 1250 591418156 591418169
    0x1e18090606070b0c0d091b0e07050c030913090203030a0e180c070209090304150c0c060908071811040e0412030b030c0402160f080c0105010501081e07180b07020406 72
    0x620b010140c2d5182108484000c0041000c1140841c010b2619180394010115032607000b031b40c0480c00822403401009000c2c060045409880030280001c00381806401103410000c14200194201043d4004100000e000e410741148100d40783d42058005031001c01c00340c60ba100707941c5c9800c10001a04820f1000b070384100e0b8074401c04201110103200500c60400b045658094041d80c88601030754038495820700c0c5d07110395845040c48291003c0c40291255210152100c020710404100580a5960308212125000c0e40104801e40d0002e003410085c101c8228401c0300b201842c0740020426050351a1681c000d500540c2c031803426424400300300402c0203440380003400140140d090401c6000c040d04042070f41c2d94200800740f80240d90001d400c0006502002c05021365031340c002052440c902840c80e10b180b09400902140c0d40542c02c2900200d03a560007021014811801b0205140103c100654000e03d0442c000c0d001c5024488080784000c11341c0d081c0300031f1002a21043c0016544e602640c4107010031100a50b1191 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591420656 1250 591419406 591419419
    0x170c0103090209010905060a031203020c15040209070c0c0810050108010c030504030806010e1f051201060c020303030c030c1e180a03020a0e1806130b070f0f03021e180906 75
    0x40140d075003686060650f0717030300500090156122404680ea1280a41002d444021801d94015a80e541a0000c0100c4c4020f0000d1780c582040303030340d0080d031010f5081da00298000100b00c005030025100c0c01c90780161500a00320004600d541d04000c42c24000e0340c071501600d280d200c0b801401815800d0150107012220b40c81c00304414030b4691002084d07014090506410494a06119a496994018103501c11180800d48015400c43d40c00094455840300740346201400224000241e06030203120311501198000d0041d514644c3c2d0482c000c0074650004203000e048403c03d1000c00103c0c0f030b9113150306403003418102c207055036914607207035080006e40f07850900ba00c100c0942c4014001070300c880c0e614404a801c0190f10744050b440f07200c151014800c240c1104c642c2403144074100b0031081100c802062585001c7c40c0c01484503110084101c03496810804454085a9259040007800b8070079070007130000304d050102c0848103940b005400d0200d41c0c00034803040d118521110b00b200f4140340028005420217000c8950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591421906 1250 591420656 591420671
    0x1060e06070c0519050402040f03170a080f07030e0609061f05060405040c020a050a030e0f1e0f240d1803170406020d0e0318102f07170c0103 62
    0x4410041e02c09005581c000c0c15000c480c08003d600c1c204412000d0103000744295251525200c0f00c040060f160300c002d8490104070300000b40c08038100c104a804985007076845c8101070b51420b03140200580054032510402d640d400711410600400d10200b402118001c2c0504858100085650398a1003094001e059800c0c8082e4100855a039a0b0122011280241c8000c40d0081c4117a0003641032003110b410280031401b40095500030180c0c4041c400301d40500c115100c2c69005401800c0c04204922800c0c500c1c00c0e4500d40c07139903144526104e00369151515006188440710f910070710030740080c1507120340c9500c113900d8040f580003004c150602403102075285c0c10000c9503c0d0032460b02c0050036800d280b064900307260600404103041c003015804550000043e12020f020081c4282d40c00ca075250b00c485e12822a0300341c91403414945141c0f41c2c00c103402c02c210b41d90701c40d05170380d400c00343c0d4001844940ca250f2002e868400048000e401c0240a420300402c40c0300000507070000e05640d55800d2024000038541014030300300c035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591423156 1250 591421906 591421913
    0xb01020106121502120c0d0c09030c26030c16230108090723040e0a0809040c21020c07060503010e1b0c0a110f09090a030f05070807030801060e0607 65
    0x34418402d42c01403c8011214405001a00240b0966001e810381d12030200c1000b2401716840c004141610130354108010301c0c041d461044881100c24000180b4002e10070404200c480d901c038901c50085400c2d4503045001034280c910052840d800180c0710101900080d0100390221013041100e0020850303400c04000c40c265000a04540c07051204a450601c6100300c007080840034104040c8000c0c00b14440300c0d9140421607114110000a840001031040303082c281d41002000010901c1d6128540c44104181002150410000505202032442c0100705400712402101074810b90200b11894900e000140c0d15540e0105141c2880860303001002030010800040001c840c2d40f0503802d511244e940441c28010000280c44500307803240c9480c400b05407096103106018041c4410000031b4003802182d11480070020f200034091101c200719191146030f00400c10f9040401d014840b503071883d1000c0e01d4882d1800c1c060b43e6810100e500301c01401d4001551101c0180002c0380c00950202c80780307c04440c950b0402c50070303a8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591424406 1250 591423156 591423179
    0x1a090106141908041211070b09010e0402030114100c030206070507020a0b1903060626071704060e0106052209080d1103090c190b03040c17100b01020106 67
    0x8039510070041c0c580a4aa0500380580c00c1d00c54aa0801c80b94030602c6000400080c0044000e80f0181e403c0056501c0074610301c2d000d8041c09041c541d5000140954501c0c0c02c0030364031135410070700001d070500c0400c42240b082540e40348000d6001e06203082c0d2051903002002e05011010f244001540c043c0a40700c1c1103600460340006425a104001b440c001d0b955061500c08a41c001a050f84612181040403400d01e401103140d007650076000e401136070708200d59a5202d04c1103172928807000b407190b440114482800901d941959515034400740c00d06007080c0f4204000c45045100a003110f007554003d41d01c011001400d40d082c0034031401403404488008074038415880784e03843c92034075024540c1440e035144c070404104000e00e416102c58403c0f88004100100c00019031a14903131040f80d042d01c490295640004187c6000708a6044c81e408084040d024281041e0301e401c0d0070390000c1c1c030076600600242030001d06090203841691900c8102d001030b1190b0220a4a40e400351060840c00c0c9041d641841814089200004d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591425656 1250 591424406 591424409
    0x1203080406020d09060c0e0f150409090c0816090606180e0a09080c0318060301030f0b1005030106031203050f040b160507020a1202030f0a0b0a091a010e06041a0901 72
    0x480141d80f01c8142003000d004103078a4000400d40d80c20840e9a0314040d030406400d1820712030a88400450200303190400c801462a5a0324406408007400240f010b2102079000c1c6140034800d0010f090440c0d25200b02524120314a0203104c5160914182840280e120f03007e4140100f4540c100300304d081c0c0c54041030301c5081146014001c0012000030008000604940211138119006540c443d61900044000341e00e13917000c00304820004820120360711943c00e100b02240d04032a0080c20100284205035a840035061340544013a810b841800c6020503181d41c20300c904001144911b41d4121440e2089030064241e400c014492100307070403003030100004141c00454072940100010100c42038404200b40a4a00d800703138180194219144040c0800c4c038064010448250740d0007101155820110600010780e550740c000030040255204602003192940250407070450684511700040b11a034401100b445e50502c00d920086160501c076090000c80c0c1000d1050f081c1000c0614800f00941010002040303910006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591426906 1250 591425656 591425663
    0xe060313030c0c0b0415111c020f0631020123120118110a0504050f0f10020106090c0306031a0703140a09020f0402030105100e0a1706090712030804 65
    0xc152000003010300c00c9500590707060b4014486040103844007101000c07604540100c03013011642c000420400c90280345950900f0b0311ba00000d05141080c000c0703041c00211220500c1c41988280764020010440500445120b445101d06143c20040002142c0010f1110017620039070000c002d00714900581d030700c45030415849001c61b80340480303880301d4044d0140c0342c800c8130600c0766060500340020441c452401c4010840507010841807015503d007402400681c0300f0b403191a00441c504100401c42410486a1901c0900004000980ea441c1c0d03640820500c600c2030f205080180d54404050003044514498041d00f604075240420006096a54000090040030f170415000c0b00385800044c04070303103e60003c0402c020118000072981c10000c0c5160050602c2d050100e1259a0004d0000138905043c400c0d24101c4e800100101d801460500094801c44401e900030750300030341203250202d40b50680c68502c00c03107000d007500205001e00c0c0401c1003905180a5410420281c41c0c66840315010907880404180c20580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591428156 1250 591426906 591426931
    0x50c0304030305041b030309150e0105030115091a07030815061b0709061206050604020f090f1206010f05090f0c042c040602071401050108100b01050d050c190e0603 72
    0x40c3c0f420046100c09040c00c00c145e040794203030408420140d200740540100c03521701c800d007600f21104900c2905c08070710108225000440c00e00040280d040e06061605000c0c105040100d621515154804120b41618900181c090b20025000301055400f58032a980060518001d00c0349214600000e030861007003002007400c049110340c1c0b2803c9800140030301e00003040c04070801c0110031b0f50f50110303000580311404c00362070b0b5900e000001111418075000321040204030074191440c0804200800007040754400f041da42140c0341c00da181081c0c41041203618060068031400c90703040303840e0008025450100800c0d40710b1404030281407151070103c40b420f40d0300740c40005030081c10761003e5003100202d105055241d5180c84051780300744003c0c8101940100010b5010705000140c00700300200d2603081e07070428403807000c0700d03404030140565201d0198845a0202014940a0b20b041242a54841a103000f41e5190042c80c6000481301040e440c195441c14040c4203901705542c09000d01000202d69020042c0414400ba4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591429406 1250 591428156 591428161
    0x4020a0903142b2a030909180b040305131428030b06120706050a090b070b07030f0207290f070c08070f080a0f0201110c0a2a080607080a050c0304030305 67
    0x80c01214280c52154013107945001c26018015151850b550114040d0041160002c000c114910203000d01f01010380d040b0f0000900016550b03a9840d01c8400030004c0d010000c0602600e6140014007040c00c005010440c00c48016113544810132000260a00d00000030050703010142c00210748580e030403011690040a40303480c551380e040100b030007040e1301c0c030103040c10b1702500e040421035139088806408a200c150b52280c88940c0c591910b1581840750080140c042a01c010000301190300c25046014881da0760380025041003600d5980030860102600c5080c1d031404400714812001b0b400c01c85080e400500a04040b54904000070b0143c076418421401501c680f600082c6641070006217070303000c02c44039808007a255a80310030301401042c052400076050019404d00c9540003c0724050815030380b004121502400d03e40501d0341d6942d90720000340084c0b442c203880890044450f1200340300d002004017041406406140f43c009002810028003d095100c95443c190a101e0b034121400b050b01e5000f9418140050241c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591430656 1250 591429406 591429493
    0x10b0d0e030c06040614040203100c200f10090f0f02010323181b01031d011b080901020414040f09232a01050a090504020a090314 57
    0x40281038030118031440005850b141110000420a1041e800750004100c800c901e05201580b1400507900079501d64051042c000001e07440d54001c8400740560300340703600612400241c5500d0b41806100325012500140d01030440000c3c20b0003c1c81c403038201c1303000070440401d940d0345512003216040d80c0540048200c880880840e4003a600510709440700d00340c0103510b000e1705002c0c010301d0002181c2c41c40103040c03100c0307400201150008004520328480c2840c4482128900d00450040c24071180f451002c0c40c04030b081e4032200301c007881b403940c0803014520700c0e070324482501d0005054041c01525880c09a032040004014500080611019401c0101d0380820040751040c0b0311000381a03480405071550741e055465140c42c0b031001180c442c2140782c135400d0702ea100420407102225901c406c621489421010390580040c1d40c40345005000307240381e60900c40100e6886130302207030490b0060445140401c400c1c10007803042c40519405e40419a00758801040c8984500c01c0250740b51840000200502000c4400c80421 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591431906 1250 591430656 591430661
    0x7090308180d0b01030210030c0504050f060d090302060921040b030a0f0e0601050f0108040c27020f1309020304020a051215160f021603150b100309020102061e010b0d 73
    0x988000348045001c042c14100b0b284000400e2004a01c074041964000a0180c00780c029100284d00c0d903140c59041903d0035040c49881d1a10144c416070020040000300c1850846200e02c00c4194029802880c2030b00e48a0300c03082c42c050f00d01c52145061031010120b4202031a450f01240d00f42d400b561001a1291074100322800a02041c0c15942c1501c2e0911000d40e1043c480040e42c0c2d81240d50841d042003880c0c81d4a801582c10b010184c0e009000d400401005012480741d0300e90700410025400b040c59800000459042c040382c2002815100e0500006201c0e420001c3e42400311002d015400002c515500f8264000b480005140c4120b0b8021491004080d00c840f405200000c0c1e2044a6010340c00725107000d2203240c89448881008d040860704071903c1d032311580c1c400a4100060801a2040c004207801c0d910b810842e0401740e039900141039140c030110000c0c0d403182034030202c03041030a803004100c03040e40c1d2002a00f0100e0041030320010030510300701406070500400c002811501142c901aa075109d900100102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591433156 1250 591431906 591431947
    0xc05040e0106120f02160b0618040b0402060705030406180509160c060b0402070b010e1807061d0a06050c0f1605040f0b210f0606010c11040e072c07090308 68
    0x52010402c0c4004506c40c03030074241a10b119111000365a0703200c908101c9850400c01040a2100a980c001400208504d55603900640020900d9042c240d0660321240b1b50360140c0c001c1d000007520084403002d00071410400750043d00040342d19480798640390080d07900500786840c2c6d6004000142480c68144070b4540d01c18100c40c000507000355540c004506100441d1642842442c505003800000903012069501d21404100390780005402e0035443c045c2c00701c0d103050b4a091440c1c20000390450321503595031905c2d0408010841600c0d40b41c0c5695105180302e040070361301c05114042c2d402004641036040112008903007a030b4021900000d6411140903410000c0580c1081c56402030704101503141040541d40344000c02950910454800c8041005815215102035807194007107103d4400c401c0004106030482603240502a100103a000b80398040035160616541c0700e10301c100088811401c0e40c480c11703a07200703000d8104048500742d203017882100184518264070001e004480c002c42d0036264165000007514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591434406 1250 591433156 591433181
    0x70305060f0f01200c0307090e0307020603070504090207030c12030603230f0636030912010e01061e1a0a030c020f061f0518150109180608010c05040e010612 69
    0x1001100d240f41c08507a05c2c00c101860901c2071046110000d041081d40c0545015111000080c1d410402c05a09000e00da03000036141c0344c02e200f0140404200610f141c8040c6c48440e00030369440c01c410f0241d0501450380c8032204040420141042d80500111748981d075120000a20040e81d04103007408242c05074117100440c0d0707032035500c0e004400500240084c68000444a909001880340b0080103079000320824610329681090103400c1400106001c0c90180140c4070303200c5418002113000480c010b41c0c1800c48049030448042004c07802e00301c106207101c180c410f030050950400c40c00580401034020310010300a180c5403004141c4c8030f55400000c2c61003445440706111500381107404600b00042c44094030160346000d0002c0d4420010006214030b040110158180d08100d030070112901e0307495420003082428921181884210040050712080b40c1500b000c111a03e03200000b405400e101d02107003500caa13410f0006c10420240400e102a410100900d811911182040c080e6000328041c000301800901c079040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591435656 1250 591434406 591434447
    0x30603100615080718120804030203010c020604030e040603030e060903031e071506270e030703030b12060f130501060b040602010e07050603091f060512030d05070305060f0f01 77
    0x81c044100e451040100000b64a80c00240c3e0b99400782160040d483c1840c0c0c5c0303281140305008100d506500300e103607074007a0f0082c05042c3c034240c2c43c0d8000c00c1c00e541c203035104400184d0104042205240c0d0020440380c00060480d0140813452858030000c001c420054421845400001441001a50204112078818150030048401c1c05202d02c142622600b010302c0035a1a1008103041c0b8031880c44600c24801605d039030b2903c4504005051903401155207c41104e5689159500d0044020000400140c007506100c0c2e68003240c1c441c0c000040c04600054510065031a6018100348031040040e640b207190b00080281100ca4500240c0c00d26030b001d454282c0c845040c0010000e030108429506411068139903c1110403103002c6c66a9905100309444220360181c40c54000c009900d03c1401c0c07060480341c0790450140041507440d210000200102181d00d02d030b60603580700007001c2288040d58003800341d0022403810104028a003c1021410100c9806212440b808504e840d8500300da0044007900103d003c2000354 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591436906 1250 591435656 591435659
    0x9060a120506070f020303160507060f2f04061704050a02090a0c08060f01020309010309080903010c0c1202010203060d060902010512070e010306080a020d170d092f150306031006 78
    0x7098494005844010000d91092a808111800002120b000340003000c03440510701a034400071211a00b103164110380d513544496003a141c849460154962000345940e2507807500107046c41c0341c0b110168010380701244140611041009a402c103014800f110101804404107590380c0c41d1a41c00c0006400000b07600000442c1402076014203a4088044280d59417900c0f40716031582401c0003015041c440340a80182c1c410461800207502c02d03003004c4d140300e11605001342400381200000b425601d15450800014107021500e20a011003140e0345a9000036078002140355080000c08596040f40d0300300003801c155120510780c021a4801c1044807403c0d10b42c14091400d5041088000309108402098240002c0c1412000b052089010803842c0c0015401003010b101c8440301d07500c00c65441c0920600d00d50040c0c091107907000d0748446000380c8510911400303000310b030407003503031005544640d000b402140006000d02494250b620744010f036900040c45000e140d0740f00d03a00c000c00245042490359001500c5810100c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591438156 1250 591436906 591436913
    0x512070809090c03100501050c07081506010212040e011203050c1006033813020909030c010c0e01020c04050402031e0703063630030b04020c0c09060a12 67
    0x2401428004441d489240c0e162142143c3e824041501d05070135000c8445410051503000d5001401001d03000c006444085a80700c101d030707082c1760480c08030500c100500303410400c10b9030341880042c4041d080c000540781080e04000c1c5107440000c0c14059030341c6043c501030659003858043c81c15104444001c0c4211007615040300b2482014101c107100450300c1040070110000301c00a082600c00c044030110302041d01e910041042c1003114a0090030380410b0460400030b100141e03d90340455441101e1840003541e980c00f94504032421070b1009050381080100e1510f0843c41603901040f0450415012140412a1b49840c00002e00b030900c4c0c1500b090540c0c030440701c011198440821050201c9006d804104100713882d054102c607041056510078210300c640340c072035500e0251500607402c1001d409021010741643e078808003c0c1c40022a00d100000030381e003602103848210f50600548152840650b019030801c03801401c025650043d1045551040e40300d98001031458803540030f810f005020010800c003440c1480d04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591439406 1250 591438156 591438173
    0x3140f040b07050f0d0516110402071b0e16200d020705040e030a0503240904060b0405280b030f100204050a1a160602090a0f1e08030f0304051207 64
    0x40e070803103c500409000c01079212011410805135a07440d21028a0042c0c1c4040042d010f0071200c4007141c10225035800d600c0c1940362480a004a10710540c01d144010000401107407042056500c40c03030102000700104150001e03010bc034150740c00d0490030404c9003501d2408500141e040d040c1407240c2c0c00d100300c2c441b4000007980001d003402143c0c4107880400c005201c1040450701c07440344076100b0010078400c00100305030603080310341d80d01d0306005091100c135000c0100001036030100041e1020f403a401d85410781e400e80c1d85018400c0e140c1140507241d040a04441c105820428500480009402e00303503180700f40c81d010b880501c4040c0440c044a402d0740c800c1d90080c590000290014041c040c0650b6810001007405c00103800c060382e404480360051410519400c2045006080600040b40c150b5000e2264061701e440b8441700201400f004130b581c24400c0d01f409804110b904000030300384459452410b04000040c4040210392407501c0d1440650390340e0381c039400d2451800c281302c40d402d1200e92000030355205002110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591440656 1250 591439406 591439417
    0x50c040f0b04121b0306021201030606050904050c011d09010b0d05060306091b061213050f03091c1b0f08010b040c0e0904060e010905010902030d02160303140f040b 72
    0x18200c40c48280c450000424502a6009541c0c2d015030844207400400e0301580311480741662900442200b41e140d40e610026a00001451215040040300500030081a8010000a00006e45400d26946896250380c0d0381c030800c4406050610518800d01d0140381b05419a0002502000e8100d005550351454640d140d40d1000350018502e07450710000c5040d80c9800320300ca81c09903840300010164460101e0300708040b00c0d1141c03019584000208100d41c40c03280c10030015403055000b1a0742050b400301c10305102d800c008844140c146260801c10480d515551140103005403410082c1581380740703080516004500081040e03a42110310a0b6200000f6003800b004110000e4482d400000c1c400301c1d0b00d200c103220650300200c0c80d00004c0781460400720030070308150f000031f54051b008140c0403034000341c0c80400701d084408903002070354965140d10b00f00e010350030200248109030310b4030301c0146040c2c4070004044103032107414003009080002003c081d1008800103015540c0c3c1c1c0e8145d00c045955169100540c44099009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591441906 1250 591440656 591440669
    0x4120203100b0d0b0a06091d010c020706170405071a0a1805010512070c140d2c06030406090b0117160803030c0f0d0f020913020705070302010c060f050c04 68
    0x801d014140c2041d4140035560721004058800c024031181c6607503000703000e407000302041441c2d035840da4001074410481c041e01034103c40c0149440f2201c2584520b00d42550500a249015580442002c00004d9071007140d44c0301d00ba0440c44c030507590b5100e0f0301d03000b81081c2450b442004140305403541d00d00b040384894020080d1301241c2e01c851122003800c10708610350542038803d01e4003288043c0280c00e185403180416551000d444c0c03800e16850b003215615101082d00c070703400a440e40e50025540864140d081b194800750320441c050070910f0070110300000b406200141200500a0b040480800d00300007282e04201d0321150b01420021080d0307181e400d88040a1026186603815200d0340c030140b8910803000d4165810f90b4402e030051071452381c0301071a0031070300d9101001401103a41c00704007080c044000c03803240082c0303d10702040144c0e4031004041004a604d0030000d050790b01c0c1d0720401180001800016010382105da081c00c20b82448543d500b0042c00404003038485030704040c00d000821010701c19510042060310b21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591443156 1250 591441906 591441913
    0x507020613060e1e0d0f061419060801060f030204020c0a0c0b0913050405060414030408060a0e011d0303040303051504051e09011505060f040b0a0c050c040b03030919080304120203 79
    0xa43c0d940141c3e4007800498400c1d0070010039045d480110300780c107126000c0140110740104400c5181050101c10704011030381103203000558000c4d010060003078080e45005000200090205900b880740c6410142170520000780700d05d5000545030350290061004800b069085904010083c0e40d03001d001e1415801520014410b9450210f40f010050381441182e00554018000f80100d988542c0d400c64101401204000c1d5488140000900e610003004800c2c46030a0052003c01c2c1c00e40e05102040c20b603090b0443c024448081010f00811a0500100fa83d078000d0305403501003004e446000420300c2d00c1c1e09034910036400508007820001c84c0d11155a0211008905450b00130190742e43c410724908036014500c0420704d4005007001000949071050281502c401e9403a0107903d021f940340c810440a500902c000b04c0801e020700104024040103001a07500303e8400c0d035003400419400c0c0e00107602c91081d50f424510856002d9a448440380f0303c1c4078854060f103c40f00c01c880c1d44648509900128030480700c0300720300c00d10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591444406 1250 591443156 591443179
    0x4140a0c0923090c0403030c060e0c0310150e040203060f060d020d0305091801050f0f0f0d051f02040e07030c020f2a030c060405011d030d0804150506100507020613060e 74
    0x3010704d822102200d415545800840c00340707a0b0b0b05005020010013000c42849205402ea0f02c9030303018000c0d00042c0301c40550020744a00e4002c0300000041403507100c110654030312070400015884c0480c030369a04c80382c075103142507a641d60f242c00a01c8410010070040c3d0482103044c60710b420141c000c001080c2d4a07504644c2c248284506480a21421100b40621500900c070452a030100e414090f481d14152800181190803100e03400020440d0840c00c071801360713540c0c0c1c042001017502c5a080c541081911121050962800e0304000281c1840c240c003030080010541e032205803500f460b20a00c1130100d0565018152101090701600740c450055032074140a8609184c034103415603c0c540080c1c1c110b9510400740410741054030b00001035503050880f010311001010280309059159900f88008001c0280390b8440351070a0601d410541b1035640c444040d461028502002e20043d035a501141591001003442d000f687c800726440404e101d405070510001501403401c1020450580021908150b003800307498409230304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591445656 1250 591444406 591444421
    0xf1908061e060904110f0d0803040615150903031d0414060312120f190606022d0703110a080102040801050615030f060103090c0503190b0604140a0c092309 68
    0x41002d4130000c01c05104404d840100c0c0c00c00071814843d40c6030080c002c03110640706d916006d041d07600850701140c4003581d5658903e1079010341480c1d4405080301d000c445030b03803020a81d0050209461400301a00b0701807a00081c005402803000700daa035407003028000b0b008400e01800d03640c01704d900a50b074091207030050351140550154030304103882030065042e000300419201c1c1040244901001743c01a100c804c008441c2881011003405520020046a030081403da0029482504c031104108400142d04100d90728038400c004000821b0f005503500200040c102040c1480000c0d4240e1251b03110002950011a002a08401c10351290303209040666038170508a8004060b1081c41c030084541b80480b80500010490380d51296020802451003130350300080b03064640000070f151009080719200b4404400d0752200030810000e00203904900c5c1500c0070701010001042c44c1181800081c0400503482c0c1d60410808047d04c6000c0d100010201a080c2400c1c1d00c0c0604414a5901300901d0313142d00072812440440d100c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591446906 1250 591445656 591445669
    0x42a0e01030b1207031203060b07080405030705060c0c040e1c090e01050916050306031f05041106030c040b16060608031e03010506270406260304050f1908061e06 71
    0x414070f8030409482d05a040da5a1600804c0120000000b05aa64000801c0c0210b0140007017840c10301640340d1307030f858525140415140084a40010380125410711000e5080c900000345048642c204031004961144c0c0e4605071351415116184000320f5520780c10b00314000725004540a816640040c01c100c0242c1c0e2a0130038040381280a03102c85880d503004100d00306006c1d1240c400f075a00b080c4000e09a03015003050508403425036001480242d400e603034036414001040f00491003000c103a0801d0354154194500400300044a0049114270711000c04005446000b04404000031402c89502c0f20007000450340300c802311641d076002040c44007282140712680030752100b9072000781c3e812102e005025910f03220241e400c0242e140c0b825418150803040c40e60900a150317427280501c00140c040700084510816264036030013444001c50102e0a002d0304108404d000540314141303011928082910310840c2c410820410f10f035100c001e40d015110b81d02032101806003412004031754410003000800386003ca503c590041011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591448156 1250 591446906 591446929
    0x1502060c090315040c030c150809120d09020a030602030c03160e2b150209130516050c03040e090102090a0501020d120f0209030307231605042a0e01030b 67
    0x10702d0b5015259810241c02e200d10b0b00c69019200b60103683d10b0603903d64400881d4550b50b08600c9421880c42922918203600c0590782d0350107000500141403502d20711a05406511a0001002d52161151a40e20a540341d074a429001198480d00440d542c1c5001d480b9682036400c2646c3d9505071170342c0c07016a2201d217031044802880d11040100300351182031828011b140014019420340449122041514000c54603481c2049041c070915a405070b82d905510702008485566095000072940c94001031094501e006040c0102101d0107060a070760358500504102d1840c0110f41c44182001021400c01800c660190080c3c2840141030b50803000350350301c6400582e107540c05150410700095215511490745046600410f80000308004014a4404034001003030451b848003d003910310000203075002a82c1000c0c98010404010340d60043c100741c4030f29540803070a1000d0352140e90302c215102c000c510003c071400f458410300c0f09900e024008040034070007005010700d55042c1c07580b40403e2030120110340c0c0e414020307080350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591449406 1250 591448156 591448159
    0x40302041118061b0303040f0b060d05030415020102041703040f121a070e04090c050312121315020412051b1c1103060108031e0403120c0515011502060c09 68
    0x30b01e0b58001e092105a40000c20801074030305580e802054110400c3c4015030003640980c0468001d40300a04080c0948840a411507005030032581c0c03803038041f407808410f690a807000025400140448690100d01901440d04044981010004084800c11000005104031412610000c1e40e4555a850240704802200e2014045520070500019224407050f401d170307800943d60401c1e6071401c41180c042021280d103010200c502d0010320405110500d03081182010803d4621081403515000c64407420314407201418010010b01e400c00c1403410000304110f0441381d0349116108549856a0340b07205000d4003191041550b0502848100034110108041c0302d5250180c090030256601e2880314405460b0b4103103c50594585440b8100406039035018411a4000c2c450400119210078102d4032041048143c00c550200e9202c080000300700080680003481c5201c0c3c032a0400944101d02400c0003803c03c14001114080142d07200c1c004644a554980341045080e0560308685c8507035240490702020384990318069 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591450656 1250 591449406 591449437
    0x8030f04030b13080d0b0f0f01021207170d09030e032a04020c100905190c0501053a0e01150905100306110d0e0c0a0303030510030f05030403020411 65
    0x41c00454a02c282d00b9030003640d9a1540c44502d4520380755070303a142d04403d00203000380380c40b8041c2c0d601a24003146200045e405c200c0e001106241c10030b0000c0c2d81c507090000c0c012200007010030000c09010b80403036052071202085000583c3e0b00c0009108a00902082408030085030542c1100180c0e400c0008070540000c06090080c484118108510340d4002c2c180102c40d0f43c0180c08001d0344680103c10b00120001e00c4114001060405451a0842c00c00400c004101000030301c03030042c103020503615143e01044038000c0c2001c0c1da0b03c1d4500080d15000c0e86c221507603040d00c0c0e15403400700c400103480400e10041d521102c001c00c000c40b00d00040b0307080c00d070313219043c59540005072500c0a1140310340e107911150f0040243c505140d591a0b9940e51441511008810580300c1c00010a46484121003406066110f400c0d05003d080d11060100004035086a580400740c00c150b82c940010702590841c40141c409550051200d50102c2002d240040d513952042c00100e000d541801e004403041c01440301501e5640c011880304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591451906 1250 591450656 591450659
    0xf03020c0c1201020c1507320a03060302030a050c0a0b09010804201026040b15040e030f04090e071203032d020d0506010e060d0908090316080708030f04 67
    0x2000010510b4400e400c2e150f543c2007080110b030070b000700180f002504440c81c60340d02c503292150010302032441d90480c2d01100701800540016000c8024050500307a00700c0c0c0100e586480c0c094000b100203211a8000942600c0380c40c1240f02800800101008041c034221341e070803216034407048240c1a9016010070740f4040340d0780002040010308001f1a82c11086400b00000c5803c0303040400050034018031905600204d550828503e804032211580e0540028207010420300d1070410340d940f0046420010626214908a0b000d039448035961500b0011030201500c0c1206d4460b1490040e0582c680d02621400012502c1e294008a002c4000f0800c13008455103804c04601585080d1800d40280007548a040e551801a410078102e000048a0980204603a10700c01a2190f00c40070800c012a1000380802d0b05200603a506410359980b003c007100e144680014010543c403440c2d00d40640d040c094402502d602d400b032801304100c44a41009044200d4102c0402c80d98925a11f800441e202d105120384900c20f04d004100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591453156 1250 591451906 591451909
    0x424050f16020c0906060d05101a0a09030204021c1b02060105030c030601030b040804080a0f150501210c05090906091c0c24090b0601090509060d12050c06010e0103030f03020c0c 78
    0x41c1c095005c3c0d0f0140a4501c0c050419030100d0484004840b80704801400410034011003d40b01c03030405030a4a069280c5186c8001a0750181010341a403000034465030300020f61000030034080070b01801c0508003140a1010580e1840d142e40403082c4191101d00500c03540000050380e2800003101041047c1c040e025101590030340c2c40e00c007415800100103a8000c4401c000025141400b00000c040d0640100e1100e806010381e454654188201815000e0840342094010301c001030051500050304688a10080707040762480c1b0786501e42030410ba004a60151001c020440c8006000c940f641c0300303184a60540320440580c1a882d01408070710034010000685072100c060002e0300f100c2d036481003084c170400d81d4241004d48001000035101a040c04640190960003840055604012254041c140484200c0c00c03030b1901c90b022036038140d0070f8040503000001420845007083d00030303003c403108aaa8079058424075a11030940042d000c1007031204800268031404031410042c0b0074401c0d1802110180701078402c00f20f8000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591454406 1250 591453156 591453169
    0x30b040b090a0506061603080709080102181009080a0b100b03090a032a0c03030f090302011407060b063004120e0f06040303020c04060501050a14030424050f16020c 72
    0x3c044c02d40181c01044403000069010508544480c400d6a400c00703649001000200304007016401100d45a0040c000010106240112420307201d00a0381c02c24880001e9180841e001001e40e4820441400b480f104807043c4141c00c10300510407189100700c408160f550f5001c10301c0c50b200440e011a01908a002c542c000684a00070024054491000440e01c005001040a40340c40442c03404a8030044204d00400416800a59040f1841d07204d0038264282444c540010b412003d4011340300c90f0400000626004004440d4005c000da82e8014100300d40b6a81c1c050b4070203000c5041104001c00c100c0c4a90286440441c04100e110700c510713800511010000580d5005550502d0341d207450039071000d0090004003264485170050002503000b540100381440401d0140011100f0303e411003410070404201590569030030403076014002640000c1d1a582e50341c0c40c00d000390303c0032194400f030542c08440540e4050b00c042039001f0324059140e000c0c5000c01501c03601c00144101b146407002d10b0240e0840040c1c00b9440c075140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591455656 1250 591454406 591454411
    0x60a020319051512010c1407140304030c03030909090f20060c0106091505061b101401062606010c03030b06030708070f022b1e0906030b040b090a05 65
    0x40c90a22a00c0814001e2002c2e01d204503501c0c034121015400c201e081e480c18030120720f05210440b000b0000141100d1004113202c2c1026424101004000380700820032030403506851022810b10b098030344564607442c0183c1200010300c41640054030b60003020070070b00100d11640f0391040e0b20940002d0240038681d14030030070713507034054444651054100340070a0300d03214800200301c0c4080c0c0b20000904103082400000c11a4000104420070b500030348024040f80e120401281e401500c40b00f1401041c200e6514001e10340442140ba40d803d180c10210605411251881c46605841a81d111282c4625103a689444080c88070300402c64140d05140100e8410350003580030900a6000c0e02d008104103d000c070104a080d441502c0c50b0300020f140c201006502c907440011440403002d5403001d04441044207a803001410380b500000318805403904100c3d4401030140d050761403100c0c510141d041c0f0764002d0560282618601d840751402007410100304910350700c4d03d44507062402c4002000c00c0074940340c2061410080400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591456906 1250 591455656 591455671
    0x3051212041e02041d1006030b0402010c05070b041509060f1e02100510080f12040311060d0c030f05072d051204060e2b0e03100e030d0b0a0503060a0203 67
    0x1d80000320140c2c0b02d034020a1505c14107100164840300380500641d14007903400e02c01c0c0c0903440c03074000c080c00000c4249098642150b02460603c108000c1030500a06100e0740d81d0043ca03113114001400618030b02c103149203994200c070b10b8071411031190303490b0403d031194501100d4040001340703141c1103404ae400d0b440741c1182c000d49213841129200b0601600541c120b0f003040d00c2c2d01e40c80c000000c0b810040c0c82d604012500d2900096030250401213030fa0030b8840700034051340c00002e2071a000b40e0b03520401620b600c0141c540d00026004103100318a9081c402800902c005182444000d040200261015003d902c403d80403002d50350010b0444120640c0c0c0782c8040b59004640d4040010400c4008101d00c90407544074000c9008003400100c45c610741411503c0c4c20360b2212940030840c02c0101950359408626000e0205034810f0401140d08600c910000781000007074a00c1040781d501c1d0111600c084080040039140b044000d80c41040f240551008021036801944034079a815800300c0d0010701100010b80146410025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591458156 1250 591456906 591456953
    0x21011205061b0912030417070501091401020c090a09030e060a091e120c08011802100c02150c0d090e010e010605070501180b06090f0c030c090a1e0305121204 69
    0x1e80c0d0f00103407918107444941000350b0b101040920816141e119140100c079201002000810302c1d041c000b07040c201301480341c43d92102c10302555203a564024002c4900c182402000141c1624103c40c01c20010b1484043c143c0018580c07078402081800c0c04000c503422460b25440c0d100c0c0d41c80c50074a450825601c0b184038625001d030754240029a40319498882701990b031007004244c44031070410192508440002c10500f009072540e40c0b9400241e10b80e0100c07219009698039140c11984a00c1c004541e85040c41c4200c90035210000801c500a0b600101d40841d000d42075645030160349646504071040c0e0701c1d00b070284880b071015143c0100405400340004040040c421000495560305c04014884601d02d40729064070307452884801c000180c5060700c0142d5100801000164090402c603885604900008003103550004000501c3c51150f500d845100c2c004200780a8403880220903480341004035400d42c0700445c6c0a10401c00001680c080060654600400710044041247d840b512540600450207035400e8540c0d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591459406 1250 591458156 591458167
    0xf0706090510090308090a1104050604090f0813060201150620010203010605120a0e0c040507090302030304240503160e040e01020a081f03231221011205061b 69
    0x7441800b03528070b8194036400000350900241070150170032034002e1950486800103180d1800007810300c141c42140c4030b0103480008140da00c00340850010440d502c4050032481300e080b545001c21514400910481207844090325040b9901c2e90168260342c03901e5492072074485211414044240b00c0c481002c0c840480c1c50314100a00300310f6a00608a9200f0381003800000c80c0080c031004c41c1030080164a4101444070410014040d00b8801c0541340d5440c45020b521981c0c8032070210705580e21460440015580040030303256900c0d40c94050f4140820024100c07807002000d50104000b4500900c16680f050700070340303441a40b0f60301401084a41c0e43c00900b003103a10590340c0d064010107000920240501c0501070700e81142e94108020301d00356031110602e8914943d09244001c2c030014004001e8884001d1401d440f111081110420541c00c10400041001400c140415103074008540f000d410a400d44588444909076600d50460019404003c24040c000c2d0744200c0204403520a0102000f60740c08074004a40d0424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 591460656 1250 591459406 591459413
    0x18050f1212060409020a051801060207050a2303070914011d010515070215041403070b0a05041404060b0c150f24010e03061009051e0c072427080f070609 67
    0x30740c0c250f00403804520888c401405881d804110440c0034240031541d0180d050b1802c0d4841c440908003101c290003042d080c001d094101c0e10208140070142520348001c2c80002c042455140700100c0034413444015402141d0300c0c18500410f00326060507100090b00c84070078880000d0350384413103900940c412030b00b01c105503441602c171a607010040c0014201440090b96a4400803042504c2c01c50150040c090f105d1301081220f9075181c005040314100e40c1c0e18107010b180c2d00b8010000a004013a160b121042400c0e00241c400001000800c1c41107000f1081c04035a002034880b000806400c00313048820003002c0070300c0d000110b59801101c5490300c030100c0524140741c2d1310541f0030210b030426106030703060510806d01180c1446200018052260702c0b100c0f203421220202984078410f05105400b0301100c0402c0c80c001440c00500031500114898582140580c0c3c60510542a60100825550a03000c400d440c0c035801c000c00d4020501035401d110380d04201d4090500c0000e0700442c0b800d61202c0c8040381d429590300c1014000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 591461906 1250 591460656 591460669
    0x1017070e0a14060f0a151110151e060518120f0c011119210e0a05060315010503100807080303060a0f0e0406020a0318050f1212060409020a05 62
    0x444000002150640300405868001030b03025010b00d2046140c0e034103c1005440e82c4007942c085540034032905020405141059480900030000c0d00001e000300740704201100441d4201001106813640303078508596450314003000f0003001c0c2e1035120301035034804070400100380300f500a01090702080001ca0400d16040002600036150200d514850745c2214001d03c1c0d00c80004d000c035031070f04402800d000c0b201144a0000c42e031110707126007001c0104036280703404605102c00281c01148030b500a802c45041842e8001c00649483d64210b885845100402e2010a035420f0081c1500d0140031003144e204c0e030340b108003001940c141d04000c04004561780c0122000520901c00c000700002064900081c5649040c42000d02c88400321542102c0c0c002030115000700040c0b004a882c06034400c0d040200140c84200701c0000b1400b8081100700745c100c0940c00980d08050000108200901a43d814115050b104815952358840c1c0281041400c100000d100001c0b06e604154009900300b80c401003030968000d071600300280c407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 591463156 1250 591461906 591461911
    0x915120b0d050d0906140306091f24050c0606041a06160212070b03010905151f030f05150d02030102090405040b04110105040b03060f0a17010e010f051017070e 70
    0x707682e403083e0910003649401014000251102d803410014814400592111074840944900e0042c20348400058481d001c2c109401c1424801403842c0c81501d07620503840c90200100010760180300103412082125038025406c456000d0098000390805075034500c20000205000320700c4043c07410300000c160107665902c8000704800c48240050900003081401440310120444007a030040f94040c0c8001d0011405e04800c2c1c90444109480c040750319a5600c1458901c903103a5081036070000c3c012004c0404000c40c003003607050704031526901000407079405008035041d11416548542c234001c0110620f0b02c0c1e030400c0c95002a0740c0b800500054a81900003012504482c0308031003c0d5807c40b0001c0c01e05c02080303603507440103d0125092810300c0c1802c3c01c0c2183e5138000d12000c0c2240380b048450b01a0107000da203510039040002d0215000d5684a00c0c3d0038000c41d4003810030002569065460503580c80e4007060141324590180c1c5d0140a011001410b0401400441c1125102c031b030028444c0810018001800018051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 591464406 1250 591463156 591463163
    0x12021203010f0e06031506060a0e03031206100f0801060c0c031709030d05031005090a0b0a090f0f141602030408071202010806031b040b010c0614060a060915120b0d 72
    0x2e401d20388021100c2d0500082d11140c0300e90091004010b410502a8445030000802c07941c15581d0700c408001a10408440e010050f00746c0004a100b01c07025000c0e0080d42d10541c819a90b1f0012001b044a0450355052010240340102e120b500040c40854420000b0301040b030b02c07070520809619102c2c0c403080001002038a5280c0d0001f000280a680c5050601c1401d00da03e0803810b0050560800d0064001500c000e4000d072405003202000143c00000c180c0c2250b040f00a0103000882c5146e16072080c4000341c06030209051015080c030401d80400c1c00180300305404041000c00002c000d440c1c404540082d11800041c18085210078400030440c00e50900010303004000d40301c06011034086900c00035100d0b4200900701d40c4a50010203a441002081600040c107005003103400003800421980160b40000400c2e6000c0c0886140c5240d000c102404000d6490066000300e4034001d00b29540d0500f21015022030080c08001a151080119100d0107402142107400c4100400b0440d5410000856212a00c09000f0b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 591465656 1250 591464406 591464429
    0x1e0105011706040c0608040f0218060f06040b030a05040c0e1320010507030c021203181507020312131208030703050a06051c06060909200117041202120301 68
    0x100801c0d24694040300440302000701500d6645001c3c0c0b01c40c00304180521450003030180d1400094200080102a02e00040d4000c102c110010385d031001c0c0a0359030400325241da0249100708602c08141c5818403d44d1308072070300c00c28a0361555441c924010050040900120360440704020042080713140030021074450754442e1401d8034800c8803030420008104442c0301e000d03c10f503202c0c03c000b103540e64400c7c01c0303803420b5406061150010341e03148040f6450340b00381d20f0255000e010204031716801e040e40c1e804003001d40030200c869094072464400c10210758458044001c2d450703400b40c4041050102030070003825420481400240c841030341ea8040b602d0000591004817041c403000000c000c0d14940500c40c0907040b40d01400c1c2007081d5401c10300441d00d41400d042c00a0082da2002d5000010404190800005080581001c1c407210710039180c20101c0c0700503513908020750300000711500c09075407080b025181c482d541d42c0342241c415111502c034840c118800400c00402c5001d0014a5104c40807078500540c000c00c40315412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 591466906 1250 591465656 591465659
    0xf060c0f030d230105091e0a0209130608030403020d05101e1505010e060f13060201060501093003020c1518030f0d030b1201060e010e13150b031e010501 67
    0x400c00c94000f03403807aa00b1202e00704140045860038500c201d054401c1501c2c00d10545d26074444d0540b021011851000a26140c4020081c0d1a40f498010b0418840140d500c1d1090300c104080300d106503074490003001026402400208003510740519080c0455018000795501104205503110561300c244209486c0d1b010b0a0740c1c991980f072503c0c41071034500201c0d101401034281c14040020b0142621b10a61403143c600444c1e99182c1c038480c0f904440b282c440020b41001ca0030b603200c0020f8003030b106070310416000c51301000700050585000b44417040038a200c1d070011003030820814140081d101d0b11501c19401c40c424100200c1070b07a16101c603074165420766410b11a46840312003801d44c12141104904a02940122840321070102c4001482e040d10034086c00c0100d010780f442c001162844213121070b4510550301f4008001216041c0344880c074140d0707042501c840b8495417000c00d000403201503400024040030381d10400100000e25507100b4405081d008064a80d00188649c5900c51140c513811600080c1c2d545100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 591468156 1250 591466906 591466927
    0x6170c4005011704030f050307051b0c0103060e070e0613120b0414070602030f0918040605040b0a0902100c0219030804050a080a0203032b0c030b011206050307050f060c0f03 76
    0x282000380da604143d10302c0c0503c1c0c50b6a000744100c1007481070009000d0040085850350b8043c90685407083d42c00760040f540e8103014081703541d03140c0056581d640071910b022408a2180150b083c168450300c81a11130214403641241408800d60000307400c540292181e12001c102c0442111500e007050b03001300e003003c2050400b8201000c0703180c4084800c010560210108009140d000b005407940000c11880154465840c03001003004004840180074801460004120410101d54851405140942000311640e61110040f40898203003034000707035005600325544d100c883e101e61520141c0d284080e00200290a06450780c0c061064190000c4801038000b05052100741845400c1a0007802141e0082900e02c0301500440d440703200e41110f05d004411840030400200107298041440802864000c0107441c141640090040400d8618980014071400000c19280701c03e0048401340c1c0c030002c000d0540203240c201080324000005100030380011041c8280404d000080c002e17820310031001005103649100c00107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 591469406 1250 591468156 591468167
    0x8041e08010b13020c0a02040513121404030b09012408010e0a1e030c230f0c0a1401020a020a0f0e0a090503040b090d0203010c030606170c400501 64
    0x108650981da14024480c189a5116507181d42140215030005aa400c50545d006050214120005e50894140806d10804003841044c1e0031071540103d04110140c0f030a0740041317480c41c141c64002e0300044400c3c403081c004103404d8811550000f408400003d10400c00100286080e000c0c0112800d2085d82100704022901c020b0051231072911243c1c0103000181d02d250384034000290070f9600c041c40c40741c40b1005241014056149007030b000b0b82049114246013448810300380004950300340ca07101070107405044c0c81e018400080009440400604c040c8465041142c2450b99600326400d442c1140b2900010002680ba00d891600280c94105c0000f0b01c29814000e0810307800d28083e0001401611700282900852404010b99007a41d000440181c1d07110040c1001a00a4699402c040d515519000d0090001074055000300200d42c9192195010b014040a0a80c96610200da8010102d00d080042048100041c180c00490b0f00b00300c0111000792540441d05000d159443c1102140c0022101040c4034030340c3c001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 591470656 1250 591469406 591469409
    0xd020d0f0e060a03110706110d060501030911060a0c08030c03010801060819020f0114030915060102010c12050c0f041403010f02040302060a0c0606080f2104031e0305040308041e 78
    0x504100c203400590a000c9042d61040e0031040e4100340d41c1e40c0c9940702c001d80c02801c5481281d005a014002d50380300c410f07200352076480f01d03d84824941c41d150300029a03501900800751a103030000b007111030199000085c000c440c1d0082440900308000f20302c504c00040c5020001d0350099211391042c0c0d840c1d60401694a0855038242c00054083d840048040000c4440d404552401641940e004c155025900010788010101c200b580c2c1580c031010040140d0b400340010319134040c503800d140103082921400e00590894440c2c030703c0c220000703030b480c4000007051b1010340215420803032050a136031400c444201130318401c0c4c1050b004151025041c000240c1c1c0303440e0074041c200c41a008010214074251a5500140040c821350011a05000455102c50b0600c1050b80c8003a001f4412031081d84d2141c07441222281e115081c1c034940384102d42d032000020080b0320f00442a1802d480c2d018810322101e800e480d10320b0243d8681150100c041100800000c000605424007400c01018403181c2c100e00c034134a08c0440c848820340c6e07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 591471906 1250 591470656 591470687
    0x612050a05060303041206020412150c052113050d020a0501110301050901090b030703080a020304030201080c070b13140a2301051005010e0f060703090303080a02090307060809030c0d020d 82
    0x700001c2c040a43e0b4040110b4045410140c0310f55040e800c185060000790045070b21500004100741c6070740f4107000da02c4c041c441c150030250300d04001040f6226019074071401084084d00c050110321f6080e071a40d10302c5101d41a088200c42091002406107542e0303062a1071000da090800580102510b00e0400c0424011041c13811701c80c1c00000d0556040c9404501e40003414404c60904a44030340c6000364a44052217110007441d00314841039035903054420042e507a82c0c090310080f4006481c000c000380d0f15141907800d0f5114203500c1120710080d82c442c140070750b65680800d04107031200b041c190b001d2010b94408004501d40241b0400c20320151000e4400540c01150090340903100c2c0c0d9061400f00714484040e51004000e40d002402e1404031310120b600410b07050511845090f80003140095400140364128180c603040701d103c0d6440450a641e1040742405038092041d103580c045e8130119003031004070b00603080540c0c0551800101c90808041c503500b140340034201c688190141e0800320007640ca090703026643c030314402070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 591473156 1250 591471906 591471911
    0x40303020a0809191e06030908160312060905010e09030703080115020a0605040c05030606030a050307061d100605030606040c0815030102040e01060e03010b010f0f180f0612050a 78
    0x51610041c1d01d51654500040580030002121041035907120714100032000812507a070211900c803012482032034024040da4620501a10700090250301c280141c200060f071040c0050308056000704202101074011508070103101d140740c0c2e0b4000741d10703281c0728610003080c090702c01086951400031024240305c1d02414040342a0420419400800e4020114604403940a0398591101460a00481c1003144507040108440c1c1403805000c02c0c0f1580184010640e40102d05542568890104041d0380e4000341c03000400c00d40041c08442d011800650000074050300c00b0250505100f070b001c0300141800c2080300b00303c54266441c0300602c414201004400c0d8005e106132810003c50203000341c080d064150040c0b211b10031000d4002d03015030030345082d01528000e10705020640c2244d43c42e11000744c40300c00c14200160280d071a02c40703801400c0d07104120080188881d9144c41440200040085403030000b0308940e015818900c050000e881c145ca03000a6006040c1a0307203000000d00060462801d0b600040c124055550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 591474406 1250 591473156 591473159
    0xc07150903031d0f0f060d090302030301141f120b0a0902030a060e090307080313141f11040b2209090308060a030b060d06140c1b06010b030703020d3e04 67
    0xc8550071400b01d51113007160103030120000f040000b242881060700440189040a203000304040d0008040d606031060901c8000001107880c1c00d005190080d07644404e503007010203080a40d010701030a6000c0c0c0300342040202240002610011807450340803540f00e0049103a00004005000d80d680c4504800360400860b4200760342800001c00340d0341d0203480006031000d440000030864100c10007251201d81d60b0b00000782840c45841059043d100e031090040040c0c644e0004404c0c5000110034030031103480070700030341070030b07041c01c0c03c2c00d40c0e440c0c0310b40080c607440402e200840260200441c900f40f110004010f0810701244001d07513890010700c2c01c04040c00c424015400220b090001403089413174940c1c0700c1c0c000c0e14608070406072414075501515400c0d0b80300201c13440039402d00c600c00c01041b00415049003140160785000d06040219562344509100c0c1100500b0140085900c85101e50000c1c0300c030801907203000c90388803c3c155500210500310940b40801c03d2071440e0304034801187c01070b0446010705558845092a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 591475656 1250 591474406 591474409
    0xb0306040b0a0e0c1e030a0204060b1306030903093605060f0a08060408030402150309101b08040b1b0c010603061b17041e150e0a0213020c07150903031d 67
    0x2c60000513a20044145d0b0204055039441c03c01401d0300c1e06400030001d102507a59030100d500c0355030110303880c1c0404601d401004940f070b500be8000c1504d41c650683c1e8401080b403400040b0203541128111102c0b200030349004003261560760350a00f41c2d444010345030014490a01c1c60405c007243c00455074950103800744080c104000c0c900890070342e500130303000320380d10f030703917a0344038400622020102c400340481180f003c024800700344400600003407189040300d002c010480c846c0100b41080400a1200000106981c000400081003504116042910045c4603682034590800320842500065112142c5a56441c000c000384412802000b600c503422015010020391210802001d45043e00d50b0110b0720145907003c941005920f8030300a03541c824078080d002d840526440c1100c0080e0389e0054181600e810303c0e038816010000455401c150b40d90041010100c03401c1ea1240744080c0d004009103010a010b014000600701c00b011114400f5001d0542d20780e51494218a0003404000c5014141011075039a02c0b6440941e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 591476906 1250 591475656 591475669
    0x4080d180f051807020a0c0b1909121214121b03010608070309050a06020d02032509031b1a04083714070f09050f16050a030b0306040b0a0e0c 62
    0x510505140303100c801c0c4e480c69000e03803400d00807507401424103500745400502c40d900c0f40050200d06190a001c00701030030a00400302d9000d606401380720381d10696074840a0010317100207241036a620060510001804940c40d00c510301e60810102c0c0700481108404206078071080020082004600408480c1154188a8014040d5400415070014542c0d118001d1013802410010706600641c40030066503104044510900a0b400594822402035200c0b4240d00780c6040001641e0351449403607072000c5034640303507072140d00500d240c410600032149060240030401c00e0000205603048040b2081c420f60b00c5107000b05203450716861006004030903051140c0d4901c034010301d204c1c070051200707120382c000303030342e400c0340c00c00900c6200b901c2d0054109101d201070010b992209a0031103411103055440820041d66aa106000c101108981904095070354590700c044050052000c2d280311005468000b80106022010034079125003540c5c291a0300a0950400c4030750041400f42c510b42100c0c80d8041c0ca440c903a01e5010948 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 591478156 1250 591476906 591476929
    0xb100c02120307060203010906091a030d030b040213120b070201061a220f15050c070b0309030d02070506060a080c011418040f0207290a020307030204080d180f05 71
    0x4074500d50529552203041c1001520755941c2c200804541e82e5030b543c8050f900520862042842c0e0904100031071900700e10300c40e4003026812025015011705003c10104074024001e0803052070f807180c7c0c02c0c0504074012000210002c00b07485648811110301007030382029511400002c04441c21a070401074113004481c6d0341940f12425009100d0300341c0c1c403044165100810f0f000260686084403108010024034191003180301c5040315140e07082d2110710055414101c899120345007078001a035000b440d04008c0440c02d14020340c1e00442c0711003600c2c02c102d10698907000341c0c1c2c001c50042d82c0903480002400f0651800303014900013010294020269001450001b034050394030301000d203d03001d00100d0980c015541245202042c0c4600500030040036031002c8000c0c00a4109103025514011003d040513920480b41c0140000c02c0342140c848100c694501850304082e40c0010f01243c200754081c000040c0040d01040984140301c0c2e540c0320141030284550304d08101c03054650003110101801481000700340c444c8100c254 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 591479406 1250 591478156 591478159
    0x903010b151c02090324060301020f160804030f0303020d0f0c02100b040b030f0303041a093301030f11091315061502070e160e04090c0f090b040b100c02 67
    0x202c0344100e6640d900900a0295039034040c0640e289950480c51003041481750542012071321407480c0c46601c1854200e0090245c1414141b00030400464401c81407941420024410008030b0f107880e0700c03940c489404401814049011a070003048001d1b00d400c0d140101e2040070703001101080f030400441402950355646d04200c0b2295a61907005c84010385540d002a4440640602110038001490b68169a6540212401e0351444010300c00701d020202c410180074051011000100303400d20f80c901390b00214201c032078180c04403075061190131400074504c031001500a50180b010b02100103039500307084052414076410135215600e04010880c26030717509021150226000399030a01080e0308107000c0d100401440c3c010030b262002d86100c1c101c04940c00a10b880c01d540b411a03c1c508140c42c5c0885115101c5003180c000008600020030f000f0329801e03d54003a0034810301031054880304599034400040544c0c03460300411000f94031084881020704250169101303900c401d481202c1c7c52601c61200600e00388210714001e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 591480656 1250 591479406 591479437
    0x30909060409062702040f0501061403250822030f110f0a05032d0a0309061b03150e190902012a0201030c020313062709020903010b15 59
    0x2500f400100c0d48021080004101e80320900c100d06070f0504042c0380141c5080344185d04001d040c1442070f20500509040b0f60240e124101d210813400c0d000203040e00000d203c1d040829460b00e409403e9100d400a84501484d00d8403801d140c2d081a188540303000212540241a01030400050310000e0b43c001a449a0800240750901c05071844007100e0303003800e01040002c01144541660201407140220090a02d076035002c600d0203100040c440c410800072040d0065250105050040040d21802500b211400520440000614807148460000d80203203054121002903035400c40144050903250400010b8031844900c070109192a01300340c02103031100d10034051950b850316030040841e4007a84820041301c8845410503000902070100c400d600031804000c1c0c0c0041d04185044200364000f000300c0d0026000e251910b0034560a15800b0755105150610762002c5280c80c00200b50302000445158010702450b03c8096a95a0342c0010542035a8445440301d10030300d00b47c0c243d800c0d0700c011042120348860354a00603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 591481906 1250 591480656 591480671
    0x6020d0e010305190f050f0f04030203041a04051c0b09031e0a0309080313020a050109050108060103091712090114010f030605060103020f030117100216021c0804030302030c0f0309090604 82
    0x304c2c02c60399440410b41c0505040900c0c00b0380000f003e80019114060414480c40030740e450104072228460b041c3c0300503015030400c000505c044030b51030f20101c416110781c03107065280c82d5441c008a200c00c2e10784042d903406002d200e00764104008a1620540d00007403660b0044d41840d906214030224150007035116442a200014003004290194000041283d00300b95001c1d02e84c58417100c01e200104443c0c40481c800c0d2030301c00000c00c03503601803104041510340680d81ca041c02e5403900019002011200d10a80780958600c2d540190660080700900c0303115189106040b16003003950a06080d83e40300000c0c4070300d40c0810310060140400010300401101e800420100d826103907040164001e10981001c07005e643c1c400000400d00300c980d50440f0410180c0041250380040015810408a00032641a0403503d4010300101d0007514082095100c034641c04090700c2c04a003280d5594015030b90199004070f025030070108440c983c20405002000f950030715240918030701010300c80054107000c4020116072040e075489a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 591483156 1250 591481906 591481921
    0x8030a0b031002180d060e0706090f050913060e0c030609010903030e0a03080435071209050f0d020402091f0f0c02130f02090d0309080c0d080901140c01091a0106020d0e010305 77
    0x380c501c030a40410703948c0e015141e02d4014000300f154015050400805140014517042040029219054184802c11425215981c801c040d0124208000043c86240d007403c085d0380c1d0500146008011550001401e40c440e0b2034040c040d1941905c002d009500725a12010100350420b078016409603100e0311034070b10066003440c1c0c16615102c04440d11000c1803d2604c1900a00580c3d0017080464051080040074145011041300d000b4850b019003a0041c0d040c01860a4604040070816036203840100050b040000c01c04c0850390040080e4035501d20301c10015003e582c0a50003ca5140050480385081107081c0300a40124450036800400c044245a891900c56001d007020307815101d2090001340000502c03101800c00501d90411341c001c202240c00744c1d0003175020501d4217005070001507a2202556081c101e401005544d107140003d8214000007003006520f42e0203100b0b124001880384101d1110300c074204211640c100c1070034140c000e0b07029503119030310840140713801010440014409280200d095650f200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 591484406 1250 591483156 591483161
    0x6031b0d0c030503030f0a0b1e011202030a0b0f010c08030f0714070309090509010c14030603123c1b07050a170c060f160f08030a0b031002180d06 64
    0xe40603286000501000c42000b10210065000d410760184003501c0380c03185600c080450700203646050b40140a550310340343c091220091403a00c2c0d5414101039a055450f603820b2020b0340d20480320001c000307560b0070140000e40750604101690305000e10b0012101d01c640e9681d811544001f43c4115642900300303000402203841500803000b03542003040080d13201c00b180c1c64054403200550040804841c2880005120640c05100b0181012100e60303c2c1e001590740c0c0b19801240ea8000740045825004015404c402055902c0060114546c40010010f11401c4c0c042c0035003070801c07d00034503050240c5211014a410b5850b2054609031881000a01450800040154136002e0b541d030000d40c004403a0a8005000708490000e440d19201c62402c0d140036031064010001248074003a04049908018846400031240c814404481a132050889a403412282e8840509907001240c41500081d2214011842414203111000704044e22810550601070408000030340486000b00050080076012544c80600c000e94 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 591485656 1250 591484406 591484429
    0x40206090d03050d140c09090c13060f02010b040b0d02120709050903121005060f0a0306080316050c190515131e06090303020705040b120d05030a0609020306031b 71
    0x404075956406985009811504100c400701c0c00b4500d004c016007080c0b0268481a44585100c40c0b003640707400c403100100620254094005002050709102c4510700808030019800a000907495075038408842c0c2c0802825500b40e0760706a8010b0b4200009003000b5202d503410f6803105681202d01a04804400960b05d107090360581c485c0000d14208400d00c04a01c0340030000b001c0852059600e00c40e81d6407001490408041d40340701d10303a00007030200410300030051408040d015641c958580400c52540c0d54180b03a00d0b41c1c208060500311180503800000802c0410480a4440c10065172402c1d41e0541214541c2608013a0744110f40c0200302030300c0c078500c401340d0000c100c412018010410f07003450342d00c641060898107680c0b1007100b14410300c600b000c11154041e0140030216075140d802002c0481c104801e02025100c0741410036004011612035000b411000d003c440050700c80c0d540c1d003035203c0c60080400703400e031a115841b408500348100140040d580f40826001080300d9004403816544a0f44c0d4003141d0b13440c084 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 591486906 1250 591485656 591485659
    0x171503100f020d2d0203010312051308070801060e15100f0e120709050f09060a0b0a09021216030c0e150f03040305030a1104080d0806041b020a020424060804020609 72
    0x504038040b20186810f1640c01504c1c1158a10444500c1408001c008910007808003034105600040f031056001c0c8150018150401980713100490f080da109129440d0000d190401480c503516107a0a001000460701c0350740d401072044641c620004010030102c0c2c0b0702c0107900342c1c0300200200b12800e690001e00403540c5001003640a442891450082d00107503484800c1d500400404a080001003480459040c030000d000d103011001500082d11a4050381c802025075403a1550020040340d4000340394141880601102030505424003154500740300c06060060f80304147c0c0c81814500080c4200307042e8840e440009131903003030315080c40014004142108500030400154400b00340001000100f40d48100558012428040e05210300f8103184000302090003a4012054141c1c071046001c400c0c188556982c50700000c0c09000000c10700c0303031066142c0207012480e203264051b0b4804020707182181018464407400d001854034032148071110901c4100382c01c09078481c1008000382c42c00031805540d40c100442d03007039010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 591488156 1250 591486906 591486911
    0x90f06131508101a3a0f060c02210313020415080c150d0c030902040501060c050c15090108100b1317070e070507110301050106171503100f020d 63
    0x2501c14010740d031210030310f0f94400b042d820510940024814101c40703990512006011449108082100b407011503450944c450f030f28a003140e42140d42c60301848178228428020ba48a5805a00504268050b10944001c14045501134441540c40e82c03580e8150b41c2003802c520141c0d9507030382c5560760070403580c2c465104017a50052030804a01044000c50242e0812201c03136405807402c481036401048000e410480003600c05050401c1820f50180007a406014201c0d154100000c0c05141c60300450200ca0f800d070000c1000c20394020780b035010310804024260f20b505085901108405842d400001c00d40030f041c0c0400d06010201000c00d0618041c000b0740c40c00751801c1d100381030b2140c00400900d01c07600150b2140e50300c055007482e11032903014800b240d4074040d40c04c1000d039096035403034440007220194051034080c0c2d14482c111141c04c0150340c0a01446000389156070701e21404240d19000004200405017078041d0480c00300001241c561004202d00e10300c00d060f80c100040c502600051880a481a0007020391a5403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 591489406 1250 591488156 591488159
    0x1b032802130504031d0a03140a0609080c010612050d0809100c05030f06180c130504140a0b060408060c0313120c140c1818030307050711090f061315 65
    0x380316401548a0b134020360700c0380b1181c60610300c905a40014000c0346900004a002d00707001051000c40034000c3c1381d41c4403049a514280075100d000c21145848003c1b00d08200000d506520340d8000d004e120007800c046801300986259a60720242c0c0c403505448040b00b84221480058007044040c80b41858070765410500b4031940c44a000e0043c40d03640203c44402458904501081890822540b0980b100a01d404215030548403c0c0170700b00c003034000510401c010f401482c404aa035481e58000c0d03030078101013543e64010506029140c05d0960301d41d400c02e28007401040c03104001c080f00c00941560030800e15010b0030340e05d441e20a030201141e281908090700b207001d03101080280c590700140025050740511605050405840d00842d254424901815404150406108502507003807419541050003e180481480007001ca40707421900121002000301ea4040b070700c0414007175120301100380d0100c2141c0d070506510b00048482d1a040d00030b081c0b0b5009441007281510750a1082d0302603610070502c2078079140c0c4107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 591490656 1250 591489406 591489439
    0xb1c020c0f0106090c0e06070611250203060a0905030d051b0a0c02030f060c120a0212091014040201050403200405182a010518060a111b032802 63
    0x708818030411081c13500e04100003250310304c0390a0040f030b0342c42d008146031314244a0b500e03141d0140422404100700c0100c104202203041c080900c1c0000202d01c8001d900a545c2501d004050916030000c1024050710b040004443c0040c1010003107404a19401800103010303103c01e803005a40c040b01418001c0303a400300040d0805c403543c02c40d10384811640b00b1000c8031424003040442ca074450340c01b900c3d10484024240802505140340c02c00301c59010a03014401403c06096000010203800107660b004596040300c0b25404101101c0c1c001c8a20b14004482115801e04055000a19501c128800a071090115152a48030512440d807800c5051070010410301080c01c5c0803410b401c100500b0310380900d01d449018518030181e8900000480c016503e4442241c515003580c0064a0740c1e440141040d07030340000006604899a03d807000f61000c0c0e10280d0700c88070b6140d203c10740c0c00c0c500b001c8581c5800304021016040c520384e030380002d988889507000301e09451501180c2c8030004104102850000e500c04989545146d48 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 591491906 1250 591490656 591490661
    0x909050a05090d031a10052a1009240e1e15010e0f0414010608012c0c01030f2901020d080708070f05090306040f0204060f0b1c020c0f01 60
    0x40140b03109461114030300389001d8049507804242c0403c0d02002130302e4641c2514000c507240c1802031550402c5440c00185103401018410311215034042642c03680d041d80d404030020400703040c00e4541c04e901000190050748445202c01c981c410411240d010700403034441101c41e150003003d040d40040d4215807440049481614001c140034079240301611501c1c040a0f140880700031084e040320034900105a085d22250401d59280d00002d000303541d0010000c0400070b0102c802d10500004001000000500d030b04450490f01c00d00280503040c10344600803101c00101c3e0b41d00170608800b044800d0030000742e06021149400c019106c0c070500600b0541c0c618914100e83c400d0011100c01000099081d500e40740d4005809803494203003681c1d4140041c030f07042e00042e0268004c4181c201c103007450707041240c100001e0764000392a2050807079040b034600d91002c40d0344c41103041600405001e0200004440400d5081000b0a4510302030402c0c0e0b2004648170050a0105d00b501c0c1c0c1c101c404803061401500d090b1260744100502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 591493156 1250 591491906 591491911
    0x80a0311120402040b010507150903020a080304050c0901151209030918150816120c030204052d090a03051c02030106080906130807060e0724090e0c090d030909050a05 73
    0x140d42402050040e5611540c1108c0d070055005258010b03000348000020010311102504409600c44c10703117000c01040c075020285200f58031550003040300e214444240440078a06034844520211f80340c0785e251400342c011500c048500102100000c8803840d500b0200c8007050140c1c055901300418190a01400400b500410036940c540124001d0f42a580c0c100c150341c0d134071320303500c80020810390402c2440381090340c5a01280c02d5010f900401e01c10b544940010b01200c4061702d0b9040840a07501820500c072240c810b0880d41c030708000c0485101c40ca040205191a01c001490041c00c10000040e0119102250b54604c5003034a003207a0119160346c1c44c0c01000c0c1c1400d41c1594500340781c0c49080000340070b8015000d500e2901079800310410342005059521100540401d1020080702c0c02110004a10f0400910b10f280d1081c2000003205942100c420014001001c43e4001910002004041080d1540e4142c11100c1011040e60010240c0b44242411a074196894105044d5a0304140505c402d08035030b908803e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 591494406 1250 591493156 591493159
    0x9050402040f06260c07240204330f03110a0801170703050a06050a0b1002010f0f050903033105010606090506090a03060e210c1501060c080a0311120402 67
    0x3074100341e000c09800341c0c101d0500324551310720303128500180003240e22030041c0184902c030303072071a4441681e050280925160b040c0c4168050310b6000c0b5003004100c40202c00940f00000802c0000d0b002003040301151848941c1000e070405103d05000a200803520036444101d090442580040c2c4400b45520300034403208003032180c2404612070350604441c2000c041040003c0301c4e405401803130075455559440c3d000e4032006080381d2800da0354400d032010720b4940c80c00042250141d0384c00003444280c0010000101d82c00340d0091040c0038580000c1003041c0c4030010031aa0040070840410440d9a109550441031014616400c56207411501d484420000d054000304107450490315001482903c800c02d1140c98007030420360590051040d501000030484941c03100d01c3c800c0d05841540d03031005900142801070b642d030401c0350b14080f03000500c1070000f103030034800d050315603003424400041949040801807000300d003a40003a01c0c5541c00503282807107038000d40c0035840754440020303400e13212100c0000300d114040c802c071800d9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 591495656 1250 591494406 591494417
    0x7051009030806010f050a0c1e05061f120605040501020c07060f080106170403111c1107050103111903140103030804170c0d0804060204050a0f1502011103070c020109050402040f06 79
    0x24103a0340c0104000940708031940d1b42d00b4107043d42504200c611031842c0f2070070360300508a008010182c0c0310394130260041a02400080c10340f42403c40319000801c124506078901e03c04004010f0001c0000d82c0c1030342d0203083c0c200b000440e4945481c28030500910410101900c20700c82c000c0005480c40d0401220900d85031141c4031107500342c2e40d03044183c030f0710300301c900c406c80b0042240d400140c0064001d404046486410404640700b2003001501c88000605501103100440c0045003290220b0700d040000002030301c401e02e02448441c04205924500d802607803400200d640c41c41c0418506036100750f100200c0007080d408481c00c0f03940d40341405041c8280554054031321070442080c40e071031401103c04441c005d800d03050013410390816a40c81195520350160085072600e40820000840c2e13500c1070b42c00780240044c0c803090540c3c540350242c4c509001c10612482829a41000000214400380200303981c2d000c40141030111105590b440100d43c84105034001c1c5a0140c40440c010403985d100303010540954600d42c540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 591496906 1250 591495656 591495661
    0x1051e060402030402010905090421031a0a0f181103180c150a031505040219021614060903150405031e03040213240306020a03050703150911070510090308 68
    0x41c041644400c45020780481c0c64103008001d5410408201d5a00038000d103580c150006080b110070000031a034821407030000f0380354522802e0740b1402006544550008552a801c29031a1200405420344039210344410104a0317803002c0700f1019290090130300400603241040d51380c5090050408100500c200880c858800c0c46100006814411014000b50840045003400e11a031554210050449046204d60240c40c4880008494a4600180840c408082c0400c07a0049050400034948000854064860498000100400700c20b5074420340d805c0d10244c41c03040c0e42e07205540120f4640b205d54510000700d1448802040305200020010b4076580c4d031540c002d4960402e2400c0b8230301c075501080e90082e610001c030300038044544000703610041d4601c0ba00208503200d101544200d565844446e4026500b080c2c00207400b01e140ca5043c071030242d011005080400900c00e041c04808003485050088089042d6140781706007503860301e40b0587d001c0e00c0e404801c49030742c0320078101c0c910060042984c1c2100400e840202 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 591498156 1250 591496906 591496909
    0xc0d0e031e03060109090905060610020d05180f19090c03020405061218030c0f07062c190305010b030d0e1315120b0609011a040b0f0c01051e06 63
    0x215010044125000220560803142907200c41d4806007042c1e050052000000460035100d004da4060207000d0b00c0644210301d8824184010100b070261880115042640780c0e000e140e42007420741e40c030b4091070380481d201a80c180021490300689002e000b40c2c485485444180040b503000c2110040d41c080110912011a07469030a41c241e0140340239059103c0400e01440c1300c3d40310301c2681d40d607000c1d151b41c08040796180750943c0241560703c4586201010b8001559071040d04000300201c01c000c00143c546260302c1000f217a00c4405020301d079000044940000c5034200404d648103080c661300b0407603034403201d0351240d5a4036041d070080190250203800f078026402c020880c1405071007500307602000540418002d0f2070642d1018020204000c403640040300b003000129203040e040e080c080469200b00342c050f03280d041000410a07203240590098614140c40b00f54040302032145425941125002c600403900c503c0074003001c02c6180100b0489003001d6281104000880301000e00b04044502c68500020b4684c46180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 591499406 1250 591498156 591498163
    0x170912070b04030b060604090e03070302060f010b030a0203090f010c02010b09060f0105041503020d0504062a02030415030b030f0d140f070b06041d0f07060c05060f04080409050c0d0e 80
    0xc100300e1070100034041007002c20303500e03c1c00c039522010081c88a131400b41c544525000f266000e0480f09429032012503a0000c040e0100f08042d04212003030481491585403020070b20031840010482580141c003c0003103034002c9420844d04c107951100030001e010710031250000070700904176003c6c2c061083c01c03a0004076040381080003100a440300c060791150b240c10b081c034480c0c24070f0b103c80f605041c0c10154200281d14603c58248101c0d800343d80b080c000132a40c1105c0c1d40e04075000440c0362000042d040b000b202c029414139000003c8408980d404078602826211000e010b500800d55441c40b01d800d805440101103040c1c60128003c0031141080d1107075122006412110304260142424040e5402c10402403040420f02414561707510082c018004540d034031180001100c2020305e401c518445074490160211685418808407000c0c001b5858481034011294803100e940301000b0b0080f202d00840c0002180900107414225806820114800d0205080c038190400c5a58408081c96030300c5890000640760220021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 591500656 1250 591499406 591499409
    0x1090e0603070303030c0c0b010b1e0a0c061d0f0d02120412020f4c080604200711010f050c1506010e0d06050103120207030c120203030717091207 64
    0x7800500030141960740c150001c00c00c41e200181400b0504a003400002d02d17821150340a44203014a540e19600040387e4200c0c80c0145003100b408459003440703210305565000b08180e400320307001040401c0720301400c100c030b180a001c2e0103405000e602406550b1010a0000185001100c21031f600b150306d00815080036030018040d50090908030071600040344098500050080e025460050a080711122100a2408510495034400301415030340024881c402c9401074001c0c01401c0007248405019840b42e100811025008000f00c1c4900d0361241a211100001100301d60b50000c4507081d642d071212103040044030705505001560005810005010401d80301c2c400342c9480d038441d07200818a100c05208042819200107141a040229203c51060240d0b1550201203589000f00740c005925411410602400801d81c2110010341d401002c0410000e41141c00b4401280d04041451030071962520000307046104560b030140c801094592000f1091035818000e2041300000c4404c06002105c0c16402034644a00303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 591501906 1250 591500656 591500659
    0x30509070b03071e0c020306072f01020702030f07030c0f15030e100c0c17090901060c0302010e01020d0501080607090b0307050d0e190c08070e240d030e01090e06 71
    0x35220070045038610501558200000341032103030251280003241c0c2d00100c240300e0705400150b00701c8207040035400c05000316500112241b078040880c08400d24041c44d0911210b0078224541104508006040c500f9419943d90a5000301903030054030340c174084690756424601003500d1903019503c001036010766254400d0211045500201c00400d0704444c01d40043c026402c826440f4054072011a50301d40703040c401c034507644140740c4408081d0700c59810042c8180b800c2c51910302035804100100c1c520fa82d03400150074112035491610b080d01c00d0507450100e0140520458030f95441d030000c281990214240d800041c140da030f115040394056a50414222401c500f244034031825004108041401c0c80d01c124020207400040201c042183d0f1100d4001c10300d00319500e5000781e0003034203038154002009104c0c22a04000c20750700340201092820300542001d5140080e004500084145040c401d00075a442480a15500018a607000c41c0f4000d090243c05a880c07021240d0010703009071404115000c1490003240120380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 591503156 1250 591501906 591501913
    0x150403030e061612030f0f0911041e0504081c0b0f150708070c080105062407020103090b090c040e0d080f0a110309010903090b03010303081506040909060905070501030509 75
    0x14400b440070660000c103d1000d1504401c80250100d64650414100d101c0c031581c0025948035203200d1401191002910142e103d824103519030082441c58541d900134010485000403100c040c0081c082c0c0d00011300d00c5075002141071404020501c0100c00103410b00d680318820740ca0058200400d200126140082d40d03a52008c94100f04508030b0814030508590240f61510662a04046464506c000e8100450490b510407104100780001c090030700905400c04010b5625211424840504c20780301249042c45903404640032400f502503a1181d00041c0f556904006400400d0070b00050050721440c4001c0d0942c000c908280340c0140300e8034002020601b4400c03603621006141c0f0385036406000301c04098400000142c032950341080d0b680308440218042d5100d60000144229a480d019000e09070f658010110300b0428401000440d8220010603030200001d42d442e10302c08010400030f010780c00b6941143c005c4502e001c91030f408001e80c0341d0203210100e0240c0101d403041551a0011400d6400440d82d2088a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 591504406 1250 591503156 591503177
    0x40203061305070509180103050712030903060222030f02012a031421040c08060f0c1605010216020a05041116050307020d0f020405072a050307061a15040303 69
    0x494642c0216040354462400e0361500058000250550100341c0c1c21001020000f001041004001c0003480c00034040c03c403840941d549140c4015101e480d0314800500301540004030785c19200080f102c03084200700c10b40020f42406449083c20ba030401801c034012804030301d011145000100701e40c000008009001d400c5c403400003540d503404a07070028800300c580107011402d104040f44a44666a502d5440c080e001d802405032815041a68420109074040038050b0441000e101307540b541d100d8859440b148262105540313146503070300e646000c801100c018001d54804038684c00c03440380c000781140d01d141c000c0302c80c0710141d0f4980080204959549a4080c004c440c10040d02120380b0182c41c012171858001c0301500c0c200b09041c0c0104410711030604080f154101ba0040032011450705118aa400c000707180b41c090450602d01070f50301401c00d00260880000c02c0c01c1004202005400c004503514198410414002e4411070500d1020001e06441c519205050124611820000b08405e640440e030300b42d0780d0301141c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 591505656 1250 591504406 591504439
    0xe0d021f0f0f020c030705070e0717070e09010e090d0314060d0228090f051302010509060d2c0604080301090b0619020f0f010e07090c050c0d0908010b04020306 70
    0x3001201c0005a80c5a00c514900c4000310070352010303042403074036040034654a045600d42182482c520703030040508580c2910a0100c1107a00c43c84e01600c0300300010740648182c0350075409994030b00c10782080a034403c1c942c00022500c0d401a004071030007015903034201c3d080d902d08031109400f518800008400d01020398800500d1500d0b20407003120820380054480c2c807a0041500d44e0712501713104c0103403a00034200d0284041140713474460f1003500582180f031002040342d0304000311644959124aa40681000b0303002c200145190f440f401121244100e4100800000c050307a00ca500c2d2800162001c07054010320480302c0e0040010201e0b9580c401c90340311070601e19580c240042d1030010700b111002c054000c801031094003015180751041e072240140747d40007440c064100321012490554070240c1306e21981d040040141445000080313000a60340400804201d43c2c4900004641074007603030354100c03550b110b000d1806034200e0b00110010203558400c2d00030b0020201070010302040e40700a58038184c11070900300c40510354 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 591506906 1250 591505656 591505661
    0x7051503040b07110706020615060f0703030504060216050a2a090c020a06060b03100821030a0b04060e0108010c1d120a12050c150402060708030a0b03060a0e0d021f 72
    0xc0781503410004002082c00e290f99145c0100f07030b040030016a1040c400e1015001c000081440d8910040f20242d00d821002150590f00b8050f00708014189a00e0340d002c5420880300d50142c1d014110400449018800142016070ba5001117204c161030000c1034404139407900b800b02c1c6440301900c21401d4140c3c0664580314203070009190300c0c03002d0000c41c0030b5100480001502783c0504001000103d400685a040c8044610407500041d440030b2455031000d1524030416070b140c1e590420110701c8504094499a0385e9051030b000c0c0c040380049992180c03030002c0c0411211b40e50001541038403d82002080342804001c0d00f82c650792140482d81400300303001e0a001100e413802400c1c1c0181030130340318180d4a854090390703038800c0712880c2d5550840100b800800c070f06894078010403203800001d205200c004510b0800342c012a20500c180c56011303000243c000005203058083d900130b00d002850150403101c01b4a043c0c40d400b001000c13140010511343c060090442500d80c4000345210325082250031458030f50000d030408800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 591508156 1250 591506906 591506911
    0x91c14040e010b0a1e020601090b04140117060f040b04020d0501020d0f0606180524190c060507180501030519090f050f060708040b190c020a02010207051503040b 71
    0x8010040002059481c4800c440ca40200b0b00500c0ca940c131380c0030010000d800c00340c40629651608100b1051008101d6001030302da811558082e00008440c210007012502502103c03c1c04c07031101d10307103800004180e4110702c41071901c011141c0c1924519118440c8007e40c041e400c0e40c024040700701001c007007070242c030340103595991710f51203940010718181c002413500d0305554017210b80064260b500d05c0300f0002107810841603982000c0c0200c001010900b4400025065082515484940240011800d904034040000c580300c5035a080c030f0701e41a9104402c402400c101c0c407804100c030a01e042c00c001c5003840d40150a01d0307111419080d83e01d103145040c00d0046008100c01000c8000c014881c07010030b88038000c07034880d4050322805642003600241c0b26080c958a040f0400da0909140e40c008810445a540d0181800c2e0f003042e40007a410807291104081c80402046940025900340d14201b1000300c2d15400048035244640b00b038090300c030002d6540c3e04000544054140e0b19003401001c200150004080441c9030f503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 591509406 1250 591508156 591508187
    0x807031e140606032112060a03021c0c090915050709120f120509060313061e0b100201020307020c0f0d08030f0702010b0405060607030f0215100e091c 66
    0x1410500c0c540c036141c40d600540412107807160416400d000d820b042c180102c004480441542010000d0710251601e0b8a10a0084024000c1a00e10120785695248040e10380195002070500f402004000440348110030f080b881210015040500040c44280d24041c0c0b00d0044e130012468039074130080030009000b070107004090100b0490105000b00c0c83c843e002c00c40f8101030340a25448280b80702c40f07281600d002d003515104501445001d0156040b50791391202140e41c0100480726500d80d009103441c1550280041844540c001c410a0f9960040724103158800d04900804544504481d0803501e41a07080b44800d4940000581007650030010508210010188200b005401c202c03c2d00010380700c000c1140c00c281d58808000c0ea51030240450b0b00c0c1e09000f200361648085404000b60306012000812a2081d070354028203000318403902c00d214034001e00c0f011080742c40e5072201621a10f043c4291110308400380c050105800a0710011039015000080e119a6800e003408911004280715202940c09000200844 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 591510656 1250 591509406 591509453
    0x15010c080d09120201020405030f01090f030f0908010f020316080103030e0f0d1e021002070f150513091506021908030c071401051506130b0c01090215031f080703 71
    0x200183c02c01020b840080e540ea800140c4850402081604141341040000c03140c3e070402143c240818404191708107815414180070b1101940d8481c2903c20000c55031203034219519011aa4262007000d40080d4850540041c0000c540380c10180d060320b81c10700c00e0002400007100d50401403d05d040008880307500440c0180080003e40e5180e0724844002401d070381c0034074804c1d01c14045c0b01c11400c0c99060456050130500150034440d0415200c001106818443e03526004040d10000c0c03212401901225400c40780c84e04116030194440d01958068803030100c00b603444442000d0006013903840811484184141010505040c002a496a5a4980000e0301601d5900780411840001580307190b00044410f01000011032145001c04143d5510070340191900c0c02501e081020391070041d00503188000740da03481d00e45984c1328070304613401500410201000a400940384862819400b4028000c0c41c80b0b40211810300c02c261580803440b070f07108078030f80c45603904507403000606000184072034402c0c82c95405140d100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 591511906 1250 591510656 591510671
    0x712050f061e03061512030705190c090510030b0702030c0709020c031c0504050106090c050d050403180902040f06300f051305010501051e041e021c0515010c080d 71
    0x3e41086401d603100085640c19282c000b5035810842041d44012070032801a50510350952070700d0340c55031642c02c590b940880c4844014000c012a443c2e07030034040c1500900400070351910203103000c04074070640400e4030703941c1d20000002e40d01480001110740c4403010002030120b003450100b40402941001e9059403039070000f80302040700d0406c0c0941141c014903100030003049504003030038020701719a40307604840715060926140b011019008800c6816074070304200000344541ea1402d088074003400c43c0c41c04080200507004001252140350b00900151410141c0d40488e40e42d94000a542000006030300149028801680d940c180000d050001c640700b96854001c1408107003229190119002290000ba1400580a10743c090040901c0391b00c0c0074140c241c600c082d80000b4000c00c04900c581d000607441c40b070f07038548024a40006500d41400d52143d0255419500e0f04100100d1000860280020702c51041c41d00000801882c2460401c1410850684030504224801c0d10f03210b80550051070044c130155210341c80d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 591513156 1250 591511906 591511909
    0x30702070b0c1c050a09090c0c110d0606060c020109050409320a03030e0d020601060801090e01090206030f040b07020c210f07180b040203090304171608060712050f061e 74
    0x301560444101d44d112076a580052002905200042d0051105e0728941014088440c4d0400d81400c1c68642051200148000e607600181000d00c0e0f07204020000c0e42000400505160000034590100d8800d03201c1c00040ca403640117010840d60408030203040340303207003203851200b464801610f08034a12070001040a8080003181851820384240c10840000750b441803070030081d120500140406420510140859514089004000c0c241c107006500c0c0190340c1d01040350f1510025070000305c1d25507001c1c01e00c94403403070418a0154801c208a9081c0c91a03022540000c280500c0032808525a60006000208198034601c1c0c3c400d6147c21003001c0c420310b20070381041100d406803c200c8080101400e20007042600c808a461000380ca40c030f24115070245006100303000180e24013205460940e000325084608650302e03805168908004143d00d205811964034011640640110702c241c4200155120446d0841354221000200c40b000c4508002600c0500c004c92301607d8440c0354105410441d15425660002c2e110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 591514406 1250 591513156 591513193
    0x409031107140a14150c0102040513060312080c0a0c0201090e0406061401030207230c0d0b01030203010c0f020d080601050f040816060f0215070c0c03050105040611030702070b0c 78
    0x4014142400c078440c5034142c2490b01d900410013070903000080080d041c50801c081480201607500790060703840003007990454440c095041e03500400000b8804e112141c41a10440001c01d50f40c0410f4600742141c4440f155401e005409850050350103a2545103400c203500421a441002000c0882c1006207071040050148910001107000b54042e2900013100d80c6070190302c0c8000344006401906050050003000301180b0b00b5040d81d0080444400808108039410b2502030900d01122030923503105680380c1c410002e009404102e5416203200b5002042511401c07030050710328007a0700700140010791003c0042d640d050703c41c12406800a5041c10482c2c18a42880c001451903002a00030700b1059001c1303071840245106409030600285001c1c14112040002d200c8000d4540c603d040d80800b90f0183d14021600003880364082c04c01c02034010700452100e50b180d10b0124040c240641c2c003076400505100000c9010140c4204480c051403442d0010034480c5c0c40c001c0104100d0f0402d103a080c582d0b00608080007585005172 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 591515656 1250 591514406 591514409
    0x15180e0c0112090f08220f061205040816080a08010503010204030206031305100507050901080f06061b0f03040611010506040e0607110f0114010e0903030403051b011d010f0b09090c0409031107 84
    0x34004051030802c55820381601c06c04076440700807508140d03141000400d802105815410301000d6020489940314280b80c8001c1c81090002008003070103041071028001c1080c0941180320385951004d5150342d80d001007600780d0046020103544000c0820100d0790354220010100c0c5d0461050080c2c40d017498003544410212340701119541d001c5100000c82c10710ba5070f48a81c030345501a248500f1902c07141801c0340031504601a55044040304800d0340030240007000700b0040e190007180d014048a540f140c0b115001005900a80b410000540c01c04010902916090040c0070980c036019008000907521400d08552032940804130010f140030314108240080c0080c0943c1c4c1101c080b0118080c1d465140c06400076405400a000022a800500c14400003039844011a00a082010301c42160070780795007a5280105809403001601840c100403503015000190440700c003901d03a602080144841940501280c84012580c00710b59401100444805190070750254504c5d600925040304185010544240340403c076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 591516906 1250 591515656 591515677
    0x18030f09120a420b031c021c08060f0603060a030b040b1005030f06040f030e030a111c0b010513060512032502100c0615180e0c0112090f08 61
    0x420b031002002d12070b041c5035441010076040344000c0c01100d480b111a0302140443d001005915500020b00ca540c0421955031311042d2a82e10300007a54440b8006542c5040f14400f08401c0d01049a81c211146d0091404034800c9001a05c000007001101c030400689600007845c01d580b280000d4030220204da03d4990b018170403849141c0000d040e0500b00c0c1904100f0916911251281c2d0184484111034180410900c2d0001c0e4840145004402d05190541c1d4080c19011000d0b01171156802d254103005001c1d91102c00c081c2c00359081441d0000f1005401c0340d825881c2d1001e0550040710004004d14104460b0301c10f41c203030038032200041540e20785001440a4150700c29000466001081c60f81442181e0700c070305141798840301e001032107068403980403519410448a01d2070601c24100080300034406150032006201c5849220ba5211700c1d02c070070020b00581c244c1c261103401c141ca04404c214005400040c241c1c1d074460705854212140d06120a1500a0070150740300f10b58480390403084000080c02070019141c1840d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 591518156 1250 591516906 591516923
    0x5040606090c12050906070c080313020607050c0a2c0910020a0903051005040b010605090d050105132102031e0f0f07020f0301110901050d18050c010818030f09120a 72
    0x4000840c405486001c0d0170441d00c0d81100c010700414039003140d001d8001aa02102464403130b951240c44503140010709501079000407000901c002082404281d1030540402110034801041d12805420404d4151192410407184041c100240c16001c4004150740401f000044400e1001d2010940c02a60084108800406c0700c0f0380051080000501c80024442ca10040c10801441c1549074456803110620820090000004582010b44c403454a0451440d4002e00240110708000007001c0c1c200d0b0800d0000e0b20595101c0307a0b51588401800d0b080015007882e44c0c001d50a03d04180d071641c40a11290007030880d08001040628001d00000010703210354240448010348a8002c0e00502c40c000310f030b006007244203900d40429804c280c40c0e810700740c3e2000a030a01e402e85d1140201e000020040c00d1529034695460010417412003000000a0004030510003a43c03009401c2d1180b46a200e040c001d05101480281c1080c085994411181c501a2040100050041840141154001c1d0500382001c2d01a214820b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 591519406 1250 591518156 591518177
    0x30a02090f0d21050310271517010b03030901030b061c060e0a090c0e0612100b010f090f120f08030a0504020406170337120f060506070605040606090c 66
    0x103503490f0750400e03c40b401e810400c0c594908280740b039800018a010712001c00d0003540000300c1c600f40090802200340c400003010000000940814144d0b0711580c800c4540109200281d1a6a100d06010300043c110020340154100603424006401030103000d000d20380c2019091201c42c40f9104020b62185c0030070101d007400100b590030f08110380d0407070200405a480c52418640700a0028011034043d4048404000c4c102c1000c2e1030300030008450326201350070f00b84c9500c5070101c03411580d60fa50b40700031600c08013602e80d445952070200b01076500c0c500f203101c0c0c028880e140a00c104808405100304280c2d240c4200503c4a2400c1d0719501d914440d0426210b52554503616020002142032501c42e45010b0700140c000104407880c241d000c19909e202e102400c0b64200e02e100010508000104410342d8440d03a203246020f049024454010500042c9041040c6850f04059485490000c10f10400080d94000b078400fa02e040059160000070300340203001112100e03500c6d40c0c0024030b01054450f00c041c020700c590f00d030032030384 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 591520656 1250 591519406 591519443
    0xb04231005090112110406050d0c1d01030f030e1302030405010b0a0e0c09010c0c08030c030a23030c09012c04110c07150c0606170115030503030a02090f0d 68
    0x2808241c008600606085006200c26100f44014a9085902c40e030003220441e03c0307401040281240364002e9811048103c0700e0810050285e410100f0b44680d441c4494455015070840782c0c04201c00e100c00380c900342c0c14403107a001207441030075030a00b4680d0260240e0803035444000007a040341d0003140d0a0303c69955410781e2610a207006c818120051800c0e5140004505159807050a50300c2611411030601194501d02401c200d004a4241c00400c0e00c07000b070b6920760102c0d010301030305c0350300030609a0001038641c0901f223035160383d41c2c049d0f0301c440b40300070480c0c0c1c04d540e1034000780c030000da01170480a8103200c02c00c0c0c0044141c81071303440c58400c01b100028980000054800506c4203540341c6100000d942d00c003d002408043c1000030718101220b01500b20341520109a50f41078030f10415017000640940d050180c0840c0d549400100681c2c400d080310001c018100841d0248495a2040c2c00003e00c280c2080010403c019501e401410020400900450200407000300103581040d1001d0200d495034504644123701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 591521906 1250 591520656 591520681
    0x201110406031e180206030a02090604091a010c200f04060905091c08011202120a053a0e0d0c150906180e09100905060906070908061f21020910050607060b0423 70
    0x1203031000e0a1142430200542d41301140c900c19071201060b401e01807a41e03483c8582c0c03016140c1d5074101c400781c010800192503030001009840100d0b80c10780c40e4820100c002c140a00711019004040305240c0d0790205590800200c1d511052681000341d0784201c08845400006e40c0c14892a4a03c40c0315500600040222081120072203000303080e0682c00d0702003c00c40c50401070300c2b0000800450028030304000111110000103c42034004000941080c56450340401e50040c1d9407001651460251501c000300b90f0398110460340600880a00092042d03150b804100d41d0304107010f12500400544291020800f441d0055421542104000c0e14260b03c541c0c00d12140300f00c00d0208540180840c84d011060b80d050029071a0344081c05440020780c83d101e040303103254100700c1d0301c1c1e050060803148500001d044c4040c24420510110f800c0d0036841a0740320008500124039003500102183e0000e803125082c4075040c3c64403001400c0c2c040c2c3d03554201e034a85c08281d050707640303290a01280d007030301c0001d0140c00e003804981240c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 591523156 1250 591521906 591521951
    0x2d0702120a03120e190204020708041d0a050c0d1a040f020414030604030f0f05070f12020d020f07090e030903030418060806060603160201110406031e180206030a0209060409 76
    0x1981d203000d0140c2c802c070101017140e0588443c0c03004a540081028404a030003807150003800b90207200046008101150803080300d24600192124088884d1100480c100c01c80d0010342c2e030001c2c0c0341e004102441100b01c064018400384141e07850a1402144181d0102d4140d540c0ea6903804082c03a4000b0b802d12002c0102418004400301c03d800a110034580390754050200e00e0b82240300018441800c1031080d801d03200b00701b01c8030791070f40c807000a1781d260040e8945002040c41c4042c1c5040980903031040d0b85446440050460800201003000340803144ca40300200c001041c0381d070081100c90100700100d1246450402c01040140084000c44070b0000000507407104444c20b40d084080190011420b004142e541da00607a81c0001c4400c0da204196a00c08000368010078186000350f040c404007140000740c003a096404880340c090320701e000620f0304150b001900200c692540003403400301341c6104080090300781031b409103500107030781c060041c60001c0500000700b460304140e001030182501c450204c080c0c3c041c0140c0a24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 591524406 1250 591523156 591523187
    0x315030f01021207081008030f030402030609151f0b0307081b03060904061802090a021b0a0f0308041703090d0306120312180609060b01142d0702120a03 67
    0x43c200050ba40030041e41d100041c124a08008081010850743c0001008001c010800300d02125980c900405001070f00340c00485090b4424080e200026802c1072000c03402080541da110181c400e40c0d40c6080310301c68010b19207400c00c01e401c00c07883c0c3e004c02e2007982c0000842c00f40809032116009403404204112508060f9026668070300800c1c000d0000c5600d507000d1003a0401c0e4032080203c1d00381018188045c0801c481403000c1d5001c91480180021401e56500518a11660101d00560400712010055541640c0701c1d00805241010100c0e01c00310384509035254115200301c400c80030f036514220317001c0c02d076800507506191590410f0728500c2490b0381500c5a403004002aa80015162465840241c103000300014141c5070075071101c0c202c101226017080807417000c55100c0003c101900c603500b07001000f00380070380038a8086a040f402250000c0344070410369294002140090580c1d01c034080840c880c0110118161039101c00502c8607400507616103100e005450314900041c0340380780c2241002010382c42c0004009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 591525656 1250 591524406 591524411
    0x18030a21051801120e01021314060403081c0b03060c030709171009020f0301110c100b06070f02030a140f0601090204060e0f0f0a03050319020c1c11060315030f01 71
    0x2000300d01034072801c5409400c804d08008404541401c100405031020b40e80c0d84180c0d520000d801b000701621009140d0a03103810030803a000070200881400030501c1980030262903440240040034100f2640c00034400d5004802402142a0941502203854544142d98541e8024400320420241e00c0e44030110000510032038140403a105903c511040e12007107042103000c2c0850b210300c15a006d40d290700d1400c1d003100c0400f070020002d25000c00c001c80b190380c100c01d10f102c1c1039016074a000c0c4440d000c00d00032048a0306001300074500c0c0c40400d5072004035100d0900301c201d030180190107244002c54003d1580005140f10307440a03100c00c1d00042100b50805038140c101302c80140c4140b1080c0030940d03105d20380b400c1c42201a03400051800c10800090039540340201c0351b0f0750000710203101204025000c409014011041c085229444c41d0b204003e03038a400c20440c2803a042810000114001c19000040b424420b010b0f9018105040e140c02c08031b0b80543c004c480034a8017810f418103000013428100407584901c071042008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 591526906 1250 591525656 591525667
    0x3050706021b010f0915020a1202030409061208090120060103060209240a11100204060f080a05191806050a0c02070503030723190501061815060518030a2105 69
    0x2c3c05c2c03024240120440c601c01000d156114034020004000303580d8206401010031045c5440083d0360f81d005009104000e03041103000100001d541000c000200c3d403051800e0305000800f0f004540e5106501e006512803e481540100386150601c059030203540510405a565603921040c800401b5400080403010796544101c00ca4200c180d400340c5010030294500881c1c400c020404280c64506000d490345403823440040c0000d43c01742c00054034035130103003540c1720901d556072032043c01c600721002155015100d03120080d441c2c04400c5194400c10390a064010014440c0056440d03102c11620102d40c94050140d40d04c01180c0ca40c1c6c0c04002220003060224029131070f12a0650741d081c0581900c5982c200020468865080e810200380710440300c01d104018117085500705c504010b4042c00c0c442c8943c000c0030100c42c941d600d0383c4e034040c01803414500083d9070030300202d8a0901c04403020303130100d1001842c40128104032290f84d41c1c10301c0007201c06030058030846600b08060401e2014080002c1241041c05000c005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 591528156 1250 591526906 591526937
    0xf0c12010618050909070f06180504110408030313022115040606030b0408130902040302010215220b0f0702190b0712061d090111040b070c03050706021b01 68
    0x1a040d065841d0303403401101c01c1e5410007182c05042015002150300c080d54808100361044d000030b004e402c890040407418417103665840b0555250900001c160312001c0040c0090042d42040c1d080a02c10a516400b43d51600c0ea8407068141150810f440181000001c6c54003030f4254a025640d802c05003406061482007a10100041a43c41c07940c038489504103519000014244006a40400f00554000c2e1040f0914906490145001d501040d08030340014a0301201181d104464820381d02500d41c103070001c0410002d0705001c1251004020f0010000c18179540c08008101501042002410710400010700b05040007141043c684c5801810141150303c000340c2003800c1540303a2400c4142c1a009120b82030152240c01c022201406810300200c0c0890900000082c40d03680e806c0b5200c00c480c0ca00ba9080d09580b10072040c14280c078690034208a07042d905000500c10389591a00400c0544d2041c552000300c10b9681c4d445c00c2c1008180c2d481031b0056080f40d540b282c4840051103410700c01580928003500c500c01e440d01d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 591529406 1250 591528156 591528187
    0x605031204030b0a1503050a05010c02011103061e130212011202011707020f060c04060e0102160b09030a05120c1009021c030e04060e060f030a050331030b0f0c 70
    0x12018100712003c8000c2180c54150b540080c41001e540059090229280e0030040c0e80ca100300c600841d203540c40c0222104d60144184a0303065803c26008000c1e2854440c60200060709401d080307003042c041c075040e06860a40e602c1c1c440001007900501005038440c1007048008403100c9059000305000308a1150340030041c3c0c2d01c00e410207035420218102c050147c0710513074101e00c0d060501080d10300c20321501041c4040c5501d401c0c0a84110382840c0d4a00040c05442c0004903155040c1c000100c0b462611104180207003440500941a620809000c4420340c0c030143c0c503800e18081c400c002c02080418000b41c4600c1444044c043c0b031807920207030b1100b8080019aa40816400541c100303070b0444100880c4500c10403d8480c9505041d0003d000b0010700401d62100c801005070641a42c400d0700c14803d8003142e840c130f41000f0840d402201d4014010f9405d0a040ca00c2244c2c014015070800c2100700ea80140800f002204100c840e00039500402c880340c2907180540d80f00c0c290180290210000e260180b255403511640007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 591530656 1250 591529406 591529409
    0x21090b03060d08041d190e1c0e031507080f04080906070f06050f060a17061b0f03090f2812050d0e0604060b06120c090613060c03030605031204 63
    0x780c0b48210010480d041c011818042c41e00f221001000501005c07050103208a409800303030f14203900c240f201c02075201c60711003103a508400c0014180c11950052104000082403040246421304060000a440134000781c14860540c01c00440080740000340f01e403980e030106c00c840d4450640301d1025018101925070404601800340d0203441002c2c001203510401c40f4550b400c101040c0d00000c10300490402031001b0420340b0081700e005008406407030340098510310300500c000c0410602000340010343c03607404680c2100303c03910a8460201c80204170440c50449014003c5210b402650040c00b0904404411941024010f800150440d02d241d4092a0148602d01c04420025400711082c51000d06045040c0e50a001e0220b2981d25103140c061980d00008002c60042e114600c02d0004000e803003e440d040000341e00540c00350484000d00000081d4510107004004d140001004240034200310030610100c801b04290b81048002841051082d0105601401010b0140c0b20480240a031b16607400214071060080c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 591531906 1250 591530656 591530659
    0x100b040c0207030f110904110102010f061202120102040308070c2102010512070c0507060f0207120b07110a0204020a1e030c0221040e0a24060503010e0403030f0921090b0306 76
    0x414000d001700318480b1007101c59401c2c054800b800624103070500b4859100130715007490165086c6801703001c8500051003081c1c1500e416002104604007150284480c03042240c0291101c1c0d03600f00004000f02c0e8140019240051198403065144d5050071640200e5220300b1079408549174213107207020f0050f038000f42500c0c0e1aa00612902c407007540c80c42c10413100118081d001030220301583c0c202150f010740c001d02591900d011502111085030707603130031084c801c4c0c58601c0c0c0c09842803a02101003000f080c46000280080c505d0310007155100541030700000d00f02da2224a2400210705080c21400540280000112210019003002c011011402c034000e500c44140040d0041c80091901c88a6080310040c4141c030058190221040114642450250300a1408600424000c45410914250702e0307444155003054814964601d815a484c20001a000c0346000d40b049043c95141c0b4030039070701d40010b031040c5400d03a4001c40d621040c140700c10380c3c540b2f48080d0b00005c000400075852814001110313030004403034000c0c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 591533156 1250 591531906 591531923
    0x1e0d020d090213050603030f070519120315080a0803060102070f0f060915080a0b0d0c030c0f05060a0207060e0f0603040b1b070c0e0403021606020604030306141c080c0f100b040c020703 81
    0x1038a01e84ae6040c1285088032202250000b0441c40074015480c02008240b01a82c4081014008507036403181b80d04400d10a080440d408403031044002405000503640091042c01103a80441d00c0e002e843d4103202094020314115030031690108030080d40401c141e002880c0058096000c0001900020301c0d62a004001500c40740d200c2000071029100e4a180e00700307507604240034107406070316450000b8400d00e41e4400e106880003100408650ba00d0248101c842c01c6010350002c040aa281c10b609481a140b0f66100960200c42c8055448050700c4900c01144031390711806047e03075240b030104d0465550f00c41241c1c0c0f020021000348108400160240896426118554403502c5c803076550f443d0480c80c1401c02141103041c2031a684000401d00e0700010030a014900c251418015036440c0c60058a0304200d10407040d902a00f6021b0903207a00b2281c403141c103621806010980d190914400c0e10300d2621143c080b610f81643d01c8140d000060406510400701400400c44060108109403e402980e500803030001800c4c440c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 591534406 1250 591533156 591533167
    0xe01110906030610120f0207050606091e1003020406090e103c061e08120a03020310171b0904081902071a03040501050f0c1e0d020d090213050603030f 66
    0x74010700b07400c01c41003000c01c170a01c00001c2501c601d1000e500b00c054115800c1c80f07150080b5005140141801c3c1c800c100d00022180c41e41c00038441c2080351300005c1d003414030850300f00340080f015880d18010340000d003010b103101140c85100a003c3c145802d0782d01444040b640e00c1c00b900114910404a0801c00b4041000c8482e104007225014403500007011303105401103185000723000159120001900b1000e013443c0c2082c20310040d030b81c0f61230a4131405203001500c0b003c00c00300002c482c194020381c00386401c00b0751031207104016912806446400d1400100022143e88a0710b5100e9440c0041c44c10611010f40940d8006680d007450340e50741110b40500303406040b00040c080388200d4000d10802c4003c00500c40340c1034040c80658103000322780d065031046d5401d403480c1d42450002000d031204450317414001d9201d1002540340400300c0c00100c0e0340b40709100c411840c0410420030003030324640900251003152407910002a0600300c6204105a880b607142c05940064200005c014142c0c1d80401550700e03540c80c5446103695070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 591535656 1250 591534406 591534439
    0x7180f05040902010201020f0c1c0302071505091006170c060f0d09081201060302070209090a0308010b0c150c040503160602030412060207060e010b040606140d0e01060e01090e011109060306 83
    0x2230003004181090060040f814296410002400c4c40d581ea00c1c61240f240c10700415842103060388244400682000c16003011190f14000c580c0c4038603441600003081e580508084000700094030b24592001d0022138084025600e0540b040c04440c00000003118203070710386410410842200e004500c031001e00241d03103110b031b0407d221500c81159036100000034840803560716003801500940081c0400d901803001900007900d40a000500058440d4054136610881c0c1c1c030701440286542d0040b022001d90340159806210042d14131302031180180100340c00700d03850b503007440f09051401180d058100f005c6401d0040400c81141c010040f68240e40304003128000c0001d9505219020b4031491000508140c1b4041c0507101e07100041d8004141003900302e40a000c46507942c60115101c0525800322842c50004005407660340400f036010b000e0700c4404100214101d907a84900043c4840240c0c020041191110505103017071600b032240d001c101003048503560a202001d00850b8203030200402c2c0c180551701400401030710 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 591536906 1250 591535656 591535661
    0x605070c090b1203070b0108162411031b0c04021315090324050a021c0203040510061e080615010e040b0405011805060603040b0c16080a050307180f05040902010201 72
    0xc00035904585e0342c0c00041c60b04208907002440394100500403a02d507041ca0386c0c200c8079440704596001a0b405400024a126506201c2c0180380c0001446009050314210700700c1070000c0d040180038414a624003901484410f820b002001d003002e80b05134810081c410410320404011001d9a008000590720303445c40c0303203003583c60003039035080680a5159201e0303d211424120b06554080200e201f001e005076150300c40003405034002c8810803200004c003d490800620f4040e405158040d0040b011111042007035050041180c5440c4c0024403080c269135500094a12400d120500400b0200028101c615010500a11030344a00c1e082a04002e080005401d5564440d013100c2c1400c600104104480c0d699503208460ba206841c60620102d41020001040352503c002900d121340d400c103060142c250f580810540f00c40d800000c005196041c5d840300d110110300010054200005a501c03603a50b241403581000e444000d801080150080102105000001e42110008210b031410b5074003144403050b03840180d02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 591538156 1250 591536906 591536929
    0x2120604090b18032b18050c0607110913120504060c0b0705070506160f0806060906031008121312051f0204090216110a140d0c0b030f0702070605070c090b 68
    0xb059540c044d880e05a03070f1842c0203d016212070041341084801c1d4140e0344884546034601019006400030020703032342d0b142040b0004140b01841403203810009552480041c01c04a82a5001c58000140d001c40e401009264400a50040503500300f150a01d481c005e0020020b86010500500711081003001c01d030803a0080b41030b83c0801c0d500c0010b90300180340586401c540204c580e200070b0009626031041d51840f034040c180a038041c0502802031032a050030300c000e0285580c07014141e049184042080082d000000b0301c20520940c00f030070180340d5190b8444260700c2e180d6945400c114808800c040302440001d500051103400e04006014440f4060350745c3d59010024003850348202e44441c000941e140800d0f11150003082d900b0302c0b07001525410550001880300000f91800340c1c08064100002460161070038407658580f191294846002860311120380e07151581040d03400c4d032000c100311014400384540500100b4058881840c00504103078060325011320742d000c1c6109003030940d03a54891070b03903140c4c495400844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 591539406 1250 591538156 591538177
    0x1c0512040506040201020610240207051003020406140406020c0f21031c060501020601031e02130203100b0a200a0b040818040524010207050a0902120604090b1803 71
    0x94451515040542c1c81e850200c8089006009440c00100740b02010030610094034002d29410f03140c00d4800964901d180030102d120700c00d5103c2c0e4800080c2c03e03a0f80c5d03c2c0c4401c00e890707a071303a000d070b101ca01d03099002d0000d005202038454600020f002c140901d560006502e4460f14049507401740504850021500340040000c600388842c402520f212003110000000b0028040c940d503003901c8519111500401721440350103880c0c0160060001040450f00e240e003c00d0b03c1d441203041c4640075041d1540014441c3c0c1d0f00040310541503402108100300e00b08492040d6008041020f00350340341000b40304000740b0044800040c6516550503002c800c0720008200004c1c0b08a41c2d200e401c0010f1420b02c0c1c1400c4096400090030682c1c418908002d515070380c2424029903008003107064881d00080084c144444041d2244669181148030f000c000241583d2a40c1c1e41d4402800105001070356102100015642000000c1000740a1030170030900000003240d51503465440084600044a0600221081421885607000b00d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591540656 1250 591539406 591539437
    0x1e030905010e010c0e0402070c0608040606150c1209030b18030f0c0102120a06122a03031e02030f03010509060105161a15030a030305090c03030f0a201c05 68
    0x260b00312801540011241c00c0e0f10f4035141c0094120b0001c00040c1c0c810590010680508140700304500390041c02000d801510460011070307450745800d0024118103c0341d1200c80000d50900604c8207101703581e016040d000c0618a8005100c600703685a10012030000343c280c0408481110700403154040902c02d440c0301d2601d0040b055650b405030342029010b9040b10685503030304071842c808030f06913040c00d200e5401240c01e10800d084505400b510b0f42444400d00b2450850b101c50340c01c4810300700d10700b550032070000341d88a500e840020354045040c0e1540000910f61582c20f640c01007140b5010310740b45100341c80c11030307008481159032580c6520040307035640075204400442550046082041000345d5521031001c40074112044403640e5000c40301007804d4110f090194041d00f041c0d40c8600400d1190f0407032603100402d4000c407140420110080707850356111480c004400d080c0031031303207200156001c051050244010241e0840d5000814290f030b4807441c004043c1800c501805041c5000d0343c2c012802c2e01c0c040046511507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591541906 1250 591540656 591540671
    0x6090606090a1419180c05010509010c050607120c030e0615030a0b0f0a110703050904050a06050a06020a1103030c07090c0c2f0603150918060c1801050403031e03090501 74
    0x1054010303424130401503040d41400c80c80c1d481c14082d94402c0d1400c0303811036a00e59070300c0c0c505070054810390720401c0344604000d12060080085001002468001c000d1503580401d08100390102c2005c468441c6480c008160a24804d6107400340d0000784207030841c11852a031030713000d41d070000007902e405e1400c60700500d0142c01c0d00c100103160b0b0049c2100e500c10030025070f0520406141c0c0c40c0b400182e100e07591004001c03903414000e0040e5410942d20103544044024000101c3c03a17240d078009030035002154807110040e0f00246a0070100803038a800f41000c40000e40086003011107494a10ba21910079000304000705039a40c0c070380c0c000c6034400c0308907600b030641148a6419042c0d031043c94a8101c2880030b03429911280f03820303103070085007480400c592140300c07443c58401e40a070007407041181490029006522034035020300080c018000c140600c501512a4044d80c503030315500e8100e420102c0355010a9a4107001c1c09100c1007000c2a00301c030348449420340b80d0312011008003a0f08003d400404104502828035032a00c002c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591543156 1250 591541906 591541921
    0x604050f21060705040807060c0201080118090501050c09031506060301030f03030209040f02070210080403120230011703030609070509190e090c0a03050a08030702190605160206090606090a14 84
    0x144180d9246c1d0041d10702594031a81d0684100c19030f501c0090001d40110010000400700b0520144039104140000c42c0c014400d032a42d9080d584241d03616138040c2d800065032000752a080200c849498241d55680040346050400203441c0d020510018201c5e06101d00b400b003c05100758100c0f002c5120041c400c001440380201c4c1100203402040707040b40a040c1c0070050a10f060300a00c103a51003903501d983c544480010b05010360010b50403d8410000003040e50207185600c5400d0088551603411208039002c1c150325091203600b000e0f602d06020b8030140c00c200240320541d06d58041650740280305040c580d5a0300d0a18020460001c2d0b04e61110700b806103181f0002ca588003030721b601c5c60700454446d812580d9005940e000c109500034180700c0104290f11090340000001c0d5032078087d41c0d01456900540c0d24280e550380d00500031140700403040b101c0c10795074410000107407030a80400301c52560510003891140750115045544800280c07940d482041828001360100310b0f40e030401c50440000036030a000381d0a1404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591544406 1250 591543156 591543167
    0x10091e050a06051903020a1206120c23040b120313030506070509030c150f0c0327030607180b0c070e1b0315041b0e01020c0604050f210607 61
    0x6080c070800d80960005112880303001910181e205002c0003241d034904014041e0000d40c006c1e080e03030061040800300d0300c00b01c21861207518010305c134030200d0b003a0500742440c1a80308901c0c0c0350070180c0c1d000001c048440c4c0750341d040e402e1041c200380159000650b03041d01d400003403400c07034884000f000c0174400010344a60480726640d00e1800c80c0e2050b03044803c00c0d00d8200045e04c0d0f500856081d42c4e090360113990102e955240c0314900c601c1107482302d1300c81490045540c0050401c2d51104004034800c2d480003c4220041e143c9400c031450030f10f605118040802610400030761214400ba11560820100c921551804040301d840e01d802810060702c059603421803d4400e980b2140c0600c00d12100c41e401d4000103948004e181c0c0e190b10110564071600389075540b4140b00802c0d00c000c80401c10341085d5110106036a07070715040da01113401c0030640c4600e80403085490009181c00b101681d1305002c0c3e0010700c82044592200d42c2d0300c0e440c0900c1102c1515000c0800e0032181c0e002240e21078041c14501c1014241300c05c031a00003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591545656 1250 591544406 591544409
    0x209030712200f01170423071a180906030106090c0e040e0303060d03120e0a060b040f060e06040c1707090312020609070e0a0207020d03050d06050406050f10091e 71
    0x64007180c00714468101004003120300c0c0803045000c07821789002d00c140e06400c80d401c42c0e40b0910410403000146d6042c3c41c41e0314103403904103002c0544d41c1302100030700035040307080b07024101e242c0c10340f218030720705051190546140c5100700c1d41c0390300a03414100403c166a9013034200d41c2c090402c03000208040443e001c4014806403a03640014040d17442d01d8600d03c00d43c00c02000316489004040d24a00354420141d03011540c005114030581c102c00d5450250480548051218401c101e0150740017007401d010990402c03003226500c6015000c280c0c0b60140410a40b030105406d11303801a01114005452107502d04143c410b01c04c04031084504018900c200100c1c2a005600303c0d0a0380c0c0a00088001ca4600c0700c41661380301d000f40d586410a40c42180108002035031000d00c164000c0d4500340c050b00303004090b4040b030601980306c0700403004550041080242502c1c0c1c2e116180c0103000c21039041c0032140c90b02011805a01c1c034580b055000b03803070180041d52918014a0000e004012071190103c0544604059540e0985035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591546762 1106 591545656 591545693
    0x1020c0d0f110f06010f06180b03070201090b090a0506011a04120c031a060f010201110304080702010507020a0305010c0e040603110d05011d0c0a050406080a060209030712 75
    0x6100040da4402c3c184003d0400703505060600303240307510704c0d003000e800c00c0760310501017a11040c1310505004032141c2c2010f560740ca44400c0402ca0250040d9040680003c40ea4024003920a82c0060380c1c80140303004001ba194580d8855180c4144410b1080e0f640401c18002e2105001000c120034948419a100e004211100c139038984d901455144d260b0a01b0400800100c1040a603090a043ea41c1000d8001d20081020300140e40200703c8a000c045c00107808084045806421640103604480203603800034480b482c0c650b62842c01034040c01d1200b101400040300b06510340203e041601601060b654408800510b8040040500c81101e1800e0b105949940d266100d1000a43c401401070a2106500002d009e041c000041800010203d41d4400760085150503000c01c00d00341d010400a010b0756101101580d030710607000c0003034506800b542210110024403810007080007441c520b0740410036803 = true := by decide +kernel

theorem cover : BRFrame.Cov 591366906 591546762 := by
  have h0 := BRFrame.cov_init 591366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591366906 ≤ n) (h2 : n < 591546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
