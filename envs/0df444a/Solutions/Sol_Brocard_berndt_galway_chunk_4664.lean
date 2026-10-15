-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4664
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:29.601707+00:00
-- url     : https://prove2.me/submissions/df8cc805-84d2-4bc7-b52b-f18dc7f50f05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 838669064 ≤ n < 838848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 838670314 1250 838669064 838669099
    0xb131107051f0b010c05060415020d1b09050d080304080f120901151502100b01031b08040c0e040503030403030c12060e0907150504090f0e010903090806010f050f060c0c 74
    0x100600802d8040c0a0100f060004011158900c520304002c14960010001c5000642c864140c45a02c00a1510060920b070309005004240ea4084111400340181580d44071b46150380018414040d12094a80f119110354039034030310241c0d203c020005070103907402044420903038101c00101d0300c50003080c4460001e10309081c0003c1c0d000342101428060442041100007416400000b54110601c00c1c907000b5080501c844c3c540c036405402d004200c00d04059581001c07160710142e00600c030711554451380c7c491481d8541860070004601680e0071091204200104020000c0d00001c1220341c4150306150103e2100080801560310743d600980300c1804030b0a0030300204501c134244130320b030340b040c1030000c00c071070015680301190290f11080c00060000554204414016a20150054000e001010100103107400c80003500500316010b0807030840c00984155000c02c8400c00400c402d501411045090075911450100026041c031300c80d04840b80611804942014128010700619045080240800c08078401c0d103c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 838671564 1250 838670314 838670353
    0x91306060305031305040b0d020103090201110105011d1015050711090411040b0405091b150f0715050108031204060b0a060e0406090e06060d0c0f080a1101030b13110705 74
    0x3007804403094240025007440e050087c090302c0c0201070940031441102c3d0f00110050300030100143c0c140303c1c0c2c10810760b10641d42403040710300a220110504920400c3c49031603040c6030601408412001c2c801c0d607814450009241c40c80c03c0032503c80d0900c43d03554002d51a24561010000c0d102c40c0d801580c4008000034480d0f51401e40034601e000301c80401090181d10104000c0700d00a4031650a075034442c034070034ac9080501c0300b0346c0340e04468024400c00c14151161214806030340001c0400002e00408940383c0100610140c4d51086922042428012903040c0649140e0305c4c040c40284208041031600032034140400c1d60702c5100c200d5030162180c01442c0e192207000e000c81814259407809649001d8000411607054454001c0c002d00c00005040d036601d0380c1c404c000d1400402582a034401707400110000e06e090b45a10013900900304d201c040d080e98410760500d00081c030038812106040c103007081700501380b564440c44c01403c0f030690324000154462044d0440b146034080e100005245102d06100c119144030310340c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 838672814 1250 838671564 838671577
    0x709090c090e0f1308091801080c18190513080c0607080901140606030c040e0f0402150406081b040f18060515071202191a06030105060105040509130606030503 70
    0x40848030b45845419200c042e0b07103001c58008002543c0e1300c4e903200c001050b41004210f00000108500c080b10031041040e580040700703038082394075540150281704c06800c285c2b002c41004081000c0a020320318026642d00c109030a221141801f150396400002c0079401d04582040e04c50340c01110440d00ca9112800840e40da5a00fa10940049204100080e170544014026140e10380c3c4603042c8040d150300c41c6814065541c00241c0030018100c410300002c240490600142841002c4a0100c250b0758285401842140045882c0b45009110100400e02c8060f8016420542060460941c0c2d07205080001a040940c003c039002007140300944500041c1700300e42038418281034207640e07004104140c2e82d6000c00c54420034075082c20240c01418050f040201d546008000d1a014142c010b51b1a8924540300c000c450b42c410013411a02083d07414141d407054448101c0c069070002080d4001c0159052090002c0c006000340e22407244183d0309003000855402d241440b02031101e1380000e0a1100d03e40b00e02d007030358503900034a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 838674064 1250 838672814 838672829
    0x605010b18030d050406051b0607050d14070e01080a0f1b1803171c060b0d150609090f060503070303090503060705090a05060d1b120606180e0709090c09 67
    0x1d4103502164500400c004207450510b48030540340c28645201603465400c5000003850304088005406e4890005000b003034410791290380d507117598400103071079402141c16217101c01c007944402c1405c108403142c003e9507a01c5054400d08019109a9800360080050039581002004040c140104e200009100701c01c0b06401e2445905d40e580000c910f1502c55016101e1031101902c1c12001002d00c4241e1036080000309626040c004044d11031a600d515500103880d0140e2110078900760009030280c61420314402d031070800d4900580c0301402890580003d0010742580101d001455946101c1d88401701c60340e021030700405024065821140d641c2c1006401c80581d44030b09402409030394002490f15200b6411580d003004020110005207081005000203500200800d00b10590750391443e100f19403400c0c403400551245540c8002c4990302500c21441907516550140040c0901451040500c83e1039281c50011740e13001125200860340c405000316010b510b1988a0400c0b185007040d0494050b42c04603120045da01d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 838675314 1250 838674064 838674097
    0x1a030406050640110906070c03050a0f0611030402030a12050c120307020d0206010b2d1c150803160c0b0433020c040c050f0c0a02090f0f0f090a0605010b 67
    0x210200b45007071341ca48242c00880350904010207604c52801d4400350107a680540d080072461900c03a9507061405003100401c4e03849070900034100d010800580654030011055028550039410a5400300303a94465031500102003c00403903002c1c4030b00788a0710680395040b8044007140c40c6910583c101e41c08070b03030040d20a0381c01405260035041015000156071412034400c0c481881c1b80181c6000d44011400d5180d101010b400e51245a5403e1440408050508580a01c1555a040c03d06d90000400c903046072454550310302e12118104690700c004003d507070421200550110701e5044626142c07031a403401c0c0d00244810078011802180a8003104c400403001003c0441c1f031400c01a13100e640f098607641c08032418005a101d581c40b0b03485c07814560014004822241003041c2400915000b0285980020f948965143d200c0c0f40303c00113515100300c605401c0b089599107080941007046003401700311401025244290710795404928070b03020811501501c81c0d00008100f009507160720050060303511500156040041303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 838676564 1250 838675314 838675429
    0x903071211010e030a081c1a03010c0e0a030f1401020301030f11040b1f0e2d090c0708160f0c080d020708032d0403030f08011a0304060506 61
    0x50f00c40000e000800070001d02c81c050741541c070301106502c0f01c0c00c1c0083c03106101052506013402c0d4025100c014009024040603540300c0410316084130751000c040c00401100029114081c0c9a0104232015250031500c442c01e4000c2c40c1c02d20964039114121200260340c4000000014814180003003131240344141e4003400041089070070441550700d40000164044010362a140851201c001c0c2d2000005d911708105a0790544140001e0103a07100b40f1230b60300d1489007041c8050740d650125244081d10744048079001c0315030408048100c0b40b401031000040c8407141c0001e01c030310180810700e100c0000030360002d0380b408240c180c0c0c5050305019045205035005442104117425480e40003040309001e490402c40210b080c642ca09052841c05006803480050781c49000d07840c6446984048002d00156000f504e07a404485449503004080c80e030140e0001030003281c1c00608508201c4a402101c2c3c0041d04050041425140e050015105195030b402c814124201c030b80c009051000001042101d46c42001c805090551 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 838677814 1250 838676564 838676567
    0x3070f0c09020f030621061f0b0408030405150c070b07061d1b040915050114011b030f09120f060c11060f0907080a05071a0702090a0908090307121101 66
    0xe422800311a2400500000b9000c2c100400c1112a60150700090920b01b4018415542010b40c1a944080c0b00091841d00d81ca4000781c4400f242c00801c002d8188c5440c00e8a0002c03c99200d00550040e584103950781e441c4946205807840c1911408000070301511007450381c40088008961041c40100c85175070803c40e500703006480e20801c80b2820800321001d800300c2401c101e6607410000140810340e50190f0748144c606c001c0b40e0104803031546071484d80c1000516505100004c4010309101c0b2519040003d4940c42d0b803450b040c01400c00c1c660300d40c0b40c00c0c038a40f100100b0f5070070f844801094000b006030076200f1040c50309021304013644801960140303404000c400340c840e508961030445a46411a19400100402c02c2020070481c156406214003040d211019126400103041c40c4660f1400c0c0e8075a030000c070041c48005200b1185540803e005484c4520b0021181e0100d104180001d069460941d0340d0300e00c2d1270a0242c00021101c806200406032003003030351504114010580d5426040d501030051542c00d01255 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 838679064 1250 838677814 838677817
    0x50d260d09050d030216022202041d0906061005030403090b0a0309020a09050c16080705011112101d070216080f06060a0b0702060a0e06070c0312020a0b0a02130803070f0c0902 77
    0x6155441100c04040099000c3c0015604140d0080400401c1c8c02607002480840384068000b424428022010740295480c00c2a80a40301408003401c0e60040418404039550313004c0040b038407040c0d81c01c10b10340720f5480382401e5070036a030640e100c01c0703484800041644a15605602c405a014402c0380c1803610907464a201c0c004039801200c4c0c408014004000820228048050440805104850a500d800c411307680d840c2c20744003202c804024140f8041000301c901440808090762111108406c0700285140c550968030a070004501e00790160707c0d400c00301e4041c0b842401540340361300c1c5c0514261801d5644400c16941c405490060090354003c990106101d0b2030544891021141600c029608107a0301c0d8080101aa000b41d90350000d2182d592010550764071400c02810b02c080c01100a0341c4102d1440c24134001140148000d001103410010440c3e001032240b840d4180c000141c0f880060312034001c0700c42810540c450790402510380c0b0010801d42c0802845070f030400c072054801c046680d00107030380300c8100c020b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 838680314 1250 838679064 838679077
    0xe0d020303060d06020405060d052a0a08061c1209080316080a050d110a08060405040308070311090301020d1a06040f03030f0e13050609070207050d260d09050d0302 72
    0x5030801c1000c154a8078100c10810141402500010301d400d07903640001d0140c0d44054145000d8540310002c000e001e4003041081e40b80d1407103084288101d010383d460005180c1c403c10141c0c90600010b20040380e05501c490002ca0840c10b5018001001c1e49800d0500b004030100480340940010401103001c2034610340441600c580c4c162024801018881c3e6648209d00c68006040f0782c400c003d020312030200100c8050080f0440380a089411560b544000c55000b03103d02c2c001044c59004a040005000001c0d82c041d600c10b92150f00d602d400a5401c095a090703103014450842500d9156001058000102030300d40e1083d248a44500b016802482c0e640040c0301b1540076074480c18007143c0c0064002c1002c01d004004541880c1494036144200207440340001d045088da8854007a4440d98400c10000c0d181050148650040302d0760000b00001742c98a00003031021651080002c21501407900d40000d2105142400020030351450104c540319415240020020002828281d80e28810b1201c400b600c28001e1003155078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 838681564 1250 838680314 838680317
    0x40f1103010504110c070b0403050c0402040b030402150c0102131508090703060e0c0406090f0c050421020d0f050d020606091902090f040501060e0109050f18100503070e0a0e0d 77
    0x1036a00e030004010007003014036400840e4a001304010204130f11309100307400c05400810700441e16141181001071414060304203c030b0145104100c180045081d0005a80e0702a80c105d40c1c0418402001d40440c06502070441c01724060360021500e40300c90f011048000043d5003801d8500300e070360884e0b1401194494015280070071590005a814800f1031703003a402414040c0e483c00100d810044003280440c084403c42d60040c030861342c2c2c443d040c545001460007000000c610380e2a28130b080c582824140302d6503050031406400c5804820100780c0840d00c07845c980b04c15940c1c20070700104640c60a4184a52501031109007000180250000210304e4541020b2075402404000360402020003440c044000075031000441d6640907101f1007040704d280d5101c0c026a0b02915072a030b108061400c4a03400900002d0030fa40000c0d03c502d0040075007500d0b070b4a8002540b10422141c1096480c2911150611190410782e40c003d00d406004a03000456141d030b1182507030b80a11290f013000c001103070120790b0080e11110390346101c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 838682814 1250 838681564 838681567
    0xa03051603050c0a150c1a010e071b051e070b040e01050907111c0e031605030c040b03030a030b060412120f0e0d0206030a0f02220b0a3e0c040f11 64
    0x70b003180318a06101c5994850007d0046c207061298440f040042d00f40d0284444211b078104100603582d1220814510500100c1c1855141c0f940d551082d894050701103408144441503400c041c0140020008400241a40c080c055901c0307441e0025007254a0f000d0141a010b1125036000c18074292103010608001039000000e0488120a82002c28014104403082ca04100348000541a0cc0e682401220100389030b146200310341914100c280360402c1c2e4015201c0d07100b00d103010303104803070361310044211402902c191600251000e08a40002c60600554010620b0075200052190403c005541704401e003446549131040e10414100c0119030351649101c1c001c0e00441c205040b5401814100c01071a008821900046680b101c501b0b0f9040485c0c00c5011400c2003400c0e020f401c503586c080b4400080c000380040308066441e002e047c05010f44021081c0504c032030740220800510002c03510100e111001d12500419039649204944404ca0344c0c0c4400b00b4000303202da40703020481035114155204100c4422503200109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 838684064 1250 838682814 838682849
    0x5060f120c0a0807140d091a07030c03180f15020705070608011d06062a0109050a0b06060403200d0b01060203090a080613060f0917031801050c030408090a03051603050c0a 75
    0x100e021f4016130381c0c00c498802554801c0c0340c4d1881649200e903c50b041540d0000340d0980c00d04c0d4001c060f25800d00b40510490754150300000480c0e9003100c00134800e60400c0d0100c00440d610b588490091042c45405030860042090124185500c1181c1a04036018a08a40c0441c15100c1035501d010605460080e40183c080040c46060130040180d138000c1d58180e8120020101d48076005403e41e880310b1011a415080440c1c1c6204202c00d0b16100c54010800fa0b4406050038215958421056440110301d401004440440c442560750b6141405800398403ca5004541d40c3d5010041c1d506e401460000b8031600b500308002c0791016001a200748510407600e404002003040b511000f004001581000301480d417564107590108403812034840c400c1c3c0d00c40da18156240b400100c1400002d020301c00104141e410001800700001c8407509132500603401210150f52034000070000f50030550540d000820034003c00c0d943d2035154214000e160103e1340070f5803d840400890004014050549005032000e4900c0601e40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 838685314 1250 838684064 838684087
    0xf1c2705131d01021b0c0f01141603090501030b04110a0f090504060f1e0e0c21180f01020702090708190509010519090c05060f120c0a080714 62
    0x1c0c0d0721045212400040c90a8458080c1407025509030300b5140c990b074000400d00c5140c0c4c40f140c00f10b116582da201c0a000150526800186003214510140b410000800a103050340d000c9035046541010300c803505148c03403030040d00e0040c1070310341c80b44101170109280c811200e0403400c05004034800e1040344400300d4645010f00d4029030707501100202403410080558404030300d0f031f200c074402ca6000d00003182130100450300d043e516000410742d00341a0000c062140d0342c06c104000e01c1480c0e440d0480f048802c119166220340b1301030b5460040920041117200803042c00e1201e0f4801200810282082020075030781940f41400344942070784a015070094006d5000000919000c1c81000c003640c004014181020a4400d001d0b00c047c142e8000fa241030041e86d54034401d224140325071140785607494542c0d00044c008080e064641c8061070301c1d60310a0f14047c04000502070320202c01c40080310102c1601807040d91740d41c146501406a660040300381c1c11b005c50b40100202d040a0300074032200c074401a642131640e1801145006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 838686564 1250 838685314 838685329
    0x806030f0618030d14011e03050705060904140a09020907050a050910031404050d081503060403030b210601050a0f0806131703040809130209150c0f1c2705 68
    0x54409a000600132806100780902507200030707503e8808003039480c0d4141005d5217440640705484032403244c000a0704000280e0003103110400c50764110350807a180c42e80131001c200030749020740800c079011201c00c007009051041070303125042082c001e45240c40c103030741c0d13510043d1f403280b080400e410701290042c03200b00201d1800a0f40c035041c1703503400e28001c10704803070049440f5012032003590104d078690440980210610b911010040c1d110a10895402d0703825904808291140b0000e0406410181c5034400444581c1311440701a142c5007924054120161100c4511901c500c400c0c0036180c840c851000000428a408848800a869105004d41aa5294000d0484145294410440303070040030381340e440c0c000900c1c1e07800b66128500852034966100720400802041c20f44548480200b14418841c000860311516000e0100801c0c5030703082551610205c00c070900d00030700f000c850740ca42c0c1300b880c100c242070000a88111500d040c00f610b075081024906207108905821a1564a48013040300100704168a040103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 838687814 1250 838686564 838686601
    0x803191a0d050a02060c0d12060b07060f2a1d1012270212070303140d060503060a0b120a050a060507031b02010204081005010308090904020310020c0a030806030f06 72
    0x2c0031035040d0419a40403c0c19078108080d40d0885400019581c032000b130300b040042c888400708960401409040081c0041d5502520307101902203036440c12204040c0b02c85500a468060075507246d8503040112101800e00c00b40800021000140482c1c070304400350318080340307990490b01c00414080030094400011100644104900750311107890344140c8504c004001150030350040c0b0401d9110408070540140701030902580c00c1c1812a81c8141410004079078440701450702c1e00d03041003481c1e0b950145100c00c0d201404980d0080c0754980107410070704c40c54140545c405c40e0f004006a904403070021072100302c291a98000080502160446175505d00000c2c0799038420b03644600c450400044000c1000f03460440461044a0040540c3d40080c007400014020000d0756030100d000030050200c0c1d07040d955020f03206c6c003802c61000d000d103000f000030030110368040c8400003114449043c11915a40402e00c1c6c41c0d5560030f01c20040e00802d42c2c000100301107040110710f0190424911008280584401e88807403e83e02851 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 838689064 1250 838687814 838687823
    0x1080402030a120c030e01050331081801031805060c0d0e01050708180d1b080903031813050402030a030e01031e0f15051f020a020d0803191a0d 63
    0x40810348000f48425601001821040d80d0b0303010100c6041c94040c0c0361724001c8110505000041c000c0100300241d04403d804540d0382c020080781c3c1d40041d21000e05800ca0b90150040001c900420034044c1003100168004004000340d1782132000a00320304280d0031032008030002401d541c0006c40044d4048c4110b00c002e00603102c0b80480007507045285c0306528211036040e40ea507800500900180010300d010302c0840a0807eaa400103442c01c01c40d4404040c010f00710401c22070440840d41c1c41510180007000e03044c0c1d42c84a00c041c041d02e50307440ca01d103241180146902040b0348203603003e05681d0015445031060750b226550140c000c4c0726400181c2c6043d0351349044008bc3c01e0415498038030312040d415081003d4512a0240c060204210b4130346801041a40c1c20701c4504c0011a401c5001089031341c1d65007000c0365080ca16402c1c851107409184104a007003030742613500650400801c81000c0100300300f207801540f04d04150440601025030702c030510f1040c1c552074518510704060006e400c0c400d52030501980780341d142c4203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 838690314 1250 838689064 838689073
    0x105100903110a051305040201030c0f1d0a0e0c0d0c0203092101060f060f031a0f1002071a070510060f090c05071b08071403030d0506010e0a08060105130504110108040203 75
    0x444000a01e00c01d21703035000c0092152220148000c55806010316900c10f030303540c10500340d040c1c000303400105003503070b1803204801c09013484020700156100e51700700c507010b4010040860004d103082e01c21040d0540c80980f046a660380350501ca01110752020085c1c0f0074042c40102241d810740c0c183c1010031401b03421401c4500c625565000001613a05894a249000748055204c61380e4200705070780003a040350480074200590403200c03c0745e80030913a1240d0424503268001c4550b0340c2410f00f20b000881c50114950000c1a4541e60049400ba0250401d405000028420000c903200305450409013416118103200d9074043c0e01010109106400780340d00040300480303a500c0c04a040c40341c0c0d80c5696486d04d0441c06400c0c0100c1e07404409100e20030041c0031140c050100c0310b00b19001d80b920000840d9036481460740e00d0440d01d03074583c00b00703145030f109007080320702d070140107004400345621044c03180d407074500030f01c5500c0c420302296072008641801170103520b110700e8001c006030807114941401525500700041080781d040c040e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 838691564 1250 838690314 838690319
    0x20109152c150907051201020f040e070203120c0403061b0f1b080313051e0c060d060312121503080906070c21020108061806011110060810050105100903110a 69
    0x2070b100c42d26102d03021200060082c18646400d10281c21500495100e480e40104066070301c1d0442c0e1030484080b1250042042e15070345e00e08000324114010a01c054402c10861400e100c0c04000200261060381e00605040041144404008a9242c60008181d010501054064016038014441070324015081c0140324100d0100703a40d44102544110749140f269510054903d06105040000500c81d08500c040c0d4480c01d0401d001e59659104544602c5104880c00203040c191201940c004500540c0d218100c0f02c1801c00001016110642c00ca45400342585000c2c00c2404000d100e080134000c4a03040248103150858200030b00825a1011600781c0b000300c001000042c4522068444058070200300b01c061780c0c445901d01c0018080d8002a141c1c03442003c81e0407011055542d00200c164121400342030200d01c20b000c4070800ca041100071b8440d07040711858220001000da0003c2880c080000e828641000941e886004000e402d060988080740020421001840000c50380003090781036510040030b101d082039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 838692814 1250 838691564 838691593
    0x5210f010e01020c190308011e0e090a020f010f0e04020318030406020304080706020102070305030f07030f11071b03121b051b1003050c0f070303020d050106020109152c 74
    0x8034045901d14040c1c0d4001024030078880c0900040002000d40f52503441c481d5107541300240326580c180034034905c412584c58592031490490203013000400140c510b0700760781c1c80c200c0c0e10240c58100a5034203038040c0400402191056109041c0e040104010782c80b04500d00c90801c090200a410003001d01d0003004400314100569103082002c1d200416150b13008690755810714464034140f44a6a0010041da030042c400a00002d0700002aa91301c10f40d0f00c41090415a64440110041c0280304605900c2902d08443e800030104403c004020a46c001c1d400483c40710800005052003000520014000004204075180c00ca445003200700300500c1c0604c00103c5041c6503071180fa0410300f10340d0500b5010760b240000310545041091560f48400c0c2941000c110030b18008456203050710500500051818000803030304c04150103a8161202a8003001080200b50707100c03100a4000c001032802a82c49901290708019500e0745401540c1c003030b1800184044038805c41820a041a03c911603410f030940c001c04410541c543e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 838694064 1250 838692814 838692821
    0x1a0a03093206060607060c030b0a0303080a11030108060f04020307150302040e061c060203060301020d061202040e031c110c010e0d110a0f020d240207061505210f01 72
    0x4070640700d401544072403207081070240c107040403505402900220104000e0b070351070b441075812580c0c020402103860500032a00f10000c0080d46101c0b40e01c14081c050200901d6405441240f1501c604242001604029203102486020034494040c140e0f1000303001494102c140030f00c0325000313403000e000c40b00d603d502c4503400c000c0c00c0a0f01408100103031b0301203000c00c002c8d90f640e032520703421043c10745492101c80c191640307144503c41902805440150000041001a1170950450b00b45020302c00302000182d49400380d200803100c81ca0400ea10070740c1403158a641544010048070b035000284000c50341c0c855100407106000c0c1c1921644800b43e1001845403181074102805564038a035a090054181c01d01c2d600d00142140c40c801e403a08405501080c10840000c030070559004081d50100c940018046661030b00c1c2e0403981c0404250070b1500e010440303155141000390060804907120b501309110210502e0741080745543c01e80b141c0355010012402e09280501800380b680c0d1032147c4002070381e00300743d208800282074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 838695314 1250 838694064 838694093
    0xf0d02190609061b030b0f0a350615010e060a080c0c1e01050109020f040909020f091e16020d031a06071a06041b0509040912091a04030503040b031008010f05150a1a0a0309 75
    0x54000100300030622f01c1e4103503c214580400d00304150b0004071440400c4850051006c0c0d1b8040c0071140c4080342011010505032003020f1092011541c41407400d41040941c10700d8940001403541c03d0500109041c003a80c02990a08030460002310304152510401d030780076203001041130742c00ca074045181c25901e40b142e0b40228400c00040314601d08110306082031801000300100507992140d08105a0f00d20a540030442184050151502140201000350500c1000c05400c407425446600040c580042003240f2104d080d621081503580c0100383d030b9500074002074507481c0d420304a003102c1001903441581e025034060302c0e400102800000f039044080e503800304017003410094500826030500d410000c00302c6c1c030031498140c181c00008080c04c0c146160340d4260790b030049004541300918084001008078203000150001401618000d00c41c0a42c0c201144005043c10fa4900e007940018145490203818094440c0341200c02418860014103400c807002200754001d0300001d400c041e101d28205010841c1705d44160300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 838696564 1250 838695314 838695419
    0x30601060e090a0e0c130615020d080c0a051b190b10120c26060708160f080604050c09030303090f0f0d02190609061b030b0f0a 56
    0x40704402000c11a0885009000b68102d6052a0720200c246034041241c0b42d1005003662082010040759043e0b0026000640001c40d03882d028812264000d43c3c00241c80a0103021a12419015201e41e82e0214071032140a50003001321740304001403c0d06402c000c095000079030605013030790f007805828910998060401041501c1d481010f109014842404c6100c5100401c56402e440988010035600d0320f086000c00d02c1400a01054a000104448126490b202c0d0310308964040d11103524000c0e4015059400940740130703981e40b50a404201a5502903614142c61008684881096544032810080680001440144442020701646480c1d481c100003441c0110302c0315000d0260152859146403420420540e54070284d40016001100d0ba5004920700b030144481c0d0070083d20200b01424010050710680074000c0000c0e181890b81c5060030010001d105148140c3d507428007217001c1b1351040040024540d1700c515170021846900300401e0b100c451103c244400c4551000c00000c07040f2601c503130101e826049422 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 838697814 1250 838696564 838696577
    0x903030a0c031e200a020d0501150e01050607120311120901181e030203190305060117010f060c1b03030503150406030c2d06020a02010933030b03060106 67
    0x34100b603041100d4801c51010520101441c141d440c2c0001e01c001c5503200d0003000e030464203410078010355082c486404c0081c2c020701800c000300c41519140f402046440d2405c0007808002c9804650b5051420000f130481c0c00040100d0b04028040d2500810715656215038000d040c0c0e40c441c48400f00e154175006c0d04070300100caa5840041d20b000b0803000e00f0740d0031141c00e115015459080000c001100c11082036417604041480c00070410f003a14060b440e5108031501214419100c4190b2504668503400141c0b2402c1e0030b0340ca6040900703582e200c00721805005c2c0601d05100042ea130f414802d280c03140f900010400e000c0c0c40d61210700e14003183c2c9407803032001c51b0f001030303001400010030490302d6030700c4500c845d850340d07400d030340403c4040e1850f140d50070402220f004941c82011079004201043c6a18000c0824901111403180c04d80d03692a10b021f075440b00103000032404034000032400545200e101c2548a1600c001c0d613500803002c5400307501c1035411413404000409242d981c2c44200c4035030b1020020788d4003130521502c500c13 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 838699064 1250 838697814 838697837
    0x3b030f0313080601050312070c030206030a0903022b0c030903140f160e06060901170106050405040e0715080618090c1f0f2a1203052d04080903030a 65
    0x15001c070320960403800990b4402d0380100010348000580c45c00c0d807446c211005481c0c03ea2460316007049030443d0b0000c1e40c0114044103100c2801115031281d07805601c203400b207c0c0c3c2480d07000c01c6880b03000000c214405003048804500a4514003070651400114030901d004078245446e5134508801100c91400e58096604c5004420b22a410400c102484420144032041c45188ac1c80b12244410300004d00c02c0340600e401007004411039001d01c21501d086134001a00c6281580c4490f00104103802512485115a01b0408900d0381b1140100e41c0409841499411892800c1c2c01c28050702c001401502180e00108680394501c0040400410035028070701c58405441d490400710b0820011083c00031040300b044400100a8034020713004800d8862030400303820040d25482804600f9404c0b001c501800800e80402c1d000150100310103010000c01c3e904180d1402c1107280c80361040107480160056200d005002030500c0c20001c0480c00c41c0307041d442031003040964500824000860f09540210f411071010910040e6032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 838700314 1250 838699064 838699087
    0x90f021003111303121e050a0c0f0b0a0c053402030607021c0503160e130c0302070c08010b0901090504060b0d0f02120d020c12011506050d050105013b030f03 69
    0x1000301c4005c90345405018004040802d091030300d484035041c000c0c4400001e04404007401040d000b940190058079144d01040c040c107205000f02c008a6007001c52500d81920983c0342c901640c00e0b6481501c0703088038082200b100700d249400c03400705290500c52201c00d034158000184e030708104083c810b1400f03a000d4003100204620000701032202c0380814007440414410048405903041098404880c149003500d5a46070940105006890818002d11440e081001c03010784207030160028000380e4466036074600815a603080f40303400ca44c030f880b1016a21018200c01001032924a4104541140c012400001d886070345400003148000110000c43d074540422098406501d085d90003210361410781401b80a29a0071400d00035100d41d0341c111204d2081d4495072050b50302080942c070040320062503000b80364015469140c042e00d10340100d440c5501c1582044004551544118600700004403e40b403520140115040c2410360760756030b518075964030481801820707180d07682041407441c200844c20242d541e0704100c424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 838701564 1250 838700314 838700333
    0x9040b040b0418051b06071101170106090e37020f0d05010611010504120c03050c011a030d02010917090d0204050103060c0215040b04080f1210050a09090f021003111303 74
    0x90b0317000c18001c0f0448081182c80e91030440311020707480b65191182000b01d10040c0c4090312107545d103000c00112000085900e5803c02113403400d40c0c10000b82c003802c6658510800c0043c40c60070800e80414901d0807a98507024030340000110200b44c403c4009810880c080d5200451034101e50407800c84191200d00412109412100240480e031100c0000c0c0891310705134131004d06d2503e12a210508101d0721120040525216605591204c0c0341100240180c00c0307428041c041442000f49014401e003d440700c070400142c0144034050300c00703501440c2800801b00401858803203402c800c4550f50003000245201c030060b0f499118031800303103200c0e00d8000340c020b04060000313141c08026812100003034000d6080c0404264004002d0354015480000c00750380381e039524800002d500660101400003030326901030080000c05440c07420291002612070160442d03642011109544d00888050014407040c9440ca002d0305006d12400d92074007090801203100c1c10030010068481d445400f0904030f0302c070680000e0081000405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 838702814 1250 838701564 838701583
    0x130306061d070e040b0406090c0e01090e071b082706040f1a12180d08130f2a1d01050102031204060b06070302060a0b041109040b040b041805 62
    0x1d061005110140d080300c441d4402070400da043c0250152415050b6940f500f010401050191051065a42d80c020320b00107010007181c440c000c500d00030401607041d40b0401010044030281a030745903140d1904001501c2a11040404c031008a144419020100c0c24102c02025000003240301c01d020710102c00d001800070801c1010151040004100070890040464004402d444d1000d0455441e5a80755030303181494441c1e02d1400024200c034100700a00b50211907681e541274600ea200b43c45940c5074079402152802c03c00c4800494441c070615285000c20000c1d00da40301c44611903900200200890710800a83d0080c80d984480f10401c010300030700c5030380e409188180d40d880305004211419418080080d4590242402d48458a0312030b00000d014410190407607803503004040c1c001a510003480c00d0003525800100c0d07a14416608010801c10700d410203100c1c0254490001400c24140503500042101801020421980c03068076480000c0b010f5a8a200c2c02142210b041c680c10f00c801c00300c4c58003074100324504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 838704064 1250 838702814 838702829
    0x80706050a2006040803070e100c080c1f0e0c040612030c05011b111908090d1106030a090b010608220812090303010801060b0903070603020309030f13030606 69
    0x1504012654100003580c00c51801810102c1545012003000c00019612110750b02c0341d80315260600c014054203000a501484056691340214640031007807211510210340f803e40010900325066000c2120780e40500406141c407807d8034045025030b0300b901c07080c1c84020b00b0703c80b040e40c0d01c0c0c1d071040c400380c000c206600413510140c5040c0599403a0840b254400400400c4c082e0034000040c0652041000a50103e02400e1102945011411307c9050040000501042040c850320a5405204442c640070f1a01160f49500c005643d20b0045290b09000d0759940032101103400c4469039010f00003940d00c000181d0b100f08a00800000c3e1740100382000b100b19401030b8060010b000032002803001202102e1503400e02c4440304504000c0142171844c0c0801e0703510500003031203002c00300d103024095842c0d00030000314100d03415003000340526074840849680501c01e908a0715490752101004120b502e001e60061030703000b0b0a00096a0400d2200790300000280d0041d030511041c0d000100d024000c1140e940301e028090401c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 838705314 1250 838704064 838704073
    0xc0f0f07051203120702160306050712290315040807030306061e2003071506051c0f170c0f01060603051303030b061b0c13151a13081608 60
    0x1a031090f102c0c880c00f142c00380c968038071800168282d0300070040d50307400b00065803a17000b03825544c0c10070100501c025606500041c121490407043c1c04d026001d4004203414150050031040911143c039020ba81d01f40050b150180544007208441510320700c80103104c5d901503448103645040c6860000e04441458010006020b000003001c0c695892242001c8020846802e045680b444a401544805400181046682d01c00060a40100a03160500d800c15042d86038050114a40304c0341000107040a05c234818a9003c0440d44001c0414030034828082407078011081c0080300c03080f81403410f10a600c4084482d4495001310078044401400348101c0c1c1c010580c5103402c00850422040084e008600400040e04140e10b46000140b590b5484d0200c520404050940d402c2d243e04809450303888003201c0e50910701c201680c4415046000c031501800c244620040904610b40307090541d40c280c01c0349062002c01c149401400b4807041d810f21403aa1002800b0b10390b009003d501321005042c00407101c540c000003044d810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 838706564 1250 838705314 838705339
    0xc0d090e010e04080403240b030606100813060207051b010306260f16090b06090d020904060b030607110c0f090a0e01110712020d050c060106030f020c0f0f0705 70
    0x103a00e80c0036054620001e202d1901d51503508090046008940024010074100180307003a403012550509034145c00d0042040c4400c00a180406403290012101c1e6a008071594601d4103010b441402c0d030b164014560081484081760f01e4642e00c00326000785c01304642e954000d12006030006060f0b10594403a15003441c09002084c107281c240044c841c003580ba041450780401800a500c00024000684203500d5841141d913501c10020089107071500c40c1c85410006441c00b0300c1d0034401d05010040310b40c1000d0140120f804c80d5100e50070b0245400000b00705860240d501d032146813859800707200b035038010001039480c68071140350405503074140892a040ca51003007000d440792405035210b4084690380010f641d0800154007204000321409030001080342c03500c1c800006000020895900e00c03c919109041e4220b41c0f5600c00080265114460b0004032078181d44104010040e2038401d410500e00d00241d400c0140c00c10301e0700351119181808405d441b008c140c006d00b0140a02117810031900d0001c080450346c0c0395000c507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 838707814 1250 838706564 838706579
    0x90c1205060609010c020612100612060b1b030c030a3515030f0f03031509040309090c05040e0a06050103180c210506070e0a060e0f1e060a050c0d09 65
    0x80f44440c0a410f0009916410b400d550b0350405843c06d58802c83e60703500d0140340090300c8000740c100c51300400c4082410011000380050ba188100703401c2d81d0f5000109441c0c1110200300c0362307903042c000301d9000b0644810451404800c82c180040c200301c0085445400c44005000031000c03800040301c85940a21900d1074004041d044278055440c0c00541410710840c000d140d90002c40d0403c40b41d0039050300c007889010a00c1961040000003107200b0145400030400c0001298100f08400000b500c0c00340c00110880024004110b003076001c02c08550301070030050300c1d181d5100d00c0901040e40445850820359030f250001c00103540c02d4007540000701004201090104d91555074040c5502150080711840c0d1150300e01041c01c039646419030402150000208c036103500d0007900c004c00c803c0440c2182c41c021801140700191050003072052031480c2e1001401800113111850600100150700603d070103011680076900000c5458041c0106401b80e001d0707950303c3d03446040c5003815107041040c0e811041084000c150410454 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 838709064 1250 838707814 838707817
    0x907030510080703030c0c090506090c0307050405040501030f050c1903060e0304051206042d08090114041503200304230123071d10090f090c12050606 66
    0x1604001445844000107075192503441d4000100920800d14040181904880c01540703241c82003074442c80940e12484280e0603034000f9a2507503000a50f0801052802d00482d0145500100301d103083ca080960b161700050a8036020780c0b00382d88103011121002c00f032040900c48030012201c10380784082c040f000700580600302c111174880501500c0d6584c4c2100c2c19100305001700ca000b882c0081581c1311840300381056588412040d02c003181c814413420201c1030b100e500641f080c82865240100c2a4003041c8607111a211584900d0142d4104510341019110140c4c045000d000030304195805100c904a1104d8040c044403020380d42038102581114403809010300c03120031207071b2199003da2080e01000b58454031040d03e0010140b0f01c40f180d42099280d0134855200e241e07070545003400d81c600c580300e86c581c03043c1503c5042c0851130144009050780c5020045050222214000f40d5591034004074581c4e803421214440303034144d041a610261240700700d44030b480d405040304603210180401001a07003417140001c0e000307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 838710314 1250 838709064 838709071
    0xe0a21140f1818061e010212030406180521030c070f0c0b07050c0a05090f070e0d050f030c1606051206120a0302070515090a0e090102070819091409 65
    0x50744000140d80064000a6010000c00c160107000014030f440c1d9050b1030b040902080383c00c9402000e60300c101c0c4a94820a415240c410f02068010784000038980c0d042da125540020020f84144e500c60090003501180c2c89140760030305009d4400713050702420392214a12003940c3c00d80120046201841480048850002114603ca50084000701c0d03080c03440c68201514125503000755041407010410800b0300102103528010380100716541c9407405d031140100101a401561400c041d1015140081c50503800b80c44c00d2000500010112120040e055490600e88201413009540a41000c031b0701016801d410403440c24000411400e060040e410140300a00314012404d004030701140f404041403603038581040800c561001401038035041c8000c1d06000c0d503114418441d050140086200c50b443c0f03561101c09aa00c003001c02080f20584928101800c1070b4900050035801c40e0395820018034000825a9009050323400c81001440e620f24052a000780002d011a80b01c0c01207000d0210010f46c580d43d401d46055170 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 838711564 1250 838710314 838710337
    0x7030c0611040305032a0d0e0d0c0807060903020306360325110f03030d05360c0114040302060702130203100e0f25030902090106031509020a080c0705010e0a2114 71
    0x40d070081802c0002e512001944070900071701801e133001c01d8569101e100078050340d00a404950309601d030003d8820501032403002e42c86801c0c1e640ca20170020084d403040244010740b110811030f030400707089001c10a02d22a003205041c000e000c54544c3c0d8410403601c441101da0b805000c60310691041c9aa1340031036202d1103841185518039554070300203544c1781030007140d0f0258803082078807452103900c10040001c1020030390000307581c0740e11407185100e509610a039024064036865000c1181407a2030741c2c2c01d20070941c120a8049a00100395900302c407a401305803000d14480c881c032911050815150207040011941c02401c3e01e800e46804c1c004002c0d030380a840201c0ca01021146208216005146e40d08500170103440c0d2000703501c030304004000182075505802081c25109189100010305560318285800c030703c140c48199001c11880ea000801b80166040a84000b074020000400c1e1160460b85042c14194281401c8810302d211740d040000303540c0100c094405450f032500301040b513403140002d2800e06000b0641c1e00354 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 838712814 1250 838711564 838711579
    0x13090204030210052107050703080612030a0f1412010e09030c070510270501020d0912060903230a08150306010e1806150f0607030c0611040305032a0d0e 67
    0xc010b003054040000e59a120940d207419036040142c4000d012364003480c01500068007480c081a001e1074541020b240b1049208000e6152049500c0250b41ca0003c5055039024014a05410840e900603036005210b00c5100068107030f525030410070a000d01c40d01c0985000b5481d802441100e449440c00212603099501c11540c51402c1c075a0502c040340c0c01c4c80c803401c10001041e060540d0350b00d0100704600d000c007602d06c00d802b07507103e52120b442d0072120200c0038460800b8000490700c1c1d04010a03801e03400a402203001e440d00d4580c000c0e18014603009103c03034816000f03d0020010755440e0700c40c0d1200c403294000201d44c0b00c0201145010380040d640b0203040c00303035416555502c00800c0b00c030150743e0810050a88000c090306c200b031500150b4540c10000070900c0300d02031000e480031424103180c181d04950910354991038141c3d45505644a440080920541c80703900780804000200c04104c00700045c2800000c900060a045410390542e41614041010611b1459000c0c0c0e1b1101030240d00558058204101610703840c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 838714064 1250 838712814 838712827
    0x140d02040f020d0507320f13080607090f0503031903240311060309120c07030c030b06040605060309070506131a040e250c02030106030b0a021309020403021005 70
    0x20000d00a04011071203203403000945018031075550300b00d9482281e10342c0b41d00c1d214100e0703e140079403010032119203214201c0d0706001c1010940e2542d0080c1a038022080ba03054108801040005031706103c1e17821a282036402042040b41c1c2a90025106015040d41100c0440c07151070300011a41e6409601940074000c1084880d000b0381a100c0c0e8002184040c5c040d8502103803040d000d0400c01d0500d65030000703031b82c038003080400007105040c0081182d001c0c80c4204010b005c1d0340341c4080b420100d034005904085540c016000004046650418003070003841c01641c0382140c1e4103044040000301e450303d62060380900e60a1042100300030001c10042c0441c5d2040c0d4042e40d460320206028100309640703030402489088242d010000d10003145010f40103071994540301600c60307224400200241d20041d404a030b507100e41d640f0b1904040c0c0c400d103464040c80c4c0c030150012034103545039641c024030524100c0d420307503c1c284d0100d0748402030000540b0341d00050100100c11880c1a0031500070640a08200e480c1800303009000440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 838715314 1250 838714064 838714069
    0x3080a0b150703080105060f160305070b070e010206090708071a0f030702010207031209021f0c0b010602060910110403020925050d0c0e0102070509100806090114070504140d02 77
    0x180d8140c0c8010148030581d014000c8080c03080d0070203442a40050301d100300208160401000312850070140500043c10101101ca4840b0f0f034800000086041240510401c0b000411014109002d511291130b801e644000540009141590080c00216683d22540782048060408a04513003910207035017541d41c2c08001da111020061040001c06440382030004200704040da810b601070058903110b982d03140d05180300035072500c0540e040520301940c0000f0300e81101400d00c88a102100020440b41800078000303000792103000c40320b14244d0100015811230010000318660500c405541d5074500003082104c4041d0780780804082c041d0b80402401580d944001c1204880b070014034402003150301c1c0c0350a03101c01034400018480e411401c110381c1c99a09207070001e00030300e02031042d81d0001c04042c1d005025040ca00301c100301099101405d44051405000000b040c0a4404d105180c81003613080008920750522503855502030301c00a01c90000c200702400203206060001c01c01696510080741c9042c1c1d510800d000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 838716564 1250 838715314 838715321
    0x11d0f070f030e1207030e0d08031306180302010603120f05040b03070e03030d060f09110d0c030605040c110d211518050402030d050405010e01122705060a060b0703080a 74
    0x18042050700c294038440e0b4510703130900000e1000503c29a2415400c0981c402441000d10303c60400402a500c02d0002480d040803a23400c00107081d0145c20702240713440501400078805184641c0035030060351a40000e0040c405080340ba03800000b401c6c6000043c020300c1380700040860080c7e0041150310b071000000700310002c0c410030302814035081c01025a903841601604010083c8003070711605501d21040540082e0f00c00c3d032840340c01c41608401c81c0741864918a0a60303500140b00d8804542c0605a4882e0086502d03100c83c8104848426036803200b581d0300d0000307030340300b480d12191000c01000c00003501500e4010440300602c400010000700d1380441c6401d440c018243c5200102d4100b08030082183c8407075006280d058129038012802a000e680ca200c0925108031080e00c034174021507021900340034507102113501c12480500014020070001034248105030f44950010f10508a400c03201c031031982e509003805024045150480541c0c001000000d00c3c0000101c41c5003d00f01000e018840e680340080d000c10035680 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 838717814 1250 838716564 838716581
    0x1050702011d15190221070201030e0318030c061819031703010504140c1b100903020c0a0611120d0b030a061b020a0b010b09010903140303011d0f070f03 67
    0x10240346220030341c102c07004641e41090030680c40c800b41201413001c145001080014a407484810000010004d580f0710f02d046074001d0808a04140d66000d007a15905d8080c006400c06070b03003445541c0748031031402e130400d45885e0740114064032402c01040301501095442c1d0606039040300c2600c12010400028440c650340c3c0315103a001806662402040d42101d00181000354142c4000311020091281910140444e401e070446200b8429841000003011801100b221914010b40600489001d41d01303047d00281901e0403001c0c01c0300541d00695040c400e03031410b000710401038080703480c013010b0000300c1850059880b5211143e80c41c010300c0000d4900c2da4070116420410029501130b0447d150700c20f80c3d1030400c00600d482d050651071440c0c03078003070306c1a0a0710211381158410340248108003580d0130b05d200c07400141c0c0a89100d5062002c4150000001010181640030b0400808050341d00c2c0c1d07140040100d081e0201e90705864151522004001d80c0320b6509581c1a04407015181503603200000c01c106500030a40803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 838719064 1250 838717814 838717819
    0xa0f03020321040218160e0a03051501030209010e04050607031a120609060c1303080d0b0a09050a110f070b180f07150903021014090a091a0f01050702011d 68
    0x101c50411901c00d002c2e02c4240200e100303807400e901c11102d0300d500f040c00e5141940c8402d8824120754000020034400c0100401c1000c004000b0781010f5039a507a614a0411000342c10618140448010415450907181c1c0c1390042c101d42803801c91a20b0156565034690720700501c039030300385a507503400340d4007400c001340301e540610b80040c00500c0391034605e9046a45e96801102c1105141c410000040d2650a1142c25140b11b190b170543c0c503c401d02d056690b089100d41000c144212078590382c004c20b03040ca90b120006907000b05204900090b050506403d0b80e03040d81c0203043c0b0004100c0c2d040140c2030f8661440c00841e000241c101140c01c40130b407100395034000c400e01a40001c015a1140c0c1d6090004d0003030200e181421641810540000c1d69034984041e506030180d40b2000c0c0d805840f00e81c0404d01c2a000c0c0c05143d034401c641c0801c6500e0602404001085041507810000400c2da8586024100c00015802c15108100031140003c95a8003803000034068420f05c000241004001c1040c681c0b14410718040d802d404600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838720314 1250 838719064 838719097
    0x1406040507140f160b0906090f01020c0d260c2214010c02032e0b03161a0f0307030b0f0301141305030702060f0a022506030509160305160e090a0f030203 67
    0x42c851030b13551f00c0548103030025004005009428400510881d20242c404002804c2040c50b0004142d40306501001c400c00301e002c00d9800381c1c1140c50142c40040c81100400f03c100e80b51508004075070300320940d010900340b00e07040041045c001910403800c0100c1d004000d1800c40300017041440441d08082a607489030411544610301c0c12220034141d40a1845151240c40c1089282280b6042640d203951007041418804c1e41d98205100c03140e04c486141302118142c00145180800e80d02009002e644110707100c50019907a07000d08003561500c0e26054130f81320b5007100244450f214810034046001006070040e44801003804406c0200401070044c2e5000d10380050031180c03208082061034010340d11400020005006040f02d803000b00c00e03844030030180b80608460310310000742009020740003000e020b07050050364800c4200c0b0324980104051440003461040c400b40034440508100c0e082000d1039508510284c1c2c2c3c1c000100306040100107000c03040c00740c02c016007000b1006036003001e900310b124403034040300c1b06240c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838721564 1250 838720314 838720321
    0x11b020601090f05010b0f280807080f10170c0a03060b2106040204091703040f0309080c1f051201030b04051c0503060d151406040507140f160b 63
    0x200414a28120307010307241d041c000f010649a0000449409019041607070009104c80980300303540001801e9030442c42c00c054003010380c44c6421b81081d904003248103000942c0040403c902a544180c0c12500301000c01001d0728507040444405e0070601c024000d14140c08210956041882070070002e0184440c4e000d05980c10082c2c80e0f0a1000c00340c500c2c02c145d01c1c0581c41d01000d103011034110003400c861004070640a020b01d62650750030440949001d20342921749140c4440800103180b544002903005600c610340102140303c3c1c85c80d01a1811145038004240c0d0b4000740c0a45800707880b90700c0614070030701c511804401c0348400711400f9281c5000341d8a2140000041344004001c02c2010014140260301aa0848114108400c039110310b036801c0e1550710000039030030b00110b026400c2621104490500c2840c401d42c0c0c403848040d00f8001c885062040c2040740840e0030030b006550901cbd100741c50f00a070741d518011494807000d8400c20507034440c40034004828007001440860389490800039040d40703540303d0540e100ca800d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838722814 1250 838721564 838721567
    0xf27040b060301230310140105040c0804030f141b030a09051f11070f061206080a0305070b131212050603070317030c04031502121302150f0f03040c031406010b04050f03011b 76
    0x2c00d010389c3c0c2c00356251024080c0b201d802001c5c400d1149074140d4036020a0380f403251040300e10450800b02c0c80c4d020b480c107025049003290f68214101003104018015501c03600d108038020040d0b403c59100724042c0581c108200420300b08180404066100c90900c09844031030081c8480c500640c80d44034078004800c84001190a6600c00c030003213183d040c0e200c006d000e110340350060b4503100e1100300c070000c2c04140c003000711000203030512042035072110ba210f0b032183d004c0401d5100c0c103a1000000e1041c10002d40c0d0602d591704000744510560350865001d600421085065595403410300208640b0030031034010100005d4210412130f411540a541c3c000324408440d054410008065080002c0a43d41254000002210700001000342c001c06c0350004c00310741c07400303d0f2008003e28590100d422039800003410031480841d15030709801940102d210702820a840c41ca181030483ca00074800308161038a400c042c004014510480341a40c05551080b10000c04000e80180002c1c010840b868440003080300607000c81e100306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838724064 1250 838722814 838722851
    0x904150503060a0b060c1204030b010603060f060c14060c031806010b090909250f0b09030a08090f040216301b0209100e01060e0102030706020f27040b060301230310 72
    0x302d100b0001640b9590b00c490cc00e90550740c0034098180c0316a401c46c81001110311510b58109018094a41b41d00d01a5000c4601360812a04486010042c0da000041c8960044040343c0981100c12402c0541100e50600300421100e01c1841d01c083d214180d41804a50200e0341401080928520032035802d406040c00c1110400c8030010b40301d207150013915a04000b03101c507603a504403145280003c01405e03100c011a03580d4a815041101308940201c030072108100a5103442c03004121030b0f40041d0f114403403008140303050404110700d0060340348482051001c90300c00e18005001101c840b000c41c102080022004000742010102e2018083d60010f00903003030007001480020442d069503048250404a41e0304d030304007038401c0c4410900c401c0c0164810030280004c68241e90181428070749908200f40380c218460400c60b5040e241c010008880c4021131126481c500c0c3c203105079820808243c0ea8181990714017249950f8a141014044180b000400c84c8520941d42c1440b07240358030341d0b40202c200500080e00b800d40140c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838725314 1250 838724064 838724069
    0x40302060f0606031803090a03030201021206180f0402040f05070806090705041d06150c0d080109060e0a0c12020a09050a051509011b020607080904150503060a0b060c1204 75
    0x98016140810401001c100820384507003009841e035859074403054034910040c0c40c500740e81c242030b000911080e03030980d40301100d4400550081e400980c8030010004659507141c4050a13243c824408180294100030141c07801d198003100c0203c2813041aa183d0010034064001013030a03040f1240f07000200507a46801c44500707409000240d07400300c2203590300c1c101614142700d04e0003410b880924103003d2800709007081f04015400380c00648410152119400c002c18150000c00b03e50b916500000d01e06403e40d94003003602030060000c0c04040c001140780441540303240310050511010580c90314010140c1f54001c9007510000801d9142c00c41d0303602d07287d03080107251500d9802460f102c0d840400d400100c601c1c21003000000b1032809814185407400c00c1f0010f40703142640140284100c42000036900150703480c078010300f0125000c4c0310700a07950302c1c01d5002c000449202c0c10060070304100100060003103031800035140794060310000000407088803040003e82c285c090b03103840781c505104a82d400004421004040c0c0304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838726564 1250 838725314 838725317
    0x525080c010c02062403010e070306090506101401080c1c0608190c06031d0102040803040e1f050f01050403020a0923151c0b0a2007080306040e070f030b0403 69
    0x80c2d81e030a800100c0e2188000d650001c03120010048400c10b001c600400e00c0c130040350040c00000e480b0f1b032412195062400540c810b403a025918203000040c0503041c40016840524486900040340c01c05811080f03140f00c00408504022000d00000e17070f5070201c00700303c5482c039201c7c081004102030341e8500750010b001c00c2d006000d840d000d031181c0d224600c2154072078a00d2183d0302120301c002042c01d100b0200c00500109659505074154064201c0c5551400c0c80200301400105002c1c681c0e650404405055103400a0803103440c0c0901c0713107814003001c4981c4001606849040383c124040901d8013004a455018940000c0e503ca0114040010001c01030750205103421036004910f07800c840c416050742c030980e208039588900001d0040503d8814600f81d008010170003078094034140369409030349425104000446410b06aa5a11640186481241406a0460303440c110031646000a04c0d9954407840c0005059107000f540c0702d04040c00d16410602415014040071002e051038a070356414818854003065400381c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838727814 1250 838726564 838726571
    0x61c24021614160e06150906030901151a07110f0a1d010608100303120f09030c02010825081005150d240b090409231b010f0525080c01 59
    0x941d2020f04001c0c0c1d50884544646041e07a69035404140301e00402061441005000104a4940d00355160f0019501501e55500002170080724140c0e84540302207250480807120807100c80805011100308110358459501c07100303102ca443c5052000c43c4c05422914000350b0f120b03903154404200c88454240300384a4440310041c070202d50741c0c1c4e124180e038640c0b0152041d403940e0705045818404030380680f1641008140d02800000e4280c0011514011039003030f800120009810b01d00c09a080d580c4c002c14041c0c00000d1601c101140300d00c4e84641c56401502549024140224140010312500101a41d00014100a010b0400ca41c00305070507905164400e00040c083e080c03030001e21610f414000d408bc4101000d07a110702001060520a1203002074000c0070b01d0f2640203858bc40420002154010340600c0e16012210f940a007400800e011070400c0e01c10034110039100508400c8481c1c581e400390501141e1286414800d55900041d5641031070202d1000b0003004207110756000c0c03000c1090030f03c01019180740c000000c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838729064 1250 838727814 838727833
    0x10e070b04080a0b072106060206090f0303070e0d050303090721020d06091b0308030a0c08090606060a11070b031b12010e1f030605061c24021614 64
    0xc4a80d4041d034082c0550a0340501d628500149003040b00320b40081d6241000200400910000900d240305a245410420b448a000b000360b6034040185981180110015110342c982080c1350036075a010041c5884204554101d941c0001d1700c980c53b44c10300a0f82c111090b641c0e645030050031559900704c2445402d1400482e0954200b075902d042c5009421158010034104018800391580c00c080c0645100c283c82006000c55410030704002404c01d000214410107590341c4074604800034100700d42da288207550501c4001010805c07942d20208070030307912900440b02c1e10b0701c807140254101c5482d060210b02150354030900c200417818240d820040c601c2241c0e08025072034204002045100640900206038420742000401481101c866114140d440161a41486081c1a5a40d0102080d04c011f91040c0e8107507075160103200550500711881c001400240752a4503960440359200c03240700d10a40303240c034501202d0881d008115151078040f101c401d040340481002c01072403406d25200ca052101ea00021610450350b22 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838730314 1250 838729064 838729079
    0x5010203160b0a14151206091f020405041409060705040b0d0f110408010509120c1b01030e0a0602070c050f061204030306090e060f0106080910020714190512040e1801091202010e07 79
    0x1f1103105405000240004001410000790260b44102c00124895001d000100312a00ca901c140400310302e801000f0382c01804e2841c00705041a60245c08241004000c11050217036081c100b0403204070744190000002c1c44020402410020000d000e01200d11500c001000135255105420a90040000130143d92849081000800b014403a4450070075454003c00304074240380103104411070302200c041c1004036031a0002840e09082c4414110201c801c994041095000d002020710481c02138a0f069600904000811001811038001c0e00b0300c24500d554444002800c051298100344e0040030340e41c0044c0580300d00c40482c6a2a40822610380d44580080d00c00000c03c14451403a00b1b02070400c09006d090321003041000000a98030145003629031103295002ca840c0c111041040003042020300240001d40b200c0c600d862400c0203011008806018020304c400c0c45100c200b46441030704151f1040c0c80310482080d071a050b07405004011700107060200c9600c81e07450080c0c0c064100c0315500e42d0207015035003801c2c2c84070314 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838731564 1250 838730314 838730323
    0x705010206071205130b0c040e090a0f0f030c05012a0915110a05060f01030c0e0603031602030f06090102031008120316050d0203040f0c05010203160b0a141512 70
    0x6400c0006440c0002d81c04a111495004d0f54001d0f000700b90b40144a002d545500d845070105582868580b8800242086040308940c016500b101c46540500480351054681080e1807038421806808400044031040c1054040c9812804003680300380203104444110401050141c078803070880f4001c25030403110559051140005e04103481c0c40601c070201041025000f1565110010440700c114800c8811a002242c82005443d110b05080e00710000d0325811442c0c0510007818ec0e5011100103811b1200b880b040355000710940d0060341c003131245129099003d0002902c0e00d42000400e0816016102c28460110019002548105850409820604e64a0250b19512090301c0e60030710640c8030038008035040c194880c004442d100400c1c60141d003800347c0c0b20101c1e42240d00641d401c699145c10301000384202725103200004000d1100340051414010310210b04800300000081c01000a00e891000448500310355010140544c10700d030764401e6901e800083d143c1c14103003c40e00c2d0b0b4441c2c15240e400c0700c1d003030f000000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838732814 1250 838731564 838731571
    0xc090606080703021207030e100501030b070e03210a03020f0a03050402010905220b010509120307061d0a1403040902070b0916031a040f1515060311090d020604050402070f03020705010206 82
    0x120174665920040120001e0524500b6181346025141c00c5079144880c0c0c1c0181e50180d401000419194100042c1c0a86071080581c0345502a41000303c0300c1140442d00308600447c20500c80103560b9075240c81a048009100b860084043c4e0080425042d180302d52590001703104a20030381b01c21084c907848400300081000b09131225070200255802e0f03048085440d810009880c1e106050117402c104001000a1454464980c099181d0348042646000e0100350b0041200540c2c880113241c05450055884503207a015504014002806150f40d10300b1114081044500030b105c0302c00110340700c80c0d103850300140c100c0040e1003948407441034038402550032090750a800c0480e0350100c81c86488602074541e018821000610950b01303840e902c80c0d401c001c2854042d141e002507803840c80000d440f1070000540c039142c8419411000c20540340c0505d007100075000d0003c6481c0c070403049030090002c41051002854620030b81d040380d900b0a0012a103c0c0410000c04590205544a82c0a995030399484000485e0340d041e044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838734064 1250 838732814 838732837
    0xe0d080d1d12040306090f0206190e0d020a05010804140d0306060306091a0904110d0b070815090a09050129120a150f0209152512030b0d0c09060608070302 68
    0x8200c04c0001404a42c000c4040900c0780c5402a0740030030980009820340c1040b10200140010100a1351403580c0c4101c041200c000300701d80462401000d0340104100d02d17000d02519040c444407a011405000c1100103900041141314103c0e07030310441484e40100500b140348101004a81401e002241041c420b0146400003500d44074201c60000c295801c002c80504081d1040c1c4100302041a03140e00e41c0c0f24030005500480c0590414540390410350f6004080c040d00800403e03550300034001c0031010b139032803411068004d4608a1701007081821810220b0040c0701440c4d00c0702d44107492042960004e07580c58404128030604503043d15902c0a8418055198581d840340202041c036a10300350805282aa4401d8040001d1854010b0401c1c40c0c1300080355908113003112072035030341e040821180c91082d1600c0749a11010003083c0c24275640c02203951100035140c4000c1c2c000741415118083d0b1180c54507543c041000c0182c00c40c4000c41e0b010350301c80b04d4400804550080170000b0f0390540000b180d090180c002c490b4000d104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838735314 1250 838734064 838734067
    0x1020f0f0606150d0c050729060111250306232404180204150e04020f01171003060501050406030f0308070509060d0614040513030e0d080d1d12 63
    0x140b80c2006010b2011060380401d00e00107012100520310342d8419140c0401e195210300c0e42d69500c1d41400c01c4c0f603959200d00000a21140036a0746002d07400032106a400c54070a0805040f06141e070300700d050400360452001d114520031510b00c1420403070310a8100c005c4a0090400700460517080700b50442c00703100921150304643c00d0700c0108081d541012502c04c1103082600250b500181c0100004042d10a852003903410300c858008401d05501d030901c00c0c2c00f03a8115284102071600c0c58982070310040940140082e1141c014000480956400b51361104600781101e10241030a143c100c02d0000d100c0214001620800c0c41c2100128082c1014420141500d4001d50b10b12001d84255400710340103a4002c0211081080500289026031540b1010b0320741411600b50201300c481c1000e0f20350f01c0a8542d003400707a1286050409010440851101c0d41c01103c0c1c2501e003500c031704c1131031001040a8071702e8213030000c244120001e81d4003900e4200d40e03c10105005440081343c3d040254041340369131400e112035020100c400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838736564 1250 838735314 838735321
    0x806130219052b09021305090a020114040b03131b0608010902031e0a060305100c0e19050d060209091b0301140a0305011d24130f0606080c01020f0f06 66
    0x6540078082030140c07402c01d01070800d00c80381100005a4030b070095400c0c6a464900190031403030024030b000002811b03c00200860302e0904010b658800c201d1303038080d040c445800400c48600079140202c1c1c0191000c507003d039030b60741002c101c08020386c1c6c0394800c20b42d4007079240f80c174041000d90b030281c51000725082ca030b584503990b03400c2903060b00c025800603021038040c02c10305070310003002442003503418492580b1807000034219185040850500303400340c10100f8001e1524004a4580f80c011065001c850b10a0314500d2401c4898801c80e80449032942006a000942000290400109400130400c0e1601a02d0700c0342c80703031a40f42d40c51021840945041c00b02503c18001440281092040d4a15030040203000d640f043d581c949401782110000b043c4d01400145800381c070b094809003005400d92245440f807260300c2c000d01c00c030b00120300c1e42d07009000046c09002d441d40c881e0910019050365910713180c002c2c4041098a40d0703071101c2661542c2c0020038a000d8010141c00c00a115030202d100c070740e0b1102100c0501050f64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838737814 1250 838736564 838736567
    0x31c020306041503030e03071e410a05010f0e06090103091703090106080325020a05040e06010806070509010c0209130f03112803030b0a0b0a0806130219 67
    0x100014256604983d03607428061410680c55068001540203032503215840d511003040c542084042d400001c2c3ca1040e00070540f100c1d4407410703c1d01c030403140c6292501c10107400051009605011140700602d00b090308103510032261030040c00e04031051104507950402c05a40b0001075841500440400300400c0682c0c0c5030410320b040c282c0090400c01d00c14900016110a6503494200100078860100200407000c4204111039600b489a42e001c1d1001800071418040c1540145840c0d03100c804c031840004104210080440d100c00405030082c180041003481800440c2c00b5143c0c2d10746003440b48081c40e1043c0808182414022070885210401c1030f940e5030101502c0e6000d10608110141c004035400c01c810390308030080391464034140d000354030a646690710458010040d9142003103108012044208207010240d6264000c110705030030550509000c2580f488000001c1d5521035150f00002c0d0758080020107208590380002c00c03034070608003200d082d4104890500000101c0c06150201565917982c11204501c19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838739064 1250 838737814 838737817
    0x10905031c0c110a030c140a05060414010b0a090c14030a020d060f0b0f03100b030f010f0510050732150f04020a06110307051009030f110c0f040209060a0906080108031c02 75
    0x6d0300442000b900402c540c00700e80d181081c8082c0950380d9411000502041054100394500fa82c200e10000381700070aa8180007070203080003885410104c40e0b407070680740c50044c06507240501c0c1303046480b28242c0b00d24040310607201a500588951501d2481d18001081803da011a090140c4440d041c10500b050703518281407000d944045d18050107040c40312800201305084500451185100c0402c4c0100d0303514041d40c1c1e0280b050642c04c141d104000d0940385c4413413250320000b501d00203508a511031042e80c0364140c5842c03811420000850f04852090441004d1103c00242c20140030f880003064102d41e079558100700030010055600035404036900c001040036520400340403854164581c00d59103032888560b0b8842ca001140c420f88840140c90380d00359001d05410009488100300c0c141040c0d82c0e1444407003505034968000c03012542c4104000c050150a6403901e03415075240100c054035040d81d680d94504050301c01c115a201d81000600300b400042643e41e008000e0b10400c10040d515002d110861040d0b10019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838740314 1250 838739064 838739087
    0xa030209060d0f1d06090c1c050a05060114060915090604090e010510060314010515120f1807120803180a1a06010c021809010905031c0c110a03 63
    0x260041c04010b02c6000360388100940314501e030b00300050b280348059220703d030101d1140e512180c4c0d07000381d010407111860118500d000403400b120521513030040c07018080030940c0d101c04090118490541110204000020034a042e16040ca000d03500c1c2d080c0d00d000304203103445800607482e00b2099684482000805e0107015050902c1c00400301c0f800c0a0701d9280701d6088548000780706810340e44413000e10120203407030f0988002034080ea290074403164514031030130490807a0620420f8090303d06209144c210701c001d00141c450b00004e10900c20f0040c18a542012488281510a24680c402c080300e0704000c0500011a5811151550401d40c06071364a0389520b1010f4000400320000c8010b261190b1803454814840160041d2180c0f0780002d6610802401001c0e4142c01850300307041c8058400010056a510711050304060000d102c5a000c40d03450500c3c007805440f040c0d50007403d500c404030704001c04074244d40781402c03021415402000f0151040b40100c1c1c0200460301074500369000310b00301c0e0000c00e200d94000c565 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838741564 1250 838740314 838740319
    0x110702120f0f0c04140f040b040204020c0a030203071403040602060109200a08091209130b0d051614220c020f070626010303080c0721080103060516050a030209 70
    0x12410754460020b060a01401d0003601d5a00b110515259a00c0c080c0f0548024140c14070140c1d00a203010021450070890103803002e072401000710001011903036035070111801080305c08180e91110f030302c918029540e034110540403511325512004066142c0c400009440444403180d0041800d640f0300071701580100340b100924166020b1b1070180350311000c000c00080118916560750a141031503d543d41c1411f1030b050090103844528200110b441503a03410310f1129041e80b33a840c00065180042000034030440b08003100030120b000740020003c1c1030041e0004401101c001501b0310000d01490300400c24081044e42030300c41c0072410302c000d1782d4004103650300003440301c00140122585244040319151a01c111036220304000f6030175580c1181c042c00028510440c010141040b0748032541107940103442c02c0c200801424190101107a01001c0c46100880c0700300c80c0a41c2c620740507509801d400d009110b808240002d40305a4117100c08107030201d964500030404440070366205030421f10a81012400395014124055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838742814 1250 838741564 838741573
    0x1e060402060a0201241701051b0c010605181006020a0c230d110307050d0c0e0c04170703141c0e1810030c0b0304050703021c12020115080111070212 65
    0x2002040318441c60f14130b0440e00203c2c5402646086d03913400c81c4100a0018103c264105404d1000a186800c0d600d01c12108644580c2d072194040080d090050002d41d00081e8000f000685d4520319008942c0602d0260f10707480c82e908520b5407102001e036940c02d20301c50002c041d03165031502040004007196503003103a03c1c94000c2c0490404500b000003060f20610744000d603860441d020308100d451400b0403400b0028182034481501407140c0d43c0324070082d203d01c1d110311641c0c4040b010000710824040421a0041c1c090304c0c0c0a200e0b2000c1080d012031347c138050717804100c591045140312500c01841c0010341441c48845165605140103810b13404540103030090030400c0d0446000000c0c40f5501e04010700540c45000140c5912415a285042213040000260301c8804044410400d01c004203c012680350241d9806561b003d01c05d86a02903801c5800101100107400428208503580302d0310b6044d0130001c0d5140701e4082c1644000e4903921214200d800d180c20018614404001d003100504010360310240c6498080c0585 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838744064 1250 838742814 838742831
    0x60e0411040207110306040c06030b0d080d02030a1e0b15190f050d0f090510200c0a02040204060203090406051906031e05041b360902060f07051e060402060a0201 71
    0x20301d016001c0c0d03802c8230340400c42142409507070707131501c01c4011054003202c20300314446494503200141c0c4a80e940a03803032079400100180e445092504600c007c40601002d13405080340486504008000440c8007e11400320907420004e0001c0d080300351004031001802610780260383e000700350b41c02154100340c06c0c140f10050200030f8511a442c031078540041030094000c580340d90347d440d080c0c0c1408034681c01000e0036071601261401c0004120207041074040c0e507500c1d540e5181035800d080c91524078400402903119000203404540983d001c006052001e01c2606c00307012603038551081105102c5400458209108126410040d00e482a080b03560030800545860b01e400c00d0f030407506c0d000e54804450030b542200003c41f10351019031500301044010860100503e20648900c01145c0f05204131340e125802d4600e4424000c0500420341d8401d011a039402000e0f5590351040d000762140c41d0304503140648403405901081440107032540c040200008600002c0c1010b50349a5082001c1c0b41c04c1140404215940d85034030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838745314 1250 838744064 838744069
    0x509010309171b1905061b0724050601110d1d04050703020702010215070c14150f240306011a0c0102030c0304420f060306020d060e041104020711 64
    0x4100700740c00300076281c41044041c05414504561003040101803005031110001281000c212150480044049810b00b0f60101141f041c650058403005040c88402c2e40c440c0350210000c945080035103000300c0c401d000541e41d503001560b0342600c3e01030045c1641c01000720581110b10401c11015400c445100300120100c50701c01040440ea42183da01021a0f0700240c80800d6680400107040a00460341440095240c6500000d1000343d8080c3c004191000207020300c6e9980201b400032000101517050340c40304071705d0503c2d060302c2054025186a50051111101f0000c1501c0d0f100b6100b00d805130140040030203904e49003100000e14941001498050000d100407215010f00380000c50040c07014400c195181c0c01d183c20810310f034601039020000304014260310700c110a040790840c404245010321102010701d86000f40000170702011348176413284e90724040380801000b049501070719a0701d00141c0104052511500030b5001440c00361400313406210300c03169105c040d00d001e400034041503110fa03880b5152103280002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838746564 1250 838745314 838745317
    0x30b040f0f09020f12070b1c0207061506020a08121e13030e0a030b06040506190e180c030718060308181e0d060203102403060b030403050901030917 65
    0x320300c48050301c40000000b03504d000080781035070a0080f98030741c40d90003951545942d1014a0700c1901c440c213801060315480803407124611031400303203030000541d41e840c41890100e00074440c400c0d01c99002550f00401080744e070f10001d9454145617011400503c2c0c0b010710240d84c07501d641c0003880c042c02e8008000c101408e0014030141280141688900100d044945240c003501c4c890310018901c0c0105d610404c00c10201d4058050702d90401c4080d6400140c03502c51030701044909100b003020f00c9146040403000101c4964448940b803084801328908102a0041641c007920b4103180410030741d16501050080c407541a0581d106188014180350000d213440e6079680300107440d0882210950304072079002200700e250810110741e9207500300519613034040c0b2600070001034040d40005000307014030394003100007021900469882c0c0f016004052200b00e660100000e0060003a119502e12000a8140080003d44850420982e0300460781500c881e820240002c004400030b1851700c0c41652003121a038000d10826480b80c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838747814 1250 838746564 838746581
    0x207050f130c051e090d11210307021e010c02091906141003061811090a080c01110a020102060c0309011b02011a1504090203062205060109060e090403030b040f 70
    0x22656a290500c142012150b06a0140a80c522100170407840b0295610608290b400941c0880c0b81c4070030010b04008140c4da040ba03400e40d0754502030740400c28070f40801d001000d4840c0070f1003258805040142d1512420004041c1160140426074521400c0300500d841c2840d00c2c1d200f0990300000d0010411552008180e4001e079100c442003100d02900450030741001145110f404903541814820141f4042d400383c074440041241442855413459007100344907840b4103d070000342000703000070611902c070040385440c0d1118100850105090700209068440c012600c00304003601600076029507a614106030307042c0c4d8401840b10405542e2480302742e002700614424076442020310b42c00000c3e1003009507541c6d04034102488445219090030002d13001c403880490f0865007a0781c0120401f5031a511008042803c0c0004400c3c0c69072082c24440b02c0c0140e005142d44904d00c181800d80e12000000d03038407042520403d400401c0d150300221500009070119000390040ac0d00728102400000f21622101a50021030b244031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838749064 1250 838747814 838747817
    0xd110a1214040f0608010509070e01030e071805150d0b13030c0203010e0c0111150a0b040e0d0e03060a0b0904030c0318030c03060c0302090a1a0d090615090209010207050f130c 77
    0x6200c103201d001d50005c0a02d0161134191980d011509141d04041e29054845c00c1d0541016103604100d9542ea2091090000422550a0341c0c0d88a8442c140004054841115048230039007490341455103d10b486e03041c6880b4141c01c100d0100381c0f42c5481482d480c50700b41c031090070f07000d1101007000d08005071000d104100c641304101c0b01601416203078200041890200002c0854643e02039140503540703c041c1c80090b03030400030080c0b00241e00503d04000c00e01030301c010148000540140c103290740a030b6400c15044055040101d0a4580740e9542140002c07c85031002107003604800d00701c000a00007406440314058540c001e060100d1600702e49440d6400ba10301a8004842001c4010801c10411400d406125499841c9060940c01c3c85d03150300c0496851690f03889170441c56201c001000204020b200300702c96076040e2210060220b0502820620040d0040c440b205a020b4011240010005124800c1d180c1400050340900003140c5403404015404e04000089680980e80001400c9903444603c03590440200d83d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838750314 1250 838749064 838749089
    0x100e0403030b0f010206070e060d140f0412050f070b130204020a0201020a0305150306130c05060301120510150909150e0a0201020d0504050102060a0c120903020f0d110a121404 77
    0xd1001e00c48034402c9600200d065500040501107c140c2100307800ba034082042d00c62035110010800c0c0003005d864040d02c5103060507220414000b40c11045960307548a18050ba040070426255404e04903214440c3d14400d540b83c1c00309200c04070015000283c110b400400194000c02c15030b01b00e8001504031ba1001d901c00c00581e40c0040c03143d07403850305401110762140001f40c00b061030b6040700d40480e40307800b0001c144858801d84000e91004021001c280e05000c0c08000e00f0980d140d40e1660000d401f044541300013911980f00c0d40c94680c0400d0240d000d00d010416008094085091800c0d070418040c10041008a0b00c080c2e001c524140e8400c180c3c810820240c7c0204010f181104a5000190a0007000c182141c1040000c100030b20459800103143e9410003000074000a1241070504102c42101c080c160509426081103032113420b050703000400961000d00c0384180c40c10729051003410341c4d020700042c18410f2039030482c003e02c10102c3d03041346804220784541d04041e400508c1c0042c11070015030058000e80c40c031050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838751564 1250 838750314 838750331
    0x50d03020417060603030f1b0d020a03090b0c0a1e05030d05060906061801201c0f03020408071703130f08010c080c09042c010609050a0c090e100e040303 67
    0x666041442d59244050050308203070510f100030980b00d1090500c001d40035400012007031700800400d07800424414034901501c140580c900c00003911568030f080309800180d0b43c2c00d000f06407110600110b80d10301343c0d0f10340100b891100ea0383d55022001280c0b914400000d41240090700810014401003940a644c40c5c8001101d152060410444071405000b06001e103000f40403110b42d10078080f0040c0c0c0d00360802d08002400e100004540d0003c010303402659035007401034808801c031300115100843d6524006484001c3c00d90f5200b08120100c1c02140710310340701c0d0351009604100401407100f008040c0b045401c01d030303441c107014880d0207550320f002a442480c940380c01810422241c01d0a01c1448100105413500a81a00f440400c0820f03900604039001d1203103a54a8035017034000003030b41050b0b0b0018074000d480e01c0550301c0c080086000b46124442c641250307050000140d02d4a50a116000d0760b21050b84038800d0701400c01c1060040c00000030040100c013032150501080c0d080113200c2191082d44aa40c01007000031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838752814 1250 838751564 838751579
    0x40f0e1b0301030305030a021305041407030509060c0a0c08040503060c040806010e04032f060703060302040617030301061407241a060301120219060206040c1e0608070c050d030204 79
    0x2218803031401a1480510040c00000c5c2d104049075081034050501507142d01500003003070326400c41607202c40e500c10b2502e00c0101d140c45550421520034125600e0030812a03031800d40450f142d0b5002c407024501d8000802100c0202401400c6040001b4040e01c0c01c94101616500800e01c0d00c6001d48410076036400100f41005800c100700411405824414025500d0341415900641000040380e035148416131644030f501044100080e043c2d03107070102c80e4121002e5050045003d0b008000c3e0340006d0303004034148100885c200c40624130115165040500441c42d50b0300c1c10030102d400344020701e00d0100e02c50040000c0804514054240400740030504206100c1445800e000411030365024400040c078514402a1303400c035a20fa500b608d046804441d82000200c2c003d2000500015000001b1300c002420740b1808a2282d50000d03a05100c1c0388251004414561552200a030811103004c8010341ca1900700401e200c62440703200e030aa0003840c10300704900c00c3d14a030b545007424086002d0010300041d038042803c20140f07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838754064 1250 838752814 838752841
    0x1090f02182a19170a29130f020c0c151812030406020115141e0102010b121c0c050703240509100606090806060d030e060403030924020d0f05040f0e 65
    0x119144104108040c002d40c1d078049011072a2503101000b18903046c0300300c41134455a1101140000006040005501040e0590020b4118200f0303100c4611403880104c00a082007804128500716024a00f0700301200140040c031444254640e0300c0c0c00c080003070313400422800208090400307442d898001040c5113820310396503031180504c1d0b8840c500c1d0080b44044100e0036110b0b0700c2d04001040f551107050111102e0900180d000d496404205034104000c200f541c01400ea01007644218080c80c10029020803584550480d0f00c4841c2c014090041c0e00004020000640cca90b228482c01e000704c441101340400c1000d08008941003152013407000d8104002c4104840c8288c40349401418140c140b0003921030910050075920384004049034090528001d1050902d4024048494243d00003040c850741c0c0c036241d1400401541251107140d05031006800e16400120307407412804103500ca194010710070101440021207400c9442211842403090800c008101004105456005845181c1016005090915904152 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838755314 1250 838754064 838754071
    0x417010b01030b090f04031107121e0305190201141603050106020616050313081308060109060509221202010e060906102601090f02182a1917 62
    0x1094542007071241259564000c0d5034208a020310300217280d664600e0250703404004407468a0300f5114034400003e000d8600301c0c02814043c41928101c0c0e5540c00350140600c24481d84038024040303401800140c2c60840c003032200c00320742c481c90720022a485081c1c0703009001d01d24041c2ca00c0d05010b940d5624109000ba054014240100b0042c4007d050514002143d00300d2800155658010041c000008c6000d009408800918880d04002440da0301c0303031007120201c0d81382c19500c1480050301409000003064000c610482d0220380300541035010540e2000f015100e90724402c4100100e2841200d51480811082ea60440f010203a54000081c0040c80302d004c9c503c0d1840040900b90b0642c440010484012100508001100e008c450507000100000c803211a4420301000c5039040d40d803070082c5e01c8080c032080c0c0d140104000e000340c450b0003043e0020a0210300b1101d086034030302080e0080a244603180005d4a51a24041492513001c0c0d041c403415024803031100115125550010702400c4e6810644e1321150b0303130640c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838756564 1250 838755314 838755317
    0x80d0b0f100f0c050106150810081f050622021308060603030702040b121609050105041a100c05010f0f051e06060702211c050418050604110417010b01 66
    0x121181c00301c020504808074280408001e1101c03160410440c2c25003080c0058000380d0b40c404070b0b101103c0705c0140040001c0b00c418036070f41f20b10b48002589180c0401c102940d2100400038460090081540001410f4003400341908018032002c0384581c0c101145040c106850b0465001d692100f561034540c000500e543c1001c0b4030780d0003480074001c0c41d5a00004864449a059402180d0b00c0000c0b80003804095441782030782c15a00561110440300c207040703621503054500c600420000c598980041c48100d500a0110342100b06110030344034410f10700f44980381040d140e1450301c07941c82400d5a4403a425142c0c0c0c280c04e010484d854803400503004050340240350380020410003000b00e140d4140010581144007409090240e4400a00381d825502e5294810300a0203640f20140110844010020364030703501152030103070f54008038120400300741c8640d048a048503040d009034405001016465801404090001307607101d95075200c04543c0041800c0500300900000c484440c1030300c5200071039825200000820350 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838757814 1250 838756564 838756579
    0xd0f0b07090f18060b070503090301060f06050703030b03100f050411011b030809100203090a02130203270c0a0b0d0e012d0603051c0224040807080403080d0b0f 70
    0x2041e6420008030304121500842c40f42014051000f00303e00508044c1c2150455100010720b000501a001005000c1d804054000304403140e502c04156103c022140075202c0080c404000f004003003840f94012591000d001015210404040d120310421100e24810b41000d2075100c40400052200601480c0d400100a00701080203894600b4441060409048021f043c03180314404120020010000a80b0413040000115601d00b01000f50681d12140c8030801c0f48500e007041c40c3c442413140c413030003980c1c081d80902088170032101040e00aa1030f844a145510072882c810b081252100740d0f100028a0002c04102d01059034484d6901c005a040d03c000580c0c20782568100492260040d4600d0101003d042c0c0c10f0f00c84500c1108107010500250801e648064103e120740e60440540a05014a42e068182281c00710b80741044c2c4600c031065010f00030502c081c24212200002008200180b0041c48060302c9494440d00e020f8032541c1e031031019040101e14030782d065035480c0c0c0080703d82011402403007100e0007150b140d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838759064 1250 838757814 838757819
    0x1a0901082a15031f030c0e0604151a130b0408390414090606010e0306015a051e061c0614030c0108070c02011d0d0f0b0709 54
    0x240b0704a008014084410070000020b05202444d661030012001c034200614000d590701c0c2085200e041c0f550049294a01c60b40c0003182091815101d4050303510140c0044644191400083c03007546600041034000d035450030004903520101001c400005045502400350300c49060808491504040240c0c040343d1017008050400d1011b90603810900100024206101045600002c08d02414600d45454644041e030b502f0b00804130004154688105004c0e070383c03001d40d00091010590384007028405c4460010a000070039294103800d09001320b00c650559100d81d240c4003200320b00c1182c8030716491000002040e1000c0d5030005640ca9511358001e040884405a0201200c40c1120551600c0c00c4114420800010b20028000f03c440c002c0ca2801115441040100c0d954a0320742001ca9030f10b4001c500c01d02a038061030301d166004040d100c1c01400c560380d0b0070b8291040d540c010f407040c9005c014001d0007803d5429403608590745916048181c42c0c03041461500e16056460103030084200613004e10103210050005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838760314 1250 838759064 838759069
    0x908070506010626060f0d0c03030f090e0a020a26100614030708090f07180605061c020723030c06090d02030904090f06050c130602010207151a0901082a 67
    0x70800d42d0321444c0c01c410400c2d11001d0004541403116402190000520328290050142200c10f00d4100e0740240c903482c0420140890854200c1d019001c0c2040e41c1c0111008644c0a540c194080c195240a6081142c004805a8401403c2000413000400100c011000b0403001405001c1440000d102c00c2c1400502c1d03202c2d80a210b14103002c020041d900300022000000c400545c2004040c00751900038003503510032504c400000c01c5603440e41c0746806000e4141710001401d41061130840c0c01c02110016080c04c1040b1100050010303620101058400850741060051903440c90501e400c00341c4102002942d40300800c81155040c940f0080100080c0d03044580380c1e041c856000305c1140c1ca0304004450000c0c50f1a41e501d445240340001c0784000e00443d10782000c020644035407800402c0b8050685180a002d595210300c12401c2c0c3c81032080041c000245d074055000d00c151942c2044c40320416030328960039610320200103d1040d00c000d1340304007220380c80f0040069082200a017040c1a00d441101011245800c800c007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838761564 1250 838760314 838760357
    0xb0405100212070804030e09100503190c0614070b070c0b1e22050d0e4f050712150302310501060f140310030809031009080705060106 59
    0x21081407203d1000040d04140c8615202d41f940100180008224105502200401a00c500909019100d414a82030141090b12000340149030300140001620341043c02c1129103150b0010040e0310f0440a0100b0342c0020f030310406140c03040e030480d5905c41c2281e5940c10086103102000d010b0904450072410209903144e030003108554811190082842100070348030444040d003898030000f0704030380546241d48444135481011030345184004c88044150668480c80340803030442080e0708a02502e040c00b117543c0c0310040d000c805002c0301e81c5a44c0214409911910900079100d003259030000252001c2c024141a034a98850b040510710391114400d103040c02e41d4089003881d01007003643c50316404900f48a0100e5050507503108002d010b020810302203941e5a02015240d81c240c050050082000240300b10181c00040e02682e216080d101403c80c01a4595180c3e585141e12080c4441d4050150340265403c2010b14003407084e00c103100b00130703042da2480c0074203110b8145401a0048410054046203880c803072000c1c2c11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838762814 1250 838761564 838761571
    0xb0306030d031a0402031501020d2c0f060706150911031305240417190e0f0607031e02031c0b0315040506150f01050a0e040204050d0b0405100212 64
    0x40c00a25504030358616001e00d0518043c4650040c000000c010248043c034244050403c82a02107910650146206440039207480d013042c26103403410720704940002c00560480c02e40c403401402c1b80c0512504e0002003446903000c1103003514500e46030324503003d10b45020b5500400410402e2420040b41110b0503802120748006070041c0f6050604026107018082d050205038241e03c814902c803000594a170111048290044509a582c0c2e1500c021142c4418424400caa008580383e4a0000c0d02c0900f0400540e440c034a02c0103c2c0350003a41424000500303888100040000e14002e85031056076990110754000a9084815010115002031003030b200c00d500c02c0e295081d044044140d004c180c1003076003008249030010100c900010780c651742c002c2c001840f90200e21180a0030920502c1044018008284040c1c0403001801030b0004a04000c088205482155034000ca5500203002500c0e09503541e00180e5002820704c130550b00c80080d403090100700312040110300482070034010151b00b0308601440020111070002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838764064 1250 838762814 838762817
    0x2061b0c120d0f1803180e0f04060905063c06010809030d05040f0201022109041e0203010b1c0c0e0f0105120a020310080708030409152106060b0306030d 67
    0x30074014186102ca810503003c400240340300300000882642d60640034040c4035000c0c1c02183e550124164401c19010361a402d88440f03c80f4a0107a4854400c40500414010815518140c2c0c407011600000e4050141030b000d06e0781c0c91903c800074a00300116103a8146680003071141c180715403800f0b201d038555201c0f5195004500b400c0004403903480912207815841002d4901ca00d0714a0001004208144003015a0400f4004e900b201c214a0480f40c1182e6441100300310481248420301801e682d41c44d040d001069509a0a100348000300300900603042685c02c20b800480203e000403500002c04400000005216008680c0900a043c80c1d0000680140780100420340141591490706001e640a02d04550120b00301c4032072080c01e46818000d9000070b4006884604125803075403000611260300040701410380b140640594506880e00038503000030a1001c41031540d40c20302e02c4000500c88640c8107140c61511070044003003003002640c07400c6412200c0c681c0001842c0c0e8402c0c000c1c04440d860000c0c11030902040d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838765314 1250 838764064 838764067
    0x100909170702060c01060f031403130b0c100e0d080921090406030b0406060f08070e1f030503070b0f060904080a0e03010b120106031716030305040305160302061b0c12 73
    0x118008210f55200700381c01c100c0c035582008000075103984400303100c0c800c49000301e590b807a052203d0900350f9107130702c60605485c4013079452000600080304106c0c021701c0c00c00c00baa0200e44400d0340d03401303800d0181d036090000c01445400410380c12226540009503030360701c04000b80150001a80320b19400e06100c01ca4101a1b8080c000404e6908958446600c075401039900208602d1462405103415405007415014010b01c948482c034001a9100300041c2d1300301581c040e030b4101d150580d00c4858450803080d030000b41140080c89004008042a002d00050100303d000d00d260208910f4110043c20048402501181c02801940100004a41c00c00203548411800746451032104402d54002800342c480880399a90290920b100d00c2c00704481503000000301c910504806200c84002c580c2c02c4664000c030102ca10402c0c0305041140e001900c40e074401d590191190400908002c1010a5103116a15a039822400b590000b01488041c4881c1c2c2e0040c00c01c51f400400003840c00384044981e03902d940711203c000402400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838766564 1250 838765314 838765327
    0x22401051809210712030626100504030c0b071806080a06080d1d0301091a07020f0d0809250b13051302072a050d020409150510090917 59
    0x10520600200501c1c0702c9292200035110f1a803001580c0c84424100c2d02c0e5011800340e4202d26009010300000c85040c8100f5130b01c50512030480c4804040011700f0411540104203034000e95100508c5564000c1d80203135103507003e10300507150084c0304a070064401c2c01408643da03030203030680700054221003d80700d2034a45040152900340c428405020703150001d1015000b614146000035038411751020085080c5840460381c41c0004051508840da4210301030301c001000b030b400d05e4200c1c6c206070345150407000798411980f407051414416802c0088002c000703030000b0440c0342400300341c0004028081c0c4031180d16281407058100584002005606485030100c02c0c03201082210004c01100079881c0240805481242c854501c000c40c50000d5001c0c1804550800410151800b03401c18500e4407004481e150000351001410b002c1088400394054404991117038440c1d51140008011802000050070344400c04160b07406c02e06203210500c500c0c7c0e0015103204d8507003542c4801045280e462841003120b50024181c0d6482d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838767814 1250 838766564 838766581
    0xb090a0b1309180c0611070e0f040f030908010c05270d0605060f12240712050a0b04090f021509130905030702060403110a1202060304021003020d0c0224010518 70
    0x8540420160544c41c8540d80000d00540151007a481107030342d2010790f42000e840700500308c6070b01d00950b61140c240b000d440014002841d00f22820706081d00030308204941554840103c0e00355407920080c078001680101d00c0782c5600249041c1400c0c00c4080e003080c1c04a212030140410a04904074030701504458458004c00c1e0340d9114074501c2c0040c141e02070443c03420043d40803c002c0d60350b010700010901d041c0c0c1c107000106140d81c6000c0d5242c00be166a9030342e0004c06d0112850140030780b10240c00d01c2c5860740c2e40c860201c01d50703845103c0c0158580c4528040086000280108582120002d200d040c0721802003004c1300130f9555840728414140800c1c4000103204c041b600b8114954083e5140081d0010300020f4080f00b80003010410718000f05085417080385998948030070b400c82c0003000e0002904003009102040c01441e29844280110f6000d10303005040c80200116402942c01081130800507801568040b061044001255103420f202031030071403010751400700807450702c5180c14007001c1442050300100741003c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838769064 1250 838767814 838767851
    0x1403040b041104290909150109020d111b0f12040b030c0c12040e060d08030a02091f050717070206030121060606030e060702060c0315030c030303010b090a0b1309 71
    0xa000a031011380c1040e05030645400424034503283c1c54881d840000001d04c61510000c3c100f03040a40c01ca01e0100c89900c1c0000d0745029411569801648a80710240c2c42c10311041d210240c5001d45050b20122858400d0038131250400c2028100e01d45160001c004600301d04c0001c0044070104c0c0c028181840d0340e540c8509241505020340c8810740d805005280342e03500001c0c0700c0340280040d00c04c104404651500c50038104540e890400c84020f007a95820301c0020007200d0030303a024040c900000340415040c494240d104d2104050f001d0302c01004150f0105d040001d1003030180c212800c2c40c294680c0d60b40361250940000390b86010511a902544800c400144594541c00b40000a510340c00380c1d06100041c0c960f5405005400d84800525240c81541c0c0001c0d0601d100044a0b4001c0c1c06402c101c91070750701c5940d16244054000381840c0c2d0588a07540c00c1e0001600c00304002d43c000c00443d00c03500d0300c5070800000c0000d0108140d00c4085022801e01c142400f4280f4042c01200f280c0d00030741c0000d00c0002200805180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838770314 1250 838769064 838769081
    0x18090609060e01060e100e032407030e0705060d18080313030e030303060d060b0315010306051008030c280f030f0e06040f030f03050f0301060e011403040b041104 71
    0x9041050000c0d466640e500200700741c49010422100b1680c98607401c890000c45003240681c00b80314190424100360161003071804021025040da9001d611145541d0a0181403400020807e0098000c0000c4240d140c402c5a5440c5925400361032a80d2900000800601170a11001d030781c166591703c0f8120000d80c0554070781d04694840101526031400a25888441000c0b140540c045034a06201c94602d141c0801241d1084074018030701c405c240c8503034680d100100301c40c035403042d010311030156121500c0900d80001802944540004a11490724100c003880d1003c1d541e10006160340b06201e00d0034400c0022030043c080781d07044092030b41004c40c25140e01100b2000900d01514051038010942c0506a010f00001c0841c00152140040c02803000e061000e184200d01c54420200c2884406100282d00d240c082041c680c004d103000c900300503100e110240103601c00c0c0c0c00440401d400d450004041d50b006407507800842e0080300c000c0d085162644070740103620390091009152200103a1b02408940c0c1d90750203c00e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838771564 1250 838770314 838770329
    0x504151716060914060a122d0e0d020a05030403110f0406030602070318080a0f2120010510090c120c02030a03060e09030702120a021503010501030e010c090618 70
    0x1150782d002e002d0561a441c3c01000c0c0f0600b00380449100e10300304282210240e013407030703600c496000800000710f8005002c0840441022000340020038401c0b030088140c1e100c2680c1c42c5000098280c441000d0a00d07202110a910b0155000350301004003103640802130700c0c110b98200001003c011900303000540700e400290280c580c0b0525007a0081709009103a40603203000c42c0710f9140c03032400014454007841c1001d5244034008031580200b08010000e21001d000e05100d61050050354155040710a0700802158402c4042001464071511151400c0313002c0d0748102c01040d880020032583c10b0031707200d0740c564445500403074a0303c0303407207510981c5207520401150140c1155581c0411101c000424020344a503c0f80c00680e001904018011030300036170900146000d500c0340307002180341619503424800207110b503808424036401071030a041c015803100f41d0000d41174035101f16110341d80d40c140740000d81258a02d164030202d580c03400c0390540056400a030706000781c0307850303040c2441001c0b00d20a8086210003a80c202c0d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838772814 1250 838771564 838771603
    0x1c050c06041508090703021e03160306020c0613031209110301060306060501090603022515090b0402041b0c0209090a14070501020f0d020d03021b010905060405060105041517 76
    0x45098580b189210440090b603030ba40090340b100300c207080da14032041c00003075030210410f9001e422202c241d68651141f448080c1c2500d540d8607050340e12441c060102e620554685400064119000100707100742c5a0107000980c0c004006074aa807030052031001c48800b44d01c1d070280c0d00c2c80e605c400c4c4900b01020100010005000b80009900e9251601c090b12081c484d50740402c04400300421458060300944414030912510b9100e24481101104e0790503254590650703490700c8241c00040c03014007c2c000c00c10440e01400c0081d45a040c00c1c410f000880721015401003a012500d01020542d60344200108019601120107130070513280c010605082040815004000b92061030201020362404038401d400c64509800b0369042e45c00c18441b003074072100c200d8008030041c0c12144411590f60302943c042c24990004241c0e604099014504c4d150031644004802d0307500e40e0141003048100b00c010020709024102c10b507414420030035240b10b03055404030320b03008074406210344d00e180000500003044805420300300310801070b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838774064 1250 838772814 838772819
    0x2040b0304061a010c2103060834050306060906040e03071110030e0d0507030311160b060a060212390609031c09020109030203030d1a0307051c050c0604 67
    0xc0010020020824064581d0190000743c560154100c0c0000c1c1d500701004044070b02c81031180c0f680c0340a01c400c80800341a6220400b05a010b0100117041d80d4003d0b094100c0d200d00e03280c804145006071281ca485c2c000b4101120141b03c1924049043c80d04000152606543c948807500010003400041d00300002e00d200100d400c00a104ca12001c454002005a403030362446614400100c0544045508a4406512007151041c585101e14010f04440b80030385000600c100f4038001031040d981c0044810881d022044500c202400350400c00603030054001c030380b03040c01c00f49011006519141140000d110031400407030b1526040304105110072040f03e07100005010b48042d4200700082550003007402807680b04030300020303403d11000000c80d80b074403080c888182e45e0103e001d82c5034006802c0f5000120f041250807000040103840402c0540382d80044084045405604809540c007035034032150710503109511074281000303240c4900710302d120a280d44441004d024052410481d1078918080341040d007003540010300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838775314 1250 838774064 838774073
    0x1b040b1311090a0e0f010314030d020301030605011e080606060f090306010f0608130c0e090109170a0e030703020f270106050d0b01180b0d0e0a111518040f02040b0304 73
    0xc26202e90b080390700c00181034032202c1d6490b210320b045403608962040c14005001143da200741406040c088002202e00e04284424898282e0300281c0c41211110340300e00040c0074502020314521642c65034183c2c1d410080b850b0444469407804003500310782c010b210000d00c0c14000c100110443d000e4041c050120388455940d0019001411401c1c403400d0006034a50700400c0d00b400c2c80b00045010260403040c0105220b007410109080e5003400f80541e40190341c0d881407500000c44d003103c00c001030064025a152503c5c8038070000342c03008990050652080d00002d109000680c1c95201c84a1600001e40e41d5049241920075202d03400100c88005c061150201000040d5056006008281d50781c200e03031084c00000b159400560386141040c054070b030200d007500f81c1481044044000b404680785442000b0034070180d9640c2032400c1110818054903c101150070721001810000940355081002e403450304d1520200c5130084c180700030110035040c07040d5203030481038155401e00d030140e902401c0c1007405255a4141841c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838776564 1250 838775314 838775317
    0x218220b1005120c10030b0d0c0317070b1302010c0b0406090317010506090904060204050d050c090c040609060f170f0402030c100e0607020307120b181b040b1311 71
    0x12104403111407500c000c103103030400c14050a0054404001401c5815184041000c10a20702c0c0c3d8034000c06035100c0c0740c040c103503882d01c00000207513000784d0010300305c0c07030650400011000a148500000e040c00b0000000001e04e02c10107283d225103204030140050040d80300407900031f00c40d00301c0540b45d001400244824005d442e0b106201e854866100d010804284070f501d00d54040c800d22038150702200a110030089420281109039005106020045c03600f0346810000329078802c690310944181e031019441050320f08007001da0711b8000d80160340040c1014070b400340013002040350f03000e20300421403003060301c0c1d1a8034058441042400303010b1010060619052406d8000c0d01c6080300c081e031182c4180000640a4105442c00c5000583d8503512200d152840b0b8040c03100036408402e0032605441074040009a0560f41071622810503c42e142400940c244a01040034429111031080b025400c0b9490007104000b40f0b110040c0145e500b5580465103080304000221001030004034003243e01d06049001050212140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838777814 1250 838776564 838776571
    0x7121703091605031c050702040f0216030e12120c010f051303120506090a0902030f0105041202060a0b0a032a0803040512060118050c190e0a0605070218220b 69
    0x6410402e850f036507001c260391103c04038116000305c2041021000d0700c601c61001000460300203000070034008800b810f000200d074002500050641c40c2c2203084001c05038031003000c11204c40119071910503910b0740c8004513103410100d904280130100014100390810b0342074008052044100b0300402c00d520b041442d900038454070700d40c00c6000a40c00c4503881d80101440c0306980c041c11001d040230640d5980d0394042002030060702d1051340d0510480751a406c40150034025284034600c40c1680d1021a2820f000283c60b08000ad464540308a007018198440c0c1e071101c004850032260400014000e1303c5041203000005c035412640200306440001d004039940c80c0c000000c20031540c0550300c03080820020503072940c407007000303005000c0c2402150304030305a10200e03500403542001d14480168a4584000c6800140104120403080400c0000309001014502401e04000906c3c0e641821445c041140e400104180d40910107000c41c1e000300004100f044a44000d61000c80020030a041903464441c20009520f100c03c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838779064 1250 838777814 838777843
    0xa0305190216030e060a080f0c040314070e01050d0b070507030c021905130b060f09190e10060306120209070e1305150102010e100c0309020607060e010e03030601020712170309 77
    0x40c1c9130040c5800d15100302c40509645070340e049550f49034007078680400d07840500b8440009009100c0800410303c00a0400d0092484034002e1541a00d0b00c10340228149050780000d224910303400894000c0350501903141e9002c1940d241075652080c151400f0b8950107140400650442407a40070714a0788030703d004280f01600c000b207424408008070549600241e5034594078054002c0d0040c84440c04100449000d851070f8103005121071001d0708030071b010410201c0103034031400d00c1c4806201401850006414144060a0145401e1181a0408082c41c95244200400900902030300700001d41d1142f28aa010205200060048462040340b080801c05000300340e0700000d800c01c5492220a55600510074460a1940f07607001e0f12078003035003111000040c614050110185504c0b18000340c010f80d00c860040401c1d5100308800180c030031018031300c182110075070000659580d10400c2072101503a0009a41d1003111140207146141d8203481c502000c10710b0b8010307490b1010039004004d100e143c0c840401d50003403ea190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838780314 1250 838779064 838779077
    0xc03010b040c090513061d010614030c09010518060c01020705011503050d050a3005131104020702030f1501031e0b04032d0905030114010b0a030519021603 68
    0x210040100b00d54082c2040c0300451142081007042c0e04198035601c10740d4020134000502c031641d400001c001c5071410308116001c4d203400001400041e40090f80c5030200340001d01550700b1480d0640e07211259102c3e1284040c140140403034074000070358010010300a42071024050584650b20050b00034082c0d000100122495401c002c2205444460410321000f00c0350080d0040ca00d03440c121006840c60350003446003008001180c94800030060400d1455180c544003220007048207103000c292142114000390102c02854a695041c90100b0b80b035007140620501d0032a0012b940d0032081c40024034000d882c0d441d16203130340106002250281900421039049a004401101304210b600c91410741e03c6007444801404401c614020601092080c201d0340c480c0c0f200442c001425003d10601d0711102207412002c4800a0483c00701800702d41403e009520695008445030100c55040114100440c000c0e80040404c169a0700000340c4944800e505c464000048076108643d1075241542035035071803252113002e8010510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838781564 1250 838780314 838780331
    0xf0105070e03160608100905100302100f212405090702031e09151b010b0103270f0b0a0b040c080c03040f03230924040b09210c0301 58
    0x100412018824a083c03a0a81c4015040800a4507001d4010300f604050b812040008104d0321441c0c42a0f9000d4015110115402c43c60342c4100600301049055000400ca0030070490010180c01c00c503288286200041807034100c0b45041606001490230403c1c100c0000d413070642d0001406042d99554040e50380c113494949999541803010303a5207115015580a80a20310486401e890003482d01500e001c400c02850094a01940d40c0409441e03005148141001c0318881e412200d012000d20660f08842428281403001c404000c03500144009980c27100504401e1031400c6804000e03040d0785802400c0d07400f80201300355052024440f001020b000c404d0384d0007140741009602010f03001d6803405121b018032503e002d2075943ca40c4e5a581807c6902c0030120180041c840c6485900c10714849410090b1810326505525031416004100c0005d8110031103804801d141c625000e20031149108690903200c40c580419503941306c0d0340110318151603140b40407004410740b407041600c0d0b030b201090981041030101c0c024440004c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838782814 1250 838781564 838781569
    0x1e0319081b120403180e090606030d0905010e01180b1605071a160c0e09030726040e1302180105510a02150c0a02070b09120f0105070e 59
    0x10482d141010414038030030019000a1240e44a0025012019400081301e9500c440212408000391180c040c0741e0024001c00c0740b9804d040060f00c2c5201014a0001e10451800002a14251400090f14100b000c460f080040b503000da0700440d4000c040c0d1042c8999100e51802c0c5010301c880c40000122002e0280290024480c450500d100c5103150b0048003a47c540000340000310a180c007502d0040f65900110300c4009048528a81703100d02c0381c0d0036100515510310451402c07403c130310000b0760103404c040040130700d8400c03410040d400d607810f0b00c6942241d02e650792142c0388501146810b0300c2d802503010a00410611140c81c0044500d4100d075001d850048004103880c0e02c040258440b101e41d05132a01d10311542c120154860780c000302202a010541d4550001c44440d004426030000d20b0200150303000c041140c090205501c4040d52100151a00c0760600d551200000d445145c1440380c1c41282401041c004410380d101c00d00c01090f252140221185110307104038550107480c08468060103e03440e00641607150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838784064 1250 838782814 838782817
    0xb0709080d050406080c0904141f0803190e0d120c0309080a0f06051e09012703080f0411041b1b020112090813091a040e1e0319081b 58
    0x180c4640d29045c0d42070b03868444042c3d20745c00c83c54455078003948410920702c501700d00006140c000c444941c170100b45400c0c2040d08451980300c0d903100039000d6008100b01d14114100c0345c006608200e4519080754418503803400644844085480a4803c0085482c1351032025045140d03040ba062094480304005690307000c0380354640841307440c003034800e040b48082c039000100b00354000d984c0201903040d81da40903a1001e454404036401101c01c42d041c2d80d55002502c44c2c107020311210322102a0004114030003141319070b50080020030050101c43c0d9012030103010504021028580c1d82c40d50802400420120b00c4a003ca015021400880d00c008912481d10611407a60301640d849034154040c0c640b03201041c94400386074000c0042903400e84540c071041c007130100007050013102d00c4001d05070340401050070141014080500600e0701e44540c0300b01c1c50098808400c00c00420030102714a50902044400c1074804911400c510034200c04086c002102d0070b14492051701b00050502400f088070510210701410f42006102c1e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838785314 1250 838784064 838784069
    0xa03021207090b1c061a0c01060905040206121005060f090109060207060c0b060d17030109060603020702090106200706021b09070503191803051b0c060306010f0c0b0709080d0504 78
    0x1808080069004c0040d2058540000301a402d80010b8400d94603d880091515802858070340c2c000000307910030f90b5440074080e040107070645d50000c01082c00c080c1d0020740c01d8070441c50014003980c5140c00007094000c201c00060024000a000150342c2c141d8600421055401a1000750201e0a00c0c040450514400075521090f02c00a40b290525006a82c80301040c4a4009005c241c3c07104001e007083e000030b0700940500c0380c40c0506a801980301d504190350401030355070780d401c8102014410310000015942e950340840c112521410b1504141019401d400076407042d03000e864501d48101d541c0000c807507078002a454488501600b200524010400411181c8407050320b81d070b400148240040f58080c84403031070401808604180c0003803604582d100c042007861414000341d0200d140403c480c20b190f2030400f84403400c1c00700380d8060118007411100007180e0780000303010141003044280015107818040c040202103580c01031081403441ca00101d00070302c8004c150140c40481e000340359444c500c3c5406841994207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838786564 1250 838785314 838785329
    0x9170604050309010c020f1825020309060904150b0d0e032d130801050f090a051506010309050a0b041217010b090a1e2c061201090203030a0302120709 66
    0x68003e0036001140e41c02c0340c419050760b0240740d80314428065541c012a286903202461040b0002c0d1030100040a82000c020705030034040782691100141e096808401c40d500c0c03103801c50318251076440082c0810011311010001d2514051204008291840383ca000b82040341c426030000d00c44000e444034030319180e00840c10f02e814030410440748038803940d02c0009450b040c012a00c1c0801d0424495220007114003150354054030841c0d545000307002c0b6040841011300ea1102d40e0b00000c0885600c2907036031555903040d280c4001000c02100001c80d80301c1c3c0c804c0d089901c07516001001c441014a6600b00301c0e9103404251000c81e1807202c112300e00121507014a1000b4954800205682d003160720f402c0e4242103da2041c01c150f6800091291701041c2d4450341030800b00c800070104101d0302d48600780300f10114502e100311010090010f12211407400501040c03035056000d8416a000030f0703c0c4080729401b50250151220095060101154202480e070b4554083e04081104a10300b40c1d40d501c4441e000d035099a03c0d406000c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838787814 1250 838786564 838786567
    0xf1101140301120201020307020d080903150f0f071b061a0409020a1404110403030c0201020d080114010c0632150d020d0f0b0907050117011410110706091706040503 72
    0x1c40300200c640800c2d543c030b0060050702d10b404000d9001840119008800310782405021804403c80d080400c48054801e01c00c08d2100040d041c80181c4008404000b0180c40c0b040304503c0c000703059288507030018010600703513000c0d8400292840c9003101c0500341d0030281c009030315003203403071a0074524140c001c0320481500a098000132504000001d4680b0402c1e80d50180c00035295108003d13a00c400720000c0c001103002c1d9079480040071040c4002410078489130250801c12810200500c0000120b4604c503081842c24204020740911918041e00902040700e090400c40c807a00581ba0030401d1084061211303141c411118204607a981012032014080c2103041903040b411451988005040210b208096203001c1c540e0311041180c29924500004000c0750002229001041e08000c80e50700700c0030350403109544041403202d035810700d41001010a00c2d860000d1091143c9151105407900440000d002c40c60304400b41d4400948500025040d0040e0344190041ca50b800f51104000c2c490118100740150307441405103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838789064 1250 838787814 838787819
    0x907050105040e0709050a03200306040c050f010c020415080708030c031918140102010b030601030f17040e0a0506130203090d03200d1b0f1209060209030a0f1101140301 74
    0x50f500c40c000070116018001c6004020510399500b1645100031441a0040e170041d134280c03440b21050f00e10b140d070322038000d0f4011400d100008040190038401d84000f902c0d20210f018034000100c500c3c500a40c03005e500f051415401c50321960b40f6800d1701055805c3c1800311501669212800d0780c0d0ba101d8480240c5060700288424042e8690006450701c0c083c42d1407070300781100e541c0202248203000507544001e002d0011001075091551b0213014080c1041c1e012806050070350714503161041d03084648500184510440306d4140c2c11100d800003510046d0008400c000490310b096032007003009013010382d09a4841c07059019400700c0d094050017100c4c8900404000341401c00040c14044e0007600380b040f4001c0301100400e442992601d404405055808410400898100c505002e5045801d001c003581808000615840340e0206820002841d01c4501c0c50900003200c2070a41818030090058501e0558075001e100e01d1141032001d200c4001d03074840d000300040891900f0500040d5007903001c000c0ca5a01182d02403004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838790314 1250 838789064 838789079
    0x903040308120a060503100e070506180f01020f100605030c061c2c0a0c050a0510320702030f07080a080c0c21070e1306020a0306150512090705010504 66
    0x102d0ba04945104800b0900c0e0b078032000042c2c1800c4500f07080c5d048070307991404141e8440808100900c0100011380300c1c64503003d162500e030082d0710445a9254020b024000c0b80c4800b60b4800c02441035080c80d8038040d00c0b5403200c007805a034050681445032602c60310a1b103840003924034100b0308446420403000c0a640800c4040b690200250181c465208001031151089495003000e8400186017000300ca400313842145498070b0300740400095500071034005e880c18041800a901c1d400e0514900c182d080c10441508074241c10b903035035420741c10308089071103481b01c3c001c0303800103000724012b4868644202d0585410742c0d041048550360755441d1040b595540c2c00800c2c5040800c0314540200800c8911100340e43c10210000003251000c40c018007070201c1811004c04090f040c5406003c0103010303100070f03021184541402c0d01c01c0709a0080641019254641c001042c102d454003984c0040024440313400e80c48175032800b481010740035800200f4010081848070300001c044910119841c4182c51051b103032503041a007081d60 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838791564 1250 838790314 838790347
    0x3050c0324030f0312090a0b040803040804090204060c03020105090c0913080c0d18060503040b01051201022b0c0306032604081c110a030c0809010203070f080301050301050903040308 80
    0x54045100c40444081c4605490a000c0085581a000015652600140760420010000500c900610317004150310302c000503a070000307403608140c0280141d5102e0702d031030031706080ca8401c0741d105140040c4005000100190480304941405010380c008202c0340d0345164003540c460100000055100c00720b00000303000781c4811050181c60038016990603003041e041340e103c54070305281c0e14000404a0804074580780b02c0340035190564007a11b883d1910700e08508190741c50b20280181030084500c1078800b45086032002c1c0e0250305403619207076014803181d06c10710407543c2d0100501584803600e04d810b040c540308011035070181c001c80b02101e5100b043c510001100d40404641081c210201e80748032441044009103940c010443e03424a07114400203a0a8103032282c070003070200000e0a8100b01c1c25000001644042500220718505a82e001000544d4070035210300101c0c258030864074001d011b850781500c1d980078042c004000d14184c0303070142c1c000c010039111400041d54070b018920004010032002c210040e1065403565 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838792814 1250 838791564 838791601
    0x29030a0b0310050f07050a050412020f03010f1d0309010203180109051f2c040c03200706050a0b09070302130b071b0501030608100e15010b0a03060603050c03 69
    0x18002800310002400203040410030070021002c03d458109124044842102213a0000980d04049180408251001d000360150744509004a080b42e4468025074032014000c100a1034010001c005296950001100800c034080380036811103200000d0035494000002180c1495405070019810310060031f404122100c040c00040e810004410f2001036503440d00b5110300120903035440605000311040c5002000c0c44040c900c0070003071600c035021400d0381e4181e4010200c3d82c0101030714003180485014006070054040000824030102020b06243e00e240100e10103400b40c035100d9003092100c0d4a0b1204e400b0709840f1001d0707580e6806034130b0380d0103d0589070007540100308800e0000703020902182d507000000c42941050005070f401c1d940000c1c0c40c101c0c4012041e200e501030107007428108400c5041c24101551240b02500b030050099544404601024040051070502409c114042c04a0b6849600103251500b0103c00200800d060000c0420083d00034055184035800007522203055039181c0303078000c01512669 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838794064 1250 838792814 838792831
    0x4050a0b0f0c0a1410020a0e062a0a0c05100503072604061e050f060d0c0902030709050102061501080a0b120105090f0c0a0807090e160f09062903 64
    0x41042d118801014815002100e000b40c0180c0408601400c1c224101a84030f03451410031071040240010b00c41d0440c0300b4102a45042d1001034991000000340f140c04804404403546241d16681640b100c2e0b80f000540110251048a10034407855480781400184c4c1400550745021400500011358494440d042441403c41d0441400d1204419440c26002e58082614103550310350700c2e40c403074502544401c5105403000301d180c4000c0243d031070140307030ba01c414000140540c2e125146025250040c00740f420b650001518444504660340c1c20800d001501e002d90a12555015019400010303004615201030403100e000c0607158410503981304001500106040d448090b4400c6041031190b242190920a40d80300c2d0700b900b0010200001410380d058905070356044260300c10038a03071a06100c40003020036a542101d100080c04148074004011042c281659808403540042e10110700045007a040e10503407084400d802c8041094030b4075140203400d200e1071025010612048000c0304820102000010b50723000251 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838795314 1250 838794064 838794067
    0x623040b130b04060203040e090a03020a060b030a0b100608010f0e010513060b03040c09060f0b0706020a110d02062a120613091a0105091e100e0c0d0b0604050a0b0f 72
    0x580412401c00d410a4004c84010307800403400b4095205100e00040e0007000c00030060078150340da075a009648150001c0024102a141c0a0a441c591420010b1020203a8080551a4a482d0003141100c580301148513000004081b10000a0b94000b0000c5100c1950f2031102c8505c0035a090509000c10021907282c015019640d580c4006103416212001e180114484c0e2800a0420301d4207046a080d40c0440c1c100c8601d4030729a00003002249854402c8410056001da8050f03216118044181c80c00511070781420740d0343c0500362074489d000754042406480b40c40b03500340b185005036170040e111103040491501200141c6040000c0b01c0318140180001d540b01c00e0051641c110340c2da1124481060f40e550240894071400711302d1071345a10b80ca07040016405814107480e28034141c5403101a02c803010f90340540c0320903041c0c2c82c03001190f1460b04c01c004210180c01051500210342c102242c0c41d107a990b01603082e46160a00d003034402c074820710300001281d045860080800610b10b003001801411039100c4131201044440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838796564 1250 838795314 838795319
    0x203040b0f090a0b03060307060e04060504050108030a080708040314030411030d03140a05070c08161b170a0b07030218040603080703021605060304060b0d020a080105010623040b13 79
    0x44020400d041c0d48080e15502c94000c4024800d4111050700a203c0404050080026075100000d0200440d911440c000b4181c2c0c0110b00804e005100e541c000079001713402c020021a200800000500d595029a61083c4055a51540071101c1690607070300240020f80000340040c0c0e40151402460b000780c010301d406a100642540000d140a0110b0741d81000700742c0358101c40c81d803c00301101c0142d001442400500030780c030708950014210003203031600809802011030315040299602d116941b01039805900c40a03d030011f01d060500e00ca41a10840c600008a816413894081000c0340412030251300103803c1c810b60711119030940c044c2d00194000c408501420240c03001540e0b681c02030600650041c41d1083da103540e1414001d0411505107544082100900001c1020b07484080881c1e601130f8111a00048692404001412031490030a000e54840300c9070310045010381c0103501c000d04030390306a10303040455900302041d0351011103192104000c03158140320800c504001c0400821200b502c40c0c2200e5204c40c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838797814 1250 838796564 838796579
    0x50f030f06010e010911040e06040e030c030d05060f031506010e0f03160303020d110a030323270d091202210601180b030a03030b0126040506060a03020d1101020304 72
    0x110240e03c8000321003014001008040004c0c41405155504401190b150604000341c0302d002c60f0006e4201c900a03035482000c1420f85400b482611101d10782442565502d000d4155100050801981c3c80da1146802242500b420f150000f0400c080302010140000e243da0b5420041d10a000c42c0302c0b2940c0c0014180c03113915190340d004c2c856084e6019180c041d8004150450038020302d09a0010480070038042100c401d84c0c0001000a0942d603131942c140703404900c090505180168640070f08a00c061142000360a1148211400c21141c820084c8c1c1803001004e6010101030303513074850240400b0310220f2284a4180119054541000341c540d0000d40084082825800140c04150b80f44a0070001c43d004040103000700e048140c2c0b03919400200a40500c840d00900300006e46420342004000c050660303c031407403952a400b07480644003400c0815005814428420002c01302c0440403101114280956400100305190071000f94041d41d4000c0d00e032200318150782d0b45241c02d90140710265410352106000000d00390 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838799064 1250 838797814 838797823
    0xa110609040f1a030f030403141f1a030303130b040602040503120406020c09011d0702010f0e03041a0f03070c0305070b180c040e1b040b091e0a06030c050f030f 70
    0x120204000050801644101c5103142140c1203842ca01c640c01900c3c00920b100320000503030342034030b03001003410040c00c030b01d560400d2504120ac83c1000c1001e0003104520042501d51703124400038124600590202c80ca00c1c000c1649a2004588001c0c00610420b00c0d54041139107000d6040d0300c2407141700018034003901d450000f8035101844000c80300207400010b050081036410700c43c20b01c41070340a560007801c95040175051007a0340d0801c0c4030314040e400400001001e280c401d40222000d0303404844104040500703084069107990090040301d007460383d0b94240c070381c95101d050102c07006621a051402c0c1151240141100e0840d1a03900c240c00b0420705018050104507070141c00340c003a44003c0400d1082c08a07940c2840d081c42003510742c50b0b124034640701089800740c0c00841c000112100305500c480001a450000034003c00d003201525401030403036400c001078030400b14010948241c3c0c142d55040296030b01d810b00e0094804030b00000345101d045038400c202604000d003800c5620f400040542d41c0381075650b400c40c1d00c0e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838800314 1250 838799064 838799081
    0x1f05041a030103051b030c101b1407060e060405090403090902120a0e0d02340314060105060f0702040914010c081b0a021510030b0903040503010c030b030a11060904 72
    0xca920000041041203810001e200a03000130340525202002c0c20000280c035202e00480088c0036442038a5100100c610603180d0350110024100c05201c03007901400c240f9080b03603055101c500a44103001c004210b1500440c01444c010000903c10740c5441d007840c0502c074136840081c104505010322008003240003d0540080c02109844030402c0c1c5c0e1a20b000c40103501603450312040076015400c9034088100b40d65020410240122180501c0480420709121200311440b16100c044200e441c03a800110400c00012504a02414401d007110b01a0741c0b00d104001881c81384542504001030108040d900508283e003281c040680600c040c03c1d408825170216034252008a000300000401e640c0810041c4525902040c2c00800c2c00ca1500e8204140715a010395200c0c3c01d480d1303c44094455100140d2021079184112000d968402d0030410941000b40e65542c0c0c94000c3d0044511030b5081c19650b0058a109110f10491902c00400030104450302d9150090194403c002c0c2a0b000542001140c040d81c0344ca000d035041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838801564 1250 838800314 838800359
    0x2040c0915030207020f0a060e1011010e070f05100801150212040315050f010f0e09100c081b070c05010804050a05011509110703170c0d0504120305151f0504 69
    0x203407404c0510420500d140300c0015244600c7d02604180079199014511030302c0031005407505c41000708100f13003e94207503148150214940d82801410003480710085404000c440e492a80c000c602c54643c410440e03607100308031044000401d000e00400c100b89001c05052840d0103203005a6207035440461800d10076901a80055480e20b0080802d1030b1040c0c00c0f0b200d415840401107036081901c0d410a0480d9071a10380c0c4e071007450154940300c804514000c0080c40b0304200100c106504012160160f6000b030b190546c1200c1014880030440c1480041c44281c0003210380307141d480003503402401c0c10b010054800c002c0140007620144100500803000038400d10891704500040c072a4000005c2c41c1c960100141c0b1094000100402000c4c40000006a00310b8844003441d001c0e17184600e0140c1d00c042e4044080c0c01003641d040e4415040100b8802884400403816020024946d4184502d41d1561501d2b130700c1c0d1070030310621a04101c203200b81440c90240a8210b1f480d050141c907109161a660f01c11203108010007481803039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838802814 1250 838801564 838801567
    0x20d201507080f0c0a050703020c120105060a15050901030e100507031d1207120c080a0305010312110a030f210c030b090c040306050a0207080304140d1403010302040c09150302 77
    0x141e40d0342c1064005030b01860158403038007186400c94003015036000b902d40c11420f0210204260b02018001c0c80000c1541c0c10207003ea0444002d030703485507030281805075106030061030703c6d1030302062514508104102c5c2c1010341d04c51502d89000b510044000f00b040d10914405030244500c0e0101c10f4140b405000c1c0507070b040d940c001c81c0c03543c9681d0045001c80d13160203000074240d004010702d45010b014201a6003040b030704454003542d0b040407c0c00644056813503c4004010b68400550b1072480e80d0542e000606a0f80183c1228407201c15a1500740d0703a0748846038106000d80e11424400c2e0000307115422407155240c0030318105460b089255600c1d032010a40054583d513282d01c401000520300da25215071103141070304458126040c1028080003410703120703500001e00b4890b01c880c0090741e81d410507011500e105510030ba1050b070b24076040c01c3c00611825038440540d00c900801c040c01c1b00303c520514885091240c10f00c60304e89180d1840c0e007088024500d00c2e12490600c54080703400200070708a2103041c031034000300352800b6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838804064 1250 838802814 838802821
    0xf0c0f1e0b090d050a08011e0807080f06100308030a0c03180605092b0509010905090403020c01080901060f120f0c0605071527060f0f1508060601020d2015 68
    0x42e4204201c003506601001400d01c804803145a00040c850304403040880000102c0c0002000702c42c3d4424241c20480c014803606c08005000080000c0c4207441c140b40c0c1090341c2058850001c01d5844500c10306c0301034254541807001c0303201100c50390701100e00081c1d51308001800014035802d540c84070700540419142c0950b28030402039854428082c46500100050b035021040e8800c1244001c48415401000100800828001000c0e4000c0d024140a000d00809106191400e460001d54408030000e11f1400180e81c040400c1442005010399008c2d5040d00300c5c43c0c4440d600381411896881640c1800343c44031001941100007084030780a1840280c56950741d072a68503030030307810810602c0e8070103210042a00d280a00f104994440703244685c50358803160303005076070252042c10a1009010300b20b90310202c013490039003050205615907004d1580c2d20050451100300603520405103844001c1102e902d801360300f000190300c3d03143d0304c142101c010030045114440d4000480341e02861428903542440c061011030340003030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838805314 1250 838804064 838804081
    0xb1003060b120a0311210301091803050d0c050f04080c1005180d06020c011d100203060603340305060a080a0c03080a0e03011a100f0c0f1e0b 62
    0xc003080401e064400880c0110382c503035501c2e0750320b9074050080c04201850540522058043c450700120020380d00c0012030007818400ca0509680c028800d034003d0350301d020300c51014000010384a0103116013544486061284030b00c000303000340c00c2e01c911920403c10104442105030312200c0140000e003081030001c000980b1030300248211780741445846403d0100521404024500325500220001e0382500c040070050742616004007e400381055030303940b40d400d04000d10300110b6008003101c4503a880000321313100707000b4283c00741c4100c7c407090b0b8078290400340800000701280700d580c140ca100c0c00f840070f840481080c0c41c005210704070180702404000294550302030081620700054090017501c40d4030003500c88541c0ca65100c1224000901c03005010020102ea03020900c1e0156010105540c0050002c0c403000c0d1000070001c80128070401114401c001020039011814403c141412510fa4039407031b59154001076807500f050b02d40c50000111285e00b000303288070010b1b44443da4076140c400d114124441150800b404c1c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838806564 1250 838805314 838805321
    0x60906030c24430506060d0305070209070e03060604060b120705550e301510090e03040504090602030a060806090c1201090b01080a150c0f050a020106030b100306 71
    0xf003101080d07a031101c05101145003c10b03020340003181110030000903080c52030203540030700413288007a5116088c01c003000b910b150850489140804110141c031034954520b42044210781c43c5000c0e4032141007040c81a0101503404d02d500e107801850908151b4201424841580340780e602171203010504001000c000750584000400c005068001540d54a25241201c001785c400404440b01c14420401b01d808284030540703880001d18150102c00c0107041120b0203005042040d50004240c0f08242e110300c00d4540b0784000c5610741c5500640c0c66424501c9418079003000d00c0c02820140710741c00e01602003080700140030350b41c0c2c0c030807400b00903c00c4002680300d103010a40d94003181c2070b03076001c01041d40083e020440d40c1c2101240c1b90300d03104800c40e504014070400d0440140100700700c1d5001011700e03030707800d00201d644100055941c01d13561007010b849040e0510000200d060721080e191083c0401e031055401110540a00085c08140a81d0b1000241c2d09540340c0301d810442c8030039200e446803800d80c081c0a0082c01003900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838807814 1250 838806564 838806667
    0xf0606030c090c1305040c020318030d0e061b03030726060901061209050a03020c091005030c220f020915030606030f04030c08070308060906030c24 65
    0x4014041d2040c0090210721074103001401141040e100180301c200845980e1980405888040c004010000030000060740d29031140c2240300c85140840c0c9050f20b64900050020b00b440c1703403955000c40d240504020700031150002100c0c1c0d210920740609421b04d412003000514400c000e55640c19a11301a82c1d4400c880800566809040300b09030754041010607200c0d168154110b4a60f45001800842a000144014401200c0082041c095101c800d0141940050318010340304040320303888840d0721900d80d415401402e5200741901034000c508500203d28103940604c1701002c0d511030501240459004410403a20300e00e44801003654041080041070901820300700241620701c070305038a1070410f44002070365800014402e84100084100181c00c05109900030b000d696801f9800607140d284610b0b015100d00c0048521074000d603984400110140790024091080382000b070140b0798500802c0810300e008a80580c0601104c940800c000302d07988045440108480760a00300e00b000045141220503e0860b941 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838809064 1250 838807814 838807819
    0x1050c0f150f2e0b070b10081906020a030b10091802090a03111c03050414090123040b060a030203010311040912081906090506130c09051e0904050f0606 67
    0x160104101868401c0e03c18105400b40401002851003c0302c00c500c1903442500300c12079116000c20800100607060001601500c6200240c1007101c3d1a1090070f940d40340002202d0800c000d40204200100710300b64010074501a5920b40801e0300100d52020640c42d040c15800b060004101300d108102e0a030300f041300440548607100c4194504100c0e840000c0d0750001e10700019010010415034072007180d80712100c40c424400c60303202500e80c3d5541820080c00e6604103101c1d021800e0b200450f80c849510701091424182e82520302c0301c00488840d10242004280c1130411b284c0c101e5034134900030b040d680d0b98802606949a07640da0240e078035811440c0c0201418907090801d03000e1400c1c042c0000014420050b000d84518403850011403503590144556410f60000f141c03100c2c0d16240060102d03540100782c200c54400c210a4a110800401d004e000108a0740424a103c00103001d900b030034012450318800c10200508280b4444a151040310001a5658420794044031960700c640300c0362203d0321090021a5104504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838810314 1250 838809064 838809091
    0x8100506031b22060f03051b010f1b0b090d030b18042d0624032001020c0301050a0504030f08071706030a05100b010e0a030c090b01050c0f15 62
    0x11403072012454048028054401e000c0349400c0b02c4010420300c894000000f02038001d101450765480310000ea0409400f056130680503260603000c000b01a16520041d404040c2d40d144c0d89000c02e04403c0b14171406c4c0710a0315580300c0e0842c0c06a008200d03120401402141050044c0c4901134201d08042c08417800d90a455024a40010501d960061082032043e03005030002082d1364001086418160fa0700901c240c404003076080043c0c25014041154456104d44050180e4510030380c00c0b445403211350110b2803100030010000c0440b88003a5000300c11030603102400600446500400a40c0000e09550b821146264a9503a4400f00018141d10404024610182d03041405d80e5003820034008000c038001c1203052443c25442008604162020018142840c0d045819a00251416055000070388140c031111030002d040b6100c2400e061904d075401d03000700c07a80808882c6e00c10740740443d030001400b40411000d050141c24810304101c8c8400b44090101c0c0320495018001e4990141854080e510025041d000c04c29007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838811564 1250 838810314 838810333
    0x15030b1e190209010c1a0f07031505012a0f110d121b08070506162f030f070605060307090e030315030304080d020c13090209070e0d0605010810050603 66
    0x2444000c1e0350301c50307014990240e9515900e00c010707141c8114184000300ba0101600d4000c16182c410207819000344a840714444ea552924a4101c1c01d4844c98440c410000085480403c0303d58001c00140e000c20600c0100b00000c8002d0001011418001c03036000d940740c920022600080008440e200b0000300c0c0304590b07141d8051034544980d5440403544150714248480759908000c60b0f4110110710084682c40450b240d6a038055140440d110002a5079015202540c0c06052080c00c1c0110444d0300d421010074071152034170228a81d800e2a000002070040118042088400020460304000b4144503000301000300d0142459010705d49001c4144e800180c4d1245041020208103c02004a0f604100240301086828108500190647c0314a911410b07847c1302d102000c07446e940e0082282c450035101110012901e01c903402c128425129103120003540800d2200000304840d005103a03041a40074060911900c200c030550b140d00480701c3c203070000d64099001001855010189010302070b44560240d001c0e200100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838812814 1250 838811564 838811581
    0x20c0f060c0613061401120201031d0a061a0303161403030f0610031118040513020105040b03101a071b030506070c02030a020303030f0402150a0e0904050115030b1e 72
    0x1005400c006181015a00200504c40c0581258854a0512032051943d50355190004804101d540040740407034104008006503441a004025411714101c01815800b40c982c1e49200081c148200c083c060f2184d035119500451300d0410180101c0080e511a400c013084603814030b222038142c5492242c800e6441002040009071400c000640c01c40300555140080c40041442038000d40710480c03c02d152a030020030400d10700094400350600d250700c00d817000c011540720140546e81689c187d82c4060301143c01000104080520f950066501090104a00c01c0254455094101ea12140c0c680d283d00440b001c86c2c09424065600e01c604141013104440c403100300c2c41e42d950151100710040c054018001031810b8031066480a00041c414140d000b07080c2c075a24500304012500401003510b059004540151186040e05000821a20046450b0300c0e0403a46070780c0d5104100f40f2440003002101d00d0b5403251500922000c0c2a40507002442c840d40509080d4a0044191220441034109903403442050500703010850 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838814064 1250 838812814 838812823
    0x190c08013311070e09070303110a0f150f050f06060a1b0b0103060b030f0c04110706180c0806091902010c020409050105061c0312110f1b10020a17040c090c020c0f060c 73
    0x40740d15083c06a45000880c030b02d6410150840030160906070050420390810145000381c95503950300705410037203900c94501043c1104d9044035058450a82080440c100703142400241c2514070b09880c0c195425810001c85900362000d4003006c84062801c0401801082080d0140000f03d050a9008003c03c2000390090780d590704503e010326010b19640c41c003041d01800d071081214406ca8000e0010b011903010a0030000c1e80010117842a1a5040c0d880c5001c00d25080100d90140201000e6008203042d40721641800803007501a6000c80c10300000891200050f1182d005801c0c240d03005074000112072400c0c6052015220000403403452840500c2c2d41c0301c0009410a01d1302d102465036071b000082e14401302c45551064410621142c06070794001c02c01c08004880c20707003401d291040c0d12040d5940300144401070020b0b80503110300c0c00042004c403c101500180c62035140c0350721501a02c82c02d013459645d103030700c00c0484034035902e08001600008483c0c4200e080c6280300e01d69071031043d01c129103403151002845844 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838815314 1250 838814064 838814069
    0x1f050c09060d0c0e1507140f0f1f05010617280207030e0316030305031f030b041712010306020a0c06020a030e0c10080c0c0102040e0a05190c08013311070e0907 70
    0x801c01d103605a00c40b229400c020804041005c42d080b141c4108050000592b1071b04060104041c1c07984d4544607809075690380c001e06040b925181c0340c0340c03210100503604c410301d44c9005140c0d19481580749215450080c5e1502c924030341411400c80184d50720040e050062400b0700400c0034030b0082d401040111042403103207a400040740e82600c8c2081c0c90791038240913080000e01c0500c2003a46003036050b801106000410032000d0040e4815168100d185043e4000c01c40c0380e000703012450104002e01c0340104085401c98000705498151032900c400c01d1031581d501c000072a00101030480009a80d13203488020908104000c240d0410100c4001556040c0d54100070042c0c0b0000702026441040030449840c905025019180a041d4980d41d40205190400e40500105021201d01ca1219202c00c0124901c1030750b032044001c4010180d4910003240e0a02d000501000140c401b181c19001151480c4d816050040f0150503a40f026665140070144180151511717241c6640c00110401418009019030344500203081d104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838816564 1250 838815314 838815323
    0x1409070807030c0e0d080310090603020f04020a022109010906050c071401140a12060b070506220503130e061e0f0a0e070f0906021f050c09060d0c0e1507 67
    0x809501039401218281d40115100b0b812110000d4217004120300703a07024511617541a03100c217008698071000c2400703076401d910020350803440d82e061a090340c1c10309400420364103589004440d82c224144c07403181b456140c3e0b02d00c603035100d00703010581200640e0700020100c02449a8a800c03814403651011482e265461031040c84000581e40c403003500e4a0b4041e184020000440d9840c2c1c5440e40d44009000e080d450140400c200d03814900900803990228000a0b40c80403500103008102a0f03940c0044003219046040040c80000c50910f0801e0000700c0c100020020805c1510714041507070314180c41e9003401c00020740003a115081d208509e00b500c420408414054410481e00c10b401400c54001264107a07202e500304400c040c910400708840603810a0b41c1c2d50800d603075641e40074031490b40c4920403138843d400d136a0481da1244040e80d044010981701d811090b08070b00c0e0702c0e514910b0420090006035055000d4160050340680b61600715a00c0d6401190350742d0400c9058a00302c09903100504015011f102d030400092 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838817814 1250 838816564 838816571
    0xc0e070f09090f0e03030405030d11190e0a05100c0213020408100207150f05040203070603110d20070302100b090f06191e1707081c0e0a0b0301140907080703 69
    0x903d11180c0010030f800c40c200058039580e0500e410701c0350f01c0b6031002d00064019810030450400c0b03100288101c7c0d0301008065031141001600c400c0c212080d035090082071f0391101030004082142d58644c1c1d60100c12401944038a0b01001492041c4002c1c01410600c40d82c0085c81400100f01c140c8010a040000d07021041005980b10058a03007034018014402466030b125240a0341202c9070b0903247c0c00340380520300032021200d51b9552000d04806a03840072050341da042c041031011400041140d008145c540442100710712542c0d60201403005560030080c41030380160b218164955040c0114450584d00680907541001945403900d01d0208400340075004a0154480090f000c000200200c0108043c2104650724001c0c8052032418040c400700c5801803240c00c206c1d0300184042d00740000b842c00f049461403000341400300180c0301407080f0ba02c0302d8018074045c0319060403144890380c0d80d02410030182c903682d44031035280c1d4100f181c01c1a410454034205805204035074280003c1d0342e00316000544c00a582e10300072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838819064 1250 838817814 838817831
    0x180806041a0a0f06031a0a0908041703041203080f0901020f072004060f05010e18060d0c030602040602010c030b0301090c03111201062612340c0e070f0909 68
    0x32001030548410f0020303d0f0340303840c03004070400c03440451060024081008406d540e448010710303141110360185008140d03a9042000304030f4418840125000060004207880c18240c0d6540140101d101d2044210001000a401c011661003507828881c1c00071500030085061001c80040c2c0505c1380702e881c07000b03881804a059014000946040d213070809d91f9014205000040da00c01c450395101c45140127180c00306031045d05841c101d04009041032040c80540000c15000d494480900507030b450142e0054680e60b840d040f010001ca00030b40020801408954000500403520110050443d0070b00403e540c86a4148400034011403a9120303081f095036000052101128411000110420410303041c0b02c1c0554207140c00043d50303040c803c45140f80841c00e02030905001e0340440b111030303c3c0c00c040c1421411900c4107100c0c0c40340000020441c141669040821040070381c1c0c0200d02400700302d100e030400f1a000aa494400e100d07000441480a40204460501000e22121904007030b01d0f640d680c1c0200c03101b0f00d0396607114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 838820314 1250 838819064 838819081
    0x102120c040e241315050402090d020f04110705150703110a080606090409051b04021903020d090c0e060a140d030513030b010b22060c02010c02040b030d180806041a 72
    0x203803c18580000d02041604050b0029500908030f1000300d0f800801107644c0001d150700b011700840e03a0210000340542441c1c0f14541c200159045500400782d0403641d0f51030035005446e007080040c04468095001406250146003c040e01c4881c01400710082505203140309d40724031014000d860001c40d0600304000d003969130f00c0c0414504c1c00382c440340c5a40181041c088009201c000300e01c02e0b0b200007980c080203c00401030024403041e1701c81e076540c251110210410800d140791095003d427003144100e1a001c1482100764850390a400c000b41c00002c0000b10203800e200d46440d20b84018402000200d04603600c010382c01c3c1c001101120000e00240900500042c1800340d034101d0381c112406194030403d02d00307180d61a002003c840c0d0300611908900f48090240180030340c444911542e0454009584103d0f85800d07540c01118007080e4050b0417030704580c44242200040c1e50500c8414142512903848040c02c5a100c4523400d0002b00c66030240398640c2081081c0400f2814080c1c0612101007501c0c1c1d036210b1034071039264 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 838821564 1250 838820314 838820371
    0xb040f080301060302090a0f06080c0a0c061d150402010926070b0742020c010e030c070906031a040c080102030423061306050c0403140102120c040e 65
    0x400805200d0000000700304190960b02402580c2c0d0151024420180c9400d241c29400c211401807402095040780010140141c40f07005046451541c509880050b115030380304000d032140b0301541100008220a41c181344401084455070505d5800c140c088541401d800180c0408160f016500c440d11058111100f100040403a60803011614411030700f00543d01e158001d0782303810120b41252450102010340b0f80c0384030203101c04821742044041003051810030307040c854000c0e0702c03031406011010f0b028080402804401c0c4580e040c0303c0c4201025603903500c0a20009810b0a417990014402135140500a2000c203070504c02c0c0e5000c1c0f0030410380038440b90b281c90424801c4000c0035031181ca00c0b5030000042204001c008003200e00213845007403180a0801c151310900e03031198005c503114600100c1c01210036021400c9900150b0304000880002490036451351a090041030210411446680d000035100e1440b130b52a00e8211b0b0b00c52200c038915070425050040302038000c100035140450302e614606100d4030f1600c0694 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 838822814 1250 838821564 838821593
    0x150e071407050a02030601080a150207020f030d031a0a1802070507051507050111030708070c14010f05041208070f0809010b0a060c030f02010608031e070b010b040e070f0801030b04 79
    0x1540691103004514100c2c2d501c00f40f404049000e806103d00014100400040d01000e1030b600c1900303110240a0210884001c1d009503006076884040110309000e252424008191040103170fa50115565404181e820408000100200c0c01224007040405c907000e00c0c4c82c4802c8080036191000b591b50000c82c20154503114003074000e81d910081101d0900c000b100e40b080100101c0d407283d0000c0c81300100c01100040280411201d220100303020034000b606284c4106042c03141d252003917902c92090003003a80541d08640c04a22605140b030759030b005100502510500e100000051440c0164140c580181c000709000712044640091000321008100d07898004c0d0801c10341810054400d12010b1f0792110000c14441441c4c00a83c042030503841d2001040307106000e488180c03110b113030081d840c04004407603034030344044900380d004083c01c0309101c000006401404028020500e090390380d505c3c0c0d07041c00b09ca507003583c20240c1444d0038414040402001c4607000955141140d0304000050390b01c2d80c0350f0428508496421 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 838824064 1250 838822814 838822847
    0xb0f0702040b06070515010e090303010e01122a0602071e0e040629090619180b09090a0b01060305060d080711030619061205060a110705010906140703150e07 69
    0x181c8501b031121103085412412501041e000b41120384035000c50030340700c1c403080c000e00c201c0641201c0103002401d07071520104441481105d8801028600403050b400303940d0300500341041c00007101e4080000d586d04201c948040c0400340c140801d0749156501d0440c00e00c2080c49070114482d50350b0001018003511394800010b21007115920040d801c030041c0540c0700c6540760034040c1d03c40d02a0f80045002800d0030b601c0006900c01c4001000702260400e820000f03c0560940b40c00242500c1c0c0c240711045446000030700d4000c4010000070504000350749010303215808141c1041b0100761516080040030707560801c0342200e16400c101a0342d6640050305100d8030201200040a4042c8a080140b006248219055548040d4031203410031420780c5036030000029145061024060b0b5000402040035280c0715444011840c0c0750320b55103464110b9a0303440d00e0035150742c5041078508664807400c00e030788682c1d649a016401030b0760740340403c050f4a00300c0408616194600842902e50044000150303d14040c07120003a030308828 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 838825314 1250 838824064 838824073
    0x80105090a0309090c080105061321020405010e0f010311040204052e03182307030b0f06040908070b07050d090b061c0803070c0512030f06030105010b0f0702040b060705 74
    0x61100d40d48035851041240000c26a400000d03104469110f1001041c031582c0e981310b256403a0400300310b102e4010b03c80400602e065180e00140d91a10140a54560700d200010301140e00403d004200880c3c1c3c05030320604c0c04118000400184540207040c09040d00d0380081000c2c1808480d50125000740525008282c2000362076910441009650005001c1860754004003005108a481d080b015100c40300000c2c4d0740840d050382c150000510b003102090454855480e00c004c00a131411205242400c2607005a6200c24448284181001542c1c030b038550100c419541032040c1e4286a885c40d107070740b0644101801c044002400700d8109071050085035a6600401000e2010040c107042c00100c24000340c4200f03120390160651480554040756200c4407545d005400e070f42c11941e070150140c1d200404ca03401120301d40100300c642e1460ba565040950300403901f2018a164034580b980515084035010381080d440704400b8001610049001000c40341504c6e03060b030b0041104034104010810f14000d106009106004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 838826564 1250 838825314 838825321
    0x30203070804090b130e0307020906041b0503150a060c0210120203070e0301050916270c0e101701060e011b03030504051203090d0c0503120702060118020c03030a0e07080105 76
    0x415001064814021201c280f91150000f07400800c81c0c61046000d00306030000d10110015107003030070409a00400c04cc1010458850324110300543c40d010340d40603404560007006000225803203940c400000e250954169401a0510401811102d4103500092140f001582e072100000e216108105260340f54001c155100d041038403000d02034060800d1824025803070080051003200c0001003c502a140f1041281005800c0400c08000394000014030f02c02407814410301200c030b542900c00d004a44007241e861841d2550100104000780c101c40b40e1003010402081072442e002c510083e81181111000d0608034040069503006803042c500c4034600f005620003a0072050113144d050740200c1d100e903210f10b060315948250f10801d1b88850106642c040965440090304608607409000034501541c0103a0031a4144102a07201941d459011141c0c9401a04900010021401c9401d800510000310701401d50030841c4840d11941e403800010b16030301c001500c4d084061810035007840340002424902c0d000b8407842c034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 838827814 1250 838826564 838826579
    0xc0f0e0f0a0207140c2e030902031f200901080a180b1003051e0309092e03020a0b0f03040209150607030201060509150105191b05071d041707030203070804 68
    0x81170700504d140204c50400d030300240e07402c40c48015070840302c0c2000b10218070449004120300420710070b10100c0c0c041c842c442c600142007100c0a548143c21000032070200e28414a41403416540000034014019400d05001c030031380d1680c018442540c84480d19900040032210801c00e0000b100a0300c90180040d40c1c81000d010f00a05203500c88010b03207000e0012070301c14040301180b6008844e00400a4070194000380004051487d2100100b500070a6044680384101c1001d45202c948180340720060304602a611401c1003103080881c1c04e4801010000f030842e050070007110b40c498140c40b00420007032048080c400007810024450050904501019009649480301450041e000701030358041e0a05c107401e00c40010f050b458aa051682142a06a4030581031245441c1c0c466015003003a150042806030140c1e400305402c824600100505015800809140d031074840c0d01c19807061240c82082c11203015504000c041804160440ba82d501202c017815174801540c2000ca00354001c0c001c0080401034001800103101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 838829064 1250 838827814 838827823
    0x602030705011b080c0d02040b0a0e01080f310f0b0906060a1d090c15041e15110115031208070f1e05040803030c03040c0f0e0f0a020714 60
    0x1a200310300800c0f2400781215504008401c480141c80001c10210014102030445009410b210500c104094101600c81490b801075805c80c0c000b003400a1800c7c460004c1070740c0c0c04141d042d0450041c48400509091103540c407410300e00200348407018082e050181d440c85555100164400582082400500d2502071614040c0074500707454000700740c8100030209d251442c041c0c0744282254816502141d000070b8242d8900c0b61203e00518a50590103285400d8201d900e8002e07800c4800e101400329036685904081c0b03a03076402e4041088401c40480fa028042c080c0ca408580d00221030324181c20300c20300d2500000007081c098112025941da034840910400410003a106c0510140e8032940c2d2544140c80e6240721003158041e1080840d04e00040b40c400303040e1841c20f0010030101800440c2e02d400792401e62034010591075903000b90f03940d0b000d8500c00402c00c030502050a103c48094400b010001c101140f03800110800740001529201c100121400440c00c1400c3da50f040f200c0c0c20358883e1160380030403110b00b59141c0780c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 838830314 1250 838829064 838829077
    0x1e030b1507020f0a03062c0a02091503121e040302150309070929091e060114131403120f030a1b02101d060f04050a1e03030c0807080f060415060203 65
    0x48140142c07900c01403844602054203518a1280140982100b5270200140740801910b515000e40003241c503040d4075181231040a100c5100782c12120ba075481c0d51028000340e0440703040c0105000a09002c2400142d84014080307842248404100e5165110103416900b805059402500c1441c07500c0000c0d0369500b100d0304100010402d0980082040307858000780310f442001115580c1c074094403180e050120900141090350416818500324484204540e200040c5511590910740e40c00440d490801c084440c071080c614608030181c0103400c0b400d28019403840320303018032410741c0c500c220007000084401d11141c1c170884c604e46542009418501213010081c2d15610845c0c1150251030508480b511036450503080e4022825a92000b407501d5526490901c4101501030400c03606409200c071a440800c506010b44140c20880f840151080c0044c0d1401504541c01511904e00f80410302c0b0400c16090b401000d000d900585c00c0c00207625694484001400800840c68060a50b020001c7d012544ca94008054440d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 838831564 1250 838830314 838830341
    0x30b0a08010b13020a0e221404050c010e0105030a020906090a0312030b011130310f0603090525050406050405101203020a0c061e030b1507020f0a0306 66
    0x802018002c8002680300340721488012441000e541e0481e8204a1138100c10311602147e010600c00d01c3e02c1184003981c04003280441510010414002070010900c0f68809200c402d00b02280e28400f0500042d109000041c480310a543c0c2c042960790b41e0b5101d44044400070304c0c00401405a4549a18082021a210103110710000c0d24000d4a2a07640d4004d005000d03d400380d9100134811548814440316107015451000074008011280ea10b0340b0f01032200180000d55041e400741924070f501012002d0140d070f0700c200302010f1500840802c204407903491b903461050310707228078011031040300606200d441e01e104030b2031059481b130782610081c044d200310b100381a081c2d4004440c00d200ca0b81c1d5440400c815038000760fa00004551041c10100540411000020355151003070040d509100260b458007100741c600e59000700e000c64001c0b0900510000c0345507000000f800346007420801d09034000e0214003000c07030088030304e41210740000780e80065641702e150041862800800036052261a441c080015004201d29801d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 838832814 1250 838831564 838831579
    0x70c1503050930220b0405121203010e270d0e030106030506010501030b12031c0c0c0c26070801060815090a020f0a090207060b0108090724030b0a08010b 67
    0x80f10508102038480701d10361100d501940d00b480810080e940c9900c0b003024103011031098001d0354100c0300c1c40c4d900c6100400703980c034010f500d0307a24200501000c445902803004154100c1d140c0d02d00100340000a40303054072000707116841c3d0341d620303036090b00003e012120b9000d10300c50300f1580311541c0e203400083c01c0c0351000540da60000b41005c15020305080c4c581d203010003055904000010b01c09035110380e214940c0158001d100e4072802d0704914045055170b010150441c0b01c400782a400c40c0b036030348540c02403100c8142c031071409134920907035030701c07600c0e90105c0500070200000d0783d0a0f0002a00c0940b80c7d101c1c01074110b41c105860240c0d595480b000e0090500d44207a02160040022042c0d404c030503116524415040407000c3c00c0421555420060f08941d00d5900aa200b50380c114041840c01303140c4017500256200700800514011010009060b03044000e00c0d03044607a1000340240400900c00d20741100e51401801e82280307a90086100782c02500f0309440481d0400c0c9018000101c10105410107080e640d01925460b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 838834064 1250 838832814 838832833
    0x90f1a060405130b010c021201090204050c072301020d1d0d02071508041a0f0601090e060102150405010f0c0819050c0307050a0306030c0f08011409060408070c15030509 74
    0x100351401284280c503403001c401459803070080c0c3e09070403420381d51805150420000c3c100707900042d4030b9500707804091013a0b0b644440b00c00c00c50401c1e04c1030a030050030520b0803a00303200d81581c4030343c1081c0485010002d0450400c5c0c07900485d4609406980b801e411074a0203101c02e800f000c40b00800e898660312842880e1040d941c0b04050743d8004a40401a07590141035900c502d01d44543c1a59a024003501c1110000380046070314445040300400a8007403041c400030552281441400141046010380244042840e03e40c180304190f83c0006e9500d10030320341c2521076625507640c0d04049004209482c010750500e41082c203405a4a580f002039035110700560001014403211700b42e02074007194400c40c1c20078a884004c101060a03140104054007101c174003031401041064503961007212a520382d5014000f40c18103200705100100b03086c00744440072000c604206540345419020a55101c0c0041c1010708001700019071001440111010080502001c15552680c1c0d001c00100a0042c042159421150301414889 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 838835314 1250 838834064 838834069
    0x2010c1e0b0c0a05032202040f060501030c1107050d060b0901121406150d050f0f061503010e101509020f13120b0a0c050d0504080a0215012d090f1a 65
    0x81d0342c45040b5a9a901741180d0303a69105180702c0032048100302d030307011031040d0240c01a070b00c81c01510030102000ea00410990b1802d4005003c2d03450003880001840b105011180f00c20b0300001d440030481d030007201e40500960050601388014400303001c004e50442c20001c0040307001d60000c140341a002d4481c1e80f8188041d61030080e01522020b095961440803114481181450f01d000000800443d000c0c6060700c07001c138026240b851074854000f00c81c0420340c0104040150000000400c49000f0200380d000340300c1600318000161b122540c0f40009024250b803941049c6070145585910070140640540c00c5580b02800c084114264000400e40c00304172000810200e240c402101c051040c06a0018a003000d503140c00b40c401d00034000b503801764405c0010a001c025913960307190045038001c50081e07803a6036a820400d031000703040646002071140701c45d060710010051000b41c113200c4648019449070300d05103482401702d411050403031544000350f11403c02d441003040f00040d84c400c0030504d00d136180211200c6000c0c0103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 838836564 1250 838835314 838835317
    0x7090305070b03060f0301140403080606040b041a120411041b050702090711014101090209060d05040b0f060406081b040603020a0b13060309080a0c02010c1e0b0c 71
    0x20082864026103010041002c644010f50380099004240100009a01c070110342180c05400800045400c10000d000526400900703040e08003409036034503481c0c40e00f440c2d9110801c2c4520320580301e406c0202000c080035500000c094907140d640d0503130440414105400e240c3c420305580014a032246203041d0818030400c02041e1000c000350700c591a010705101d40c40e002c1041c05000200080c0511810039010031140c202840f50181c4a8580b043e11484800d20200021071800400d07040d00d15042d07944a1504c10010389505141102d800b20340169440c048039000c25524050000b8842d16141414280f000b001514418180b056211724080403240e45d600c020001602c0c014410702d030054002e007022601c09514000300115600c00a0404209a07560394003145e88240c40780d0046400703203c04503152101000050154000b00020314050120b504075481e003135010700c11a40600103200100760950110390040c014008003a03081241502d0110481441c1c008040103210211012070341c401c00111030030b52040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 838837814 1250 838836564 838836569
    0x3210c080106020f07030b01030303051026060609090703080304050319031b1e05070c08031209100b180702011803050c01060602031213050a2001080105031c0e010e0303210709 77
    0x6200f41f82c07a40f842d20260014040035250441401c58220045100c689201c150000c20000700000200300400000c010b040500203071003580300d042e0103030500c14500b80000e880c1c0c080c1c80c0c104091617525116840d0143c0b03584078aa43d5400f035000030a40f695000313078040c0e009680403011003440e600b480b02e4421003240d2109942c09480380700340340900548082c44c42140904203051140c801c1800994880d0480c52a5410000c0202c2d00220801c0400c02101c00500c002d0700c195400c0301c010701c8104c80a80006d8041c40d8000e41c5401c0000003000010055031003504964680091070010100480c0b8074200140386603c480c899003250340c01d0010026400744008100c8450f2051072801086580b83c203540c540301044880c0e001d852920442001c01d0100301da51085541c840c02c19001042ca4420010015000302d0050744028801d411990540c0284501c11a2380c02e043d5a035441c204100703041210068580003001c180c01c1d0381500c0042200000d07120140d000120300c680c040642c141c1e590310440b084940b08000d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 838839064 1250 838837814 838837823
    0x504030906080a09020306091006050a03030203032d0f100b0c0c0423070e030c01030b1011012409060e041e02040603150f05090105060d03210c080106020f0703 70
    0x10420001c603849520303940e8100007401c0010903149020340000b40b500b001960060300c0f03900b0070a0030000381016489200001c010640349221035910b1a00c0c040c1d203030b01004080310100075400e040b2014081302d00d200b004401886107445a294180780d03c02084540d421241d44114421262003c00c4040d000825501c43d490000001d21030103660105000245c80205036a40281c02001c060300b19402481c40c159100b01c800d41d8429402415090425140950304098181418a448540842ca032600346c140000190745040c42c5c020740d0588048a4010501821007070004804811034100c6c0c900721990f810110740c1500814030240391190013140e1034100c00c2d200100440e1035074a44001e410042254002040c1c001400050341a960761503041c40810400e1620000b20b980f180c0b45c8280d1030789441007541000c0501c0003040a407400402099080c0c440302d4010b424407840a001140d1945100701c071900a009004017403028800c0b40c00054444030007805090058060480c00104d0034500103220350880303402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 838840314 1250 838839064 838839077
    0x4110916050c030d020c0d0f050a05093a06050a0b0a030209220609021009050a05151c0209010f02160306020a02011508030306030c1206060913050709061701050403 72
    0x1516825552940100e000c0c0d002c501080c080800a60b400c0c0c40039000030344010002d01200a40c008008181904a00510090200034800d0a00c8560300c0025a10004001e50b125071045101039450300804130000c9041c0c030703d082042e81828820032407140c441001441518217000e261103054003001500d00182c03500d608285000010030261402104a03600007110412407800006050b846142c1000c000710305440d0f1540f40d55166045060184050880030f4803881c100702220709020002d602d428251140034070a04141d03440340e1000c8588000c88044201c26180c0440703402a10070132001a40008143d1030105000403004202240003040d001010007884a089214505650f280350017500f01c084020f00315942c2e10740e01d10f40031500b041c1c43e002901c4240c003f1034503854401c00f00b51071b020144010704d000d0340c02d010311040d00b070400085598110800b00c4881c00182d442194560b612004000b02401a10545400044001140d44114195140d680d107680010100c1044242601c60a95000300040da0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 838841564 1250 838840314 838840351
    0x30b0306131118090705010f081b18091509061f03051e04150608010917090402090a09020310090b01120504050c04020a08012d12020f120105041109 65
    0x40142042c000b0402807003000c00c2c0d40c0c5103d00c0c00c02040111078440280d848188180215a009a841000f0080c6460b081000c1e103014050b1580228003c0d00540c40c0484c082400c02806869000c1e04400d0900644001e0a515100c21400c04207940f500c2000d01904404000c107203141020780c402d203451480100042c1006400500450007030074018408801015400540d000b0b0220b0100c1c2d01d400b6601078911008a005030002510071105942c0c002d507100e030300d40004100002c0201c5040031886464210f40d0303880b01b00324404280648540709009034081074160f80812117900300e601440c0605a07a040e9440516121007010707045401d12010907021404403401011505010340000e58810720440950380300c4d9551070049000da800100281c804945080010310004962068030301ba0310a203045c442501a0750040303c0d40c0348403440d0060321000300300c0c0074010040d9110501c1c1940c140b00090206002180320080090080c40b00307850444000f10401a084c0c594640006454040d43c80c203401c45003420b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 838842814 1250 838841564 838841573
    0x10020301031b03021c060207020618033304050c03062d010b12250f0e0d1703070309080406050d050f011802090d060627110f07050c090703020406030b030613 69
    0x2002c104102c91483c0c02300b10000068072002c025240180707640d014840316001c1c04040604100300583c0ca403840c11603990f11501d5800c2c0485c5491448524174942d00b4840e10f59003021030a04030502d00c000c1e00740c865081030024000450a41d20072a90300401c912501c3c26140701c0580c22208207124040100406210b40d00503013010030115508030321144000800181c013180503406100541c409003020079400401d80f001c1a0300065200441c0c40c00f2101040e10f584a5600c200e2802003000e807207500d400b030100000303402c640603601143c90260010442a100c1e41e842c0002403255203c0d000300607140d800d204c082198070700d0f404825030594102c0c2582d40034407580c02d18a0002134104065040d403046000c0c81040c08100f5130310608000e070001c4010440c0181030341140c0c2e02a01c6c2c4050003412014940360700c900e60ba00092054520100c1201d10355603840c140da0900728580140800c58541c4803034507206001c0359940540c000c004a0341c4684090080320400d004140e00c030342086607400c44149880d0032410006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 838844064 1250 838842814 838842859
    0xb061215041709040f0509101103070f021e01020d0f09111009051f0e010804120e0d08030f0907090606080c0f04030f12021005160f02030c10020301031b0302 69
    0x140071890402d4100301c0740744005429a082c40c10f020600a66410a0009107001803001c0b08142080341018880c405400e490301c8002d1100820030010030041c00e0412219510902415102110102a0881c0c01075100c0c0c0f614000d40c451408e5070302940c5003412000014a1a0080050850b04012061885a040740c180b12100b040a0800c000300b00c404000481e90365183d40c00c18403801201c45542c0219103030740c2c2c00540550005201181031003401020480000c40b500542c000b104981e20f0300240c09a20304c40420140300703009200030607003800402045103103041e100d03505100e1640001218600b41c1d5518006084070828003c0e0710001c2c076208001000c505510300200451540c4100c642c2c506030752922240c89580c2c4004085841350b00c0e4000303806031558108000b604006c003540081140b82050032000c038022200b90070381303401e0200030b0400301c0c034450007481540c5090b4082000c0da080d030200b4080c07980081d842408210380c89044001c00500b0035241c008801b080c1c1c0d41c003a04103442403042c2514080e48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 838845314 1250 838844064 838844093
    0xd0c0e06070f06110c070806010609051c060f09080a020d0e060d110c1e162312030a0e1f05040b1b0304030c09051302010207180b0a030b06121504 64
    0x80f548400711000c000340480010112407030b100020340781c03131410503040b1070411106a001104008030326609120a680300602078403c52204400100740c102107217040b401502c005a07911428903d460844418441c903600140400d1070107900b940c0111100d40800e8a0402000c040181c100780c1c280141424800664003a410301c8102d68809410b1186428816203090601b651480c9521507003030000c0314584080042c1851800703a05884080c0c141001902c2002215205603402288001ca20309101c03510b4800304500810100030580b035a800c4500701c060562421000c506009010002d15401a0900c103403050740036030080e5650710725052510b000c2e1680c64200d01100004141a010814410f50040009200441c45001040c118a1501d04507404482004014100d804405178020b80180e034041039580035180d00d00c442c1d8103044803020012000344807440c86103800803044980801403090070301c0b809200d00d100303c03020303ca1103040220080d1900360440035081c151200502090000303c0c4480211071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 838846564 1250 838845314 838845323
    0x209070305012d05102a0807020906040b041113090227011107090f05070c0f1e05010f0603021002031e1e1b01060b04050d0809040b06040b0d0c0e06070f 67
    0x540f19140c0c070008252588489010010800c1c2c01261040c0b019100403844600310280380450b030108040e00c80100c43e00c03800c40d0091141103031000140c3c032a0760704e0388200341d06407018108000c0c01a0781c100e119100c0d40035050302181c50040035400580554113001302c64000000b0310344c03140c56444503642c45425081c10311400d81404184003589540c8001000560020043e100010407403518155021080701c101610110400a195540300e003c1175905807100303500340e88103808004141d1b02800001620503c040c004285500780030742000130300340c80d0f001103003070301d000700c504c5607040500c00c5050782d40c0e00c2421900c02d880c0e544001c3c0580c991305030b900a07220b240c1e50403040d824a40c00d0758001050300d500008104040310564890103088035400d20030100a00065200e41d031420f410100007410100d04020020700c2c407400000c0000e850b45564118214103240030300312035116603d821552a8a81109005000103440c2102e1103403003a2091109445410001e0003561174665151901551801c00d80001d44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 838847814 1250 838846564 838846649
    0xf020406051911030d05041b050915041d030d060e10180216030206070f1110020310030606060507170a050301140d0b090718020405031f1512020907030501 68
    0x514211050009242e4000e000c0c00006d5589050b00e41110307002e465001d203641c00440300c0018012034607203441d03554000342080e01e01e10382521200d00050107000a07050f07034180701e211b103611200d0308140000600505c2807481410300c1201c0d15000120400d0f42c04071060000b00b905007c080201028007691141000008040540b8103600e00035000d42c2c101548508070010ba1100381007002c0c140d0700c401d0300c0d0343c078485900d00b2401600070709483d40d0b80d41b11001c1402980d654000041244181c1c4610750700c0086601c03c10602c0060360380c0501800b40c1c0c0203944e003a2001103007540203407942401c84044900100041d1030b5181181d00348004406204100c1e04440e801680d00d440e42e00100c1d640107205c0b84682c0c03400d00102465818007608015240c041c0700900e141a0050009101e035540c00300b4400d06c00d031401c40d0030007080e10701c6910342c2001d015003c0880c183c40c0801100401c03040c10004216032560b00130b41d602ca4441e241e421084044820901c11041d403401c1100400d596401c02d00450807019590b800c000e13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 838848920 1106 838847814 838847837
    0x30403030b01023d06060203130906030b0f0c0d0f0f0b030604020d110a03060216200a0902090a0e01090e0c030f070626040c090f0204060519 62
    0x800180d10707104900008080d13401180314030554201824400c8503501c040103900d0794000d5122082d081403060010440b18554000c4204481c1c2c0100500641e50b980808001c8041d8047d001c1c0c4c0303a05604012500400d41d50707000340300040c1d070304040015020707191590900440342c01031500c6000e0340194081001580ea0750300300c0d81100360092a68a0900503032800100c090740c00b50402491a4070100301c0340c031025500710b02070154510440c407000c03c1000312071000e800805540c8a060740900d04007024800000181c01400d00c90f00c0181c2001d00c00c1e0f842d04155070b80c049003604444030041d0f41d807083e110001d000b080000720190098002e00308014076001c60b25145d0106000308010702000e9008215280c4011200d44481d8041c00c00e03480e0749040c2403800001e03680c1284500e11005080c41d280c541c607000070744200d6089910b191136131890b0040f6450401c0c41d0241c0a040c02c0148084800320 = true := by decide +kernel

theorem cover : BRFrame.Cov 838669064 838848920 := by
  have h0 := BRFrame.cov_init 838669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 838669064 ≤ n) (h2 : n < 838848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
