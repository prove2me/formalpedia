-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:33:01.317902+00:00
-- url     : https://prove2.me/submissions/9d85b074-fefd-4cdb-8179-47404dba1b52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 243884892 ≤ n < 244064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 243886142 1250 243884892 243884911
    0x10e06030a05041712060f01110d0503252003040f03060b031204080d090905010e0417040513060e0703050106090510090305010c020114091204031403070f03020c13020c0303 76
    0x200050108184c0c40801c220344c2c6840e107010750321848446101c00800d542160058000c901114150050b90300c6004203c040718440d501402804146000c115402c0e800206806016804000e0301d00e0240244c13080011440200e5480c01030803444821008480c82c02060700b503445070300074007040c0080380107800c0413811280d20081c00a1b42d9031a40d0003090408003800407010503500702140c0014040e4011518401d00200707580c41c100c0300c40e100d400ea0003c40d6000c1c06256000590400001c0000711004680004200e9031b00d02c0d40c2c10199a0300004030413907107840d0240122501c49c0c10402c00350b02d1031841c0703039088070b0642001c1c1f10b59030500784028002581c0d48500b5200d03c00a849080d1501d0060070080003840c0c0140090114020819010b8040c001850f0b41c0409541c1c200f000606502022032407244045586042c0c51402e46540c9850000110b401c164500b58002000a000000c901800700c2006620a4007e0714003c1390090811140c107411015565030f003401044018661030020048a45c00309503007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 243887392 1250 243886142 243886151
    0xc0b04061d01020432030105010b041d0408030f0709030b0c13080c010e0609040608061e0702030c0d081005130509062a0f0f030903070c210620040320010e06030a 71
    0x160710400c505c01d0301400d41c00d540f0307202c0003040c2406000c00810545804c00d15145181c860602c0c02e000140d42118050060b00c024804103104008800d592500403a0a180c080410768694852101030354082c1c880f1001e000002504d02c0c0000c0342d6003650801840d0f1180900181100c180020b402c8150008041c0e10507580060b0f10101d50361350741d11900103080038004507001e6140000c2591481ca545903001e0300340318100380c002034000e0310000c2181e10000880020b454401c010980c1a5200a400b0788a02c20400ca2180081001d072a5807084c3c0e03170041c19208010425082c0000b0030390400c072018000380c00c102400f40c0c0d02b0300b0314000e0705440002003201b5070000e50745008803040303a6001c0c05000061300f48035a000081c400ca4030f000101a0000c03601800d4107124150b40d03008400c40c50811081c01440902e214017154010900c2a4000d00080d211010b604103103030109940c0c05c003141c2c00b940040350710052170f603c1e075410307a01c0781070b45049018002e0034500c07140554200001c049005c002c2004d60340e1500e6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 243888642 1250 243887392 243887459
    0x303030b010e0d02300c0a0b0c0d0305100b0705010218100f0c05070e01120b0c090a090504020409050d0306081b010206010312121107020102010c0c0b0a0c0c0b04061d010204 76
    0x5079061780441d201c400100703e091130060a07016222070700d40508038442e4030010808160400c0d14412224050318400040420040891003680505002000540340c119114800100320700c03a4001060450b2003000010b9440d0140040482440078103a200e60094001c6a80941082d40001d02c030290340407503042918503541c40345070540c90f2070816004545001d102c000006049645560003c0e902c40c4120080020b5a0b1496504450360140b001c0c819070011240310104050406a40181c1c0c02c14000303040890900342070744a1500e040f10420a01c00002d40d0340c041000303103c0b41030041d0391544400450b0b4a404001c1c26000079960701040c000940003006031441d004c0400c0c0100703081d840d141241d50301480480c0d000c001d4500c4507008110140d001d0f5080001a506091043e20101d1100d0b07030000d00401c05840790007010009003100706080f01070011003680003006c0360402c505603110300e00c80e580c00b00c2c0045000305480c01c408207581680c100c581c0140410300c0f007c1401c0000d80041d070315002c1103643d40b021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 243889892 1250 243888642 243888679
    0x30c03271a090a06020c030d0e03030a0e010c30020705030c09061f0f0f0c03170c070b01080105100b07110405150d0606050102060709030c120f020a09060303030b010e0d02 75
    0xc40b265150302c0a584040003c5864000ca06807550120440c180c4c2d0340d11410070429038540e218440e582d581740d0810402c0c0c10440340a103815030f10804061411684d40100e40d55680d24072480350b00c5000c12030901020004031001711714a0907050340017a20244c00e100f0315090201ea41c41880c58146c500c2031406000007100c0707868243c01419401030803018003200003a281409002c42c080d90040100040300344030030500d590701440f01d00da01ca40d81580e440d4900004d1031800140000003401a10030124200000d10116130201d0429010300261000051242031103000103180040950000400701c03014040000840c076a041081c591450665010440356075510020840b003074545078083e441901c003144041030100c1a400b100c1a100b0a80031241d140d217405106403955000c6100040103140c8042060000c40c0303003400303005030b0584031f40805da00c041425400608078004540014203881d66501040003030552501420300900000c0c02c1c240106000035020030f0498078594070181c090242c02c06004440e80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 243891142 1250 243889892 243889897
    0x90d020109200609031b041a0f01140c030403081b01091e03020a0b0a0207111504170f030a080712090b0103060e1218030c06040e0105010813020301050103030c03271a 73
    0x80080688406600800304403062101c0c10220b03901032494418250030144070348c100d0200c0c020005100300c8800ca0504011a59100c00749144502594140007803039602d04100080c2c00030310700c90f40d580b50704c0b09042038940100240880260303d00d03a04100034400825003810340b05158030315291014200502c9818240e15008040c50002c21590502c2e003040449075071503018152403885040340e012181444810084030110300c890346404444104000c0000e103280030800b502880b220700c207450040c41440021130458001000040224000a0030000d11a5000000756103090103004100400410b540700c48030740c1d140500004219550711448170600620810051100c0c0000d00e035859590451100003800602c0318050042c001c3c400da440940c0300d0b00e0004152000d8a9014800a241e6860040112500e100c05000313402840c40001410000d600d0a0152502a6000b521030044a28181c40c00401c100b455540705800c0b455240c18590041c0c10001c3e880089a641001c0380c1c0d03c10582070080d91070352 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 243892392 1250 243891142 243891157
    0x20a021f1e0e03060c03150f0f010c1b0807030b090f030f0c100906020a3902130f1407031e020a0509040e100e160510111005090d0201092006 62
    0x188100ea0404c10417122a1004601c02e00520000d284450305120902080300c4003241d0050f07000061180040c415407180e9031b000740c510b0040060030043c0494508248919280e6001142c0b00c0c0c014171414014030101e114401d40000d0410020501c445034090307440d03220702500c24a00c2541000207134803820b81108200c18540030034050700070080701c00e047c0381c140001d500182c00c48003c1402c2d9800d41040d400700503410081881a04540f5501c1030b602130a08052030398441040360b20441124003041c4102c83c0d80f20b40800c400c0c8200e030010f03203921a5040315010650041845c000c06040151000300824890302e140202c0c8443c0c0c9002d0f0301e03100c282e0b07810344542c040c1040e0310b60042d00e064018034180c0750024540c1d480c0380003048108a01155600000c0c0c544009041009640c91484400c000d6402c00d800101198a0b4a04d401d0003154001030600c0d05041510340720500054032003043c030009000c2446042c1440225000070408040c0d1035032503180d44099960b080c0c011001044411320aa103131107044a445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 243893642 1250 243892392 243892399
    0x703030f0b130608070503010c05070605040f15050603060105060a02150702010605130b0415032f04090302010c02060609101202060d0501030b0103030305130209040206030703060f06020a021f1e0e 86
    0x2a2580c0b4800c0100464860f50085102c1d480700019182010b20805942e240607a5400e440c01d0040d40b9a48090030002d00211207114406002c54082503a80240700300d44980e01201080c1810500101480c00d9810b800140c42418100100e09071113400085801182c030f04002d046a442e0b4070741a0a0b80109010391085802c02c8020241b0b47c01d00009034048406200d00716001c100e1640c03080c4007502c00305494080202400d4602078071021004010b501c101e80d481040d81c1c1c0d54011040350300494103942220608902503915183e5080420b501400b840e0350000302a509481549018410a003548969125602d00106108245400e540340c880440304100c4040c0d04c18891540d40389003c95549109100c01d41c002442c08021038410b40c4030440100000707400034100c03c500d484580030010346900c0a4407500604d60f6455001403820f0701c4a01074801001e994005d001169058014010066030600a5186806850840d90750180d0004400f5005802607201c0c0308641020250598412030400f60340f030b0b0b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 243894892 1250 243893642 243893659
    0x70b0c10233402061f050625140d0e0906040e0304080703030905030708030705061b09030f030406030c02010207051e0f0102040902130e13020108100e0c091206010305030703030f0b 79
    0x8100c14403981c80380e10040d42241d04c2592510041e07141420980c07480403401028110410151a0104c06080030000441d1078601100c8855880c090000c0c0441e0101c0f50990b924611190199091001c21141d002500f41058405015800100c0414000340042d1007641d80d24500c40185c1c40030001e450140c00010220340c08262241000f6000c03480078403485200e44658034001c502c2c4d0385d0220507280c0d9190b1000082000303443e1a019003c60780d491451400e4490401d2101c40e105507010001542c8048021000d5030740d40303080c458001c0c2680d14003c840e1095a00400c90200000c2c0300161400d1182c0007000e9582c2e5442c4c44000c4581825902603a42d040d660020070041690019a8010882050030300c40203110681d0780d0603140300041084400302030100a644810f8050350203000215480000000e02d04045a01c59460801c990b02c2550701c000c2054010030011103030b0400148000c60040088001d140d00d600d10b5894559901c1075450060406840b507009080b9101140c01c1003020810050a414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 243896142 1250 243894892 243894961
    0x1050d0f06020f07140604120203160b1305010c1710030213050c121e0a060602062a0a020604020a1d04030c0201020c040e1c0516020103090c0503070b0c1023 69
    0xa60386d0314152019141400c00d411000e000780c0c00041190b5829246803103074003400105480b0071800c100d000349891854840024110000b030740a02c10302030350540e81e854071400c8111502040c003140d88000d00501740c0702c011070428005a62046c03840c0300c81c010038040c04101959003045003103690007030144c1160f100c11044184000c40c15540070303d107142c2028201d1002030b03030b552407507403c00e844a40c4503210150300024007284280f102d054a50740400319840a040f0300d0054500200444c0e8404070050005821501c280030031480c00311680030040444502200f90b28840d00c10724040c40d4000b038001018046c08038410400c5900900020184a8004108000d40700200c041941c41d40340c0c007807840414401d01004850349500900036a1a40d61011010f140321040c0c5c5c7d401035005200740081038a948100880000300da5600304402c5010f0300c2d000c2d041c00d84072100c1c08400d618102c081030001030210300703201c00103246030120100b24402c00c0060340440c807945c4848498241c0740150024010380c3c0903c04400b074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 243897392 1250 243896142 243896183
    0x5040506040501140f01050118080607050417010b152b06030b06192601020412050f030304020d03140903010507050306011116060f120504050706030501050d0f06020f07 74
    0x21031103140078000900072003a0792040c03143c22400c115205e58400342e04c4001442294401d10a407501b858034000e001c60785a44460040d40790050440d89800005e0000a06020700005520b04254401a100080c0220b40c03440b00001d091103011800344101543c04100c00a4403107118444030341c1440c10f5020101d000f000d80311035074040c1240b07000540322040068040343c81818069101401202c0f44107204031a1402c1c1403000464000740030a035101c070700305805503c0c0505001c2c07005000030040054034111125181c54100d04001d81103000070f400303410620812015132142c02060b800d41d42d040c98050415591108240c50501901d1002030701586840300b040039280d044070085010718001d0300d5031110000d1900010f55203c016980068440850b4102000082e00070960448600c2860410410002d0305500f0042102c10441d8295402d50205404011842d0144101d9015046c2582d0301d42010389181c41e88250300310805002041079900240a5400c03503800d50a5440003175000014003030451141c080f4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 243898642 1250 243897392 243897403
    0x6030e030d0c030b1503040f02120a06061401021204030503040b09120a0302010f0605060403150c02250501080c0301141003060f0b030103060b0a0e130c0e01090903080f0606120406060306050405 85
    0x200f80580b404414017a480c001c14419640f003154030080007400c50b8a47d40c04c1c00194100c603100803101d44104848107000442501442000c0d100000c0b40c0b4003000a1400021f15101c4225001c040d0381008000a00100343c010041b40d0981705074800b100d9941d0780b80d0b80072035141d18100a010466008030900002099419040000940290401440156110303401c1081520962100801003003046440207500501604005480d10060050315002592a105030301e005900c541e00b818940e400d10800e02080da0000e40c11500a0000409079083d98101092003542d5421a92828030071030405441024983c841d40100700a001088107855586580e55140e94183d0001e0008036826400c048140783d80b07092160310903086500d020742d1141640c40704885200a00c801e80001e4503001103004021400034802e1015a00030125400d000815041b07a080c003c00300e07900030304951401c40c06182840f5190741d5400990700c4005d003d1301404215110303450001e000300b005030300080c609401d0504000a000e00404e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243899892 1250 243898642 243898661
    0x20901031709130f0e1906110c150108010e0102040303090e10170c01140304030504050114040b1207020c1203030105010f03020c010e01150f12080f0d0906020c16050a06030e030d0c03 80
    0x606101d0022403004180d100c40060541e4075091010b654083c010601d150000070411410070406c1d27180c0300c032000c002402c1807031180c980e4403c0b01178135004200d00c4009102d500c8211203031030021030405d800c2d43d800a121104503c280000044403401161411444c0c42c010002000410352032070010b00c4920289881d54100048603000c640075046641100403480c044a128a900d581e840b8a820300303000042d1100b6144c000c06500880003480b02140191088004081042a0310100c4200385003c120080c98a1000f0148900441e504401800020800000d41e410f40d902400c2c280108401050700700c0c024014143c00140ba5030820800713402011043d80700180b1202011f0f0006e440a4480030b699004000301c3c480e140350307616a03864040c04104103502401040a4005030785207004c020080c4202510710030300059508a50001d1031003882c005c100305800081c25812800c28105140100003852400c182c410502410307100d40c8031400c840d009008071040c0b000b6140082140304070700c50707009005106505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243901142 1250 243899892 243899921
    0x1507020f070501021b010f052b1d0a080a0c170705210f07030507150f0c14030f060d150e011a0d150f1109090601050702090103170913 59
    0x15000700b025440400c9482920410216060882d075000d001100c2460f1110343c44400c00c40140440c620b00101d211a0090042030b40000804540c2e081c028402159441031048a941006600d811068280411b9503007900ea003054030180c0302c01100320700756100c1481c82401844208110b041c1003400d02c11a0190100750701400c119080c180610185418900710751034407180c07601041c0b1452070040c3c5004000c1c68541e21900d4040c3c1444140d96a00c0c0d01e103420416001c0e03500344c450395040c4900d0114850340340c0c1c50415281c4103401204410078511148000390281070400104400500c080c3c440f40104840e1a51217650f07003e8a50907000e0b210004c0103021014580c6500700b00900300354141e08029402e481c200200314807021036607591540074140b442a503003005252603070780c124811581c0b403045003110b05901c000281d403001c80108200007071341c000b002207051142c180f1006c005070700d49010880c103503a8072803103000000042101e0351249006840c04198010949403400c0000103d5800801d034011141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243902392 1250 243901142 243901153
    0x1401081605031b0409080f1c02040b09131d06040b07140d0c032a0e041401051504030215041e0608190f02040e0106180305030307050a021507020f 64
    0x24030a00c10140d03040e104036a450b61060003103007801400300e50141140c0c00020800941c000442d0345901c00c80e0805019001111008141514442c80000b403944213080c0982c0c0441c541400c00c00510b03c9230042e241040c0c0142c6443c4518407659800ba8403070070601c1c001102482070390b2500807202e9641c100480e42161521100000308400c0d5010b150049140403442e12050700340201098504000c0400641500405071a9018013500d07030885d080540013410450b80350020b8140d00c2e10064102d41d0945c1c10f40703004a10b03191003418a0003000701140e05542080701c403524050520721608800c0e0080e60806540111244050480903800034000c00803504102e2003400c807035031481c0e118091000070703114480108940800081060341e6500310701d00741c6419040001340340e6148040500403030700550800219052040e005001d800c2e080102100003c00c14a0760718065815980c3e03440e260b020103010f54041c0315010454820340e5001744040c684400701150010024680342000940d50480c02e0030000281c0281d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243903642 1250 243902392 243902413
    0x30f020111030307092c0403120e070e060105090604081006030204062408180a080a0305241306030212010603060606020f3406080601120c080a0c030f140108 69
    0x110540e0310131a5030303031a818542c5181941e01e00041c01d010941b290174000180000c200d069800407800e0290740030740d880c41080b0610100c50350454032090343e20000c5a210034420801d03003802040f0b640d031246080c6030498540c4c080402092090049400ca80c40d9030144180200d8000080d5118804803030003100c0c01d2091940d100c4000304404909a4007440c10410b000010f2034441c0a040d859401c4143d0760702c0d0840c00090702140d130f410458840400c071031403480002d5011000307a05004454001d0f8a03511080441401011804a241030144505002e4044040b0707011040c40346600807002140c000c0c050703203560070800d0601c500130400b40c081100d20034a000404681144000350b0140324841c410000e2040c0716000300d403080701c00364201303401d8151041d018203003105a20310f6050f400180060340f99180b007404e1603c009010107180c140140805072404d00c0b8114003603030090016030803006e8040000f42c0d45001d2001240900300e1840050b0209040104c86600d07109019141412601c44a0568144004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243904892 1250 243903642 243903677
    0x30621120804080702121f021b0f060106030e120705030c0d020705060d0f0605040c0906020c011403070503061915020c060c07031502070609200103050912070602040f030f0201 77
    0x2500c014180f450700303000c041c005082030280e125030200c00c0c1d0100c45403c8010036000e55000c4101417860030310398010401060406440c031400c260620340d90050000b006030b41e034501359076410502c107000400d6200c40740881d08072400e2004c11101000c1041c01c2d6940c09803418926034071340c000c1da4501c40d030344228440c1c00481480403070303044c0555800074174891a207608010800c000d400d00b01d8184004640c0e0700c60001352035a452203980c40c58a10b03034884240c21458024040d05007248030700318a06000110400203109900d05040301e6000e802c0381083da4332500c460010400c41c0780340d83c0c420f08100c0385400005c580c3c600e558001e00c40d804032603030071511000340010a000c1c80b405031404100c120b51202d03070140006034910051201000d14614018144101d5807135280c290ba60103030068030500c501000b880c0c00c10f00c400704210741c40d420a080510450405100c050340c1c41c0407034007214154507004610b0008010749501110000c040710219144040e48034280024040b84040741203010400b101c40b0204220b0f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243906142 1250 243904892 243904907
    0x1060c0203060f101403010b030703030c02090a0612330f060f050303072604140103060806061806211b12070b07030e1002150a0b0d0206090103062112 66
    0xb03001d18052000524240300710006090302d0245c2541952280c00d5100c01b40c03000c08c0694000d40c0031784c0e1400e03070003401da00511408400141a039006c450401905000d0b619140c841e0141d030b42e5211250041c19a1980340503201003811081051000040a0901c665286103401c81900c0301d804c00410003030a0340d100c03103ca6030718034144030302900340c0c0040c840c1501046c440380c0b0510025007801100e9078001441e01610007a0341c02a008a03480c042180315074100c5503814170415001c0d105100080c001c0b4200080060001000301096001010342a030000d0000d031516081d0a03030184030f441e03003c00700d07a4590581a4580d0403001e41c180d00314100c41112801854610f400070042c05510014014041c14024829542d0740560016410301030620840320060720381651904100714241e02811951190070100c045400c0090310780200c80c1d0500c0e0040d88995244da050f1421035a04039102591018500c0050b0090112640040310f840c1744100040150a0320390003038903240d4800e10121420701c90162040c0c4551 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243907392 1250 243906142 243906151
    0x1409010f0c120905030c0304060201090302061e0a09081c092006030403030e07050a0306020c06061e120a0209090a050c060304030f03050405011407020d08060d020303070305031e01060c0203060f 85
    0x34650325071241c081c40143d409620704500400c152407810881142d10f900d980e006921400041c2c0d07440316903100780355041c044542c02c1101043c0b41c4102c0381929688402a480250400a1450382c8000c414104941d20040b00c40008490f960038041c8244900e2880c0101a01c61043c0d415070240c00102c001a1000700c0015005040101034a0031a2101d44049008142c840342c0d0304641e104a520204040c1d40356001d00c00154400e0781d0150b9188600d55035117050042c0034010300c1c040c6645001403000c0c00c40300c2d61946031980301a51090144080c500c9c05915002c5002c2010b5004042c41e41400710505000c600c00c18594064000c4443c00e00b180828042030740310440d400340000300e00301520590b451081d0840c40c9c2145c001c2e00081410410308001d409496001d4529102603802503c0c60f4400c190030801c42580803000300c800f40006140c0d87c020940301d00c20713107500508004000001844c00c0f02c0400c0166403080707690501004030343c0c40303c6011741503520b0740b030302039100344540b81c0014142c241691074603105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243908642 1250 243907392 243907397
    0xb0f030d0c06090503131d010b0a0309050703060e07080d1d0405070c1209090605060408060a0903120603080901030e0115060e010302370f08131103011409010f0c 71
    0x80c04000d10407552920881400c481c65502c0f0500c0350086030b02040508460000218156241ea01d8203000e65464114842d40c03c41003214400100043d080c00c00a9985100c42030401203a2400603180007810a095170704014486890040c028041c0d500028141051341d4025046a810001000b801e4501486036220300b120428031109007511814140c0055811440d0390a244d1401d0030640e543c000c0c09100302596400003030074100c00304a00c840a0154500500e81a41e05514240c00e1000081c1c07144401024019042e44544400c2c04161050210008109001038108442903ca1420740540e034032021255001038100840165450010b20640c0090900011068502c1d07181c08401e80b100c009081c2000c0c18190300303008011640204204d0f1440c1844810107101030b51108082d00010200c0c85803503403080105005200204e140c10003d12500b0000d918044190101d032860441c410040050300190075508003621092005100102c00e8015200c0780e000b40400e8481c80203503c1183d0798030240500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243909892 1250 243908642 243908653
    0x2040606140f0d1d01091e0c030602130308180307050a12030f02030f0703030605150c0714040902060c0102030a050c0c1b060d0501060903170307080a0c0903020a180b0f03 75
    0x4000034a0b40041000c5001d141e0041681c4101d02d5084082d440c0d06465031040b0794507060300208105104c00e541514803071000d074030103000c07a1603141d41120b0526070200510340396000480c811002d1440011900456104280703590ba500e08071702d80c9101c54048411640603200c0e00c04041410320703220102e1000ea49061f019414074120719102100c00c40c080911940550004104104089098400420305039002c0d40707000c01d07018070302001d2140c01005c2032000085038a081c805030b540c0e40804910641212815502d000300300c0e00810000c4c00421142c02d0080d80080002034500c0c42c5076064000c1c51040d00410b0701004150b0300c0385414274030727489a01488501c40e004003a40150301508620703c0364004802031729090a22201602d02e40440d10300313801040c045802120b0400400804244102c80d4007860401039003541032560010b00205800f4000e80c1089458444007018a1711548480b0011a001040d1600e010707a00d40d5014103080c5c1c00700c5c3c00c8030000d0906840b1416418818440d07400340700d01900410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243911142 1250 243909892 243909907
    0x603011119170a02090319020303070210022b020f15070311160b0615041a03090f1002040f0504090b0402060309101e0506040b0102070504230a02070204060614 70
    0x1c595611940140140440310b604901082601e4892503c0f40800c4030005075a03155200805240c0400e182481000c110702d80500750058030040f094402d044e90654821160400d200006c2e4100710018130341c20b035005c1d441c003041060704180171006c600101d0359400303540c2d0241c00380984c00d44500c1d45012401d41d58240311f020441c018802d92240180c8440c0c0c15041e42071203812840f08006c40b6199078103650129440c818084036140059070514a07071503901d411840c1502e4108443d0900c4d42c1009054103412001c00002c0f20214103106800401c40300710280c5008408561840000350000e0241214003051010085810708203841118015a0480011403155480e6801c02500383c0c001008041d0902503140c1c07500289200340181c1e4500b1040b01c04600305800801105012030b400204920711540c20000d40e1a40c07642c0104544055503401d5401050070728107602d00f0008104816030410f19a220441088900d800c82c2e40500102403080310140041c0f03a680300100ca003c1d82090301c80e80010410003501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243912392 1250 243911142 243911167
    0x30910050307021213030203191e020d06050f0412031e18080a030f0f0204050d0f06060515270306070c0302120a05090a0e01080316140303010f06020606030111 70
    0x10340d40b1030510320403509041440344460440e40c01c41c01c0b441c0b4500420000500440ca4180079000000e2a01c1d00300007a14000c030303114100d08800201d50103100451240d407880540d210300c002001d61a8110400303001600700b000302d00c90808000c640a03100034541c180c145218501c00c1c020401e4019160812402c00724191641d1001801c0098615003482548500c110000d40e41801804800e2410f071400101400782146110503200016400c601407481004240016035400d01c40b21080d40e00210101d4a880c1145000c02c01400700c1d422242d8821151241c0024100c0d4031130040502e941841d501d403004041b003090b03081c51424200f05080d4141c111500040465205100c000303810780c00392048a840c07600f0105049060f0b03118051071700004400140c156031904000480c00c00034400309801c54150340c50300200b113407203015244101840c641218500310a10403a400604200720160741038075925655540380e400040c040380700e50405801408001002482c0c1840351012520746005490314011040561 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243913642 1250 243912392 243912397
    0x10506130b0a0e09060109061a0a030b01030f05010f1d07020a020603280209041803020c1309021008090607020a0f0f0516080f01060819080304020604090515011103091005 75
    0x25941210b00201c000800204030700031280100d99140c007400070340d41030580d02c0301694101e40006666942c4c1c5614440d001c282ea40898411030201e1900040045003a00102c0c00352091100320154075090500214446520700c21180c105c41d16a64010b00c1c501c0c0c41492500f0b006c200f2144500507130007038440c0d0805400c000006550000c2241086002c14101e02e07036050243c401c0d545500001c0c1c1d070108910406092034454030204001e8000c3d69620a80140d0b0020360340c90444003424050207940002c0458104d854110b180311542c018180c0b0b0310312003140c000800400e422200c41c50240305032004580e0246c00450101389480c0c0260034400c8403907607074542e4110058404404c580c0c1e849905c100c0005249040c06003000360245001030720b00c0b140b18a0050b829280740c0e0b0803458407a0400d0301c0c001d0900c0040030301c10359555071180c0031944030754440c00010150b0042c0d0340701c500650309000c1009013807045000c504584080980b105c9400301440310085517207000d038000321038008032110300b43c10219005101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243914892 1250 243913642 243913661
    0x20d080f040f17040e06010e010c05060a020a092304290904080409050f070207140d20030303011413020301050d0201030504050c121605010c03020d08150909060f0901050613 76
    0x80f0408114540e8440340c840c2e00030350100c022541e084045c0181c541e4010300181100d2800d103003c9003448220749403030307454510103000ca0740304550005d04050114001c21499005141c044082d084640241486e08002c103480c0240b54401c82c070b0003220f4100801c503010450800d0041c0c8004c8a4a00140000d022180d035010b441074505480c18080024054680d003d1107200d98001c150b40c604a061545001c0e15220641d0410903461a42003000303115620344c1040e89445d541c00c8a00d0004212401302c00e06590103c0a90441d0940000000491010701d8050600c120030003d60f100c8108040c17194100003280020b0003550361103242c14403a00701640c1300350440c035042401035003541c0705c0d0340301e8070001040c1d1417440340c0380c04058000200b1040000d80b03004400e00145000e003003a00c0365120b00e9074001d442c4c4a602c0c00030000c0c02140b4001c104016540c0220817203203003010702002d07014103080d010303942d8441d41101c1203601803800c0b900142455006008141c02240007071308858140d11024440e5014280341310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243916142 1250 243914892 243914903
    0x120c1206020409110901030b040b012307050f06070f0e0d030518040614010801050406080a121110061e05090a09170d020712050c060a02030c0705010c0f020d080f040f 73
    0x20510b120b003403007146200c13205a001181d944844000141c282c03034007112410b1181e450309122120036604851640d05c54421400d00404081c108002c0450902031042c015000b442001c0100000b41000511203024140701c0d1101c2910445061044881000f24948107400c03000651081c00000c1c051000380001916038070a02615000f02d2010504803401940100089201c0d003100481550300044094054581a942402554144085140d030354903907000c003c1c84c001d5407003c0054030307612480d422131a103500700042e519000c200d00d01280103058180547d00c41c091929113501c4845820301640c2c000c60f840540013a4443d40d5200c41440282481325080e501c881d505d056003103590780e03500c00030141c00720502c2e401610b910560600c183e1206144144605111081001120039a000100f003544040f89440260f52603441080c90b40e00c034058544010115070a081c0c4000500c3e81000d030b43c590f05a00790b800c803260300701c2c009001c95111605a564640080020000c07034003103440c030005080c603070307002c0d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243917392 1250 243916142 243916147
    0x18140402070203031b0d0e0306010e0609092109040c112805010207140d020607052505191e020a05090702010207080705030a1d090601181815120c120602 67
    0x17100050071801c00d2604846140c00c11700d281c51403660080d10100c0000c5c4190020f28071581080414880300c44080c24884c818181140000c0c0742035401c02c60030b000908010b44c4105507403202400d403541504101a510311031402c00e196046070300d114140d0326200607008801001c03e8003a82892504c8480c00f1100c00400001150365000460750034001084402d01c0780740300046503411000101d04100e088569101150041401d02003040c0d440710070380704410003490103102e0158000700800c2142c2003075000102140203d40e0754042e80461000710b21081030007000500c2e002c82c00e014005100c0c40340c400e0f009602285041c0180880e04051002d1540a44503000051030100751f07407190340040d04128411a0a40d10004034aa0032990090040c0c6515000d60244070b54682c043c130004411f003030000c4c02181046103080109100c0c039a2a4403c1c4010100c011020619019009030f09c4082c000f00708410180d943c0700c1c2d0703001a819080031200814586c220301c8201000d4100360b1251030445082c0000d48085409 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243918642 1250 243917392 243917407
    0x180d0c021201060605090411040605030f06040209090112140f0a03050706020d1104091401060905240a03060509340c08040902091e090105011b14010b011814040207020303 75
    0x3480f030140903204544903181c6586083d02000151001c503440300000240c103203c100710701a04482031703d4012007900d03c400320350394a107008103000307005644400d82d00a1003a00009104400c80d0040390400b0f004801c01c10840c14011019a5116107001e8800340c20791001c1103150110303215401030000a4441d02015141c55290f50916003503c0c131502200c5600503000804004081561090700320440510400080305d40c50404050200d080c184251805400c0e10845081080100000b0250052411254580b217100b4041d0044c000e242038012030380030380c00381c40204140303480100320268946003c02c0d054074511003c1950b45d05454031001058107200020000100242410020b04080d0001d81c50041c0c0b24044041008201c0c6500d894642d60700a007241b140c2101d841307140301c4a066510a083c00012445d4521401180070759180004d4040005042c0320300039004e0641143c3c100344400d0340c408041e50040600c094801c201c0b03102d0b008071210450b5003801c9a05107034002d80090f0b8001801e99050610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243919892 1250 243918642 243918679
    0x6120a05070b09030607450b09040e06040803070f260f060603071d13021306090e2203260919030507110d051014180d0c02 54
    0x24240c2000010800110784070303c05007010070003035502c0406894442075102882c00815450020b01e0908118400341038100d40fa0801441c0385c107198441165036442d4501c0d80c07101017014681200428034869414480e0410407131900090b424000d94005040d50301d15143c0d40070689041c4109940d520501c0968131000b048007050700344d015600d002c84881c1e1900c80c501907044400942000380f946101711024424000000d5000392079903074078403041d12525a0402200b00003001c50007580148000c0c58000215259000d000140140444039141c131641c1501d500c2d030050042d13900041b2403881d40c00c034031000d03409400f026020031201018000e0800300b40c01100f04040b0b0900d11120118480251407243c20300c10b03046010082881c820802d014a0781105c0f40d00d0340c00501c203101c0c40d2800307003050804d0424194182d0360540e0031014107500c80c00b202c00000e12030707004001800321a0724516007040c02c2000101490464042c024201d250311f030103081c0d1600e1607002519075000000050f0381100c1c04820b01080e088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243921142 1250 243919892 243919903
    0x7050a120e04060501080903090411130306140c07020112020306150708070506070e0315100801060303080132011d1306050906060a02120703030e030a05040905091506120a05 76
    0x4150754030044155100180000d903529603100da4108046041040503640000c41507810f140300456020500c910310b0506032100e0300a004c41c0e05821080c021000040140d01d0f4044030300c0e080900380002c1d580d074603070001c8511402290740c0680810410441e6500c0e80300300f0760041d40c0c810703c01003007104130000d14083c3c602e13140c20000707081301d45804c00070f404001e0160811200340d0105080c644842e40040000109454101c40504a03032000e01150104000308240d41200c2c0151190078000c0160303c3e62400c004004020030300c100d000442c031140c490090f49a100003074000035091311a200c0f8490002c1001116413044490802031200344084040070542d60384031801d18110485000420b5690400040022030400540710038420701d4200f185030700c400c3d0041195504050990460368440140e41025400b401c2d01c1c12914403103001c00140e40000c1a084030280c000c0d1410303a181001555038031021980d440e02c001da0042c3da403c00400c00200c0300d2130068410342c86000100180d400d861199170f03410f442c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243922392 1250 243921142 243921173
    0xc0907140d0911090906150607140604051509010501050105071502070f060605010f0c0f061104080a0606090501091e0b0a0806010e0109050f0f04032d0e040b15090607050a 75
    0x105040c0b03c00400500d8603003001d5800480090142002d400c141202c441004100b20394103008100204911090082072140607070119082c02c11b0321f03060b1a107490107e0311850070001c4200641040c00110390501c405125031b605952042e1076191912240361200344d0402082e800100e04107800b046410000303250354403d88005403117000c01180715810040090813000e41c0c1030802040045030442d0801140c2c0244071200c1c01a002400000d01c080c480030101e80510440d0040c810910503c8103810030401a54040c01c1240e12139101003202c0c0e40c0319a00f01d81550320100400051051100c044a0741047c2c55001c1151358900400510196a0302c960080c2010401d80c80b1464000400d80100140800c074082c46900104150b0b40150038544030501102034580a400601044125010308c42c1100b800510503058a141c0410012403420b00100109042c0701100030394051803c02030044490f0404000c0c5409840c02a6001d50421803500d041c0019504400700645d40341c4291034088000c61984c40461610303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243923642 1250 243922392 243922403
    0xe0906071206151107060e1509011b03020a030206060901030237121502251109040506090d08010b0d050c1318050c04030305040b070204060503070b0703020f0c0907140d09 75
    0x4c0c00303141c20443e800c1804641c40f260a05c1504541189070313a545c011505819007003001d10340c3d1501c0b040070042b580030202200414091054440c001d050580008160b0b401c1740c420f5003120466a1503038103109469100f071000940200c0700710308500403800300a450312003040410740404038900e440c0758200146211540242290301503030041800f0701c40a46d034400c0c800d00340100b080d0302d402c5103680010030352054100740048540035003070303403504000902c0c0c00e0071640c520050400c1303141e041a042168070b40806840103034882c85112801d8101a021f10030150480e89500580c80c04d003190391407030001400b03005000d1000c40c1c6040003081140340c4a1150714014292180d0800d070103a40361940c0000711207014082d03622141b01400301708006540082120309035652250355a45400740d03440450058429a0030260b418003500d01c0c080b525800c030101600d07181e8020703030842d51141d40d050605501c6070010802650003903c001c2c0002d2403103008104040d425203000760000c6c980301d9021654401c03156500c1040300e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243924892 1250 243923642 243923657
    0x5070f0816062705150a170405030301050d030c02090c0417010204050a030201030207060902040e0309130b030d051c0c1808060702100b03030405030a08090a0e090607120615 76
    0x10340101001a0300c8801c80090100541605055002d4014030b80041c0000520415090003000074a0100816004082c0607190000800e0b01548125107078101e01c3e11800000c065000c5c2c8a08100d40c8030300315000d160040065031459082c01c00b84004451420402c1d014800d40079010070068803041d580910038601d10710000d81701d0782840a07006030001d0603000404268010b020a0020381c1d41c3c00001011240e090030016078402d0140341000203001c00c044069071062800c0c5020107982c2c0c0100003009200c1080300d031074140040d028004021100e000c2c0015405138001100716a00a010348020104606500c007042c00c41c071702c01c842441c1038408004150000032100c0b10503172500313040000071501500310036003d807100d4a40400001e40d00c0c82c041c044010015110a55000d40d501c041c021503000d42000b4099414810b9242880000c9911919040d80680c105400020300700708120300d598040d0030700d14003400242e15041c200301c0d0b1090b040080d010419a58160000d9a100040081060f44c000c0f0740325001b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243926142 1250 243924892 243924899
    0x60302031f1805060a0c0c08071a0109060e06040203091e070513050c0a0807030b1215091914030d0c0e01030e010501060903080c01060b040b04081c0e01030c0c05070f 73
    0x19200e00e00b02408000c1c1c4400c0490703000420120314503902030420000040c0d4658901400c680d04c101010010301403a000040c0d400c188060b503d1030b448100007018018440d40d036a00184021030b2a180308903a01090074002143c0c05e890250021a0041090307800c48178107003040000802408041156108643c2c880c010800903402c1240360502d08605c529004c0000340b40c681648402d030b216007150101004101400111124040c4d0300181c1511006000300d59210300d0043e41f00d607101110304610b024240e003000007580ea10800261250940e20703090141e2207003d02580c3d41c040107088000c40d007225001c140b01c0300011011501c200f40303110b0394540e20010141003a60025088820300e43c10b0a2075039050030014014180c01c0003424080f00d0740036046c07641e1802c00903403c43c01407906800c1060740c403100141c00242d40e2000c00141c000d9400c40c82c2601c014150103180500e126400694644c0803464054480c00d080d8040c1c0c0c003001000549040ca1409000d580ea40c0e01d00700b0b58203401200040c03400c1c030707002d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243927392 1250 243926142 243926203
    0x30904020301170111120105240309070f12020109151407060c03050a0b010206060609010c0b090307030f1e140702030604050d02010b0103050118020a02030d1104030308070c0b0408090406030203 85
    0x8114101c01c1d02c841c6180210800c01218580014003965005848140030604d201d014503275038401d05400400340645138144400c42d41c0d05d600c0c00d442400e000307149606011800311b08217842690240c0d07058540441242c5002240d80b1400d540d48000307810700c031141d00034458505401004000b824480c2c1000980c1c107050400c05012190082d080540b904c0c68161038508598000801981000c002c8405588035402d180040700c101041d83c2c40101038000d17038000d019415000002410843c0c6c841d0301d4405080411410032034258243c240d15000710341202d1100541c641c00f410300001c5800208500c3c0340380c0446500403e207031050641e811115580058640c07400c1d56428840e01d11060024601400254542151000c0503680c01c00020f40349a03000440c035400b1402002164110707459001c05102810b6002c0400074543c10034441a800728201c1c0d40090549881104090080c0c0c0d40300741c002a05445d99215100d85030817110480e900f2a503144408409aa0208440d982c0c56220410016030085481c420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243928642 1250 243927392 243927401
    0x30e1c0f0303180209010e061302041205070b0a050f09010306090c0c030e0418020405070203040807120b0a050121021909020306100906120b0a030c0e0f090d0c06020c0309040203011701 81
    0x42040c0038403c41c04100503502d85000d28111404140380c85c119444000c000b0320b0122045803181074940c40040c0c005407980035003200d4002a4015002d65044564900100f45c1c1d62182151170000168200300c001d40001c4488007601c2480010b2400042d01621040804e08503041c0e00f00e600c0115480eaa032200803d94001002c8102c0f44081d06c00388a4094035903c440078455010900034803454450b400148000d2081040d20020f0501100701d940d681d6a0302c11120118003138400607903c0041100c00911442c1c0503015031030403030f044d60b0071102c0d582d40b541d810081c40d40d0001404a920000001070000d07480c134214411409403289000c0141d8130b06004040088180340c114a000502807210000c0244a4211501000c10707601c1460120708410660f0014a551003070381c100811100d0300b0070021132094942d4104912624207014031043ca0b4403291620380d0b660000b983c8840004003001807490000341650040c1910800b400c049904240c10840007406a03002600181c00c09840d05100f41c004443c240035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243929892 1250 243928642 243928661
    0x40b0a0c0306181808030c0a0e040213050d020406081c110604020603070503090106030b0408090f03011413170a020a0203150c04140f09041101180f03030e1c0f0303 72
    0x341040000d103000c615038288a615481c0d0700d074480d52042610180c40c1d407a48405013440c0c1c4400101d640c1d2418101300c0c0e8060f0441e50480000071000c4203840c032182864821604401c0b00000181c4202d890502000310710054030408a0304070b0303291800050301840c01c11030500c11007440d00035800e551074000801040d040500c103083d91154800824440541c840c2d500b200d810000701d1404555070b0f0b03285080c942c003500050f8001041150030504000904c4100c8000e418448811140542810401ca041500b0786002a01241100c1c410002240d142e1100b2110b0441e15482586880c500e854252841041508150020030260300114900000c500d024054414540c90311100a10b0354144020a216036002e82d010302d60342c0c1c100c51880342c100b44d90b6100c0900035401c0010a15001c03440c1919210b14201c00c88690b050219000380340007400c508529841e80f0a0f01e540e250039016841c42c54a04544440202c40c1003900481800d41c44912201c0b202640b0400034024509001c1004030740c50000d08590b000710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243931142 1250 243929892 243929897
    0x130509061806041203090c030b040c1d0405100209120f0c01110d021b22090b10050d081b060109061e06170c1b0c090a0b010203030f040f0605040b0a0c 66
    0x60030070000424200b800d135595032103850009140200b914140c030701049283c00243c0304404440c02c000804c14518009800e8642594103034070511540700001d01d6200741650014a0f58100c0039070360403114030541c003804102000031300f001c03c0600681140c0341454072034003546410303400100c504802da50300208a650a8846280144031502c00920000e4403000030601200c90309040d04608007040c1d48a00c6a0010105030030252202d03201800c0e40500242040c06040f141c0a1292002170344010113644144129a00549a18134804482d668011654000e40001024290318900044500c1003004601c1c040c02c2c003502c00050340b42c1404d0f4150f00303c0c0000d404a001c4035000348410b01c8202d030301409040050441c042c240f1100d0b25480a00600c50081d840ca0440c038030311940d62810360190006035044d0700381064076070f41e0031a140c03003001005079541502c2450240e0701c00c0000c1186121200300256000d401140c0400b0503441596511040d280c082c2d0341075131484501002d00401d40c0a03813217000325009060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243932392 1250 243931142 243931153
    0xb03010b010203092110050702030306100f020a06050405012307110601061715121609202d0a021e060a0e030405040207060e10020c0c0f1305090618 65
    0x1000054513100b602034004400e17418030340200c80003290400039003115800e1000c090083d0325042400a41e03076001159030500c0764131000039036041c250240e000d000d800591030303000d132010003103580b15400a0070001e0421a06c03903586642c48000d0680360030003806100c4d4804001d89190918940042410301115000f070140d801c00f40c010024107400c034801300c0081c80100352040c4241e03280105d034500d2010062416030070580030741c200c024940d00420854141d4441d50b640080e01516140c0030011111581d4000c205004100c15858040880501410b030b840c1c8020600c24202c10b620501c3c01142504c002c86481d070310400301300160101d8040c003034410083c071492003044c010b00c0c450404a030f030b98402034050050203039980210188808140101d901900020304299070751007051800f100140a42d01d1460f0342c500440e80c2d04c10050180b8000c8403610110b1000824210800c030080080d14115203201c984d11200700c84100c3d41005403402000d200360107140c0505010310b080c020380c51028292460f881002d400c0b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243933642 1250 243932392 243932407
    0xf060e09011706070305060310050f010501030c030e0d0e0307030c0b0301030b0708162f0f010b010504081b0117101a09061605150406051b090d0204051f06030b03010b010203 76
    0x103010350303c04803501c5d002c90781d174031506c003c02d092600380c030203840c000343c10141000201c204003038840c3d0407143d0a90f800c025145104004400b20b88a40980b480c05070403d40d8001c104038864481102083c44c000c05854400e55650780d00081031070541d0007807124800c003100400600140e980072560290090500702d007286022502031802c004060740c403600380881d494600e0465400c03085040c188041032200101c000c551600429941d082e92020a0800d40c00c103031043c80f03194441c600b0388086400c90342c010a0600c0200b010884245c900c2c8490038100300000c001603c2c21781500c051a40510b082e0004010303014100704851100800d9001407100c103c2e4100715100098a80300c0803151041c5c211090002000803a24005041c00c0203220703544004035031a002e00c000c2c410141d1060380a50514000c05803080041c3c1003060860003240f2900d9841031141e9008805801c1c1900900d0b48850b2242c1130301c0040c13030700440f007102840c2247c01500c00a60b442c003141c02d4071b060903c62441164002d00065080841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243934892 1250 243933642 243933689
    0xa0c050918090f0102040803071401090c060309030516110a060503130b0a06030503070b010806101a031302060406020309011b0507051c06050a1a1005030a090c0f060e0901 75
    0x2510808051407861000c0051210041844000001441a4000c1d5625680e400e11503681c3d401520f02078441118030341d4185141001489080d180540c082c070107184070b0340340c40001d44c001c1c02e07801c800f9800d0000800c800104517008114004545104001c10201e541003c800c0c00303048051504440300f132160801c00d101c1c3c0c0d44a210354410b40c4a51008000310103a940c0d600b100081e013002d500041280c0320104500303040000d032014450684504004644580e900c6407295610006c0038800c460f0441e4400c00c602c024496010010340c0d102400d03142e10a02e07802240d001c00c2599121703602200058001261036403496a02c00803040301c00c2c0a928160100550300d4560315100e40180c41402d100d18606440720341c0103141502e003940c0c0b06400150800440c500b0601d60b0026140c0f18100c1111680401d20038a48c0d0b18140c001c2441d240c4003540d0319419130f554000300d01c000f041815800d945417000d400000440841010070304000c1c04041e61507480e1207822100340034041c00181c01003e0141e03098034a41d6111007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243936142 1250 243934892 243934909
    0x603120304030c1e06050f060310021c060f080f0309010e0f011e08150109050307121e120801082a0609060409151a0702012d0906080601020c030a020f040212010e0a0c0509 75
    0x1070394ac5c90060761142104111021468020f08101300c0d503082240c0002c104408000a0045808030030a60310070914075a90340f61240306440105020488820008540d0b09000d03094000c0a18107041130558001c0c850720001c2003503c4501d032800061030f0307030040114020a140300001c030310500307003030a00c0c0960510000a4940b6030364028500c104405100309401c0c45940f2800f50700c1c44c0d00c80199242902042d090501da4194144038843c0403510345400050031b4680083c0352402550b1606884010460050b04454200b8001011682c401000c0c0000710b001d40d20000248010608110002001124130080344200d00d866800000c0c20f40104d00c1440781c8115410440b01003650918140001510700c20810308402d1411810910203510310101d02131103170b0080c8150f02036540645a2007a685e540d4001240c0e1307100c440560039010f4021340603840040c2805511034140c9100200003500f01980403e8245070a030307090340403000341d889503000c0c010380140520a41a240c101441c1551426039030300301168494 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243937392 1250 243936142 243936163
    0xc0a0519030e090403020115060504080105011a1801020c130501090506030628061503140a021303021c050109030c0b0f0c0301060e131e0b03060603120304030c1e06050f0603 76
    0xc03c880400203003054401e520000d1030408503144071201c42c0d1144001131580d0040e003e0301615600e401e001250354000440711186243e50950070520300440c0c9507560805c0103c0060160640c82a00b000a031240da400303000740d900f0024845c00240d650b1620341414107441001d030442e40a42c0202c0144940d1340c100d00c0d0308480c1e01030584401c00e812814504a18003d20495100e005a1380c2c2d40560b00b094140c0c150000d005000e1201000c0c0007075190010900300b203200b000005013884030070204c10001810070090103003c5040d4000d05c90304002c9203232141b80c01c0d00c8800300100c0020f0000c004440070810a6105130750080f006240e25441e500d01000b024505100601400040c005864800d54040d6100003802d441320b402040700340950b44910910111070303481012511141414000980d6440c11300161445c4aa0030040c002d01110004001c034815550014206404000140c0020701c042501c001c009110451a0300031020344030303141d040031001c94901800300c007031941c051414800300b55400107050480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243938642 1250 243937392 243937399
    0xd02010f081003120c06380105120103050102040e01090c08010302010c05030c07030302010b13180303180c140108090d020c010513170105060411040b0409051b0c0a0519030e 76
    0x41c0d110b01581205081155000400b0030a0142d4a2012942d200d25548a1540704580c14084411031110b003da10844500b548010881c000c00b511000c00075141e0b42c034510070410b04050389812080040840c4480d0241c109032800da4000404016555100c4c445600401c4030740350400c81c2c50142c080050501506104c064108001c91083c0030500c0803d0048418000031482110f8455030340c0d06c0c010740030f4281100c0d00e03031044000718440680b55a0b980640480c00f905001007480c01c524642d0198001d10030704071090390742c00780d01e0b42840000701c00b4070050016090b40003410300f040f15080001031130844001c040030040d8004420444105400082d600d0344840e003401d00c942c5030010340021840000f401d9100004c9216042d25044003140194030041c0030b14402d0b1424815916025901c0760248250b101e03440c24200100010050760515a01140d0460b40721200352007010060108148290001c140440054011011060801404104c00800c00c480c0d5106151314400903240641040d00d054000c900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243939892 1250 243938642 243938657
    0x23601260a050403030605060a0e01110307030206010911040302060403030c06110415080613060e060a0806090d050a02031612092301140408010c0c0501050f1009090302070527060d02010f 82
    0x10580a90805405081f024001d980c82e2200e2540040414200080741808610a0381c0c4584141070040101d510f0642c042d0010201a4039241c0380f040280100400c0011300c50050001100585e00d0600910055000f82e9426000c642182000c100b00c0e00640e504e840410b500304070412803484c007603019281c4480142440c660590381c0a021480301c1600600080702c4615040000c070b038005600100d01d006000582c1c400d000ca50f00c0b00305840c0d6942c4141e60a8040d03a001194600740d15224200505411890744156410b00c074010450514054002104440080c000e4194030010740d400f011140040110300400750090700b902007410700702d0b00c1160209042110320305452802820b294100c4004149560081005492440d00200346a040c0d101c2200d49500700000300c1c04501c001203001340103034150b81c9018031444c9401e600c54020082c1480403030550090020000c2d09035644909410042e0100a00ba010750000140164114800070100340c1700d140c85501400241c0d0f4840206e0001003401d080680 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243941142 1250 243939892 243939901
    0x50402071e020f090a0e0705101e020c210c01030902010f0e06090a030c0611030903120d090c080706090504051501081e0a0c0f081306023601260a05 65
    0x2000720340c0c43c00c50700c1e4204403504280009691950f00a105105040d019683c01a031641308110303213601c40260000010390001c5615401160889010031400c00c0741c0101d4980c3c0742c101000c603240d82480c40c601c1e00c170312401d16600100803401b4002c0c55040c0800b40303410000e510840e40043d003007050703040b12402003040c4450001101d8640740100c031801c9000038403010000c1d0b40da02d030011a014860288000140c51000d00e64a186800029100c06200080140c041000300710620011034000080c4618035030b44682064022440d0710002c6404bc22500c005080e400d820320501070140d805550010740224030349000c001c0711181c0011016803010b024030b01541c0315101c0350004850100d041c19103005440440f800d211103076000d40e06c20581ca046035111a90404008501940c5034282114194440c110106a1000240c035560040000d1200400800e58140e50750311103003800000c0b0440001110b42030300100a5540e0080090509070344a4135054107a00220707003410204e100040d1400e421652910b0114 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243942392 1250 243941142 243941149
    0x7030209010903140109020312030c0f030a1803090812180411120703060302130e3703020606090c03250e060307080a0509010e1e07050603010b0310050402071e02 71
    0x104011908400d9a00c03044c40004076050003880c05980c102c0c480d2284801d000c5010f00608241c911812070500c005051500d801d01414103644010907440901d503882403800820500000e40ba600c1900030340c1d81c8002300f820441441e00e000304242e01c4016a481c00e000074241c0308801d029802014000f51004a4400c000b01114000c9000c0c28000c2d030100c20850080120b01171b4550311010449000b2241c074600600900307003040c1280c040c00740a0355176400084c03090800e0030b112074a8104a46214011280a42050040035025030b0014012401600150b041c800e11345050346199800800c441c50f0503245050480544140e849802500d401c6181c816098407030705806200c20580345180982029601e1410f030800908000302110400d108919100208403500e00501c03c00150341d811000400c012560300038802c041003141c03240300621f4443d10708081400c0c0c40d403401441c001d0902c50010b6440e030800f000c454440c80c5082d00300501562043c0240804240c2041c5c50b4081102c40320b904a01d404030342e0020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243943642 1250 243942392 243942407
    0x6130f050a050a14070b04050904080918010f0305010b1009060c140d05190c1e11150703020d08060306010605030a020c0610181505040506060c0d02010902010e09040b0703020901 78
    0x58454050f9030a080140b1400d07002e1140114000c03001d55a10644510810030640103074060b403500403083c01c00040c00103005070018040103000400c020104150803440c1c84080000341c00c00c81110f15507010402c1000070074010084019000c0b1660305001e800714078020007412091240c3c008209083c1c001d1001e000041c951441290300100540b0010401624007502075881560021862619440040c655a10800040308403a034801540c2030701500c0760390141003034200c4200a95095003041c20101c82c1d82d07111000030380744008424078a62180f02c181006030070240e441201105200d0440204000c541d00420303003e041d600c41d414005c1d2262034101b42d4070001c1c0600840001c00e44204001c0c4001400d4981d000002c40b80d0b0508010510004580100252a01801050703a918400c0000703001514041e08003540c000c4000d880141000d2029411502e4015480c00c4000580d6685040c10190751f1300020054080d83d0562303020341c2c01c0c101750781d80c0c055004005056808050f80843c4481d5140e100d02c0b00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243944892 1250 243943642 243943663
    0x60111030c0615010305070824060d2a0203220306090506040606090e19020f03060a0b13020306130905070b0c06010f1e17010f090b0a0c0206130f05 65
    0x403281c0700e4011025055448070203842a0020100000412085602c01c1c0030752403281c6040e944034400c9031101034400c401c052640d18114441d0000c40315041c12034485030007422810804d2240420807840c0050007a566500060080b610301ea1034404d040d13100781e00001100c031030240c1c0700d03504044411010003840000c04c0c20f410040c142030034014404207200300003036460300560090800300003c596910903c01200c844028048050f0806c0709030042c101c0c401890b12070214000b400580501d82c05100090801710200d41e00404d960b0380b80d905000c0c0e0f0505420020345e44030900811451030601c40000364454041c00c16180c15035440c0c1204504220081c03181c00014460a008541c5900c0d14142c80c41d02c0f81002d00684404101d106d100254000844dd030000b40700003182200700155090054800340001181c0c0240560b41d01c0b2210300100c9400c9200c0d500b181400381c80b241f0001d0814409000580b0541d10592003194860020f112990b80003200e1181e01d031f0340c44040069210300c0ca06c2c16034149440e122 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243946142 1250 243944892 243944927
    0x90b0f090406030524130b0c07210f021501170c0a0801090302010515061b0708030a0309020108091f0b03120f03010302031501260a020a180f02210601 66
    0xb2800020880000f9040f0000d42c0740200101c007012140c4d8109082100407513070440b030541d00f0500301000c00e400c000f8a9400c044038480e0303075203401c060380c0ba090200425044038903501c00101c2c642d40c80a55000c1289140c0c0d48040c40070384030b4100c220400a1091406016081940b400b01880e000103860410002c605144050032003d0401d0740c0c0e81c1114001c15030038500740c025500740400a0440380c00350105243c458030090107a41480410785c20061500c082c0d50340c413031007449520000305681c0410006001121155540412180c10510004141e880054065006507100807055102e001076a038942500c1e0494850009100000c540021b2610786802c80145000b880060b91074172030500140118140ca0090301168401c0001d000302c040064000d1140001520002c05a4205813410821014003000d44004640038480260002017440300c141e4084800b50703403800079403211285a8012038030610380c1d080b41103007040101c11100141c03151002e20107001c400c0c140000f6900ba03014004224035044c0f4413 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243947392 1250 243946142 243946151
    0x907170f010c0201050a0b0306040c0312020f06040809130e0703120903080304150c080c0f0a14030a050709080a03021002090a170a020109050609010e15090429040b01090b0f0904 78
    0x480c000f900902080d00c503035072210f0500034850041e00700010a41e0107507602848100d20145507464480d681c00c04241e4880441c007a00207500402842000140d015a02407080c0340da86162450410800d4100e032000905100e041c40a40113096101007464002c51fa000510101000d2810f0350072190100b10380c200422110001c0180014042d030070313429000050030744404221400d4811700507550401d003111049030000c0100a01f140000310700001d00560b00b03c40c2040d880035507251100400075082101e10b00d460980d203504210300c180e072203a42d540060908401402240155131002500e0b04c00340c2d80b010031030b0f030b40000f0f08410355104c40e00c40c0e03401004a9410242581c490250540e1107020030881640054143c3c0004a034a01d046401c0315002d5070140c5401c9800800345052248034a0036640305282030300c040c824000c050b10b40740140c4045034200d800104200c292401802c09103e03103001c01c02d0046190601440150343c1140501054552220301d41e911041c08003442002846480442a00203082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243948642 1250 243947392 243947411
    0x40801151707030f110f090c090a050a080a0609110301020c030c0705060a050306040f090503030c1b060705030f0c0c160527190212101a030907170f01 66
    0x203203560000e4510609091801c03801d14052240e071614640000f41c180c94202115100042144084010401014003044183c8400d0070000e0505d00044480708191203000503100158034000071080d000d07110454584020f1810b04038229500c0000385001010356556a01d82e2081c801c50501d030010400004000350355400c881481c080c1c0ba50000c4000e0103940c03060500208107890600c095486580e6a80c1c2c899045a030385400b080003900582c0502000d1075a40c038031500c0402c00c01d0005600c121500790003170b5030320b01c050383c0720309a62004103540000302c3d0010010310010550080403070390002d0203101d04038060788441c0b101c80d00c4ca1040690803121807003080e0008081000011881d402c4660455006001300d461010910b10f903521a441d824098856800250104545000c1001440c030004401420700e840440050540c2a055030b9441c4440d00358507003000300c2c9013118651a480b0100c0303040242541440b002e22a9540103500903800c0c1c00c4900e090103103030b226007046209101c160800090110125 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243949892 1250 243948642 243948671
    0xc030201270b0a1a1c020d03050903070617070522060309030f0c0f0615170f0105010503152d0a1409070605040312051b010e0c010c030c030804020105040801 69
    0x4080c50465420700042c1c00540400c803e80720300740c041015082c140081c010700c0d00400c02030074821010392126800d01d2003510050784960540c0640f00340b098850035550341d4444201843c1070803550082c0104000c848121002d10140f01c85180c0010082c149941c40300c0c000c3e072070050700030740c09081181b18070316809000900951640212034114007948031040d50b591040c0040315400d401c045c010300300c451a02100400980c0d02d9010b16040454440c2c1088501d482da0310a800961460800c0300d45a0f0124020ba100c46c1030a02c600e41c01000c00710002c01580701115680d08103010b00034615285d04070f803210080341080620401001d900008182c0000601d814030703c00d0018511040a4200b5540a90000300204030006100060710030b1911814105441c564442075501c00ba0144942006810301c28418071420307030703402e2202d545000c40c0042584282406524680041d00d0704d41070400400b42d0740c850119800031003d00030503405140c02581c40c0e45a00040e20117100300d500c171320345540c80c0c0b200700c0c00c450300b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243951142 1250 243949892 243949961
    0x31e0604030e0f01080f10090c090f0608100b09010201060317540a15020606040b0604090509010e0304060c050c10090501260a0c08160206070c030201 66
    0x10321035110040005516400c2c01180759030f40592074080b03040e28000c0b681040c0f90041c20760703000020403d2400074070380358010b400035140420210804101507100c00d10001c5002c020f00c070083c09207841c00900c6031a0502043c160b00c8018803400420450009503104564800c0d00220003654100303503660409640e056021509503c0042000007604004a00c0c600ca0040c074584012004020140280c100313070f4811200800801d6111000746d41120040140360030340f284102c50340188044c4444990020180700003900380500103107818800c038904410444140d0b04c0c00241c80c00c0e0f13160030360001a29500c4d480401d00400d415408580a0310022400141199110540c031248512400a07110f408a0b403070244180f244420440102041c0003000502c01544070351591441001c0c0040e04030030b040c81c00c034820200500c4c150350280500c0e443e24081e4442035040001c0c00e03000303100c1c0c0b80f9451005800500c000e44618020301030500b003000350242002490310075081030100c0300c550880205014421061401c00d40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243952392 1250 243951142 243951151
    0x303011e080717010b0f1302090a03050a030504080709060503070b0702180411100c0803040609080403080c01020405150702031005071214060102010b1813020d06050f100807060c060209031e06 84
    0x82d82042c54a411900341b041d0342081417100074107222002107125200502030340024007420b803c0a5580e5000020030020490b2484440c02a141d00399950700b82a071490410311640c003d41060382c104a010052600c000400d5421103000780241c80d03c3c1c11080c030004010500c4002c401c6201d03044603040c40144450340155003185282120030a41000c2d0003078050764415054000903000c0c070402d00c00079000c11803541164018522984810f0f160540365030301c2d84219004844031020582d40440d040c0513a04100c519503440a1450951500785032403540041e0f41d800c2c4001400c007803191184041501c0c0d600850f030340303080386031130030020320040b0004080000305035411641c0900560902c800350002e0f0070302415001c03500e014810400d029644482442111446000b0104d8001c40c0d2000184007041c258881e02d802103001445080003402e0515425604d2070380354012000c1d68100c40c004000107500b150301102d513503a10900168480d00424006410070174091016003001000c0c200d9411259008244140306 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243953642 1250 243952392 243952439
    0x50d0606080106060903020d021201021e0405010e09010312111f05040b0105011b0807021c03030b10090b040e060d021c06050a140a0b130c09260303011e0807 69
    0x460b40c0e84c0d181180d48961511002c0c0d08004190301c0000541400621030b911050900c00140c80c0c0902c1180c2064900080704803d141040c002ca028007240d070b402361000c4d0418004680a41482d41140c4600201d2000031010805000c1700b07007080000c103502801b154480302c0a035200c041c1c0300501d4107034900c05807404540c112580700c0035400200e0158000d0144688a03a9045031059100c8540d07605d8510380d500800083ea07008005030030450350314640d88900d40c5907500c03e03503011805106140c1480f0580304480340000074400040300a00c40106000181d82c100c070b56803030342091142c80d000007007000c001d403c40c000b942040c0101c04600220080d00f0b084540343d407103104100f1140d580c04200200701c0b000b01d40c0c4d0402002c107110105109141640000040315002440038450f100600389902c2100c003511011008a052501c04100408007200c5064050750000c03120500c3e001c2203102c0b25220302c01401580402c1000307c0c0c100c0c98005007504e0410290800f0703000c550b0929162194201d001070030100c1c0008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243954892 1250 243953642 243953651
    0x601031d070609170a031224030506090d0206070e01050408060a0203061c0b13110306160e0102150714190e0f0301020702030703060e032803140705040608070306050d06060801 77
    0x1444d501a840300120810110090114a200c50380c00300c40b1001c40c82c00d4040440d8803051070b8881414000e01c3c441012034a5500c40c02190315601d41107003030400c02010400150001c4c0d0040c0c189076000326105620949030b24040c510f942c1c0400058407503025075084440326205200801101010903801503016181c1111440e0100e199145503010071002103000406ca480d22802003031525a01404220307100d44203844480c19003284002291814130304403500b044110846000410058000349451000c407000c0c40503040a00e8074a21005003504094115002c00403811a0104400104020345541c005a811013001d060f000140c01481903210a94051103080b01003403030380702071074144204c0e0390442d806000b4245851851300c509000304204503240300c950204010403000d000503d00c1c030b04107942444a0608031304000d2000101160303441034101d8602c8204800340100740750400e043c1d6003211240c1c9064013850343c4048046010300065417010360880c00c00d007140e41c10000d4a4120000f0384242500802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243956142 1250 243954892 243954899
    0x1020c01150e1b1b01020705160b040f0b0306010c020607050c0108010b0c06191104091a0307060c08160606060203030a0f0c0504060c1b060c0b090c060a080601031d070609 75
    0x10b6480780c2921100c00c10903181c04458074401035000a00f2002c90913521426400001c8a095030a82c1c2c00001c01300c4498001451302c025405254000001030005401020b040506000c441e400350115400345017450100840011083d07889410307201c80d1980c2c0540307420303215000c03850040c1d80d6900715494036004c40c0301c42e8004a0803020003c192038166440000138100368840506400070794801a460320039994507850444544c1c00b840009100402408500080d2059040c4495003056088202c4500c2504450010448550301c441110049071300210142da03594a20b00011802c0709800400400b01400c6c0900014099008000740d846044200410710010a04100741021515880d0321000412001c1c80148100e92083d20507182c80c91045a18185c1e408034418a4020480ca1794002c800141e9100d650030100540c2503005504800d4060081c94400d04e0300001840c640201d244000806c5640c10004000b030303101e50007500c00c106260610f01c0c2c42000c89650162541c18500400e000b0400004c00007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243957392 1250 243956142 243956159
    0xe1b03070b1c0b030c130911041a2d090a021201030b04050606040606091403010608030c010902010f05030408030c070f0b09030309010c0905030604141005070201020405120120130801020c0115 84
    0x80c20fa48800500c4c0038907480c1749101b804000c08a503601030b14550041c40218205407120b22403400031220919814407460014800c00c0384a26001c0c082120310740200403040000c41442c040311b982000100c0c1d0b913844507070718410020000c0c0110380042c4144c1e05880000421322a0107400700b03008034050b00c00c0d031f40599205000e01c07007964407134030030300f4001006a8410400000000d1001c6440c0d58000e0000c250315941c0d40d2260702d5a0461400d10000d07948d901001001c5681011103100d00c00350f0b41c10301c02e08502e460b464105160000408142034084005115401c03c4011401c0e446080e0f40006201514105010b1740c5030350f078208460984442d032808a04107019409129031008403074000b0002d03c00390fa81ca5640d400c44803040100803010784a69140081a070640740140c03441401e16900060301c55142404001e980311520000d0100d991408140d0b000a846003185c0900041540b4640c82d5180304c1c240680c0808200344c1d012960551002c20051944d04041d000080301e44144400c95000c2d070b03150b8024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243958642 1250 243957392 243957403
    0x60501050c0d0e0d060e250f09020703050f0c01060608092806140408090112060510140d02071a0109062601060510030c020106090e1b03070b1c0b03 65
    0x20801c80e54400e0520900c40c5104141c140014640500409586001c42d61104195540c001131420207400030264620344402000d00490004940008440341c00d240c21070340c0700d40404c18000e076655250000344580030315000f20100d400030403031017510070b0765451000807842c005d041c1c0c0e014400c0003414201c08100400000a0411038204900358405060404006c500b1980d0803900bd081355810303110010083d90080d040002403190340201c1d04143c0c0e070b40e00680018120b2210020003010709150a43c203000da0380307460920380244051070800d03070395000b0b2a64802d076040c0101c481900c012400054610108044091116a580100324a850443e40c0f100c40704800d0710b000380a044500d00040c100c507050848403014428001c6150800010382d20344a001243d4450b281c12002c4021035107c080c1c5140d1181d09202e904000e080043d0b04004410100000b81c1c0c4071042c5080d004664a2203d031590710b15601444588024a4200143e070b949140112070040304207a500340250205241201402043c00c01084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243959892 1250 243958642 243958657
    0x108100c030b06040506090a0f1508060d0c12031404060c020a05060f03070503130804030b090f010905030f2512141602060f091003020d1d03121f0e060406050105 71
    0x450341c01c0c03d0919061106e650080d000040d404500008001210380c40b1100d100050a0010700000d4402d8201c05c0103000c508003e010030b409030000c521058041050845190241c0d119413021280d10351550500f1140384c03420002128801100040c001900b1350000c2e0780c0e00c0c00c03920950b146102140d80b407042240358010700307084410300d440400c0040c1c41148940000c540c403c0741200c007a0b401c841c1c55180e00350f01da0095042150b0001c00d240a01c03810180400800e0313455045030000380082d11141d511141c43c0c1c0182e10321200f07601c0011644c80f05c0c90020040d0880400d1007845216015000b40c10040c102c80c4424501a02003100740c05403103054400c51040346d000f00c054400705955041c0f42d07800d001656011841d12845103206114890310350303a445e90500711100c915038015071a904107030070308402c40f0f03080c2050140100320114a20403013400030080c3e44c018800201e0b5122941e4a42c401d80c0660a800140714003590a080004904091480c41d1280251b409850802c040d0380c0b00d40c01940c86101d00d01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243961142 1250 243959892 243959899
    0x70314011509090510150203070501050103080702040612021e04020c0105040507061e0e0d030e09040f0615180209031603030203031b250c0512060628030605041a0108100c030b 77
    0x8100f4090000c0c6d00048148840c1d2510403640f40003900d885480c211070013030300f00716100200051340409624150051034003406040c2c075113050160555000401c86902240b43e0394440107035402c0008550340300c3d4180c1da0481c15840c0248018a858a40b032501c0300858007618000c54010041541c1c4000304200d8034034580b0031625668280c10b0043c040010882d2005401c4007001042c01d90381206842c0d50f44801e00840c03040d1601d6840d2043d924000c405e40b442d8100071103207404141001c008090403100d01541e40c2c00c400000503568220800443e003481114100080c240440c12400010180e0010041d0310682c001e8905150f007410240b5201c540340f00702000100800c0e03401104000e000190b92903070301458414041100100d69510102d038501c0c1c0884075481d01b0303400030801c21040303041554404804a00f088240000c600003c82a49205401c2d8000642100d5542000030104a28030000841d400005c00b0103808540e503841e070442d40c40b2545e400140a450824201c140214080d00880401046c000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243962392 1250 243961142 243961171
    0x90506090f010b31020c0a02101d0d1403040b070b01050102070302060702041e0606030207060e010605090f1b0f0903150603032b110c0d110d05030703140115090905 72
    0x8000e25400d00c1c6004d00412040408022809081c9968801030903480200c5014121000445c0100050040100c042c4014010a903084858000d00b1051001d441c14046510f10001440340c108401c1200120000d503a00340310020700810b08480140c00f82c294203106001c480c0e02d5a80f0760700120303164084c510000703411080501800300141360940042180131505100540901e442d00c0340d01069600719031260020990001703003402070000c24052980030042d860b009001c0d0920380400300d0403048000380710015055841300480c9050421400c088001603514000307d49540c1c0129803070381c40e903000100302031080c1714a00e500d5a072104407500b01882050010080d600b0416240c0c4a62043d03224010513203554070607028802d254100347e10940303200c04804c03a43e203034943c481c0580061410410031808020f00c40c0c0709a003080052000142c400110700c0514001d5200d444299041d03000c0c04030281203e2895881c3c10010803904111080c0d5000d0100d01c0c0e4520001d50340e102e04210441d4001e6903a6039840110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243963642 1250 243962392 243962419
    0x30f09030a2a020d030905030f070f03080c15010303050327100b03071805040b0708190b01090518070816050331060b030606040b030c19050301090506090f010b 70
    0x12101c0b042c50440740800003002d04001c90b4000384080c2d626140442c04078000701014070141c20200403000005021a005014003414084081d0500e04548001008540005002544100c0034492050810403000e148400343d6143d00d000b0300380b500100c881c8001080f1402d148480b40e0511100d01302022a10f0703019003405c0e02001012009441009441501446400000140c9209820310740c1003040f01c50307000203403604140c580b05d5807120300030780f0010802580c1c01c10b205074001c0400d0003265201490100140015600c00140d0300c1303a0441d4807581c0c0c08050b440c1020b03024610880d555118052a995128070b41d42c43e030101c0f10404001520a400160046c030004040030150140c414603007403c0c0100c00c00c800303e042c50394668203500c450112130b082d0f00c032400b1501c41c0c2000c004d1640c00ca5000c03582441410800ca01190361100e251140520569991032040c0b40c0100180c1d0020240002800034404000181007490b07480e10705071030f14009803056034601031282030103100d0900b41040041022480318217 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243964892 1250 243963642 243963677
    0x15011805060a0f06110618070b0d0f060b07120504060c2009090706032f16050f03071106070210050c010e1516031a1c020a0b030f09030a 60
    0x3840c081d0042414100030410f40d0684a864008201c0350b078406201491043ca02400d10074082c158005240030b11103a0011060081843c0c07081d40c03410b0204680741e083c6120b804010b401603103c00202c081c03a11901040920181d001032400c03e009200390780e03101c60725001c01c03221480b442c81010002800320b89048000380c1e00c801d0300d1840b0703110b034078000b925007078402c00058034601d0548650955605c2140100403141d0103008040310720b044541c800071000b000144c1c1754081d4183d505142d0b8801400500c0c07502d05841e00040485e04c5801c80308440b658911510040d03942d52040c9400e0707840c2e05104501500f5807409400b1100741582c040c044c40d0200d52108819030300c68000d2044d0002654039941a110003020401c0100c41184443c5462482030801d441030031100c2c0324041d00c1c1000c040c1042c2c401d561401c4180710b8030001140954000c8201802103c0034071851100510003584004078031000070711680074002443c010036504a52822584410020036a00c1c821140000042100c0207140d804505c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243966142 1250 243964892 243964901
    0x90403200c0f040b120d110706020a080307270320120c010311210f0606090d200303030a02030703050601170402041a100305010608060301020c12070203070305060106030e150118 78
    0x300103070603550329114210312142480310a010420004a81170021421f1000c01c0200000800c0e142c00604008019920b50404a22008007000140b240c48a1000342c41045080441001d8050f450020b80903500e80c989207405001ca0340c2460304601c7c40b0355000a8034540181d099440701050300090002410100054000e03084900b6044958103091240888498030b5546000c00d02400d4002038403107240404200141d000701411180c05203d05101c910030540351010f003400070a4000032000e40c1603100150b00c40210b0b400f178007040e805000200600080c130085401545c02084a0380342400107684005c011a0710700d11a44840054064040100e005405d1590080d8a5505000d604030118684170010a5035603c00c00d1401c00065520070040180b40d42c05083c0707c0d0031080c118020351074200c020b4000ca44d25565045000384c1c2d00d100241005c215581000008011070f44041078030980d40e923501e40580141007641610540340112041d28444032080400903044e1100792a03641d074406032946240c0c0c001c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243967392 1250 243966142 243966161
    0x91e010e090f0601080307170405060711040f090f020301050c0f07060c031d0609151513020c0f060916150302220b0a121107030804060605090403200c0f04 68
    0x41c0100c04020310742d41c1050180714040d00100d4002c5039078850518140c4040090a185100014001e10062280d0398a4904565000da0032108004a119500c1c00080050506c0705160f40c4051514034200300700000a0021990b45000310020003a60707a0f50700b02d4224600c90319807a45801e000410030040080c1445e800200008003034038002940b075400100342c1d8000f00c6044902d080a41c0080d0401c2440c0600b00f00c0c00d207c809a644903440e0310b003400c400c4c1a90b0b030002002c0e41849056110050007600c0019419955526400021144840a0491b42a880708800d64100b00617001c0c0d4014800080121240c0e2030444215203114040003104580c1280250800104d11461802001c541c1c0814a0008015000780112209680e07460b0903008000d40f1004544250b11242c90411201c5403d40710840103850b80d15425060068003592140b9003030000f03004030340042e82d10030080c40070702040c542d210405070405038020001c2a000018058840e03625080c00044a521008a810103012401d1540007110306 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243968642 1250 243967392 243967411
    0xd020f010c030215041a1005130b0103020f070b18190b190c050a0e0a05030705010c0213020a080103060507020a21020f030f0901020c0d121b1a0402091e010e 69
    0x41103400600042d00030141c5c1d003134604d40452011002d034010181c0c03215400c01070206200e10064602004601500c003801155800d10396503c1c0840c040e80d02a804a500f9480410001c03030f030303400e00c80c41c100201d4001901e5000d01458940780d030280701d2a00051001c8201e964075440c49024510f540d40511701040203180b49584244c200c40c0d03440d4009240140b101c03650050319010340300c058a450040c030080b03011821500c2030841d444200f0094074003040d0032017610020f20f48180c3c10740740342c00401d200410702c0e2448800e85100080d0195019031016100d41a83e20509091001d80c071003110481e903511903040d001d001191203c0420303103145100e00452082006c0e42c0107686503503684009140c290303044040c01210050000a0752040f56038180108020309104403040d001c1c460381910307100020945501d610040c401844103160056040107525000264031440b42d680208501841428504059030105d000d2003a030b0f000701d41340e800c0802403840d5032a0200b1030135030142c2c81c052410901e4034000e44120301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243969892 1250 243968642 243968653
    0x80f0411030307050d0f020a03051903022101080c04050114090916060e090106030c1b0507032a050a080307080f0d0e0303100b0405010c20040515030105060d020f010c0302 75
    0x340c80e1018405800c0c41c0b4000d02c06060140341201d005403030342030000148021500080c3c21040080d410000303582e5030088030761041c3c29071821180d0907070013840749100341c41c4009680b000b103807004001042c449050b1400c1e4030941d0b56020081c1c040c40b080d00c0e0700380a00c40ba40e4017000310300b00c018104801401d50001000f81256401021020103801d602c031950898400100080760b40c4090341407101c20303940104400e1030200250380304140010501d45440c034944460184026041c010302a04100403400345801001c000c09469940102d042c2d81c10b68103100024a011031080020789180003a4070000320b030782e880e001d140707020100d07980c9a400c1d83c0501000201d20f4800e1181950b82c03e030900ca400c01c010104001140d5034145105495150040d0780e0084000c05002c200600040c1d81c400c0d00003007038581c044205041c3e1007040c04001b02507c610001d042e0406e14043c108046030319034440541c03030741c5001e034020005622403100b8043d8440200b540a5008851400811010b5100780c145a030041d000744103551 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243971142 1250 243969892 243969923
    0xe0d2007050406090e0705060a0903020d1a0a0204050102160609140d0804030503220311011b1713090501051804080c06131a10030303020309010b0d0501020a02060f010303080f04 78
    0x2d00320341c072035013019022a0340c4540883c645082044450082d1908650300b500740b001c0e0110060541c106808028040c20014900404104085400700c0035045502d8042202e451f26135000710003900b040c0f04090041c03048502a4420904540e0348009503040c0742d07610f6216505050940c040e00344450105504600000c4281010481c072001920140d4824406144e507041c4402a401003001e80040d100030741ba518002c10400108503071038003080004c0c21308200c4d9410454440e0004800385c441009840700b0840c1501c0080e00d07280900030081103c02410345840380351180b800f40202e6000b4094181c01c00c25035695031a00101081d0101d600c43e00c02c0341d51030303e0710242107681801c002d816038030451556060f0a401c0c0400c0145000340c40100745003001c400a610301845030003c074141620000d170a059000012a1f140403003134010b8070a5940203014000445194a803044c004d6000420034070040c01420007280420070020f0b2864100c030380541c0d409e81c0307503101d400e0010481c4002820450300103070002d5080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243972392 1250 243971142 243971149
    0x120c03320106081203090712030e06160b07050c150402031207030909060b030f1626060405090106080715020c0d11030601060f0f0806121501090e0d200705 68
    0x1409100c1200300202e011460072800710328200504c00d6880900c0030900400400b80f10000c0e140003200c0000e4807011046034103080a681032030594614680190000400108807100e03201c2c0b903803a0b02e2080d4060311a130340d1403000c12252401120a011aa500410a16035040ca400c1841c603400500044c2078640341e031391400d0022481d81c840f11044012490307201017006006683e110700310041000d012002d18501c0c0a10000c0ca0002c40100030003441d03100c55941c0301c0101d2141c1110002410b010313a8200060b92030b001c030013031000c0007100c065101e1420000010403010060040fa012200030000411005060640020142010800c582c085100c0c2840c0d50200707690326a200f8204074002d00418003c2c0320140c05050400340160040418000409821728065501c400144540d00e440d10b4061036507255840060800716049104040342d01c01c0b03e200c000240c0c0a0880c0318122803080c141000900e40703100090382c0703407501c540084012807102c03154102e145440c101c51411034040c090580f080d658545000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243973642 1250 243972392 243972473
    0x230d0c05031207022530020307060e03010b040c0804022701090c021507020712060207020301060e06030f0a03020d030f0b0d0510150e16050c150f01120c03 68
    0x100b00141d200100000ca0071400d0480c58903180c0042c001000744d207040c645005400302c0389030075042038501c1040300d1186d07100182061910f00da90040a845d001e5070380d144020601000d48070454400d519052540c40341d4a081e00c43d41c107188034503445640182d43c0c0c80e020070070a100c522a103ea801c9690000c0d19010360584182e15028112040d4000741880b001c5600900d000300b00c1c08400c001540a509000340d03d40c0003c1c010040f1000d003580c22242a40318500180680a14040290190709082c00401c80c000c684e13003841e204a80070b40440b0224400f4403401ea03078901101030f0143c050303040f01e0300701007029209403c100d803882d08070100810400ba511005c0340a194a100c000c3c0c549401c0344514851a426074080e41000284580003121100d0034a440521101000780c040b000d10240d1405c00314642d4011016901d114000b14140c0d0220b9103520071a000c0b1302000c036412100b803000500041410180c0070700540034590082c010210312030070342d951510454182d0145000c18290fa0280c0b50b5080e006401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243974892 1250 243973642 243973651
    0xd050303040308100b0304150b060c0a081b120a14040806180d0203040609090207050c130504051c05071b080708030714010501050d2009040609230d0c050312 69
    0x4403543d4034035040420315444c4945410081c51030f101002400b01182406269034100c0e0107401c03000825161140001c0c0790341c800e400b04040180920300b4507400303022803100034081102c0102d0360300080104100c03c00da1290406c050040c61480148004045140305800100300c800d0310b51241807401da25660810300c0d140b41101c0c03142100c468050700d407a103c2400e00140d684114240011814a800c00b480a0041e82880c06030401142c1d000c6503802c10b0000401c08854080c20180004411036074002400c0b0141c8802c0310152014422006174050380321404540060011050765403609000c01c0ba175075401042d1701c0450085030341880d2800442d520b0828000a4000e010310001950303030f103041c0c1c503000c410320b07003110f200400e103074500001003102e6240c1e1110403d8056014610081c2c582c604a00440f85006401019801020540c108001c1100c42d1784405500c80c085c41c040b20b44c2d041c00f02ca03804450540c0402c01d40140c4c11814030003444a0148180c625414403c1e8103582c1030607022180e140c005201180c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243976142 1250 243974892 243974897
    0x150c0f0803180c010503160809100c09060f020a0f020d11150c0601090b03060c0307050c0d2d121104080322080a0302070311040b1201051b09030a03030b0d0503030403 73
    0x8075202e586000401c00c804261000f8286142140740080d400b0020301401c0b00940c09001141001812071003003403144000361075180c00b01300030002007410010241d00950251101254060f0110350400303000241072000683d0021b9003001c2d541c00740d401e10107501c0c0c80300801c4418090700c0c1c2c07000c06c00707560b0191030b08080c07807075504101e4070355014407042807501006038440c0a041e880c140d407070841c5803000301e082e50b845492081525520348070a002100c3d01d01c103503e803d840d240078854109505540c01404010030010444030001c100308000552076a03040085070010201d211500b602c1d806403c43c0c0c201c00407020621b0042410295680c070124195400a010a038007100b010500e404001003519441028140ca070004200c0071695680103541d6003414000509801481144040b803075440d900700c0307000820040c0034084080001c04143c1c0c0a0242a02d0802001001819600b510610507042c2c43c610303580140100403d89164500f43c1c002c1880c1c0916542180343c100c000340c0452020801140140e1080c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243977392 1250 243976142 243976171
    0xe1b072414010e040f020105040306110a0908030324150d0203090105181b0409020d030c060b03030f090d232802010f08062403011a04150c0f0803 64
    0x11200d0403940c8081c610154084990014010710043c80b040541c4280e00041d808034078003980c001a600d5001d254002031065003840a03121000e440d40c400b03403489105549070826460780307403400c0c03c1c0c517400100d611400310b10480766038040030b4000d407139030036981040901544041c81360441510425401400000c50b450b03000414420603440c2441480d070320800030015019400303c040e44403912125543c41c914a50004a90240c0269459510402e02c081d401440e280c0a100580741c0604147d040c0c00080c1c3d0f00500c2d15100c2c1096080220072220340e100c040000c0c0e890a00403004002e0702e0b04001505440c42c0d040100e0318064107080b040c40714050f0760030500078080c00b00d0590201c01c107114803440708030303400d1103011040c0010303604020301d401d000a56060941d4540d8545010602c0d0144080340c40003018035000c00340d0004041780b002141030390b402c0c0c1400354052001031500a664440d5106400c42c003040ea1000c5681148140c203681001d510500f000c1441d07003035684501c4c403507070000d44030300c015820345 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243978642 1250 243977392 243977453
    0x20d0c0c090e010e0c0105041a030439050a0f030201120e190b07021b0609130c0c0203120306060a12230105040506040605060406050a05070b010303030b01080a060e1b07 74
    0x1048170b0340c0184400d01e412460181801c8a402ea10111380800f40c0d100700c0c000c404141004803a0190800321001c5c1c0c1c0807641d10306940c103110ba240702103c900008a02070104000300706410030180301426101424802c0e10000e1035580112445200c080c3c2081c40e0b2a5900381e500b1010509100b03202010b21400030705a507944c0c00e03003480000c58501500c80015540101c2c02c550740070344002d04400c2450022100710741c0b607411460110f0030b114040406062150300d002459507005401c10812201c00d0300a070215101082c400e01c9a40c00b500c404c2d103c05a202000340110000783e4030961904c0c048003008203011443c503182c15010b00120204c04c0360700500c00c00741d10041c44582054480c099000000310b03801e11500d803809010460380d00c2a1b00861080010003d070100c9200d0080c4e0440b01c0c1298811038505203581c0da03041c001c0003441a40c130151300180030740303022074021020f0303000c1e1200792445402d4051142e00c6103610020a80650713a603500f41da075410300102c40442c5c501e01c00720340c100480128110845a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243979892 1250 243978642 243978671
    0xd051b0108090d0219030509030114011502070e040f0c030b0c0a0806010804020a09050c090d0807050606033c1e0c0612060f060f0a0c030810030201020d0c0c090e01 72
    0x10460300712584140000f52072543e0001c0c80040d102005003008003014460b050840f858481c100320f007a00756080c500c80c01208514203e80701d0480e40002d4404c5814420000e04070788405091050f401c0320496000030034041003030148583d20140c4160a41000982c5d41d59414090343d404580140314140040b81c2d211103241c105900c0b035030041c024a050b2105181c6540000c0043c2c0b00c5010320040b903659080040d1007104000c0480d181402c00800c0b880524481386000b41c6d8030f603c802d400f15102e0188002080351030500092011681c0e44481503c5143c845d8000880840f02d107043c1003000760311030303100120300d1514140010300e400812810801a40300b851030081d450b1000d100c545500440c0200960344801140d09115500840f00f240c400c04401c8468000603d213015a00c0c41c1700d15610009102001d16801c4080450720501c280c4840c4003568584440d51744402c103501c006405130304241d100320b1041c1e1040880c0b03884544902a080d44050310f030600c00c000c4840d16004032085030b540740d08041103400b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243981142 1250 243979892 243979907
    0x304020117040f0b040620070c12080409050c07060f0b0108160f081003210201140c0301091d03040f060915021c0e030114013807020d051b01 62
    0x40074200c01042508080d9207030034003030f81000030141103894510007140c10803280d5000b215403080c01045450001102544140382c0d0f41c44248100c85085180c540021210704000300b00c15100c0e0086240340c00c080c5040c0c0c0c44409814000e00b00c054090b4104072400003d1500e03c943d0104c03068090002821007900340015114680241c01c00c450020055965440031f90f1014002940f07500300d143c030403015180ca5000080600541d0801000d102c070100300180900c10140c603400904020f0f0b4000c0c0000085007901b140e030002c3c152411400050100300500852406810600c0f4400e81c203903c4a0110380601415804c1d60415001100e855a000104000007940106c0c1d9502030a03000b41c008401601c884006540d601544203006080d1010024641c00c140c00f40e0200f954041001d4024484401710b0700358030aa41c0824000c818071002c410070000c0141000704c0c9100d1500005030070b42d000300e515000e002492600030b01400c82c2d104030b2000b90a4005041400300c050030a0401c000f110300c803c2c594001400c1031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243982392 1250 243981142 243981167
    0x40b010206010b1b070806010303030203090d08040c0b031f1401030e061302010e01110706030204060305010602030c07231f17040c12020a03060c09031b060e040b041503030503040201 80
    0x66202200500050214000700d80b03a60200030030480803031858a00060410445071b008407030702d0140e04000401d154254004620460110040c1c034143e038400081510280c90a40e0060311408000b0014000488248011908071007441e101e05c40710803894080c1402443c064004071443d50352619003041d5541c050040d002010141006080c561904480c202e401c401403041c082c0c100101e081d0b24200590042030f0a001240106c000c1c0c0c2c0269881d4240503001e03600c9403044e103000034544000019900d10110a0359540414880074125030740c0b81010007000c0039a04010800254010a0b001501c0e545243c0f201e0255200c0014440322501501400390032800000d0100b000300468404000025140c00c22410035602d440b02c03ea010001d0314008a05c0c5030086d80c00007040c5915016400080075046038144d01181e200f9508002079054505008001141d544945004079611494507081860680c00c44280420090000108650043c50800c0c040c54103510680115100005220555900c030440740143c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243983642 1250 243982392 243982397
    0x90503010b0f090604021c0501030b0f250e040216060b0d261c05061201020c0d08060d0803130b090106060914030106170706030f0b10120b0a0311040b01 67
    0x2846206404030b070490b0a400021071040c2002d6000a203665202d074181e88840000710400126120040340c1003008040a010941c2c403c104400002d8450003080c098510400c1110404002ca40004000c403250700f0603144203506004450107902101e071035034405020700140700da600382c1e6042401c0c180b09088030451620315020724142a1440045a10f204074800c440940348140b120340025010b40d62031902071079110a4045540015200064a145e001203010b084100d078074002101c1c5c0c0e0010203080380b09494200101e900308400c500281030003654441d40c0440054181440c079211a560400c0a0b40704a071090040018022020f00b48107010081e1350380f09a402000300025803e2040140c41da6401303101c0d07086020004407a418164500b03400c41c000a09000c1c4410661149981440d178895a443c06400000703494100740035500100360080c0300c5151000303400c040c860607208a00704c034800a1040b600340072684481114200e80c03034070b800a00095006001844081d9400d0007000240c03030a1540c803030704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243984892 1250 243983642 243983651
    0x20907090906140d2d110315040507091806050a05271903050c061815010f030f0f1205030a1107020f0405180114070908060415050a0204050d1209050301 67
    0x1035079191404c0c80c441c00d80e080000301080010400403022200c0203d1003880f811050000250f00b0007000f0b02c1515600130045090383ca04e030f80344c40030510850108542c050007a03800340104001c02d041a030302004604011213038007885540d2030b80f644001d40b20705031448010980e03114100148040000c0740d61049074040424a041c802001010550380d40103011200159911024840304040c000c104481e000000c44017502c85e03034079080c9041c5205070701c2201212002d000e81f8480380f0040b0840d845481c142c4090a1840d6251421a1100013034400750100c01c075070120044c128000400e28020303d110b034142c1142d82c0d040d1380c2d00e0030f1042c52080e1152510188503c020610903000141d0f580d04586100100c01ea400040700e5451154010011440b081088049d5180010700039607004a042da4900c030301041e0301d50440440d42c808010381c0c0d40760100c40141c008880c01200f0385d4040d0140c1c100f103802460140c405400c0c66180c0c3c00042420171080d40403581d14680317094030070187d03812000d004001d200881c001c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243986142 1250 243984892 243984929
    0x41715160f032d0e0105280e0c03070305210c15070203090a08070905060f0a14040902120a0312050c0a030b031015090f050c120a0603020907090906 65
    0x100003900880c071a00a01da100c00f81c0d0000d8250980360410288030402248440c4044020484024115826007107020350800001402d207120400e0078403d14011003031072055151210117240001c4c40d001c3d4034060070303008080c41c3c03801c0e40d40d0401212001e1070150015101a0032060514001d403864040744881d50b003014041c080f900c1c1000b00e1108509100c658030380e43c50703540700300e004c9040d80314041c03500c1d5200f00600301c089246000000d03c00291141c04808003c142c84040030001040d091000340c8e81c0c00081500180400f85e00b2407421580144040d02c046940880d07036000070511a01000311441d20b90010080206250340000c80d00300c1400c0c490720801007400d102300d0740c1c0d880f071189881c035609140e140d803003a801548040044658914003070008101c9030800c81c05507940d4140fa0712420800500b80145500078950078401d160003040c801c0d00c5689000f4034400e0a242c003600041105c2d000650b00c0d00004007680302c01514520030303034107640c0700b01495090401c81e5049038419001140310100519050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243987392 1250 243986142 243986147
    0x13020318070501080c0a030c02120c0c010801080102041a0d02090a0b280e0f010c0602030a05010f06020303062209051b0310060302030c19090905030702040f020a170c04171516 77
    0x22136810000f461f003c144580041c2040e450413214003e2480e189500052040f07403041c01040e01d81c2c2c0130509036603040b403c0e40e80e9070319070742030780641e000e803942ca620601d2000295800040041034816001d200140c100b5138000005104003015a101a051010002da040401c0b000350210008144d0004000d80c1c04030002c16000301141448410103005080c00a9442c000368040c42d900300515500c4070007503690f4075001f6180ca010b00700030310070440c41403003035040421a98008400d81b4459400600800b8a00030f001c6c00305290003001c041c044110983e0380c8104000308406204030b560000480103015050301e203200c2807510340781d00a441050340c0f40c0b03058404c0c00107036408607c01210a4007101e14082540207540311201402c615488407004519080360340f0308003c0f01002a18055000311420000c85101541602c01e074440c0740180000034034102034008500100d85041c80e0460000740d00c40c2e0500c9d446408005808690103002d00c041e0b0300a4040d00810685080041d5001040340000501e0b0034121202 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243988642 1250 243987392 243987397
    0x70501030c08040b06131103010f030b070207060e150c010509070303090815060607050f0a0302070806010905092e060605030a05090325170a051c0e0c0d0213020318070501080c 77
    0x35202d042c5030001342c243d01c0e0142d001540c908599404459803560352b002d46026806440c802103603d030100500050003c6d002185500846410b6112206a0300040081210781540b0040842051000b8082c0200340c00c03092181c24400e0240c40000e001d42070460802400d00b01480c2e100015640c403020120302c401803805000c43d08200255007050315070400d450110300b800c0d007001250106103c3c01200c00706155001030341ba0111610f41c0195aa1a600d4200c0300c0c2c00d030303a021118550907501038a07180c80d80040ca0703003803048611074030700600e03154050001030032003940c6060b48603a00040f0003205000301305002d4812288c102007541300461400c00c1d4140034240d041c0031003202c29040406001008140146846030742400710030007070156a00c080050000d803841e0090a940c64040503001c5c1c0e4541403e00511a10004031540d40007800601582d4040104060f00880201d070803900d070042054007201c517400503500500b0394600c554400c0e07101801280c5030080e1980218108800e0902703010607844103404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243989892 1250 243988642 243988651
    0x503120409050a09050312070806040b0d02090403140f07030219020a170c0303040909110a030b06150d0c0c021306060915020102160b0121231905070501030c08040b 72
    0x40810190342e04001032006040c44c5030042c02d9400002445e00048a00381c0105114500584902c15240c44030320a002c00c070b801c1402c1440e000300300350604a001d0319003441c41a52040c800d2034555602c40c1e1807051070100e50064011100a400b020401d07030201074050101c1a48100ca01c1514080b610441d00058034103c124468800100c2c661103140c503180d07601b4041002c8240d80502240e68541da80d40c0b0b81401401c1a500a071203038410b01c425031919203071444400044030b811845035010354660008100700000e010072401c1d41c0d06020040c05140354401d00402481503a6a1118070002941340103000350303854900304080030b562800005110503074202c00324205545109501040380000410164020300c2100c5000d000e0002c4040d00c00e0400841e48085c9041c1d5080c2110390500a1020307010388900c81407800010309510110007881d10b000030076000482444d0700f9004507149041c0075064001542080030080d91907412005040c041035802d801400c5001c4218034007891245001e4a1301d400500c000703003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243991142 1250 243989892 243989909
    0x40c090c050f0307020a1e020102061f050a1503060b0f0f0a05040503010504110f011d040b01090f0806040c1505090136140d0b1f030f080c060105031204 67
    0xc04412118071800c203450740b180c82c90a10558906003400040d42c0c070107220a04132030301e081c8841c87c8022a0704038a800b40c000b130750680007090580c982c0e900b5031001c098816054060f411980340001a1b03a62042c82100013022410f00104104191043c0141a10a10740110050300020805008007691000c2191030301d00d0400b0165440d4100541c1c03c50f1140310340d038400f581c15030134401407000340100003003c02c0c10444201c0b000c0580380040320064502e000c541da00d100d041c010030701344600c0d05c0c142900b000320343c100145080e370031207600d443c810029600141c00c015101d51018003000200310040c0600c0d00600944009130b454580d88101c01411840350005150402002c0d1140003250f61103506105d4401c40a003414410708102c940c4150140c022603c50108030980c00181160682090b0b4107602241da0001c94407030007079071011600504000c036031042074500c080202002010560f4401001c006030711400d2801c0d51401e071007996629110060304514400e4210926548040003580100d81c12510a032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243992392 1250 243991142 243991151
    0xf0708010b090316061d03010b010c02060c0a020d0506040506071b021014030c070515101502070305011103010806071718030906070606050907110601060c1506090c021203040c09 78
    0x1080404d050100340034580d48a00345200000c56071680080499440d0781000c02840079034030586041500307840030039000700c4c0840d088810440140c2002801800c8040c40c0200b04c0b05a14051340c0402d40075061035005a8154010109000401005001443c0c020200c0e00e04402d00603001002d00d0f103101850310b4020b1155040c40b40911061f8040c0c2c15010242c0800307902c40d80c4914140f51851059808440101c4984c0034281c0d401c51481041c11007603024845400c0000241420180c3c1d201c54030300144030039015031080644c00800142c007401201301e41a56110340603201e5142c1190a454601c01034a10390038071103100e41c2050b80411200580390300141181044500c1c0e62540b1482c2d0542c0b06050040c1e810000016100040c0400354004104940c0d059175283d802c4d545400e01101c01890600c0d041b04160099030040014501c81c00820407803a0044a04c000420000a092021103145034080207156403211030210000e82c042c13094030644c000c4100000c1c510b2516a494041c640300714003640441070742d074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243993642 1250 243992392 243992407
    0xf0a0b0f0105090f0a0b0306040c1a0c070b2206030614030d0206040204052805011e060c1101030b130b030c033f0c0601230105070f030509030a14060f0708010b 70
    0x117917001040b603884c0180036141380c2d00b810301304207a62150502402d550358400510f082c81c26180c0c102121100343c2403c0182640f81d05020301c000d003d5101c5046446214448000c042c88038840707950140061009440000f8014503043c0b1412802e05030040700d45c8641c108152090507a85c011495075840340e81110005055501d4400c280e285014070304107403140250880003a05c030449164080d90590b04c681c11104140044011501140a4603004001c0016410f114010004200e0359004a014805040200360300b03002102188002c50000b030030501c10b9440c1c501031100c038182840042d640190035009042c0368002d580c440b09242c0c421010f507a4038025240240c0301900440c00e00640c0c40d501c50013400350342d8401d07540080c1d907801080c001c1002e0490881706286035250001e41c405110701060711800d00b000c00b59203d950360251039001c29424013004014181055805002000d0300c544200c41c101015400c540d00149040f000030a02600d102c034030390a0000880e00054a1070444d11540c07166a40c4041d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243994892 1250 243993642 243993661
    0x2120108030309011808091915020a1e02010c0b1e0a020901030c020c1507050304080a1a010b041505030601031d03071106120112050a020616031b030f110f0f0a0b0f0105090f 76
    0x48c0d5401090b10180c008110030b0210317804034543c800b490142a000c1c00b05901c4c00b510317035841c0421110003800b14901d4103011001800b8068002d5211a80d45098800004500041c03111400100c0d1040000380d40001c03202c07c0c035a01841080283c040c5403000b8000b01000c0b2001c40c150280302030904000782d00100300030003000002c00845014140c0c4109513460144549400b44006441480d00c80341410b8481c00861309110a506603021500401c020303010500100741c068440d540040c110f14101a110344040040300c2c00d60121090b0351084000440c0c0c0c0746628100000710040b400890f0b40b184c0010801c14038910080c13501c0e0f030306664166080c42d03c419018030345685003141426000f504042c010030490441c030700d909843c2d1103440c0280c640908422035002240b460101c0d50900a020801141c007024925104c1c60990074020245030032242c03442e007c04849468188158050415035221000780c400302701180a203c0d0700459609640c0e40d0f40e50401d400120b480380000d099003851200b00c0c000a20515 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243996142 1250 243994892 243994939
    0x5061804020706020903120a0503060103090201170903030711071404270503030a0c1701090c0203210730050c0d15030501110a08130201030212010803030901180809 72
    0x8000030000c55852003149060342c081d412411500340f00c0d000702140700c864411070f0011650070b040c042c3d86982c030390f0b51036500550040c210b80c1d4050781080100340400c03000b0100d400303410707000d0b44140c0021916407401d440001c2014810440e280c01507007046504002001c40d5040d00e51640c0f104840c04210b400b00c4142d1200108070030452580032001d4184441c0030301002000450040c01c248c1401d00590040034025190170401030316028113082d816004102d5074a4561042c007946140703106407890321401c003c0d024003840d400b41007810502242c400303001c0180d4101c020411800701c401e520038100c1c40000e15100c01c00e075001e10000145134035480024001c0201c01d00700d43c0c1c4041c00f040c0c10001060700c2104910420520700003100c4540c0b1b0705a00c410365014031030945188103441c3c2d403002a03030f0742d4541042c000000c00380c0c2c013241412f800f44104420388030301040f0729000c1c00002c401582c81e4a400e0b0107007829910300c992040102c00d00d60020b0b40104030544c2c2210804402a078071400c0e240480d03008540d810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243997392 1250 243996142 243996187
    0xa12050c150408060601032901050904021c050f0f0414070510021614131a040207030c050c040207080906030411030d09030308010b04050306070c030522031b050a0506 73
    0x11400411954a1109141c003520640710400100e41042d520311005600701c404065065060000d4840c0d80b124041000c548600c41c002d040c0b4109043c1000100442d00b81c6c0c100443c0010b082e00403c4015100c0300c41403040690040203501304070a1818655140c1c00d1140d40a003018201527544400c40c40075182c20810407000341405001c0098281112100a44410046548000400403c1400a04000f000d0251102c0d20310040c04009000e500c103076100c00900240880303207100c0030f4401c007c518079611031001d010f5960103601d07580022690761400c181040d0200102502c100d10521001000c1340c03119003a2613013050700b904d0b61a1b580d12070741004041500d0080416915100e0b0b6003e6008141d4060391070400c4920079221014103036200d6000c100030b40501c0c0162a0503521900005103450300c50400408518022b06000d481d0003100943e140c1032402d5019440703580000703150308004000e66030200304440101400151045400d0400013041403e5a20500b0320603400418481c42d41d0f014000c0d04141d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243998642 1250 243997392 243997399
    0xe0f1807030803091009020a1205070f030b040b0f070801150c0c031b0605090906061b0a030905090702150612101503060608030f09040f0905062809020a12050c 70
    0x101d60741e16000351654411280415140260021609104464010300d040c03550300403c541c285a04118070203004000540040e0f590b031142410028603010389641803005540605121525860a814010550346005e884c5185480c004c204020706207601130000c078107440406034240301d1076101c0141121180f001c1c0c68003904c4007480b180000304200c8504003125400074600101e07070f4120760303458060780c860080c2628190800b6404001403010b25080009050703500c0c08500015001c0c1c03800700003900d0500c030800218003160907000d05000900e010340d452139103d04039100420743c103080b0400c00500b03481d000d0640b42c000d040420014620010030300c01d0141d01c01c00c584003000281c010000300070b01146a48002d550040ca0300c840425202e102200701c0d14130264941540d4584401a42400000e01040701c40300352503aa81c440001c0080e100f80055401070210f29600c03172481101c903c1808003007400c0d00b99071799600c0c50001686d0050300d600c0000d004884c0408081d42e03408049051840c20119002c003803950 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243999892 1250 243998642 243998653
    0x2030c070506160305061801210c1d060a35010c2109080a0509030307020409060f05010b04050d231501030c0614070f06060302150913060e0f18 63
    0x583c4203c00100004008040e64280b0072510f40e04107111003c80200842e00d03000d009070005102e80580c908549600842e40c00207184400754984480c5c41c11060341c1c0102ea07001081d60401300c001c0741c5040269800c0541115000400c40c80d01d14805030612402c0e200e07805c01c2c81030002d807444422120380e8042113a00c00314002d004802134100c0040400301e00c505603260f0791408008888004516215511650341d000c00520320f0000d100c0410303070301078000380c0712543e151004211060041c0c070780b40500581030b4070030400800d03111030701007070201590f405070055000c0b00428001005203581d6a50400d9000340c01550741600007032814000c04040c07084ca0f002011a100d00001d090b5441d0f40741c84d6072812039005000c0c2d0500039896490440c2c0040f841d2840c02e2442c0018094440401c2d055003071102d02c0b40c4a200c0005407181d0741d034081141007041c100321500d9180c4c041849a1203081906401e100c240200c82c2c104103150034241036171104800a40501080c800f01000100300d0b0189042c001c000d4001d0008556 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244001142 1250 243999892 243999901
    0x3060507210c211e020c07060c15021317010b031b060403080304030c21201e0607020114060604060c021201020d090201030c02060603070b0a02070504020c0a030906090303080a02030c070506 83
    0x6024000301d030a6030300e0103096109010350700740131482078610461092001c0d041c400c1c034080781203460212484d401d43d0144582a10b0b19250000c1d40b009040701c001301e001a2164a01d090001c8203162004040f0f001c95904000140e4140d079408103001035510440d0030150262044a404295180a0303500300805860000052005058114042d83d8030300348944030305144800e00c1031142d0b4002d41c4440031040801d4010a00181d0185010509181000e40e030048481c9202e0110b6081204051064450b1403a00404280148640d081c001e01101c40c0d020310302051981008e501003030841c8101e04c1030000704004034981a0440d40c0c0d01401101c00d9203a2002951250000001e500c010710240c0700c203c0c0030a15181950101c1c03030000c510a0700c200001005054054a482101d1030a030348100480002c5001d00c040c0840c4640d500d1018080d4481c0410080604d400c443c98061302b0080303241c05c90801d03ca4030102c01c200103030b440720f61581c0c008030075400580c480d1900c40c0ca004640c043d0180c018500d01a0743c0411 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244002392 1250 244001142 244001207
    0x90e0105100f1202010c1a0f2502060c030618190506040e10110903070e06040630030513060c0615081203060a0b031003060507210c 58
    0x140981c10281d28100201c2e5200d68100451000348a0b0074000762054000c1c0c40550702440d80615450700a04c0303081000070000044210b08041101c0b116a401c80b80414000d6000130a28014001075940c1c600e40d440c0c460141006e551010300910034818004c00200181c0740ea1607121f9440040002d4000b19840d03424106904511360080c800b4488500f40303000001403e42c90306001d0f55400c1c40c0c0a00c0a4011806000044c0d00a8038940e004401a55020410000075841c1089070b4001000c55942810301030800200b000284c44003940b103118510200c0b0b580080349003484d48108224106881054449100b52a060318180100341190040d4001c00c8c00c0060820b41100ca1a04014428401000f98440c0482010500416809112030a901074001d14203160701100003983c06c0a00107005c03030303402a514a20b4058642c4100c464030440c49040d60100208986801003a801c0070103030510034030251900c81c0c40f6041d80e03c008124139031a40c0b01d90990001c2809451411041c01e40d8a17500c071005804030010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244003642 1250 244002392 244002401
    0x20703050c0105091606050a1701090c030b0d12050307142a0604051902060903010c02010b100807020c040f020d0e1e0102040b1b15090705010905030a0228090e01 71
    0x32440c1c03a508000004e0380d00000840c11030f4030428451424448070b81041001c503207a030810b20046007441045482c010702d2814139403003203008008040001c100502581c0c0300030140c8040300c08490148400345240c20014018002881c00010765243c03003900ca503622030341110b11040401c02c01c0c401100c0020380c155250090810420400410ba003a50710034000c0c00001c3e42d4500c4c044030041c0c180d1b00692416017038a0300042c0c0c1040c42900041c140ca0400d0750020000342110541500780c80544e5481403414202e060102c6032100301500d904085d802c61501c2c44019403640b404000703181c81142d443c803404441d82c60701c0e03041e07482e8500c2454040100070419000e007555a0710f078640c0c08140064200c40c582042c2014000c540035101e039035460780c0c10481a0303030407004401203500c0030744100d00480341c3d002c4600d4183e120051003140c0840041c4942460b240026020300e080d82c0085000350401c464400140e1140307001c500104000c036102a8041200003082c4043e210640c118240c26800c22110071701000d0305400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244004892 1250 244003642 244003657
    0x3072105040c06053604020301080105010905060603091b04060914040b010b04080a020f0f03060705070c0608071b020301060819050105071814060d29032802030f0102070305 76
    0x1203020740c05440310380588403409424000c0341d025285c0d9211040c4188403a6a140c14401c1c1c082580d141442c0002c0000e00340c1e0001d80044d00161f640d070b401044070340b002d0b0040c990040d00541c1c42a02e142028014240c4400c500c101d04200d048002e11030509030f80742c0d54043e000070061900100048071881285240241c003d40d41915424180b81c004100c0006010845040701c0c0088001c0000451aa00f030182c007580c902c2025512103034420611031680c50612590340302d4003c50340d601c0d540340705d98548500c1070822600940308000029003000304d15a0003049010048400c01d0b041400103040d40700007409007205400040c030500464101e00881d50b0407074039030f1170304600c140c5c024070441d900c1d603600b00d48010000316420041c0c0b401550030460108440c07500b00c15028040c101500d02007103d804102510348188030740c2c032084044d86c0b41c40c84c50703840700031b078561040300440141004110800b03410300045448000c1e409404859032031135045690030814602465039079002035494030300d54140036040d900900c0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244006142 1250 244004892 244004903
    0x25030c05040b041710051612060b0f04090f05010f03060504150f021b0606010504030210020c03030403120f14090f01030204051f0f210c200705100c0f080307210504 72
    0x15041400d1780042c0540e42c45800e00e5202090b101e000705e8003c4401c0d410503821080b245540e16030200342d41c032200b00101900720840780c40b10359851400201c0c004898401186e03100003440d110040c8800c0240300c120070100e980001010030300c0d07203407800c210160710110203880300c0070b0b1315142c9030540c0d04405801601003c6109919560140c00090003640c603030340704940b15130015000708010300c014a040744c18000f0313960722031040311a400e102502080c5143d00c59041074441c0c04000da45409401d43c00000180030014600d000308403900d04400920540c0515405c03241b00303040f0321041d801264402d40c181d90041000030000c0c0890600d010f254244030041c1340640d000141404924a11940144160001b0b6900c4440051600314249899001806224601420001148809000b0940400104800c89078440103001c110f85410300b040100200952100244040c0742c4000d0301054002064540c8160032604290f62640e50650072211120b9010f00502299021104982034002e41c0e0b129912840c80359 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244007392 1250 244006142 244006153
    0x110d05010608010515030c040905100f03230309130c02010e010501090204030606080604031b02010309021002060a150f35030c011805250f091425030c05040b0417 71
    0x317811100c054031040390b6502241c9400c1204000d081d507030b98041a801444440310502098441d02842c50306807155005442c40c0d894010b58598020b00a005000003412117402036107811070510100712005403001c0d00094680c2c3c0c5aa142c2c4545000303400000701a4030300c00080016684905403040250454001a20480d1a0250105180c900007072824003c40d01516141ca00d240e43d04450407210800355000c0f41010f44800402c4010b885031904151302c1e00b440e4010b88201d1603e44800c030111401942039a03188200e4040c00c000410304281c00d04251007801c40300300c031000d0100b60031140c20442c04440c1d030001c80040391840f034001004005030000c0c1981c00c00a01038502c0c843e58194401641d202c018009420900380c401588490303a99403a000c3e40c80101c0c1e5071500d03545201306400c246060b0300c1401c0507a03c03407542c1c240020320605c81e25802005052004810341d00000d408448000807606402415a07801240c0802802003040d900142100414030340d4441c0c5501c080c1d51314002d95281c2c1c500d00c2c401d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244008642 1250 244007392 244007419
    0x14011206081515010c02030a141002030a05042607080d0e030c030d0f02090108130311100c270303050c030d0911040507080613021621170f0a110d050106080105 70
    0x5e42c03012601907001002000d80d617030130340c0300d030302803040000340c03441c0c46120f444020001e460060010714450006070b00e001900c3e1500d41040c02d1107103103a00200c0c04000c101102e5544801410007500d241ca41c10500f45a00d8000c01049207000784100d0413a0182403101180310a01d9030b4000006020382c00c0e01510910100b240c0c000007105a008404441d4041104200041c414100d418007840d541402447c0c01001c04002410f41814000d0030001d490000e0785800d4540d05890304120f966241080503c0c00c03000040036030b2840f40c2000007070b0000034100100010912251030042080d1a00042152410808818a0324140c8c1150b2081c0340c07510700039800c1c000081c544901442d202c503c1140c0c05056030085064407500030b8000d40c401030b07000002c4200f2400b50030120341d150312a40481600310300003a8a21035912000b401c01903000341406012000e900c20040c1040c4240ba02d5a00098603150200f00303003034191a00e840b540640c01c001c401440c13420000182d120760241c42c45048440603145024040c3c00b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244009892 1250 244008642 244008647
    0xc01110d0503070f0c2018040803040807051c0206191505190e010906061e050a1d06030a0506010f02070f03020d240912091401120608151501 62
    0x34200d1950040350007400000c0b0142e0007404044162840b40c40c203185203905c1a5a03007401c002081081e4032071140f0a03121100141040300800050300c154049103030302da140560f1603010034803008000410740b01c030204000301084020800506040c0994a69550940f642200296140d00c12650b6103030110641d6451a46944588903c417420a541408000982e04000c10300c00003120341d19250343c00300caa1500004913451b1410b130040c0a40308900700800c071149400001808260180301e90038241034040403600789545c200c4222516201542002c20302180c03004a40d1088003416800141c00c22800010807510214682c4041d200352401d0729203139410102000300b01d0740c4000302e0250031005107036100244090f00d0300300606040280f244150008000340000a151050046100110001d84032500c0c03c04108444900304564180c91801d889201e00c2c1c1034803074003842100300c010b905218040c0040c010b10749817a003240c3d0103030210b86c04030340041544048110140702c00f107075035084481482070301480a62 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244011142 1250 244009892 244009903
    0x90a090515060f04090c0f0306060812090607060f02121603050c27360a09080a050309280507050d080307050c1c030515091006111006080c0111 63
    0x780103058110345844120134880100600c1d04203440303100003030900040c80040ba180101c0518422280403600364901124140307040e2111003110500c000602820199446082c10b98110a40149002c0f0f0b4134074050741c00c90028400c102e0008202180303d0200304590070071482c1042c4510940e07038204815902d00e54001810300801c80e07200e400b40032424003206050442a03059212072001404269001c0106200340c01225036260302d041c0082d040b5461070b030702c003042404982d48000580d5060019045560b62903e4511540c6c6215041c17003000301c00702e08266403c010b03a4004141030000706402d1800b100c21044a070050a5080740c0602c1241404140ca04100882c03094982d07200c1d0a02e802c503194a41c06654940040391040c80c544618004c100c0300301c1100304420381c110955140058103007001900d910303104500c01c2046002d51561804d2044070704107240700c0d02c100e501d1032400190328105010b90741d050990341a0250600743c240340b408a0110030200300101c0a000980f01d03071414175040505162200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244012392 1250 244011142 244011151
    0x4030b0114030a030e100201060e0103050d12050106020a03050c0109061505040c0e0303041406070b33010207090b0f130506030c011e050304060e010c03061404020c061302060405090a090515 83
    0x1100c00c3e4000300d486c2000070441c0380400b030500012800d25103ca0780707028244000d0f032003a185a0f001411002c2d129030042c05451803005441801e001fa0b605144000c0e6680c22040700041c05c100e0000380307a1051303880031340c80445180d922070780601501c56044000c0c14210b15a00076188a42d20b4003030304d05032183c01841581d81c61540070b8003560406103800612501c3da1a403002c62a0802e00030000c0d0300004405400540c866502c0c0b48110341c002040190304d40010f00c2d0348202071030241124544805580e00016100f049800030200413400243d680c020420142003404000c0d0031245e1281c100d01807400790b0f0080c40c441c4c2015412600714403a00401103038a00c2c0714181c40903a00460b011103114242c8504001c0d075005006880c041843c020420102c2d0864016504440000b6511041402403404440c0c1701d040c40c94003100e0650030060314221280c0c40f901f015000742c000d256040c1d80e09085440e540c058400401c001000b4070803528020090f00b02501c1c01030022585e40c007514090040711082101e4482c000e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244013642 1250 244012392 244012397
    0xc050108070e01080a0509070e04120e01051c051906080303010e06010806060f03090102070206070f050d0305090705060304050106080304060504170102071119030c1701050912031f0b04030b0114030a03 88
    0x40c0c0e00d0f0f0317841c400014400a84550880e010b40a4003003042a00c401401d4000c40c41b95801520301c48507010020712806d0444089410800c0420050a4800e801c0032241180c0701428000682c075128514a03001444401c800b14010b28180800051030000c044081c5048070706426000c801c0740c0d038640c01102c8845040384c15a500040c1408812001e1003201c02459120a110000524107010303500091030340e0300f100400b11840b0819208500070000180080d04c07090034107041c180315600380001c9841c0c94201c40e001c3c590017140c2c0400010b05000f000d4000400078003083c400e499680d6120038000b40668480d025001c0d5082d185e810200c100c000520842c1e950f59000100b9a42d034444000410500c00c0d1030a11800030740c0d030454800f00200d200d502e07542d0014034050719142d016244010300d560070740703100030002d40d62508031084d00290703117000d0f40850f40e10030005a20010f001c204040e4000303880000d034001240c055404030f0048104000c20714104d040c0c0e182c0c00300503001596000100340d507403034044500800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244014892 1250 244013642 244013657
    0xf0e030708070f020d0b0108010f0b010905280b03060109060504320901060509040c05030610210606031d012d0e0a062a0c12050c0a0c050108070e01 65
    0x2042201c1c02078011a449032115503c03110ba03a40029020f00300f41042503074110080e500401c2040400d00c90714506440500e0188400c0c01e8200000e0510000d40c4101c0380592910001120f25810f83c007424800e40101c2184010346036210328107450306410840340c0760b0101d003411601141c0c0314014001d40d0304036003150001c0c0029108560040c040c2c07404054803640440b901030800c114a5640d404918003926103550340ca907e07640400100000c0c0e507103644070300c02032000410900c800b980f201c6128907091501810681008402c158440c9220202003840f0008107240c4000403c038207615402150419200015034450038040454040c01ca80401c052901d0042c0070b2000e00000e05035846c3d41070030418500c500080c015001051050600c1080307102124016a10410348840349020b41d00800e180c2141c88040b01c4412001c0405891030800c17141c0a0038100c0c0220306290b0251041007204c40203100c010a550000009140030402070f0224001c05000c10fa0780000540c005102d00d5a075080010141c3d141c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244016142 1250 244014892 244014907
    0xe0c0303030906160e180403030609020f04050d080c030310060215070806040f02160803010518040510020913110a02070905071b080712050301080105010b190513170706030f0e03 78
    0x1201070100c80110000e02c26070a105d0101d694643c844480e01d80f0281a107020603241901e001022558103810411a4a00c140030b06c5102d5510304086d6001d40318261034031010000b4034140034805000c1c0b0f6034006070601c400030810408008040030f200480ba0306800f21013400c5894683d44281d8241120b0500011700c3c941c001400310b1420381c1140da5040555580107260441c1001c608070300d4201e4403000d459200e0000010032031801c00641c40d20131800031603182c407000d040c15542c080d01c1c2e030070040c0c55088441d008103280010b6911b40c100001507414500302004203140458087c1855045945480c01600a60200261110182c090702d032003038051b1b07954449959504e1504403e4440340c00010348de00402401581c0000e44040203c80c603000c041c1d16903a071250314060040d405e6620580107205075032401c0c8201c1500d061112030034600300034681440d0340c45c0c203c4a4000c017500c150982c001000a120b810ba100c22234800440c4240655503999824000c1c803072002844420703035001d01c010320040e9204010a8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244017392 1250 244016142 244016161
    0x1315050402011206060314060d02090c031e040f030f0207030b01060f03021c0615031806020d0f06090506041a060a03020c0708010c0306170a0f02060903070e0a0e0c0303030906 77
    0x59000e4814100b401d286844030692104076903540d00650302107950b079042c00c1030340c0e012030204a13800082121484a0311083c1d50200b08100c1d006401e210f820480407020426400300d9512034800c0400783c04861208c3c1c0f0b49824126049682c9136410303000300707140442c0010081e01c0032400d8420381c0e411000d201100e034a018800c90761900c6c030341c1d00c110405509000d03407001c1010303034500b582a0400181000c04d041c0d09000500c641d8900141c0014103251400745988102e540c00a074007e20242c00c00001a246d0394580741c580c0180c40244e1001029514028002ca03074011150300403401514203960400290344800454801015200d015690241040c85040e000c588241c000f00842c070109010b440586540e14111829900040303240c00c0801d0300c0e80424130103c0003840f10007000e0200c04004040b44481501c641c290b81e0f01c15140039001d810f00003048612034408024500043c44840c524003e1032402882e488010460100d282040d80618526080c49240000699000d182c00b400500310b40e44a02114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244018642 1250 244017392 244017401
    0x906090b09061c06090501060302030d17010605181206150f0a0b0a1701060f0f0905010e011101111314060403120e040b0d060c2a08030c070206040b0a02061315 70
    0xc44404601c07071440c20010744c1500540c100c0f1071141c400420050704502c1007500348203100888408000725900f02181c0303500c40c0c407686811120740e070070a2503450000c42c030039120030410540825042040d1900340c109015002400503c64040a55901003c00180701004880c64806004580c05a4440c4007408040c99040040141c5a200d09000115000004240040c00d500368408408a200b1180380035580e0f81040d00121a81080e241c1901c50f1400d0000107400c0d400b490b0255030401918100d008100d1000f5444201f10300940703050b580e00c8920480f0108082c0c4510300070046000403100820055040c68415281581e92140781c688510060f010102c0d41d000c0d070f244040794482c1d00d03000244030365251108002c920310700034440403428495a10700034081c1c4030140a600f05060b0304400750400701203000c81c54101c4640c080300d190350b280c444044051240c0141007000e584600c2c005800200040b551005155041507502a14580d507201b14008a248921382c4000e08660003500b903421600584e0341c803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244019892 1250 244018642 244018669
    0x2030f09060a0e37080c16052b060f0f0e0d0207180b06030c0904052a0703110f070303081018020c032101061103090a03230a0303060906090b0906 64
    0xc41a4003d000f034a0070b012080c10f20300185d4403034100040760f03410800140030b03402d000b42c8800d5400102514103000301d5000e0841311004c442801c4240c03020088001e510850068040d004901807003040121200000204094541440c1d41d6241003055800900b0114050402250f5a0040c101d003a20303002103850010180481c231448a40e648190440710740d80d40001d036014002a0102070348900d0003a050000300d81000c2c1642c0f50700c10055070158501c000c051005440c00001d200b19540b1070310145016070320500c140a080201d8065110241d24065000590001301c03802135840301001e03281c42807010180049401005800401c2c040e213001d40541035002004070308111011a460452002e0302082101120080304580403050401084410741c07010144008080c14005545007081940001d594403509200080440703083d80d10904200c418401c070101c58050b12015100c82042a140003401081d1a00560b01054600000880c02c111207201e480c000900251200d02203460385420842c1c6c0107010710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244021142 1250 244019892 244019953
    0x3230c09010e0a0b071101091e062106140907080c04050f0a030f06060e06040204080c090a09080f0c060112030c020103050a02040b0c0309040c0e03072702030f09060a0e 74
    0xb000011035103c804018417006024255814246d19070f4000100003104590101c0d886150002800d49640c1020000d4011500039051030000c001004082d4200b800700140e4003034000f8940400020b1003a60041c034040100000c4403880b5055948900a84180c0c50544a00d41e1080c0705110501c120b007401000313402d050000422403a41e259803641d5050000c2192401110002d0b00d07800f0400c40c244900c00c81641007030b4216800d40c01c00341040e401d01e54075a440604280b040c541003010a1140758070358031000a56800c010010b650340080030746004180c3c480c048480742441120000158800300d050881185603160740c85940c40ea08640046002d004003034096001d00c0ea003000001743c29051103004082d0034041c6001b454807401500100700c12590f144500a040c05070400401c51282e40101d40042a40c250302011000000105400e00d001440060100c585610000034084116001c00c0d00520a030328400c1294800c1d59426102c40c00d40d511680d980344c207640060310002d40070a54001e000a002942d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244022392 1250 244021142 244021159
    0x1020f22080718090b090c0307050a2909210705030d08010e180607020d030f0902090612010b04050a090b0601020a0c0603021b100203100f152d03230c09010e 69
    0x580f1340305c1409005884020441c0c0c04815502e109003814009100140811990440c6061030403e044440c25110040400c208542c0301c54103003030041c03880c140d40403c40b02800300500707001e8041c034114429212492000441c80342e00c0001a280c0b4002400300145451a55011403e9203841551171054902518100503c04040c04100017900c08020035441030845030300502c4c10a8100c04080c0440d24492007020100f401c00381c280015807103000d01e1681000d07095410060580180c0138142c01020013128075a4880c0c10b103024400c1c10b20140d044070060360701400d10f80900d900c80d48010f82c0e9440c1004c500411119501d8020085035000b0341c040c081064130041030013075844000d640281003224401200c01000d50100034804243c0002c241600503103505440195802d04000795114980714000e00e074001c120045c4c01140c403803582403951840810302c0c00c05003180d10b120249c01401501c9091540705044805004100f80c0000b43c2c0f140c14020800700c0c070304510b040c20740001150903001c00d0603a29000000c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244023642 1250 244022392 244022411
    0x30402030c10080610020f06040320070603090c090513061a030604081b03031012110409150c0309080d050c0f04080c1e010203030a09030e0301020f22080718 69
    0x1040d04490502c00955140941d034a00300c81002102041044040210340c84035901851280d03001601a41117034040c103080d1703c1000550020b07454241c2c1c09030301103002e0050010018a298041c0c01414903d4851100043c035540c540d011181120400c135007048051022526003c04900c21b03a1108010441142a4450344040f01d004203140c60025102115a0540050f0718a038203000e650307101c903608010700040d515509050032100d480380f00c140507440712580c081c1e043c9010031015100050b40414058014001c40c8440d00304003040340c0750030000080823800c0218035020580b0a10501c2c1980381d0041c00d542c203145520645030b00605008040c0c502c5000c08005560010f6542c1024100030000e1000a01340301c2d200300213120400c51125407440103010201154405031ba0048280c03944503035040340000b5a0101800c0440c3c035103604000e10342d05544001031082c14145c03000020203849014810403d0101c10004c003060060640b0711070441d680c1c202d05010b104045801034030f056440c40d071480c085210045c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244024892 1250 244023642 244023649
    0x14030c07030305070c140a0e0a020d06030f050609030f160809030105090304060f1e030f0b0613140f030c09130503030f040317010b030612070317070209010e010515030402030c 77
    0x601e40080d008564007107540400c02002a6050b0050b10038164845001c0c0034040c0406c6040c130700c038001c400000e45c41314006680b0144660681d172820503000c00601400341d59003424106031845190648090140e640000c50f04480007040f00c0c540f07030076256071030300d40504c0302d241c5180002280ba088a07801420002e0450b01d581c01d002d09801580240e000e15501c0d803500a003d021200c500c0c1c85082804418001004010360320700c0e291880e881036080c003084140354001d60b00010300c8074540c0e082d8804004500c1c04904010010008299803503a0a00203140b1080c00402c400300035030300c2ea0a64164006030070400a424941540cd412080791110401e4072044c1d42c2e2024255001103d84a005501a9041000b85030f0301403048604508811401d0f02c06504160319402240300042417103000d146440b0003400d600c001000420000d41e040480004075200c4510100020350104a017a8424119403002250205a00c0c01746030490703038018031003070030b1042c1c020403200c8a4000410176a81405580c070700d281580c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244026142 1250 244024892 244024903
    0xc03040f170f06040b220b0c040611030708041401021002180f011107060807051c0501050108090f0c041109130509160302180a020f040b0405040b0909060414030c 71
    0x5000001c001c000e03294032481c54941403011030031262a034401c00900002c5500d42c52413a801c401c182040440200391126020049903000d40c004001d1081075003007280c44503151001d4030070741d0200d82d40d0441e21000f089502c6d58030b025462024064000070071003080f00d00b070b103c0c1352070803040c1040c01500c5110300312256007822600000212486d81d403c520200010386000c100c1d400c0f400509081002542c0690003800359176602502444060280c0d040c01702d030300386000e5019a401413104203807034140d40b81c0e41040e000103803600b07128a134013041c04140811008030000c0ac17009031110308600207040c80a20714003088081c141a41c1480c0c4180010090300546071034002100c0e1080d07682182c003190b9030400004591804c0300c200d011120036061140180016078906c40c0440711100c0c0507191105da51601801c49000b4441c40d005980300550008001840300ca09001400865500704ca0030440c034961401488800b40c0202c402810341e400c1007000030005514588021960303141d14040340d04000e0318039501803600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244027392 1250 244026142 244026149
    0x6010b0a020715090e0115230f0a030605031203040b0403050a03180302340e04020f040510061107180e01060b040f0905060307080c010518031902040c0314010501050c03040f 76
    0x605044030900a42619890350350050440320307003011044411202c0180122280d0681010710b0900022010708c40f0080d5003034680c000051601c0c56582d88607181c1c003a004000358440d8601901524041130140140760003030f40c0c4119009800d4400e645c0c2c641c0d40443d9181d1041d0080024540d4400c000a107290141d40160f0000307100c5e400074031111400300b035803a40007905080c0d004581511111208001c0b602aa2858205c413415000e034455a125440001c104100011213690030510b0041041000c03003a9400d1001110354031380b201c0d100b9029108845499011178002e103100118600ca1000101d04c00e40c1c000d01040400c0000002c5098031580300c1c8903964070552102d001c0b4503509100380040c02030f41c880d05820040840081000604d015005619444010417081c18840e010600110740c00e43e52541c140003a100034155481c8400c80c1006400d203c00c50002a4051880c0040c4200494008e10a51003c4540c415803030906a20304401118560306c41000d01312180414000003e600551408480c0038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244028642 1250 244027392 244027397
    0x1017010603060611060405100c030b0d1a011a040312050c0f100e0312060103020304210302120c0a1709011d0a110d030819061508071209020306010b0a020715 69
    0x8610f041e10007030544442c0f40d5843c8050b0031070b0091000280b00001d490a01c2d181410002c10314000d001e50a4005104040403580c00c100170500d898204001c07880d07151104d05170010494030703691322408007255886808410798080d0008000c06d1001c10407850007030021004501d04940340c90504204541450386d0340783e03526241e503c200c0801d4510019400794544c1c0c1c03142c8130001d504000c0144045020200c0c050000c034181913001010500741b101191060401c00d9200d2600c0800d110b4200f0020021744c4010500f070040045400440e0303000305400120780031f8400f83c0ea00d60401c015100740c0741d240c620b0081c0501d0031643d80d824407003c02201b514045040104140701815030000141080d1510100c0a0340ca20f03c520b25110130b402c000b0781c1007600d0640183d0b5003006c0d2004560340035090002805a50000701030b4490009482540a6014002c03500c581115500c070864a03034002071240a07a01d040100a40c5a00200c006110042c0b415000c0c183c598554030454140b180d0320f9540c103080028a0080100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244029892 1250 244028642 244028651
    0xe060d0b120706030c0203160611090303040b03040606090506061b0c030a0605041a040803070f0c0c080c0a090b01021b042309060708070f050a020a0503180405060303181017010603 79
    0x6406100e4503007070055a0001d9460440c0f4003044065103146441d000707162964417800c0c4021800242c0540c1c2c920be1018045030350b01c0352120400413891f0011101161030a0500c08007141e000c040307000341c5000b2040500040d05001c40311018008241070031003141da241c0f06650f08803460744d80c1000500449801540001303410309113424211b082440501c103c1e8040c2c4592030034000040c2000c81102c0e0700000e18901032003604140c8000b00e51000001c40b001c2e010030241c0130003284581001c10950b02402046038410301040c0d075110076038240c038511040340703000da04284001c640703e0240791300080800d203005000088101802d900a1454601d0001c140000d410090030800301002c1044103903041881e90034641c809242c500c1d001001e41100141c0710381003002c0415213121440c02086100c0c009540042600d03110314110560b0042520505003003807150f41440c010484070705004c800c5450084509a200c1008100401440a080c00714101c2104004101901c48040641d151810f03000c1c1189039408078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244031142 1250 244029892 244029899
    0x408220f03062013180c020c120f0102040b09130903120209060c060108061e04050d0f0309060615090621020715060b0316030506010e0108090c0a1212050a0e060d0b1207 74
    0xc540c003403c040041185850024600421b81d000955034900d6101215801c0c160340078140d00c1800c000981200380059800030901040d00400070002c1c2a660345c081d2840707000d8243d00004803055680c404030150104041c422041c1141486400815140380003408003440d0810b403119282c0b41ca00c0c01d0340301039a0b9412040501000018000f19110300d8480e059501c1ca440c1800c1c0c07541030315170000d0f0344d2450a1004664040c03207007600a4010250064009900304101c540d20904400191041c0244d18006036418a0108a450003a1144c1d420034103004120448090b140d500c000c000d5000340710541f01d1100344081000780210034007404026280074041e0a403681440b12604103468001040a41854144002c01115903882031907840095424603103e00103480c1c0c506a80d041c84001c03a0b880c0e400503100c16001c0348a80c0310580c94044d041c881e50640c2e00e0900010700c11501da001c1d00c155000098a4541c403080b1310301c1c207440505030b00821002d0004002f102040007584588412010308010b42000c0c2040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244032392 1250 244031142 244031159
    0x10216030b1f0b040e06040b031b010e010906020705040506030a020312070b0a02030103020105030a0903030e010c020c1002010c090b130f1404110405010f03050a140408220f03062013 80
    0x6400c02c240152564040606001416903d4003841c000c0340c805c0d820703039030000340039503241e40000200c400050251102d00c0c080c071080c4603480c1e03032420400740421003070443d80d1515441100140c003250400c3d8040d2403813600702002c04c4084d00c005403406d0380c54031450b824880960f0b4180300301005491282c1915985e5110740c038184d42104001407108880354814001080541d801c901100ea0044694a0006040d000381c03405a00414510443e219039600c0c1c40107031401c0c5034000980c0c4074a820100d61aa50030040000100d0985410032028000101140300800c8130801020290940020b021403450940f0744030300007403060240645c02013000a01d591451205428284140c1071100720002415280906101c0040e1560a8620710002015990740006003007500c694082c9941c0c1c00310000300240c1d82000c1c18980f100750000008024030740702c868070701020480800c96500445262080341b051051454540b04020702501c4440500c0c4e0000c0340711010340800303400040c0035040030718011005103814031003003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244033642 1250 244032392 244032421
    0x1b0408030d20030c1b030c0705150304050a080a050d020a0f1704120e130c0c03020607020601030c03080307030b1003150b090d0602031b0310171501090b010216030b 72
    0x101c001c5030a5482c400192078102500f1694403003907400701c1caa07982d080d84480704003403405c0b02c8481c034950101041890a00c10081041403ca0310301325420100b1120790544c00106110680e00240254030084038940069202c40181840000710700307100f41030060403100075041c0d9100d040303035800085ca502040d1070000c1e044058030f00c5641d919440b071126441c0582c0c41c80c2803942101e000200b40100707015408039070f40d100c00c0401400c002c048000d0200c03892210300501480c0b944401200036020b400e0000e4107007480000d000f4100d903000051002194030b140c0310310751243d00c0941000201516a0b60803040c54031213840541c0360305065034001541e0350b9500f00000c03882d440ba8000030241c00082000481e40d58a02d00507001c0d107504450b0040c2d481e03c2d107010520b008100030b4646000c0c00c8011080280301044200044115410403c030f0070000c060342e0042c2512040b130b95800001c8090300b03000521844030254840143d04030180100c0f580300203100260307890b40c8881d60040780c00d19081d030100316a1003c0c2018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244034892 1250 244033642 244033661
    0x31e0c0807110a030801140a03050102070507030b090a050601050103090221060609010603020a1d03011b050306150a170720160504020c0a06110702090108030d060602030306030d081b0408030d 84
    0x41c02c08160703260340081c018017044c424080d900940c54000e44080d80e40d0413a034401036602600840d903441d02450101e03241c006602c1f081e1101c580d544001402100c0100d000b1260340e034410040d05170790382450010b400030a60403409176040f152000200301c10751400303400341102039a440020982840e12a00300144c260058101c01c0805005000080d01c640d0006200250304c0c00c5400500209070000f4086401172000c0c00c05200790710541030381c5810740f0703401000035401454182c0306008014940074540d11507200300069031000030741d101003074006200c00001d03058029000380343c4111241111418694400006a010009900224100f4030078003407079007200008090079681541021070b0205a2503d03940049030161003240c5070318034042d602100408492900b40d00900c001442c4d40c40c0d82c00c49030b9039044088030012161600c031020132071900004c03d9a200c2c0c0701c010001c26003500d0385002214214030181c2181c4821201682801e0b4120502000e0400782140d6001140c56040c00e84001381650003014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244036142 1250 244034892 244034927
    0xb0106030917091e03150c0301140f06120a0e060c0c0c0901031e1b060e011d090c0903010209130504050610080d0f1b050f100b03030901031e0c0807 65
    0xe983d40c0c42d207503041c440030380124902d0210310910141000c64103143c44c20001c80c1641141c601006a14076a0901550688070079100348044143d540c410f0046080a0540d000e620540511400d44a42804000c00354000034109000c10815466440c25140039026140d24451540204001c000940c04000780742103074100700c8460310a54034644030714014034490703000c0e451203641412044042c8040407181603900c004000e1511103065030740d10010645c268900e06640010548640c42c0c06e90404030302c81e5000300100400090603034403a4002e40355950b00c0215195095502408000c089954802031011812014580410589032030302d400e03801c02200070500014503400d4001072000a030001a050080410b0b800c200640c2611910255120254004002201c99114103410b0411070301003007140b4040500421110614018590f0009548141100640590090000d411030b50300c02e4012a00386c04081100c41082c440c591218029200042040004105190180a1000d5016950390041b01219 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244037392 1250 244036142 244036147
    0x9090405010b040b19090c0507050f03130e1b160629181504061e080105010603090201020307021306031a040519052d16080601060f020619090b0106030917 68
    0xb028050445e215500078070307030300550351005580c1c000c1c015022a00c0d01904a8111500003801c90312056580c3c0c0000806035560050200005c0e00c1031482181c0c2d8040c51214081c00c0e0307105000218614980c200100c00f02025960300030759004901103200b140d1991184c226601c80040c08494004621b00d01052006d00525041c0341d6403054210307841815810403402d4a42c424080c4042c4005805444d00350002c000701407000d150003060448100401082365100d8000b8000caa0743c46000b5008c0b1426600c010340544c00400400c001403402d50605140c40c8118540000c0003a140d8554011410741260007101815440c018441802010000c0c036070190100000012092490380c0c2d801e44818481e40a003040f0060038201031100d122201209a002c0c1900c0101d405007200b011014220082d54419640310740580c0740045080c9218207599000300459800810700d0f83c580c503002d0350508988036504040d095481c81c0300400030794401200c0707000b0213856030085003030812820105050320101d028040c590b1002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244038642 1250 244037392 244037419
    0xe03030606041701020702040f0c02160b0904050a1407051804060302180403020a02090c070c0510080f09010e1b10080609071b02060a080f100b1207030209090405010b040b 75
    0x2008210b40549030b01c0d040400000482905950181c01901e100035803050800706009400d03141a0b010215030a0b095084564030105c25a1aa201a40e01e0040c851510020425110582003d4100c0d03034000e010044000780c1104196015005801c080e241c5800051001811110b640212921200000c004440030031585296500095030746800034002018510aa400942818001d00c0151300d0705030081c0141c3e50340c2c607103802c070300415500051040301c010140d2840402d50342080e03070003d610250f145d01c44107026180c103c192070044d0001002c60b20ba41d922070061010600b414050020304950b2003550080458440f42008040728882d1341e01c50070020320804024007035a80c1055660880300e9070401040c6801d0803184540030600c0614065000980001c0c110412a8050760403407042e411030300508640d4551100e0f40030110007604c120039045109001c000182c180c040141e0360003030100c0c10018508040390b004500791035411141618980d5441c0d0b42c450035030409004078080700710f080700c01c403c0e03034287c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244039892 1250 244038642 244038649
    0x812090306160503040326190f0b030318030712060606091e0902030c160803180f0604030318051608011506080c22080105071209050a0b07051306020c03010e030306 72
    0x1c0020341040035140d0440b00500c034640880581c01c0a003075040c15940781c0040d0074182c0f4481c1c588c0003181c80e40b4088100c2495034035807265500c0f6501c02800b55203416204900010740380662000740b03615006020300002c1048800c0e10303c1d04458810342002c21802e2030442d010f451049250702c9910000040d400c20b44440300c100c0300010903a01c170030700010b0300e0b6141d180d41e203002402000f0494560020510248040c40008000b03507200f25002c40c5405040c403601461603858200550f2440d4540c2d00c40c90105000a01030780224a0a100b15420711848030b01c25165280b80c012410030798070200d10148814010444207020344800d4030182e05000c40480e2401000a02e003103c01840000414000301d44800d44103d000240c40070500c520a0b9400303041e48030004035000b054185e8142d00450b1403c00880c1c03001e43c4900480301c0f9150010b0140030f80c00f90a8031240c07406800105001c0410404202d9103079410720409000d005404c080d0700602042c45260241401c50740b20282c04102c6500500c10082ca556 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244041142 1250 244039892 244039897
    0x5030a050714040b04170703171810050712140f090613380a0c0302010902100207031106182b0f110a05030c10020708120903061605 58
    0x91204001a450750307801000c4805900440200c1d9002a001800007042202c0310043c0041d954090f21032280d51901c0320407a82c5c0e0302103920000781100d00c0e241c0c45444091801c0060305031200810075a01400b40680c00040c15a020112100b006c240301103006414895203a182e0a940e0781b003410502c010140c0030314400c1e0140102c82c0c51840740300000500803503689481050300e10103602643c0c22200039032161444040194100c0001c01c00d10104cc0d00c003039114100c4148548031034000f1111914041d00c0300421903101c502d442082d8103542d21151030030010384a00194a8003440301340d0240400b45d0031443c1181c000d9401c440924440e030802d02c000710f100c031040042c002e5544c030221000340401e540c9034500300b11455680320724011240e10920050521401c032107a0100188140d4181a05100789001c100804815015a94041e806100450a6410819450341c421f05081c01118441695001e00514140480681c0220b51502081e04030690804100032500000c2000e40610074410b0702400074242d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244042392 1250 244041142 244041151
    0x2103090b0604020a020c09010602011b03020405010c0611090901080102030106020705060c1b0a030f03092c010302010e19030503070b0c0301030f0305070f082d0f1c1118030106150503 80
    0x215030014000380a036008011074100446d018003103400300d40e034815001e4020b010010400620805520f585880144284215404d448058451040140207621518010910151106907003042040345d0100d03135039200c2d013043c028283c050002d40c0c0c0f981400002810b01c041580300340e0140c2000e01a61940c1d401c085880c1e001045244c0d858840c1c0d1181c20001050204a0360014002d011540c500009040e804000e0105071111001c88444281c464241c07013900380c601f1500c1c041e001c080540148011340c8603c010301c64591000b405594070700f46580850b0b842450315031040b211541b0000e541010007000b094025807000c000301071b803810b640c0b542d00d41d04050b151816005040001c0041d4140030448680c02624415402003202500d90348083c480c40f101e0301100086841000c81d03690b40840303051840003203540001200c16100d0400c00d02c00f10002c000c40a4940c44000d0580b1001a100c0030550000034101280c1144007580c0e040400c40149401c48200da00560b00030141d20301c0b802004c40e0004212500f1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244043642 1250 244042392 244042399
    0x110f0403060b0123040501091d0f060109050a0e0105090105011b030503060613060c050705042702031203070503070311070c14280e092805030d092103090b06 69
    0xc507014000121600424801c000741c00b202c00303c0d041c3d070007161400090000d440087c0c88d40500c60340c0b40c6540000414a8a4811009081000c00510041701c0c000c1c22580002c0c060404400d0192690002a1060341e69081f10000d141101d0042005241011405004200c00e0800901c82191804032000b0310000d14400f038180040000890039075201e440486002013280381c0c01c041c040d13466800c010300c3e10041030b40c1500c2c107128001d80459140f80510901d860f0b80c03544049582c00800725920344440c49001c08003664540200c1400340090914a402103100e410650346143d079900d0108400f5046411061081d80f0191041c00340c0c44c0010805c030465015159116900c1206d259120002191081c009010b50350041d121840c15003a1900441100e0a641d516287e1145e240d0f99020341c1640c605170241800300c903a20317400000040c80c1003841c04400d848c1c02102920f1419038187e40100642d9001a01215010110744c9620403422101d20860203440781850203100080700d03500e40440d46040500814071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244044892 1250 244043642 244043651
    0x309030f030405161403100b2d030a061b030207020102030d0203150a0303050307030b0913020910030b0c1305040209090c13032103060611030a08040c1710110f040306 73
    0x14890b0812810288110050304013020b035860b03003500108082081296406403040300b07031800c02c0c280c440c06002d00c0400003401c1030559410200804003104150751081907040345c0052051000d4400307200d50100f041c010480840d604804030403020401c403440e9048400c2600c14000d20006030707030200c11581c521840400140c0c803500e54540c40c00c41e44000d400340c40e038090a050300000801d5045000b640c4580266101002206184814491045400c659800e40c10111590400040c0b0340700034000d410200360150700720181e8403075030303004980c1e081a01c0d98902c07004040b880d840e4102e05441ca140240c0429a015420b0401c81c00c003060b030b401ca010305103291005001c1030a403544205921188000c681283e0800344200e000c0b1658081a00101806e000203405c000300030a165004a42c1c82040c030b100e50009624181d282d0030201c3d07042c80027a2003255143e0146d82c000030122824001d6244041c924806001c1c504c80034404c0c20110340150045c64240354040c441e0711603660a80d01a21b0132250040004035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244046142 1250 244044892 244044901
    0x1062705101706040204032d0b04141608030d050903270a0801060f03061512050c10180909080c07180c090b0a050a0c0c0b1e0309030f03 60
    0x15400101604041d40122840900151142e40015500d0040d42849440c0700a52643d2041c08264490b50001070f101e6200c01e203200090841002d10001132000e4000d84402025180d42c1d81c0c0092401070b00c00366200d5402d04143c49600d0010b02100e05241c0300d4503680d42a203450074141c0380d10790040c0075030002c3c0306503960000750020350180700307c59516106004410342c0b241100740100c884030315400c0075030160b0082040400d800e14144524410343d805031559640092031991400050400c800c1090000f141c4010001112410302c900130069038855000b40c08034103102014001d80c8858000300c0420055002003601e2109038545940c1c058809804021942240c3e505007040d40340b08011145200d4403440000040c03a601003000520303d021680001c7c040300221020440e02d40703e4602440e040b0200c204451480940154000c3c003541c40303542422154503405491702c0c0e40e0151280e12032030ba43c03000084c21401d0150340c807111120501d9400c0e007090a40c00e098000c180d5038069046a42c05560001000c103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244047392 1250 244046142 244046207
    0x8040504021903060815390418020702030601030f110303130608090105102c15030d020606060a0818011122081002070c0b0f0415051c0b010c050a05030c06010e0106 72
    0x8820040a40d0382014003010410303440401f5620030b101d050360b43c080c14006450a01181d00071184000d80007070003000d80b0390031a203400b007140040d000d003200c601a2201440655407010320250041c00400048880706901d03042003c0c04101006014501c00c0e4505400c20003e08458404901607a0103e40e440000c0790040c0d580d40091844072a030f104180459078208070400300c54040301340346000160140c0e0402c004400c005e99655005a4032035034400c805101003201c082c440d410840e4006980c0000880300000c4c0c900c414219144081e00f4200303270b42c00040400840c0d2410a843c2007484030044001c1d102c52411050b29185c404059200701c1c2a0340014a80c0c080c8100003507000060680070850350798a50300c003405590103a102d4407400301541d400c0f0340614041030046060301c00581042c07a038002640c0081c40c480c2d00a100111865060106014003000456000c000303458804c0c1c80740d8011a904c18031002c10030310701201603019040c440b0351a401409010307482074401d0103a90800307400d068202040400c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244048642 1250 244047392 244047451
    0xb0105070b010311010f170112030903020d060f05060d020d0206030a1409070f060302041401110f0d08010306060b0306030307060e01060b070f0c060503070507080708040504021903060815 82
    0x752140a904001200740905101951a10542600d81d880000440c2c030040c0c84d030031266612040390481401c010084428241e1244c03030390390301c0317403421100441e16540040c4082c001d4450940d2480c0d0f442a48281c4140e0318850316400901c100ca0360440b013031981c0d0000e0700d80c41c2e407054000c1c05882c2c080046a10b0300c100e50001040c0100c92160220070713280036880d055403881745224843d52042081c0000031401d00034800c84096554041034810078021000040d0303140306e880c00f410310551080000840c1062018058240d400c8501daa460605516605100081d00d116400900040c10204240440e0f542c000088600e00f50340030002103400c810703280c4072600408140e4441d0540e5100000d01d40e08103d40100700810300340c420740314050455191502240ca03400201c0304030001c90300400c40400440e80040142448030b208140052802c2d40b1000468107980280c1c030307000e12046040002c0c03c0c42c01c0d0140078020203084c07010003e09050b0040c00c402d074010340004d4134040e01d0348204e0a00700122012810b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244049892 1250 244048642 244048657
    0xb03390409050712110f0109060e01020a061109010306090c0801061805030601090b0420030123190e0a1a0f0102190818030a171308010e0a0210080405100b0105 70
    0x20f035810b40741d0b16001c0c60040c02131010100d907441aa01c0203219245003d1100d41041001a91040c00807818002d003a50403c10b02c0c0241c90643c842d040909000599034001c0851103480108841d4543c010540050180c8806802440825040615a02e4240c5c0e2040c10f2a045545526007103250340d0040b013202480f50f00070b0300195010301404002040b21540da80100e449030328141e07402c11480301c07a0100360140c0b000d0030240030301800b810001084a0480c5020701c1074a6100140303102200078481c4001003c9000300d048500c0340503051082003182c1c08912103115880910803005100425140b18229403840313034010654891803075a074103441580d1081000d40355585610003514000c003581d0504242d030f40c100e50b11101c84007000501108040c01c0100300944102c1d40300540c0c0c1c600403482010f070070344c1740c110241c4050515005100085c42034405d00030138911022000c060a800b0000f80140819003100030a107009000b80b420a1000040000903d00b8201c280748000044100d0054012200742c460580c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244051142 1250 244049892 244049903
    0x803030c0708120a020310080a021011010216050a030f05120103060c09090c030b101b080c011104030b0405061b090f01090f0e0a0c0e1311120a0b03390409 68
    0x104103a0504c0d03580258024094400940d81d500e541e00c1034169079030f03250100250000d0340c1c800e0040e01a0f024210750140700d41e03002d00142c01c0c48001d08405200347d400280a40359035001403030351001d0503000a00541e0b244114503205240540c400104003000b0b82c10303c0004d00b1a5030350b0106c5170410784189511006000d0152042c002090568401009484002042485081d004032440303040c070b004114030240380b51904142d0135000c00a450b1107026402c040c00c814419504ea043c0d0010300207840000b803000c0d604c90b40c02280c103418542405032504800800700703051001e00d280c0c84003070300c580c0e44151028030404841c01d00400d002c600040b6020304803640448031180805170003107a03003401002c2c014032030000312a080103d4010300708203c50307452683c41c0e030980140c00b0240d400040140754000800201d039800b0306520707203440c8603008900100200c9090016913a01d0f00c0280c0c49180601c612010041c3c3c4284a90600007010782d0004020811030410f140801901d101038225103c3c1c0d00208007950708003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244052392 1250 244051142 244051177
    0x1401140901090c0f0f05120f01090510060807061e030f2d020f040b0708270102160b03190e010c02030a02120301030f03050a03020c100b0f01090803030c0708 69
    0x6200d14003908440034101e85400c1201c101040c0d42c00480300d0762088807241801900c40034544800c1c058586032403804805140242005040094002d000f4051081c2c8154020607100d1500c8015030112035107901f28807402d03040143d04003e8181c0c0040c1007100d2083e1ba82031921400c480b910b040d0000d000407000c8181217414059542c02c850340860112910482150340c0d201c2008000900c9803ca10810f04440c0d00d6460510007440b001014030b0160419a1017251000c0c030b003001c08601004d440e03406032900240001107000210083d40c1c103003e10300c89801c01503070442e4030a0500e8034480c1980001032540005078980c41c4450b80340007032500480001e09140e002048400d00c07002000b5200c1e07002840304009032080c07901100c121020711048a040340d03000007541d00e00140f280d0741110a030303220044050400d0303001d2002030740007141809a6440b41c1501100080c100c10214140700d00510040945414841840c90801101c0d03008800c40390321005543c00655108128a40031425000b45402500b20100c207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244053642 1250 244052392 244052401
    0xb0a12021e0a110303090601030f05150a0b0a0902070b071b021206090705010c0305090402130e0f06040b010203070f1b030c0303120b0a0305031e1c1a010c050a140114 73
    0x35000a004000140d982c03482460600c3d07112564a00c020f1314004000d0b4000f60041012a580030711013098288900c2c1914803500d00b10000b5200000d0030340b02154403507540e1059100d00d00c0c2c841c86038030042c200b101080d4180f107002c6c0c6840a1408006000c0f20600c41100c603120b12002c1800c3e540e501240d4010300201c18040003405080c1c2d40c800481d1307210703464802c244000c41c0c190302030042c510240d0360544e219454a002d800511010b5082140304c0c0041c10440d01d80400c160040d09a514464060442401520300d061410070058800c032000d040e06541041151001184582d0002c0740c031242c01c03100302c0100420003000c0080d803c205510140000c0f071903031008800c050744188040032a40c40007406000c0e110303100c0e0420502c80031510008040ea8802c000b4058044c26141e03403040034140c2414040d061600a01c3c840450644500070659450303950058481c6c05003000c0c020480c065820328181c0e1410640b5600c40e561074507440009885c580c842c01c01c01a031100c0035000030032032048110489046051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244054892 1250 244053642 244053697
    0x906020706050108190312021201170714010903060e0c09040b070e03031215010c02130c02150c030403080c0c030a030603020909010903020705040b060c01021617040b0a1202 76
    0x105100321070040c10b000000929103c002820f92085980c0a5400224803240e80c06071410756801c154109202e80074030030b2480310400390030f50900900e6920344c24998400720302203071410801d06801001d890f42500002d001d9590380074149009596010500041c0c54801040080c58850030450244c0d01841030010041000f401d001700f18080d01494980e500c8030307030ba0300d0304140e102d0080381c1400c20710207030301800100380c203c05004180d602c40040c141040d0121560f00800c0b80d01c40c02048030303c2080e444a58451180ea81000354581d40000340031401d0fa21b0818680003e0b484c8009040601000604c80c04198079000d070710120b0342c03580d0300b803c00c40e0f64541d442c10000d8058980b510040e4030441692001841081040c09489801c3d40e059014210305030500007008002c11841d070000b17401c80d42c107006860341c1003c24070007028a0014552010b04911242c84e002c100102c405a440c090583d00f400100541d1a21005950041d01541801c00a0380a01e42d03010009008858000b03841c2008003080c1c802110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244056142 1250 244054892 244054897
    0x7090903030e15070c06050402010c0512031b04030f03230309060f220b100803070602190c0b010317070803101403070302090c130e01061d0f030a200301090602 70
    0x31141d9042c0c079800d103078092035400590f000300c9480c40810300d00050000050403541c01180e1041c4141401c00412006890307061a180704240c0c000c0c0c40030303000402c0c0000c54004002040000c804540c00350324090859036484401c1e09000c1d0024140060750341200108035410441c3d08800100101d0661240780c414902541e0700425a031004040c440e9030b003c68044410308844e046121307820070844520381c05560b035080d03208500601215040e0880300b070202d40344406100409006000310070141c2c0380d8400c100184000d000ca240c02c0400d004001f000240010341240416045980040c40c200b41d1130803000590000d881203ca00900c1144008100802c82caa840710113402d8680c98400e8148644000c410b050b0b03a0001400041e6001c40000c001407113000140d4020b150112004241c5a070f807a58580c02104a40020b03000030001c1104c124500784401801d5841d0715074844120381d211101c032443c10100340c4410034044040c02040c1c250840306042c1e00d0540c80201038020140080140a0075414450001d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244057392 1250 244056142 244056161
    0x3051917100302010e0409240609021209010e070e0a020f13080d090b03010b0f030a0e010e151f061b05100603110f3d0c0b1807090209030709090303 65
    0xc012000c007503c1c80c01d151203401501fa41c810342c1f00340d00342d2800c440444070150a0036903148541e101c40c0c02081010060014110354035070442400e1590914192560964150014800003030b406040b0401100900781c8035207410082d100c100503030703d10301054081d84510a00180b09009403a41c540000c200c00000b8514550804540e2807180a54550b010100d692000303101e5954156000c0c004074025203000c0c0011604401c44420000790203990461403420b50301407228101248e0071884d804110080e40e00718156100d07030f10743c10912420b03001c9054003e08481034091041009484180702c010412503a000315103e580100464150030480e0442001406050000f114941c20500200d002801c101c043c202e600d600081080704070140f180825085000d00d030303599034188030b1501a201140d00440700e244c1070219072a52001180380c00c0781404820510042e004160701002e102c000d16081001191003029121201005a50703104660002031824150f5004042841e140c240c3ca0800c00d131f0903034000d1408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244058642 1250 244057392 244057397
    0x30b0a06080405011b02100c0e04090804061b03230d0f0c0906050f09040917070c051c050a08030603150a020a021c05030406050414030d0c09120305191710030201 71
    0xc176651110021121100060b0f0103025a0211203140c41c001d64941002c4440407451502c0300c11a03550b40002016a9420241500c1d0a40001030500c801580010072440f0807003066a500e155000950f03004041c070411001503400b10000905202c90100148103d03148000c06400a102e1036500c104004014011101490080780130823400040141c00744042c0c0300002036844550741055541020b10005e405800403c80302c014581e022040c10100c6040076113407840c02045c082039064180007e02443c260301010404682c958901020001600026010341140c0d100310f2040e1680c1b07440f40444d140c83c02034a00400101c1c40c500821041da4025405800383c1902d980c00c480280098400078010070b00310310b101100051003000000c0c041507180e0405900a4403501010090a1080e10207504541045c0f40d06845161500c0e1003104590f405803008024090880b00310101603d2541c0c0a407051003521181c1c414443c0008a100030030340100c01c41d807140e483e030703034107081c890303d8040140e942201322070104901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244059892 1250 244058642 244058651
    0x61315060902180f0d0807060209040e0a0b04020a1406030412030e010c02010b090a0e0607030902010e150a030e03031e100306090f05071a0d0f0e07120c0504110306010f030b0a0608040501 82
    0x382c5400701c500c91040f43c014106c107107000e04a03155031000e50b010b00034140c0c201d80c031440890406241001084e5005000e09401c1c2c0381400c01e441081009400e580c080d01c18003c90030b0301a400c51303840604498205a000020300e20503420060103501a140030400304000e5468144844210303a0190403034000c4010071541040b480d40c42d101000100c50200b040c032810f0380c0c40000001c6d45d19000e0b0740212169801418101480c02c01000011550310b420b01d400d40310340002058405450390580104010030758075101842c11441c0c0440d460000d82c1000506c206154040c1020a2180c1c0300c4070800805550007410500890071a400c0074550340d800070b03c0c2129940701d84100002d000c0d521021017401c050030007a4003442e101081c1a10005400420b0140901582da04405a10900300300310103002840114003840e4010b074142004860311245034043c6010341e09241d00c5400c2880007070116584a082420300d5616603a80c400100d0050681a01c0c040d001040d46d10007040d4641c000c070989200f140708200a20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244061142 1250 244059892 244059919
    0x20102150907080f0a03020d0f0c02060304030e10020109030f140f0708030402150a0c0308070315090e10060e041407090204060203030f011d0403110c0405010b0405040b0306131506090218 82
    0x5030f1710010f910000d030050304040d0b402890356209031244401c5140c0b07882d00b03001405603078001456541c01501c2c05c03804101000701e410014107204081000c1000140000c1000c0d1605450140030b2505001201042080a42c6401d189000c07801c1980e441011040d0b0441d09c94680313207801c205584c001c0d1010b134440d042c2c6c09003021340039401c00211602c0c0d800564071829224895901078804c1c0c44090040001c0c1600c1c1c1c007030880c001c4040e1001000801100c500441c800c080030b8074a904046041444003920740c1441002e00030780c10200412070b04241c0c4041c40d0440048040006401e1058540217141c0190001500154156000000c2c42c040d440da2100055140d90b1a011948024074540003000c1c41c00c3c101002030302180c014402604504803000076142036943c40400502240c00076080b121800001280900060030507101e0709442c01001d500409403403c00b8003c1070035100120790003e0154041c1001038000d2030541d04420010708204c0b0b0155180d100c2c0c8100b00c1e83c881401004140515860180079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244062392 1250 244061142 244061173
    0xd0501030c2702161208060a060203041d0403090b030906190603030c0f210513170a110105070b0c0d0b010219060f09050712030e03010615030902010215090708 70
    0x4075031442c1c010355501c0900c81010418019401c80f10031003440c00c0341e4104400100d0410785412110709940e80e2442006d240c01410070006905036080941194424001440f002c200611100400c2e460703808401d40d00c1d640c5d031504583e012001c3e003021031098008010300094000002340c49010b0300b1100c4111019101248814084031080c0c0b2000d40020101c1c030949010a50303150003c2c0010f401110003000e824240f1050003001010030001d480029000101c0350442c002e807807268000b41503111010030000380d00d02d0521f6500c084600000d800382500700d03440c0910303a001c2d00485004c41c0e8490480025440e0885d03801244c1e03005098030340e40080c01d00d41c00c02003640c400700b80050034020010201c4114034a6403241001401c0d06810002c2e002e683d00880804203200b04040b10007001985c9842001020525009100c15260a1203d010381c0c1425000d020200c034100d07d0b107680d83c0d91803030b0000341d040791400102c0c07030482e0b24681c1c0303504e811841c1c090040086001c42e200342903a0503401203605907171400054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244063642 1250 244062392 244062419
    0x150103090c0b030402150a110f0106060f08190c03020315040504020303040b1602030106090b1f0206041203141501020708030702060301030803100801020a0503060424090b0d080d0501030c 82
    0x10700c18091800e003400120703103100242d13810a0000d46440441e41d491111644180e20032140c50010030f00180d1001141c12080184040740041c00c80280106403a02a0107400011901401c105100c0321b04002403003006210000310101b0301c005014400e800208401500a5005a5a6142c0407141c0165008103007450b004641c081e0340d000d001580b81524248403020349801442e0180030604c408070324100035a40134090740c000b03000c16100001c0c01082c0c020811025450221181c81d101744d03000b080314200c54000c56400d5115822000042a16865550440c010f1514004600150340300000303004200c4041541007210000c01c1e002c6900c11a25801e69540e00c0c0a005c42c0254010401c00052001841d1003010310342190000c10b481c500581c44203916800c1e608440998000074402208028007840d00b40944240400404807030344202a00d12002c5880c403d0354001c14540b140c80d1241d403d426100e01416014050b00807403119110684c1c500d422000d05000c1c44182d488401d504000308a100d09003d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244064748 1106 244063642 244063661
    0x10030213050f01080f07060503191506080907050d08130f09051506031e040327080c030c010f180b0c0303060a090513020909030d090b150103 62
    0xe100d100504164013403000369008003152025030501082c040240c620a01c2c20036625030b500310b030030358200450380a10360078146440c12210140d080009138800303880069651642c1601c54402040d41e40515004540e8001441c0c0400e80000368480001d01200f003086c3e903140000391755040100017402495000910040c0c490b820080d50f001008009011950111141c6085090040301100b09a010003541d01c00d0b582060301203018107000340359052591181d11140d200f0400c40201440081403288510801c512407111402d456140110b010200d400f01a91800503110f01d41c2c1045179011214821002100708008000c1084140e5100400e1a048400001d4ae5607050007003d11000c10380300d510010f240c03450031003444001000c07c4030308100f0640498081d016170312241742c000d0440c031500b04288802481d007040b1004202000c10b030305220351a000d0311040c00303105030001542175485551 = true := by decide +kernel

theorem cover : BRFrame.Cov 243884892 244064748 := by
  have h0 := BRFrame.cov_init 243884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 243884892 ≤ n) (h2 : n < 244064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
