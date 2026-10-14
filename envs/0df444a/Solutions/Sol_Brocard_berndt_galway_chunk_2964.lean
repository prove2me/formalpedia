-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2964
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:56.583597+00:00
-- url     : https://prove2.me/submissions/5dc862e3-7010-47b7-9db1-d639793cb249

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532913669 ≤ n < 533093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532914919 1250 532913669 532913681
    0x30f07050705150c010e2b090b0310031a01030312020304030314010b040602121804051012080a0806030604210e0307080303090609031c0f110a020c090c0c06010e0901021c 75
    0x85501b0030040360081000401c050854800180d100d052900c0d903032402e0041080751025a0f03060100140c404a582700c850400b0710311421301d540691404071700f18600044464114400310b050340c02c0f10001803000070380282201c41c420142400c01a140d0742c079801d04901070055010788401852403900041042c401c55801407003500d205e502200c8403000c00c0e08400580740b162048543c0600034a00350110030745026000181c1045584411501c40c60300c42134542c0d001c1001c550119030048001614600c042d8000041c540d1100c0210080c185900d020b07100c005118203120025001003100e624114001802580d14001c8103001800b181e154035210061300b40e982d803040d030b01c17400d442c0f081800041c0750701000401c80d0541540c034100311b180071110400381400f0b040400d40380d0004c43d444801211311610000d024007122b041e240d00031320079116101f0034410b601401602d400b065000401c990b0501040002c1d200d4115030b9240303448101603032914800ca0081c0a0150405010900c407214001e044590341c0081c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532916169 1250 532914919 532914937
    0x3030507200d050a05010b010f0905060c0c1c03080705070f022b03020303061f120b030a080a020610050108090a0b06031603140d0305040b070503060102120a0201020d0f0b03030f0705070515 83
    0x1f0003403168400015200d8642c40040d450004900c034006001c2c50400c14064401212500708032034051250400081d000544000c06a29400401380e00704141a40280342c05e420040d0340c1030151500440b51610400208940c7e0007a02034823040700285081d11060283d820400d0140c42c840d10502100c2c50020740300ea0040d54203920501d440d00c0182d0105e1080b0301d00a4041074592203101142582070440d40142100c00b0500b035050242d00d0801000c1000a0000e100e21080c550141c55145040342001c440ca2051380c0202e81041640800c1001d4001d00148000c9e00d2070b0004504031495880c440020300d003800301e442d54640070032044000000c02807090a0160402c4004017913a00b05880144200d080b1041114050302c41c082c0200840c480d81e00400040d41c1003501032040e0f890f450b052000100d80f640c48030a06a0042c3e60020b920320401c41e29104500c017003810084103018018458000a0b5240241040e403201100001041410006c0810091009080240c014406110006000c001b6901700180d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532917419 1250 532916169 532916171
    0x11071e080601080631050706030204080f120d0f0204030f060e1002030c160809102f0307170c01050a0f14090601060806011808030a1103030103030507200d050a0501 72
    0xb00d260400820200e2042010954030301d400541d80e4805d8250941d900d03102d04a02116084500208109000e08000b808568801580c0c0f1403414054519250100c1c80c40107194024891000180291500302c1d0488510b400c2e01003a081030f01e01904000348241e500051a25070414007003001c0010340c1d000052011001025540a0840c48a05500f81e20013100c2c2074103c01c104110300061040c50b14801c68819006103801c901f4030f245035000c03504540c0440c943c10049040c101c1001c000d4941c0183c2c114450000d028058040c0239460810355481c003490703600404103440c094011041200380404e03200e0440381e5000034400c60030325003021002006400301040d0a103060403602c020240c403461010307004103081c80c0140303080da203811350403101000040c02c0d05040101200000000c800c0c941449401b03030910001031550340030b402201508500d4112041406a00144010008250000140d40b04142c001e02003540905039580b500c0714540c81507a01c540e100304990311000c03e04c240014204a81485280 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532918669 1250 532917419 532917421
    0xf0306090237090509040c1d0412090b041a16060c0905010c1a04030201020927091f020705120309010b0a0806090712050120030a06090b0a0611071e0806 67
    0x10300700c8080c1410b5103000c0810b403c00e6041009042598000794024010b0600c17850864950700f01199000e00b806c140c0d030810307070030500b484103011801d048074044190720f007408519140340005240b0203008030f2207410801c804252080700120303110740c212040b00c10298082c80040e421460040020441400100d0001d06a120301140a50160310304031119900109003400c101d54503d20040c140c1401070040701155000e00212400f91603005c054481041a080854420b5003901110210b09900500f0f13500b40303030b200d10000340d030b0060b10094003405011004030240c0d0360b55050401d00d241000d0906038102007100042000703c0c100c3d040d07004207035402007150380d60900c5903201c5986664034010380d0700742c1c969002480100071540c0c2d502e0001000a100b4000451405100701c082400752150814107551035800000b0400030070624407c400261040c58010450020601e012800d84c800074007038007040c031a110389520f10303480c410000030300144600803260880009200400c8a258200d206e070201d9403107440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532919919 1250 532918669 532918747
    0x15060313061b20160f0e0903070c121b09060608070207031e0f0206030a1b05040f06141308030a0e0d021302070212060f0f011409070f03060902 63
    0x29841c1e1190b940255901403100d00c0740c220803407a01c4502100e1118521401c084035080131031022040004003941124201c88518007144540065001010782d103541e08200203c40000700c0c200c4050040e40c9503000b40007107000700c0b440c00b132108000481400807042024800014141d41d103030004005e880690341c07030500c00c3d100c0d101c05a0341d4800c5400000c000c0c8042c4a0880081c18030b00f10f032002c0503401098039120546490300410100c0d03100b5200081110f0700d0313048143c2051700c103584d000c0480d9201e00c0d0a62402d032400e443c150b4240702a008a20070000c2007481d40301c17801b080b0800e9a51821540d4249200c0c40c0d41c0b400b001c1e50700e90103441c10401080948d10726581c0e91400e402c0364020310f0340242202e40c4070440f01201c0002075020581c01c81c0d201040c4800300d020101c08004180c0f081265003400036140c2440c8501529016059100c820120801c00d25000c49840c0e0105513504070400e8201025104450340064001d400140c10003018035101217451010f01d03140c0c0840550b08102040d28018012000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532921169 1250 532919919 532919951
    0xc0d0605030f061906050d0b010305060c030903090d020609191a0a092c0a0504020123121008010c0504030c0602060c04140102190320060603151506031306 68
    0x707100718810700d03080140042c100113007410040f0440c900c00758000075055198000201d40070b20009080e520030481c80010700c20080b00300300c1c0c540c02040016801d415450000c0825642e881009100c502888910882104540700e02d4284c032600240200000e030049064000400743c1e240078407440b01645141198000000c0450301150000481d640d54120700301d00381420401c1c00c81e00035008051003404030544440d40c544281101e4082c00c11103c0124031800c20340001006c20b0100d0448144600d889070798580c82009031030071550064042d00b07040241d40c3e02d103403508481c24020392059010b942000280b00019038000300800559100742d0149000d80d80718802265109821540d400b50104100802d018407a54940001064001481141c090080e07008462005007207588003103002c00c2403c0c2201140d1012002c00c9045404e01000804843c40c060300065601d56104801c1400410700d800444d01141e034402039180d060b080070f0b1810756a810551800003a954941c04113945c0e071490440010b03900d0880b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532922419 1250 532921169 532921183
    0x120a0c090b060909040c0905090607090902040b04050d02150f0a02100507141c0c0903031b0309091808040803090108130302100c02010216121103040e0c091203030c0d060503 76
    0x20141042d030034461010705010b400480a042604e495400c11000078402006003d19845031000002a0106080c18500645402c0d156080724040c140140024810603443d542900d04541048802c40711420050000c1a00d01281500442030301c0000030307400000c101504000c0c596507100d03071308580700c0840840c100b0007210420740d2280000f407241c4020303d0b0707041003450143c046000d210848001c00c01c1e03038901010846081041d482c0200303007550030030802d06801400360003034100302030006038041101e603a0003000b201850080401c640e42d1030490446108461208648495001040c0c2c2e654984480e001e45d502e8000441160000e401a4006020342044045d0406c0556041c0c00400c009a003407440c040c050050402c0d141c04565080c81032103040003030054403241e5680250105030201004c450014004c449020f0b050840b58001c101c03c20600d0350000302103600110141607141c8810545002072007501d0400c1c3c64450782e200103c00e22509070940002030a8054201070108041582d81c0f0525480c6d2107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532923669 1250 532922419 532922441
    0xd0e0a0f0f14130606030c0e041a040c02190803040b09030c07030605041a04030c03030f0b01080c07050712060b03061303051c0e030a0201060e0f060d0602090a05120a0c09 75
    0xa1020320801404004000c05102ca10008100ca08040c144480c21000c40c0d0440d8401c01c001b0341c131032a0800c4406e0704018000c1000070b0982d0140700040340d81214005c000300350b1282d140138a5491030103603912407081c040e041c0307480c041d240c01074904651414040300c56003007901d050701c0701000340f80485d06120000007203a030050f20940c003400c1c80d00e25640b1504001c20008105581034154100c40fa60794041400c0c03203502c101d210ba01c2c0c50f09a41002d082c000c08451a00050003070b00c81c503000754503c003a0b8000c03c0d9103502c4001c4405070b07591408645407440c18001540d104c00d007c261007800020404c921a080440f50300b10035030480780d0aa550414114180a5014024020400410003002101140e05580851302c403045000324800b1000c012070740c0f540c0c4c4000300510042c0d45d01d03041400b84042407d00c4540005000d03544c010542480300c00a6a6250044c10060645a0000e210443e40e240c0341210402072500502c0e03d00191400301b20940c0380c12403000c1c00c440034501d0080204104000748680000c50f5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532924919 1250 532923669 532923689
    0x23071a0a14150a0513230112110d06050f04050c0303040b2502060406020a05010e06010806010e040309050604090e300a090302130b011419080c0c0d0e0a0f 68
    0x240715400440710800030385080c80e400c1451030401142d40d40b221a10301a41900398071000502c00d0380c040103410300d09449030881c01092940401000107681030013848c0c000607084425a1008551440020000040c0900c02400325007418200125070300d440c4032a9101d0340c0280281e403251500c00c2c0070940c03613124070b0080440108081c0000d8880d04044801c042c41e1900f841aa1080e0008030340029260790490b40c0000d00603401580c07002d007000001e0040f801c040c40508000c0c140d9504180c6140c0e01d41d035050041d001189000000103080c10b100e640b03200004c203000b404503692261500385010142c080e070700301c0c100c1a10401d8500d00c21000c000744190340700341c4d21b14003404003c0b5035005030005940c804000042004581100400507039a00c00b2180f80c5180b52520004200c0c2c805800540200204c1241440d14103050181c04050715544001341c5044130720f403400b8107132661a05ca280701c40d4025041c0e100d10074426903071840003080d0810f205c1d00361881c0c120303141500565101942403125095004140e881 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532926169 1250 532924919 532924921
    0x30f0a051c14030c1605011a180903070b1e012615071209080d05040209010806040b04022716181a0f12190501050d110123071a0a14 58
    0x14101d4000605104104480805e02c01c102644072582900c0d01414505815a145049915649800e82900703441c82c0e904690f031180b03450700c02c070712903100c0c01b88420240407600030200007045a100020186008115180d0310703c900c2d611520302d01c070b044240071140c03588010540d0002c1108040000c940628107040001e96003140e0711a80d00f10ac0b1094240d4013a00d2480d11900804000380600014142d02c403106240050140b8245c01007202e02d101c10b80c0f05480c9a0407417414030000c9204c1031041a442601a40c1448116640c6001d000c51600e058180350303020100d500920000412140301e4610722420355036041310f4440c40d040121403140c01031103000310b00d210304601d6000d0290381070041c110307201c60040054204550b01d02031152640e000c031240d24491810034070080209001d03200e028054a0300361030141512044d5601c0014503000c0201c040d05000c00131050100d0b0800d50382d0800d2403001c100190030340f03442551500701c072440c46c214035a0810007806000550803c0c2148600100f402907110001c0c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532927419 1250 532926169 532926181
    0x120403050c010e06040812130e06010c030309020d02041805061501050a1d03010e0708101104120f150204051e0a061d0616020913050705010509030f0a051c1403 70
    0x102e00703650f08080d030403500c28480050901814030590203014000d10304580d4441c002041d00000b03103a150824035040e90000144481c9036800310a022403d5414100054103032000d00000e0036546614000039400740c2015003c1c40d040002c148440401c1c0c0c4500200d884d1a1a02210048500840c0006900050080c000e4600e024418401c12070307400428030500e2070003c00740d00444d081d900c03042841200c5500550040103000b00820074040b4505400d40d04102e80e1280041c01c030f5551003188100d050318034105035500203000210101183c0954030510900d1342072100842540a50020b22880713118090818450700581200e440628000c04002c06159045060a1061756030743d2200e501a80c00d0321880039001c08544600000309100c400518800c26030f280180304101c441c1d42e00401c901c500c0b0000c5451080022400138070320003528800d0911540b104010004645080340c0c80200c010726206580011003400000300301d031171451403011544410725401c15400d440010810814200e03880c0704000041c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532928669 1250 532927419 532927427
    0x5100614090604030b040c0515030f0601050f0d06060305160503090607031d0d0302130506090d0809030c060304120801170607030522030206060301060504110304170c030417120403050c01 82
    0x68410780040030781d42050303100d40b01c0d0540700208032011208030b03110030002c3c0000e103000030324442284038404e07007149149080325031540a110068041ca051000220700c0c0b200e540710300c0c8291201588000020048155103c1d801030160406a0b00342c0b240442c80300001461368401e000712885804440000e01190715401002c50050984400d0888420382038001080540018403a114445c003081d03501503181d100721903200404603400c0c3d12091142030100300c2c1d036440f0b403507008441080a40080b900780e02e0300d01200101c1d040006109010754012000000c12080000e03880203e095000c055803982c8442c0e8039000001441140a03868407142d900010010350818860341020394440b0980e5410144d010480129030001800c41100b100544c11000c10458207080074810701008040c1210207002e440c1600c40c0c1811f4520010313001a2600454503c4c2d000429075000882e40515098021030340d82d02d0362740c103046240c00740b46000752116024900444010618440949062700c3d00040500a507000c443e006407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532929919 1250 532928669 532928677
    0x10303091d182109030c040b090604050c0d0905070f0b030708010b0304050a0b0f06030d02161e03171c0618020706110313050f0d0e0d060605040207110405100614 71
    0x181281c420500d0b401d545100b411648405490b6112119407079000c0d860416081191102c00e241c0514234088002000d9541c0c1c004058000c50706480026194a4542400d450b41c03240200c4130405070704100e0b03c902000000034400d000c40b45e01c0000c44041546035a2045803500c4291120f100282d42580181700540240c0c0042d40c00512900440f0300c81ca0035030b81d4003140c0100803210445900ca00702c0c20460141001c1c0190300303240420b44003070300e124107560a5588410910307014101c0c0000d403c0d1000c0149407130748104880610380045c010302045404d03144c111400d500c0b20204003004e42d61010380c3d40d4a04142d0180e0801e80350b5005001c00c4020a05031500020f41040e01c042d40d040b902e405280041c414032000641c0603198103043c4103440b140f5802c00900c0c0501e8076825000c179600081c2c041181c20f503c031680d01510304049034003009012032030801304054182a0040e40e84144002007031810001091014181c846003905e0501c422381d503860035161002c00911a0f03001180d02c3c1811081c241400304010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532931169 1250 532929919 532929961
    0x405090d050301270f020309010f0608190201020f0307050f2e0902180c040603140c0d050702100e07060329012f030702010305100f1802040e0f010303091d 68
    0x2100c4a00d00c08070245d403040c0e02c82004c120707400010f10080b0102070240d00c01c03402c03001d881880445d00d0b020f406643c4a00140510310507401c1104000d0840e8824000d2440003d40602201e48450755410701544071151000f01650703a22400304010419075070081c84c0c0400180c08000c07641c100c82c0807440140540642482280d0001580e541700c00c0c0c840048a106000700064000541c03035a0500750040c084400d2000d400a54444c400f04100150400000319504d2046260010800341c0300c90304180d1801ca4040e03940b016103030400d5007148101c0000164401112040d41e0706010011203018100c011082100b481291f040080e9088076055001e030300d142e080c0402803900c01d4072403200441c1c03c1d0048c208100b203041a5400010700e0000b55a0715004068024188417054061185051017044001c1c54910440c61f161006040074481c1d01c41c0c0703605a42c0100505001002c0c107103412890140c5070102404210007245504002081069078140c103255104404507141d507003911001401c650100004220b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532932419 1250 532931169 532931219
    0x6010e0f0411040e0708120906070807050a02060c01050a14063f01060f06090e010e090a0803070f021005010b1602040906060617250e03010b0a060903020405090d050301 74
    0x700b24031a11103104880c025a00390f405050130318140040c07503003451040e2031040000e19052100308138035518007040301e40042e845070920340c0ea03503c1498401d0810980c502c020794002c8000c0307034418010006404c00343c030801e030010003046500c80510203c03140031000d54003145c004812111070320a000300300e240d0f00e40012124044141007443c0320747d0401030400f0b020004640d82d440e958204400c40811020101508850901c803130742c1d90410340340304030190052050200f101090700208041d45001d2103081c1c1c4180c0c004445940da460300710805000710403c400d0700801480799000c400c022600c2c030b2240034140d4907120350340303490501c84551070401c440c2e041c00c050b80d105648a00b000d000840c1c07807051100900c0540c40e1202984140580c95054100c010500c07490f04e82c0892840020520103e40c1010b0501c003401c01c0c1d4260b1001c1400f0a0040c001c41200c3e580081c2001d1001c109550803600250413a442124148160f43c4c90340340d4540c5880d148545c0a0104c0d00510061020881218038800300c0804041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532933669 1250 532932419 532932443
    0xe0a020a0807031104020a05071203090c0b2a0c1e122b050307030f0f0f05162d12060b0d0c0206040f021e0303030a0e010e06010e0f04 59
    0x144014200e9031000c00207500210041003000042030307a00504c0c08080750218100300c41890b0184ca05d1149000041403043c05080090005009501036106141c006101c0700f4141d803100340c150120b511164001800350f41e000d5412030a40901c0f00b107109445894409400303040864010320040d0b403049014800307117041406c604006501c80981d07210740c594908005010303541f00b400281403074005045152a8203400c005603040b0264110b01165000880384ca400113580d83c460114500170302300d000644c00c5680c103080d2007a48804803604094001c80d0944000c5500000c400e2041c0e030000150031410458440324a1120101611800c12051202003418110078103100001c0c0c00b0103c958541100142c40d80224117510165410310880f98650144c0c0000c207010304107911402200070350048002d11134843c3c80c4d100e03003c444500d0102070b2400f40140841e6100d003801c0000e00c000d400000f100340c15540c68050125064400010b1582c12502a18004003558035003003010001500028026a11124244 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532934919 1250 532933669 532933673
    0x3030705010501091d03180402070f15050a09020d110f061605070510170405030c0d02060f0f0403050f07030519080f012709020a0f0320060f09040e0a 66
    0x10004124091059000041a40c1803c50800c111400101c4851260f50242002204904004100e804180155000115008a035000107010b0301c2100c10042091040c0506207080000900148008003042801448142e48243c281c104545043d42e029600502610900000c9082e00d60b07120f00301c84021303017490502454600401e145034404841a200b24500040200900400b8003980001d400c04594542c817403407507902c0050298492070003c2145103000400b14040010070001c492400c001c1c41d0648a81064560029440d100103c4140c800590341c00c1c0001c4154150807102445268140c031410308140d803901411105401c140011000d00c241084082c07481503455040b408002c8032981c803030449180103041503110243c181c2c0a225220240c117085400200340d504c1c0007101e00440c4c10000b54915450001500840543c0d020181406880d603006c0184061203414801e05441d0322a0310b080a5092001d0260764030484d072030640c1c604801e20545640e0320b07181d0059060b000301d040444043e56515 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532936169 1250 532934919 532934923
    0x40e13081207110d050307210e0c21032a03070b0105100c0b06060a020a1203020a110706020a02150d050a0e101107060207080d0204180506040203240f03 67
    0x99414106071600d1041000708032a03000c681c21000141c00c03005055403080b801c1000c0d02500000e0a50000e0040d1102201c000302100c0e640c20448020014081c0b00c2004441001522607500e0102c1c207006105100c00303010300303070380c64080003140015100085182c984a0b00c0030101100e6040450107111030503022015003081c0c00c2001e020340c180520209109545010204800400061106401d2000142c00c01010801519001341d10640c01e841d1648d480c1104601241031026140c002400c50415540118460740c0c03550250101008c1900c0c0c80810b06100a100b59451207184150401a84019010340050402e50075103901047e4081700141018581484141a280202e030490101a0b89404d40310b01c50318204450351180d49400300410100e12480c4e0801041d119246025102c150001942c008000501046a480c260018011500d076501c07541c05032482c0c003074210004949400c11f008103201d0701e418400c0301c1c018059841190220842c0d0b029008107524480d003550740c4008030000381483c1c0d40381 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532937419 1250 532936169 532936177
    0x12150c0c1005160806130203130b09061f08120a091205010c180b0f131505030a060f050d03030b01020f0109150c0323040203010908120a0606020f03040e1308 69
    0x60080214240c5000b00c243c0c5100070800d9042c0d410002c2071300030b0060b20b494802054620a040c280056581e5495082c100011940e508009094108120402000407000308400d80a00c3c141c0345400b10041d00480d05070501022070181c2c840a40007500207011030018000140401c0c4c100d400c1035039030907540f242c042d14013000902c006e40f4a070351030f0700000e4401d0341e2020101e40c0c4481d148d80780c60440c0d8140124460b8501640a105250003000500314466001c2080180300410480a050644003243c41b0024150703042030b207100a03103c3c01c01d1700114080184807048030655501605500c07403078025132801c40c0540092840d45e411341c0501c0c5402c22907084280034007a005406102c904280c0c4081c0024039045170f80004410302014500b80c60144042d0150305100c0c03030780c80f042d00038407003e2f1103d0000a0040480203c010000a070006010300600c220b080058410090260104981d036900c150980e15811485984440c60b0010070083c08402d1202c2c1580360080b9442000c0c5080c0c1e082a900d41d0b04c1540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532938669 1250 532937419 532937443
    0x1903140d0e01060801021c0207021c0c0806130209060108190c05092d06130902070f1202160504020d0f0606030204170a020a030b04051c05040603060512150c0c 70
    0xc0c40c0c00c800c6070300301c4003401a00000c00e4070000843c50704440d15801d0200c0129407041e011015000524903003556510b164400c0100400900784450249526003e80440b0151042e83c0c2c0a01503d40054074000030658034801d080d4000e000e0002d40d40d02d04004640e043c80080043c080e10881554015032510a440792214415841c2c85c3d02d96500c040004000c0c4c84030750b04820081c61185003a420404008000241b503100d00251610380e11045011403080d07505072290011540d251000c1b49120034403014958150070316000e0122807020284840040762610950300310b031950712441e400c00b0000c0341407650040460f4860310341c0000d081524103540a0554401c0c0c0c1c0001e0020743c01042c14854100c5805401c02c8001c5c19600038609030f0380c1640820700300d030f000e44070240c5003080e0500090140b240a000e5640343c0c8140d14107480700d04520200c0944a50014011100041d10302100450b070307400c2c4405001e80031803c1100904600045500000c0c14240003060901840c40c1030050f4514044108040f8024036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532939919 1250 532938669 532938671
    0x102010f0c0f02070b130e0408041a18030d021507020a05010e0c0414090c1005220312050702030a0f02120708060106080f0c070f050102040b07062c1903140d 69
    0x1000c0000900e40103454001101085d001c001c0080d108003403103041c9040300e50000c44190950341e14244402c1b28041d6920a031403104140c0943c28000310840d0040c0000c140c0d8043d40344289104805169907081103035501805640403514100803000110900b0390702c0701641c4101c40800c48180d0302d05e401e40710350000c045071540c0710041a5410f45000e02403100f43c007002ca05000c034140b6003940456134490300c02c030b040d034020040e46c91181e000c107214504071070203506e130002440e1801410446554408c0040d20090302c5003804200741420b003504c200704a60409800500529010802c0c0d140c016511488a40499018200140140d040d003401d00840b40185280c901a10300da6140000c0500602001040c181c0710002080030407543c81030501c2074800854000610a201f002d441c54101d0082c490340c2c10035044504045001c000308040780c1c01c440154450303607000c8800d044482440201c24811030383e6900032500130310401808988104110400306000c0c3c41e0008904c079401078081d08961207003101c41090303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532941169 1250 532939919 532939937
    0x30403020f0d050d050a0207170c0f090106091a040e070203030f060d0f08132115050708060d11040207151802060f0a020c033c0a0b060102010f0c 64
    0xd85081841d1214203442600c1d0310340350301c03010358034240c0b00c160f002d44000600101083c0144400d108010800c09042210000180121450b4203556030b41400390801d845540d01c0d605100781030415801950403101c171911100c03030765810521007803140c08040082c01d903100401d210018801d1701d02d51582d802041a5009940d490811010030240984010030603405411036070006000140248100c000d8030f03800810903511a81198480b11030420954044204c078102540c0303200b07a00c41e8500010440610800341003a035047c40c0300350041900c1c811281c1030040350a610014203141080048048802d200d051120107401c403440c0080d080f07800403c01500d08605a411524110000c0d01c1154540c01c100c61206807251400d5000500703911031b1405007449800701046840e4401c1c020402d003010020000d003600c44100000440e1000000c0c0c0c81550500c00500c11a40c42c101c61000d58062102004a40903101403110354440411124000d4210f070304666076902d540110101c580324003040b01095075103000c4a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532942419 1250 532941169 532941173
    0x1020a0b04110a090b030d110f011a0a0e0c041509030506150909010b030d0e042a030506060a09030224070f060c1b0f050a0c0f08241504060803040602030403 69
    0x320f01c0f03a81e0400c0000d075190440c5c1074415940017804940036241442c040011142d40302e03065091407000701031250590300300800d00002083d0441d1406403594142c03115007200350f83d0305d00600140000d9800000f004420801031040000c00c079807130300c220846811b00c90780c82c0e5a25030750140340800172500c1280b040c1c0d806081e80c9003454806151034214681d10028440620400006911032412504040034451010a00c45094845801199000301c0203600c004a41c50b1081c1550282051001c150001038580b500003035980c600007041c1c65018aa903034460f03440394119030034040d001103208248103e410510308018100c9110800070310100e03100b109917401c1c01c00d2030f20b401301c1170341e2107561914140601e1061940d203442801b011201d4554100c290748000c07001c107003030050408007502c0d005030410309a2400440c3c0682d40860603000c4900c41d1040b50a6120807581c0c2643c0d9640702c04030602c4000340000451002c1591304200300f01c1da00e000b00b00148555031100c080e03296502c03e51000300540c00110382041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532943669 1250 532942419 532942429
    0x70c021507030c050601080f190203030313140d051c060303090905100f0b0c01150501050d1508060c0a11070302060307050c100f0605010311090607030f050f040608181c0c0201020a0b0411 82
    0x44140544411145486810b03030001e6102d00001b40a0f1043c12000580d8003f8482945042207074507a07040d0039502e0100341c941008100d5402001107030404a4002d11501403a12207209507801c8903055a514a130041c01e2103484005080040e00c4501d05105291000c03603900e4a4481c1d8400034a0031050090f44c5a8002480340c1c2910352000429050010300c000812090b6000011a403490400101c005510f44c00401c8030b03481c07175070544c0044440340300740750401c20b40c42120802041c4002042c1c8862100104000040d84d40c0d505500001750070400134004a5030711806100502217840098007a221340042002498044a0790f45005201086d10303403008004d0740d40c1510816450002117110741c0e14240c2644d011840328854101c3c000c0800c0030b540301071282244503109840800b641401c01c07075612942d60358003d01039901550955407400303061052076a410800980031115034040760581c0091850003d05556481a1041c160706600a024072400001ea641c0200d0b4880c40c8074a01c040b001d1908581448 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532944919 1250 532943669 532943683
    0x21e040f1103060105070201350a020a050d05131b1e030c030f02190906030b01080309030c15070507171608030712030b06030915070c021507030c050601080f 69
    0x1000180340400311403141c1c2034281125400307802801e0081d9100f18920040303640300100303102914000e4400e00212822030204410501414600552a11903294664034408a00c0744040f80004904100404c01185455402481e0301858903001c3e003414030426190105900c03480d402202c007030f0000d6001030003a0a0b07130400f40c00c035162003e03928030200350650ba18005440628000a001d140f5600c01d5241103543e0070031039090003030108540100700340d0707110060f10107003801c0e010407034a1072074810020030004400005d603050311400500504109114006101103c03801d60504c10b1a103808000b0000801c0c0304101d000014008528070b4141400c3c5426018181244046000380b188034000c0c0410144e84c0020030395160075007129240d8140c016000e010360041400c03410481d04070801200b00300002d81c2c00701b021003404420580c810460f945040d012603605007003c00c000e43c801c94082445441c464000d001e03051a41c401d0400c82c01555150300e50900d010f0003644040501e81c01981a21400c1e4400d03c00e03a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532946169 1250 532944919 532944941
    0x50406050108070509040b1008032205040924020d0905100e030f0307030e031902010c0306060305220f0507150e010309150b030705090a06140307060e01050d0207021e04 74
    0x5840051308141c002505903502030405400c0007822004911641c0c600c440311b000500c5d400048076501c0b1040001140032140d00268680c440c0d900040c00036550070240140300030680e1020a0850499000e5003201d0001c41124030000015801e101c19402d444036407065264043c0650010012a490b00700d5240986000c90402980d0780c005005035291405004240d0b60000058280450707401903200c203683ca1402350080c9150190040300725800c3e442c0d010743c8034814240c4c0c10768040c00031549927542501503074030030b41d651241c1d203101c0440301200d845903140e1540400e1181100c0101d111003915014580745140e0802e190080310000441c0595400500d45405020282005e00000348035880351b82c0c089108040f01d4810179111400d64886542c00c0c0a00030143c18010018006420704c4103421000705400d005d04c6c0c0071841c00f00c29142c442d01d80001c5040842e606a62045030304492a00119a2504060542403500e41c00780039100050791440c0f0100d030664480c1c000c00c590580c1c143c0401040e109003200d0303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532947419 1250 532946169 532946173
    0x10615110c0609150c010e030403060608160b0f0a09030b04050f0f0a05030301140f0907030209040606050f2a0703031e08040b070e150309012f220305060a050406050108 74
    0x401c6050781c50341303070215011645100c0600d0305e842e6466203450140a81c802ca81c10316001c0060007104221440c0c0c411010744038024222289500c480c02180d01aa040d0b000f500f01c429818000c000004001c1401001155080e00c6c049400c01d071349684021806001755811103880d00028251020342c0d000b00150300f071200344100100701140854a403075440744018014200030510f410114802d64032548901803407405c0c081c20101040c0b500a10040003900b080c0c40c410f20039800d00b1400582148500d094030036005814103110719010a59030182d0708004400004000c4011030030907124065810700c121801180207072103840d50351a1980030b000d0041030360f40c016020b01900340144408505902080b40c0c1c02100c60400c40c0d05500c01c0800218860028080200c1104d40001080350361681274100c2c60307a046c3c0600200340d6901046042e1112003820194182982000703012144074004c0d2464201040d110200b80e903c1c41ca40c0383d485940c2801c8007220540a0b41c0e86035810310040100314401c86d401000d06c080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532948669 1250 532947419 532947427
    0xc050403030e0f01031b0c0201020609070b031602010e0a060204092d050c0903010603030e270c0313290a111b0708060717010e1005060705010615110c06 67
    0x1d00641a02d1542241d03030b002d4103500c10f0080081e40640c0c05130000c0c005c034404903050724103e0040202018424031040780103004100100304500e400203018016544051070441c107541d1240c101c3d0194022290302c0d2411507480e080c0d00c40c1c08000c11f02039200c1c19800390f00003503691400c01100c5000d9403080b2050501c0711250009071074402e0290006041c1a0842400101d441d898481c074001c00c0d8040c00d90300c0c99141d4a0640300004041e040042031140302d2082c4ea030401103008050b05208000a01d4550101c42c21002c00040c00d4503000e40d004646c085c18442802c21100b1054a0764001100b2034005079681c00381e08601c030f04504100d2148d55170b0000c1d41c1c1a00b130029040784010504903002e00c004200158030070348140d41c0042e500340305400c090005030301150360354034044800034400c40011180031298500d4000201340a40c5205c00d180c45400d0602c50b01c15860310781070520266500000080e692951b072a400407c41241410304103040e0102c2c1c0e59903c040b00b4114004034280401c00c2c000500c0303070500304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532949919 1250 532948669 532948673
    0xa1205130218100b0f0a1b15020a03050108060f01050d030507050a0803010918170d06170d120509060c090303120906010810090f03051c29090727050d0c090c050403 72
    0x3400311603a105081c61f040c0b9140006400d500c513030907032101000300110961005500c0000181d40540807101e1256000d1200741d0b40e4141d080d440ba24241c4c2c1042444070504010f0007c0e04120b001c0e03014607446843e2603843e0044a842c1c050416840c24400c540070b02c40000104001149030050b02016043c0c40e05016a14021341da0388407103100c018206003030106011031031100a0402d540204010320301d00d07905010002250450030344030140803c0c101c001c11486005121805441d1140c5071084000c0801000a51144089407416400240b0002d90620042103c02d6140550b901013900400382980200030075410303c00d13164200b00103800c80b00302182c0740400c034402103150898160070082c1c00d42029580c1e0f0840a40c0145d5002803c0d608640090900103101905032041007000c0c01f250089903003c2101d131440c400c01c4421401659440c0001d0f0388503103403002c3c3c280b8800340590942181d9403d02401780d550008641803403507a0a054038140540c94081000d40201d010301c00701343c0c1c01460501e07d42400d50b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532951169 1250 532949919 532949947
    0x60111061e0f07120b010207030615081509030406121803031401060f05040e060d050a0f060f02180f040b120f01060b040f0b0a020307020405010b09040c050a1205130218100b 76
    0x101403080a52200c05c03000499009010a01c00385401003414003007041445102141c0f54501d114241d12407041d82c46103510300501c02c41d2540250b24100c00b81d031901e40b411130100c51441c2c0c1241500c014a585030b140c20000c03420088004e42c60380c403c2d1004100007941c038a240411840581c045010700061880894031242d02074115001e50704600b01003151901c40b1000718079001907022005004e0300c0340d01034100a010f0340c1181114090712950b0103001d0908004007181c164010003a641e42c2c0d1112200e0350310900c2c50400c1100b81c0b01c0388040c000280882d40a0001400103a440301810f40d00c0e00061820b00350fa40083c0526800f030103144100342d2525240c6000d00d641080c1610071740d40d00000214a180303901d0303c24021100e0781d41d001042032049503110a80943d0651103070380342911940c644099107244074041d400741c030007100d0316480f2038101124a8051b08084c142c0140552030482e582212080141c1e030b030003480c000d20942c0d14072030700c00c6140003030310b04010b142107801c02004c050003800684001000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532952419 1250 532951169 532951187
    0x703030c08090402210601050702090c18090711010f050106080601080a1e0e1501030506060114040e010b0a0f090305060415020d0603080a030609090b0f060111061e0f07 74
    0x21615118803402401e040c6030740d60740214441c156009000081800c0c00c102c00e800415544201c2c80501c008a894180054803070348200c00707000350031040110000300d030340f5101c0700500103c5c210031145201646407035000910b513113001c80d80c817404a05405000c05810400b440750b203480f42042180bc000b95414650090200700c1c0042a080c100141c1d0310004000c91030a400c096042514003048134541c85201c03d45101800d030810503407009110300d00b844010400600a018101c0b41c200002d00b00a4a0b000011070f032442d048006443d80c541708100c006601071580d03070410300910851040c60707110041400e0050840e890b00840d601040b908900c14004603501041703958009501041c2d1545180350880032001030b0042c1410807080ca0700d0f0020002c02e01000400030302043c4080d036401c0200c41d4550481c0c0e02140c414140107407003070480c4800034990903400039280740c00c14014100800c00307140b00041645004000c0325035171080d02056000c840d2101041c14a15000010a8034405c02d900c1d060340003c081e541 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532953669 1250 532952419 532952423
    0x170c0d0c0506060f18040c05010e010302031015020c09010902120c0f0405100c0209070806040609060803070206090303190504150f05070b0a1b02060f06010f02030a050c0c040f0507110f0703 83
    0x1044001084c05560340e51300300c18000a982440761007460503061140400801d4400c241c04941c0380c1003905860340c0b2074804c82e4403840b841501000c4071420282c60b0044000613584903c15032040c071020400590740c00c2c030b03040e00a00c013440c4096601d0241c80c0407510000c01c080c09840e141182441500d040f007204034140c0302507c0b0f007903d41110345030751428102c503a030407550006501f1159400502c08010380c0700a080d4407134541a80e00b48500796441d820003040303030041e224448858006001c1a00103141207030041021f00d200408480c11324035000c020420503c00307200b80b080804c4002070100b00d0f03d07240c0b8001f404182d2103410141c0c1002460301001d0f00500c10003100400348010880000ea500509510030800400314140c40e002001400c00060b543d00c0060b111003074129031910002e1455842100004c0440b021940618100004402c00b40d4140d000301c1c010800c80d020b101c0c2c080b111031300c0c0c1d8800c199912880301000f0030305091540001e001400748500c00034a5070800080410008000200e900841c5d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532954919 1250 532953669 532953679
    0xf030b070f0923010807110a170d110c010f02070c0e1806090c01021c0e13180609020f010e011e05070f050708071502060106050c0a170c0d0c050606 65
    0x101c80854111100780d181d82250b55211000300011080f007a046449440008080e2500800d80c1c440560a555041d041c0b426080c0f0b83d404043d241002a40030000e00d030301c008282012500305148440c011042e41e001e003420548038080403400701c0c0340071400d00902c0708801175400114a020019100c3c0290801c00d40503040c0ca0070030a20105d140000129441c1d42c1d00d100d12003c0d03410600b1304d00c12043d122002141c03214018418034070000725410002c103a030102400c1c40c0d01c462a0034000d480a00c68101c0c8180c0b04910319a40c3c9400c03885203502d107048051842803184500190099051041000c0c01d20940e16460401c421401c0d040284d90700000114202a640300c40117200c031146a404903440c0c0720302003000386041101c0b05100d040190004100040d2000c01082d1805580c85800101c00b816000c06648016801803004000c1036000700b00411120b0014010303540183d5a5845001d04455480e0350707000d82c81c2002800700d81c131141c01e010b048085030741403412042094541c0c1350310303588000103410700c1d1040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532956169 1250 532954919 532954937
    0x7050409020f0903101a030c030a030f1106040c0510180303030e0f011103010806010e040b06100e0d051510032d0c0b04140105030708041b05041e060f030b07 69
    0x12880b480240c80c2d400a0090445034824102e80145001d8242403102e2500301d0140218019a407501181101e841d20300038000703150381c01080e1411901c0007201d0000c0010b010762105410041102484514400d41c09030200308a010302d0141030010900303c02c3c04032400c1010f01c0e42d1141803001175801002c00c5a405240115500d065000901c0c10300140c0b510912043d8641241c070f04002071110040c40c12a203039101900c40682c1c0c0c03042280c100c030404603401810b880d2101e000440300d01d00018005074081c450700c1c01c050800004004034280c1c4a000a05469680c808203c20f0405e04420ba59981e20914201901d00024138580c0c2e00c80c1c10b52040f840040c0000d565044800b060008111107080d011341140e00808120794030307103003426190301c10700580c0f1000800c01002042075018800301c80c01030007143e83e265801e3307a99032510b01140050043c492058400100b0000d221707a5140100c05007040325003401401d05680d2800c030400c50b0000e511032010a00745101c20000b10b0080c540480d4001c4203400c01d4045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532957419 1250 532956169 532956187
    0xf020c070b2101031101141909030215030408030712060504180c140f041a1518010305130b0703110c030d0b19031e0609030c050c0117011202060903060a05040b0f0705040902 76
    0x913070017110031988c01485050201d46681b580001d803042203034000c0d02c810302c0380c000d440003805c200d01c412070b00901032020400100d0702a5104035103005c10b800d24218002841ca465800160580e8100040c000b0354035645a602020302000c00701c06001014040d0712070312040c519001041103005c01d001c0f02480f4541e5042405804108002c81c050030b044024050320181442101c20308441d0400074280c141a45001010b0f0840d5010703128907806204200d4a000440281c2d60320311030300d504001c0c000b90030075441c4c41c00041e2025111001d44036610480000e10340303c1c1140c0e807004e000c503548030002621600c008810600d1051101004605580d080403103c4040000c1018030000c891044000400d02407900f580c81c401e15a1240442084a200f08160744421051500444003048044011010058400c0c0100305c04086140070705403a0380701900c242d007043c2c424000281002c20844800c0c00071a211010401081700350000154001a02000c1c004241800c4a0040940c000c078016000a00ea00003085030b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532958669 1250 532957419 532957457
    0x709020913110406020609010c020309061c0501260714060c0a050706020a06050601030510090e0c090c0a091502060f060a050907020f1b060d0f020c070b2101031101 72
    0x51040210805011a8010b5654040168007512400005000b02c0020444c1c001040c01407c000030030342c0d401941880e600070304010302e035072242002c00b80c80a41d1885600c1e046406000342c03802000020303288400c5001449805c66190700310142c4101e00d41040d02c3c14442c1e68410310130742400100075075080352503441850080e40b90910200018006125102c00058059800181c80d18085e00c2194140a10b07107800c0010740c1070311000e44600405241905041c4440704081d84451800b086401c201d800030300d10080410707002641a640c0188403480044c40010391900200c20a000b417616030102102c1c03100303602d4001d4031194090300141c000c950300c9000c03031910f41d01c2444a0000d030500400d41c01c1d02d82400e40d40a55151140501d4241d00e0050904421217011180d031401550b10010340740c3c0d494501d0b8a48910700800081b041c0440c1c240d800c1c0300c0d00840250030010000a0b192481c80750f9920403151307804141716150600003009280e044001070000880d01000048001402c0c00c000c0604451003040003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532959919 1250 532958669 532958689
    0x612110a0302130504020a090c02100e011b05070506010e01050607110a0b2808070c08160501140103030e04091509020f061911070e0c07080c01060b030f090c0307090209 74
    0x80e40c0680c0c84940d101c8103c034a984482e0140b4400c484c440041c0344e846110b0b07400c0d1603480b4681c10268004140030b030950600e07030b00240034403098003000140303803001082403402140350480e94000003036000c1441c5c402c20404101e11405440c148001c684035614200001c0e000344203010b0000c28a820101011600d9117481d41200c015044040c0e026440c2c052003c6441040c103509100c6440805494480184c070a0045014038090003803030f52400344404044d143e8144ca503002031440045000241c0340c800208100303100c7c4030401000903000c0b4085500d1828010004119007a40911440c60103d1510002d00d5900500300c00d1211b036031021078440b010340002400d1000040c50320760407440020750b008808150b190150904443c0b40c5400f5000c0100900c559a21080c1d401004c10f148900b0303000c540c204003010f014100080c4203400c0702d843c0c00303404503116080d9030b40c80e801a01000c202000f40510071011285443c1e2040c10301c0c0050002030400c4000a54440080c402c440107207500248038003ca0311004d200d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532961169 1250 532959919 532959923
    0x3010b07210305040516080309011b0804030521040b090108060315040507150305060d170403300c0f0201080c040902070b04050c060717130801180302010f0612110a03 73
    0x70050300c0c2100800070707001d80300c2201c1c01c960a0007000c00f0504018800007546d020342c1d82c0a0000d50510683c41d0040d0307840e010300701d2341605800710780e8044000500080f008001030352141c0d0182031b610f04802d160a040080305507a100311014107020034800e50100308196140008246400800d075195000070a0030000048074903400d001009040000b44200042d054003180c03050610a002040d1030042201290390540d840c607800b403411922a8003180e01100250058401070816905d850f550b65a0348500c040d1201d4000065220070313101007070010359104001c45004c06418150580081940c80b07403400b103580a002414011a2008122051180b4094a0203000c40d5482103503100f0705e50402041941d4100c0701200e003071181441c03001e580d003880c606480629911003410100c62084801d280d4580c1c0140b034100c20220686080092001d1007406640100c03061143c2050608030b00d400c0007401d5908003134008140c03074201030041020144450001507116040145100030382404400038012000603400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532962419 1250 532961169 532961213
    0x40c08010f091203150e060414070324050112050c1c06050f0d05060f04020316030609050c040c0e330d050f010605030712062402010609060b03010b07 66
    0x141c0d081100300c03030303215a001d83d005910070540b00424142c12410b0310784c0740d240b1003d42c1303a030f18104000b1500542d80a90304614010004101c400140280c91507041c8201c0721600065222402e88220b076020b40700703925054401c40b01c1c1103001c1d814640040e2000c107a00303945002103030b59240084d01a80070002516142c2280f042c85005041101c100e0f0300203061309019251040050b107080720a646040300d07a4000440e17100002d80320560b140c00e0b0203652820000c005030303054040d10300241d070f0644000241038040c4d407041070002800c3c8624245a480c0c10f0070703907202900a501c2e0440034402140c1043c428030100108540300d8881307944092000da480048058004000381017550000e0f40d02104d02c0c05046c0c4030180c090704001c1580c48443c1d0a40c141400e2090b00040750741003012800030341c864040300d14844030030400824081d950b6001d0804030b0000d06c48848000c07081c500b07021100ca60a00440004004415050180d24100344048480340300620581c0421031001170258100318090354240d000e03e01000f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532963669 1250 532962419 532962431
    0xc1106030a0e06091005010f080a0b0c09181501020d081308040e0c030906070212040b1b0604030914060909061014040905010501031b0c0605060a08030706240311010305040c0801 78
    0x3c02c07607511042840203200707490070280041081c05e61488403100710781d00d9000a08500000740c4039122f1950000e402c10800304810400d80c655900c038100c4241030306460f414280540d00c0e1040c0c450440c0e0304100103072411500b003003001440444c0e0140c405a040160045008048441ca00c1c000400344550303031000f0400100c03281005030035042da002a51042d01d064090314540d990390701c0126101d80d801c0c1c400c41c0c007a18040c8818041642c420700503002035511030205500c0d024079684014900101194220005070880105201600508400b000890030580f0141d0501044400203495000020000d43c0a0351a04200c4003a840c030524010078145820001c0710303a152385455036400500310034042c9501003030500001e0080e16607442c1d84c0c80004046640c0308004800c0703640d80d4001400c000340c400380d030085021402248104047c40140f5140e4070600c4c0000da540e0071001c107403000e03059140405890800049041011801c4043e10b004910350034070303001800d56102d24100404044581114405601e840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532964919 1250 532963669 532963681
    0x9040b1e04051c2303070e060c0105040507050409020a090c02160e07141812010608010e06010e0f0907090b040914030703142704090605040305040e070c1106030a0e06 73
    0x105504440018a002d040544400444151844e125403c1c4500410420075412444484414043c60300888280340c88800d00650000040b040e82202c6a102070b40d954034414041002410481070740145404d0354207000090b480c0c1c00003854080a44030304024591619642c5505520912150303203100202d051f19403055850b040804044942100c0c0b190101c4d5102032210003403004201079903180e0410b400e15425841103101800b00302d0040c0d18815840750b40351100451402401c0c011044d1102405c401484650302d0503888010181014050082e005400c1040c00030011001c55200c0c10307a011004080345407440180850700400d8107200180400580c40796000308044048000c160b414041e43c0c94590702012240b12450360320030301551f0380748080302410b0001c0c2a100d0395144610400001c0000035010320a8880070283da9040300c040b80041d1002409100e05442551081d070041070903d0b09107807842280e912132003600d031480e101c01d114250200000b4943c8810390003418050710706105682c040e003444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532966169 1250 532964919 532964923
    0x10f0515340b01050d111c1211060a020a090317070605070306150314070f020a120306051c0507050d0809030f01050a0c080609042a0618060201090209040b1e0405 71
    0x5400708880c2400103400001d22450f01a04540080b5003001e41c2d00c4060740840100518942d0701c103a0708102400320800c400100ea604d03502070301c900c00c4030b41302d9100301405010780030706010300140100310f200d10512048441030751000f81c56040d0ba40c49066010ba400124403d0340d0366005440e00100658180001c00c25201d1b0315403c6081100d09200065400101c1240c0030790540d001c802510b5181c10208000501451040d000c030100380b01c580c0141c0b0070038045611041c0070750b0324113480c0300c010071b4030b41070100b015007010711070741075000b03c12000303405d501401c1d5403900d403600d03140d03c00c561241c45000072010a000c51074040b81e441c40e00050841e001003e08903819400303420f04540b104600762400e0f122002e5103004100051050500074130106040d6aa81d4030491002040c00c4c0480314807d00c440101d028041e108140b00141540362900d0761551506001d044440005070400380469041ca84e008006807600510b803a00182c2c89401550507a664a0030080e480781125041c144541c10103003404184100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532967419 1250 532966169 532966267
    0x306020f09040c0e090c0a0e041503030f08071d0f120703020a080309030715090f0303050903060a2f130f0305011802010c06051f090e06010f0515 64
    0x1042c2c1d81844a55081401660b80c418083c0645402941c00c0700001c0312000c00700010f203203c001501303000e0400d1000a01240c01c46451121004680c80d143c1001c0c000d05800c4001c101c0004141c0c80c0004462802e800d00500941000e038400da100c03003803107103155419902c0c0c07450b6810314540504801040b6094091340e907a560068441a4054030151802090014000c0100c030b805003005001080310600d0000030313085440c80030300800204490087c000c121500203450078001140290380c0d16403649002c2082505280020306100f42c0140b038250702c201840c400380d4a9407402400030107051205100c4448082207803240031510754401410160128a980c50144445d060702d010b800200881030710b11005e0001d003540d805010380800c40711910000085c0d425040300760302104104d01600307205455410a600c28246070000031040351110003400207060300b00075443c010104030442c0001280b40001051208540300d18854440500098485000d002081c07800348a074802000d071403030300c0f58000c010801050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532968669 1250 532967419 532967437
    0xe10030b2a0f040e0a0f020426010515090402040f0c02010606170105150d09170a0e030601050603130c05031c08070305010b041202042c01110408031206010203040306020f 75
    0x561500100106200c42030710301c107101c102c809a24040c00d29881c000e0400c03000b03046412807a114180386003034002078000b8200034182074001920032403c2c80c4001e81c1002c250548000070340c4c5008204100e103140480340e01d005030010760350205035849900118001d0b040e0309440030282130421441c030280c5941503000c4000c840c0b01c1d80d1011400001028940d280750000c1c850707150f1142c1d274000400d500d0280b4100401d03d00c01910300010701c09038541d441241058515004c4000301101040028269801500c180c3c0030f14030480c003500656040c0000200310b4040079003880f00a2103500d54030010045034114140c041e1800404462494030000b190008003a00004103a002070344901c08590305d58003d0003800d05940c8080700b000c0c18903081c00140494806c6801040e42c1c4103448001941d0b01101c0c0c1e205205c850300c00d400391489000c00800381e10703003961400380c0c0161083c80c003040304115040e00403040d81d400165a80d130025190f110b40004034030303502864101074030084c40010105001005200100400d403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532969919 1250 532968669 532968721
    0x41103070b031603020306191401080105040c080a05091e0601290d090c0b0318010e0724020114090601031101031107020d080409091a060907090e10030b 67
    0xd030300c072a60001d00c1c1c00143d641c4001400340244950300d290294014540c0604081d00070a060300e0f0308020307070784640d4095100031011041000e66100701d591011426006d440255014080004003009c01060030600405988601d5501c2c80400d0b50010240849242c2c8210a10110903200c00b880c415615401c01f803081c0801c2641a24600c103115034110741d00464400001d91450920a00c1d0400344050700d007409003107074203004909000c9081541c510285000785200081c1c030314518100f0351060b0845040c00401002c543c00500200031441102440d4440843d240e05070b43ca039041251004c0e40900135240c0b0300d40001e0300d944100f0a03004000140141260f004805541c0103c41d4200190200c0d040040102c1001c101007040c1e90142c20500d21149000744038140030b91919550313614060803511074480c1150000d20000341519000241e405007904030f1004ca0700c101045c140144040c11034a10340c400c0302421121200014104044080c2caa001940c03c032480800a15002c040c400c02c1e0340301c06100b012a5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532971169 1250 532969919 532969933
    0x21c0f0f050402030a0f0503250323090409080f030c0d14160c11120d020111280201060b030c03042102121b011b080c0712050a0314041103 61
    0x4500a401614003030303030f0007402030050580641c071140c1c200205408151410700c010080710310580b011211120b4a51004082e850104503a4500103001c0c600c420500483d07902c0140d4003035000c0c0c511800320360f0301c0001103800007a20303841482e210408d4080c0d210f4034842e0b49408410071404a913800010001e00c0703e10b12040110300042d0008a1107203c00307641394169407a501d80c07581d0341036000c0c1d840d0606543c010340e24242521507802c0041c4601c510203120905980051900d504401c0e0240100c82c50a2900c458081c14401b0810042c0c883c40c035041e00c035100d04283c2d8020442e00078000e6200b80054105032108958a242c42d0502c0c1505a200b900c040b2061340c2541c82e00c0c40f00d01740c090035214101d005a80906003449446da43c1082a8020881c0c1c0c0c0d0701e2080703412485640000034881c0881c9414500000390380c00d0700300d220203003e00380001c040c001a03403403c001c0c960005100c144e248110051a04115480d0302205400300c0040c07003034141a8005203504006c0c0014824412320811801ca01141142c4c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532972419 1250 532971169 532971191
    0x304140f0604120b0a1505041e05012606090a11010908011a1201050601120c091824060509060a1205190b1e0d1407090b01030f060e0402040b0103021c0f 67
    0x2281c1c6c9107041c0300e04021500300c0c00e05c2a4901a00810408158405200510440c2c0750020701251800c0c0e00030f00c8180c41c0141d48000c4210322400f03201c10b041040018280d5031400703001c1662078441d8200c000306011401401840141e0103030b03040502801c0d4000081000a506103007a03091103500c4800d01d0301c41c1c90075492004107128140a00352280e6410307135908000144504c0d40034040d0040e0302c1e4920902481250201e0740301c2120280318003254803020045595039084131002d00e5103e02c0c0350403d00c24040310310240880c2c3e1300301040300c402190030f9800ca640d41c000001700320317102c500700d6550703030300300d5042c1402d01804420003101c0140ea864540810461421443d08000000e80e0342c08408014042c44100e0036042c0c0b404401c0c0b00d281c180114040800390b17501c03100c15400c0c0710707240d0011843d103541e607040048156494480d5808968280d441080120300744a006403c003c8000c1c03000384990b40f20310710f600b0300341d10a405030b401c40301c0c00154800102200005041c082e01103415891892482d021210300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532973669 1250 532972419 532972421
    0xd1407060c05010b0d020d0b09010219021006051503040b041e0501090501293a120206040305031504090219030201030b1507030f03090b0708270304140f0604120b0a 72
    0xc3e05d25130080000d0b03a800c2c3c0a035940c6030454801000840786541c00d2144071140344c0040c15000d209005640608208034045004000321500342c0c000e036014400c1200078015030742540742182d4100b80c02c8001101d456072285003102d000f203400d90070380c3e01d4070303003403045034001c0000c150810031090388220024401900c803ca43c024a039032030040c01a071807100e442034440081c1040c10950b80e00040405444d05401d50300b4000e03140042d175045101d2035013050440c1040a00c00c0800c40c102c0c02d00518400317088182801e4400410902014040189200e0042115102070780c2c0c1c1e9004094031a80541408980042e0403000180070103144007d03070119052240d1a16103141101c0840c4072007801d00692410005540c400722021041740010b00b0516568645110100e0f50090580b442241300d59035403c242c0c036103801c41001c04c200c004c00e41c00004400c20203107641c1c114044252001c3c2c070f4800003040080c2c0c15803000120b5000d9214600d0750000400540860354001244d00525000d0143d42c01d10001d8a4403148a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532974919 1250 532973669 532973689
    0x9050c03510916080a0b120d050c0f0a0201051c1b05041802041d0712020313020a09141803070b011e060f1413081005191a0d1407060c05010b 62
    0x10f00090b520740005441c018540c0d002698910f0007034039202080d41d0780d10a8070310700100d0700f0801e80840d0740800c180e66000401c2000c200701c480b00002501c898859580040c01034023031030804401e44c890055011100f0143c40d400b0440451003120010508c540c0240301400c594040d004e51106483e0f0031101e446c00860600840b41102d26140c0d0b1110724840440161403100005803201c420000400210780707500e015800518044e10f0406036002c103000092041005c00060360303204c408042d06101031024240c02001d030341a030090301364900c1300e021909092481e0030b500c9a07050040c03181e41d1410000c54158064150209203051081151801584444054994180180d440000540340341d0200c00034082580241c81806107050000590070b0312000c1071b03420410000d4040d90900d940d030080004e40040e4211307d6804401520040064941c020164046115414031060250640f0001c2c00100700c2c10704001c0241c60900b800f40c90b9071070340341c202c02450759141101c1610550300300040003142c1d2410080078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532976169 1250 532974919 532974961
    0x132a0f080a140111030405010209190b070b090c0301020705030409061703031f120f02100302031e040f061d0f030a090504050a0e0303070909050c035109 67
    0x300503881c1a03a45142114202c9198403403255200d04a50f4903242201001d5401a40f0420001d61201e000714203020444d80d003c40e1001c5030070054501080b01e81d0107d0304a42c032080d0065012009595203c0d10b6610b008c86458031941c0561001443d0001e0040100150090319070b02e000521200d42d0b204c1440340701a1201d5503075200c6810030004642c5a4070742d08a17058011900c00b40d400321031584c40150680380016140162000c0013500000811490600900701341c010082c1000c60550034002403d030087d50391560045545010000481c06000c01405100c110a0b030141c1d09101c604d1004012440071040076601e41014032403418251703810035010058640d0420745946100e41107140104000243c60007810381444651768105800401d80c0910082d440f031006520354840f0301e80707000c06060443da0001e1020181003418014130402803a880944450000c3c803101101032a9500c01d501c010070305c1d5420301c1420344075066142c0c101600c0d07540070500c1c00341c5080320a13240d15529409801c1442e4655994 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532977419 1250 532976169 532976173
    0x120201181101020c100e0f0a0302100807170106120e1605010507080702090903070b01090b101d04092001050c030405010f09090f0f0c0807020a080310091416090303050301030605132a0f08 82
    0x340c0707841cbd00c0c418842c10343d002405140002c005a40c00703051907139818082e007144000584076840d090ba0604203005401c207001c9000000d110044c18075011410b003080768041c2c1d0b410040e0008420301400040b01c240c8a11a030028500b050718104014460303a0796010100440b4040b5685000013148503261052901c61400a000030803602c6400d401201e00a1614100c2c000c0343d0308020a003065501c4521075940c0e168810201e1703a0040d40c040e0b2442d8207558821600904004040040c45c2d403200000c41920b04640c020300306a806844602d000761030617403054205141451074000000d9601d80590403141c0e01c03480102d001c202e21030031520101c40d0144221080c4000da4043e03d0071000080d400c0c001980c3c403040c41c6d602c0108540c1c03610103c0080d14025022038040102c06420702c100260300710150500721103d8104a40c8952a65038003030854041480b001e002135607070700001040c0880c0108c10300600d0380d01203049002d1031001d284094148580c944007180301c5c0d00501012682298115001c0c0a6a1401e80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532978669 1250 532977419 532977439
    0x160302040f4a0a02040308070f02090121260c070e0601030b100804051f050610091a1e030103260301082505030a0c03120201181101020c100e0f0a0302 66
    0x3050300308002001d0100074605501700310000c0070444003000b800a20303102d148512100071403401008410139040e0848040680c2d8a041c04a410070241c01d8114007582c072100c0c0d2036101c5114442d20302041d9a00381d01d188441000500780300110408560042582c0d20710300e101820307886007001103003202c00703181d40c09800100302d4039214079403405920b120354814461011100a4070100c546200d101c034640d41c0307125426450310306200d4949419410303070b8540d00ba107203003507001c49151402c40000c0d8203851207141e038040c00c0040e4000d10302d00711540c1c0c40c44029036003030b6442d0349580d00c4c030f032000520550201d0140365207811420b403159222402c084a0488246e200140041c00c00c0004d49591800410400e001c003080c0d0040014083d1414088115104d008101d08040c03c0e1660500a41080d030ba44030050845e4074120050085204d80208050019001080c403011041494010f034030b048942408c05074820341c9603e00700216603114841c0b489400e410394030014400e05030310030701c000700c0f209002c02548491102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532979919 1250 532978669 532978799
    0x15010b0c2808030a0f0f09020f1203071205040308070818010906021f021c27020a180e0601150906030b0a030b10030b0405060406060815160302040f 65
    0x120165400481c81540001d170980081ea4400807524240c007240301407074584d010901503240c880c140c03a0034400309541001500300990050345d102d11a07488010f110240f40b291201505100304199400345601c140320a94600c00c03070401c034126400607248001444a001143c0c2000d511078114030080300c40c00d4004000c2e148012159001c1402e00b04551030f9116400d00c4204444801c000010b10501e50140000408001c1c4184003132081801d240c4da0348004546405060058581030519000c60b0708004442c4c1450a05011401c054a030700b0708101003038401c44002146000000100900e071000f99111341c1203090b900c807804e4059a54900c0380d41e4bc400c040346030800206028008083d0b02131841c520298481d03460b580c0b952100d560660703090f5180d41c04201000100041d03441404003811681000784841c3e0b000003800707000342031300400a094480004002900d130900039010341c0c0262003191030720040c69441d11065600c1044526491003120340700d0354800c0080b6405404101400c0c2101c40c0c034440d5490003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532981169 1250 532979919 532979933
    0x5011a130b0a0e0402160201020706110a02010305070e0402030a050106091706060f060702100804060b1507030e0a09060602060a0c091206090201120501061d060906070f0515010b0c28 80
    0x241200403c1c041c220340040c0f00341c0c3c2e4502c002c040440020f0412000715060b07000083c5803104a41141c3c09102d035a002043c51050002500c030300c056424030b80420959150782045941040d401c00e525089400072051149408080c0c01c2941030ba4601e9542c0501d60b5962001c9914203907100d080100c00c3d401010128155040841440390001c80181c101807400f41d0560122399180f041c0301b10000040e540c80d0a0004010841c094041000030494002c0c50415100054020600c10f44100074148140b0566500c0c16450300c0c0d65110050808000401c00b1559411000c0c2d21402c0407034001c0c50742c603d00441340490f5400350800c60291005c01034100708075a1940d65a0000381300404013607042c88a1585500d106a4503070048a02902c910b07076600c100094402408078010f200034400320b200c0e11042c0b091100c05d0701c441c02640c1d002038002003140600311313990030524202540c840448001581d050004038140740c4030300060421013034070012261007901481d8041c1c904c0340c0000101d800c0d9070328418440041094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532982419 1250 532981169 532981177
    0x13060c1d1e0a0f060207080d0f0503130215071509111012020d09030e100f0c1a1303080a0908040303031a0d05010c11071a0a0912030305011a130b 64
    0x11465590040150250002d44498010f80c0070b90003032003a050307090054a0b810b04c04c03600200b481c14010401c0706012240901030381d403180011010885c0c0400000c406000c1c4402e01c051240c1c015005000075589000310100544c0101002c0d1032441d1482e903415050300e220b11549074203076084940107801c000c00c182000300381d0019401c0b10041001803001c0220f4602d26100600a002803400000750002c0325140103801450780c0382c0003910038401d6a1005020540144030180d0800691401c45035603c020300d0a00d061501c18000030b0540e518040c20418a4100143d1001699010383c9941d0040d65500e00102c0070350300c131400014a5404281f10400000c0e00035007000214258020341448400500d00c041010111400c0c0c003540d95030344a408941106400c071081200304814080a0328040f410001c11202c0ca217540255036581c03034000500000300610458070080a0b2a428503100214103050400401420b0203001c0e001f05c043c503149060f925074141074111398501021901207081c0d1840c01d4410310f080d0f04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532983669 1250 532982419 532982449
    0x80c0a03021c0f0c1e091505090a1e0b0a050910060509040b030d1e0509013c05130e0622110a120b03030306130b0604050913060c1d 58
    0x8400d8456000842a0b070b420809494028090000d017840411900b816481d19840310030440e02e405032109040c919030701400d00f92107055498405548440e042507008000d0883c0191045501d44182c2d00100d241d40c01402503a003044490f103a12584401c01c0010041042d14521000301c6081c40c20001d00d4041d1001d01101480208000f64566066010a05280189008100042d100c884414500900d400f406c01c2000701e602c0d04505062f64031001a01c0b10482036500445420b020030084e45140f007070045080107071052a03400408950b5004060105d03000000d41ca885103602d4800842e011a150200d54810500100860921011000c41100344119001d0400200340c403030817104d0300d8581c400300800b00300302641d40301c403020304403a44420200c84400c20f07503a00c260001c00a00c17100f43d4440828400c2c0e6140788000041e5101824002803032441150700041e00500f103402080b110381402c12210f11103500807801400403d0060750125614999201e110a04e601c02543c00900c81c1021040c0c090108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532984919 1250 532983669 532983683
    0x3010e19030c06090f0b09060a0c0c02011b05070e0a0609021903021305120c0108061801030201050a0219080a0206061801140303040305010e010203061002030a020d05180d03050301080c0a03021c 85
    0x20041e6205d05c40302172103071001036494061107801c0c440000030402c09035902c080070b1a4200900c00c22000000c01c011a400c5019041101c416605400c0c01c070b00702c250303414556020044a410390340e140d46800c8541030890304000764515100c0009041d03862402194100000204407180c407407880441a0000d401400041128201000012415489100203000785009001c024084d646851000521881004110314002c03406141c07080c0c92401c11216184c103503070382401c000e03890300c0c2e50070780480c40c04c04400e0031115103c04020300f00060000c440014030703215280c1c0e401c0d01c41070383d00d003824403141e10036038121041c141e030300c0c000100150300610807940c4610030700909a07480c1950b0f81c1c0303540d401e48083d1000c4042da42d5002060110034502003041d40e540c07009a00207141410754080003e9154103001c0c0025050100c0014001c503030304151000c21b00e41440091071385031000301500f0014100c3d0030901901c1c009104d0800041502d00d490111501205d134000c102d18110b561001880c0010303002018100c51031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532986169 1250 532984919 532984931
    0x6010909030813030c0c0b0310050f09010e0403050c01050408280f030b040207020a0b09040501080f2a0315160c020f1531050418030e150a0e03010e19030c06 69
    0x50102032090008207c030f50040c90312401d0036510340c40703052540d50102c1d101703100381d40c0c0c105a280c03a003840803070455982c3c8131051141d69482c10183d80c00e104208035015154640702c2007208020350759010b03100c10a0110900345611100d060b1858500c0d20b0003215002048260203039900e06840394100d05450000617101504084455020034201c3c00c00360016100c001c000300c0c54203071609052060174010407444001305811500c4038186602d0390b000e0506958a8134502c0030080b058400d006a82412000207000c0714083c03800500c482080590540d909600108500350349013030300344142d0165030410f8000b441c544401440c9020400052040550011104018001b40c000c0c400201ea402c0c0100c003d4403580702482d0181d0342078030b89420301a00500d10603860f01403507207810b0341d40d4480c4100559150420004241d2200006010415100305903c0c00c41300016548503060781c4141550070414060b070081c4501212102280d8079240d0300c1001d424004036003480000424403892102d4071050241c0000910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532987419 1250 532986169 532986173
    0x50a0f031808030903010b0102030703271503020903061b040623070302071d13150b030618070b0c0619021309020406180b030112060e1e06010909030813030c 69
    0x781e419407080c6103a0f040441c4132a414142030040c280800c1c0244040d41ca000a10ba070003402002d004007802c0010b034980084d00d56010007c4510324003400c030101410700d10601c6020020041e61040c9007941c064010b0001140f80b52020b81c045615891740c0d1950581070504100c02100d420348410150451070b0400c191780b100c013100071402092098013942c00f800c0c000f404c10b50386984039103000f5000401b0b200800300b00640000849100c40115511a014400302c0803114503800c094108030303444030390500a51080c00450711001104c010240003200959014955840d082280780c0140003658425420602c001110380000d48400720100103406001070609102024039400c0ea041900941025a8001014400719800c6402c003100480c6500c5803460203800e1041d500107074081071207110717019540102d0020410a16401400560800508035202d00c01180e099940c0c404008201e2203041c028000041002606070150203296609621504030f652603150110f080c00700c43d40b10035000c0150103445200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532988669 1250 532987419 532987457
    0x70b0627280c02071d091e030c0726060f06060a170106050a0305010b030714030604020d0906090c05030f060402010e010c050f0d020c0a0501081b04170601030519050a0f03 75
    0xd00407540103013440c5003494030101841c4101c3c201124001101c0040103950000080c02c550036056140d285401c0c102100078413071039400b401ca000d49031341c0160000450094902d10701c2c001c10355440d2101030303001040032400e903488800c15559440b0a03030a1400145040c24444001d2003180103502e0b2464560004001c12080508207030464400101e000a00884440e8580281b03405010070320312540c41c505004d103025002285602401c440583d0200004066688039815101640d030b80349400e011558061910b1401020019021250141c0005000c0ba45040000c2c1c1224020b003528020728554907942c0055a034003e202c2c5d41181000081e0758041c0000302c0603c4585510075024005180c0c401d4501400380c2800311100d0082c0c01103454400030410740c0e0344000c13015080540d041c2c103d030005800241440603031007107030041c0d900301c0c81c80d203000c002284001800354101c0b80120306480b112901031162801c51480d0102c040d0096018800c4500810400c0071060b2a02d446403c10350245000030007102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532989919 1250 532988669 532988681
    0xe0109020a02160b070b19060303021c0201050105130e0a120509010801051c150902060c03030a0b0901030804060509010c0506180601240c0302070b070b062728 70
    0x4940c01160030400141c0400c51051249002d428001c4000c0c1410064513450007583d201400180080b00400c41000f611000d10024403500c8006005030f9889040c0030b0f650786260040c25000c0c20424203106480c61061046c903041c2e03400141040084407201448601a04024041103154024142113034002800742c42c2c00040c1142135201c0684411100b40090000d0505030b100c83d00860007041d12403489000c8580d108507055224103e03003060030b1040000801000c01c07020081d08004001000f0346243c81c000003562090b4000750083c45540c16070340c184803e81600703100c01065500140000e20000b4010009010140818501200e0b187d100e40ca80c145403203010364403900c003120500c4600003172880c00e001441c058416240d00340134009800340c4403440807820360400010041c0030f022000825109000d608020400100c0c0750380c40f08010f040c010054501034544c2c03071080c2d02c844042108101c80804000420720554164003c6684000300640d0b5040c8040700030714000b80044440c606070360144501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532991169 1250 532989919 532989929
    0x61305060d0f0b090405030d020703020a02030a06090b0a0204080c0411131403010b0d05070e06010c050307050105101d220501060306060812070c1505070b070f03230408130e01 77
    0x102c0c02d07022060110007195000f082c82802200c000c82008003160780041190491781ca003110041e502c140c0d0b41802c90510003840e50003035043c0500960740c01404529000205403a00400c40c00035282c94211300f1804a210340d10800889421140c418540d0346000d512160b80c078000103461510b0020f00e102104520b440d03540000000300d070007081203a441c3c1403d104000794070406555078490403d085e04d0340c599070300b0300d4032504d08030030045d00c001045a4411200c51505a81c0841202c0e1907a480d40f810501a0408840f0f101030051000000204d801418203440c00201c0781c614007100e10744513009214030801c50501001c0c18001e203c4861000640b0901c14017000310b02514000801d98101101070f810950f490b00b459107421002c0c1b120030b003c240101140412036800d0004011003e0420100b561903000e480c0d000b5000072104003c002210750010740304c003a480d201d950f042045096000280003c0e000110381c01c061001c3c560009000503004074000d000d0f5180c0c048071080070702da030740d4404030f6a10390036001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532992419 1250 532991169 532991171
    0x2071206110c240702120f0a0c020910080d050316180b040e0604060b030606040e04061107060b01120e0304090b0612070c0303150513021605010e0708150601090302061305060d 77
    0x3d032040045501d111600450144007030420300840407110310030340c090016440288540001c4001b00e99005507443e0003190707400380186505181800d00c04110111620505807940a2100c483d690184a24101c9200d00104403120700254800c4008907900c07074404404402c00300045202103814440c007c003600003052503090f45540c51500c4020701041e101e143d031000201d44014021b02c0901e695200588094400203a0054203030358550030a20090b02c882d22200014110002c0c00805011b179581140a1542080c0c0301c00d02e608480d0107c5100322401550550071682090105214a084581001082000041002d4100702d090746030040341000c10b0f05c120000c541c2d1510100b04060301401807004131120184850441440c0c00041011408189903030700450354000744050300200c40200004031550010b00810082c480f84031001e5444406000b03581e054410410301280048112030031a104030010382d101c00c000d0780b469082c001d4030303007080c480c89401c50800c15011405440d00740140c41c0900010344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532993669 1250 532992419 532992463
    0x1030312091704092007050304050d15110a1704210908070602010b030d0c020a0b0d0e010e0309030c0f15070201020a0b0c07020a090510180b031504050601050102071206110c 76
    0x40c840710b07518000705400d0817030414058900800d5010082d80c08450003520748003503c203182d180c04e0121018922466041e5484c200c2005964000300000d411041c00d0358490b50b40b08040003900d424030f1182210002c0020f10070388088400304141c01804240c660507410624143c0d41c90340d1601b0708040781c80e04005c005030f649015032480b520b02049070725105046400e00000159450b008035420075514021005000000030700d501804039586d11071007040b0422030080021800e440300c1f9946aa000c1c0407854400d1054214150051814803514034240d4801494084400130034011103805803c40c030302c02e9065000301031901c00419200c5414030f104c0e0300e5035071115584001901c1004800c0f0810303000545d900346004100140c1481c2841c0c2d03401541c0c08402030220750700b01c201b01140500011200c1a400d40111409050600d01c0400b445003e00e214a0a4602a030703210380049075503421903c0b82c801038025994005d4049185944000d02001e2040c1c01a031401003d9103510b40b8010008a400f08180c10a00f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532994919 1250 532993669 532993691
    0x411031b361512070e010e06180901050625030e0a0603051e040503030609100909050601030209060301140a020a0203070b040308040302100513140f06010f03110402030103031209170409 81
    0x820021020095840e07014240760f90f103000d240c4081c60007011241401016014880680e02a000e2400c185000903e030780d648203900411500c1c1180d001820781d029044001c0003242900e811000d482001d070000f15035001101a066000c60038407040841503082c0300c4449014030040e1503189409000c0c01864501240c81c0c03e1200c00070400c0f0180000304490b001401052000044003c0110b0707070096412500000151948907a0424282043c1d000c0e0b0030703403803402c0340442c2040400308000e4101c070300032900400d9a0b607401080c54241e4006440c03504180c0d088000207502d41c1d103154050074840585104072400d02c0b415aaa1040c12007003501c0a4011400080405c010140d04000c0e9014050f01c1450601450600851000300800c6056004084900054a411502e01c0c10002d4602e0380f0761074001c41e03029595170540040b085030b241c0801e0f02c82c0048400040028107003030080741d04070390f4035645081d000800104c0a5000706880c0d2402c95880800c256400a01c41c6a04040c10207414800d40004c1d03141410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532996169 1250 532994919 532994929
    0x8060103050c0f060a1d130f0e0309030705210610050306070e10050a051213022805090405030c07090c02010f05040c050118080a0609020411031b36 65
    0xb02c0009482640c0d4500c1040158440c00142c0c1e002040c1c60401000c143c04050110049403d440c10032074000500c1c890381001d25405070003040000c030175800d0400c540d202e01504580c891081070f01598055101c040b08001604009054403c1a10280940081c150b42d0448a03410180203071403107411100d1008040c0801d250030b0000076000f015600f80310b600f19014902145889100720581d40c1846408603c03a070b10305006800701d40070954008000c0e94280352041c2d084091139454001a8001e01c071116100601400150803046803480003040200c0e51850041049031584008100710303030f540001e11490090315000c02180c0040c10350200003181200c00c8240007402c45482c00c0c40368415078113140030f010110715100c15503015110700380b90000c94102c00900f1309960a440343d005801d00c0c0710785a149401d00445911106490703100326410f100050210010034024001a00e20140c546013940d02340d4900110440185041058980b10700100c08240102d00c2c50310740c211089155101c40000001d00e14608 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532997419 1250 532996169 532996183
    0x90c0905060d1214091206161728290a05060708030402240310090212070f02100207080705010f06080a030f0c02060301150f020f0a060906060f0806010305 68
    0x410380b004481004903894030030701c0d040d40107a20703014000000c102c604915541c00c11946100340103855001d01d00524070125070f5030881250b801c441043c411a00304210f62160700440401d160b040c40e0355143c0d0702c1f400d84101040c0d5109100b40280708070315812651052440c003034203500d103440e403d102c07541c00305826651440b20032601d8002d11070b098040007400550340e50001d1311403858000c0c20307403500d1307640d60f1021400c6005200d900b40e00f15203000208403c00a4188000d5110340e00c926040040795642d40381c0c403c240e001d28410ba52440700e2400c0012070884c8140044402c3c50341c18811100c0b000444bd01100490b84205801d890302d03a000a804070a1120034000d050040050a0003000002c0c545402c80d510382040500080400030294020100c0320320408a48802a4008000c030b51360356581c1c29281c00f03e200031101c0c407020903008202c8409580c000b1401c00042103d00f000b410034503000d42d40700030041c80a240100d6159558810205159824550950103414014003c00081d41141802864003413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532998669 1250 532997419 532997431
    0x8060a060216060e0d0c0f1a070201170a0603061e06080703054c0b04050402010504090f020d1506081f030213090501090804060e090c0406140d090c0905 67
    0x8040c1c0044426030b10020b054800726a182d190500407640c2c044005103100356241e0b03002c0c10a2803420400300b44c0c24090f451035400c40c1d242c600404030f10b0314015501c00c010300800101a011900090030808810880c1003816802100e150001504940720350302c00302104c542c40c0840c003106600e1001c1c052074000700c0c82000d0180080c04001d000203490356a50f00e603151034441c5003e580303101a008210465070b0f0a5602d69030181c40c0c204040510a0550030320252034440d5104406a038140b201c8440a400c4c54407420b80102d4060351503500d01170a00c0740402c054103504140f010700680c00c00640d22007c11910403a401c4008180307521050615003a0001c04041c009400c2c0300d41c494008640c011004070f9088010200ca9050718041100046103085a00404d00154003604650800041d8030030011140014010340d2440d48400c0100d10031502400b54503042210940100c0350100002d006103070080c00d000030900ca404003003500e05000c030300c0c40005803140000708817401c080284051000c90514010f1320f038404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532999919 1250 532998669 532998673
    0x7143009010617070b0405040c020708010f0c030609020702130509190503071a0f1f09020d0b04111c0f06030804060807031a130b01050f040e18011b0e060d060608060a0602 75
    0x85e04007606500710344a28450644607541c0c0d140040d001d180207012040082c100100200441c3d400e0081e0000641404030303143c40001e01c2c00201088005143c801d94000b941c001c3c1926040505d058802402000041c281030035178858420341100341c84400586400ca01d10800107582c4500c11407605040e07418400b140041c08020f000200030b1540c0285403540e9000c9503031000c0485a61b070107000310721701d10388540103040c04900010701c031400200e541e00010480501a02d080100750348500081c0981d0040c1202c62801034580b50580c0c0c1d1a000783e4104c0c0c2e6015040305400500680e8070343c2d846c4400c3d8056480b441c04031704280100040c1c181c2511070005481031080032a03640c0501c0d00700040d102208610b074490780c990781c1c00009115910642c1a01d03100d200c001d6002e40d03940c0d1198007403180c10408692041020350503507400022960306010380003c00445400b4841c0381e442c81042520309807111710401e60004000d020b1084014444e00580c00181601d1316400303103d08118040c040383d042c458000500f55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533001169 1250 532999919 532999933
    0x250e011a1c02040f030309180e06070c020604030b010e151c030e1f020f060f040b010320061b0106080109030e150913050601031404030807030f0b040e060f07143009010617 75
    0x21009c0414401ea20400a10301106150390710b10008186020b1600b000e840740507040b00203d03e041d5045405405000d291401c1044106480200011000e00103003440a80314100c4992000900624825071501d0004205900080c3c2c40b00c02000c00e5400ca030450001a44500d4102c11104028480f094000450100629a40c0b80c1074540185580c8184401005560751020058000094800441150000901e9240d6a150403425034020325a040f230800a103500c2e2040c00502030744140b0602c5642e580c0750f01d402c298040958100603203880c014080d2244548200303c40c0900b40c0c0c40e83c1c600500b1120002c070005040c02c0c00000101142c0b405400c011407080d50400340404280c005070040ea0150a62a000c1260000306a007440600022444681c02608001191281b9100411468441c042004002c0b000340c2d170722034040f03d22044901461281060030400703a8540641d005040c075400368903c104074001d4030814805900c3c41402c41e40f8842d965552001884030130000416406c506158400070010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533002419 1250 533001169 533001191
    0x4110a0f03020307030803040614010b22080d14070501141b03150402031b0706020403030e010f090e040218100302010f030905060a0509250e011a1c02040f03030918 72
    0x249484c5400090071010010001604100464002c0e840701c60250b1040c25080d6583c0b03114400303035045400c4400311558006056220a404d520410f02165030a05c010210302d41c00702d80680342c006103072490302003442c8100310b00000b05000f4010f103d403c240d00b252950071071a1107920b921550000160318a080c01c410400e005540755a180b400212000071070340140d40340c440c141c4080c0c0030031a007405c4182d50b41020580e04e0900013150f020b0320440340241c4400300d809110000440310800081400320200d42042d40500c24440031105031a40a80301501144082a01b0080b071460380c0812144220024040d1806004550b400004c0c1d80c0004464103041c440044159181910388000411480e0080e650f10000703450781c203040200c1700b0700b020940121201d290300d114054854201500840400f00342001c0001100c8104101140746a41071fa15000d050049000c11020700420f0001e0009402d5020302001c20041d400c45a080019882915620103207072034114402e010201d404d040c910740e586001c140540f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533003669 1250 533002419 533002423
    0x501060b09090402010e03010609061e09060f150201020409060b0c070816090e03070b04030503090607021203150a03021e0306060a3b07090302030f01090804090b0a050904110a0f030203 81
    0x1d0042c4e424285034101050100100740181000c4c0c1c4007100c0c031800c00000184002203409043c1c58209140780900e0f116803100d0016090b10150b1040c403200151045017084032011244c802c0e45642030510001d460140d0354050075003600c140340c00065610700c0006035180320304810040702000381030460250090800e00f6000003285807643c40303810061622101202c1c0448018012202c40c942c1c0182407424904060038001c185410403196089140304510108100500005500440326010340b40b503851a90340d45040b0103420207400c1c03416008419490040016039a80b0320f6403206a000c01e141c11905203401d0205445c1c01c102034011070081c25007507010b0009061442c4204003648201d00800400c05006503c2800410800031118030310b8102010301948503480707030b80d9108a80c001c4044811454041008d24221303081e0150041074031030b081004000c3da0b10710b40c000400f40e810041c0840c1125a60380701095400b4000c9904548008000308445030302c3c904210804003030003044150707490042c11030b80829 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533004919 1250 533003669 533003671
    0xa060e06040b01120c0309021009080d0c0201021e0f070f053106030524060d110a0b37170a0e03071101031109030c060a09210501060b0909 61
    0x2a0280342c40308582c00c0d480e400f42510342d07070b03110641030108a101d510200080c01000345250481c483d4924010340303120f1900c1751200b442640e420300044c0114007035404d03040c0c81e9003425a00c00c034194007a5440190101016907030303009000040c034000e003425402c1010780c142042e01d2078203d2900c20020300c0301403000e501e41e290105074030008142110b00340412030801051007202c441000351014101718010003000320200b59171480e0086624501307507a2030b030408001d101c039a0466035250422130300c1070300001103a01c4110400c000000035041040c02600c801061500f544140070324031000f10b0310403011400980f03201004200c0d018411050301c0050f0f20110080c03500ba807280c11103d05500f680c0201e07074441155406500642e03003490031290f80704c43d10f11f400c071114003030b009040303011a152010020885007410200e03617000b10018040c245030000c080800c8501e0300144094000c1224204010800348400c50409070034242040c20f40342c0e81c580d1031502c01c0c20b60300650400395404a083c4440c203407070b480da08191303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533006169 1250 533004919 533004931
    0x70f0b030723071209080d120504030314070513050405043309060b0307060512040b0613091407090b0a0302010c08090316031103011e05090a02090c07020f0a030b0c0c03040306110c060a060e 83
    0x1080d4ae4a40d0308045000c2c055517001e9001034034558040c0000309400500421030b21075080c50801a096464040104480041701c1c041d15620910051801c103050541ca034407025000d1004180c2400843c0414100b1616084012110f00e81c2e41e200c040428542001454001c000d24a010b6140111301031240f120110b02901c020060b041c51404038403569501252031006c0041c80500300000c00d210306024200d280b041c054451203005400d40842c0f121940c0c00390020000d00503244481a520b180d004688185400310143c48215042c00700245030795050089500424030000050182c0d81141031013402261034591044c0700380c1c500f040b104d0000360803804441d403210026034002000d55500904504240441034000e6220180008001e403543c000c8016029403402034800700300d8803401c00d060040c0c446480c0030142c03100d2181d400141440da41903008080b01341c2c16009a9051640c2c1c2d0355040c2c20b5414205685d0203010001c81e1a9180c1d0380200003043e4064000765040c480f0a140c1180c5c21501c04010340f030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533007419 1250 533006169 533006171
    0xf0e010317070c0b13180506030d050d020405090c070311011812181707091503260703050403030e04021201030809060c030c070602070f0b030723071209080d12 70
    0x10310014000c0101d1007074000c0425130881ca0784e5018002120310a04218083c0311003014010801d0795040c506031050900c1844090000c7c00005080c0c103041e01c0c0d5030095021030001d02d400b00408140d0f503c41f089124060080740708060340710300f01c0d40780c05001509010003031005e503071410b0402c800c250f08441d00794001d1a045403d44072404640f4000b2945800b10003814840c0c1900408001010800518050351000e903c5040c0d813095900c8111035801d840300c00f02c200d1010404a401440420741c80246c6040140e550104014030785214903456005d908402c9082d0003141c40420304100b4150092807980121508403800c5242c00d03001d00e00c407443c2d508103001c00707055504042021800f41d200c0c42d0841d1a5400d01500b241e0325020600c11031540c40a490040e0f50050140e08400580000740301c90f03c405540c04004845e0541e525210120b48810080c040106d201e04000c1c0c24280040d852001048001d0041801c1d4881c6400d0250181c20502260301c91001c0d9401345400b9003020740c1c4500748107015524020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533008669 1250 533007419 533007427
    0x3071704080d05100905011208040e092505031006080d0305090c1801140904030f03090c05180a1a010203040e100806280c0c020f04061e0f0e010317 65
    0x1060800750044425200b001c40c5001d05204041c0e0007400707102c1c00c8a041c40824086a80c0780c06075040d564481c45c000a1401000b0f000501c07071240140102035202440030b0407034140c0402d42d40c0c2084904480005012081000c10f01402582818400601e1140f48408103111003031a040c1459a00c0c10038104e100109a583d030007045514405000325018140020000e0042c4503a14200d10074000c0203100306120b50740140310b0100d01b820003d002c01c0c840c42d0035440703528604946000680207011013140442d076454508c54041801e03a91001c0e050f11500000560854614107120355004032001040c69002c203144a0418100b241c0e40082258207a802602c100222a22500b07001c424400180c0c2040c00b0600030f0100b000300400b0220b00f04400d41101403480c81200300a40160340407078040d4245140024244a1031901606000740900450000a040094016034900b84804000f11400301c1c140c80c5400080104030303c0400c0301503003000c4e012002503041c1652660340d07801c0f40d5000340003040c0c01c0c4000120b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533009919 1250 533008669 533008673
    0x3020304060b130605130b01020c150c0604060f150b04060f05120a0b01140408070302100c0c0801240e0a1128120c02060a11091c05010e0303071704 65
    0x241140b1540039000d01410700342c20403006064080d04050140c14011501e0351000f900500040c061080c0071b40043c4c0190901105040901401c2c00a0b00d402403804001042124500081000640c0c0300e07074003503e0005210401c1d28058020f82d40314802c06007071603034600424040440c81d802160b048803d0740c200002d14421101041e03506001c0c50034898003103100070003000020350740c0e40c04c04c0740b24003000d036660851112442c990306424003441c00340c130860794000b80e01030005042c0f03d40c008071400b0301030800b0400039000e6a5910031350046908840c1c010794407102409803d4102e1131122880c9010150f00c0396090781801c005440c052001404003c1164840002550040400341240d8600c00f030902c02e04500311034a4a6108103007040004d10f000074105280584984060344034140100c05c2d503601600044d294a01100702503c00d080b45c400069008211080c41965480c4008014000c0d4020564a503c1203042281c2181d403040100380c3e940d0000c0003001401644500d80d03004007211080c8917070080d140d074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533011169 1250 533009919 533009921
    0x60319180c120203070509010b030a052707140301020f0f0a170103120e10120c09051809010c180306090c0315090611090310180f140f07050a060302030406 68
    0x40c080500740000490012401c0d40003140c0d0001928020340869460303541c2c032024018101424842c24040c00414004180901465002550001d5100c2100c0d0100c4a20b4448121040c499080006d25640b01c00020800130001852490040c4012402141000c1108d55204594842c1900740385ca5440c0004503583e945000d0461034071400020440c040c20356031645000c02c2c100228240040115960003200b0507146000e107503040b00c04a55035980c0300312008501002000e40301202c01c40382030007100d06d40030400e51204448802d0104043e94000c0c65420000c800c0c2d42140c15403505801040b410220040480000200400c2141da000b800090f0a0700709040000000707240303800041000c0c03c0110000211b1704240c103d44080c034050300c001c000c0c030401e0b082c00d04000d1050f0340042c0d4064100c00c030f010700d201d0703d15031001316406e4192102c0c01c2000616550b008501190800c00c8a07050503407214500718240c1040b50b40c1c46a54154010580c1504110000328446e030030b48108010543c00100041c204802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533012419 1250 533011169 533011211
    0x901020f1b07080105010303081f060c150b060309071a0a0f110703061401031208091905010e0102030f0f10030b011503020c0706020c01030e0a110d02010c050d020318060319 76
    0x40f2000030011542c4034500101a1072060300c1000c0e4420020210010002802ca80f0368211160f9883c0d421860f003141c2d8441d203202004284c82c100956aa1a2000ca551500e000071403190120702d020301b01c0c00342000c008214004103108020207004c000c3c40110704958000c40391880750802c9085c014981c40203030440030b1401c0081d800042080303082601c50b2074407a100a44c5141030301c5c03080c8000580f00c02901e00c1128610021034401032241e2014060b10642000d6034804440180030314004901c0c1c803a1440b030071f820790340103941a0030711324901d0782080111100c45078010381000443e110f03501d10510395107450801e9039040c05840c12000d040c14040c0701c0d2501a42c100c4045c1c000c8a01a04c0c0010f030358201c00780d1221104442240030034200203540b15080e6010448150180e0f100e0710820207038070040148080594216812814004854216800301c0c50808c0700e10540101540110740d5002004903104101e11807550a50080c0000e10902ca4212940041c0260022050900296100b81c1da194107281d064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533013669 1250 533012419 533012429
    0xe130f0503130303122a05090d0c21030f050f0403050a0308060103063602090303040b0405030d11061303270e06150a120207020a090b04050901020f1b07 67
    0x2000140b07200e04102d524400104490003520b0fa0140c0d0b0202e50200001d90784020b06526820704801c4200c41d0002c4259040a10888503240041c14094a4008902c80e4400d00906a44003900d295040004038280500d00e1868080b107500800104411b98025003094002000d0a0030f002001c203040071385003100d034150340046401c407003118000100c60401406040007075450500082c240316002c210b900d080c540503000c614041810907100c6449803450481d0800390704214101503020030140700e4980d410009003001d451072030181540d507031400080524060b0710120340c40a00ca51551440c8550f80040751450f4002c0041001c40b01054661030308a03070125404034924400c180d83e042007200b0340801100d440030780701d1100f2407070666100c100801c106140c03070401e50b002100701040b01c1c80745607128150325981f00c001c0340c0c00503040005540c0040d84010300c0c2d801c841c002070340e41e1007402d5a40c035040c040c454100f5a400000c614100c1107400c1e0807081d1042c0820400d400c0d080943d0361030020703020000b0000070300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533014919 1250 533013669 533013673
    0xc020406030602030603010506090624040b190306150e060304230309010815030d120213090b010e0a0506090409050703150903080115050315010e1008160503010e130f05 74
    0xa07200e141610003500242c80d0507010398030300f000180c01410071900c00c6001d40300082c21226000050b5102e4408010030900350141c01400348000a644030628000e0500c500750740e4484000400c3c141d030f0050807505c00d603000004051a520643d04000d4004a8410030204165240d0f5543d030b2740c500380745071185201c140d00f49800f04031090004000c14084060004107509aa419030103488440da69030800440d42001d07903241e005003000012090050205a4180481510140c03d010f00b00c1601025100315900864190f516201425015a40229140c0010800300d4001d0145030a000208042d402122111405030b55030b5404102800710402c40e103001103902280c42c581d01c8082c21070020140600700c4080700070820300000815495610903511000340c00d281d40700b40c199652074510108403064010510b052120200c40c001c1e0a48801041545070449610b556102d800d08014008441d21090513176401c00006000510402c154200c034290841e01c4002032103514442c50900e540000c1691038010700d24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533016169 1250 533014919 533014931
    0x2031605090f03121e130603150305011a1002160302013009021906080402101b0b070207050d08040302060a02163203060403031a04020d0203061e1005030402010c0204 73
    0x40031007070000b80840c603c0d1034040c0c201030354100a05c000e00e0042048100368854640ca09101c410305c03a61040c2600365042083d000030a80d00d49480342100c0d034590030300c609180c2040f00074015080c0103100ba400e84800e40f0060a0640841c10016601c0d4100d020003410407440a5483c040e603a07109117800c6408030350440d40301280d004109174000400d40040c04074003c1c00007194100026400b1a01c1800b141d07501c1d242e007103066540e40c1c01c2211580304501c400041c802c100201d400200c19100c206d494080c42030344211094104240301030302d05010782e030000e440b94514180206c0040c041c1801c0d1011280e05444154445040000580c1000c0f10769086907030040c0300c1a400104a0407140c52050840e58219100301d00400801100303059140100c8a15003550281c00458000ba1195001081c803282c14880345a45001c0c55002905a0703000c0004640342d5900802805511701c0d04582c1d205010512010400c5554843c1e0003040c5103868003414070b007d12002100240c19039000c0c084880b0125802001040a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533017419 1250 533016169 533016193
    0x10f0c0201020f030a09051e0303160c23180126030f0c0d030507020118020f030a02130e01050117070611010b1c060c0c0507050609010e030105070305061302031605090f03 75
    0x1ca00e001d100d0b0314481c44510450b10110061030745102c08040e8049c0180d4540301c14601c0c4070b5000b180408046400311300c00e4100040d4844802007800310642c508415113004d500c4407082210b0001201c4101c0041c1c0c103101e00402109102d0b548e02c024003001926a40310b0341c1050300a142c1503014209074030f4008a0b0005010784c82c0703080490b81405075006500d08110544419000702d080f2640d41005e1a1700000b01200c0078098034290901c2052840c0041c01c444550080c0d6020410362040b40d84203501aa440342000c0502c0e600a0140b640500b1101807141c1d40200b50b00e03802d40daa2030851041609100c8140080c8500080070340003e1900c06002d0b02d03000744c0668103400754200070306c0c945e02070780e02902d0408102c08480c881d1200c125400e40000042c244141000c3c200101d0b540690416414001d9400e690b0b07209440a00034244140c0c0c090300c0010340751900406000000e8140000309221510400c1080a4800101c601d0100d0800501d401906d84071740401150318920305107407040d418030400c04138500d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533018669 1250 533017419 533017427
    0x181501030612080c060a0212151c0311010e0318091b070b040c050f2b1e030807020a15090c0902070b100b16080904060f080d0f050405010f0c0201020f030a 68
    0x24160200c401122111381d0394444d244224050713404012385415000c2c01003946012034004030040040020803066508146400c150407045440008a0104142c550041440c040a02c601e503a0603a01d24040e51409030100050340d0941c0e000c1c1c40b118420301400e000302e00700f410000f03a0302c14403040400400e03603201420300304001c040d10100c8003141c4035a815400807440341801494945007a0015044410140c01e0b400c0072032051012041c11071207100b00030300035400310320b40000a0442d40241c403185210082c113030400402101005000c1015544402c54110000c1c0b004000c2002014000400151241c1035142c160300144d8141c1c4070b20505800410340e2003d0015900317240d03006d400c141480d000c94541c0c80294003818050031402203951800241c07890081000e0500401e4080e10060000601a49841c0c1c245904207507600102c0c0726a100c1ca00300c85071290410016074800e80582080c034189454600000d001d444104900fa0411540360140400c590080013510541d013080c0058a40b11807000c3c2d0020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533019919 1250 533018669 533018677
    0x2031f2003040c0f1203032d0615030204030b0c0304030c0f050c01030b010e01091406040302040c0f0f051204030f03090b011707050a03030503072709050f0618150103061208 76
    0x5030301021001d5001407410701034a003074411500b20039075917282c1e0815520700b0f90041c80f0a04224008082000c4101d1420703096007682d000401c004840000d081d4202120b600700ba001142d60141814130400c401d201059140c086507610001c2049072569a6a4600c0c0441e15512800b000414201c01c01720450100301000c914403001a00c2030307804101030ba0582004542e4020805080741c040360340001305004400d05034542840352900503001d035241a65030390114046a03901c0c900780d03002903040500105040c4d80840705075041c03409032030464204009207181848441000e0001000c2c40324040c4500050f80c00f03908203650703841d000302050140d90b0355010019190006446e061030030b070080690118092908540e14010780b5055510346056545190055551011142c00c20030600d580400680c3c2c08090701e125032000d88003881010440b4280080000007014000e0302d8107208024441107100082d10311003134a0350241c40d00001460345061000143d0040441d0b400c00d940c0406004041c070188144a0020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533021169 1250 533019919 533019923
    0xb070c050115051f030b030303090a050708010b060a0305060d060603060b010e040e0303150303070b1017190305031306021303120f0f12021c0608011802031f200304 72
    0x82c00404405a000c1a50207240d0081c2d03a4008002915242800c82510542a581c1030504001a070701096400080c074540080300c69501c40c4d444445036004000c020b04c40b0130010401000207100e01c00c0c4180000d0351341e01448050310304055541c0c00140c0c41d6520915941c040c0c1da00034008000098682c10090090140440e0ba2030100d0000850400c103401d0500c924401d5040032006507040d500c6103c2c0d806a0300c1d000d4001a81d261000303008900208200f030713103018005c01c0105003416000d0720707100d04000c20060045401d122a000f60036041031020303000e40480d124540c10b00d0000ea1b25651044c414112120604000e09110310101d1034450f2498252003c000740c0e801034046060f00d5a84a40840ba454181c0c4018030008502100c80c42455020700d18644044540580141c00c20074510070407902018031042c0d00f240e160300c2d4041000034290a100d0145842030011011030059070b5500400e80d104003400445d41c0c070381d446030280085c090440d400081c0a16040741040c2c00702d1040000782100390016a01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533022419 1250 533021169 533021171
    0x910090f12170705010b03060a020307020105070f020607081801090b0a060b3a020c06041202060c0a1101060e01030c0e0903030655090c0221070b070c0501 68
    0x1010407400c2640d0320410409500c50365403203000140348803445054020743c0f02101c0641d22260414040e0307405104951051192107001078680c0340051000b42500c0f1f01410750001e0250031003032400c4031a404213880341d1110a50506c000281c403108104611803200ca03a4405042d480c2090440030012440d0b0b8030740c000e00034541d0900030a40c850229240b940f1840f01c248094841c580c414050300c030400002200720b01641c1c1264400202a404d010b0305a03405160f0916594128100704030030850002698400740d103070740c80240403528254096100c54410041e950ac148030b402c0c800000c800400b50031200182c80e110000c8011075a480c0740c800d42070364140c002c04150607a0a000140c13040000401e580c8186030080000c00369200ca108000304c0c49900100c5092010840707006810118000c0701d0200c410344c1100c8441d500142440d14003044564550007060815081110103103d4903800a241841005075800e8070b80b0340702c03034135003896171034411090010420300e89a010414041d4000b800140a00e0041c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533023669 1250 533022419 533022449
    0x6020105010509010609030201211b0305090610170a0c0915080102070b0708060d06060e0105040f020c060c0903150a15050d0b010603110409060b03070e03150106050a0302091009 78
    0x4101200109028480005041b0002013026600c41d450095081000ea095050414021400c100c1030f500803801c4039210815948060399140e501d885840ea1004034200541814181000061442d054912070641c80b41e503416408807210703e041c0300315445030754049441d20300c1d5561004050040d1400804004040780045c4000901d85418021141a1603100f5520f00d015500c041c01502d2072031000e072402d500407103000805400101a4400c3c10040c145003141e415056142404001c140c3e4280050118001e00501600040e07407070001396950040018441c990710340c07149a0100e4074041c02c00104078130500c034000c14490f008200743d02c0022210180b01d502d03090241c881081c0118a484d200d07000386036488000041022611030380c031a2103500c02c25100c4d1850079030f4580810050b05e10680248a03485400000e000c281c03a04051000b108290036409400e202d1101400708103002c505114070000c4c0100003aa0810662082e8110350180000a1603642504c800100080804170107000d10350504036491 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533024919 1250 533023669 533023679
    0x60902301312030b100c1104060806060f0f030316050601090920010504050301020703360e090118050607080c0f0702060708040b070f1b05010e040b01021e01060602010501 75
    0x90100d40c030421108032503400005066a902d1400c80880c6802010542d80340030410b0380d6969a500519020296551610641850306044c5003424081881074400d9113400c004000d0150085011948040d0840b4000e40800c0141d000c600502c14402010340c1c140400180f4040c003a6481c1ca8003150a402380e01101c0c8182c0e260003000c800c80b0700441010704112044840b400a410740140c81240131f030018549981002d41d500081390990708502c80840111740e44040000c078a0010060610b07990881030030001a0f09000d040726913064085016000800207080006000c00c1025001402c0308011013070300d030410080340c0c188152140b60980d1131800250f076243c007042c0e500700e505090715035015449070503900c7e0900603400c004040c0c1c07194104960141003400009141000000a803071401c1c01054030008510081c90100140d42c400da0b01e09a50081d149000d1180b80da00407a1030515036000d40d0001a01c072090b00c0141d150042712111b0400c1c1042424030000800e406411031402c40d039064000384442d03600c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533026169 1250 533024919 533025007
    0x304030602030f0103201804020102150c091e15031b030c0c2a130e060c07140a0506150d0501050408180102060412180e040326130b0901060902 63
    0x1d021b2850380301d01a148807100c0e118018130201c1d08144140102c1d45424014181c001c44410101c600340941100401c07458028180b0000c0c45040d05c3d025141c5a5002c0c0310f000006c0c05039450492200803180003c40000c803801d84401c2c0e074020120143c2c20403500c07803a2611801340b40d50300018440c041c1c0c6c0a110100460807620b5491002220040314140004420000c14040611224840c003441a51215140d41c0007407411310416008580300100203a4408041c11701450941c80040c3c050b425510401400022810100e01142c005203685039a2050105400005001d0f06686201030035551900081c04100a20b4030010414002c00910010301f06e00254010398860404440142510805003402130600b40305c0c4411b800481c1075454140d1100b610b64000d002402c10868086021400c0841d20280c00750116441d016420042c100d028620324010315040220000c00380000e140c0003403030001c5002a9403e4021401800380085c085440385a40b9103910b400d4030182c000b0502d00440700c80303214618048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533027419 1250 533026169 533026223
    0x50306060a080c0c15042d0605071b050607020f07030506060108132a0506091305062b0b0a0e1b01051c050a05090f0604030806040b10020105180d200304030602030f0103 74
    0x4034841640300c0300010b88456009d480024000000c000c0c00b2030f80d40d06494441c40c42c45490502441c010304440c9451000646802060702449246610900d02040042d0001410503403200c001c1c40c080a0725100c00d04401d1014850b00300c0100681a08040964124114440c82c1d4881c4a4101c90a0f1101d5549007400302d288110210241c05c548044500020464903800c0340d5042040035001548050308241c0d8110041c00d03c4202142d0301000e80402000c1c00030310050903820020300b00d81080004000840d00d5541d00018049085c02e00c030410300516580e001d6030503030b440d140300b45024841d91031302500304a0050000305c410301c800070324200105842c81800105060605802c00080c2495141e03510103941e0414020401030740291140142c189544819203460080c02081d00045040c0c01e0140249912405201030f140e02e680c44404810009644240480030007400d11a031250b520f4821601142548540e03080903012600010a015070013484103c0b09048a0040c140c1c1a00c180c40c0034004004280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533028669 1250 533027419 533027483
    0x406080307030503101a03150f31060602010c14070f0b13050102070b04110922050c120d090e010b040b03071b050606010e01050306060a080c0c1504 65
    0x1005110300c100090040c4011504070119940f5821510b0742e540718400d0000941241b02501c01001c828492807541c24104c0c0751405404803202d5202000060105030000035658030b5503010070b8441e040c08540380c102c400d4140d0b4006415010301ca10350712180060701900d04c40007020001101c1d4803284070310724030f0401640c1c0b2259200690207603408007a251440400c1008d00300c40c80409a491800c40058030920061580901c10300f5020010304e003e04241c078446010781100d41c0211011410003503240002c441110403000307a40b12001d0303d040b60341401032509141842c4941c00214480300e03030047c220700141c030701c04a02c903d5a031040072036210398202221280070301c6440e5000c9014002401401c0002000d55440406031400b442c00c00d81007400d03642c000346030310819030346504100280300455a00400c3c9900050003820b0051070f60502d640812424811b500c0359004200411001c600a401c1580c21a00050030075807c036410304081460403c4001c82c10b66080f60214802090080590b07004042441082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533029919 1250 533028669 533028673
    0x1080c090414060f0102070e0f250206040b060301050f010306050a0f06120203071a04050d17030a060e0115080c0d0b120303070f030504150906020d110405180402032a0907050c0705040608 82
    0x611440100550349e1000ba00244080602d5800d402c1c00212140c02d04c00000d1840c2d006091130300301070030103081030303807001e800e0034003d0741440d042040e4001d1304407000381100d030711140010ba1903131628114030003010710141c0109140c0c2800741c0040e0b90044203d4801c01603008805440c00b0a07641d89425403010a0304050307040d405014801040340b8503045202068403130044004480781c1410344517000c03459108035210310031196030300400d0000040307941815001d8500031007c44089507900d0303009005a80f0003450880b03051800100308036141c0307554104440000300500b40e64814111035110701c3c0c0700d401c11240c0900080d44211144420791203030042900840d04030111118140410a43c440505141d140540f41c3c01d03002c001100c0d0300c4c0d58510440e0031803680000115100e038146800c0003201e20141c00e001001c805420140000f5a8004c07170081d003c5076034001e17030030502c1c210310b00b501c42d490aa415509034405c0e01882084181604400141107446440054502050b110401c1000715101ca0185148075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533031169 1250 533029919 533029921
    0x81f0e0717060a0216080a02032a10050603100b150c06070806101202070303140106090e06040b0108160903061109010206100303050a030c020307150e061b0901080c090414060f0102070e 81
    0xc61b10402c0208010401d900c1542e14020203000030a0784032607164040d1080100d00d03180c81490a0043c080c5041515900e20240024180900041d960760520a41512201c8c1c0c0d4044000046c0c3d60741c0c210003407038240123082c240c803428450039103500c44000310b4100c00410f02d07840c00150702e440c051b5800c000052150700e4038985402140c40c1c0328001c0d00a003504405160b510300d8242c03a90412281040d00824855460300900c03070030030300c1c2104024000b900f501d000300e090a4100c2e000f60303001000307180d011139032242c1c0b401c15a0544104545084031940701030a16407400c4100002005807100414101c9820303000c8801c01e44440f5030840c03a9001c148000b13800501e0501c20803582d9071080d044401e000d01144100ca0070048261580031810020014a4141710b585126502003da02800b070b44d40c1c055082851181c00307649001500c44a8400c088940d410040080300007902101210203603140702001030170401100c1c0c1c29100701f6a046100780c802d5480342200e038400080561001a50009a13100c13a04403800e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533032419 1250 533031169 533031173
    0x31e0510020c031b100c03050f04111804080315010807020c0103021b03040b04142b0f1e030201060b0f090d140a030e01030c0504081f0e0717060a0216 66
    0x207410484411000d40010041e591820b95801d0038050070115110141000e0605c0c00018070407141c9400a02050504020402a030050080200c03588540c2010104034a00c07000b000007000e2440d034069000f03034040900d040c0024080d800307010b140f240310304040c942210240d500040d140701a08507000c800582c00f000d8002c000754820b801610440714280031106000d4134107101c0a085030070907040080284004142048281c46800d419082d404041c1c031032406a501d2643d001d0f540425001034400d8500d02c08440c0410441d03010300680005c0e8120416800d505a0b0312aa00851307142d95a00390019800c2001c00300314540c3c15000c43d5071140a40340200d01c1c261050060090990a082098504840c499424040211300b4080c80c11824820b0b61840c89040180d00003504454546040f00d04111091000340042500028500e6405000c070781d1403011060703803151090242801d14000f1681c2d001c0c5070000a600e00071010340d1301c07002000000f940d0480d030b10104001c0490090a050102d0045034101c2480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533033669 1250 533032419 533032421
    0x6040201031e020706140a060305060103060e100603061a030c060403060f02040302090c040306060f03080301090506030708010c0f080109110319090804031a0601030c140f070506010f031e0510 84
    0x41402009022055240d920802d4080360000d00703003604d516444071817030380002c00300c140704aa000c00b04550800030107003035031a110741d90601400000e0450383d4500400680c00000c000701c0c41d901d4000d801c140074160701c078909403014100542c21a00111640f00c5529080d2034007003194100d150001d403000781480d18503140c5501520403059142006a420440800561181e4850a1054248051490b82d8900d54940310049405aa000704002400407105200182d04202200c0c111010340e18041504d850340310019080c200c2541c0120740340d40c61308194507c1c080c0c02c082c100100c00501e44800107903a9031441a807040d03e500d0014008118001c00c009140c500c0a070840310f402004903900012500703a0b607a5100342943c0b103070304190346458410390081c1d82200f200003400e82c4690f00303280174480000160f02c0070700f800b09514196001100d010980c01014100103040c0d860080e005130490724903503907522003d582c103000760205561041c1c00d00b045020b0440ca03c00210010f43e4840c000b4148004070044d010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533034919 1250 533033669 533033681
    0x105090c061e12010e090f0a0305270a180609051306050c040b03010b04150c050717030909040c050f1008220f03021507020712080304021906052104050604020103 71
    0x2004459040c428040421034800f6054081d101741c0a0005080c107042040034642050200403205650000c1082800664810b09468046018480d0501000001003800101d000383e085400d8002c4c01607680050100306030b484459101c015080100605034468038001d082c0e0380b040700c01c3d60001a5000608000031000c0d400603601c5135180341c0041c180390b00c540300c09402d0303071084c0d01824610002250901400d48803001144032183c250510303a095030095500c0d243c940049105d03041500100404008002200f80111070072020020103010082c030b018585404040b840380116402112086001091810300c42c4030080e00341c11303503203070300d1407958411604a044048286000901504003d1403c00155941c0c0c003901003244250054081211100400b00302103c00030302300001c42d801100d0801507101042e000c00c0c00701303400c0850301c3e03541da44a0003c82c0c03004800808080340420240d00008010354420702a02034282e4028400c0d00040131718514110f441010350b40a0601d8000b2004600158002c1e0301c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533036169 1250 533034919 533034967
    0x1d19141605040b19030b010c0b0f0702010f020a050d0b0a08031b1009060c2a1403070b180c03070b031303030b031b15130b1803060c09030105090c06 65
    0x1900e41503c0d0400800d268006160244101c6688030261008a8044c014002c42c42c0c428a0007000240301e0744c4a0407801003000c3d01003c0c400a00402107200c01d8402e4010b2a0740f1044400c0c255030fa540020300041c041d0f4007001d14036101521745510648289440080002115003400c006c501b80001044102c0c1c1c184446d052840c0d0901c1155004407000219000b0101c080d8055440000c01d04200c4501801400340181d010b489001e03c641d0220504020001c05a1920317001a444d000d080c5000c45c01e5403847c42480c802400d5407001c00200481c200200c8031000f0141d00f0f00701500c10003040032062594810480c006c1507500d00f014000108824001400c042005010340b8010804000c80c001080c2032421207143d000b00c40e4114800d41c5120f0401c4400c1c88012040780d0351503882e08086c3d0050b034060040c030b030054400c0c3c03420000e2409051603c1a040c00500d005c0201a0b403000c1c141449040801ea0119520318025401d04e40000d04104002c0b90190300d003440a0140d5103885241d0307400c54201c0c05a0300003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533037419 1250 533036169 533036177
    0x4140415121a01060c022106010e07030c030e100e07030b0103050616020118060c05070c060504050f011b08030403051b030904140f06090903040e010b21042a1d191416 73
    0x80203114280c100230b80341c005c0035007600c00c01c40ca0600800042c140c8101441c600306050070b100d010000d1000005d2420307a50041e25900040e40c072280c1c88424105400c590020f020340c0c020720000700900101141d0680100000c426080d54182c2e1103506034245c0b06640c0c0f9446118080c1c10010002c00c8064000382207140a5182c514946403081e03681c0d050942941c1c121034002280400c06101c5805c01030340440d60714009003800b55286100b404094804030401900605104010020a08040c0070742c0985c0c40702c0a400ca262085d1241010050759250883e0420b01e100b103040201680c0c9201041d030b1000d000d02003030407066596641b14418811813420103011001300b4801040b00080075400880030601a004c00040300343c2d9050100c54001e00c80d41c131101c400c14122080b50074800080c62401441600e250241404600c45030465541358500c21540d00c88004005180f07400c0348215240654203118900303e00706030b0552003231184030604075590b8100c0a0409000d82c0701082e5003008400ca41c0035400e1309868 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533038669 1250 533037419 533037469
    0x80d0f0504030207080d0e0604140109080708150a0522021c20030f190804180b04060e100501050c010e0703082106010504140415121a01060c02 63
    0x10218121502140c06034016001440103000759281402140c210641901d00b0410100e22200024130f284250b1042c15480415844900010b90041d514240104003c405407005d040e41d481c40280c0313401903000107038009007017200080ea141000744641400b45032040008031101000d8090358a0400c3d800c1002da0f4403d201d000010717801b400d92540c405180b031003003c05100e942c040010b40c0d4400c400c035108481c440d403c0900d103142028000901c2c2e11014041c0c0d840024100540d0a03c1610b070310543c0c21014140c080b00340f11940c000807a40000240c10002c0d5810425266554010401e108007504e905000f0280d10030200920341c8100302801d80c0f01502c80002a031001a01041072a0a0715580101c0302c1140202e40c03441e1001310004004803c0140240e100c4841c07910000003415842136000b052103070301a02034540d41d551240e0b413011241c081c09440d00c03590503854107a070008500c1c2c2c003007084426003100c0100103100c038040c00500307048410307503154110b01046a0b402c00c030142e690303070080d40079004100e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533039919 1250 533038669 533038691
    0x309060e040920150306030a120e04110a0e010f080606071b14102a050f010e0c04060915060e030a06020f0310060e13054b13080d 57
    0x408030070008410f401558294614006001810f0b400c1142d540c0c280d031081c07041080e10340380460180e1324a41d0108941807441c21090046d1011300d401d0940e1074001d89003040080800500100074075290320b00f9201c485014007400011200020010000c0c000600702c000401c5440c10031401402000340705401121a20000304c0421410720b466038402201c41ca100404601d450401d078140e40c03418031240c070380020940d41d800d801d40000a288042c0da03c5492042012205124061141e80c1c1d032840780341c000340500070280e0151a40c52000401c440d2282d840c0840025804955210700b00e03a108000d6010f000103450508181d511000c407a01c0d10390140200f032070403c0058918402014028102407005880e030a00c00c3ca84980c801c03442e0454814490000200c00c4140d0321108410100d89250f40c010a042d50f0b15010340c49840340840c540c03508403000011040b945180c084140c910103544603608985e0a40401d45070301c000d041940c00e1802141c100300d0b8503000c2040c210042c05000c0302428049401c408071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533041169 1250 533039919 533039933
    0x501050913030f03020c0f0d0e180105010503060f09070309050f0a11040f150305030a1b0f0b060103060f060522060f030e0a080d0f0f0e030a0309051203070215010f030309060e0409 79
    0x10711001c080354001f04c41803e00c281e040340c000c90b64802d090b50051520b06012b41c0c5144418010b028990500801100252150307a40c0f10f40c1044103134001d02000e496050641000c0c015102d0007404880703a02590b884085258800507804080c40c0c0c1101202003280c00c06070610009001018002140c581c440303104289140385203e100700114031030002076603252550034004111389155104003d032031841040d520089007000804001d0181c0180d00b82090791540310040e4020145940aa460540001000584560000090000118846038080181044028240c03001c0000d008e1000450706200203044054801c1e40844942c02450089400a0180303455403075040e04202c007088680c607251600001d0300441c7e801142e62a0442e0b120610440180b888165264054442e11030101540d410440741031200421000110054100344035540e0305109400075110142c2400029440c410907000080c0510748043d124116505952056249802c0a508440361003241c10810390041c2c03210a4800072400c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533042419 1250 533041169 533041183
    0x11413320901051311040b0a0f0b0d0e03040f0b030a091a060102011404110609030c0a0b030718050d06021b070b090301061d1305030c0d0c060501050913030f03020c 72
    0xc80c8001121860111500e50035030742c001300305114143c520340c401c9001071a20b50101010f082e0845020804d4060789000c203d010761664010f4404444280d80000d541e100c500051042d56801c070021711401100703891550366072080388103031107020700c012408000880c91000a103802c80d40740400403404004a4030f4024408130081e450240301c000400c244001e960f024480c500034281038040c144821315054955011140a81c0e00300390040350300180710f11080d50180404414540000c04c0b40440c01d0f100d0455150942044a60401244440385180000c201105d441c0703089820007407403000c40c100c0b80d603038103070203900810000405d0603105100d82c108040300b40b080c00e0280032035081c59600c41c0d0343c3c10b0406080d203185a012400d41303d41c0f002410088a0f83c0a82e1541c0099000164000c20300d480c60315600c1c6200c0c00300509014081d80f1602c41102c2c4c0c1c4a40f441c813115015800500c42662510200800d240303040e911b00e4000304080d0004000603014560761003403500c280c100107051010020b0580e0070152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533043669 1250 533042419 533042501
    0x1005090d020d021c05010510060f0915030608070e0a180b0a0b01030207050a050610060f02060a0c0c170705070603020307051603091205100e01021c2f03040308011413 73
    0x51a1410001e400b18128041c0006140c10718251000002d2b034030010b04011002d01030f41a0a0743c1e100c1c01107114900a412401c0100170705400c03108619a07134407045508800030744800081d2030402c004800045107915440c4003094000003a40302c6a140c90014900a104c2d00c9800c0781815000d10403100410400e0105d40c05890180016201340d02d080201c0c00d495004076040b80080c0050090600c8a00b540040c003180d02c58000280081d200c10b2290003507407001c40480d401444400034503084a45040c1c440041c0c04954440c800b128400382d11924190144c3c0021124040014030911000d10000c0c418041d80e00340c1c03806030800031042c1e92104554002054509410340f0251701c020441c00302e800c043c0c8180d02504038224021407d160084024800c1f05032901c0f0440142920780304041e5544440d2001190b0740c10345044d401c2c800e508404141c801a41044500750041081e40c4000640d00e2060003003610850002031030f0040c1e50b070301312110000404542c440d408080b103809261007075561304c00e08520b090030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533044919 1250 533043669 533043671
    0xa0c1815030f020a051209010501150c0c0b042403091a1005031002071505071715060d09060c020a02060301051207150305012102011e020a0210030b1005090d020d021c0501 75
    0x1190046e4401e6600e000b400034401030b8506401004044202d480000c11b014003440c1407585030780c0f24208500320a050703400070040c0c3d040005000603080c0c00340c1c86010701140ca004025508a556503c00c0c1c089400440c8003a0222581d15118600000c0c0b14030120350010a485501000c41c5e11600402e15008076552100c0c1b0085c0e00280a400b8000044800c407981c204a000500180c43d090b0340003806403407184050080700d00680040703007180680303958180b03804a014100640ba0b82404001c4001341140020a0715034a00c1d01500d03081840c07000c174000080e02c1d009011246183d29150502542c542404503076440350082c4c44000c1617002001500707402150032654081015410300078400d2000c0a00c0d1b40b05200190f4190b802c400603600302045646049400c2d03184c50080e004400e080e400e101d03403c10004e51000040402710051500f6034411250b0308000d6171000d8240a100005807418820380c40300725480700007410103000500c0c0c0a040382c6840c51014260307200225118140d004e01c07007403086007107a107a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533046169 1250 533044919 533044927
    0x10f050a0515031204060c150507080a0e03031501110a02040609021809090d050310081c09080f030d0c02010207241103060f010c051c05030a0c1815030f020a05 70
    0x1000e181000405405403c8024003c1000030100c8a0b08500c1180305420510582c180348000348035a4040e00d00200101200900c11841d00c2c0400402407807044401080062901e040114103850010580b44180c0811400e480300500400c010b5514030840849030400c0d01c10003a02c2401601d40d40a90340080c04813181c05a20394030103916000c06c203190078807030034003031f403a06001c00101290001d150080b03103400342040c550f03a0b04c0321803007501840c2030782c4c001c13aa040c4500f900355822030060001204010314540d4802c2491600c586100b5203030390110301c8108940d40144804292109150300c40107000c80c9500006140c0315560380c6090444050707088542c031140018134074421005150080394a40c0e50702141481c65407801a00044032500813100d010b04202071a07100400300803080001001800d544c40084200b0112454000d100780d0003152003940017410000004e8507030f030040f080114100c2c01da5044608003801c042d035030901000303000302180c101a01c1d40020f5281000501c000c05159005070795403552 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533047419 1250 533046169 533046181
    0x60111031b0c043605160618090e0d05030a18030c170a05070818040e010c11071a0a0207091409060f09030d090204090b0f1009060e0117010f050a05 65
    0x8a42048450150300211070340c000700c0c4c075641e0310001c8000c8400342001110003680360401a10785020014000020785000304041210703138104202603801c1d600c03003961580c0140c4072550142610091410203a0baa170180f0400801c0500400240d603021a1030a000075100d4400b0111082d03191582c0070540100c0c1c000e003030300028071941d907034035002102102c940a03140c1100c412008100d44580b01c000341c240040030503040918520b01c00c0c02c2030791190080040c404000f5181019008102038800c2c000032038440c41801d03004060101c2c901c0d0413a07000c0401580c030007402c90b40820035584000c0c101c5003140503480010501d01d80d00c1c418445004000c000b1000d043c40c02c1e0011502d08007018014240559601040001080000044800c544181d21022818203454804030f805094039a0000700101c0409041200c842c10400d5041d108602c074944480b0700c03690b00c400c1402192010301450300b010300e04500521a010040c030045c0c82e44900382000140d2401ca580c1c4001c2140c10654075501207540303400a20038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533048669 1250 533047419 533047421
    0x1120222030b1e151201050f1e040f0201080603160e010e06060c0a06150f171e030315131d0c01050a080114040905100209090f01030308060111031b0c04 67
    0x40d1010040300d04101642400d041a0b8150200904080d4141d0040e207101d4460317114a2910211551040002d0100d401c14195801d90303030300111400c07444070803a00e851200903021892028000e503003011600503070803036a03001141c0d401001000d41d6018412441c88140425064840e41d006040d00840608254100071440700c15070f00191406105038000d21441904203030100342400019440000050251549186004851000da00510481e00090310024840c1040c48503464610080c4007500c0400c0048000c0303145220b03110940c51403580c001d10000d41c0b80448d18080c2c24100c0340081c80c110704001022144001e403014103200c03a84c0c990210010200043c410020003030303090310908006050001032400144100760500c01d815810085841c001c0e010b0b11180d000c005800e4010b0252140052218031207800395200344921401020507000281c400b4805454640c1a25815502c0410315154100119070900450350101000e000412400d6040c40311141d64070301c00007003107015159060300c100400c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533049919 1250 533048669 533048671
    0x4060f090504030f03050f07031508010c02070e060102070608181009050307020307053f070b0a0e01031803030c030b0a081509010218010503070306050a09090b06030703020102030901120222030b 85
    0x11300341420481800345103094074107000d520a10f10716000405204484a82c0d08006083e0310100c603552070000c290050603408240c45055845100715940f1646541d401203944025510076100000c140320080b80e00160000ca901032040c02c0507049644205076592510f0071105d0b0307600121170130b038000134003042141414012140200f6044401d0701c1c82450007804100e6a52076200c0e410000c42c404545c0a1070400b48541e510080204041201c0919440f20390f0700304203622010125021808566018040b03600c40c1c021402c4200d400440318502c12201d5a00340c015102c1c00404001380740e1210140700158407400500002061140002d0002c070005c160b10340c4202e10080d080020507401008044040c90081c900c0324a020020700e0116603981d1150411801091705402056000c45042000a920100ca8104800081c01040e088035161a245d0825507140e156104c02405a00240100360096014a4208042d014000009840c19010a1080501401881045401d881074100038002c2c4942c440d110303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533051169 1250 533049919 533049947
    0xc060503010e062d0a030c06090e0c030601020d0c1112010c45150f08011202010909020d020702060301080303180a05210f0c0703020f0303090f0f04060f09050403 71
    0x440304001d004c140d00d045401e0702c08240e00308200880d41d4001911113420700300086422424411419407140b00080c01003150b1721030203500740034000c0420608500601200e0060505800800014401c50310540c3c2d400b0140c00252440160b182640500e6200d042c040d0310f101d0b25040c000205491350072030141c1a00034a2090350b05400001c0d1001451380c0714105100304006020680d0192210114010034402a075a0421117013814480e044407810354000f44506480301c0d4688402c082c1d607880704040402850316400190000300070860401c4442da4070f50050902412001c80580b80c0281038002c82e189900a90000001e684004100804801c0302107000758103805038409003295021a88560707540c0d4540400c2d40120100001501401c0850082224006a401e210480d1036800c410001610350909100507230050121b080e003180c581c500403040310801c0c04001c1924590080032014400300035280c030030140d0450755036800421804854140c005c0200510a00400c01d840d2618000b02501460140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533052419 1250 533051169 533051179
    0x5010c0c080906030606040503030d0609050f060d110303190c110d02090f0c070c240201051e09070905040f170708070f020d12020c040509030f07080f04030c060503010e06 75
    0x200500180d4008100c900c000c0b022030710541c5944032040022107520480e130006925200001d240b151852440d041401281d5001e4410041a1742d038141c4544189001c0359102e511108040328840000c096070282000340c0405411641094400c0c001600302002106842d0041401403c18104108081001400c0318409482c00c440b46001c0d6400318458007800b07401040b80c00840d02c0000c01d154418402d4a4032141c000b03240b02c83c100c1d91506210a406501111000c500c0d200c0c83d00d60f0409401406858005c440003098581c9240c44076071200903036180a13000040310f0217800c100248000160180e1400f0303e000d1229200d400050f0b01d840c2c2c03a1004102e1a01e2400e21082c041103020903418419218010f42100f9201e441e030700c0701c0c0f001900340a0307078200041441d4aa0a40501d116a0005200310180801e031800c10041c0c4400c45225030701c3c040c551050104040410000c030000e0721203c090410604604030040c20107450b45c0d1400444102034010f28001040400100a101400d5090581000007512 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533053669 1250 533052419 533052437
    0x714030703170f090613030303050f0606090103090203030c010203070201140a090302030304030c111906020f010b030c061b07090f1a030d0e0604050607050105100e09150c090904060905010c 83
    0x5251202d000055034028070105010400c0c0b011604880e0442d201100010a0b00e66200088500d00782007502c18041500002d10f0b220010304049090507420380030703450081003142012020401180640903080003203801d400103210604040409001450050b4566000810094aa620002c51143c8024a42c1513501d0410100c00d0200c1d40200480b0f400c550185803c18038001c03079007401100e41174000c00c1903403c42d98400c402025803540821103404e071480f9138290380c0340b215040c1c1181c0c2070360300c00e100d8107034181c01c09103408402e0b29001c0000c1446000c1c1400c0a400c0030b0020a605040c807106500042c091038a403030f404905115a44150001880850a0100035411420220350b071041c580050a007804400c544a00d181e95602c42594014900140a207941d00002e248c054068a41540c041e0324603500d11601140700001042d090b0f209048910041c85100c0580d6104001c000c006001025855010064440280c58080401c1d110ba4041e01c008a0141a1403802ba42140c00c0044140c0c1000b00e185 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533054919 1250 533053669 533053673
    0x70203040605250f050c030c0a0b0301090207031704061b140319020408010c02010f0e070510051312080c0d0302040501140918010e1008060c120403090302120714030703 74
    0x1c01034411403841505400f00c800d100815003942e8811442c0042c0003203000356858003c12000044809052500781d0a55950001c181c0922030500c117980200e03282d016041c001880304441d607501030046103009181180c8058051403070103000d088103032001e0f0b40b6180c48030084900a14031065005440000b441c100e460580c01a64107005400098902c8640d00480026469659940e4040d20064480500208a100c6454601a00924002c611307000c4090510f640c0c0150080003069600854901500c003075000b51201c03000700d40319440210141030440718001c020400800110400203c140703e02d03282940c86070b002c003980d803420781411500d004141c0100018012641d00040003044035140c28003568965a00070001201d00041c80b42100d1002d4109000003510042c0c0c40c000d44c000c264182c80c5006594031540741d16161203046030303419032a0070108075101214021162465115000785440e010598589d0f00048071344d4504145105941e201d0201406414945421a582140c1c114000c141841c40c41d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533056169 1250 533054919 533054927
    0x305060f0f0f010519030209160801050d0804060c0611030a020406021c1407170316091e060e030f011b020c0409050606090c1c061502010207020f060d09021e0102060702030406 77
    0x5015090281c440c0d110217000c440c1d05041584040e41c0d00a103a50764514058098016100c3e11440c408002100c01c000003813a820005c01d02501d00f504141d00381d14007400c201e425110960664400c83d800e654400000035a140351002071030040300e0000d00541ea46282120081c03501502d0480c0400c000006202400c050350000c0240103010156405a0b855840504045d90f0b590643c0f100c07001400800000c00c0070f280740c02401030582054a0b00c400b07042c0c6443d00402c8002c45803080c1d600c01807040300a024080140201205041080003c00700c54069511003c540d007034500c5e03040030050700400e20f1036500c840c43e0140051880040b0a0300d0403c0014000d484680e40c45401a0049010701032500109050801402c21101d001098618464006c44580c000100030301c202c0c03140100d84190602c075041140c1c41030007100c0d84a03400038140f48507000c038601040556400718490541565070f84c001c204c016140c500c1c40400341c9400500301780780c01c2440c1001a0800d00001e202c0c004540007000140441500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533057419 1250 533056169 533056171
    0x3150d1e2f01110a0c030b010302010f050304032f0a0c0501081f140409050d0507060c09081e25080105010501030e030304030807030b0d080711040b030d0e0406030206040305060f0f0f 80
    0x3d19100a4203001d44200c241800b9030342c40701401640c0310000c08400c0c0070000c10602e040307034401c0c1e98440010340b909900b26001d000907035004001031107054a0130424096501040d1014500c00c0920b80319a20302a6030b203149c040401011200c007020031130100032640c1c000c00c005030b111088071640c41203580d0504002505500c240205e1080c0d0340e00803405922034569034415004242c1c0402182d41c2c1030a15400588030750007041c0c0440b031103418080b240e03240900c03c90f508411544103000030100e2000820345c131240300c03100200e801c5251160440c0c000300b80161601c031415444060728211802c5040000032401d454050700120705060510030301104800c0000100c952094151602e520b00f6141c6600850181c180e441d0015440401000071205000d503590040040a201e4085002c8602d076900a0100f41c41080400e6036160f0080f140d1024000d00074251451040001440052566203d0b8001041f0f50055001585d190b44504100281089091005600000d038030314450345070701d00350b2600b20142c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533058669 1250 533057419 533057513
    0x150a090501230a0816230a0c080313140109050a0f0602070f0809031603170d06080f0c12060402150d1b05090f0609030303150d1e 57
    0x550450100d00389240b0081010999040b6030020307944580c401c60041051310309541c0080c5071a08900e20011240c0a00c8040c0545000c0da04d2030081400c0450300300e06160400c00d110f8003400f41c3c10102000091085d0002d522681b00c80c0403140300440241895400e0039080c2000b090540e05d0a00d01d9000f061340003910a0f989680280c140784501720030b180000181c000c100f40108150f0f0014058001c218282c0040c11031004160200d803580000c0c0d284810741d0310b02c2c2c1c0c480640258030020b51140d02d540c0b0034000b0051044070503030100f4295910407145141511080c4040c91540000528030028540100034030700c185000c900404113401c140c0c000803c4201c859024111407500010b0100c0300090b80c0c2c22882800240c10190303800b41a000502403c40c2c4d0260349200d125815101001d2501e1812606681220002030000c5086580f5408241d12100c1e000f5440383d486100e1090460004100030010354208521000380b480005151400b0300c2500e01000c8410401900440c1e20618101d0b0008a40c031510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533059919 1250 533058669 533058677
    0x60f06050f0f0c0708060a09111e190515040303020715021c120203070c0204050606070b04110d02030a06022101140f040b060403082d12090304170c150a090501 70
    0x905500b050b14101c00c1750f0004000b800b0344400c1000140c013541c006407134140540090280b0a128900b0442020313122400c44441303840240a83d1071718205400001c1030b00000428041c0140c1d1a42c00103030091141c1200503248200c0040c0038001c0503410700049000305800d20f955080c05400c410060348802d9031b4004054000b1071008034036007152040302035510342801807400319070341d00f0700038402000c0e000400d101b64010390030280401c5040c141a030844034400d4220107160748940b95a070310944058612805280d020140e2000d036400359905014900034203100341c070016606d56070200030b101841c4411541c006c40b409074600400954007a0b4603d000345c40000c9907035410b40d114440001d001070003a42411500000086008410030080c0343c0203069151540c00d00243c45070403c0782e12031601c1840c0c1a42000040c003440310106401030b100403190041c1c043c2098074113240d00c400107042d401c008800740e104c1d2171348040300000803402c1c49489020f0000466085515015072410003602e90340c860f100306d50400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533061169 1250 533059919 533059927
    0x209040b040f0c0602030a110f030921030a0f020d0201110f0717030901020417120702101205070305010306050f010602030a14190206091006030203060c16050a06060f06050f0f 77
    0x180e4050302422050b8440200504503444e200000c0d0707260000845000491107401c5031100c00b04001a007103604582040081d031403d0107001c03d000329480310380c2c4c0e039001c1d103081c42c004046030402c14405800b0705c0305143d84075000004140c1d0024503215034003000e2805c3d641340812001070071280e2000c0300d40c0b00741045d05030707581c60402d4a001842c0c112103400382c001d8000d0200c140051140190010403c82e0110401d40c0403880c00000002d03100c0c02205242c91100300c0400032800141051402d202108406052803000303904801c0da807100b65801201d8881c0020b0303980006204003d5a80700d150780102d480c03d0080c00660402c0340195480c8110190700c001c0c840d001c2d40008640b031020085038140d16103c903600c0500f140812020356186025256502940101200c04020305d0651252908680d0020002d0840d9103408040240c640d00503110b44450940032407140b00850410030003d8005c9120300f03800a0840c0c68012810707454121038000008028082112410003480c48c026100d0714800c059080b076903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533062419 1250 533061169 533061173
    0x9030906180910170105010e010603150b040b030105100c050c0f0438190b0a030605040510080601050105090f0f0604120305250f2a0308180301090209040b04 69
    0x1201c010110a558084205070030006410408054041140c0014403405006108403c0980c03d9450074003a01481164a00c01085000d109800019041500d021002c0070700351500741c02d0569602540100051143c0007004105505080c00c610206030038074a8804d00c1d03060b40340e441ca6107540301105a24030480c4820304042540c2e480760303c41d055503048001c0300000c15800300d8000e46910b040b0442880c00b40010641900907040031307401a112101440288003503030342410078804071500020500010544e48400100d11a1120302c140c0740594840d90700761402c1d0b17142c0360390189000300507080103041282c1440013030354540b2040e03684a0310540440321042401c0c0c00d0008180a07000b82e0381301d90525a6002114418190048000c0c0311050f41045c2440380c41150f0302d080d1010b62002c01e03004182a84054008010421070020a00303411a03070b0300a030030001072403200002d40c420b854100346c99020000408806542e0600c40101280345c09400900503034120360001405c002c4001c00180010913881d0000d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533063669 1250 533062419 533062447
    0x120c09090c04090f1b05090a09050312070c060606140d09170a0f0801060f0c030513091a0f0d020307170a02030304091d070b030a020706110f070b0c0309030906 70
    0x740203900540704002d12656418084598018040c060320016400c1c1c225401d005c40e0740d082c140940b003019161034526124001c00c000180f02c00b110a4625000038042099174802041140c2e024280560716640c0d08407203400d00008460f120351010040c40304186801507514000000c3c0ca00d22150710b03000199000190a200c01e12540c1e24001010141001600c00002c940086061444104640d41e401182ea203884064403401700342400040070402c42020080040e200304020900d0000304d0000e80c132240e594040801c107550402c0b1464028955031244108141003011407444698000c444940756180150082510b1304014001c260002c0035a40a4490101040100042d119070144c07c903a642c9590780d0042e401081c514410419142c1110890b1070320b50000070381e510648801c0200f42d072964490310020402903204110403214a5240c0c5004043c1d00d0b0400080c01410b9121a0003666401d1189800c3d04415401080040f0740c140c03e000b40103e41d84000261140032405503016552400c258072031807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533064919 1250 533063669 533063683
    0xc02030c0907170f040f1e021002030408011415010503040c03080c162c060d0c1d0619090f1d01060614070201170403030e060f15120c0909 61
    0x9410070342101c1400420303544100006000300e0f40c1c128103c1c6a40b14243e4200724854241e4001e402c814258509101169941c20b1501d400d01075204c0d030b508006110390106a00d0710600c010040035030404541000032040c00e00600605429041400c00140f82403401003c01000322050700f4100328001c800642000410b1900c040a1038220764110380b01c1c01080c0301d85694850042c201c042c0040301450003d03505000c900c40080a5911003450704140400703085900200310003d14540e0304c40c0d0003581400102c0c03248851a0090400c0500d0746c00d4500c01e01052002080f8040e102c00e000e06800c40d42c080106940b840c00405441c1410340c04170705c1d110704000c1c80300079000c0304110b4140c11140500e40060780358154401412608103444010b82955419202d00440c0141100a40807030031040480303805030047c0400c0b03a0701520a0500040652446080a241100454550142210480c103000441001c12200341360030b10102d40ca14081c8050160040c0c8070f01c124901540698821008a0600803043c4101c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533066169 1250 533064919 533064943
    0x5010911270a1e0b21101701020705240118020432040b0a03080f0c160609050a061205090c090703020409051003050307030c030309050a03091d01050306070c0203 71
    0x1684150325100e10b030f01080c41d6950900160000500000740c0310021005492500602e02d094101d10142c45c600c241000c0c0008100352000d1001c070801007105901d5242000b02d12503c4e1000580f01c8202e440c0031442c100000b440112208580310104080d14992816181902e00003804089400b140d41c4000f0064051a0040340300300c04040b0105022034400c0303203110020751051710346a1040e1781c41c005200843e00076851a0350070181030401800410410801000b8000c02c006a052524050b40c0c065410030351246d011082130f4044441c108113042c0e1003d54a80602011a280d040040c07401070701802c00750321690321440840c1c0380c0d130000b8001e07001800f0946142c0800703000c402103460035140041c0254058020101580d1900e0042000b800d0318040c4903081d250b112006500e440c200391010340d0340a2548030100c3c01c01d500c5041010001c0c0050100b000214800d403038a400341ca00b4074408104804088884807407424850004002560340040c3d01500840141440c10307000c011800032a050900c0b100304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533067419 1250 533066169 533066179
    0xf180d050d11070815070314010305030f0a0c0f11090a0507170c1309051602190b100b07060605041b02120901170c0c15090d14070203011409010501091127 68
    0x140c5030441c03a8a40b03117a40300355803664040128141c6100d01c0c484000d0203004c0503106500c240260041e01c0380000062a02d0030b854280700d0300f4800b25544100c18411080300449822041c1d121310020f40c10a0702026801c40182d040500017407030b18400081c107004c0380600041039814080701103901c0ca5180000c460311488080c29080e405500d41d0f80540182100795554085107807440400506a840440d088000e207000004030401c1d48000d4488502d50f403030280c03082400322450b0303500140408006009000c0d291143d1004035000b46031400308400c0f01c0d051758200105000e01500a200c25034046410f02c00c100517040015111540000100d44429050682c08154007a02041c030600e69054009044103c0b6524201c035401d010080600130110b00a0310300f0380c03003079001081e442041409000d144409807a180c001d282862030b0764000078255030603000d049002c1f01c0400c00b8081c040c1028001d55001d0f080d800d0f0188007804000c004a00d9030b1181203000c0e00c55141c1c00284484080000350302003455240104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533068669 1250 533067419 533067433
    0x90109120c06080903040609030b090c0a0e19020f09040c140c011a04090521070206030123060309190501090203010608060a0f110301030f0201020c060f180d050d110708 74
    0x1a1807280c940c041e00428021460782e4001a01e2568001300300d5080d14400c2e80d40300180e6146540340000c41030003500e0903460340a94040740320f403515454080401040810301114290900c4000000e502c0f050001200d50140100240a6607509a008940c80d102003035070001402c042c401c2003100d50006111040d100803500007182141528150450942c46881e1150030040746010701c1040100c5200240051947d04a4481c00441c00509107080341202c852000c1e1515140e0154005907c0350700c00d8000f000b0b60300394440daa00f421143c0e01b0901510500541c1c210b80340d0f050071008160b559590004001d400d00050001204120b0207410a80c4480d6004c2c0007031009588680702035464440850b80c0c0246a807410040100d0840365000b0341e000c2202115a4506c1c50f421a21b580d40800001081a0f05610030065800e20303644504000707080c8105030344541904d030080b1444c1086061040444a413080c4000640304000c01c201090707540d01a1402e090400074245c180c41207130b050104a5118a1150180715 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533069919 1250 533068669 533068673
    0x5090a151202040506031b010c050f0709060608161215150314070203121321020d11030c030d0510120f14210c0304050303030109140105100c0809010912 67
    0x26a0881c0741d544200e8041c0040d90b81c100c00c1c1640c98003800c003044070461080702d1300c3c3d105501681e15000c0e518014410390360f0f0201c61189003450504580c4c88107101c2a580c103002c120080d440080140c0004001c804054001c90110303006002c400481804011203a503504130a40c60915043c0082c0204182a031914203041c0100019000380307032014001400c0c036440e400040001e44003200320b0303101c4508000d00f1459030b1101c0035a90341c070b14010710084560f08084c002c1d6010b2214005528010034007254014440003505050041401c0b40141d08504640c0c4280242a80d06101006a81d03161060b080000340b41c0c1c0c0c80f603580e419110070603480640c0d00102002c60100f030042e52400c0504a40c004c5d210701201454100b1705603500c40c030015412401d0340011030121003c0004800802100b065081281e003059100c0300002e00f146e0003a0b024056030b0341d43d04054000012076401050051508032500300d403649a46001034140080c00303c000b81b0038840010503181503030092440001410b2013404541802c1003034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533071169 1250 533069919 533069939
    0xf03040e01120b01061b060515190f2903131a0601120903090510080103020909010507020307030509010c060c0302030402090109050c1c230f07051305090a15 69
    0x60084208103000e100020601d10201d80e20221956441034a50740580c0c0b034520b0484030b0303444420100e0001c9070942c0d01c01011521383d010b40344c0520100d040c15200080d6100402c00a402d10740c01505444805400c10403c0c15060803584d412140c08000c060410304a00a1100321b100d0000320344811001d0110500c03240322960303000350380d4062107801d44143c0c4a42c810900043d12904842690000389010340c4240d2105050b000440d8442c843e0410000941d1a0b50000300950f00700320705440020322000c0108154503180d05901d0708400b911000700040e040580c030094803480346400180c01e00074005998040c0d80d00c1005500c45550f00098108429641014001c0295200707680036803081000301d00100b81000184140c0313000d101c24030281441d14280c10015010580205208412a5031350052124019a0b299110002c081080d400e0215440c1100010040e072002904e0740081120a01030402e48112803c0c02c20140c0300111030b030b003400f40d6408100e10050414001c1e04403400454400c0040c0012039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533072419 1250 533071169 533071177
    0x603051614131a102c090403540f0909020402130e040210030b0f060c250501021b091605040306180c05060903060411120f03 55
    0x24210500002959980a902400010460560b80800180411612400d0641c010f10f000b1150034112080d50b0402c1000402c0e40a1002000c404240310240380a002e103c01c0010162940c8005d80c0c0510066000020410956004000906024060400c800c16200c904403c044080b41e4140c040400300b1580a599811150780c1405d0300e8007501c2000c03810321182da106c201c1080c0c81045021607913a52500428a0240400f10400d80e08690f00308810044808614000405403411400c0e296035801e05205210ba44003810b0109010185000b4070505039541d40303202048040710440e07150b510340c1860307005c10342802403041c4607182e10304c030842104c036580007126104011503009800382d542d500d0010810701d04a4119901403079000c0000000a04076070724a49131946407003c64500f071400c050b12a5035800c00c641c400441994210400c2c1f610000b04105405603d001e40b03130941d403290030b002d078410100ba0303651000f810080000179041109642501c4140906850131000c501300c1e142445600d46058032540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533073669 1250 533072419 533072443
    0xf031902031f060203120703180b092808070209180a0b010501180605071e0b010b0403050c062b15120605100501050a1412010311030c0102120405010e030709060305 72
    0x40c042c400010b082d800802070f186c03003944070b0006580d2036803045e10840003060044400d4410391004007120012401d42102d0500c5030440800818040c0d05480070040c40860743c85c000d0007805000b040607000648198181c50f0851340c155001c1d400d41d154420000c4032612110301c100303814410079001b8003e0101003090141220800c0e01c50040c006055a090300000fa0f1600071017001c18030812240001600b110003074012840000040f081e6550700c0e07a14020f6200f000c0e44071441c2100007003018420b01c203082c00400a600400c5075170600c2c01000340d480c80590391060f44c00c180180400c03840d01d500310b070403500528000d00342030a41c042c2481e154848a540702124903070546d0424035000005481c0101203030b010080c1c0c0c0058641c0d40c03c0c449014801c8480303d40035040e800c5585414002071010b10860690a40a507128103125180603041c00145407814444010907070455002d0414691084040021034042d10820b1030418040b40f40200403e1070708410754881030002d460b141000051100210f04000401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533074919 1250 533073669 533073721
    0x50d0f0209010e030d09140d0b1006110712061d120c1509030f0d020d06090b090702010b0913050a08160506090c0102100e0c1005030603100207080f03190203 69
    0x1000f00400e1680c0c0f039000290781e1300890044a02404901c2d400342c90050700b910010104c08a081c00c1ea40c4c0d024282e00b06030380c903031000c4074141018450f01d50000d0303100141d140e0200090500900d890741850544050000180420740e441e14101c0c003000010b90484840c2650500700c444682c04501685011380c00080b000030b180c000d20600c00c100c540718440c2c0600489000d002982040c0342e4116808055008000c0840d529074200001d40221207103004140003090000000103120011405014a2250080600c01103900d003481c0e54003e5910f01440503005200b07068007001000745450401d1410045400c00340c0300e102c01080106c0c400c15403103904501288113105640103038491143c0302c3e0b60780707a03ea107001e80581c022200000410030a079100d40c65120018080720141c1984001044006a00c1c0104c500003400020030807039142010420071000401c103000851400070a0b8940c1c844034000c80c158401c0c1403100002080806c1c0c0c80e001400c1040c1c600f84011035490a24101039190300c90407036141d080725 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533076169 1250 533074919 533074937
    0x3030e01120902060702040c120c080f070e0d080a030612060501090e030301080303040b04030e0904060c140c0a110607080f04090606030b030618120708041e03030f030507050d0f020901 81
    0x1c5150340510300340e02c3d50181050303003402c070706070308100140682070700d100d00300075007214808031101c154011080e8212250300c814066041c4007060100e143c500403c3c1d681804600c5910850710744030140d40750001500b045a168444070422030440140c141c0d030b0b0040c65011a951081b20070301007254807080c125003054074200100745281002a4a0740801d21500c00640c10070b0002a001c01c043c801c0e002e134041e00ca8940031551038054000609000c0e0180e505a41240d5114186440741d5080401c481c80c8800c1c03520b07490308010241208035a29051700000802030021180712542c030780c0b101c01c203860007141c0c031414068885075001983e1142e40c01500c141c001040c1499000102035000744500c1005000160140503150348500c1c020b20103009403101400d051098404001840352580d010740706031403003001102c0d51546000d1400c00720503005a0410200c0e40c0c1a241000003a422400c00e14905a503800c0100e032941c0c03a10015666406040e100090740f50810185141e180c010758000c251100c02600c0306551 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533077419 1250 533076169 533076197
    0x6050306072c0603010308090f0901050d030c080f03010b270a03081605010f02090102010b0907021c120c080604140103050c15090d060506091b0405010318050703030e01 74
    0x61500140c0307110020607504450000307106031000016081500020007001c4040354003011400d140e00990041c3d0b16442d010451001610707018034035210318a07040f91190010350501000501100480e1002001d0028500c1000c08201c54102610f41c40c0c4410204a51250781d01d03060046c231035000b034aa0084801c01014054030700141407c04103c411005400e0f1881c0d1030856540300341c40c0c0d10059080e00700555002c4a000001c000b4001e281204181480c0035880d84d01040000e400d640d6000b2203540324074091010003400c01d60009441c02d249418901103540352040d00010b440e200c0f8010800000305080840101110382c2001c411400381806840c200849002c6040c4010300010a0100030030310381045071008000d2400d0304071040540040614203161003520000545114100345040b03610a4462040280c01d01c0c0000515a00990100c05c8648c0038407481040d135098400c6d4042c1905040c2e072007a5421420545140c4152869070000450b00705036140e0a015005c01d801040131f60005081040d0051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533078669 1250 533077419 533077423
    0x12030301151101021303080d1d0a0201180b0f131203020a0b06040b090907080705031b100905032b0e0d1e05030304060b01080601030e0d080a1b050d060503 68
    0x4100d400d040300d01c6410014800084555804420300e10356a590280056541005020100c8000710b01c1444100da0f00c958240ca42025600007819641084489001d0352401460220b42d1030a50350342441c1c040740548203003504803615481a0010b944d03100d8080346480000c031032040180301c165080c0c0e10300c05803203645483d000484480b0450040044e007040058400154400001d540c01200041000c90300300540401b01d5008401103d8020150b4004141040b8030802401010090241039001d0078681a0f10354202c0d680390300d821350b0720b13002c0c000000c19088114411380145010301002016150015442041401000003144800305c2030340401401c00200c40c01440072080f5100090921101200540c0340c07103042040c8002c11000000c15520b00e8400280e0520007140b0880c41181d002030021001c0c000100303100001403846040c1498403000f000021400201d030031102c0120714010f1031580c1c0341381c0250b0182c2008102500c90440e514015100140c000015001081140b2020030220782d441e01011307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533079919 1250 533078669 533078671
    0x115030b150a030b041202061b0901030f020c12130801061a030a090210020c090105060301300606030503040602070b030f0f061f02010b030c030a0317040c0e0c0d0f0501030c06050705070909080306120303 89
    0x827482d240300f00442a0207500035085070480c80410200141420352003c1000e0600510b23180c03a00004200181036988280b100b0740082c06050410b000b005150f04003040591314131002040744030041c401100040011060303030020441301e54064113a040b8409003a034041e40e00d05842110611400b0b0038400450141021015603049540c0809071851010018540046002c4500403c80c106441001143c001c00c00c207014040040d8407500055075154a800c00007414009940c12041e000882042406814004480c2d4240c010f4002031550403503850b034100203548030741c56a81645409040c42401095160194030903102540113a05803652500c6e4201016103a607051580240850300c1500360405100701810420390051140c4c5840108035250031040710100402c40ba072224001001590510a0122740946140443c0001c0309116650455840803c00105405040c007008000f10b207a0051001c2004060014881c1341010804009107003400c0d80303140d000311940f40c050101100e16a0905100004803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533081169 1250 533079919 533079961
    0xf070c0312020a050c06070311030310060207120203031207030b0a090b0a060804020d170d0f0c1b0314030601030b1801080c010c031d060c0105090d020115030b150a030b04120206 78
    0x94044081500b04201b01a00f0150041d003c0110100302c1c012181c004100550060040c0a54801c22500c4c00e0f1000b407400b0800e8200c5450310301104501c1006890003c10b48003802d90b07404126110382d4603260101d00038603515000680c00041005d0010b800d0b2001c1d8440d5100c0001602d1241819803a540b0696070500300303a030002d4020203507400003404200c60008052280036401104d0b4a020440001e803425906c210941940701552100d1401d601034000c00c0140c050001c8078501002400d141d140901810313500f072101c0051080000014640e40e1181e40844007111005068512032200800c208803808006d0207654514442d0450745841c80d07006060415030660b043e991000d80740000103144a00400141142d82c00100c2071004200c81c0e202030059034407030036540f401481111301c2c2c2c0f040242500c603080c0e284111050351510030710100c3c0500303440992000c901c5401310030454441020520101c1c0e16403000c0d00c070440e40d01c01d003c1042201c0c3d240d408030254503401c070b420079100c03289410024450780f090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533082419 1250 533081169 533081173
    0xf090c0e04080915040f060e1f02010209060705010b0901060c2102010b0a1d241909050705180f06091306030507061101061a03011a0f070c0312020a05 66
    0x100200440c1200c16948284182085414a080740d03001c5000c81c0011100f1a0003550041420701080c41904282001000c05242085400c0301a4020640000c0e0306c80b4240c1104059442c1003000c13900075012501c4007440546101d6070743e0070320f082c050300811030151614031406042d0000100d03580304c0d04c0c956080a4111000090310403000c924000c010ba203655501c402d40d5201d0380311001ca07030703200d4084d07000a080d54940c07030f0004408840504000c0b02e0081c582c584a20440050a40e0030006400d00f2100b110241c80c140c004034458880d901d000c000030307440080d126040104200340c0c40d9011001d014030b4a681c43c090300d58088a030b8100441d2503811030174241c1114060020380d040e0314100410301c914a05543e40081d2158994a0345801c2211a40142c004501101000900b1b0b0000f4450180200851000d460180307880601c2c01d1580d20041c499104452400c0250030001c13002441154456203884140d07075510b0003180f4200c04600960b00c01603440690081c2ca1440d164000b0588040b1142c1c03200c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533083669 1250 533082419 533082443
    0x31b01020f091207030609061e1104090b060708180319080706020906210613060e04020f1201020a09051c0308071b0204051306240b0d0f0f060303030f09 67
    0x428060b00007812403a2903e0380c401e810000000c98854860034005900460001c2103c500100e51900110344c1000695001450514070816141c1408280e500350341d010000490410f01d60070000340c84d401032400181010800185510512003000040134036040250706071030440d2003a01003071808000d4900003410304081046440c0c00207100d0741c010401c03000000d00c0142401d00305034045c40340c03400c0300b00075942e107042e01070070b00c22145010803446040014510301070141d1390510125a003002d03c0030f00000e010380804054541e055841d0140c1b00c080341504002103481c0c0c8401e080080c0160518801c0e18014461000001405502c1824407100c0c550103480d54031041e22195402c403130850b4014044c440440c9002c0e1040010783d40d901030540200400034030380c4406500ca04145003240c10007054006074404c0c855070085181108886801140d103800a15519000700c80341e07090140c00d96900d421462480c2c0711040300c046002c1e82c402001e1340e0003a03504110150f545000c1c9400c80b49064000f500d1078001c24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533084919 1250 533083669 533083687
    0x60203120109151502010f052a07021f0306030b01051509012a2f01170603010b0405010e0a0f02030114040b0406080d091d0f040204022109031b01020f 66
    0x14010400038540400343c50720a659811000a140c0c000035112001030751120454181c01c41c00340076854010310032a5041c0140031214000b2888030f54800d01c1a003155102044040039540c0f207503181c0d091400b104d08001e04000f4039403001401000f05000443c0d95044200001c00d660400f1599450106030100324113107012507003030041d9540040304800c200b480107040441440b41d1805800c880049114403403034a59240700420001002100b4844228010040f081c0085140c0c2e010540c0901101d10300300e494107548464021a01510110345220341082c1000b000046400d20700c01c00503c42e100740c500400961460058480c00e0348020f02c07880099849050206c649490181d1046131083c00003040011010740e00c2000c1d901340344403114844046841180204079211780204503491501c1008507000342c034588030b80da00f80e0550001d000680900d501045a40715403603120302440704000600440359080c40d00c40c074610f83d0b980c00411030081c41c1411030007841d4048014000e884506003280d0040381022154 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533086169 1250 533084919 533084921
    0x1c05061c0c032004110c061303030902040c08040605090c3601080a120207080604030309060902150d060509040b0112031202030c0a1b0b010e0c04081002090a060203120109 75
    0x500903038100d5040e10740000001c501c0d169882030440c88181000c940e41c44102007204640c540c1e4031302c07441c424041288628404000c114107900981c481900d402454107414100d0003085c14250003500640303019454281a60001620f910440c4120814812550760030b0040b43c503002442c5155404c5a0760050b05440b419003042c02c20041b4200001360a10395201070f04a4454007001c0e4084041500002c8500042c449903092601c00c1031103500051501c64a041c80241d6030310300c000c0014003010341d241e00c0001040f1360794101c040ba03150024010485480308540e04130390355001c0e158091400b0324042d0002003c2c01c04030102e9120350f4000c0b400610580c40c01a00140c804902c0608a00308040c0e0480150422128809180100440f181c12600d40c1c140f81409442c441d1426032054501500c030762000c00280c095030000c1d0540704406100d00782c0b80c0750202c81414500494103c800b260003410304040d140941980540f203e80c1c001c40340d640103036541d840261388a04c90100c0243c1951111301c01070080d0181 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533087419 1250 533086169 533086219
    0x6110c040b0112090f1403040602070b0306040b0607030e010e10020a0b0c07050d0c020915210c030d0302070219060f0e0a150807030e01271e081c0506 66
    0x41c1094200f048440740301c082114803810301203580d400c07503c4e4200d00f84810400c103803107501c00d0000114941400c003100a07541c0d400c1e5100c0c16550107070000002e43c90340c072290008a582d00c005041d468584529180c00382c04004030745031643c0041d034805410703d0280b804070240d100501c03c64003d0842030340030391034840004200408140800318200404d00000382c1c10003a02543e82400e03a60280416002d20403c0400d020150010500c550515441c903141d59503048200c00c400e03544080e100d004000100755070b003000d180340d550035410300500041c0046190190010702c2258070846018511107242e800c0841240202d00030704000425007a8000c0100d802414005d414010003081c0d018034aa40711910f5051810036140800004d10f400c041c4015a60140541c50700740405000038031907420b0940040341c074420301b091a85c1d0b480c525424013030180540500da03035200e90341c200f603a601100480d0030609069407141021070350901d1919407a508100552090031301902d0300070075142c2440c200312051128418 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533088669 1250 533087419 533087441
    0x305101208031e010803040e070215070c050f03030a23070c081308010204030f0210021227060703020102040303080705031504023001080106051822050a030c0c06110c04 74
    0x300043c0e420100d080d07070b1003400d00806003100215656814104000140c06014040c4020765104d03192007001054820061a03104140346030951501046062103803520050044050107800004140410550036030040c41051203a90302e9085000e8080c2024942020100e9420000404140c92000060880307002003c800c001c0c0f82d1000c0351103441da05200e0032648151f2084031400d0301c01204c11300314102042140c00880301d40c00035010b55815001c0019481c400e680741401592401c81c41c002c424400300190100b00d0300040d181a84443c0d6925019000350b010f800f00b80d020030407010020358100d200780100d074407600b036007490005542c0c0c2c488240b03c080d4002c0c10403030a49426208005032400700c035040c51008005c551015032010b506d03002c001c0707003158019000303203000c0c401c90382200403031558071200d543c0c00c44060002c01104520040c007106c4071100c80e601c010414013600700808107040d4850f1318800b40a00405910156555542c0d00b0f54152190400f080082d0708582c40b00f82c2d50346019805040e00c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533089919 1250 533088669 533088691
    0xe09121306080711100b0f0d020a05370618060504050402161b05090109062103110321010b03070c030f0918020301080c03010b18070504030b070807030510120803 71
    0x250313139609103a040c003084100710140f50f41e4441c0c0c1c041d86442d002d118452181c20640340040d9201d03194021880f4442c8030700a250007054414a40ca004149101d9030610030520041a0400c00c404490070060b06880c2c4d1046500094508029a07100c5071848080710464001e5140c2a03e032520b450107010280d0081c90598809035200140a4082545607100140389811200d511a18601346405c00c1307001001a00b10424440c40d011f018050800c0c44101d54500800003d04004601c6140c58215a02810928040c6071400046090071605d0000071109440c2016007001c0c0c512603032218501c0030b407400129102800a00c20480801c007080c019006a086501146050800b880c2c5a5030360888640b555100a10441c3d400001004010310038003200985500c12002403040c03024440c005406401640149080494100089403013540100104d0f00210b90101801040e444c0024020300b800b8000c940ca100424182000121403101360145c0070141c071160380d070f800942e00301c1d500c031140b035504020800c0e2610 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533091169 1250 533089919 533089937
    0xc021315031b170d030c0504260c210105090c090403180f080304030209090304030201090b0a0908011d0c01020c0109090f020d090506042a14040b0a0e091213060807 72
    0x103014603012016100c02ca03c000b08082802508003d00312031107440700074200842440300703000c1a00030903510071a40000c01100a44128440210380c10510046421036101c01c031000c0c0a20001e04d40301ca5508119001d000800c081e55034a1407541d11800b04a606540c0407041400090009024a0884400c2606021174044450300c800104003d071100303401480e01580f0208080085251540e01994400301000285060030b1842d40080d05002c072900440103102e40110b00c0d080c800c1c3c803612444009040c20070007440150003416030001e113120700c1f06650400e80903000320b0342c04950002910040c80e04042e0340340044145051314210082c00e44124520030303150200f000800060003401840c040a0007000038000d20b080c03e180c145100c00c6050711406038003803002130820394000e00c807008200b20780c0000180c142c000d0450303002400401080301c015038418a09600420018036109400b1311505003207080369404990722501800a02036101320204848000d00c09108261060302c00e2074010b140381c2444101d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533092419 1250 533091169 533091179
    0x160912080706090302105013150c270503060412020705030609030a0e040207060218010e03010b031c02071802030709151704020616030c021315031b 65
    0x540340d00220680040c0e00c20080d2402040e814442c84900001d5210b401c1c204a10401c01c00700020101c01503071454072034403281051901d0b4241d1075a07852107c100311079100c508c1c000c000280781300c440b08010385007120100380f412101d0760300307200b100c1c11100c03d501c80146000301035401c5040381800d12051078560211130b1002541d074504001e02c034015841414421300c802030150000380303001c140340c0c09a40b01e07900800c1408907011001c0300303c82d0401003620340501403900c060040380103807048840003003d032480001d46003503807400c0c0c100003118801c09a982a00c001c5502040600761a540c0e400c180c0d0540280d01d001c150b0302d4400d50010000c0c5c64a0041d00c41d240e42e60814281c590102d8810311700b1041d00007040005040c1c1c480610006000f0030350b558030b00700040f81001080c031035802d004081111180030114040d507503204c09880903882402c2c80054984403a01d401064040f01034001c0f1b000b0b40e43c3c85a80300c010105e900601e804030410076200e410403441e46d01c0300e07150146c42e110aca0009240400d00494 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533093525 1106 533092419 533092421
    0x1080403111203090a030806010306180906091b0f08060c0a0f23090a090509030f07080702090109061503090809100e04050f0708160912080706 63
    0x500c1d0701c0c036207080342c41e080c428022080c0a2a0100070003400141c009002c2000324800e40d01d00c1d0345030300c660006401383c07003040c041c0040d52480f48000342101003041d4130040e0aa4084e00c40840e494903651200b0000d01c11030038080050b2100c0d08020b0103a040c4036820400201440c000034000b61400074400e4405004004640c02006030f02200c0300261403095030000303c80421101086100c00c0100243e41507544030690060041401c0e010014a11100e441414450190400a5460b000d030305075551100d036000747c00807220741100f4015140580c49106042c0d004c1c09410000182e650704082c0d00d242484840c9940004050500c0680c1000a0104c811b0303072181d03201551806500a00540141c2e0383c1c0c1d216000c0250003503d00410802d000403103490751801511a511401a103848403c0d60a0410710b92481c0a00458000c0300304000715001054081a03260040062a0403c042691810 = true := by decide +kernel

theorem cover : BRFrame.Cov 532913669 533093525 := by
  have h0 := BRFrame.cov_init 532913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532913669 ≤ n) (h2 : n < 533093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
