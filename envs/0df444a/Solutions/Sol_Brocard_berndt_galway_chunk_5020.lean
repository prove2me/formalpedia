-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:09.127807+00:00
-- url     : https://prove2.me/submissions/91affe56-445c-406a-8b77-65ccbe5a8b22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 902697841 ≤ n < 902877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 902699091 1250 902697841 902697853
    0xc040e1e0a0b0901091e05150406470d0b100c053c070b0c01090606050406120314220801050604053c04061a0103060b0702060f040302040608 62
    0xb190409110360390041c01e43c2d500400c10804061094001e0801c0d50b1001000e455032080020800c0e0340d8410340b41c42e1140050001c02020b51581c0207400807640c244007a5002c00591086180605c0d00845107800312007148200100110302540712070000e4018100f080d0a040e12040301c100e513074907000245101e88030340d40c0d08d80c0000f844505085003841c1c40304940503869601a2259129200c2116500d54800039510100d5403804041031802e041c44c406821100b201540001c00d114400030542100041c2c50186100b000481c6d540d408200496000e407041801207000200d4560119001d0101600d84903440c030070040c54204660030b0050304048444c02c20005142618083c40b0b03519003482890751048083c0d404000c141040152520040c0d0500d006402c1101040044c424050568018409504000b8180b5020b400d080c0351110250054003034480d14902003c4001000390b11030f0064008841c00c0031607091070030689409000320355000008041c0008020080080142c4481c4100d000070242030000d006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 902700341 1250 902699091 902699111
    0xf0f052b11030c0403170c0d11010507080402010c02040f0f050907031e030509130608160e060f0a060e0a030c03080c0601060c0c17012a11060c040e1e0a 67
    0x46501040003284070301000e1003002444180b007411101580e4026002200c40c021040303002e40b162051080054940c01034905203000103401c401d005050000110090101e030380c500808a9154001f100c001e40015546800c020150400d0b502550074030100b1207003c54030002000c1d450040c0d92098036000c2895001820400510040d04800500300144981141c090211920002d005000b2850424801c910720070201c03a0105c0d4035440304000702844402d66818883d003c4040149036428411303489030042382000503195203480c01c0340c00002c0b500100900303012070038007500701c0d8a40140c00199401c01628040400071507020f840c0480118070861116a80c0c1c0b1423440202e003801b030103034000b40600180001442c00961000b4010081da1110710310803610491801e14503015118142014105044d2044000205065100d0036030143e6036548441c14805c10005001ea03507070500700e46001961405010503c04010008003c0d50002c00c11040005007000f02c0c85007a0060200782d407040022a0340f008456 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 902701591 1250 902700341 902700427
    0x30a0b090111090d0602090d0b070302190806150c0a080d060614071205030406020d0207150606050906120912120a0b0105070201021917070c05040e0a030f0f05 70
    0x2e01c988030111085800d10114001044001002c024001d10b401e4002c01c071a40152118404039001c0d076007003854064103080442001d80254007040d04910800340c00b0081240613030044c1d12650258001416804039408507901c251042d800050240369075025449540d008103900e8000b0304800d00380d0308000592a0b00c0c107500a0404010002049100c000030310a000c00310b03000004500751440c8a0402d142c0c1d07039880785000e40c003e04c0391100202c4842d03c00710303062080c0030313881c034072492100031072581084002d4454605507060700412002c250b0010302088001640304288901c150003441d041e0855960a101501510084d0012040726107003214143c01c011200c030312402a044061340030309140d468120107800003900d4004280310380100c3c80f0038001c1803081080030305031100703008002804180c0310011031604251203e003910a8074415824508210f02110010424600d506d80c991207002c100580c44a09a419104540140040c8070081c401040e00d00810f40c0b1886482d9440700c03200180d101414850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 902702841 1250 902701591 902701601
    0x130305032212030f1b050a0b071b20060309101a18070909020c0f061e0708130203031305090708010b180402040815040317060d11010509030a0b0901 65
    0x1a0a041c10000400c03006140000c4038800c0d5030103280200c110307124590103481e000d90700300840c455484503003030071814040003060f40c00c41c9901c91480140e081e00e400c1d20486200d144e901d40000601d0310740e00c5c86400a00c20703005999100012201500918542c00e0020301d240c1c104840c106620340140c0711780b401016641c45407814101e80d141c800002601c42d040402d0504880c09a075115042c00c0d540420089401901c1000040c04441820f40d6100003001610741c40b005401000c100ca4400d10020a0901c43d041030a480081d00040c1005055903c0d80e001f11802600601542500c0412484a00140c1c80c140000c02000c8840900038404500d080700748902c0b08401072901c4100044400148507850f142400c03245061204000c80101c0003008000400a00c1154040565881035240b801844252411007501c030300d0080d1aa6940342018040c030395440f0340e0440300b0701e07405082c10b21f4030b00025030f4100095003008018503080b0306000044012070700e8443c11900540f05501544100207902d0000d01403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 902704091 1250 902702841 902702887
    0x304081c0203161b2a060305090a020108100e013c092d0b03160f03060213090f0603050c040905061503010905060117211204060213030503 61
    0x1c51462515070480c440080c00c0f07000c928200110300c1d040c0030180c1c0710446142d00d55900290302005000140e6825411030403c07409819a1003c100c000061280c000e01c41d00f403085020301d02400810006600440f0001c7c0c0c001c00148171418851b002161100305040c1d124003804804030031070841d0700c1507100078550400494420305840e2110010208510701b040070041150381d4903401080386410041b400c084001442c0d12030800303150200c0200c0259840307400070b10403c0405d800350b070076894210a040100c0400e40c002c0c098160112501040014119070003440b54427009000d42030095281c4001030140d400040303c0016494842c0d00510a1103414080103a01030b008640c1001400080d80c0d43c51344480e8010000c11205040c82801d0145483c290007426980d03511a0650300250b840d0600250020808030806020703101c2e011640030a10034449203203110324200407180c2d05180703e8196070620f181c0e00a1003190076a80911885000e19000c0d81002c001e54841c0b40a07507224259610500250703140c1c1c0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 902705341 1250 902704091 902704147
    0x5040e0f031b100506010e0d020a0b0a02280206071220030a0201111c0b030a020303071202060906041e0309030209010902040302040b0402030103080a080c0c070b07031d010e060915030408 82
    0x40c4001d587e040071307140e044420191200720701c5200d03500000d0654551644820b141110026071a810301d540410b42eaa60034860401c0d900c2c1c0d1040c00b1040000d0b4822109000350411800c01017400890749540c03c09224410b039190168403a0f440742d0b480c16889482d04100c4000d42d20105410710b08a4080c0980d101015001105500b03002030a42307401c25144a99070080900ba903035000c4145a52000d10012461580180c102e982d1240c05280411848a0122403100140100c3c130201c2d1414102061041c01681c1282c0e044006d12110300d04002c81e040301503011000e00051250002c0140c403642140c1e0300800d1903040040c0c807280b0f140144420780708001e40c0103114620410040c0700182004d02608c0c0341e03800174501000ea030340d103007003029805120303191041301c00b449a41e40025000c41402c1c000c108041c440e80d0b0b0a01406d4030701003034440d482480e10781300380401e00c8900c00d034689090040c040e104802000b07144104c0b0840342c902c21a5550b109403025907074207000151140190800708242410544020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 902706591 1250 902705341 902705351
    0xe0f0411010c06060306060b0a02070603090503030f1f080105090c03010e03030c130902040305010603150504050c01052113050c01020a050303070e040b034305040e0f031b10 76
    0x140d0345020181810318081d061000c42c4030321034148003140d40300f07002860784444204500b6480303c6000c48540c2140003034100500c43d60501007620307442401140202c5074044000c50854032103122000451074000d100c140b40b045101a240c00344199038414030014455540005007508101c101d0720b00700341e9403422060080c4e04100c5120300c0341c1800401c80e680320000c00c0312140ca0b000c0d000d680342e50b00c42c0c090384441091400400d02000340311040d80701100320307803050f0350000b800034160f0118400d0300c03400c44e4060704070340040600d40029400b0ba4010b0003028803031041007001024107600401061000e44d55803c40021000d0104c0400c0420014a02045002d000800c0c0120f2144e40e4180e803480010175900802081d850540d1386c41c2c45640101e104448003e00303840b00311540d01c0c0e5904a10100c410460300c064803c034044d40055110092601c0e0382a6642c21600d03000d81002d043c4005080303007000500e000c3c07140102451128030144050303c0ca108001c603a0520b140b480c0400310f8a00301040040718a00b52900b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 902707841 1250 902706591 902706593
    0x3380f1509041707050a06020306010305060f0f040506121b0f0406030818010219051b090106050909060d02041506121a120f2d0609060414071e0e0f04 66
    0x100769035a602551100404080c080030074030500007801503240c000c245206081c4130f4030411044e60003940c4034030000c1c1d0701000a540d405042160001080c400260000301004001d01507003040d4125a500c06809000829130120b081080c501d84110710402c03800510400304005641e01d441c44066211640846040c00814116141d101061248801740d2503a000c05605410312a40240001c00d41000c280c606040c3e041c1807401e02c1e0f6150b600c9888110002c1041e01070441240c0b41c2810203a0617115650b480d142041c2964050010310040030700b00c6640702c0200c06441c00107a07a14043c00300c00b020074030564207a052030608050070202c0e19400768040b07182060303c58400d401e02d020846c0405c000c110740000142c1c06e600b40250410345851080c101c3c42c01894806500b6620003030504d0704000c0c0180640f59454025001540c0341c050907910503d15811060200d00801c0380c0e10100080c05101805640d441581c5100d820b048544038190700d0000070788030408000701d00c0e2203100307940d118020106615003031401e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 902709091 1250 902707841 902707849
    0x30504060c0510020a05040e0901090b0a090c08010903031b020102090f01140d0c18050f03031629070801050907020c061b060a0e060105010507030903380f15 69
    0x8a0088004019080d1400000d2282c00c0104450704040c92400f10354410070444010441e0340039024940c02d25124201007031450205110f02081c103600074107100407a403141f52a0402801c3c5031017007564092201a004280e0140a200355824603201b514002101009a03903411511092000004203591050156040c0b58440e124001c481100c04d00e010314510100301841340081c0120001c00108614001d50800742c1a081591840c03c00c807a880c09081e1503a56604001e4201c0b40b68541710340640007448103503102042051211007503841103030b00100e207202840450542e0390f184402c840c200307000030f03050100180d0809030701405401c0540c0d40080502e414400655078003650201c00e0700030344000a50000440800944903d55201c000a4035500e04045444201400c2404846070701c1d4014000002940d40c000e800316000c09505444108400b4599207801c00c0600340c900c0c208d5107220002040c3c0b1090121864115100200ca1031b0b49151400c004440c805c001307100030040000c11340d48201c0381e51203503a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 902710341 1250 902709091 902709097
    0xb0f040b0402131814070b27010e1e09010b040b0702010e0f1e040e0d09031104110715110333030a08030106030b03061611011409160504090305 63
    0x14043d02c4100340021a107080d4802400c3c82c018030440800355085001c10081e0b110040e4095130400c0f400c6401080c2c480380455082d1141c00d0046281180320600c1207003088040e00c8400c0783c4003050501c1507000030280003090306180348070750700100c1c000d00b40d001e01182d01d040305405000d080500b00e0300b403c0c2030501c0341c442e080e48500380700070381070000341000f1900a54401c10050100100034050101400c05c000d085050001c6602402e44070314240031807401202e60000302000701c1c5071290b5800c0c0200d032840c5c485481503034020070490341003520b401140d080700d941c2c1002010401d100c1e8540c86082e911100c00d580882e861103001c1c544244082080c4046950100c080094540004d440d510664188480703022010b810000308a8040c042d05082106100c4060b000d141221900d450611040b001202090345450741102e110004910600c00c08060a01ca065041100384454000041c00403003800c0c09016004201c5013151281d0140c269070302444c2468000000421094406001c2042540d41c0540540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 902711591 1250 902710341 902710343
    0x1e070b09011b0c0513020703030e0d0806060c03190507110406060906200d030c02151e07200d260103020405040c170102040e061c080901031d010203040b0f040b04 71
    0x291003602d41c107042c40356889010005100040c480c4200e05c0d0098071045c040d40099900b5404207103040d4002c11016000328401c010f400302c40d0343c2c8007000c1d6200c1c020030150390010910b064952005002c035141d9260b40d00c0d1480d0030454143c45054441c030344e901d00031680400042800b0b024a00b010020003050b604002d4603000d480c1e1600b0101c05c1450344a85041c2928280001c030b003018440d022143e0f1040c1d415070b01803100041141e0a982007281440300c210750003c03094858415041440d41004c060b450480c0196811010501d0412003140c518040701551a5011400400f40e8100c00d80c10300c011340e00521080c038110314404001010f1683c400c41c00103107010501c07003c0d004a8440300007404009050803250042e15102404295003030b81150824002d40150140316600110207000c00c80900d0644038901c0195074080703000d0500c501c0c0d0756404031a03401c400e244034107254440040b8400e00840101000440d164000010380b0f92510f0304040001d1300340a407803006111842024000820100151a6841 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 902712841 1250 902711591 902711627
    0xf010f0503011a060a110307121b0b070c080c1509100e100c140f04030b060d020f1e0a0314010609050c0703030213180b040c02010b06040608090a051e070b0901 70
    0x1185d410030107980c030302ca140c0f1608806000018102c400c00611a00140d55000e0a9a441d4001e01030444d008002444030341001d03117550383c0c4400194030280b00361441c2c26924842c0503c0c60070005018045807505890b031544156040003032040142c030020030041101d0070700c80480244403000c2c4510b8003e45a045c02103400c400c0a8582c4034052801e8000c40040c5600c1c04001c0d00181d44140c411a150030503045030004999540d5104081141403401d42c00d201031241c3c0092001c2c00400c01082000020b401c081c1e1043c0304a80c1424044105a07125004000114040d0310140040b101d442d0300c032801c6800c0b40e00102541458070040c0181e0400b01e0017541c03500741c1c1c5070600503682c4271812040c413401f800382e5104400740b06850440e82e69280041d0046513000c0002c0d02d00780700102c10f03d10241c1c00d80300b04c0b90a00e03400480500c0104170182c4031741c00a80d0440c42110a882c18641103403180d5042400703030700b8800c184401c221003140c8000c1c02001164002c1507081440c0f8240100d640000704420102c0001c400c03d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 902714091 1250 902712841 902712847
    0x3071707030c231201080a0c0812041e03020a2c100e0a0b0604090f15050105090d0c0315050403141e180d0309090b010c170c0f0102030f010f0503011a06 67
    0x2011005000c944c110b40007041e07024003569480c4403040d91a141203c1c2203803025005200007907005400030f2014034640b95041024103260170500718440c00e9001144001150b05070b03010000158a86020620140802c2001e03c0c0d810200342405c50340c01e400b400806480843d080c4104044019999002020741e01080800d003107039128440b91001070041c90b8519a4402c600140006107048258812030003d68010750600103141102d82200310035045100e0580414000c22285560b480e2402500d044a8030808140d51015101e88175541284450381c01181d50f07030740e00c105200506030024190305100c2d850420b2289044007411861120400c103001d107021805c0042071410f0b0000b60505031448a45028004480040d078900700245810054820100780368075108046086500c1625510385881c0c0094600300400704000c024410303030740800a601420300840030340541e001000e0000314050344441803441c4155041c201d514801d0b01c51a407016120b40e1507c68032605c0c01032003c4132103500307650480b00d81d91 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 902715341 1250 902714091 902714147
    0x6010203040e071709030a0e01210501140306241c02060316090902090f09220f110639010c021015080a0609080f03071707030c 56
    0x22940c0180d40100030000008010415015403104204d440c1c0c00c141c0c121a01d590302d5452030151240300300c081a03800103501010b000b20550054800021401001c1030444c60070490388000c908640e0b080e0004031101024090543d03103850100940c0750007079180b42115849941d5001c0340c001e150901c0359887d0162211100881c80703641401da0548050b0340242615944c2c0c070342403c50b0a00e241c07410b0901c0000c91922000415202da2b02e100341c0c0c1070220040e0911002c00c0700380042000241005000645a090038804403001054070641145024402d1000380c801d17000074a03013064000d1205810501440c0140302d0300502072038180034040c1c0300c2c900c0407442503003c064062080c03c180090030100c1c0f4560826000064080e0b0000d5400c5070106808410803070107504da0760140079484a07101c1e40500340d000810104c0400c1150b40a0704900b0720400880f840c103020751485c079074150800c076060404144642162401d1500801c50107501c0b004038582000b800080650190048a200304285400095031080030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 902716591 1250 902715341 902715343
    0x70e07031808030c07030908010e1009230a0c0803030c2715070309050d050604031b020312071b0308030c0703050903010525020f0316081b1e0303040803010509060102 73
    0x209150300104880d43e28604007030b40300300c40e40c070506080700042c016400000e141c403418400c503401540c03100041d00446801c40ca030600034204615054a8541018400c0e40887c44800c1681c528440c500000e800c3d81c5841d41014640c1d0f2105074041d00040c0c2042041210540b0420700315150701c003a0060a40c252541e00300c8000300c0a0000e68071a070001030224030000031014103005002c02920030f03a06c0020650300c880900c85210302100000344560b004002041c0020b01800001702c5000070b4440810721031042da00064034000661040b00b1000d600080c1100910280142041a4251482440d080d44d4610390b10810326110040142d1b074a03180204440b41014440c1c03084401281004000344210b0030181034000481c1d9407504101040d81c00c80c104000802c1c00070561868105200c0003030341c100340110f2007000e408020b0140c11148844200105180c03c03502d00160340c80782e06042c1c010103042e00d166420f282d0100074444061001d9005000b0000011080411241035400c1a44d2500443d100d0074010303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 902717841 1250 902716591 902716631
    0x10f0911120103211706010e18010b07031704200f0d06051501110a030305040c120303050615180d0303180b070e012d3608070e0703 58
    0x100840c500c41d80300000500c02202040c11480d922080020708050105005940c940c0e050006030f41c0c4d503e0000c0000c0d20541c06402e401142040c045c1240c8480d01d480036070206c03c030f1402d0b00301112600001c42d26205140d403020030104500500c440d50106810140ca404101070b000c0390010f000c0e0440d00701140481e0b240d04c11000e08600c809000700d00a0700c0c244c0752203005040111000c50589045410908566116040709c0c0700c000d0070100035158240e030b2500e08401800c0c0c02401a03990080800380000d110701803582e80c04a840c000c0da0001081d040000802440c440700010110381c91800340b020301d0301b04c3c05034405003030444001c4891194003403640c40c05401605456401102107080d514140041c02141d281c09889000545d4445c040182e000b40191860040d450040000c4a55a0f01c03000ba851700310a070264200e607160600d0000095004418030140c0a140c001c00c40f40b900b1703a01e88030180444002c601000c0c10446026000c02c5042031740c0c1018081006110714101501c9407022034001c000d00e007070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 902719091 1250 902717841 902717857
    0x151e0306050108190219030603061808163f021f1a030a1203050705160f020d0b0108011e060b0915091518030d050f0708130303020f0f0303010f0911 65
    0x21b124a50120304001074018202884190340d15420a941c0d0740d2a90b440302c0300741150300c1d44220b5141c24000100b4109402c05681002102e10760508444020007150413000039050081c44010901e040004208254010f031009407031030150740c0b05e00c884008591290a200c02400c607107100018400e00d03503000c3c0e0035008050030365898060007030305050424880820011225025191820301164840c00da003100c052042c2030036100070100d4094801c00041c1c100c102400c01d1400102030140004451b112807038031910a91090825070342d01d071240003201c0340c0108510801d0f0400350040202c140b070b000224842e8403503040c59030312032240103c21203201509107068402100c805000e4900c0181060440401940079143c0450382590b40400b00c40c8601e80041c1c6891500403d46da0700d414000c1015015800c0d402c0004122000b041c02c6c40b0586080340f0000040d0002d5029500a000780a24448180c1c2406c1d0354078209000c4c0c0c0c10400041c800c1ea180d5507080c50845807000c00025039031040102d40b034200e00403ca5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902720341 1250 902719091 902719117
    0x23121e070c061814060705010f1401050a05042a050c100b040509010c0210020901030608031c0c09150e010c1a071404050a0b0310151e03060501081902 66
    0x14818040c002807440d100c050300d2540d165182800a00c02c003030902e490461254140c04004120000a603080c40d40290201341c1c030810000c9412284038400320f0548100020a03c482c2580d00e004020354580360302414002c1800380e404002c16400041803082c240485070b603078000c114a10a1a00440f4400c2d4116814001c00c03005445690b8245c40450001d813901000742841541070501080540c8d006225020a000180d001040c00d003c0303001c0b814010303410500f03910f0f051695541c0001038040041c4002c11403375a0704010707a4000311040b419001142c00b4140100301300301507600c080c000b120310103183c6c492072001c034200002643e040000403107002c08800d03401440001802140c0940509598003140990380f0f6031190b10071807000c0107001105014912071203900c1440b01a0030081803041d0001590441c040c04200071130f0f2500e545440d000602c00c1070300840011a0507105070055200444880c07000da52609c0d05000c0c41d0f1600300020881240030b8409840001e00c0313640c000e407800099040b9914560300341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902721591 1250 902720341 902720347
    0x10050403050d0f020111040630060305060406110c0d051e0c0a032d12060806010f091503030903060b030f071401032f07050a081623121e 60
    0x2100403c00e8034600c4419001d5801c0001003030f0b032440351806480a941c610f070740d040d40709031250325001300c064a80c030440304480411a0550a40801c01d010750400785004200810386401c1c10b00e4040c0c112401c15100c030501c40c1052004102400e808100041d48142070715010340c42d01001442040f0301004600034001e03603d800603079001c0009011816400c01da00030b44170901d16606054070b8007101c5241c95201c01d180c05172120441e51850103043d2a0780305204003070001419039203d540f420f240410a8118401c4041d01100030800e01180f40100c1d410f410500f0502c44c00d5900e10b0390054141120707030200a080c1030702d603400c9400c151820007000508c06101d8044401c003541d2140001c0e0f4140b04403542170300280c103010503e2441c0d01c01036010b00480d495621076458141120b05612100d4102e8507084400780a003880101c00716841001a218401810382d51101c43c000030f03d0014010303001c03801814001c240049120215110114034282190395010807950b81703032100c030f030101010b21050200c00c80010002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902722841 1250 902721591 902721613
    0x80705121501180c020d08270d09081b0a05010503070c02040f0209040c0c020d290c13080f060601080c0903010e0606040509160b1b010e3304021005040305 68
    0xd4554580906030850400075131501900c1281c0301c01d48080b941300441c9201010540c0c45203680b00085440041a240ea040003107034100c040d00f014541058100010620441804103100a1000200d80b00841c00c4100041d0541c0c1c0202d49203050500c5214103004000c40068105400740d018014041e80c014400c11280d01c840c041040250411100c150003a407524000201483c02440d00604030b68000305000b2030440980d0f50b01d0340c01810311170304044030211228150340020303409544c20301450242e07208a0319038a04501c00c3c904100c8552026181d0b0740009045056104c0c0460316503048402840d00788400d5503204113019492184803110f075015864080e22489020010030703024043e034001c64051050f51100c1501c603a0360b1380b500d880d00c0d4603034420310710410514403400020560340340c0b4001d645018001e2880c150382180e60b501d1f44221540c0050b50380c03040d00b4800c00520740300440700440e89003c10441c0104071a60100c020b000031f00030000c4c42d80d614540c6010f2000d03100250743c8001201c40b241d0407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902724091 1250 902722841 902722859
    0xf030b03030a0c1e0f0210050c0f06090d08010e0f100f1206110a120905010b120c1002010c0f1b0501060f1a09132a050711030601080705121501 63
    0x11203105480c801600380840ca42d10134207a10011169800400001803003260790200940e46410105600030310100300400d10408070144840c0c503403aa5400c0262040d860618404d90820808504480402651000600070003a04295240d0402521818070441d0b42d0380c41e520200030100c0790405e40b01028804400135041c20a100c815190798402c405c2405003481410048816000e81002e44001c01d03174510b00c629902007540c3c449075450340188004a45440e845011079013a1240310196241c9401841101d00c1e1410440e40042055035144020082595500f000810f15500006200100111031460382e070345c0c4506a00e08a15250048001c200c17069655601544610f120b10404580b82c3c51640030426000d41282038985030040a17005c041244010428503000f842c00d08401000301d6540d02500000c411032100c840005039a58070b40e13a135254580d080903200e82085507002071203507000c1030041c059200c0101c4c03200304488050701c011720003040c2865601d00748194422460003a1079004000107010113 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902725341 1250 902724091 902724107
    0x609020405030f070605121509070504060206130b1f031a0403021204050918100c020309013c120f0f0605010c1a06010e040207050303060406120b04030f030b03030a 72
    0x1d011422552041c1c00d880c5141d44644003803094101203901401070040302d401036060b055100555041c134100800e0f60b000011809001581c0e0780c00003c1c07011505008a540410140b40c2240c8144a0304040750103035a200c0c4507101005005400c01d010f05181d141d000d40705280801c01841c2d10a0844a81100980f4079043ca120215030a030010f1090581070018444504111010344030041c0059a055580504003208180520700040c844d12640b4080c0c8003100c4903100795a114041d60340036507078032030314400018411888201c840c0d4179001c0d0f14540c0c80b0080302d103201c0300e084201d42c031b400c030b40b00540660000c0d121b8410116003150003a0900950000c1e25400b0303406000310b4000e025040061584442c011620500308980003002c004850b41d0f40500e40c80301d0440141d102005241160850035903501040a03a04015000c0302c5030360020041c010f05103058010303e009000e01c000500d041246580318410020405000907041c800981a43d031740841c400c0d007016030615000f40869560350140803004002e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902726591 1250 902725341 902725349
    0x3120601020d090b030106050f0706180201030b122812080603060106031b0e0f0a030f110301020c1005060a0b070311010b0901141c020d0506010911030609040f0507080106090204 78
    0x20260030b16040d405402000c0c100c054a60002000b801d51b03003450000d98195000701400048000305200d03400000e10b00e4001d05034035002d01c5103200740e502801c0c800542035652800505200710083d0404188901c0e0010341800e46801000a8080080c99002040da020b445410003030001364030303d5a90b0390059040720425004a00541c100c403040c0e0380c3d0f00b00c2101101c0d1000c5014801c4101d06401c08000d40c41030112945800c0c00401c100803070b605100010340da0800544c002c680400500010794140100ca070781440a0704030035002940f50100b2080c0705178840b905507046681d015910070105074070761500c0303a00401800107c9036050b920403003803c0c050140d90444606814660800c064142141800e0088a0483320340e11800003062001100300201d03940c2c000444101030104895134009a902d00011025080c05400508415410602298152004043c44215004081081c440140c490b9015103900541100c05400907440c1403030710f50f051008640c84004250300302000401d4542c00381d0700800c111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902727841 1250 902726591 902726593
    0xe0a0b0712090c030b0414010203180f031e0313020406060e040c030b060324060403031e03140f0a021209010605041a030304031205130636051507050312060102 70
    0x45039a2101140c01e840a10100520340f00d0300e844204000344404040a800a10aa5110b544407a5004095003241c000b110749400e2140950041000c6400510160710202c49000107103241282e0a03c405c2da1324240401c680c144e481e40003000501e00b2001117080c2ca0200d900910134040f00d556070031b0081c150a5103103a040e20862802c801d0000c00c6010b8811518090310103007440e810340d900d2962803007141c0038241ca10f0440043c0104000100d60368507000b040903600c2078440480c0b030030f01107802d03000d2040481211010301d842d01c034060810310803501110340d01038034540d548865517503800030343c0c0e010380078411420f60b203000402e060003100281900f0510640d282175804008107541001b54056000d08418890f4242d00700700414004102894400c0c00c15000d1401c0161038050000350b2140002c89a511940005040c0a0b215000101d150320031145002c505241c48200c85560381e1804201c08540300300c2e88079401c5006154003e0b490a81a0703440190000c060b240c0380c015000115166034800c880c91401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902729091 1250 902727841 902727857
    0x1141503042f0a0303051b01090803090106150804020f0f040c090509280203041a0408070b060d0201120c2f0c040c0f0e0a090c020c03010605060a0518040e0a0b07 71
    0x20854564110030318103030b0020850701c00d040ca162015034455200402c00d4416080801449941d41000d0103024a101e1042e02d0311036503442c1030400b10b07084400c82c0d0810203510380401c203900e0109906c101482e80050701201c62407501c01d203980014820b40b410701881ca81050034004404d00903608044044201da406840c5101aa43e500c42010010740f81041e201a0460070f031074002c0309400703803607024542c014411504090b02d01c221000d4005400307001c580803628900005030000401c096000720640140054411842001441c1c0c0040e0010714481141c01000fa550244203296903c5906640c00010107407000c401040c401d0000c07141c24140c1100c0b144518851030401c1106420503126840b24429680d507201c1d52030110b01c2007101c01100300c0e040b060303000940c0340f00400c6034040c1d445a04640220750b0000c045040010080c0750070340b4450340c8150710914003804000d00858200701100c0d848140203001d88190410b600000d80103061100380c1400501c210344000b030401c00040480350041940d5290300c24 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902730341 1250 902729091 902729153
    0x1f1206080105061c02031e0d020f0105012403060519080616050f0c0a02030303151804031d040e030a050a0219020d020f130c0816170114150304 63
    0x20030b0340c0090311669040314880c5040c503411040da00100c20b50b940b0040c191500701503a2104c0d4040149015011802070f045100c101c140503404109940010740a50f00074401c03985049200440f8550215529054540b07403031480c440e03584a41d01020140c103001b08521002000796540801103601401101e245104910209140c1c480090155202c40c2c0e03540e0712140350a121003a005581d4002d035500707074018030030381d90718000503603050000d07510480c81010410101e40300e034170801c803600308200f0701c011607000080300788000b0130740c003a82201e590f0440708804d4215000c208003003002824171196100130b43c080804e0440e50964007400501011090b94212148107a100c0011840707284d0208000b580300241c40c1e0320400504112550791100d0b00c004240c1c0082c07140151412003560703070f903050900004048108000604804640780b8031001c0305890101d21304403410f200750242035010300a06110038040003008415079564041400d6008152070221b03102c1c102454030441d03005140d004104290687c051080d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902731591 1250 902730341 902730343
    0x150b0909250e0a0207080c061f0b180907261b030c1c0f05040c031203021804091b080d120e0a06200c060a0b0306040209151f120608 58
    0x5080d9000c0d4072201001d500c0382c40f0258000d40c0456000c0307813051424080d104060300f09009403480342c1a448040c0321032103420b0001c6801840c8640080440400500045815416035101303405000002c0d105025540c850010946062011600313070580c85805030540807401c080a03c2480c0291005026451115003200405800f400126000c104000c0c007800041600c040303070300101e40001080200003030f02e42402c42d0b0000c241c0b00b0455050311405100c140410800c4850041441c05040f6460b085051000c00c242201d01054038180081c4120b0329150401d003440540c14100c0400c1043c06060600d80765200900390304c0380000450b00703010a0f100100c907000e0110f580074601d010404d0b040a0b000501c0c2b00d950303840081ca4010301c0c0c80e0103850b0590348844850300f500020500704a80d00700500703c51512410b0682903c1d600f01e5050700030340000003808016151010115044001c1480f928140b4083d2340c0801c81c01400c5c00c100702d00c0324000440040c58950014040100c100d9a21400d00c05280c90f600c000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902732841 1250 902731591 902731663
    0x90f0c050d15091106072901141e03011401061b0c032a0621020c072304060906080c032e0207080a030b0a08070302030307150b0909 58
    0x307419004140514880c80b40e980d0f110030401c07889038000c91483c1c2031400100d1501e4000001c1151007101c0000c40101e0702c1c20b0040319413803030005a040902c0320342c104200e1715110211032080c580110102d407641c13075407103403000d030440b0312031038064000c200d0141c4c40442100c40007000e02c108070124414003004200c400c02c221885100c0b9030000f4205622a01d16940e468180a40100003016181c6540c50024240a902c0c41c01c1d0041005903035000c1c41614001c1c0030401602e182c511100007510420101000b220007050407000c40d440b07160405602400d140e040d401c25400c040f41540e00c240340240208040c4400e51003075040e00e050b6401c584003404140107050f5245103025241c410002c001c51403580000d401160140002c203996409801d000b9166148000ca400500209002c0780d11520706108609040080740c0083c0344103402800d0661441c2c000c40e8803032103401c00242008072a0600200c0595442d0030182c4214405080c002683c0f604104003a140c036a00628080140c2c130502c50751946800c20009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902734091 1250 902732841 902732843
    0x20310050a09020c1b0d02090117070602060103230304030b040f2306160c02030109061a0a0617040201052203060f140609070314190f060b0a03110409090f0c050d 71
    0xa042030102105c01303030a10350745a50140c0c2d00003c0101801c0042c0c9030140458020324043d9103c100c050507a0308a641000c506400120465000c1d000420100307003221443c81040e064a00014042c0a45215103421840f0710381016185174594000c1c80104003071b9940e25207695008090300d41921114030415005040d0213907074011a5406407002c5a58404000d0300d201c052001c60078403080020195001c2429900d00030400d8500507664407110041200c003010400e10241b04641d20041079080c501d01801c0c11305506480e40904452400043c21a4081d6040700d00310448a200c15280701d102d040c0d140e06d59502c5000454450307080c00e50181c05010b00b4068441c0030b04041d0b6a01d03a29583c1e59060103480c040060082c0300300345e11804803070800b04d0418007240c0102e49800c66903080c851810318900c03e98603240c0d24201c115186c0740c401c0007a521f950f0107803030610031186030101d81e10b0780c0e84140315414065508015180f5180ca0341c1c9100f005460031003505001d124422019000d42d0310004c004295002c0c0340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902735341 1250 902734091 902734093
    0x2a03100507050d0e19030203181906180f08160b0415111002030f04120206190504171303110303072301150e07020120160f06020310050a09020c 63
    0x1868003007050f55000314092211100440c0c02100769280010700c8110005400d030050380001a1442075841400c01643c0c3c000c205480f440e02004c0c21078000320740c0f40402c0c407c1c50200324840c6101d82c181c1e10043d0b401c000410940400f20074040d01d82105a464044d001004507510402c0c40c40029406416010303282203c143c0c0700d00003010040e250b0107552030240d810309241503000760718941415040502c05540609520031010300d15140c2440d0070503008040c1c40300d220030355109804001c00003070700313445c4030505214620002c83c042d181c40c0361802042c984200d03d50908a4003203186040003800071070440c21030740901f8200405440340340604be224400c002c40034064890b100100d49450032100d41c0c001c6003880020000800b00c11000d50308001d1101c40d0004282c0803810300c01c0c052420b6090160300d0840d004c010800115800c8125070b00124842c50429022800c000301480050200005100c001c0a03080304040d5a00c0c985484050f0552010340200c910030102500c003c20425a00e1082d920b8459490b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902736591 1250 902735341 902735347
    0x2f060c0c060c070f152d03020a170109020a090e190b01021005010605030603010b0d02090402150412060204060f02030a1e111006061b030903020613090e010b102f2a0310050705 77
    0x1d007c0b0b002c0d5006c41c040034244402d10071041e9520300071446003402030103400d10060b10703038542d0800146415401d6000304600b12088050280408501504500b10030400400103210900000140c0c20000d68a1102c1c05c86843c040000840c2c2e42c200c40103500c00d4104030300070480542940100f1433451034100c8065000701c0e41c4000900141040c0800d94000c140ca052040d08007951000c41400303405031032604681d450b03000b281c2005013507003040d010b00b80c011300b40c000703107040c40c0003210001c002030842000591420300810003c24140c0c000c600f02c58441002d001981c4085180c42c074020054030103849101c0006682514222840643c280319a02940c0d15030703107001d80c0c146941c0801c04e664004010185012289000001e00c0f8003083c410302c04501f5038400041000c0140030100108040062110414096018860052041e140d103024116442c04003070b14600018032a2385510b0841c440c204441c0107100604d1107440e6058054010300228821001c550700205651040000c0e22020b03110400450824 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902737841 1250 902736591 902736677
    0xf04120c030f14072114280314091c2405090606030d0906030504031707120e010513081305030f0307290a0e0a2f060c0c060c070f15 58
    0x7000d18605410003208655042403c1f540c0482401d1000c03403103e902c19840d4030005c04140c0c01188080a001d03e0061540c1441c240c1c40100b60042c494282c961012034401c0840000c01201c2c02c002c8800c1d40180003038840c6030070055459401800140c5054030580b10b01d40000d0740718980016855840400c1e03540d00c0c0c00140c80d0900640250a0242c411800c0c403040c100b19890f0b0412910040307104015558648d0500031121800b139040f281c841c01c024103264100030030400383c8090302d0364032414964010b071513a41d00e130080194803040480300e80040b0381c0340c0110150000c442d0000000350007098043c40042d020815401d52410507544000c802060003000309001802d1180d05901140c0048039990944088240640e09c5604042103040d030b1440782e01d11200d00c440760351400c503080c502c6458181c811074504032502c0091651040e00b035421902c928000940008c01020038408c2c64010305c0d540c41503052860701c40809448242e200d0411100085200072495911186c24001c46055140031040c14452114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902739091 1250 902737841 902737853
    0x2070c080a03170c040308030c0910020c010f0c020d0501110304120f02070b0a023d06050d110a0e070507060e1506040c0e0901031211030f04120c030f140721 69
    0x4000e00b130b503204082c00d000000c00300d02184021445a20808140c654882c50fa10420000302c08002e10039003154401029080c1c06c0c1d81002c9101c0c0600294104030140741070a1001800c8214001c500420039404d00c4601b0444010b40400b450007148584002100d214131641c3c100d03604846d4020340001030703000807010020001c1e09130080060004500c16104030300c0c544098981d80d01d50903290a00030620500c80040c01081040d41000d25240610080c800c0900c0c00002400c1801c1c1d80c0c802420085014400050942d80c043c0b4003c01000d01003140906c80c64016006002900060000d559203810901d48100144000c56512103030075070221000051b84401040c0001000d0040001c000d2000c025490207196864152007130007148504a0300c0c02d481744013100103159a60700c00600c125a441400f859200c0003042e81903506403080b400020042da0402e050841c0c01400340d81c40170701500f481b41005030512620030b8050142540d0401181c4d0110755030f4001541c5140400800301040315200640800111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902740341 1250 902739091 902739137
    0x1014070807021804030c030e04060308040b0f090907090509390c15010315020412030c0501020702061209010c02030414010c1a190506060301050f190b0c0102070c080a03 74
    0x20000d4696602d60341d104111000d00c43d826202900420b210315800d0040541c0910200040700b0705403010301400707103180c3d0740300ea00d4041d80c01800a02e82d00480c2c1101540007110a50b02d50f01b030014a19116410700c0c0c980030f401080c5500500d0b029940d5640090002d600c0c981200400110b01c0b000405800840c0004940e21101039a182401d00400c000d41041400d0030050901c076801d2520002c12294518585001c142d0b40043e9800c8507a40144002c001e1307250800b120a081c1505820040c3c40c2101502d4114024412090025803050000c1400010401c02009007031103150294000c10921410f914180d03524010351040080c5480041c01240b04d55200d82401d030341491140c0035030040000489500d40e02007404a800c080401441e12a03540d104d05540030f100d400980944159146506000206580f01d010b0000103014401c041315000400701c1e0584104000c0c494400300f1178441a0121600c0e02031f41c0300c000107907441c0807a0040425004000301d00105481d85c16101c89038804210541403145007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902741591 1250 902740341 902740343
    0xf0a0309060902060a021e190209040c0305011503140f0303010b1303140f06010f080703350408070608060a0e071e020309180f01090e03130e04021014070807 69
    0x1d480300d001400613141c05000c0d06143c010740d0040c0a103038000c100e02e0b0303006008000d6108105d80c4048448880000c0301c1e8036205c0042e0301500e209581e503a403410401000011944010251341c0b03080340c854200300c01108010250f0380306048840d01044000c0d4020790f101482030141410750001c01c010008111500c00401a1201d090360518056a41c0d071900100050300360128a0190840031040b565104d05214441c003401c003144440403403500381f010007a0b9401607400020400224040b45896000d900709140062420103010305040d2510880e10b030314140c00602c01c070742c554840d048000c56a40d016401c114403484002e0711401505260541d15a07100201030814020b102c20180707000100f03492140001010185a0021036480d24014203002820a81604900320050003400f4010f010a98541d1981101d124040c0800c40700700c0420001e06500c20240158110a042c00f40014191104440c42c0e1080e130088070f5081c0303002080704081d44c0c80c10741d02c500ca001112003000390360001400318004c3d0a0f09 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902742841 1250 902741591 902741603
    0x6030e0a060608060708060d030801051516140607090b0d110913060e060d0b2a0a08190204060c0b04061508061918022205160e060f0a0309 61
    0x120a5201e40007268242d0b008482690000810821655040a0240c1c0c019806507942650602c01c0d0328020310440044c01100d1080c14216454404003120304180c8608002c0e400c04c0c1d00469456103031480d01d621542c0c1260541d0f020b44400030b4005401400580c0840b0310f0b01110914028604c070000e0300a0161040d14036010105000d038000b40d40350686800040d03194454005602414501d2040c65043c008102c00d214203040b5940c0400104a00f10040c0c22444d0800c411124808030343c444016200c1103001040203ca000c00d80b000c129510620050090070202032201941e4040c413a2801a44124028140030580c10010031001405600d142c5510078069080044d000c1e5808010401d02d855581c03100c480ca038024000e0000b00041304458090340310580404012082c00018046a0b4409800f00640301e407441c0000c1000b02d248094424080c2c03248540f0070480740c40e1034580c400480d005e854000b800112030f600014074a00b4040c040380d0810900704942410070f59400c42c21009400209803c0b0f901d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902744091 1250 902742841 902742853
    0xa0305071b0602161406220302030321150607030c0c05040513020f0f091522020705070e0f010314030c070609060e0913030e1815010f030903080106030e 67
    0x4001c0d1034062440151034142d014200800c40d00203400c50151040c0c0144014a60300b0354100c082e9503400044812802001c00e400070031940c24007400c1102202c0d5400030750940000074156000a031140b60303000034105024400001070300c030308100b042c40e848401100d50b00000704024003030119000d16400308002e4841d05010600d50346400124086d103106440300c8c2042054a1001d008610313000407590f58500342500c01481d2910503000051202d07a019003104408240c7c01840740c6640c0750f44444011120449004510024914548030025800403400351041e000e01e0308007103070003524506080d004102100c06414a079003907031a82241c110300481c240b515440100032900310071009014000c020305080c0c0310170140390310705540076005079100c180041c40360181a040004907007903121404009600352400a0091100101003140b145010a0041c00301400e10f00300180c8060301c40499501c2102a44c94040400380c11205409542c29000020041120140107100c0c1c14841c0e0f2000c04081c80844c21601 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902745341 1250 902744091 902744123
    0x904090804150c020103060b0a140a091a0c12040b0319141e0106110307110102070f090c0f0e01020604060b15070303050a0e030f0a0c0213050a0903020c03010b030a030507 75
    0x10010914015a00200d10703030f8881c0c10f05544e014403441d0700400003955030914007050410f000f000784510720b1a0f00701c150f801003086403c4034441c04902001c0c1440f00d6221035110754824002d0660703000f140410300d182c400c0b44907100754203000c107042d01c007104c2000031a1800d54854000c001111107411800100455440405d0700303403040888141f41c02896544074803044480d07421400040c8040503000f000610100709000030b40f041001080b0f0b00d00720f4011c0300103100300d044000101c1c100340b420b9000b00311300160950046008491580038698900c1030303864429048402c08010345800e00060b2190340503030081000100441e1240c3c000421170a00242501c0c4d0002401404101c01c1d00107542c2500001d43c0c0e1010841c03c8256031060151740d07040a4029400e014110030202c45510038040d03c201005440840e00d0704548071401401c5081c04201803e1025242c4000d11030024000000d05400511078591140709508041c491a1082c84010f800303003220400c00d44080d00d55034031409040f94074001c0707542010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902746591 1250 902745341 902745359
    0xf1802071b1401030c020f0307150209040c02151501080c090301060b1308071703030117010920100309150c0519110607020f07050f03010902150d0e0a080904090804 72
    0x70107005203041481014100000040403940c0d12501401950300060000003804400800d82d4880741e480300442c6041c99500400c28042d001d803491a40e00f0034204040681c2c040d402040205246e80c0e8107428240c0d5988a045084690195071111800704440b0000302e4503040010000b04400000030380081070140c1e0740c00d814401c55106030036294a1240c041c23070603c5601802e00c00000100198241400c80311050302c0126140c0c403040c07140c0c00300803441800c8010b010000303422840c1c044e41c100b036140114140c84055808010410020b60340318158003090715030068000d2003241007090700074076038410484c141440c143c01440806d509006200050013041803c540041810710030b204039070307610110304080000b684d18165001d050301c1e096403c61010403001d124000f036000d04440040350700741d114089441c00b0a006000d0040041c1d040b00c1069004c0071869003040080c106003801400802903055682d001a4446443d0000200250800c01030200c2c5880c0641151691500a6100c0380c80c142c2d84d9401c038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902747841 1250 902746591 902746643
    0x60c0706090317070302090301140123011413030308010602011b0305150406230d0305180f03011d0d05040e06130b0a060c0219030f02151e04030c0f180207 68
    0x3c013002940014101480d810300380160300204d80b0041403e0f0084d414000c9a01032001c2491488810302036040101801d82e00c01d5104041044201201c590341e000e60462403e040d25403030005401080045e400090f4131481480740007040307060b0f048076851b041807441d41203015001c0136002e55070038510907401c10341703941e11445120020884101c0710100b0840001040c50400c0030038010304e01c500c0103842c078000401c0e0031104a4002e6036036a50a10750410b00100092440c0e0f080c07031710b01074156180505110107207645402080000540000300c609200b4103400c116111301c12409010844240100131582030b05006808200c030040009001c140e01c0310301408a015501c15038009000030300d40d000a403007541804a00300c0c20b802c94030603544803543c0c155180c504043e030b1007241c028003a041006490140941480c165001c01c1a10030071100601640c007544111a0404d01041c4c0e20750054080000d01a21000000c5040b60183c806140900e010117052f440250000326050303980c1d0342c10781d0544501b85405810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902749091 1250 902747841 902747851
    0x6231e210c04050c04090b060f0a0f020106150909180210021c0305041110030902061914070b070c050f070f061d0616020f04090f02030609060c0706090317 68
    0x28446160280004241c0303007200103454203000d10b1400e010b104051142c40120380070780d0300300b07540413903006003101c040f890702d105004004001c20030215440c00e806038007240c0d490000c9002e17070080c8400381d00c4003001d07618880076030fa100022400d40c64003005443c1b003503000515400750310030400e1480c408179008031350383c103840011a500603040160300011804113a036009408442901e8100054545640ca90fa070352a9a00d0034548100e427500008001548030343c10410b5070030ba002d010140c0b9141606c1c00c81c5005007403901c02001044098644007c8840142c040d60715030740d0800d01c107078260746803040e0070303208000d01c03e2058901c3c4c01001442902160704200d1302c802003e2a03010b45009a03c2d1060060040721035842200500c60990300504896503084141c62140c07a034184041c0350626144001a420000e10303000c1e40d085403e0003031110502000c101c0109115000784c00703482003a99440445030325000f00322106c0c0c0f07034440305000301c4010070040d03440198203500ca41000300c0d0b000c0452440045804040314 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902750341 1250 902749091 902749129
    0xf07030b1521090f030a050c0c1302030a0b09090c09040206040b0408060f0115090e0a0e06010305010501031a010e070806040609021b0c0117042a080d0306231e 70
    0x6018103510481c9403643d4085203640140803034640c2c600c4150b44070700c80d0030580400c2003030100703500610000c2031210308006000100a041d20240c0e5401207400f03508121822418035140c0302c0090312504000400510500d4081c02070200404c802c41045002c4602400aa8100388103010200b0349102442c002c0011b00402c40090005141c2101d0180040105030010480c403003d5401091100d6088400c400507a842c441c0000d11565403030100303a008006440b1040114401c000c000400c1c403c040d4462416a806640b036180003403e044407101d92014284203040c0e07418902000921100e200e4200d550f0403e40082000ca821031b515000e0500b0f9822022801c6c00c50402556150a502c008100126240e1801e00701401e0020300d040d010900c0060040001e408c8620451004041030b000f06c28045091001e04405a001c5484050745503a50301c0f00c10118011038580316000c00c80c043c100540c40d82100c9031060107480c000703200091214022140c0400c452780180030403051540ea403224082045501012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902751591 1250 902750341 902750377
    0xc0e0a060807060e0907320c0c010516060e01021309050f0115050409050a090f080a09090603021e010e031f14070c080a020a1221050f07030b15 63
    0x340507107080c0001c962091080c8034030301d105403110f51503030040300c1d520030401c0c28080d40300d880841010094411101589041a00400903200300009060141509486800882d18141c13059001540c141c0320340c00520490028108140300020400d40002841c1e0b0040340015050400b80c45495500d1519500120006a1210100825100d2030f540080c018841510303000440f40c03640e00050001d2080b4061004229100e20000b04036403140e400c40703840e05900c104616182170b01c9060440315900410041c000003881d441c0300240c1d074000d81c0038003026207400034030042e100600c65550880002000110340c0c140900f102060025a6060020014920500c000392140c1107181c44590202c1d40324581c8481511000b906100c1582e60080100a0031544001035640c1c0306521032003a0300c0e04186e114014000c07140b6100030904294003e481940240154043e070389000300002c032450a45600300d0390356075403190160016810f00d11a4000c1d10b240d4801401081880b1600c01c81e05000341e01440f000030703c00c4401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902752841 1250 902751591 902751599
    0x4030207120837030c0e121e0c03100c08010b030a09020306040809190e13080c030c07060306050d0f110a170102072108042319030201061508010e040c0e0a06 69
    0x3811039983c1000503d000c2080c1143c00401408440d01002c0f4580a0b0b441980c4c0c003103d12400304604000c5406200700e404041016803080ca40d107a00080f180c1d40280500215940402c945d8003d001b140d00994640640c185e00b0999403194940008141c042490389034402c1f4409030f141844102d00a60003054025921080001401101ca450a020380c0c65040040d10422685005944d5103400003910200001c0e050400d0920040e18000c0200040307950200069100304500d0003d00101110070944060025603500e03410040b0b190306884025150ba0a0980c01c100044c8084001001c0da2400030401880151240442d4110b215060075045076a90700007030300000d0094000d07641d40000104d0100c40c0a81c0d0300000c00400c6614090002083d514081d06581c032102c42481d108020112030300222a10115180e4803505a0b604005040e00554640364003c52518204d1045140002039610344a41c182d280604442d208240144280e84500190002241c18041011141c1c083c0c00300c0e000100e40a410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902754091 1250 902752841 902752927
    0x803060402301b0909040501021902071e0b09093102090f070c151407021e0f1b0a03050118120305010608040201030216080c0f070509040302071208 65
    0x3019146000303e0303806400d1032451811940803600100001e880c1610b4035207175480d00b14064004c00e0360510000301e20303024132816640e00140200450303100384e020858a003080e2000311a114020301846142c580d08201c0c403080c6041604505410402444132401264018510740c1212007090b0141402440410075840c02c0d071820a41c8150040c440c83d4055109082c4820b018200e070004000051060301c0407600c02c00401c0180e07200d0581038074003d610310b240e4034214500945440c125400d40b1840f0001364140ba4400c2d40c002100091881300d40000c01c0111190300e00340c0302012045000c10f0303015403007000100014000b8080c001d0240000080c0218a030400d01e0910801020360b448182003510b004010020b580d40885035503009602800c005988545c080032280d82820103200c0640801c5001925000c0780100040e40302c0c0403500581942c008a03114010040048810344014005074011401031091840c00b00c08005901d1180941e0791402c83d80700c0c4a15084000708a150405900c05982c140c08920 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902755341 1250 902754091 902754187
    0x11060108070f0612020712050403051009200d050d020a1208070815310c030e0607030507051c0b0901091814120309160503190803060402 60
    0x258094031a1608240c4540c5042c010b920440c010004a42919504071805a0469440f1900004044d0010740309580141056119110869041c802c4200d120540000c4d03100b03025800303610100c008540988140c001c90a412002c48081c0d011b10351264050006004001085452081da0060f041c1d0705d05500b4184050545080c1440600007854200282d140d800020b665100302c4203201881580440008100c03e43c80b180d2040740e90307010f02c0741201c20540142d81250107400b5040d0080c0110242158128150b901441c41d0355481e0b0700000c042140c03140250040f650103099841c282e414481c001d1092807c880c686004140c081e955520950301c5402d04c607a14901400701104184607204109440f6000c850303041001500e03d082084a0001412045c0109444442d440c001c5070b45900303008980c1a15860080001101c0c0c0c41080d030009003604010480d20a9101c44603800040109a6200c548440d4801040a68403e82c02c0220384d5a03110804007080000d205242d4400c810088070140280800c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902756591 1250 902755341 902755349
    0x30d0f1b050a0210110906030a1d0c060f03090a02090f07030609060e1f0b0d060f05090c0307030f18050a03080117100b0303070803040506220c0915080d110601 70
    0x100c002c00070352906503000910310650060407200001d1341a15659240e000b40030b54204558001c000005000225201d41c014640a90524441d423101310103c900d819500c15914920680002c1c003404000d040c00b4004001e103078480302e9070068940c650115800580200002c443d00c05400e004002440919031303041c4540400fa0030b2400e070030000030b41044200c011140c3c000380454040380001d00c982c0d04101034811071100a2041040050320380001c1c60440d0058900e50050701c07102c8042101c006614030741500c005001e901003428144c0b07903031508001200500072040a40030030a440d0800702484030260014090128080c0e400391500c841c4601d0010440581039010310b001d60448944c1107205107000c540e41c1040d00e41c45400261a106110100c0d045004000c4050040d480c044204014010003180152040e09200c2c168821086503401e0841e0100d003450b000781803502007020a00c96501c0c02c0d445031007041c0303040082c011156502c103145131404203c079800c00c0000b031072a1031400c000130b0100610b85c050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902757841 1250 902756591 902756597
    0xa090911030403090b0c160f030201020124030201081b041205010506031606260903091207060c0f05100905010b0109060e1806121603120c150b03030d0f1b 68
    0x1400d02e030324014005030441c0502030011030009840080b0690800051621889010f21103001c540c0d11420703d02c11410b44d12040c1e02650901080013200b20402d4131420280314803c0e0341c12080750a640045460b1000249080c00309001c1140e00d1801d150003070064001032289801c2e03000d03803003414a00542501c6010b01800c0c000c1d44801c41100103510b140003c042624420301d004401285420303820112840d140003017005401500050007280d00011004000002055401003620303945090450b03694030aa110703a60000306460f041c1c100050514510002c05806001241d400e842d018010504445a00c0811680da030342d00c10b07011526581004c100300c0203000c50f040000c088a1180d0202d0315a02149400c40326200c03500001031602d81d2106030b0080b0f460900c3d02200c1549003654800c0e10091040d000c01c1c0c85500340304000220b1280300b490706803801c0340d01c03070f62030440b28400e00c41410180c008540714550502090129801c00d020314444d91210443c4c034080807074403c25060030000002403480c101410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902759091 1250 902757841 902757847
    0x12180409050a031209021f0306081f0c110d12061706040602130308040807090501050418030804020a17010b1003052a070204090803151903020d14030a090911 69
    0x4140041502c4840c5501030a00c00380f00200c0034010402440b003040001c3d0b100709001c44515807110030000680030b00a042e101001a15240c601032641c4411086400030103108800228100990700d4100350040342d0141001c0040300c1c0350074006030808036482d001e800010080c2d0041c4500e01c0680c007402c00100407560841c104600c0342c4c09050b07202c01e00100040c0880360001161b14103203000c2e1050900441c2c0102c2e800307440f00e0f180e4903007139152401c030322800111034140784c00407ca610b03241c8034a5a0500440c0950f503941c1445a8081d505404000e100341e1b807200030064001021402c005140d40c42080850000800d04040000c0100c601c0c00005000b08140c9080b041044440144a4500c1580c1030a0296042c4e4080c806404030244a001002900035051842c40341c200003c0c1c60185009081015100c2007100c1d541082c441c50180c17851307507003401410030b04041003d800c09404002c90140518442130118441241d60780c619440310000c1380000b040301e00204450712052140500100000c4102d42c0307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902760341 1250 902759091 902759093
    0x120218131509020304110319051b0d022808010c0908030307141b12030601110f060a150902040e010f0f0b0901050307050702210d050f1e040812180409 66
    0x3014900303000b02c0501d69800808141442214601c2541c80d003001404c0314031000804c0c1503640c1e42000c0441c112403500c50119014510030b44000c5668440d0405480c0c452061260b4003008000081000241d5152402d052454042c1901508200245c1034000010550b0805414001e2201c4c0165001c4003054000b8414410b442c3c0c2d22526282c9281c603080d084c00c0d1940890108103168030510030b20550140b19a0040e60540540380c0061031280409032104064054410400c0743c07100d0310380e10780d402c880d04090001201c20082d58045031006400d241070082d0552a0500b610032680240c214900c503c0300d91004020000d03000c403000c4054007442103038488883c500701a21825010712202c040c18058044006644580306900351030859030018494442014509960890300703c40300404030303042c01088100080d0a0203a011600360006d4030401928200c0c200880741c908140d028801401c0c15000c1000080c503880800caa0382d100040c440c103a41e0f0b107840440c0445038480403070450b14003442c20151580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902761591 1250 902760341 902760371
    0x6150f0a0f0210020310090e0a0f0308070c05030313110613091e0f32060922030504090b0d0201020c0f0a05040c050d0b04290112021813 60
    0xa600800a09001c049000010000d0b400c0c01503148900d1240c510100c1040300d4100c4400d40b180840d0828101008001e07120000780ba1034205080003d083c0044861034130300004d100308c26155022055107000c0220070b020b692803a055030300c190762031201400c480d09002c00b44099104440c0034054102c404601e8440c8140ca01405007a141c840e845000b50341c4c00603010f03030711080d008145c007240c00f00310104400000003500d00001c1802d081d1840801035010328407502088055402016503698035030882d03c0381c2c0c0d0b0208105030080001d2240f07a1040110141d44c081c8070030000504400d038465140e45407181d08003003100341125500d043c15031048401000910151740c000c6109402102c00782d031240d07070085000700410310341c2030325038815504285440a000c4400b9031103c05406071025251042c000c4505407010401a180c1e00c0c010003401141c0075a082803c07210702a0003189590040c1000c1e01e003000b120000d002241c1288240e40d110f562905c051003041d1900221040e041e1041541c1040380c081d8035882c807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902762841 1250 902761591 902761597
    0x10b01020c180403050f0724050c0702060d02070b090d1b2307180b03060105040b030c010f14030a060314280503040f120b09010c02120d0f05070806150f 67
    0x2d0b22030781e0003004142810b1040c400c4910910001140325540c44103450000c6079020352400c420403580c0c0780020f403840d1010b1402028000c800550700300341416150703001c1018541c48042c003040f07025402c10045001030105100c4a20914650015058200c40b10001070601c280803201c20224942903404000010401d012440c4042101141803407400c518499251034409103400144000032036614015410314103030007118103a8010740945519980e21010710061b50034a00240d549031f040170101710880d505c56000c500c50840a03192540b02c1c04101c3c007800019034001e4444011860f100c100a00c2445603008146480c00c0d0705400500070080d807104410003020300a41e0118221100030159805e0220410580e40645200c1c24000e00481d920607042c2072500d101c1768111802110a0300250140e04184503808a0540b640c01411351300001c4030341040c840c2c0c03100f2401201140c1d28a10b915540f001849403e01c5003d050b265802c10b07003040b00401120552035810849134440410030100180128026 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902764091 1250 902762841 902762869
    0x30503090709201b060103060510060201051012082110060503040209041e06021306090803070816032c0405161707200a0c0501080c090d171b010b01020c 67
    0x30540712040a48040c1d0301040340e8265101354407030b1000100038000c42e80e110902801c4c00500a004c21591075405a00340c5000300c030b41c01e100d101c000000300040a0340c411751500040c03141451030300e403146008201401102c8030490346006450300041180b40004025103202030945410468210f1074140d0005025000c01440240034103401c0744581c3c611010440a00d800c00d034042c0c810b40d140d019031941c03030aa482c0103101e04000030701600c400060ba07003030102c111000a0341141109141c528901c25202103800c44140031010812408030301101c0501100745040000c0c10f421103251001845420401520030181030036060300c0b2074031515524075400c855400c1d00343c0703904a02030002e40d48039001076510015680728201c3c00141005420007615000c00d40c5507001344207910307000741c0c9074642004442c0701c5002c60b103126510508001c0e0454034030f450310140c108035100b45040070880d0062180414650488030405503a440084104100103c0a014210362500300303100520b04070100340b001441c81c80100c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902765341 1250 902764091 902764151
    0x180b09180c0d21030605100e0a0b090a0e0603190302010b1005041d0402060d06120c0b07110904110307091d03030f1308070b1509100f140604050409030503090709 71
    0x41d0030300f41d40250005401403000400300c0d00c001642d0076000e0000c0201003401c074814801e070580810006100d400f5541a0100030300030516140c01c00b08500c0410102a00e0390b5494420500212000b2001d15804078065101e80c2c000300300e103c9914103028403ca05011640244401403209024000c280c0740c3d841100b0214444868560701d5900202c7c1203031007092929550203041c60404515a4401084500302e40d1260b96120801941c41e0b40c3c0465500841000500c00300d03c0101400c2140f8109142d240c01c14090796240400034101e000007031608842d54496884c8503110132100c002c6051001c4114900080d4402542ca07529012050300700042d0020441c500440004401a043c81a01801d86040903400360407028903003001c04024110607aa0028a407007104000300050100e200c016101c1c007128500781d18040c1190034049003800c00c0740e01c1e81c0b401d41c100800f8070001950b95581d02170542000d0094841d5941e030b080c403101c01410300c0f00d16004031001d0380c04e049010100c2444c3e990207071080d0ba2140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902766591 1250 902765341 902765393
    0x20d03170a0c17160f1701080a02090a05151210060e060103060f120611040b12011404150303080c1e0c0d050c0a030e0a0510020f06090c060301180b09180c0d 69
    0x5501a900300d500c0d540b07081100700494001280c072354400078003040524002c5130500c0035603130703207241d1481520421101030b81c04850f00340500c0407506000c5200300882030342c00141c51088907465441d0045406036409003000703a06600a00c003140d605846104003400f94001c10380d0015042003101104000c45803002424255210800c201100903102a80c02821368914902d95490324001d0a4410100a006a510740605010301d4403140ca030a04c1401107000d00684101c07803480c515101903803a01c00c01400185004000c10411340703024600007a0742c0c240325003c086a1348030602041980d10f84181d10b18500240401004a052006000101104c10641c9413401c404198903a001081d2800e40950056400001c100d000d030b4542500070410841c12110201284c3d0715594030041c15076500e21411041c1d420040c200010b00c600c207001400e4108100b07100790040f07486c0c100f0030302150340104c0032580b00034400d44400400410b64030501c801c0078241c80c200c1c2c004040040c162030300228403511011141b032582002d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902767841 1250 902766591 902766617
    0x12120a020403020a03050309032e0e12040306140117070e1e07020303190b010f0503040c0305060106051c05070f120b03010c0302090a0e0103030c020d03170a0c1716 72
    0x540484010b1036010f84407901c3d95549142880d901d030041c0c00141e11a00905401c003090001c190011038128004040c0e48030f01d5000160701100400324000143c60b9402491425144c6160703240081c4006c44c800e000006240c0303014038200c8020441030300005518007000f600004502000120b420543d02501075184030307a119841001d0221407602008003808401c10b040040140d00440550300c203803054141c0d0002c034021321058034203d030940310b0800e010a014a0b4825212403050002d598410301c1014040c0c030030f941740e4442a1500754240d200da00011030000350300f40600c1c10300c0728150004209230000e225600340803c020b4201080200b1010821aa140d0740074568103854008402c0d2203c080d008028802c5e4042d402030103584540910790003402d00c07180000b0001e0750101194104d81e0075541c0d0000d40881c43d82005441000302200fa01040400e62800419080b8041400d01403802444002414410780c0e10283c4200c0e852007003104182c585104000898041000300c08a8001c0d900e0503556180748 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902769091 1250 902767841 902767861
    0x7020312070e1306081e1c11010204030819020106050a0302130f1406031605030c060c1501060c0b2208032e030308010e04081e210103020108091212 65
    0x7402c41d2540600f070b40c803200b240c2c280c450b4011000d440f91042070703c400186410003c0c1c0000516070324640598131000d50100c02c0903842c1601e159003405440c00c0d640d1150b04084a5007a80c0140e00140c40700d8000181c102003000b07030003401d8030010509000a0000615001c0012080d140ca40300203800389149040c00810320f01d050303010007003101c008941000710500d1080450940740f82114414002c2c4524002a041c1c403201220368021500020005c0007503802c480f00b0b10801d40c000840c0300c81544aa40c2185031222030000495001e00a030341d40e080c10554450034407007200030300a800d4003011101c100d102c0d040c850305402c440269982001d182a566201c801940b28505007821501c83e0814010414840b144092403044003224003942e00c0041507625000102d9001c07030140d9005020304010001103d50580004d0900109144001d0706420503080d842440341400211100c0c0000264031030043c402c40da0807580c080d030880c101c000148003a4603101ca411145200303489803950620030000c0001c1311510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902770341 1250 902769091 902769107
    0x4020904050a0e0c030f06130f020a080604020f0d030512040201120e030310061407031d040606080901110405010f030f0e1e0c01021605041806060b0702010e090702031207 75
    0x5016000308014503003615000300030f28521143c101240a040b2180e0703201e00e40002d004241d141c3e0440070740758544402e10200b810085210b400c07134010000000010142e96000c89000040c4204c8000e803200749094810400d0111543d0507241c40b505100e4000740c0800d84c400150751005480c802050101e442d50f000680e0204142d40c40944400d06040c49560040000b101941c05403003039294000c40c1320b03194503007a9900351488080c070701070620612800f0080780c0704030391489055101c00c02d003069072401d030707404038082c3d072241d4000201148100d0184001c41000b4070034120202c85508516041c14106400207114613190740304d0104254641749014040c46081d48a549099404011151945142c0c500238200b03807840c50043c5142d014461118040b540082900400c04800085c103a03221802c10040100030000c0b9298074201c490846030f16800181c02e8802c44015200b0b00c58000d894400c1880010840605542654010100d83d400d02550340e8001054031407011514422020a44d604082126021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902771591 1250 902770341 902770357
    0x30203190509010b09160f0c151407110106030305040501030b040f0533090109020304050309030a0c290d050c0c0d0302030109180b04030f020c031213050a030807020f0402 75
    0xd441c010a100220405600008804805030744d898420340c2c59105040c5911850624030b80464a03c100349660703031b48680c08035000244900040d83d00a950403d01e0340440c0c036500b10301c0100c600707840709000d03009400044140d5041c5280d00280009400c50f034000f0114001c62007250306268440c8098520356603160003503403a40805680800c82d51800d0b0728648110381c04c103140b810700381c0c00c0440d0184850040a0319071200071005080c0b80d02ca81d10308400c6100070751008001381c1301c40c0130512848549560601c108172685020b01248207109007131108803000c0411070b0140281c00f25184500e005094090000d03102c030a110354000090315070300c4250000c2d09100c0d80035200040e0086000009100da0141d010f0b50503640038034001c101104880202d03650a40b400f0704041c05034003c900c0001c2c0040c0c45400f1203404c40034280305a500700141c01c1c0c040380c034041e100f140c44042280040b030904038080844a000005050031603840001610355110303900c19105801005c2d014142003502d540650300c503501120540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902772841 1250 902771591 902771641
    0xc0c09070207030807110a0e22062a0f030c0e100203040506040e0103060f1e0c020f1203090f0601271d161512180206070308010911070b0106030203 65
    0x528140d00d0001003060304406c140e07110f11210180464002c000a0b0000e220b6101d00c088000050240c820042c0300040d120000c0f24015111244042031150040b08040d88000f4804041000d00c4460b0001e4240c2c2114605e0001305450a200d0401a42c0d2151455110b00e0080c0c40452a100b002a8100d0a41c440e03074114907041980010b00054160301910340b541224000d07081003009007502d443d44815103c1d2541c008220320320f011146004180d060b44036000d0151540121034032103c2085d00c0c0c0c0c0c00d0500308491070071544404004c001144009020040c85594484058406907040c02488032504201c41c0c900d00c1c0c0c50101500903039402c919640042103182840c0322078801020030714500d0365212041068940f030184100c02c0003840d401100c10301303480b007d0300c1c7c0c03601c0300649600d03441c90008120485610000301400074400000d0380701d8000034101c26003c0d41d030700c9850390304041040b0180d58400a003840207030b20401500000c20a1170741914190340c010301c2c016a0780d465001042941000841601d108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902774091 1250 902772841 902772847
    0x901060f0e0a0b090c12060d06050703090c080c01211811040b01091809031b0c06080c04260a0204060603020c0709110904200307170c0c0c090702070308 67
    0x780c0c1d94400600e00c00c0804040c184000110704040c0080d120040c3e070044c00745070f418001038040c2140c0c0c0c64001d82c011005007400c20045800d03110302c0282d54041d2040000301e40d07034801c0c0d8005d200f0b0310f180720b4001d8007200008000c8003690700c3c0000d00700000c5104c50895480d4400e8103210b5402c0c0da8000b050710820b42a2240010382103410a2a500504c45d2034040c0700d07a1402c0d040b50441d50190401004946911000d10010b885142c81d403000342010740d000b20104051071207160f400032503550100c90014020300b13090071981e080000281c013401e0b0240c448540e808060104102c0e01e00c07000c05444d1120f42c00802181000d0800c1c680516110010f5402540300f07050180104005505a01400034061781008555030255500004411103000401000d088201005098118103164000c3da415100c203084240c0b40300700801c2810b280d9001513440310300042c0500300c0c2ea401281c1030b0100f541c00a0702c62598903d0701889200e040c0d0b0312070300000302d48c2c081c07580f00001402c9903000344240c10056420640d900e90b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902775341 1250 902774091 902774099
    0x1b09041b1508010602190201181e0e0601170606070c0b0a0f020709060803043804030b1b07030f050903070902250503030406050406291e0d03080901060f 67
    0x1224600d00041c80000b50040340000745051001600c0245281514424410a015a00112441480311020080c0122140b100060070600754400c1103046440c8c2ca94140d0701e03030500c080000308207006401c081c10440f400488903010400300241642144c0304a8050743d942c0c547c0d14080c1403000b025849103507405c0300410800300094001d82d0210103504250f007a00d0a040c1c0b540d403900210341c000d00a80304181d00038003050118800340c62103c4002d1009020a41072440c51002e6040c20b61000070344414000700210b804c10800141c5042d268011420650101014240c0032038484c542c0101100582000501c021858019000d94110703400f6103009020f4400c007a8941008a010b503106c03c0101c0744d180400c803418071000f1410344400340000e500c000951700d1a110707511003c001d010090015a2000c1d038848a4002c05070a40b003201e1440710b00e01c3d041c007000e001c5840810003510115100135104030106040c40c3c0701c2daa515485044203503414200101c450b00c0c1e00384190700600c4141c101e10544001240e000c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902776591 1250 902775341 902775359
    0x3030a050a060902120f090615011d040c121401061413260705030a0f15060b1314090903040603020703030e0304030309082a010806030c130203181b09041b 68
    0x340c81400e42004840d1b40351101d4203603581c0c0301012500c403502e4008607001c200c102c0d84584540c45c143c030410090b90201400070030020307040360794548600d00454103000f0466402640c42c001d03035039000b190242c0185035600d030a0002d015184400b8031090660300000d0f130f013074003a520307081c585015264800b0041e803c10500b0092542c00f090b021030103110361050100000d00b925000443e03c0180e0742c80841081003d2640d51032090004086204182168032400b001c101000000003134000d0140b032501c1030f0b0506160000803180c10710b4402903540548c030001c0400040000000807113040f01e00c20316006a40e0005418201c005100380404900d4074000002c1c00024943d0004000307050310481e0b01074600c0148030000600300c1118000000c4582e0440c40015906580514000c992041016003621000348000c0000f40261088c00d0800c01900d602200380001c0d800300c25848504020503d008010b611441440c181d060850304400c18440d40040b4001030800440c445041c001000d140c4040303a90b561220a81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902777841 1250 902776591 902776627
    0x906090312110705031209070b0d090b0703090c0510090515030405070b1c1107060e100605010509011d0d05100203070e0904021c0204020408072c010803030a050a060902 74
    0x34500c0507040c0b80e03020700c00940c16411211070380d42c450000d600d032890061241c10410401800000c03540614100003c6c02d101640040411107001c0c41e00107410300e624900040901c10107440801050300e02516540002d0058240e0001d407a806c0300c05403c05407040ea02210300300025080150001420001e03094820343d070002550080340300b503007a10b2440f134440558096030f010380c0940107101e640b0881450840034441d0301520780180d010006e2483d1400980341c103030944805103803a5869500c0789040b0305619000d0301c2801d0160000b460010300d440401e13800240724951038007856148403590303200c4410981e1080001c424056000c81501c0078000c2c04c10416009400455075400441d40c0021380204030b203081d03a4854443c80d0300600c60003c203543e001807010144120001240c116600b004080384000d020428100206030f4008078508a030150300c0a000010500d1a801a036440341c0f03001400f0b03141012054036030065844000288507690240b410010340901c1d0f2000c3e8205d44001b40220740001581c02e6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902779091 1250 902777841 902777867
    0x403030e090604090305070803090a141b01050f120c090a0b040608060f0603010e0405011d0705030f0a0b0f101e140f09060d0318080a0b01060311030402060d09060903 73
    0x1040815910780d0b041c442580c0212000500080080000000180d5000003542c0c00498110031181301180c0f40d580c0e4500b001442e01c05d00030340d91010382c0510b40034640c015540c10423842840c155060036407036060110340d40244610720350600001000581303080180f0301621038042c801000c3c1d00c0f079103580300d48111659025000b020001440c8500295207410102008403245101401140c996071810381094080c11000c2c004640c11354962211585100000000121001d240c81c09803800d00d10340341c20945402d003a6524544580c11440c01d40c400b192400c030a03154070200d9445c440c100d540c0c6030303ca10030034000180c101001101d103002d411a000038480c9901000d448804070740da44856000c3c401c1000c04182c9070b1076503602002020025541b401d000190007407040c0320b42407858000b60f407040d00140403566500a8000e0b584804004000d120710807000500500942c1400c00c480611914840b2040c0303c01071000c0e0085100041da2900e01041c2e42c071041555400c050b041040303c150b803400504a03c00c6139a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902780341 1250 902779091 902779099
    0x1209030c061b0308131704060237050709060803040614091f030e0a06050702280209070c050618120405010905091e0a090606060903111201020903030403030e 69
    0x4030200d103050196101c01e851185202e030200d05060b0355030303080301c20040080114a0314903202600f03900207050054032119403429040110307100c606040340245841c00c5160740340c0e20303030b900300d0600340d58030409105160059200d0000d0b04a1002e41c1d0500c41e1505d2842c2d407090742c1d04d40c41d0002c00903440f0004006042030707400666034054020142c84c40c002060241d544490fa118402c0700145012440c10401c134181e00140341008113035080c40e42900d5090203c80b44d0183c805030345420402c0f03a16641840240c02010f10a50025041d0359400d4142d0741c0ca08221800030300406111000c00c4c0f00602846007070102c560302004a039081d213000c5212040349042d0403008080e034031846880d01c0c070920a94041d82c0a444040c3d458950140c50001000f1000c100600f10103150240d090304080c40030340ca60303200c40c402c0381018804a0b0806451400400301c0c8c0f040c4e40700e40c08000924405000007049126026040c01003201d010030420000041d0780c0c020b00c1140c0711254503100001d800410190040034610034510115 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902781591 1250 902780341 902780363
    0x1a09130b06010e0603181204170d0507050a030c150c030b0307091a060d060e131a0c030c030405070f06020d080c160206130504140f06030a230a120903 66
    0x90010740b0100600d842c0f040e4090030130700018140312103216920b40644c01440840710245080080507280d6402904a024041d0880c01e070341e01c410500300a886101400c2e031911500d414070b01d4503190b4031107440f100028100700d03a041103001407107284c8042000d0400108000c21165000d01c8010f00240350880c4001d0190240003800203401100d40314070804c541840d4a091000101c0c0010010542e10814018001940d03410000c40c0c05402110182e00c15841c8124070040d802e11820040540c25240d01c405008144020402c0b510140311000e40b508003150708600c5449881d80d1502c6030900c14160449140d0040306c00000500582c0003e00b0103211041e0303100c2c81c200c0c2d2212100081140700d4180410b2400c01c02c00010f00040c01c00900910b090f128001c1004407007519032001605464885e213000130015a1041031003c600104030748a500301508600510b64691595220a011060802d1031304812855001e004010242071000403086903108450406092002001520721a860702003510031766824 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902782841 1250 902781591 902781601
    0x906030515040201120c05070c030302031b0c0d030c111002010515060c0703021203130e1801091109090a08041203110a0b0105240706060e060a05010509041a09130b 72
    0x700c41014040d903010384d501d5990341c00003d16400500440061030341005070400110001c211202c2c0b114014510175405142c2c0e0340c0305a1042c00701c40040d00700c00f81d4107801101c907104480c0e80d1101c0182034560b05080c01081070a440c202220420340040510f030300245520101100135906600840c0301d801428408015400c48506202441c054040042c10310340c0550401d0016283c8550000d04001d1040205c902c0e0078a194015541c50449510992030b00040310300b400320201f1865404403210156100030040d00c0c8080c0c60305024181503249060048484030040b41c0c0703d2000b40500b21183c0c1c7c00008165440341d4070101e009554410303c40640c0015409045103960020100300c8078801900803418181c1a400c01c01004410401091400354012442c01d411007800702c01030103014424004c1c800010150301d0000c40000c0303244010111403040440c3c00381440241c2e0440e00b03407602d4030030966000800c041c0404210888440060106910001c03100c1000504000b0000130419213100b921015001d0b04d803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902784091 1250 902782841 902782873
    0x20c0a0c090e0601090902030c0616230d0f0306150203040e0a02070503030c0f07061802010906050415030e0102090306011e0b0f03071b021003090b09030304022409090109060305 78
    0x1442c1020681504140010482c00c0c290b07410441d00c3c00e000500b90742c50b40c0340ca500020030a9100c000100910001c07608504240030750015000e0300e030a0340119941040300b41141c1c081d00e400c5060303070001c1848800190189100c2c03180d880003001e020106400d400c007001c100c5010b50340f6002442645c000e100f4620003c0c018038514001d8441c0c05900038001c5045480700b6041541e00d0300001ca507210381c0c203002c0c004030010490710b004089013190502000c034080d02d40b038000100460a03c0d04801c0601c0342c01c10003002030541c3c4560140c04a0700790301e00002c0d003d804110943c00391090001079607041c0308800010411800c0b9108213040c00a07011059188030b41c0d9804001c0f02d0b8042c01d4000e014100f000d00000d18004d01410b065043c100c01c404030500d16525035170004000c01d81c400d28940c000b0741d071400c0d00030400074030b201c506030003e1040000f1811444c00c0e17400210317150b182d122030689040110003400103110302001540e9500100900036481986c49600c008010710b25884281d41700e1042c4540325407a005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902785341 1250 902784091 902784101
    0xa060c0207081b06040b220314010b09010620241f03050d1209051c0f36230109090212060411041a0a0f081621020c0a0c09 54
    0x100c00b0701110f04140c5032850102c05904074034080c05400071f5180861400c565658140ca02440c487c24036041c41d100f80a100500711002c84813814041c184000c0180144c035005819020100303090350310191401d0a0741c0455041c503601c071030500000ba409803041c4000601c0102424441c1c107a100074003c01d04280300c807000c880c50003844040c0494000d225402c0540d40718800c0e0000d1400d68000110b400210356680c2c5203400c080c816144000743e00c8000d02c0c60105c0d4003828520346450310f49000095480c4103140c07007045091004103201040c40340c0d940c840c0d400c40c00d90701d03400060021098401d814000c01020f07103483d00c000c504407400240400c401103503448480c030a46a400b030000c1c65011160b51801c06120042100316003d040c0d4010910001541e520701e010302e68240e10002e07a0700ba0320f910100401810304002074a441d400c2c01607070810014035a800075264810004d0a10303281c104002507600c0d14111846034240d4104040c000203006036003c40000d44103504620841d1403948007a62860a44100c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902786591 1250 902785341 902785393
    0x11090c0f03251404060c0303020f0c0703021903051b0f180f0a05240109150e040e0a1e0c030b0103230102130306050a02210f0705090109090e0a060c020708 68
    0x8004e11090200d1032040c101ea5000070f2090900501d4400002c02590707840e00090714071101540035600910440c1403100c0980c0c1c3c2440b0000c55090810308680d2820f4440503000310081ea00c49501d00725030616610354080301040d040c00340c0b44411914400401d0418440221170000f9446241004101805000d11495108030070b501482c15003203030707030818038034100d84503011283c1006414840480c0c16030100c01c400f0460380b100c2d00c403010b80d10450000d00095894003144519540c03c854500e50109040c8840d9014000f0071440020600c0380030700e049010800c00382c0000d00041e0120001008100b0310b19401c00490307040c600030040e0202c1d030010a50070703481060101c40781080044002c1001404a80005070481c030700010260070116038401400f5400d840c2400c401c807240100303080c0405090700801050b040265450001c0c60010340d0800a046100607103e9040d5503031b80e80007035000081d800c4c0b1421084a510200074410184002002503881c880c40c0203480360340c050300c101d103c00100100c5000703041c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902787841 1250 902786591 902786627
    0x70501111608031009050115031506080606070f0501060902071e080406260a09021e060304110102190c050f011e030b030f0313031a0411090c0f0325 65
    0x1065952040c12a81015040308613003000342a01140c032031902d01405018113a1403900c0701e2260001d04006040e2924000c41d41407a120720304083c888968081c20703d6610130710544580e6076985403440d110b1603c0f4152080941117500c3c03d1004101c500140d00100060f0380110b03210542203920910154007007083c00c0004050140030401001070380d02075820480305c04060f401131000381005c2c00305100f240d8812585107840564445081d4114548040d0410b10406100130040100b1862004200c0610014202074007501840c0002c018071fa108200320710350290441d140da4109035162510407206000b41c002c0520031801c040d8500c0255214050b01d035014210f03030b110b5000c3d0398005581540182400c000f40c3e600b6014080c01ea0b000c60100b08000c007428071540c03000c0038040b4914142010400810011200039140501c20301022881e000466010a9011590310f019501d03130030029031040c4904810040180c0300071040080c06103410390025844101689440243c080c0e40c64100c0f0100d00b80307031541c158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902789091 1250 902787841 902787877
    0xf060302271603180506040209100605040603021606091506090e030904020a020a0f0b10210311190f0203070506030709030f020d0206031504061410180e070507050111 73
    0x9440e1985882d03001a1014200012018044102e201c05102c40101c1516070f6070002040c0421420440c0350720350f100e141001c40043c006d081141c020014816441040105600031910000d00301201d49080c1509030302c2502045a640701e8a811401e001c42250400a0b00d440c2010009910801e409102042101d91018600d03051245040000941001c2840011403050440150000d500805034001450040348900701b035140020421001110642080d8001c00740031601c1c00d03072202042c02040740b1031384c141400794203500c4068043d40b8060007401d54110000c904d804103401e1100c030340380b101c9496001703800380d40c00e080d200e10038030400e0300c4180e400c04001070056004201160543c6030b9010642e100422030702515985030001030107500181d884402d19809100c40c5d405504c1d0a00c51722000b0010030201864000d5800002200d41c1e000c0304200007172100c01c3d518286c520301494254006041c1c0848114404c0c100b4403002042c1d13412010048800750710b0802190302200c2520b090b6220407002c8805440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902790341 1250 902789091 902789101
    0x70f030e190b091c1107090c0e0d03020c041d06061e0907020c040c0809150c0d0e0a050304080708062a09010e030d020f0c011805010c0203100f06030227 67
    0x2800d01d00080910180e402495050640b0100a180c59501130310203640380c1c2e80903884002c0e114189480c55101107000b0f0724090b50054a160040c8041c075440c80c044a404101075000c0c01c003641440c492140d2107038050300e081c900440f8201c06000004404401400702d4036a907481d403081c00361103101140500c01850311240c01e91450300d418001e06902c10702c50b1055505025501c40410709468030042da66011408040400040314006c01c0300d40e010100b0590303248001e04002081c410240702d0364100802c078945942c0103082400341001200641544602200daa80b076980c64010380f504810300a07441c1c01c2c00f90002003042541316181e420400910450041280c102861050380f16038024407440e81400740420421480703079401e02041306141c1440e00a8210b50b6418080c01e420114010419818041510b43c140c1c4056900c904071410394400b0f00f0720b8004000306000185ca03285401030a840b00c0340c2424145a0a0368160300702d9070469100f56941d4400e20307480c2100145444155407420442091140014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902791591 1250 902790341 902790353
    0xa05061611063c0a05070f1e09050d05030706110a1b02130509070f1703040909050f060c1822090204020903030d091505011d070512070f030e19 63
    0x1424150b9141d04005001c0100f000b2100800b01d6000761200c3e42e11100c1082210015401213592020540c80e06650008030040080c1880d118000c440c1c030b40c15003020b00116514003501013000030b00002412490500603a190090341c950100d80c0c1200c4884c10116058800b1002c1e1040d2501c0020544508211041c060b40350b0300e1f518030300c4400b41d034090a80700041c1e0b0482e89510840e40100000e0000e0f00341c9030b06080da01000d9175070036805403402c0c607201000800078044c0401500c080e64204100820082038506000c0d1030b11065080c403801c40d02501041c0300c4c0e2001c1607001448202886010403002c450380c10304211031555041d0f82c00c3e18144400004071444111030340b0080e811803000300010700741904c6401203840e64128549115120303075282a124140400e90030302641e080b500e400144820341c14103188421703442006c0581d000410040c401315514500620940d0581e455140700e4221b546401d14000340b02c407500f41d001c140880d00d0000b104094101c0415442c81e244820320301203060312260b0b540c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902792841 1250 902791591 902791621
    0x111c02030c12070626070e010e100e04020c031905030708011d0a0b1201020f18040203040804120f02190e0f0f0c0705010f090317090a05060109050a0e0a0506161106 72
    0x317690500c012090b4160034504020055000b8900d80d0356035804403401d000003511440407000817510441c0d105110a5034180d008000c1401900d0a031000b584901805400e01d181d4007420041507035a40701c1e40c4445820583c04000b451080009995125159990790440049030300541c0c4520143d11402c00054140c150713540004003d58006421003c9080708807106508a81008440117408200001c6c6202c4c9002104600074042808171021803850a10344da84500c240704911480443d0b10101c00540284504502d25020300c580181c2403900040a6100f0b40c0703e908103a0240d11403140d17119001c1a0140c2c145401d1a12866020307550964a4891580d09452174000960440c0c0c03641d00c3c0d1840c2c0759200780c02e00580b400c051194940c440101041090040360050003003144200c2d0f404284074101042000458034111a5015400200b03600d80c400f00300c0c040c04081c03242d99068440d030b80381d0100f00000017400c24451540510f65030101400100110b13040b8060300125040740c0e101c00301140484030310000c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902794091 1250 902792841 902792867
    0x10e040b070e1002010507122702010507320a030c2406090c08090f07060509060d02070c08010b100c0219150207050310050f040609111c02030c120706 66
    0x40c201d51a0b071001403902c402214807600180d44800c140400705400c01c11908005006400c00d0180f003903103510f5800340b81c06110713a0301182d41c0c00048031015a40140100d411660700054011481d800c240e001e2221509180e640c840d030246550004a482200403070f0280b0010751603626030340d1105250f1034026000261342c1c0c100411011003161192900041d1007a0002019803c40207e03030140400c0e0041d2a040b0002c0034081c254103c840d4150880001203a80404d480c490b0414a84400d0fa00740400c0107402000c0140c2013061001030000140f00d8641281c0049600c0b440003809268180401d1003120a28030f0401c4021810140d038800041c5080405600e01c8070140c0c6c8a00d03203182c0d8501c0504076040012540001503009a03400340010306040c4005401442200410720250800070780107460403900620280520341d40c0e00e484010040c4c4414000a00e250041c0080e20034034101d2071882d007000700001d04a12034810b48421040703500f08195014600000f140242100d00c0c507211040e2120b9a445031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902795341 1250 902794091 902794097
    0xa0f140306040507261e010302060d0c0c060e0a0c090e341d0c07110103090303110324040908040302011202040518010315060b04060e15031f0e010e040b07 68
    0x403031380e1761041c8000341d01c20041060340c40b142c4d60741c1420400d0051b0009000080540200c0401c0140003680f101000c80f0390040412000140086e900314084411a540d6a03005211605008a012440e080003640c4803607540243d050002041c0d0320080310046481c03500d00f800c1c3c9900004001382c9801088001c06500000f54500400ea40711010741d07038008159aa08855a0b01c0384000070705e0412203001c0780d0980d105d81022502c515215858444a034100300341d00040e410140c5801e00417003058030a4000c2d0301c05214008566480c2d0811134001203800c01424a091010780450508882c20f191070f0107000e181641002c0c002d4a41401d43e0011160360700700e152070030003098080000096a4890068200c8204241d5a0210441d41185000d198940c0303500d08084440b410284c00303022903506c1208503000c8030311608141c00d82c405800e001c500355a400200c5503000d080080100320220404900d0f103290402c1045076407103240c0e115140000d0120082c014072015041c24030004001600c0c01141f0381d00020982 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902796591 1250 902795341 902795357
    0x30210020a090f08011b03020702010e090402030a061b020f010b060a030b010c0b0103060606080906040210050c0f0102030108010501031e0302030901120b04020a02011b03090302033a020a0f140306040507 89
    0x10000d00000c20261348000040e80d55980c1d104160305141100d20425481842d055240403050307000200504819541c96100e0f20303560000c181150b90401c410020300d80e0003907050020680030782ca6080f104180d207442c0ca0150050744502e0700d003420103100c0d4420281c001443c03203082c47c505c2d050031001003810b0b04885048c01880c0c0c8040c4c010a610011184c000d6108100100e1640c1c24414000e2501c031003d03001c800c2071341c00312041c40016655213600702c1200e80c203842c1c10360f2249010400f503071070900341951100341795100000204250406422060503a4083c0595106400211a1414844a078000041c0c016001413103054110b40c400c0408101c40a00c006011a20701d030010b00040c03c0343d000c40b1210b030141c4e40d10201c090110601c090f09540c9003403a814104403242413a10b003e5140e101d48010f640300840c81d00444600e900c1c00d148002d1000545c000e401d6010800a404000258046070544022450680119000d14801e0b1140880440d08081c1241180c032024107200c060100500807805004103d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902797841 1250 902796591 902796599
    0x106081911060c0703080c0d09120327081b010c03080c0901120c081e0105010e04020304020301020d050405061b090d03110a061109090609070f08040309030c2c04030210020a09 77
    0x2c04c60000a94019012035640340c4041d4001032404214101210a000080600f0040115170f00c00d646841505070510760140000e0800303500b140440103c914148200b24000071403400c500080c4450031107001822b030b6441003021001980c00019050700100095401000a0071840040014220059040c1004060080045110307403e440d0010040000581c111082009807040717005403e401a90384d039410304080d410300300000d1014070380560490007182c002021404540b000d50480d080480101800c20681c10145801510740d0820750300b090082c01407682c000c84800010003100c40f4080020044030440410b65000c5d034100741d50344103039011030049580705e00104145000305080300c8502011940d98040764410080000c8000c1d0149000e4540c4c0c1c82001102d80e0001350310a1a0025800c20780050342c6c1e980b074102d07404060394200428842030700e5000590f502d042c85000402c8588200c102c1040b0312820710101840e041141c0150050303100c444945101d40c2a940100355101c0180781c515000b0b038903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902799091 1250 902797841 902797843
    0x10f09030b0c1215060f0912030d3306080a1b02100e0601030b0703020c1905030307170f0703020c1204230102062a04030f050607020106081911060c 65
    0x10441d48000300100019160303d94004203d80b040d8070480840b00004203041c0d80000c03919074000e1aa00c8405488002480040390759920b80041038100b922046030f46d18030018250034050044004c009440303441c040c47c2c44610340030042081c1c4d80d502d20810945019490428101d680002c0504103104032075070345035041d01d4200d90b031a00d031075400c4003034005281c0380f14500640c404603404d402e1b5040c0309130844001400050001301c00345402412078500541c07102c103240605130400b2800c210606080300100c2d4082c0400c14003101943c4200504d448141800f90000480b8114503400c4440003024484040019074640c000da02901e0150080c0003221404800c000c003003411030f4810b410100c001075400031a000c0c1c1d4440030340042c55021080c40604200d0511001d22091381080c044cc60060403450203000c1204081d03003054070003c64100d0a40d100c1d682d21402c2084d21951300355450b10055080060200300c0004c0021071182c90a40c0c2880c40841580540f100c0207261000e5035000d0340f241c4100145807072014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902800341 1250 902799091 902799113
    0xf060b0d030306030b011d130c0e1306050f1909051014090618070612020f0a050309070e06030c01080411180115030b0109050f010201090c0b09042306010f0903 70
    0x446502c0003d2040e085040464108005a10200c682501c5880ba2180c10304000c9400d074014441c0c035400001c0000320300c0e01c078026000c03c0c0c214903411800c000c04c00c242d8510003500140032900035030041001d41c6a003801140c0590084840410124000d0070700d20100d2115800204001d00507030a07100c074400c0d04643d08040c0c401141c1111003241d0280c0174000400d20070b019482d044010101c1580420741c01c500120346515a51244005000301080c4407154404290106c0c4e07514946218003682d00c0d00d400001802c2038009403102d0240784034003103002c9400710700441d10700d0282900400521118182200440f42c01900820450b000351a074200c422607500e1b42c20261754000740c00e80350140e103503042c4114070724240c800380c00a000b01410b04420714942d98025014800382d520580e858103019480b480140d015103807031040141150114000029001a000301400302c0e18001c0341c003400b11200726034071400e1040038860741a0505900501007406580200c0301c002c242c0311303242020038580d650703601e40c0c0800c1031f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902801591 1250 902800341 902800343
    0x50a05010e1318050f010e061315050c2d0d150b030a0504052503030c031b060c020c040504152a020706140a020703150908070501150f120f060b0d 64
    0x400d43c42880d01002010f004076442106058000c02011800c241c1050fa18200035080f6541c0006a03511041844840740e0704810b16000c01030140102c1c142803000041690007002041081000d07241082d461246030b901c102d41d030b00f2070010301605050001042c04010714140e4080320013280154170006660321031a020714864070a00b00001100e26043c18101c0c1042c442c0343ca900048070801c0d803121040c000340020324040d04e0f05490120448001440c0555181d06000940e40003240004011760400c40d064012255032001982a00c450456100c02c9c4419100300703490042c1110382400c403501e6448001c0d030005c2c054241d28a00003c0540d403283d001d10307100d11600d1202005070420202449400d0304000c010841200c15070441780340c5550a4070003074440c01180802003094200f0347d03c45400111540000c0c00c01a005100c29035190090f0be4030038020203030441d980003407041004000a410050030050360445862410803010410f09640d10a02ca08004401322085a41c0d0744c00d004803600d034a96548025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902802841 1250 902801591 902801621
    0x4050a0204050901410439080402060703230d061212081f060207031406010b120c0f0301180e010e0304140d06050705130b04050a05010e13 61
    0x460030502400b850f514142c10002c074612050003164030304c00b40d8461108600001d100b400036071110580d003045d81d1400c5500d40c542d10605003941c24450350010110a2031100c080001501c515030749034005051903000b1003407080414201000900542032440080c1100c43c0f0038588520701002078281c140103a5640703128015600c6000c103600484c0c0589210b80340140c1055540f0750111001030f83d0351224100e44024440401c904180419030403562846d40d01940c81c081c0c1d145007000340c1c43c0d140081d07403245a1310041d2402c60170040ca115100070017040d039505231041d5903881482e164a85a244044540103010441d01d00b4040103101c84c50342d40c82004d14083e16405a0070710410195a400c0c0080c0e5014000e50301d03080e4035003481d0a608140000031a41115180c0b50045844009000025188181e428000e0142818042044882688600104103440005640d040d5403925848450b10701c0c00b450007201d42206828109110307660154420018a0200500e40c17682403c00070004400d80c1d4822080e000700c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902804091 1250 902802841 902802847
    0x10f1b1b06110f0718021309061202030601050904052104051302070b09010b0609041521030908070303080f06060c010c03020c10110304020103091403031e06041a0402090402070204050a02 82
    0x3000400d116003090742d503d5600428505081a008240000074504010960740c1e0004840429000e105400001031a00e9001004035542e5040304e101e8130602201c089210f40214000420341d8508140c615000e950042c00415010b400300f00740340c4a00543c407000003450081448005503540e603045120007070400010004da100c0341c4e145809142000b010700f804001d64103012041e40b482e110303042640c0445900311004504090f1921200503141c025400c900030144000b00b941c03903150309041070031410510036614500f40070f95840405865080901000b070001d1a140040340d00c50b00070600325900400020086403a00c600350310314a00315a2500410b001003500821500400742c41449455604140e4140500941d815100074148603c0010002814513640f0a10030080c009145c0407030142c86200d600b120f07980e040c030611340800d83c070b41045041340f11009080054440e09050003886001c1c951010307501c4041012000b0040a5000629200c0d081682400030501503540c2d03000311030080e5003156005076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902805341 1250 902804091 902804117
    0xf06020d0f110a021012050a0e0f1c0f030b060a0903120e03071205011104030506010504051e040605090309150c0f030c100228120506010f1b1b06 64
    0x1c10703054500c0c0c070039081c8040c0c100480ca0b40a07020a00944007030f0704aaa60515440800094031050800313000646203c0c034040410524400035440401c06942003030440e00c64041d002341055950152000880c1450084000d5240590040d080d8100c2e00c00755003004640e0f404c5060120741d842e003141000900291139050100184540b1020740000c101d0b640c40d042e000d001d540070200c3d55410031481075990f151012140b01c01400030031341c80308810100315000b03d40d0b596540d003040390355a1020701419120f2850840440c51089034119069070b9900014200c200d15595900c507440207040050540009001c200081c4d02d143d40d41064200c0c0c40710761001901e444403846c41c0071900d0301c0ea00c0f40c0807100d00d40c0104445108404000341506010b1000c400140c0e03038128030400700e48802d0608042c440400000c50050002c1e981010601e4508606440d00700705590321400111981103207034040c80c01050348042c1201d900e519010a194410303000d01007060060403440c7c0703044806003142d0701010010f4440e140e800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902806591 1250 902805341 902805347
    0x50403170a0c05090d0501060b0a2106050d02210102030c1305030705060715021905180d0c170a020315100801062312010f05181f0c05040f06020d 64
    0x5a04035801d88401c202001042e40082e145118980c0041d00c100c1c01401038004100c0d0940080380940f50b0105c185845011110010380480790450114080751000a040c68564a16100d541c0803144024850109803c56809000321810b03200c41d0710043c09110b0103901507510f424001503001e1b041c1900b0b0300750b031600da00030590300300031040e0400c038800c3e000348a0070000780d07070380038195404150840c819212035200403081c000280310390716000020441100712189084e4104018180605294601246940d280b40803c902c3e031034644030003000d0b810307034000a000c241404c0c0f52126909d5449000c645034000d01c0d4000a140504100019680b07000440c01c000303140b6a89103846000b0030445000340700460500a05444202c10400300c1d45900e00b60165401c0146d0fa241711003603118007240020021491007214240140004481c940003403c6003050458414800107080389140e4034070002004001c04140e155000303068210207900400006010100b8142c241c03c1d20700c1c00400d00c580090a60400d910009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902807841 1250 902806591 902806637
    0x102010b03120d270809120d2109440a090501112802090901050f0619120804031202030405010e0a0509070e0604260714030307060504050a06050403 65
    0x10a507518510101c050102d514140140104c0e6002000949407960b10000c0341c8080303c00090384006101d003005140000760814484200702810103c064508200002c400d401e450341d40a000704200440756641001c444800320300d1203468003c03580407419040046c040503030001c0300001d075a89003000140d40e220301504502042c0061000782004d07141e9106811203551100c16210212403c1d222212000c01869401425504816801860b0f82d0f024100251214001c15040301c4009a101601010513440e1410b00c003000d9042c040010000c0105080070613440104c2c400543c01c0b0380d141420b010100010b00008448001c00050b9401117840318500000104140c02401c07000c0d0094001440c144015204d19414562040f041d04113480c107108540040f84051181d68090041107075400b00c0401d0440d003074810011261003460031517021546a60070340d09a20b071003200c0540d01d98001c12003040000c910350002a40070b4003407001d0750760b2500d00f0f17100d02d003c0c0e900481d8101d0006a4084055001c24854810303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902809091 1250 902807841 902807861
    0x30c1b1e0e010b03041b0315050a14010f090b120a050303040303060f032d0204061401110102040e07180b030406060914070210090206040906061106090f07090b0102010b03120d 77
    0x48607050b500d0030030020198800070300b01a08001c994a0300a08501410301110300a5030b00186001d82e082440e1080d0005003000d964050910b41000100c82c490001085090305880381c0d100310200c0300b450101340500401c079485050381c1001c0003a60507440c4200c10322030304061038002e0300610b0f601d1909150040885480d504000700428541c1020720209441d55080c0203460721203060031a500d036000c180000200381800000758071500300000464882e05940032130701009000e880310500003512220301c90a034040d5001c0ca83d280c820760000142d02c5441414541401102c41c0451400340351101d01104007940700321000d8801d5a181c0808001c0146140f01c0d07040300104089070b28080d410803680003900d4a4290690561030358444045e40155900c040c122002814021030070413040f03546000c0a000000f0031180c050040c020a80003826031700006c902400c8021101010b09642ca0501e07030b610b0014424070000c01c0c115076032045090101d4408024050754604a81526900c07050400e00d10402e480803100707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902810341 1250 902809091 902809109
    0xb0301181109040902211c1b020904031403010b0a080c070b070f35070c0302150a060b2a07030201050306060c01111c050f0402030307030c1b1e 63
    0x41c900000449400c2a18440703034045a003c1030303410181c00000d00c00301415505020030b54070094240714018001480e40e84100d2070b51042103500410030015503040204009200403070500078502d00041c90901102c5510602c2410a0b43c00c0f200054400c403202d400981010418a07030000f42c8422154000700c5041d1711403011042c0500e880c40710340e51000c00340005403110301400f24100707503141d80601843d001080481040e007003040003061510001803403a10081e1100300441c80001080c10f503840380051030034032501a001400d619880a800c5017a02800070141600d541d80e17a6004161030003036600614000b86400c1d079001111584070a102c4900360442c200c140213501003041000180d030441c040d03d030b1101c42207400c82d0321030909a11250260403484a068050314000500c8200008100420208010442c908001131740d44e44121144084069034040d515900901c51036000034411542441000c1c80784d49440502042240758454400007600074417541c00d502c071040e00034003030803007290002442860 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902811591 1250 902810341 902810351
    0xc0a05120a090204110a0c060c0516050304030b18060c0a03020d050a0b0111010501210c03140d11060f04110316120605090114071d0607060603060515150a14040b030118 74
    0x481b019180c10750300c500043c0441c2d20b5640703660031903009100fa1500900000c2c100303a00403d00c0e14209849500c5070000700d9520501d0000305565051034410240c122a042001b00f01e192108408181d142d0840a858020181c08000d10141d80d002c0d401010701805031000c01049566000c8009418402542c072000c0941e0b14100c010030044240481d155801042c07040170541061107401e28061040c0d1541002c0c01b0b40720800f03c00000ea14000841900c42d6001d5034030340b0001c03500044129220f03072081d1401800c0d07041840100c0c0c0400e0b9944401800c41c3c000508488004581d041001c42c03a407840d901150066034210b03d0b03e01804958014168802e0b010b000030013801440d150140105000a0f0481003081302c134844808034802d48410440c0e92550040c4a551607420740d1602c54064052804100c40150900001c1642c08500d0781340000740640082c03000c00840c1c80c07860010002e4100c44491000c00c09140c04e881c44480c142c00080001c0d00c80f004140d0307540d40c1000c000d03209a501761680445010300c7c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902812841 1250 902811591 902811607
    0xb07060f2a0807051603090b0c0d140a0207180219030f0f060302031905210304022110050c091f0201150b030a02070c15030f0c0e090c0a05120a09020411 67
    0xb2a0b803c6140b007004c2c1c5400700914101107407411490b4002380b106400c005036084982e040058404c2d0a40e5107969410400481407807181014055600d807a400340e40104000c0c1706c19440c8100c0c1c504c506405040040c28802d000312054014140e00c011300340420750343d0307065038070010b41d900500001e030f400500240700c01403659000c00c1e82c8582803040740380c011818071900f60802c0f2080c805102e11001c4012441c0c8c000200080045841d4002e40d003c030303c1591501051604e200010300d100c000030500e54050700801c0000c460f14005020001c042552440d020040500f90ba6950b414420114850044241d100c0710b051402908441c9042006001900050010411240b040040b2079016036400005a2075101d40d241c030040d08403241d0070401e0000c1d00110545a0720307a259200404450800a0078801c410f48004207a4400c3c83c0803580c0b680240b201400917607400020760080103422410300c0e0951601c042069903206134041038070648202a220030400c0e0640c0ba0501a003204407a103000c00514003660 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902814091 1250 902812841 902812847
    0x1080c12100e0312010801230906062107030606031104062607050d110301110406022802030105010b210c160311120a02071502070b07060f2a0807 64
    0x11042007003a4860700c854480c2000c2c0000d00546096901c1e5074400c8082e541c44140c0700e4082c0101701d4101c80501d80513941c03003180c941100c0300c482c0500081d1b0041c060395142d409c01c0c8820540003060001208078a842c0c181d0110400308542d0780158000d140004410b030552a0214140b5030030405e140c8210304080c020300030444902c0c540aa607540c20064044442e40103920642460800d504c050b502c502003558044c1800941040c2d80c06807071049008116200f0301c4502002a40140d001e0100103a210300e040321030446000c98074802150000002c0c40c01a052580003900b50f031401d030030450082001040c44030031810004024000140104080070503450401500c0303095000d02c1d045002c4800e40e10301e910703003030500a14986150580100540707140d1003401e183d000e4280d2000c00355100502c076246000565000c000242250740d61180c4c00380c80f800c3c2c0b0f46040022140c100c034006546195a0340c1c510340030109180304490b2000da42c01020210031650302d0003100118950a22901440500f070100020198 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902815341 1250 902814091 902814103
    0x1090803010e1e04030509030f071401050702010504090e01020417030c0c010c06150b13050910060c031209030c0b011d06042708030108011116061e021201080c12 71
    0x2160b1012030149070f841c102c1404040a000044030014110a0300744800c0c1076200c00184a070003003d03412520300b09483e0941e1960346009200e0208503080001441889600c5900100415401450180d080c40d0300d490091b021612820040d04090b94005006c000a200c03027044420801000000b5508000480a41c0c81e200c801380b910306810408034004043c104485903201d000440d101c1d019920110340c450f800c8210641c0a041c00900d0b248002d00005807602c1c05528281c4290305400f4500c2446150140569409800201c22020f2021240e165102c0305003c0c4104415203003c0c0c0c1d580e050103d40c41c240003049940c1a0813121907503000445140d50a20003070b801540000b000ea0700043e0340340711a030007101c41040603503420428840101017102030140c07000245040c5c07160400200071303103045000c465201d071060894041111000f4a903400116007142e014015588401c4c00c522055007581d2044000ca0748100001d6007071a203480d005010a4be0b00f04a0300e2100001070f1002c41507000e44ca1f001300e80e544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902816591 1250 902815341 902815349
    0x8010e010b07080403052d0d140912060f1b04060c03140c03160b0c09031e15070c050114100e0604060e010b1e090619020a02030f0f0606030109080301 66
    0x800903000c400c00c050f0030201d1380255009020744810352820056018000448401c2d41c150043c0042d403c9600c100c0032030b0408102030280c8403440b140301010074400b43ca40012940c507a01c90403040800400510a02c24036208040c2003c559890b45440c0e14140d0b002c106091181e60240e0003404240040b90300031280403025901030070020754038000c3d5011205644141c1a00c03407030030300000c0741141500b40030800c000960b40c850b0b413001c8030f036554128000c070140c01000c1c4c0255059010710720115060441a14141000c0102c0c4195603081c04103811850b9861025548500002d50500101c0e060220038820107201c0c10714080c90a45508001440300680b8003203010308030141e079481000c503045070340710f50200d0010240301d85c4014140d0383d1010140202e42010420b090591000315580000711880070450300b00310001424241010406100c020807100424007000640c80b84041b4480503030390810000a040741404000c2507288030340c0710342508149028100c24080da0502e564403000480c0c403400d980c151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902817841 1250 902816591 902816609
    0x70f020105040f02010e0d081b01060504151e081c111b0114040e01060c12050a230c0a0507080d020c0a060e0109030807050309040b0f030c0609120106230108010e01 72
    0x403200c1b40002d8102c0300c81540240035800c001443c580007a0300c1d001c072004502181c40200170301da03511790911003030311501c1501c071300c80e04200c101c148006404062006003240c026400302c0c80d1903032180140c80c6031000c01a4918403614643d51a0070003243e1251ba040c080492040261151889504003100c0400080b01882d05007e0f5100ca020600d04903101a2802130541b50380040003540c0da440d010f00704400c3d40f04240c441c081e288600d0885070b40280100c4808444c503566002c1d80c400e003d403502451101181d942c01100300f040004901528081112883e840e0041015021840c6000b007070b5031800017482258425500320440c0c0c500640c0d180851503003211054141092400c102000407502e100d00c6400c001c00c0b08102103541002c1c858004060008058181e808005001c00c020030050a030308200c607142d606034000160f0900358240a00a8881b404025042203c2d8405150955094038210b401c403254041c081d110f1410441500402c22446c0a0207007451400380d4140001851300b000140980d032f803c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902819091 1250 902817841 902817857
    0x10c0b0601050903061015020316020f04110315030118241d030310060c02030a14031309021201050d080403140a060f0f0e12120c0918070f020105040f0201 68
    0x99005000311103d00f0710050a880301890400f04214a0208500404102c440d25921085115000000f00c6d03d1403050784400080e510210b9003000b8201c48060071044d00a47c444400070b50480014000d10b0003010040c60040614002405042c2112080300c0d041030302150401131180030684140d814020442ca41041010824401541e4030141034130a80f10f0940e520b0f220040803080c0c00220141d4000d10031100108030351952802c0403154000b50610203580358006110600c00240b078191082503e20102e4103407030400c100c1480d00b61b0780700d103c0c0e408441499000140c2d031080e00a040d22590141008664036a03003444151100240381c02540070041c140031070700780411001d4508000d04811075138070074801d1001440d01904000904104400100c1c03103420010018041c1c1c0c400701d400c414450b89100f0b0f190401a0190040d020324101030058190110100900e5500d500c901e03030f014812251181500645042c20200102008000151541107901d4002484000b440004450441310f40901e0b26100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 902820341 1250 902819091 902819101
    0x315030d0c02041503020d0f051606082716060e040207031b0302010b04051014030d081f0314210f0a030908120a0501080f0703050616180803090915010c0b 68
    0xc440e504c3e42002c0c0d40510329001c620104405071401d030030054441c030180d42817801d034928807400c80c2c42d030b500030000072402a0f400112803119442444a042c02140340c0495039101112900d03003000419080139451032403408042c0b00b01904003159000c512000d680441c80c1a00b60348005215040342140e9000800304065580d044c54070035008101c15240041c0b0800882c10000034214900a45102e82360039107400881c01034141c5004601000d1035501510f8101407551400f070b9400040d20000c03190109850a20301c04408944d4400141500e643c1e000001c0500800e1250045c0e6000700001c04c064a102c0c00700803800c043c0d0050420754681c80d505040c080b0707640c1640c1c54694100c0c02074041c4203065403150400c1100d0720388203400c01d80c1201c03900c1060710611603c2c2c0c0d60643d240e005a02001c1c080d83d101c2400300e0240842c0d5014061049000d19010741d65940d060480b4105101551092104c5d80c00031408070114504000955000700700d00409060403101d02c0c00103400b20140d000c0251041c1103080000d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 902821591 1250 902820341 902820371
    0xf022409121c1112070e100e031b030a08030405030301030314040f06050a090e10050a0602010b010c0f05071503060f090603050604021003060b0c100516080c0706200315030d0c0204 79
    0x1401d41100130b4699542854440300040011840218841c426418030303113001c8100d1300420002d081c000c80034010b4414a40380400000c5900c2c0170410003074140c82460010ba003c80d103000301860049100794099652540355042c010818408025002c04041c420442006413890300c404c0d12048503001d0074450b0b100d2060380026640700015602c00907150a2600c104040302004031180000c0d103100b118076010041d241c070812400c903242c07080c08601007a217441d844e40200320080f00c81c01000d88a0012501440c0e115417649115241500b00380d4086a01c03000240018035203020f50b040030b40360031042001a185162074a40da103450240c03010740103c0341660b07801805842034010b4006403101000156079100c5c0c61094036540d442a030610042d4a1800c7c0c0070504901c2e039007030784180c00d04481d595046c4a403181d8010320b0a0b0f52080e80100c4020381d86e0580920180440b400111481c030181007056100c1c0b9140c0c00e162403030054080d1891094005d054450f81191304080514003a036010f850005094002813704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 902822841 1250 902821591 902821597
    0x9050a1707050405090a0605010f05010914040209101205010b131701111b0105060a080a0b180d0801030308070903260d02040f1e0e070f022409121c11 66
    0x541e0410300306405c100030140e0004110b1915845001c08100e1030380d8640e804095000d443c000d013400500e0030402002104007035540c214119500410042c904600394000600104000d0f4424020440f00c0764520500301d014441c1500400046901525001900f8002ca05100e06402070b892011021101c0050b8024258803445607041c0b024681543c503050b9840d13a032105221000460f04560a180006180d420684000d00c1226007400c002c280403142d90791508241e040080040e00408401341c0d01c1e04100f001003140380314194107a120341d1410350540c1401480c01c1001020203090207005001080013800b501c030b0300e40c0d003025030028a102c410700c401c5a10100e881507201b0044140c0c000314000c582051658070410465071224030450200c04456003600308014948a010084800030300001e250b80d001c3e8406113288005841a00d030b025480b000d0001c051744510168003101c680c00350400034080810170000701c80d404120035083c00c002d402841140d48041001c2d08000c1c0d1381c1c4940043c0da5000ea2003043d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 902824091 1250 902822841 902822849
    0x6070516050f010f06210611160c0603060b0a170c0f030c040e011d04030e0a050301020d06050108060102010b031b04091a100501031b0c020307080d0e1009050a1707 72
    0xa0351420700b1000d180030f020701308952111a4680c600880060700c01482880003c146400e0030821100710820b450342d00c0140601354985516035010004484002ca602c00040700d601c2c8a6030f0fa5500003410b1000040480c0c46e1034010501c404420400f81000e15000f0206820f88907c03c440c41140b0b41d030b201d52181e000c1c000d51820000c98040401440305c00c07031050010b8420749500c5141d07400740f80e9803480c0070040c2042044415205403001e50100e4003207485210703e0343c4800406050007040690303a0004c6422a8855101e003003240d95200010301c80ca6078006082034001c03c3c00d100038005114104006529503001c00401404403aa0021485a94440c6d401820901d6003290041008003402c03465440620412519810f00380341d0b5420124035580684540507014210142d4800c41695100054480d000c1c0c446c0f09980c540701c0c3e010002007000c4204130011526017039030359044015240500b44540d44554480e4182800300204080c812601c614510408880400001c030003070a0100000b2802d041c01a08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 902825341 1250 902824091 902824093
    0x14090d152021010e16091508091605060912150708151519140c0a0c1202060f0d020403020301110903060a0608071710020d0b0a120201020607051605 65
    0x44420050220030000c0c15002c540348002e034100c0c40c803440891481500c24003480c0700c1300441c6008076151032144c218041c0144820308041081a40302c625483d440e488012020001400880401101c40001c3c0a020036010b0a245440d5505082c1000101103004001000e8003541c400303140c082c03002d082003000620110346810b0003405801d000600178400b8030300300d8a49048040601945c01241040d00e01d1515264100c240242030440702401800c1c15420002c3c0b40003040a0703400b02082c4141054003c0051000d40c000030885040340e40b8149028030784943c00b0648110003420400056150030048030200074104070941c0d500d408088000c00240034a41010b50550305e0712030700d0b076842c0703909030b0007456102011004c903000380d41d400c910507055079158040d2070340c03641285d0020050f8004190441900741001c07401d40d003d000c48411400c003213800048245500035203a02c588034003030400b4071036000541140262200b6501e9030780c0010b0b68131400600720400f007000c0040d0710b5801282440325100c4c560f9101c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 902826591 1250 902825341 902825381
    0x2d0a051c0204180c051008040206121e01080708100e0604030305070c140114090105090c09060102031e0403060b01050f0403020f0f10080402030c0d0c03062d0c14090d15 74
    0x13052850050140b03001e002d000f01c10049250324503500481c00a841950b004200614061201104130079844025211100320680c0005009640006607001c0d0302a00140380101203032880c00301c4580c0741c848030480d68035810b40f4015000c040ba00000c203650364000c0e09400d01050613200e0314400c6441340e070925400f51036502d06210038465035606401c035810141c005408000151144d4581038220f843c1505c40001a50000d458900c4900702926460380c0208140162810076444080000c207119000381c0c0840941c7c0001403c0c0304122040c410070b9020503080c81c1460030812102101c3e8140d01c141c1c000a4070030802c011200a40d55078000000070240c0c0060f00000c070038040705d04054607500b000da400324404d000c0c41c0d180305620b003400c0728080111500038400000d12460341d152003001f04161400e00940080c14211280303601c50820303001a441c058403a001603138080b03002004051318503402c044403011f0000c1243d14000d13924505a51003060b00004025410700407100100001c22060203039030140e402c64 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 902827841 1250 902826591 902826593
    0x408030a02071805061008071b061e0504030215100b0c1f020f090103180b04050a15020301060507021909060902180409032c2d0a051c020418 62
    0x4112907048a03554803c0c1c15901880104440c00c2c0da40468940c3e0700151411261003060340304000140d0400081c2c01c01c040c60380340c8080c0e001004e14041101781c90450f102c86903030400241c0704984100c2070181800c100100c2c1441d40e002900c502c0c50141040652000e180458040300b802c0c110113006201c040c0c00d20360f803103001051a40e100c50041e400c1d5040c81003400551a07105d11203000311046642090605490048040015801014013410301c4003800c0c02c1030705520001d000841e03024000c070b005000602600805103440e543c0d589991880c00910307801030004101c0c0c0da0300728056940d00c9504641048080141c0700c0c41c2e8074162400e5001001e010300f444000120703c1f50f80e40c018401f5401c4006050548903043c0140001d9507509580100014000c6643c805216402e13505005550b90f20ba9000d0040c0c40104001016221510106c55090384188075902c1000c94000441c1c481d24000d0700c50091f040d1801c40004c40801d071943e14000c015240214401c215600c80d4880030214129481d02440d40f400c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 902829091 1250 902827841 902827843
    0x1050108091f0c031a01051c0b1305040b070315060c050307060528110f0913020a050310080c03070b0a14030c0a020c090103170f07060507021015050310020a02030408030a02 76
    0x1c546450400310b498091034510f401e02c103980705ca00d4204182c4481e40350000c0da034034001c03030300100d030303082c002c038569180c103120f0583e90f131190094058070801b440405d0760308040c14850300796003000c2e2244051501d4035a032080840d0100000780c08449141c10030903102609400c240c0e085229015000b40040d14000030019541560409d4901d1902000d40080c01041454100c80880e0141d110f0250100300902900e020142940d0080201a0b030142c40c8406a040c1c4070310701c4081c3c2e00300a0015002c150080208060100780354101801821010010404013410002081d1149100e001b03c0c101c0a0b400110781c140d41d40207044844000c07448264443d07072880d00c814422500c1d04031001540040c02400c10341c540c0c41c60000d0b40d00c0e06070b0707801c0090716815109402030511310385d01c4502003008040c410b0200c007011440701c2c41468801c3c11281c01800c0c05001510342c4000700c4500003400c0000500603071092045807800521141d019250800050b51548070300c000744d25600a81e404524a444000382032105103034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 902830341 1250 902829091 902829101
    0x7020105040506060607051510170303010302040b1c111c0305040f0e0708130501090b01031a0604020c0c040e0114161812020d030e09160206150901050108091f 70
    0x2002d807003515500e48400040107440c0c450600003410b5644108541600032001108054000329607410646000c1e5942003008101640c42c504500250000300c010030940c20203020b500c40781c0500b00d4400c200070030030303a4140e0702c440020759001e0305240d2500c00c904200e4646003944121040c2440740c00c00200d01920f03000b000340d40140a20185c03003500304400200c1e01001440c5501802554503144140e80d103034100300800d403d480100351402d648524005010600f80404107018501844182450400c400769240e01e18502600c1180501e10407c4604151240481e8810107104202c43c081218400b20307007424003401544c40044100c1032100103000224010200d2a012401c1c181c480d91905100603900480071a0345101c0e200401305440e2400005250402c4403420007440f90410344070801c1c0711404228020b008840c0a98000d51300d0a00e0442a5010000c032980041d19030b051040340001c41c0082071281c034044c4100e070705001c1c3c030b50040742000409004c0c8908811101140d1400000e80d03440d00700c00b43c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 902831591 1250 902830341 902830343
    0xb0108010e01140402280306050f01090e0c0105090f03012a020d030603021f110703202403041e030914010c02030d11030d02040807030b0f0f070c0f05060702010504 72
    0x142c604004031203080c0043c02020701c04c0d50000e01500c0c0c90344140a94000440040d119201000c40400010001842e64485d05010741155220070082e0744c1400ca065044a100382d105078102d5001950004540c0c1c0d00c001216001c00713080e40c00d6403501d0089001700c2e0140c004501003c4e4040981c007420215242d41d4154081c03480310036800c0b0b9081101a80055044440314000650041100b00c038890581f5500c1c1c0300c4030510481e0303140410522003400700c450304080f05500102d90000040b104101070700d1540084000c04481203411010001c80e07800d9084004541a885440c91100800014144050403814079a006020b6151720590704040c41c00070610b2000340a4400344c0881a11141b1003544104031031320744154050000d00c44e0620001e81614000703411018506075210400c0325602c22115800a80002c00100004118150441c644010388100013090003140d60805420044e406c0446641a60819400e040c921a1046241001040b8210f60880a880d42c4502c4092000403641540f01e54419 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 902832841 1250 902831591 902831593
    0x5181306170a0b0c03190c2706082202040902011806050c0d0f020c09040212120408010b06031003030305090a1e0308061c02040b130905070e150d0803130b0108010e 72
    0x1660700d100ca107084da4041540c1042640024046608003007000341c4c0b007844002082d0030720452100c5403200101c86045076050f43c00060080088c1004516000034101c0e802904808442d401444e01c1000c041140700003080182c0714645403d044015a4050f07620103105180e80740d54816655145d00340074049901c0001c84c041d091151404600300780e80300381c80442090f90203078060003580d05240108061602e002e0301c26a40300980382d04011100e103041100c040c002910032109526075282c040e101d82101d49401005000d92420010808074070306800f0008240c030b83c1800c0011303d68403420300861800025540040c180d07031a00602280d01d4000d6104800340900c42e6940030080c1c0d80340002e10030160405810400c000b55442000c00040c40d003500083c2e1210b2025050303202888000f180f10055030840b180c26a00c0f600165030600861200301c603c82d6021740429803a0000351400d1340401c0d00a9520003001d00300400200102b20039812030382455404a0300460000340558540300042e0090007681010314603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 902834091 1250 902832841 902832863
    0x33d0e010311040c050d0e010609020a030c021c021c170a0204080d090b091e090a090b090d0f030509010207020d05010509071a070b22111005181306170a 67
    0x2d030b1510b4000c800f482d050954410342001c001c183da9030081c0070192450b40d455500e4503000300713508030548040c00e52001c01e9640442c038180d01e03440217414581040301b01501308842d0b40c070000c02d51341c0025094801c0d615065075402a0740c005a011554a859040e20800c2400d00c0c03010b122200d9810b40192041e24040d20694144003802001074a13030b901ca5202e00c1c01402800c0c0444091031801c0c2440395961015100c1140026a078040060000301045a41445955840b03036500180311035140e40590001542004011b1182c1c980405403103420b407600071404058695002810070721081d01a00d11295001d07094050301300146c50001d010b4041120706006074030401c800001c1c82c210390000c40344540c041c0c039000c501d445610745648110300d4002f400451068001030342c864400490302803000245000301d100e094848003400410840554941c00031040007024040d003203a44080e0300845000721412035040c01e00d80309861880c4040c2070700d0351003228620245114150382000c0842c0c0c00c4040c030320801001074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 902835341 1250 902834091 902834123
    0x80607120c090b09060c2401060807080a090f0506040b1f06051213020a03050c1003091e020f030a030203040513020a090b030a0612050a05060c033d0e0103 68
    0xc03585201007650006640d84000c01c2540b03054401400c403044080c0006142610b08410a442c200301c4501c41616601002c4d400761201d0401c0c040c09014010624140d655810720600091120501400d03130b9801580e201440010071051107403107100e1a5226040c6c41c40d0789820f082190400c60111480b0451803002c0e102c01080d8600b008006096038900c0c0c80d66414285100f080391450f000c0140f40d0503a104010011401581e1000c0700c0300001e40c481c40c0140301c101c2200c41070101c140406150442818108040600002c003414010509015001d08910030003800d40002028040498101034144c0210b0002d4014180d0120080003621405d031342034041c00b02d00350410340880c414403407010f0002c3c50403002031000c0c0c0c400c07400842c0c01c51402c4501044442e20f406031031400f15000041140c541e80180a0a01000070602ca00c41c1d006012000560540c5030070355980c03010000c0005010452001d501c8940c207a0800821206242d500c00352410f49182d40b640704119010300280402d6a0240703280003150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 902836591 1250 902835341 902835377
    0x302220e1f0501200709020403080c12070308060409030e090703020a110a0209010e0c0706020a05071e05100207021f0306030314030c0d0f0b120606011b020604060f090807080607 78
    0xc022568181c4d240c0c952180300800d00b00808000b000e04130f080d800303204c0c400104640c41d0b00103000954018151540c1e0703042d030f002d80c85140511964002040d20414404000400c1c0c104000d20360060f010340d400328182c0040d01d0100c580c59450340c141c6074802441e90502001d281d055000e011214044c0d21000e000c44100368000d41e40b201d00c1c51000758850800c4006000c1c0c4002c4400e1140c205071100b2000703003400d1480c0c2d50b1000b40d821900901c000982d01094580a2000481034030800d1a00c9125034071008040b03880d955180c102c5182000ca6807500040d10f00c085450b07002c1981400b800d0b80e03d001e4211620100000c028000030b21094001510b242068480364030f00d2804c690141c808800800d00e00b906101c5202c0180c0340d01d088050342c031556403c0c04142d1f0303110b40c48014205084140a42084d2a009001402d46461741400c1848481d83e8044140143c803190115000e44c0e0450501c15207000ca00380048a01c80361981050280740200c28000400520003d00340d400791380036440d40100842421088 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 902837841 1250 902836591 902836651
    0x16020106030b040323030f04151b051c020417011d07090c1101050a0606110a0506010e100308041811090108161e02100f090f030302220e 60
    0x501490b60101c081000240140f07441c00003100149046058a0004030402560743c0007101c0030343e0320754005020402046030400040e00503e410403c100300c19050314066038400310702000300c3c40500c24005140c2030003c149090140003086041001d55903940c84094a001c8102ca4030100c0301c80c1d40c200110800009080282c4034001c1050300c0c01000d40328540101e01b0003900d0023002c031005000400e082c20031540c40a0140c0e910804403940c2c0881d40510b449001041d81000441c180c2140e00807614420016001003980f904403003020352003400e1521403420211040d03040d42e1000b0503002001600240003e10360300d0740c2454040c441e800b00301090160341041140d12480d0281d42c000b0b0704c1400080c4086035010b4032920f62040c01d150108115541f0207082d8211003d1401d01005644141d081101c00c0c0c2c424051040719650940d07050005507402c3d96548101d19a04000505242d00410740034240410081c018448260880700d40c11401d030b54001c2400c0c0c911050754000040c03a07141070b83ca00022045886 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 902839091 1250 902837841 902837843
    0x818100908071e08031513020a020309030607020f0a06050a0f02160c0e0f01062303090114010803040b0909090c100c0212010509120a170718090b06030c1602090f1602010603 76
    0x100e5403456941c00c07155515910300e021811f40c480039068080d01c5aa030244064810503107560001c503590402581014500140101454110f43c410a8850306007080404c080302038a0b0300800c01708003a1110313002070307019105958103107086600c04104410f0320342c045130301c01c100b203802000002c040623103883c2d00042c401c0040b00c8112920040d071004218040c403869042e0b1a0706000a4506000400c821071800590300075547c0d2045691102466160407007410070a40c01050041c00840c5803614010a510141c003504d0034452182100764006000648103200d0403d25400007050305003c1c15020b2070141c0451400340d401d0f400b071180322200405103501407044038000d091b034000504136100c080c0504801390380103600007010481082041c1070700002d54180e0502884081d1100385066490048600303409000f94005480d9a06005410030f25840b9041220303045051020101c2d500e02100111100000c0310020080d0050710407401c0050300c117505070600c0e0203600c1c80d91344c00c3c044541400c0e00700d0a807402d03408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 902840341 1250 902839091 902839103
    0x50403020d0c0204020904141608090a0b190504030504090501080f120f0c010f0c141303020f0d050d0309050d020102040303080c070c051f1b030818100908071e 70
    0x1c003459490041c00000829480104058602281c40c40800c0c00e4440c0d80620854504801c400e110441245094000d8101c80a20384006c05241c405003542d9158070f45d510144c07600f800000426201d031180309140800c030744a120300380a28100351070020600d074400e20609121510340400803645010105500321110440e500030641d484a41c2c401030b540b54084100854441400c2180100c4200280510052000d007c03400240711600180083c0810010b107c03110f40694042010b1248111031a01c41025a901130700d250900382021008189808090100900391b803152940007004a1340c10b800c82c400c5580310b10280c0b0342d140d0040000b41d081c0e000c1e0703002c02008510050001b8005105c008094641180101200e841e211398400104a0401c0ea0000344d8034440d4148201c0a880c540040742102441c80c610810491520103840003401041c018040d50300c4040740815101100f1030810245c80d41c00e0142d00d0412104600d840c0820341907000650440d03c2044c082c900c01240526508030b00e0305107401c10307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 902841591 1250 902840341 902840353
    0xd09031a090709091103010b010e0d08070501022104111e0d060902040501060504140a0f15020f06150108010b0c07061b1b180501260a1b0f060305040302 67
    0x44041050200010070780e40a51080311030001c1c0b0445203018040c5854002e01801180201440605003554820100c85040c49165854268540c44400384141c2c0d01d60400c0040381c54520b58500036019104581140012184115111580d031b88150242800745100700f456094808504060001100e40480c0400340404101c2601c156410b0110240108500c1a400004c03070100b1580003e0448100380c0148000030f90200e818000c801031140d01800c00c4004541d0a82c10030700c1c1c840681b840fa00d80d406050480302c1c0256191504030f000700240c103154034480c01550300310300d03006001701c81020075920f0b1680040d0303501d8000169010f420003101c18036141013018003041c4e81800070946045144800542103c880f9517004400704105240010341542d440e0306007103c19103000c0301401011070f068160b107000da142000411074007042078044606c54200e80c00203200c900a00303420a09042100601801c10444006400c03091440300700c040b810344400c18844800d4540300c00044044420860700100968024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 902842841 1250 902841591 902841623
    0xf01060c08070b04060e10020412030e01031b0518181f030c0b03060414101403210d05010f0e060d301229040207021806030d0903 57
    0xc01012a4007801008428940030090b40ca08541c0c000464017a29800d0361072954070917441040c8810164036402980560429051481d0901d010540c0300008041c46400b0b103180201d64003030303004011444000160210076003103c64018009900000005400c4002410100e0701307441c140d080924255003a42d428003030742c3d40320f040c0c04600381c000000c50385680d0181c1000100242102d8101c6010f40b912446498582c02c051061005690982030315091a440c8542044140071100d00b401d0203d601801c15522030160000100e07041c54688104000c1e0343c1c0c142610494901011001049182c0d80b5200401c25a81e803000c902034202060300a0b1583c0300511004541e9500d0f011030031980c1980103c2801952045484015801503001d003002171900f42241044050a44c10080e00c0e203003600780c03107020f114010100580038020780f40307800d00f40b0b450300c00d80010f03900d2a01ca55050350030b8641c1c054101c141203441d4410184d1060030480714144603200c1c80000c002100c3c800d0343c181c4212640400414140d140d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 902844091 1250 902842841 902842847
    0xe0303040609020d021905090c12060d020406120303140105040903051c060e0f0612071203050705010b03120c07090623012a030e100c02190f03140d080f0106 69
    0xe00d0b605903801101180c00d980581c1c2c0c0c2c1c00c5400c40071031050b040500024900b000348403240600901c00e00310700c42c0c1808403003044080c031580d4a07440b581c01c41e0303650b031400080e03c0010020030a0743c000e020540140c0140d1403c06416900000307100c2103c4180e400e0340ea0340e400c104415103030005c0e001000200280202c003420141203116804010b0f55040c081202c80c1c4440200c640020102e07020905c041a24080c000141070110310010214040400b5000290403d0071341ca103000a10300c0e0060030000009620070038050701394482c480e0b03100001d0a40c0e089070082c14450b4800c0c0c00c2504c1000c0e00f4040e00a000660060302e00c5807804640a00c6111002900004003904a06000070410b5062064026103500d0300c5100025072442c900720401a04460a110b0400404c41e0041c01031160140807a0021340006a0300002c0d410700031a41150305008002ca1094924105050765105103140c207640301c008030810151007101c5009042e444201e8604144429007100c00344019101c1d00343c80c803803040050000500c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 902845341 1250 902844091 902844101
    0xe150406021603121b021c09090c0f090602010c020a0f060b030f061501080402030a021207080d0c06050901141b0705030f0409060e0f0f1312030b040506040e03030406 73
    0x3006800040c1840700030000c1068101c0300010072030001e80075000104841c40d040c0b080317450490501d220051006004071000c1e41c0c41055010180d1f4400c5108001d08825118174441070142000c008288141ca614100145c00c0e01c11100414004c100c66460110300c81d8070521409004002550061980c2003c50300c8524217021030110545882c0d4488403404910344040043c000406104802041c0038178015a000080d00b00c0219824104150002130002603079002600600040c0c0440d80f0340704a11410390104e28000d550707030040301e10f80981480015481c1e00500307031101c0c841c0074050a01082c1d4540c030350700b401c0300c4142c0507641c001c0b046000844d0b003100f00f400381d6010f400c1c00034082625200d01519154038517007141c00d803031802800000d0103008030f030b2590140c41c00521071000e01c05550309115410305c0d41c2c00001444900800103010000d02d00c0d003403815010604a8101c000c01040d209100d00c0240609014544030740680d05101c00301c0c002d820b0622030344488010380400385046071030795951207000d08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 902846591 1250 902845341 902845343
    0xa11010c120305150913060f060e0f0c1603050d1104082121100503061308180d051605120304061d0901081509030f0a180f08100e010e1504 61
    0x144d0900c1807440261204560035028402c1e21075203105401841c030305003064498008212240c3e41c10b100303042002c1306000380c0c019001441c1e0302410481d0703900d03070307850724154002c0d03ca1443d10704030260800010715400230020240c1c02d003032900c02d020081c842224005103215500c1002860360051803010307011031225000000d40e43d20589020b240c003003d40006000784cc490300104020802003401e005600f825500303218000c020a1b800703070641c1e15081030145105954100060000000000c0c0d00c208003141d000c15880000e401010140f6244c0c85040481c0d0300c49104d45001035044101030003003035902d000c4041c621100704200046280a00709036041350105040c1c440c0c800d07c00403011a00706147c3d9504203082c0030304040c600900ca01e050501ca40003001002070141c1810b500108001e00c070000c500422641d0045031420f05001c04506910004032101603540700030340a224034100416014404030348078400090181090004803649591a070072215000022900d90344481e43e00c00010004031401d590203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 902847841 1250 902846591 902846611
    0x1b0c0301140103022413091b140708070503040e09100e060c07050705130b0a1208040e09031905030603070e270a120504031713180b060c0a11010c120305 67
    0x120b80c402e100d108003a001400905010180d1080030321101c10107224038603070881d4080c8c115064a0298101510303142500c5442880e204000824400b8005040f007104c0019505c181100c1d40d0f26920301600340301010581c0c00005901030f942041541c03540714000c8604803001c41014190680b2040042266544910740454040c042c1c680000342503640c9405403228020000c00103ea01c01303160040000600007600003d90b9980001401004505490251000d444400601c07aa05880e03281b2030510354040c003040111003043c0880018801035201001e180141002d80440e007a494407501308440c10700c2d00300c0d48c0c00f010134028484a03280381c40408848414044501c1526590310041d254015096401c40301c49000c03440005041041081241010303840503221400c076824500300f0541c1d900760200c10310502c0b01003d0012506805205035600074044840010720940e035481c0b0856000c0c0d141c0241e14811740e609401d52010003d254001c401002280d644000780180b5915000c00c141d004010240030b02c1d1341 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 902849091 1250 902847841 902847889
    0x1031503050d08100806550c08090a02100c021e04200d0504031404150207150c0b040503220e0105010503070801031410021c0507030c2f031b0c030114010302 69
    0x10600c41d87c04503e64040c100b10415050002d01100c6c54250384407283d1900800000900b0800c04e00408241e40c068190304650300d084030f2400070070072202403001078000307944a409041c12090701c0c01c0c190502d207400c4401795800c0c40340ba04000c030109582900f030503a181c410801041581c03d42010399008541c0140b103404c040c046030070329804540740c0740c00c180c0280701c4c10503002d0645174030b03150100180d0006202c2034808010590075141c0042000c1d225500040510383c01001003010400301348181c8500d080d000801c0402c080d440154154100458810207001502c0c0d08000302e00d95105400b2644a4003440c0c480d920b1607403a5a0b24200c1000400340041400d0107403521b50b41021407540001d1058000341d004191900c42103a030414215040078055900341468003e60703054030341d04880c00c104119144110105442d1080069540510266099803140c4c000021100041704c103040c45240d2042c40c0c601100e00044000050500b285c00d0707502c071030040c42440c500402c014034010b10300c40c201d10784040003194 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 902850341 1250 902849091 902849191
    0x6050c0a080c0d1205160f09090e0a020f0901050105162a030303051e07140409150e071b0212010b040515030d0801030c0501031503050d08100806 64
    0x11904110401c4030070b42c100c0442084056071141041d004c0f0b0200090400c12800c06031040c3c130700c5100f181d02400510070740e10301c0311440701d004428010050003c02e00602c400781a20b00c01d50340b21502c910049110b45031003d55606181800c0c0240c5050300e5043e12104e00d0038590000000e55110f0f403140498200e10786c101d00604c1540c0b242c06242000150300d60460646044d460080c054400c0100700c02c0100040181c031045000325141d0045d0850190704000d00c0d60020441c048100c0e120f260012030086050008526941901042c032104948010000326440d4907000002c440700d264021451480c0d41c040c040e684013518180329040d4042c080c41380001100003140004c81d043d580200c820b00d0421284851203409420140811010034041b0301d4180c5c25981550388001e444a1640609410180c1c3c55a5105004070101b90b42c030007541d00142210a04100154020300c48403040301c141030a0b002000000514070000107155001d0f80f40d41c01050540f079000d0340700c2c4103800011101c00035688100d91000c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 902851591 1250 902850341 902850353
    0xb240d02210f13200a08030a110708100506041806050f0108030909040609030e030307080a09050a080d081b0703020a051204060903140307060612022806050c0a 70
    0x4000e280103215910a401d80d03400d01c80c5440d503030042c03007165006200d03400c100f8010007010300c8159040c1d001d038281c9070a0718080c1c04851140710089800360411030030003010411542c004007804a40049565032944000d09a02468445001d8461190309070311101074000600030682206910840c0584001003405040d0448aa1080c0c88042a11000e0ba914140921100b19003071642c09400080025842c0c80000f00200750700000c000d201500181d50b40d401d260030540708044421401d4401012651102441d0801c0782c1c5550007a00c030b003800300c1c074000e00010760340c1401d4031145c00300c1d0100d5019048242c0c41d03400070794000b071008203034a03d118000c21000038941c44410107042042d0003a4024805a800307840c0903840c0542003080c020800400b4402003041c1a4050740c0c21040c0c0364840e1404100825445009156004542c4010016818204049811041c10001559280c02103e0104007111000c013414045881180e4401401641c90000c2c04018000d100600a0200c0c40341180d25025141d05c1d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 902852841 1250 902851591 902851597
    0x1c0819111b06010e0618040215030f07180f0b0912010e0f1009050c1315030f051e10021308060405010902150307020613260307090602010b240d02 64
    0x441c12818400400c510719004110b0140507040740714010500713051060001d10b280d14400c8488100140c0400040c0c1192550301107001d0040421242c60b0700c81c14218440000500d00f290000001105040420b0100030120b003083c044a50681d02030701d0581c1000c03101549036201010080d00305200014843c50000248070304d0704c25424850140101120084185051800000c41611001e082c4581c890125602260310410a4811a070401d002801040c1d54405840000d840760810b0420074000000d00c0303403503c442a0264851030a582c4c00040206003041039101c203e1841e00e2540c4034100c4002d524603264001c1501ca1098410080c1080c0e413010344030b151040448089070281d44034101c030b1045082c06400c905d10f94812000c044c0c2075250942c1d0081d560b40c2c0040c440c0751082e200c1030f016002d2100c401a03001c044400103182d0b48021101c4010030180e50310981e1074900060b600140060014410301c1141d5070740c1c400518001001c07041c41065050301c02201800d1a008030204944030b00b0b11001c0c401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 902854091 1250 902852841 902852857
    0x90118060809010e1c051c14010501112406030304031407080610080c010e0a0b070b01150e01090506130e071d090f070809030d06080307051c081911 65
    0x600394a80b500c1c800160075510f90403100541540800d10002600f82c900d4140c500c0e0b04c2c9a03291807603c0d94441540b40f02c0e800c5444003c1f1904d103181040c1ca11080c401e4000c00c0d8103031602a2030700c603020b044064201c0d0b9610465455000c0000032801c004e102030100c004801e8004000404882c00c064136902d84c410f0810200c8060b003e10b40c81880c3c02c0001c00350902c142d550002c011150035418a00d4451281d85031002c01030410704000d00035101058550742c180c0032501800b0049145901c5481c00d00d0006250380c001c1c054130b50404070a6202c40401440740b0181c0350101c40683d42c20002034609028880d00d41c01481c0380e4900f0b91004e1801050156520f8a01d5124410507611500b40b11140710704d2140056039101c1c00350040419004101c007040100c02c1c51500318510340340c51140760380d07800100c80c250701986e50004244c90070210b0000d04481b00001030f0450754000c005607510003213050101c042c102040752001c80400c0b00386000981103040c000e411b40c1d4210415078081010702d25100446103039401901 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 902855341 1250 902854091 902854097
    0xb03012d0605030304050102030315040615020c01181a0304080c0f070f0501020616050310030b16110a0f120c0203120406080a06180c0e0603040602042c060609011806 73
    0x81144400145070080d04010070043d070246113000d0500740000e40320320004140c041581c400c903040a146032101d80c052002030840a41c200003000315800025180c0c02d0160031305001403141c001c2d9452605a101500040381d007041e08040f05c0316108482114280c03c010820340c1d80340000d11044180303c8040c031400301102922005058817504190300c01c0500f0915811a034110f511510821001e20340d07078018101c03003a11a0900645075030f40d0401030303100c07140303135400041a20300388400f80500351101a1343c1114801d50f0340c680300511401d00541d01d584407020310014010503024100080420035415540d0b1401140740303051000900540c020a02e40a040c08030165565000602000b28507803005200ea08560b407100280302c482d01c0c3c40c500d12488045003880c0340e80d40d40d45848107070030079003e4421103c0d64100035084944a01d081c1c100130000703400502c28a124070300d0422104c0754400c180c0144000110980242d103450340c5451003440100d4010000300760501034403400034044600d10f03001c4007004090f199 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 902856591 1250 902855341 902855411
    0x6140d020430081b0a0f05010e010e010e06011509150519020c0102121c0e031308160b07171b0c01021b0603040305040b16020a06140d0b0301 62
    0x202c607890140903200109200905001d004000040000089415005102040800c0b004026003c18200010800014034503018806000c0c200f00064110660641d10f1600802501007140e07516402d850318071007001e24640001e0300501190001454400c04850740d440c200034bc203909c0311184d1030380c800000021004954003190a6450044030b08241d8500342c15840904803030000000041c1d81d42d46084e0442c1c03041000452003030044100d030004a9218460120140445100000c8540d104d07484031481840407118100089103088001520003a0f0a00e139640d500b240358a055040310541d0064042100c1000150720a01b40da14481400381c840c4010075800b00002090340c01340640b62103001208903065421010800c2c8000802030b200402e0124191140d80d40c81c1e60700e140c00c540034480d680080d11201ca0208000104014031b402459501e4400d0b120001c5003900c4002c00c2d1541a6048003003803124070100310a41103d00160001585000013800100300d080c011304070030318101c3c80c410320441189109 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 902857841 1250 902856591 902856629
    0x1021912030219051806121503031c051009052503060906030b0a0f05011503020c030c0106080d140f04090b0d08041202150906030f090a0b0703021206041506140d0204 73
    0x42c960300c400c070219646c6d450301c0001d02c8084011840204900407a48140d0026081e9440900480303521040c4035020024080a18075480c0050400b51250f00000605d0380d4080307088035407445140d000e880c0580c20400440d40d200c0380d0010040c00d04d1600300401d0307203c800c00036140506000f0307007002e50703c40d2513003001d032f4901b607003a11080300c40f03000001012900f847c004000c078a030304120810345081e05213405691010301404445c0395220b01000d09440390300e0603d00050792440440c1e100c4442310503680f080c18085500481c2c0c2528001c00c010761100380d408000401400250341d00840d0810350190280c0d080d0210382d1150b00d039030741051780700f0035030510050050f80843c80d040c0280c031210280c400d00030741410f0706040441e030a400020144203183d14040c000c144483c0c010003c1000305ca5001c1100c4100d80307010000203010b504001c0038840f1500a5001054051501d8000c50061244a5100360001841d010301282c000032228a5030014000401100840424600041004d07141092010b010720440b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 902859091 1250 902857841 902857867
    0x18100207033c0803070e041e09050f06070219020d0b0705130f080a17070b040501090b010e160f030212130203060f04080720090f010906050102191203021905 69
    0x4520718840003182d0605070000107a501c03001e51307422801038a003541d903520b05200418001c00c620402e43d0540030007852002045812034110b0f101491046060b546856040b1140581d11a001e80d0340c0350241e0494441c2100c0d01001040031070302e40d40000c000403401c24003516a04d899110654070800020400198482441e0030f501003000200810b40300707170270810300d00305d07a650b00d44007050401000a104908a15401c01440054449440e0030101d01034950520340740240c02440c080000300d80c809025000024401100f0001910401c00d441841140301c4071070b03008070f60068400004400385036081c0318104440c000c01d42c0c4d252003a00405000141404203004140c9081401054020304412007801c0000042c0303d241550180c5600070242188114003081250000340c5001105800408141c1040201413000f2200c0c0d049400d490420460b03291260012600c0700103040701b62145030f101d000312000080140c0e050b113400c103400745001818170070302011030b14032006040501d6002407004140313400c5441d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 902860341 1250 902859091 902859173
    0x7080603070303140f190c02150f160c1d01090e0706140706060e070509040b030c06091905030303040308010f0605130509090c15041a1810020703 64
    0x22048000301212803840d940100200c0510156550003d004180c0521144009050703d030181d400510003158204c80c210000c00410004074103911070a030500d501c142c3e24203003c085032030380048150700f14541244041c01e5000317201507010888248003001000070b5440754103108540c0440308609040d5803545001d003160f0a9507220b110404103604244410803183ea041069802c1c0803920001c40e5444550f1420600000c10603540f00803803401490303082060300c3d540103000b000100800c40d4100540108502455980c0c103411445a41040702000380c08602d00c0c02007810002200c2c4020045107254480c80031038150781041e00c1c00c8002c00c8044005000440e04010064082c21203460400d080404102015070041c03c075200e082c2c0150b5020021030100b420a006000c102c11000d0207039501400c4020300d100099029101e400ba4140d1090045c68a8494001c22108007041410201c1035003660710003007007441404400c41005500c2100000400034210f510f00d09841d018a440ca589888100840c03802844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 902861591 1250 902860341 902860351
    0x191b081c0e06011d0702150709210309170a020a0603020318121204050f0109031e02070f030209060a09090b0417160605222a0b0904270b0708 62
    0xa0002c0006201050101201c640b00213441440b00301035440c0d0200c142d0500e075400340500c540d06500c400300031085400082c0e140450b56201c003411080d80c0490031003d2282e5084000034005544440104500d640c1d40174018041031a14095981014145d400a00301c03032501ea01c00c50100c0c1c0c02004008410b00e0760000c9100c040700314400b409410204081090756842340c58200c110f40103502001c507051007401c1110b00f800007254030007040b800c2d9180c14040d000b0240108121102c041400140c0100740c0b0200700700040720703e80c0303400b46030030780c2507600300124040000c0c80143c1121140b00c0004614115000301c01c81580034140c50300c000d04003400c214005002c14540c0f000c8464041040c1003041860980602301660408400280e42e116070882c46107401c0d81001c0320040c1a40c482c51074040c044201d0b11008491480103026600b003c030408464405080344c031903004092814003880c0c0701c40c1805e07000041203060880c458092030026026411306200c2405060b2115000142049052070300042016006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 902862841 1250 902861591 902861593
    0x305061503030a0206041b1e0f08030a0c0609060e06010902180906100818241f03030309020609060d020a020606090610030b0d0b070215010605191b081c0e 68
    0x2c030703142c030300007a617102d5010380010901c000384180e2050b03c0000e0001c04024250031020040d0340026008070b000c104225001d1100301c059503450000d6007901c000121400041d8039140c040a1082945403103005144e180010f071221a1211901004640144a4030380a418a1440182c50302510161125020b041c400e82ca03010744d14007800c1c05855643c034240b2004800c0280780400541d50752000d19841c0c4c06a850307500c0001c0c41b840c0500c0000b441c0c2c001c041510300d00c542c102c5035115a54880100344160946403030030565441140c1c1480480d120b90488588a40041e02251502c2c881c540482c00c141c0c0b0101c03940044660206030310301020b6040c020fa82c1c000c502120103032600d041c0140080e000c140780200071021b00d5a90160041f480e03c40003450a280750300401c04a49a2800e000082e40b240318000b0519989860b0500108056018609481e094a58a111560a240700c144207417007004407070400c0d00b251441c85030f001000410880080500844100c0c590261b43c01a0100c0c07429a6000c040600305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 902864091 1250 902862841 902862847
    0x31605040501080a05060d0803151c030e2106010311031c12090c090903050a021905070b0c0f1f200909070c0b0406150803070b0115020c030601030506150303 69
    0x1d207a901000c81500101060800111034542d80005a035031181d40314001c0c40c184000c42000090f881000d404006220240c07071018644201108055014000e0000140441d401014401d094281110301f201807018030a0108081d031601d002d442e00e410b03801d900c00c64800481032040415410180700f05000180045102c21406244400180242041c920300d003a85694900503c1c06010404025000410300040108441d245a047c0281581d221501c10f00251180c41d420409450341e116200c500d10340c101e07010304a001e00300301b88594640e001050040c09440340319003c410100007800b450100c3d00312100c15400d220107419051003074810741c1d07549007070300383c659801c441042c50500c1c01c40d011641d0407a2110b031155503004c4140c1c2c070030702108006010800084200f00402a40340d101e440c103407041208150403540e03a603032940c2d034920503060000d107a54641c0c0010040d100d01c00d00941142a058015202c0700304000010a242c56801da00c10358041e4458401e010384161860086070001d0b002f6030165207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 902865341 1250 902864091 902864099
    0x5071520070504020c0304030c1707081f0b010314130516050d020402030402151804060b0913050405031e031504090804030b0c090a08060711030307020a150f1103160504 74
    0x9241ca125104450081e6000266a0946901030049078055a4041c0d43c1c07800c10380d00c1c1e5120440103c12846807801c5441f0303122021490403000500c9103c100a000801c580c41d9540210410181090140380b605050b1100c2d200c0c04a040c00202c80c601c41c1c01e41100e00ca050021508149242120f81c10078246841880b28080c07105448040d2448011901914056540e031214404611200c0081c4104d540c40c200c0418071007002c040c0b409454440c4842143c00340803241e290590061188a25016141d11980c045c0c01d16640d4416500200d0744103008106881c14420780e101c40040d88070301c40d454610003001c000100400c40350940300b05d4032881c0c03040c0e40c100044600c2c1e958046507841a8000078101c00100c034000b942510103141180c0c02e401025042540f043d58805040740e4a00701070303c0c40c8011620782c80340c0450788000002680e100d60160f1340108404a41500c403008054104803550128076201c900c4007071100e1942c003070245c0190b908ad0350707581e0b0b91800c03c0210705104404a00d01c1c0400c901040100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 902866591 1250 902865341 902865343
    0x8391e04030305090109170327060f1b010216060e010e16060815060a051b01020d1b030522020609040e06010303080a05091f0905060c0d0e0705031002031305071520 72
    0x83c041c2d0510309007200c9c000d00d00e8044440c0030048104902da001000140c0c030a01c4050380800b60020340003014501449107200c140072400e07405101c00b404002e407079028010f03020075440d4000390545d0213104000181102003006d4541448046c4d08902800040020204021980806400d030702851404560008100c82c600186507840341c1c1000808200010404070108070700d08082c8048011588001c550303628600d260480a020358290030207442c0085804040268040c0c025540300300c02401e40307500703180843c0d0300c1c2d92603100000740e0a0307070000340a12810145031a10700c54152100340000050007179614524000701150340013440e0b444094140303070030b1000da10000240301401e10014020030b0415030304102618000d21050074050140e01c240c0d000d1041c0088a100100345a207101c0e541403045e807840c0201e1039030340c01851241e070f50164807030b02a13203502e10744907030280d904940c959000303065004064a44500c0c006a0b500801f80400e110350400c1499070f0004081407140070241171003105002040009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 902867841 1250 902866591 902866597
    0x7020415180e12090307120606151d04050718080a140d0903020d0201140315040c0306050f0d08040f0b1c14060d06110a08391e040303050901091703 65
    0x40c040030000130072850b845543c00d1203540c1c042c000c98510550b001140341040c80192040d885100481c186442460201070b20401200880b0590304012400c4400ba845c00d010007800f00030220410407102216145162860b8603282c1e005000030381c010b0107040880d003440c00e110f50b000080781b17681d0740c410501d02640c26003044c0084c0450340c049950b13a1150b5800e00050301d01e4440d0383c00c075240d558000010000b845a099030310200202054404100e100c0d80c00c601035080f01c441e40242c65002e8491340004c002450039400b48980603115101c003908040d503410b00b2840f10350340c40d0230040c40200b0100d9000740421088800b20454015100c0c18481c14402c1400d41d003c00d80094040c40c0120003640003030017440700641040d541f040e00b00b0f00c0260340e10403859008200100540d0103001126051402081d01080c03840580101140b00d80020100d1000346210811648003450142c0c40c403d02d0b8030072400d42070700000540b0065000e80c86035135591080e50300061400e50039412440c140410b4890000d020400002030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 902869091 1250 902867841 902867863
    0x70f06171e011e05060c0f012f130801110403060b01090f030201030903140a0e01020601050a14060307032301090b03010c1e0c05070b0c060a020f070609030507020415180e 75
    0x4680d121003c02010303c9004000c6410460704000f00003800700444d040003c038510210340c0c0e10001c1100801082c84a4540526465085285a620204080341010584c000e005101e10b28045040003a50381c06041e003076480041082d42c0300000801c041044c440240202d00806c030092030041441802c0c10004603a0305464040a410155511520342c00c04d401a406426003c02012800e80c9969214000134000040b20b0f070410300500800c00002114100101c0c11400e0f28508190280035080c048203100d41500014408800c043c1c42c0c03e02d46a002c004d001c0707910001030010014182660402141c18191038a1803d130501980c58262442c400a42c080c0c21020b0100780038012404505420404076034000c040031001d401401410704c009242e49101c40105521402101a02e0481d911400d410b4224020001c004d80c104404104000c0044c0e02540030021aa103c0d0a00c43c0c10324055402080880f80d03516403000307500303020250034040c85144c40041c903104e8500c0035040c485a03071103e912a8a44500180d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 902870341 1250 902869091 902869109
    0x15030b1b280e0d12031112010608190228020a0b0601120f11040e0f01031101120e032b060302010509040f0b061801030c2d02070f06171e01 61
    0xa01c4003016110b10b110034040040144030141d007a202d4100030740c0803420b1041c80d10100340742010400130f0352804410b60740c0d0351981c02c03c83c01c00c0303a1800c101942c0d00c5c0713002003516030142664140310300310400302c3c4040d00c080304100d41d80311100b15403001c407101c60400001401c0c056610112000c40021400380f0400c0c2e000d4400c1c80e065200180c108034060151034609480340001b420000c001c080904142e002e082256445c030701c0da15003500d443c1c5090320550b40a01024101007a000244000d9501511100c00c1a904004000900900041c8080e080d40c01002c40c0d40c120701d00480d04850034040c400c40c2441000311812040115a19650018106218aa0903540030340c4d2100100a407507012603000b04261100030313103100e03a41c0e504050403a192000103001180484d1400c025003c440380310701028098000418102900030720340d00c0f102c1d1b08100045440804510980001051012020303121300c00914041c2c0781c0740c80d00c464084a80325034420041904100441d2040841d400f040c9005115044a007548 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 902871591 1250 902870341 902870407
    0xe0a060503090d1821050d09080d0302030402060706020c0a2303180409050706051213020d11190f05030715020a02150c01150e1003230115030b1b 64
    0x4c10b01c500d4000c003075444103c000d8426107141c8080c8141d14000182e0710301ca00151500c4800414007034600d09420b00414041d0b60204503075220080c003d900a540260000b4506424a81303195200c5013a40d000c00300103d000d4000e40c01c85410030004480d519207220b0b01030424404035010000c090782e6400b0b03501c5420660078413000c800005494641c000d400c0f440c1c1180950b09000d443c2c41004d8210342c4111100341402012500194a621440101e0941c4a03801495000741c840151508800d0624824820b035004001b41a00014a0361651409c0020320726111141019071802c0109428100240d1090310084034510071100e00650101d03c031256075904035a680ca00e50700c041c084400078011005d03425025071030140b17120700c18800540c4140480e058000029065590000003000c400c0180c440181840c50714030f42d903513104880140020303403035038981c00020300443d8102e0304004400a0390700654071442c002041c00020128415441c1c40c100703400a13aa46018111459400041919510560300d880d030760f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 902872841 1250 902871591 902871617
    0x3070f0c05030708190504060f050708191e1b08030415020a1d19031113020409050405010e0a0507090c1b1a0a110301140303040503030a0e0a060503090d 67
    0x800554400640040807a030b00c3c2e000600e072030582c550005201d1080183c2030583c0c0140181300e0b608a40a4403299940c405000c08204010f581b00c1e0004c081c03c8640320818070600145440034052074110440f599038817044011030404140e241170340300d2450002c001400c180d100c00118403040440c00c181e800700c001d50341d07580c0794100a401c901c801252059102d000145541e40c441d4051461100b1104000703071a14400703425030030000c4010300301d204a10803c0c6044030030004100050001c4141c4680509450142020351513080c04984c00b81e009405102e5499081c0014803031309204694180c6484401810340c00b041c2d03150541d44e030307105104175450300d6201c42d0308444051045000c3c1024022030b00b0041803048051a111041101300007600410184807000190300c921030b8050801c8003500c0050b000d02e1642015101615035012412003601840b04000010303094600708010f00510f8102d540e03d181543d000c8081112903031469000c0e00411000b401404169003001c280d5180304802403c00d50552921 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 902874091 1250 902872841 902872847
    0x90133020f0601090c0f0305010602060f07030b1507060f020703050f0c0a0b040b0604050a1a13090206131e0b030c07031e032304050c100215180c031203070f 69
    0x5410750000c05000c2c2400010306080f00750441c020074100c2d030726400d01c1541030b250100e003210700034454a0010b0303004601048490f5500116140c11500c80e1801154541400c004242c0b0001c4240c203822108034000754040a01080d48641b40302c604051400750f160550301d4130001c000780584080c1d40d500ca2000915941806020001000e025078080c80d1a0054601800c102207015422982c3c40d01480c100300024500b5241480340044020744141c2c851304030007c2c03d050007040080e00c21041cac401692020408090b986079030151141d04118407491a007542061040303a0400010b5600100c1080c2010b028030041a041041e60303030085031818215107904280c1822034018103c9040408400500ea8561414035490382000c860030000c01c040c0030b0b00b2000c09525089103403086801610301e801450b0704000301d25000d0804104039641340704503400c0c0552000314804c003e00582d80c1c00da55101c2c510642c03084220903c5501061314007140074217004401d181d4180c0d901d2000402c000304100c44c01c1440002280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 902875341 1250 902874091 902874103
    0x907030b040f050f0709030b16020a0c0e061215040803040501020702040e0f160b04090203091501240305130b130611041d070522050d050c09013302 65
    0x3005009000c0c0c6180140c0d200020403040c2e541014400204000641d0640241000c030204d0764842c2c041c003042da5440300141c0910074820307081402c6001f210f1408000c546001924000741c030b56285001c4150800c002007002d0b5954060700c0700c18940005120844401d4010b80c55a80b2a42100c1c00c1c40e9656520724009009128401d8000e41c050700d0090038038103907240014030a28440c044012510300034131450030310303040c000c0d50b1142d141c00c80e40c00c00081c0b00080c10707a006141c001e008102101c100064090391110540400d8000c05d030802d1000c035400411066030302c0118480a11403c08001e54200b4004000b90035201f0040689110400404281d242880310b00d5074100c540c02113010072010005d0401030842d54054410451104c454407180d07240315041d050110301406054a03a540f41c0550300300386245a290020440407402c103004000961070302d800852103d4948110b0143c80c2c11154030341040541c0300e040e04100541d0602000340c40701d50584801121180140400c455041c11400340c0480c9060703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 902876591 1250 902875341 902875361
    0x9120b01092c0709050901110708090d0f05031e0301120609080f12100b0a0f0309020312040306050a0e0c0f010309020303040b07080a0207050613231e0a080703030e090703 75
    0x20b407902101d005501008548403059030b0ba1144103200300c0e186c3c0388146083e070300103800040401030200b102e40b0005080700001c10b10008080c02c003107046255500c6407082c4141c0c00d041074607950000035104940340d1081c200c00007903490282c1910f0440d410306030385c0506901030040040583d6620801131041c801e07900d0666400d25814401c0d10340c0c0304200c0c06401c103440310541e20032161140c107043c045529800c1c90300f038900b048001e03034541040042d416422409000d5000301640c050143c400640494483c400003480514041c0e10b01049908007044141c040340c00c040c140070601e801c112082d800da81e0f42e00407c0b920200d02403802007070545150001a0440c4103d51044a201d20000340c22002c02043c94042e10300001c0c02d80035a0200b956501c28080b03039105261020704e944255010600c00020341c11840010304905144407000500c0e542c0100d00840300c05254064211501a60b0408601d408003894000e8800b110103402550b01d555400303005494000b01c0c827803045080500040007075200e680404415 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 902877697 1106 902876591 902876651
    0x71a1005040e0102040308221a07050d0309021f0509030118150506240d090305191115070c060204030f0201030605010503060915030f0f060709120b0109 67
    0x1004401228030023a140460128616928030108075000306602c066030b13580c1700142070652420f4141400329041500300851000144c843d9403001040f07071110002501091440941034a403401002d828a40543c64501e45224403c110713604210341c28080c80b801a2008400384009007541c100f01e030902e80080724041642c1c20b1752200c01c050044030909120742401c0c2018102c003403081c1c0b070354140c0075000204c0104180711215104203e12109103480d0511064403428090502d4031400310007042104030014000203074009009030305c42e42c10b250707000e44119503450f1640782014600c048880f041c3e002030700c0c1800c0407410394040c2040701e0284000400025407640d81940322984008040c040c55010b000d4520302103802002000241c40c540c180c0c0740500110711b41140000e105c641c0c903500007400103c0705910303240403504003102039064800b0181c020558210304101d4503000c034203a040245070 = true := by decide +kernel

theorem cover : BRFrame.Cov 902697841 902877697 := by
  have h0 := BRFrame.cov_init 902697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 902697841 ≤ n) (h2 : n < 902877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
