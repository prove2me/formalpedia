-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3964
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:18.201028+00:00
-- url     : https://prove2.me/submissions/bd725915-a46f-4c59-9a04-c3faad8ea03a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712769784 ≤ n < 712949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712771034 1250 712769784 712769807
    0x30705030102180d020d140102091f020607030c05041e1e0e01060e12013e0d020304050304050603133c0203070f06080609070203131e03060603140c01 66
    0x1028075403a00c3c9840d5082841d138840480d48001c0c8650b840ca28103603501c86040b0328851854403281c1d0b0203d002001800c1c40121184070242d01340c01d07002270007150ba00003991410700400e9881050345987c4040d11481c06034055038003408808407007542c44041d01e41900100d031402c0c03240380c118190020003c1c0382850001045004d9500c10002a1840d078209842940c2c0d8184113100f103038100e41c07045008981c4039020b1040e108000250700c0360744444624030010103000301184c2051030094030602882c900107151a411a21b10720210540562240c2c1c0c0ea003000d0b170441c0100d0b4031990300140c000040041000c043e280b00154980b0439a17040e62085110350000015071540f400304040d140c0403980d001400d900348011520790380c4c0b00404541c1e1960701c2d1034000c203009800303900ca0b05c045080702c8184013462402122580d400500c910007103081074900e0900c0d0080452501c07401418207084203a1344401078042080e1000746030084424003c0d25901d141105d921021214500c0140c0511100f01d2030540c41103e00c3c451 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712772284 1250 712771034 712771057
    0x10c0807381f060f11190f14010506061813090503040f230402130503030c010c080c070c170a1e150b060418060e01080607110606010f030f1d0c030705030102 69
    0xd09640e124050780c42c004410500000b030b100f041524686c003088003490b00d00c014814a4903101d48030355450320310800501c1d50750762411b46c1d042c181006070300d4440d02d050740c02c001030081050410b509000c0118144901c000000001a810b10405600348038000005108a0381c102030304d401c40b0341d680c0e0702600380000c1d10b12850241010f00843c081f0301346862f801030f040c0b0701800302c00c1003081591a80041c2c550b81c0f1021744a502c0b65100c1b03103081015500594000d500c04071402440c1d190211940c0c946418604600070b90501000946802650100801c020101c60703030312100902c081103c0da480040300ca80100d4044031300c1300004a01e085074600c68000e84416640203040f403030905003840740c9685442400307136a41c6802c9030b581c80006240c0d0307040b60040b0300800a01d40509807078103201e803006159540144034000942d1004060080c2d591f40082c2900071140d082c0b40004504540040c01c1c405001a01440d45240000010103240300e80082088980c2800480498010070384d0341003414240d0003a808001d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712773534 1250 712772284 712772297
    0x21020f0f06190213030606091103090a0b1803130f150801090c030908070c030b0105090705030a0203040c091401150f0c0f0c081e0c010c0807381f06 65
    0x100810755501c184403202e0080c59000d400e1402c0d0742c00d10b515541d070380e900c1907550985500c400c00052a061043e03640041100480f949107180c480e2031540c0d10b00c000303d002007140000000160340034000d0ba00118811116801f529a603030100e00f5002d0f4090382d140604444842080c000140c4a110349201c9404030300240c5544c0c000c0e030f10301160880113290302d1305e4440c241610307488440d000826a8004040c00c6104440d1003000c982541094440c4000580195028150391010711070741e20b820000350307540310041010159481c0d40d60302d070910365511950301c800800ca0030400441068444015580c0c1681c21800f170040400301b03400c008940b0b1117118003483c00482e80454900000c90381c00ca142c4c580a90003000d42c001c046a40300c008624040c400e100900c0401c07000720080c007075403c0034401360414040910f0880c0b5404407a44424805102d1440002c1ca0b4030901711024a2110060802c1681c0c2801000030003402c0306801e01d4003441e0002207800c82040354200001e0710100d24109062020389945641d0760 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712774784 1250 712773534 712773541
    0x504050f0a090305040b070b0906060a0b03040609030306170c1e011413030b09160812040e0405010605040c0c02130603080a052b29150904060321020f0f06 68
    0x4500810b100d0000750200031003004081140080e42005100c6a40300300b50350461450460341944c00e0120103041c20b4440c001c0c6903000c1001c000c030841525005500110001280340c554070702a002820f6a030320500d200310103900c9441c080440400c55012044064804c21030801142d141a130001d148020081d001c40d440516000a0385801760103480d00e04428407400c1032458494941c80c88a2104072810080e42d4460050740d8460030400091400500e0208020f10409445da2a00540341c0920300680803440180760001e0107010094005400800010307000300540601c062008083c1290194183e024074606070102e00c000f0001d11400c421039800070030b000d05010260ba0211620f91040340e024040601000303060185c00520f140f40000080000c0d40014080c408280f80d81441c1c071500002412000c0001000703003139464018120144035080e809080c0e07203000f840d0028000f4200703a00060800f00c0917001101c11081d0760a07c02d1848404c503022903000f031500c00300c080d944416403642d000c1c80750000c1011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712776034 1250 712774784 712774801
    0xc030e030a0516020603090f0706020d0906030e01183f0f020f010501060e040c0e1e030118060b030f06160c0c0302031c030518030702090a0b0904060501050a0504050f 73
    0x41c03c0345640b020003654544034203400241458006840200d0765402005108004040c01c000040040010b40081d1602c0402040040c1c20b000300ca04c038210515840705c0c02c0200c0390707900b1340c011004513100c0c0c031203482865468146040c5001d00100032030313507104607440000705a000600d00e1001d0b0340e80c0300501e00070442c1111030440e00007100f02c1003001584070311144c40251090038020a80640200d1359189460031220341004261440180a0380511403003400448803900c8004484202020f042184040750050030041b0b401000043d02240c802225290104100002600400c600407401c40440d4203200c01404500d8480c10103546000801001c01040c03140940603a41d503903651402455501c4d41e456403038001c00d051605560407c04040d810301c1242d0f00c4550948501500700041101c4040b0340301180240d150340e446100300280c071130701c5440d0019a100a80e504100503025010f8205070007803c00749041c001902080c011140b0503050420003194a04107849018402c10000503011540d4654804c0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712777284 1250 712776034 712776037
    0x1206052e0306050d030c03120209030d0e1201020a1236060f06030524060d02040f0f110c1b06030c07020a09230f100b0c07050d03080702010c030e030a05 67
    0x80c0201410b8442200107065910400d45011140c0030743c48a655034811454000c012129140c2c640300820b10601040c0169140000c00480303a65850403c100709801020001c1c10845401c15201041d40c000158690f10725030008186002100c058020301c240310011b00f40c07204003110a60410001c41d14500080301000519620040c0640102000160030010b07180034020348180760030a0b2965801081e107944901c2c000d03200b0b8860766002d00b4441d8400d00300b100020321603882042e006403041e5243c84444203281c500d6445400701c503410203000c10034007003810500c41107500009118206402158903420125105410301e00c00740300001c200c00d1030356581040191954000342000c6c1e030000c1150402040b10f034035621400303480d0b252075840300003031516030108121150f030300034080131a1800103018048000c1e07403001c010095034040452181c541e95285c80051400086a1045510500c1c0400c0340003859000710100d405418117500038040e2000c6113500307500f5540820502606a4801c110100e0b0300c5104a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712778534 1250 712777284 712777369
    0x607020a1e050c091e01060801210203122101080d080c04080c1e040f021803010e0c0402220906060e030307020f190509091014040c060c02060408030a120605 69
    0x507010080004d007840d03e41c090445c01d800034404a205d0710014000070b80d4590101c50b00c0340030b000c3d144541c600d655020030380354101540d03070b004c1c048408618107010240300b4218032200c1071008201181907a54020495907481c00c8150342d000324188402240f160000042160300703a0301403070003d1840d0b020460521040a10155100721b030b28030700e602c4000b03165545000365294556408000358a5110340311034003c0c0714600b00d0010f8401e82c03421000781108140440c01d66415070081344c00603110b003440e480c10350f40404030301c0400c218610b10780e0340450084010b900200036207059a03074100103000103005141d568405c2800c0694458001c044c108001c1c03800450841e0a0281c4c03225610140d035407800410446001511064080d40040c0a0000540e800c0d101da4203004100d042c040415040c03c1d200ca0304284c00307038001d890800c462420300f070b815904e0b0b090440300200030800c110780d036803020300c40003d00491104240720304641c1003000c0002d10386001d4034507603051000d6000313180c041c40661b4080b016020820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712779784 1250 712778534 712778551
    0xe010908010f091b081b06040f030303050a0f0b0609091b0f12070903021309020301110703030f05070504051305480412021e030607020a1e050c09 64
    0x100020580c40c100380a070380c0281c8800a00460302d0740442c40c0102150003110503500e030050790210100019900001e084010160320480c0c1d0f00310352610004a4803074407868001c00003800c00007100104050740b580c440741c4a8200601c040202c06c06500111066a0090346002d9000b02c05020200381443c01101c0c65410824110fa10140240790b020b8804d40364011510702920400c0209107c0d000c40c0040704030a070700141a14114074083c1c04c580c001020401c80301410180d20f0750b0744100b00c04641f0309511031003102d204050180c0c0c0740c848601d0001c0180040040411896080030041050280581c0558081d11001048200713841c000e08030120051400078a01d00300100c92011000c8440311f200000c060b081c2e2642a2170f00040c02c0c1103612144d405841800001402041104000000c0302c0f44040ca01e585c0d0481d510b1030103425003441240d2407044040010b505016407024414540c0c0c000404d140e220b031081c80340e400d01e64030b2442d40c4150501d070b4103000f030090b40020041410320314050410983c0008034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712781034 1250 712779784 712779797
    0x4020f011218020103050c040e01180207050a060f0c031b030903020111070803010f0b030c0d091109010807140609031908160b0f010b13030305031003020301090f030f020d0806010e01 80
    0xd5000300002d498480c41c0d0008003000030010103082d56498090302c1c1c1d21400003658546801c0c40d0441060f6540c0301442a48002d4040e080c00020500140e0121100180c009088aa140c1c1c0e46087c088000c01072080101c1e4543e15140580b42818020f000342d00c80a1003083c0c204103106244403003a006004010012011035580701440c3e00d01001d032801070540795010b1b981a07074487d814103503040c1d403404580d0004010042c0502c00c0200c04c0c0d10f0f50044070414000c01c20041140030301072074442c0c15103004100030b0ba03000c0c60620000c1810400003072007400b04d8100c00b2a844210031400c1c1031008501c00c1020359501a00f040449502001c1a0310f41d070701107644101200741c5002402c00701c9080f1980c1d0114100c1c3c070a1400790074448480c4182071039901410410a040c0d240c243c40508400b842403061200034244007000c80050078001c034907000302c401981c024000b4040c08006250400840042050031004a01a0b07440981c0301c1d40300003240d010b402e07055250f00c442500c401006481c02c0c9801c0310f0540c1008007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712782284 1250 712781034 712781057
    0xd080a0b040906051806010b092125050109050f061e12060f010f05070b1513290901090e03070804170f0f0c270f070e0a0b0304020f01 59
    0x44520400c0b0351180034050000391400c00b510b45000070803021403180e00c160700840c01070004550410482d540200100d07038056814060300745081e15001c403021000300601850a0300c841d4003c840342e00d8289080b02092402004d9200c0b070043d074120441c2d02903150080c0406100703214038103248004020380311a28804000c2c010300d01c03144081d00da005416070035040d40007100707210490400704103840300801c090a0402030304250b40001442409504e101600711904c01000c5070072840c0d0b8614164903c00e014201100303a00504001700007a20050360201c04080325110b2050140740d03c2d42c0c03c00c50b0320800911480750760b460501560090284000044414001084040c0c0010300120040c8000d05041d0b1200021034803041c601810311065a00303002c0789401c03841f00e12400b80c0d00840c40200341c0000301e95600d40700e801445080d000f40241c0350f008001c040b415060085c559070b0094100d105203c0ca90b40c103801d1450390070a10440744103074400d032410440107201103401440c09100e0140c4500041c940704ca02c1c0c16 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712783534 1250 712782284 712782289
    0x4061d06042106060e04080a1818091506080d14040b0706060510020f0304170a05060103110909010605010503010501050a0e13020316030e06150a0803040b0301060f08090d080a0b 78
    0xca082440741800782c12800ca010030003129008800085c40070004000807894030762611902481180d10107002c02051060f820303203810702c80303140344060a0041c2e04500c100722156a41001040c4054040c3c507075019403c41d850400620f0701581080d0b0304000040c21100703600c490282c4902c9021703000c000c0e90882c00d00000c01c0159014024190f218045e00703011461a01e0700c0140180109266900e00442d0041c41c1c100501c80000412a0210307507001e511300185e081c0f01c0c01068100503596200a20300e01030304000200307210007680000ca01e4001201c203110503448403601d007400c075051485007a001c44c4040c00108200d600400c0a80313401602070078a2105d07801000001216161044c00b00000c9907400b0051085900000702403401c1040c03542000c1010403500340036143e842000603e000098440c085017090507480d807460840c010000001204d071100d03120880300f20346070804d01441001030ba0740c041380115140b0410181c0d000c1c8202c80064a2000c02c46d0f00304940c03000f8001c000c034001a45030700c04040144c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712784784 1250 712783534 712783559
    0x50918010c0207050405010504090c15090b1603200a0305130b0706060f05042c15010311011209111504120303020403061a0102071401020a02040e0a06050c04061d0604 73
    0x10300c900c0d40640f40b15803c04082004a581c183c05c11030140b80b41c910f520000132100000c113415285203c0407020002131000085071645039641051009001c0429504c140701d800c451004c0c60944a910341d07521451400009250f01c069004504220b40d22240d84000400e00400040440300444242c2c40002601e40c1e540105a5208000842c3c241741c0c0d88100b08100010511009e015181c202c40c14030031040a400c561741003421342842601048000e20080c80c040d88100801b43e140d0ba486a210300c00c9694a00706048005403c4034024003207500185a2041096240324100e1140e50080d40d0381c140b5160b00b000d001c0c21005151310405184420840414810f0522524450729842503401583d03071801e500c0d0440c10b6546c5540801c3c8400601c0d00260410b03a00450100161403409200c80403101000d00100e01d8906000000f07504189011403600440a02041041074140620780030b01c030a4540c0c80040d040c5224620910300001c0e001804c00350002a03c0ca56600e050400911013420243c41d41c0d00340496 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712786034 1250 712784784 712784801
    0x12070b07050d1503080d0f0b0609061309060e0a0b03010209360a02041a0a02120708090d0c050f010e090c0a02010e06090307020a140303040512101407030b030f0705091801 75
    0x84000400c01c81c0e140350641c02807c60003090041c040c082c0005010204480d4013034200800e1044101190407031102850090103c0180840c03441800041d544517007001c601f0000384c50710050f4904182d500720840c10140202c035500c80005d042c21262245040c0d07400c444100400d03030050201c03984145586c0e0021120200c4e03001d4100c2010040e6564541850700c481c844036696a80a0b4000a100b414030103900030441d03607000610002d08030b540740110315060009114030071b44554030070100701000007446600f1004400b600ca0948803620b00c02000001515482a441c1c64158818030580c001446448010064046d081d4180004510040303c00340d21400e02c5421550780c003060748041200025413400000d418002d02a4503220b42980d144000031944074407441c040d940c0940d000c4040c400080300b08000c1c104400f00030842c208011401c910400703c40f1002074030040b001030f05004411040d440c000c42c640c05d050320613800403c1c5051070402071103880c100080c09840d0390070703a51800300b084840a00030081c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712787284 1250 712786034 712786043
    0x4050303010609050319081e040b12060603091b030c0a09140f010303021908071406070e120a060506030106230a060e0108063307020312070b07050d1503 67
    0x200c0c0d60500e80001c003114a943d2181e8425404481024210481040401c2c40540c11001442e610307804074800c01e807100340107440e5015050300000c0006030444480082c140c001c600290028503900c4440c1080b40d24041a1060038180d0400900c1400e00c01c1e0426104000480c0a4162058030041d440064000031701c2d503029043d00740d182c00780070101c8020003032400d601c0740281424400e254116200255169807104000c03000480f01c1c4400810300ac0d005098480940d4001284500f15288a50144d01d801050f2103e10200c2d5034580c1e40388183c500382d4910842c88283c82c1c0284100003e030f03203c1c04043c00000c4c2c0382c2038065580d4a4040b030304030150000300125480840d8240706000003801403020201c1158400d00c10803017210341c940001d80e801411684c0200c801c0340c01103100d5070000400e02d44081c584001e1907096102c98450002440600301401c0507900846c103035607007500249841c27501e51180e188001c0c001540c860004803128082c602402c1c42c090590400604c44104882c20803071060700f03810035074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712788534 1250 712787284 712787287
    0x32f040305010606020a080403030c110d051e010b1003020d3902060601082d090a060608030c0712061401091a030a0206094606091a0a050d05040503 65
    0x401d00c9400d014400041003680300800d644a11611211442d00950100070208110461658180030491035108450303240240060903402d0145401a40c4481c64403101046d08103000c51103040304418860840072210251495100b250034120072002540a441421900bd5884009509004070400d0007480640c90344504550b480d000088400c081c01d0202c3c042046502c40d00400009903802408143c014038040c03490b1510000b4a80c820668011210a00c0940100c130000c00440c040005000000607024250811205071112403860b100d100d02100c1c0d28448e840004200301500700004d032801c206000d44000111070761a000d656007101800e900450304547c892100c01b51215444001941180040b8014901d1465983c0400c2c400c1c002d1640c03451144c14810102c9030a4a8801d184102e10080000000d02d200c04804402e921142c581e11043e0592002c0000810404e0103a580c000136214048000d00c4032500c000c4050202d036000086503010000203122003811344180380642d40c05680302d8405076 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712789784 1250 712788534 712788539
    0x70f0f08060f0c09040209010210141608010305030315180106020109030e06031510092402121804090f05160e070c150b0f0607051609020a0f032f04 65
    0x2460220054003a01c1c2c11002e803000c0c050a40340c0e0000b1a00080300595000d41c4486a64006030b0420f01c1c2c00078413240490031300c3c6000105044020300c00740304d0380b0500c01c14415a840c40340b040700c003100240002030083e8810008140803203200800d10310745039401010f6103210300390790f400e002e03645c1400c0c1c0c00840076130b4482e540300d4209074001c4406443c500b400c0e21854254a080d02210880e407850402613030007840c0900c20703203014510034072504000d0030500107000c0000852048071900401410b42544c018080c03400303010030025441c01102c40009003940100c444641c03035000c00000b001030b42411075440c8050188040014000e10825000300b80c0c80106e00d040748e00c0c21701c0281c068100100054204014200105d00045810000b0044090265400500c1051034404508401c072107040f042c0d8041808185882000030000310a020044a10302c0348107842d645075894001d9000e014004004184c282e8540d58102d8400ea00100c40e14094000b50100402c9400115410140e0801d02090030040002c0a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712791034 1250 712789784 712789799
    0xc0b06031f0c0822060c030e030f1809100e0901021b01020a0e030f030d0b030307020913050c04060e0a0f060e011805010819082d070b070f20070f0f 65
    0x460780410034050010013a6100603004260405440d401003c4d203541d51001041544a035000f1900481810100c90b07403205150305841c02d075040000e503000c100c0c40501701c00100307040c0b0710b000c00d00030461009003d607103906000010640d400c004000c0e04041d0341c02d008200844592a0340d942c040c0300010001a50781c100100028912403940c4211800303640159048141b5040000c1100e0364801610f000141e41348a0500103400c0d80304011000c0c0d8003c0d0300d1014464a00c3c80c00b07800d1034905106004480704545c00000344000c1d0f40c8107110300411a910b280000f40c07810160f421214192035080000113860381c50302240401680281c108098000414201443d07101c400d1041030302501e280b80041c0500d00f0300140c13400304600341c90801450010f001c1000c1c40d04441c0c0300c0120412048801030000340d42200020113105401085091750381d501a50003040900b8018620030320400b4983d99680155461070001196801410300605e030b90b4441d42000050000c1b002c0c1001700500b1002c1101449207180403031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712792284 1250 712791034 712791047
    0x705070206040e0f061203091e04020f030f010905150409020607120e01020106080f06160210060902281d030f06130b090d170a0929070f0c0b06031f0c 66
    0x668020714090b281846d1881c000000e80350f4500c801c031528500c074940061203411407103051b400681c006002042c03800c06210920043d600c2200710300407406941e80e035050600192001070f42c1e01d04144c4014004c0c1c0c0e0450400384c10480440c2c1c005800d03d4a0240b02d944c8008650401c58600000204c0034507803000a0760303080c0100c00080c0301e0b0130010110500800c071110384030000a0b0150000030044a0305c031003014000d01012004269565080040c0c60b0f90300c4461020354480302045100b00d03104585203404a41c000c0103c2c001c01515a01c40e42c0c0a03ca1541010040c003903c02c049505206603c030790040324004010541c4600c000f070b490002c01451602c1d04a01d00e070000b40010001d508030900da00811580903003296110480c0b44a40010342c0c45200d481e9000788070b03008001d011603284407035000d100322603100e840710011195030f800354044d50785140c2100c2d2b04119401c1d2000051034008107501080d0139200b1903400000080c240e073304c10912201c00c2140e08681e80e105482c243c1e15482d00700d03007040d00720381c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712793534 1250 712792284 712792291
    0x6080609070f120c15030209040b0402040b0315040f0c031e06030201080f0403090b041d09060c040308074704020a1710023115080705070206040e0f 65
    0x2000740070103400c111082484848030300030784080484400ba00000e0142400102004002606540c0c3e014810040005c2c0a503010100c030034019808c1c102a0005810035201301c400302c4a08002890840d100c821035000038000392107103140c0c002e0719001401e8a000c5188208840608503403400198030400102001c07501e540891641201440c0c04000c00141c0d03085070704154802c1c040d90805025682c2c600d010b440c03070744440c0c002018102c40402c002c682c1c40c2407a104103450f000a01d070028003556520080e240c1d0f6290131201c1d256500c07402d000030030000d07841001601e003040c030800f002249990741543e0402010010011840720010100c60700103c81c0c65150b030b0100d80103c0c070011280c01e182030b40110304500f2042c1300345c4505500e0f066041d4180401401895081c0744030800641d41e42076140c410340135981001e0001e0000c50f00c200485041c44807008204412a2040a42e05405510346802540d008000070402801e01508004100060703845600400c040e0100e011281c0c0c0c9800c0c0450120002c90004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712794784 1250 712793534 712793551
    0x40f02062a010c020d050a090e13050139050705010c03060302090a09022b0c0801060807171b0d0618060e01090f0215040905180c0303040b0a050a1103030406060806 72
    0x10614485213980440d5000b8240307983e040c143d82da200d810720100c034406c0b20359108400848213032052025000c0c9148000103140c0c0940002d010591803c034601908500c800d030040401084400c054000c0c140d60700406082d203200341002810900039803219403d50791004001e20000343e840340203000f10710780b503030f415900041c0e03407482000b032065540c0c04101d00c603886a8250502940b10307220300c0800442c090805001e10382c0603802c00640c555a140d4240a081d040c0910003080c080c0701808101c91020351078004c04c5c0b0408030020803465005440e40e2541e1313031240728040c0d0441e80604604010071007a0003801c800350040220341043d01d1460420904075030760001042d000ba4141442007012987c030030240901c1e1601190702e0408050580c040c190320388036135448102114240030400411b43d03501072204100180c1c0105480001d11500201501c4c0e108501400e2000306082c095101d0030341c402e501508800c00e2a081107040c48500e1480d040c65a0000c40d02112950b455000038440040107014080c0c004481 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712796034 1250 712794784 712794791
    0x607180f0b2503020606010503060409021804031e020c1509030616030c03020906180103290307080703080307030506060403060207110310020f0d0b190807030507061412040f02062a01 80
    0x2c980e8001d45a110250400c4d04008010011502d80d41c0c4035802a062141d0003031500010803010b0700c40e0203404804070b500703801086222000c0c40d245e00d0705e00000e01301c1403265409010910301e8034081108121000a0104052800307011240064408004c0e4a0090040c030310003140e27a4051810083c02e03511801c2c800340400d8018000381c052a201c040c152912600d00300c0d000f0400c0648800102c0c0100410000349407400000040441c2407c1800c144010184082d03080c0d552403911f0b1400140d8905141c072000384041420000036552520a51060f0b4011074000c01d41e03171030030b941c036200c0030140d0f04203920a42e0117446c00c40d40d0034170a00d000c0051110107005130009505180104000030003a00404021048058031501c0c2d52102e9900d04000302c0848107101c0a081b071807034031445410307618840d0b070000700d0b070a104802c004100d0394061001c240035110503000440c40c2290b01c8200c5034481d00080c0003100d8081c0003032070020045ea610fa000d0a81401c1c2401c000d03031410b1080d8800302c0080220411140281d14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712797284 1250 712796034 712796107
    0xc020616020d090303050a0c0b31050d050d090c06120f06060e0607020301020412050303070f05070528060504030f1202041d04030513060f0e040209030607180f0b 71
    0x3045100f0794112a01810a26140d1001c00d400b03a454003007060005180c04543c07001c00002d90000c0702c0300c1c1c0f641c0e42c4840c005843c020071451441d20582d0329690142659010a1a4480c520702c20001415001e04202c070204603042c0641d01c0c5e820524240d044100400c402160003844003219100d24042c81422140520955180100c080c04840c9401c45080c041c14000540b28150f4400b5011580144402c6049016088540c1403164881d081500c03410002103410350700f03040c4244101c05031018a6044006080c00c031040d034507040e00d0001000c0d03200110225050610000c01c140e485410301c12406915000040000010000d2201003019941030416205000920001d014007448011203412006444002e894030305058606000c1c80d801c0e82d40300303178100f400401c5c52648043c044010f00d5680d12851460071204c000c12043c3e014400c401901603020b40d0000d510f080c402c07601314518403280c03810b82e4041030f1070720804200540182c00030050740000040e11000d05817030804640c19010900c140505401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712798534 1250 712797284 712797287
    0x14070b030703090b2203051e030c0408010c02071d0a23070207060504061d12191b1202040c03020c07060c050f12030c030402010e04060e071404060c02040e100c020616020d 75
    0x101c900402900304407000c18000000306108d00184100c0d92191a025168a071058400390141d100d8000d20301594203044664020710b00000d00601590300c0e005903001000d0342c143d941514410001d040050031b5441c0c03810105101900701c612a82ca0b03494260b44003461a00c3e15020f03251001e158441e07400c1003001c10003080010b90103141105010300305181c03030030340368840b100160116505a1403884c182c050860b40d1001094200101c0c41454421a0582c40e60090840e0041070481e49108880082540c81c90b0701006190560100031060000e041c01410200c6820105103082c255403c5000411902c40c03038030301409000c2210004140c0c81c00000c2014902e00191140d003030201401044206002202050440e8001c0c454541c8484014000b00b003003580d14500012500d50a40f00700002c1506510701c441e070740f10f400003160700791411f03a12000c484200990031f0100900c8003106040282c0a43c410800804082e4040d110324444d07a54020030050516030a05c00c0e0441200e0303410000d55003e181c80c505042d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712799784 1250 712798534 712798591
    0xc1505090d170c030a0807030b0f091317070303110313030c030c0501050705220509220803090f10060f151101240504060e010314070b030703090b 64
    0x5910039196035031052290b10b4840e114500610729070840c1540440c040142070400400740604801960f0351240c9622640070070340c200e810a41c0403d0300300802112900480c1407444815410254602c42079840c400c1c651140300148502e903c0302c4c1000075000070403a0902d40e241c010001050060b01c80c0c14594109440c0019000d401c60200400340a030b00d0303c5100505014142444040d60490001d0080d49081d040080c210361100a0041d078005c0e020309860f04641c210001041a1003014285090780e48070315007001d10300308022017504881035030b017102440011010300c00746014110000082403a089107411060030103000e00c1d00480b00a103007681c1001100e4402034210100c0e0603402d40569a03004440742110301c0542e08403011601e40c28000100c24103e40c284078400d80318491401c0d4043c8544400c100020ba603081d00c60300c2c4030a12440d0040c030100302c54000c40440e0912101c202e42c90710340c2d14040601503030000c80390b51317001c207985074410801e00c042809011350003880314202812200c014030592549 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712801034 1250 712799784 712799797
    0x1020406020f070e13060c120c0e240301051219051e0a02090a0f0609142710052508040b060d150e0a051f1508030a110106080708160905090304030602180a0e040c1505 73
    0x440800702c00003d0fc10040c000c04d40ca005c004d41740a401c01c00d450605a0b03440120700300f4541840110700b40844031190105080450a0740148071b14140d440d08041003026000c20b240404c00c0b40d907162030001e90742040d841600054402c44405099510700106442c0c0040541400c40010081d03515603c440d030000483d4040d038030445131600003819101e02c0414207240004036003801040c1d03108601014010703080300e0010310540c42841c207040aa0350b28018401d00e1496160010141c0c2ca0759200c05900c8036444c0c01c0400402428000c44012403120b4490510340655140d4138041d004020103440d805d524280101c83c0455440a01080c5080c6401d4655a680c490180d4200400c0800000300c81c00180c00c0d042900101100411184425110180c0e00d880c0c00748400000c105400801c80058002d24501030184a0000d0b00c000c4e50410749035450381d0b000303940192070414480c81c0c14540500641e980d1a02ca40180c0032110943e949071030140b4110f05000a540c0100c89036003c2d0f403108501995004088464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712802284 1250 712801034 712801039
    0xc040b280815160c0f140a2f010c0f08041e050109031703070e032d0a02010c0b131707140c06090103090203030c01020406020f070e13060c120c0e24030105 68
    0x3041c0035411712441003807115030b00412092009846c07911800002445402c030500030314071504a0413804058040c043c021000000d1500c011505916044d809801e000c2091400f071004201d41c030659580c2c0401d51b500c5500042481c181c081040746c1030907055040c1c217001e071800b800d0000310b080c210b840b4640c0061480d2a14403420038000b0014500620076030f1080b50800c000f6048440d0703c149030ba0b0091500c070383c9010401072a450050a40044800041e140c4101a01a11000b140302c030942c07550521001c00405040b40010400180c2c00000d03104200c03d101c003c039808035140c40703041c01c1c41c10041c0300c40b00d07040c3d255032680041c0108505584610480d04000300908001030b0f11400762010038118050f65082500d00e501c0841c0000d200c136004500540300384408003e68a0242d280c64000c0046082503070b9840b001b400e036840c8036002984650024000040a003001001155103110101c240c80120821000003100d0310210b1281c1d041003022081400030543c010005c465503458407041d2408140b041c40d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712803534 1250 712802284 712802297
    0xc1602130e0d02030721051c0f0c05090f04020304140307030f0e030d210603061505190e060d081920071202130e030d06030209010f080c040b28081516 66
    0x11054051030032142d85c03840c9880c141c8104080c6908d95002840b9003145100002d0038484002400c40c884e0080303580960006050b41300307400340342d01400000d4200400c21622602c5072041d99580030001c001406c000c0b48030340e0380c038120080d40e0300c00107001b100c007038100d9402648458100318600d500010344a155482c20500003c50b000c80040c80400380c03680340d101078101440d080ca0b02c545890441c05c45002e9a13070a845201c0180c02100340b1a0b04100284035896910a1040c0841d1051410000f600d00c41802003140c07908103801400d14034080804030000d0303c0801d61440000040f4402c0c0d880301d215138810f0201510211313140c00701c1000e401c1d2038620024815003c4002d90302d000c10b1154488190740d4000000c41380c03a072402102440050805001c2644152000d400000d008030307000429506460200015100d00c62505003031001070303d507402c0d0071580140781310b00401d50612040007014a00040650302501c280c0f03441403803030070301e050254009078131032205081000c00e410b00940c903d5030700500d15011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712804784 1250 712803534 712803593
    0xc18050411040c1e1101180309031709180412020f12030910020a08040c080c060f090f04020a030207060506040b0609060a0e03030403120807080105090c1602130e0d020307 75
    0xc4890b0300c416130100414102d500c01100079550711940c05810701d520800208500e058800301104140d2850390003c000071105042400001c108501c14140c2009041070756081140d684001611559900c1c03201d401141c0540411090042e030144071315400519001501c0040e808100e525200c40d40224007203035000002007c030b08011010084582c00c080d038007030300b1500c8900590380104002c0040e1400d42ea000b8095001180c1c0300800300e0689120f19000b00701610340305040150283d65080101d03103560000140d441540c0356200d50005054440d000e070350050762134901707107049812650090b0446d80900d02e0070040311220740b904821200c5400c011281191a440445001c43e084003d101d0b01c1e0350107010210300001080b2900c080e250364240140c43d09046c603a0b03081000c50752040240700e5507034032a540c04081220f03041141c0040c1011464110b0680750801c1c00e0b000b080c042c942144410342d01d0b0380d860310910300448050001401d0040c89101640c079021003501e0342100d0002100340709440c080320a051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712806034 1250 712804784 712804787
    0x9010b16050a0b070e0a061107060e010e090901290f0918150a0e030a0f0f1b0803061f020d0f1e02010614040c050d0e030f070c18050411040c 62
    0x10b0340d00554815100744151900800c0100644240d80001d0700500300308101040182c0643d118540420742c510080806501d00b090407500c070b2119402d5281482030b0401d1080c2992150903aa62241512400200b121f07040740f400ea903a80000c10301c4196000e00005040c0c0780641c2c89100254440c48200c3e5840d400751100304001519011844d65450148034071141001280021a0550701c14270340f122040180c1c8801204064481c070814030000c001a03000f480e1741540c40e008d190002c4501d4564a080b01030014030003075400045440701025150b040d4003008101d824038010203440c0c004080b0b0004a404444c0544d8080d650300e2802c40310100b40705080e02903a0703845220704000c200d803050788100c15149048860000c0d0003454540100e0381035001d5600c035488942014001c0a0f11664150755042c6040c9140d60254001c01a40c3e01000c400d000c10444604200412000b070400c040c040c1031302d01d95051501e2680b41c8031081070880820072034140307020880442d9442d5541d0391010300654000c20700030380400d030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712807284 1250 712806034 712806043
    0xd03110f0c0108040b250314160c021306080102040906080d0201090201051608091005190906021e03090307151205010e01030f050f0105090318090c03041412120a0b09010b1605 77
    0x510000c0d46c880054070495a541c142c0182c88c10444c07a0a00c074007991100036282881807104660040450a018080300040c10100742c55021604034030400604135840e86162070a90384540c0c440806640c54240c00d128000c1c080c041c02c41c140380540000c010700016680003900c0d1b401040681c4440e190042c1c070003014480d071501111034910340100000110086000040d0940e004000c0c4040405280720840c1c80d00d60083c410351054880d180c005008560444038109000b180318003204249004c00e01680b04961000c010181c041c00c84500c00401151038070400800095080100842e09414000100221031412003e981520f8009070440d28407801d50a000c4d1a122108000317600540c40d02003000311282021019050712200b4a80301040000c0c64010003085410641e02c160b0380701d5040021800140500c9002800d01c1961402e6030000660b298034074941341c100c00c8440010032008020881d00181d5442408183c42c5c04442041c441e50609090340d0143c0030380340c0940c520500d0202401c0500c4070402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712808534 1250 712807284 712807321
    0x1a2e02030702101214042102030d06030807022707030b190f051c0503030a051b030103030302130608190c020703060617070b0a050d09020d020d03110f0c0108040b 71
    0x30596050440f0076400140b081d48100e0406540c40d00c0c080742c604030540c24880b81400f81d60440d841d8003c0381110b00c81906181241e0102e03c1c1588401c00c0140c902085d54000c000045000c0c7c0801ca444d1849401800b0003003a82c144400b0340c1e1a10300b81465042d1502c010065084025483d001801c1d0302e1030750120717201d45054092100e00e840d80241c0041e005503035900d1801502c1094a403078a54490020303142c4591407940d0780045c80c58005200249180b8055880594800a0101114007129081480b060140c4c030a80080e400243c00041e10799111181d40300303043c01400c440c544010035103410824402d035030300c0344c21042d000b40303849a04404800c0e10130000c03a0701464200100300300c1c84c0e030707908035400c044480a0f4168140d400389c610f00086403c0d8150a5a640445036112186040d2644e01c4610050107450012030f07101091562540c09602c0e00c0a10b200c004d407280e02d5602c0d442d12022110b503d000390700030580703d69500a000c03104103640e02100503500154445030b64015904ca98100c15850f5042c02c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712809784 1250 712808534 712808539
    0x6092d010f1a0102010b0a050f190b0a08010509010501020607030510080d1e030b0604090c0c061d070509060303040b0c01061203080a1109180405100f1a2e02030702 72
    0x880d000ea4160039603484040300701d02c071042090303441440c4001642a10100d50306182e100072940003c000c94200407404040225000300b0402441c0280000401d000744260000700d0b441c0400b254007402e00fa0814000c5024000495031043c056151500003551158000c0c400b504040d04c500c02b041604038841000f40203000141c00b42c0c0e0484242c406c0042000b0100b410402003034605001000b61103000c0e00c41e0503007005001c0d1500e07207084d0801140301e000d004040c00450400011000302d40105065109a40111070144000c2c11030000b201046842e0640580200780724910b00c101340700465030000201d80881e00c840c0041600c880300c0140f000e00520065001100c14940510074804040d88010311612501869004000310b0503004000380d85c070700840300d4517900500816014441004110761542d8013610030003c0355a2880361400240590355038121103003840707844215000110405a01031281c00318141c0d4020300b03005004000e215030002d102910001c0f100d070650b0b244040c51003401200c6040703801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712811034 1250 712809784 712809791
    0xf050702030a090e0c0712020c060706090b1e1311120303071202031504020705010906141006020c1011150c090103050901140106051602030609011d06092d01 69
    0x10480a52a5030100c0802d40009800c0b04001c6420401041250b00408148800074202985540c64600e80385440a1072000c2d44120341002a1a55800e0003c01c0580d10601300894050314510301150300c0c14024000040c141421840c1041e2000c0004849920251030300c0b01007a18180c0703003424a8807668400e01243c2001d150f92600e0b20340b07040000110301031015903864070140c1c41d0b8007062a040380030a07a103136035011004030180407135454190007400200e800f990001032100580da95980c11100424a040302d898181c07030400c11280c5184c240e420080650340040d045602c04480043d0206000218501c01e0000e0070031030400c600303800c0110b010009101c000390702072410714a585800360740221b20f10b140001e0612001801d000d1040c0241403603401c0100b9581d4181e404d00700181c4064200f41850b29400d20650320800141c1d40070005a030007460020000240341c1e01c0410b01c2c441f03060300d4094a09655100f101440200b900c00a00c1c1181c01d0b16030449401181d090801042c0c1d0f06102c1c1e44030003003079801d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712812284 1250 712811034 712811041
    0x110f0408010203062407080a03020c160302030d020d1e2c030613030804151e020d2d180b04050105070e101d1305100f09050118020d0f05 60
    0x1540154060113045071407007108541464082030305103114151002c0100c041c8412400a8071403006003110300300505001d801d20354452100c81c074064848002100701141d002041055050034003400380204000e101500241ea01500054100b40341d568640c0011040c4403565820144910406185018030546006896240c41c900d000c0501540b08410721134040d03c1e01050024000da0f0440030a264507844022035a502c80d21000c042c400048442041c1c142c4410010040700c01d901e0340c100b151440c142005850f611107842500c11611000084041c41000103400c00c90a001032956075020900c0d5803000c901c0020b400b11805c0c20702c118800c01000342c0640c9081c4010040190000c030b10410403a60b50500081d0b50600f00b25420300606052000701d5001c02448400d46601074141d04c100c84060a40f00002c41c42d034803074000701d030030807110390754010f074072600c28400703c40d2030021000204001c05003406154100320541030315240c10f000715401c4070740c00914228240d02a80000350b03e50901003040006d0b24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712813534 1250 712812284 712812299
    0x51803190501050105060712110a230708070b0f0a020c0411121f09090212030307080105130b03060c160609080903010e0303100b09010909060f210b0703110f04 70
    0x1900d4000441e180d50800c00089254207286050f2003910303030081c140791140c140104003942d00c01c04a417240c001c9030244030150400719801d541c0a0f1049022000c0446d0082c5000001d941418000e8000c1c02c00c6421040d020451208601c05071004100d04004d6569102049401030f0302d01002c40c01c0340e503040342c01c1c00c482d41c2c01d00c0804405003004001c4654002a5941c1340d24444036011070200040701400000901400000f50503401240a1803001c4c0c41700e00c0c00200380e60604c0c07071500100c0d1044d0008150800500284c101084211f03003441940d41c06028802413140065210781d00208010846680440d10160000f850f400303413020160450300412000010741000c0013981d00003c54180a50f0902c01406605440001120b11500e41201481072032414a412480715911001e80303141044540c40010485517810303c156802044d8401800d40528903046031740580015004a21030501e08601001002c514801b9159901414514002401c03402c0c1c00e416003901d010b19618802d048201150200314035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712814784 1250 712813534 712813573
    0xc1002070204180213110909040503030115020a080f092b030f0905030c0603060103150e040c060512062b08030a0f090203100e10090f0213051501051803 67
    0x181c001d4805208401c146000382c090881c62090084d040343c0c103c0250300b9028040e90204020441102c0794601e0004403000180d2040c00980b0107580230b03000040104981e41164100111415041c0041c101441d03868803204013034011001e110103468000500300190b990b82c1036403048080c151005064900b6001d00d4582d403c64030960044005c212640e5010720450300a03070b500303803c9510090090440c2044a0f0a00500d9080941518149911001010602140d01c56030202170700c10680c5009103440d1070b0034107101c0c0307441d07a500c20380c10306c03204002c00100d50f68581c1c4215031003d0140d45429034207a00c0c1e01104004660200c00c22074864800c41981f00f000200d00066000301c044170b00c2403080a00d201114412034446000095059016200c20710b01c85115070406034108502c40c081e9504410221084d005450140d0004c566a1000301c1100c02145031a545540300318181031400c000c2c525200740510380c84000107400038140310000c42c041040a280301c001d00c54900c0050b0554040010200c0c064019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712816034 1250 712814784 712814797
    0xb06030109020c06070e0f0409020d170705071d04020d141c03060b0a05040501080c07020d08190207360c020a05210306060d020c0d18050d020303031b0c1002 69
    0x34080c0101185c8894403404111684400040429045e1862070382000006d004040081303030804050006400400c2c1246240134400c1c5d070b050f82090395200395150181c1010502d0300040d45080e0b10420200f403480360b44406c00d0340b00d5410b841003503103644a0b090241d00310f00066100001e91191001180907010302144482480c0300366102440b83ca500c039041c2c2d40ba5030040b103400400240d1f0a0208014a601c160003135a040321a64100d1031500d2021740106100c4401c008041c0c0d4074401c0000e047ea845100000c04130f0241183d440908680f505210290030fa40e04607400420480c00f8070901030500070030315021442d0040101d20104114482140040c1d10f940300c0c0d210584081c001c41c4501e180c02d06210001c14a00010010418a1603a0b60320810015801c00610115800e0b800d10180c2080c9070100701450800203161554440600340c800307202d078034040541200340500401c03910580161400805d6a400000c8000700208503c082c045401d010b0159080c403007003030301c100c4401d04070503a8a58001c080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712817284 1250 712816034 712816057
    0xb0f12071a090303071e060e031c0e0d1211130503070e0103050309060f04030807110a050a05180a0b100801030203150f0a0c05190314090f030703030e010b0603010902 73
    0x102101d1819020a0702642500a815800410098000900d402e060581086400e40e181402c40415194401141ca4490300000c903940300145e005c244116a049001c017000b41c051041c08907910b0300c450f0688542e0400030180c2130060804440504103010f402c80783d090005038820b02c0e101c0e0000181c991200d03890b03100d028024002c5e0383c000306909140c140018180ca8000b8025890034038004240f09099011f00015003681005105c0403001500c071000030211075014921042c203010f081010000d5440315544100d2040840140401c85900d4140010f800e6044216031703081e041e92004c51500c0904110406d00b0f622046078520240c4040d000701d01d09050f40c0c001c0d011603590003030740701900a4110003664240c1709061194000b0740c04031019080030204100c6032904504203240b5454400111240c0d1030518040303a1212002c40110f0204541e081d406020351008101031004500c0154031307442511005010551160040d4450a40035080b00c03440340300207030040783c1c1c4c1d41e0b644607854020f4215998201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712818534 1250 712817284 712817309
    0x1518050c0f030a020307060c1a01060e09061c020d061104260307030c260c031b0307170f09090a1b020109020303030a091505070f080907030f060b0f1207 67
    0x6190b0500080c0031000325030240040051904000c010f40314851001401c07a10200101e00e000243c1c4110325220740280705503124001260038400810019a500400b41e5006004504140d000e0744210303c0f450704004d030140e840350b101e600039003011005414a0204601d08400016001a032440868400528104c0100101ca140c0c00804081500c2c0c3c401c2d5540070380012100388243d400300304a0440c1c41c070082c201c04010700000701c11003280f00703a80d00710110020194001080510341145100c4095411111a8001e0340c90003500340d403511400c0781e12025801c880400420840b080380b444804980c0701c010010301110013840c0543c070036000381c0400c0b441612034409030701c044c00d0024014040d50740c15681c0140614219038801035900000d1600080544010843e090b107020004154450640142e1040c0d960b003200510ba0742380900880320280c00c143c01680b042600f00040340071406541e05460b441030340880c6c5d1402100011742c1444482030496400391044410504c80140003030f405003100c00380c52900303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712819784 1250 712818534 712818559
    0x1206070e060c0d0e1003110f0a03151e080703150b1305040f030e09070f1110150602070f0b030a09210c0501050a0216141c0f080105040902030a1518050c 67
    0x49047e07852240f210110024140641880001e802c0040c0039504001d1500180c20744140da0400305524890f8014146041000075440118008004000103428110014240903145a40e4040841941c0412048844c0d40740c044040a40e500501c8143c0460480030622050420703040410350f40c143c450b0202c0c041100c1001070710840c02c1502d40303030f440b4a03016211081003448170142910f138141100405105405503540c0c0345031b0300300c5511035241c42741c5926010b1000d19003840340191810316a03412543c00000c1c405401c00200d03000c0d504480d400039844001080711515071134100684214208405c9502c1940b110601c030040d40704550303550050244000f4016502c0f54030006c000c9200f51591344015403084943c80d008521001d0003140240c0380d007000c85154500400e4040c0d14445c5180a940000348045001e010260707100c07124a02404003180c0401c40544c41da40001c1c0e0302c0d0200080101802c50200c25007032065821340c0501d4100181110311a245459031400780e8851004007000d03482880746a02c071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 712821034 1250 712819784 712819787
    0x60f2f030720010c050a0b0a0e01060b21010305061801230709060e0a0501030e3306030c0d0b090705040617101107151b0903111206070e060c0d0e10 65
    0xe03110098005e0081e0950f82207036250007145c844010303c030550b540d48540d00341c00e4002c400d200e00001000e4001c0d115032101410300c40042a00001404000318800c04c50050000c00c40c0410465004840c0d0105249924002e0313400c1c034003504503011210420780d941141030441d90180c410b454451180c6030307030b42ca5044d92108015910040c040d81d232140c100010250500195002e54880d00c01804070708211450300c0d01c2c66000300a00042018820480006041070849102c0e140d1040742e00106c00320050b110345840301020440c01d5104010140c102046d031004200c440000388140d502418002e04240001511201060640e004404803071055116150200c805e049180c8a240300e00c1c00441c3c0c1c40362800100b52a8a5100c5800580c180d20b0142e2340c55010301040e5401c030303034412880b8880d110000c619181d424440000300e40d00748454054451420a41113804000c01d034143d1004440c10540e44000a02021a1940c0a00c1c2c20442161052020302c0d075803d44c014000608500c8111005801d40c60503020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 712822284 1250 712821034 712821047
    0xb061b100f1d07080c040c18120b1024170c0301080d05030910020a090803040e060405090309010f0f2f0f0a03050409020901030b04090b04030207060f2f03072001 71
    0x1090300c41e8002075985c0788180313000e8005440d8403109141c8500603000401d0f035410086e80690029280b00007020101d42000000400d0350b500c000e47d4113440510510f0300c0159400311060100d41129900c021649075401405848001c22103407505105030020b2821100300d035495072003030103445800c1c800c1d0301c0c1c0300d00000d109200312446100d0481c0a0700f580341c00b4040c10400b9411503400b440510048640c0441c0400301040a00020300d011011061182002028082111400780041d80f0a80007005260072a1343c00c00741403a030b00301d80ba16001c078002c6000304007151900030490700c0c5400007540394071303680820451020030078403c00c4c82001c0d40e00104c50b820060380d5031500c0000c0107021070005e010400c2200c0280d8003030702d806c1c2810b0502046560500c00040e04031781c0c406000700c80c0c06c041601800103040e0f040000b01e001d00424101941c03000c01c0303248050055045200400100080243c000803046c255012425091981e102141e80302c2200d86400d1555a003021203030b0101804492221040358821074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 712823534 1250 712822284 712822289
    0x10b030c03190507030515072c090c04050301020d0b0f01020a050601060c05010212130b010b34020d1a130807030810170a0b0a0b061b100f1d07 63
    0x200182462100d0b021a4655010320100554a80c0900000003010031014808044c51040d403003011407261800c80c00c09007294032006420020b41a0b0310314280254425029002c8407010100d0340701e06c15a41c0e41559079840d2007950005c0d6019400880d4028030201d1541201d8801802202c9070140404810f0049980d984010400f0b48140d0125004020082c040c040b01c0342c07020300030740026282080401079802402426980d4081c5001c03401e560500b8803100c2c12250b070242840e125031510705501a0406c01c50202c05410447d25121881c000c8640c0c0100040300c11030069002d0f00581c01d8980b9070401000c0d8003440015001f03800d68050000d444013021500c4001160751140701c0c1d034100002510102d8800c00d00600352a480e00700002c0101d01605022050308071a61204014511001b81d842c0c0404440c00c098503207104141813040c00542540e540094070710b006101c00743c0c075913900f540689c107034034180741412094080c40c5021420200e50312207030400c1c09428400c800366070420300c0c185d00c940d981328483d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 712824784 1250 712823534 712823539
    0x80a030311090913050109050a0b0a15060f030c02150a0b090f01260a150617070305031605030d020d09020f0306060904020919061404061706010603020304230f010b030c 74
    0xe0002003000d2007880f812200240928000110420180d0f07500786007009c1c9040594070b01412004019a040c980d005075664685588040c0000928050005d49042240c420241c181511103000a00b41442048444003400680c02d0050003403c203410f04c14003c0940e110110302032203240d030003d0b0040342004a698100c40d0742c840c1342c150103890041400d0352008880300036140303401340da4a643c0c040f0f00c0c4a501d88070204c000c1071000401c5440d00310304030400d09403504808070301c0c0c000c0c00c0c040021910103c2500c1007141c1c1d1880c030002c5001d41c0c1c50041d0841c441c00e0000d0311194404611305544051a43c0806040b61090b07603040b000703025031410140d840e18112042c030390003c8944000340042c10807234031071500000003c1c3c0480800c0d4000c01e10f9420703105c144d003058040c10020080b002e05407402d03000380e100810413000041c005900601c08161903003414012801410b8000000c0b030100059480c40b0141c4140200f2000c4102e640c1121468032038102244010082d0308020303031000b4070710f0301003622043c02000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 712826034 1250 712824784 712824799
    0x4404060e0a0605090f18150306060a0501020a141f061e12150e0a0303090b0601080c0304030e0114180102070b0c0c010c02040e1e06010905101e0305010204080a03031109 74
    0xc1604000080c0c045c1618940c00810b806008501800e201c0c2546008040c114449140e005040d82850301e40180145064401c12001404000366600030458011654011144c012a044050b6025141c00d8019056401805140541320141c81d542e0307000005035102480b03115003c540c854a40d8481c20300780d0041043c2d80102c03100c0c1700c001070050248841183c010f0701020030201034a01d070341410310380c24141c00e9010039100c10b5010208005907414030343c00701090034086058102108a62070314000200000d00380130035001040b89aa008410a41362603200242155032440a4007000c24802c0b180304030315000d48103580010446c1d4100000b61003407444244010300b224201c0800458007618101030903600075980714203054004005002002e0820740040d80d40320000b994010383d5291900507807000481900d06014415a000c080b80c2c40030440d4100d468001c1124003001c2d00200c1291141e2004160398800180001e00010103d10044210701a1310200300700c0001a00da42483e00c900da81c8a0740c0800e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 712827284 1250 712826034 712826047
    0x60305060907030e0a0507121401050903070206030a0b0907031d010e2a04020708040302180712091103101e1505010315080f070513094404060e0a0605 66
    0x3c00d90001485000b22000c031224580580c440604051250304443d440da800e02024809000658000d541e9580c03a80303000b00690b2500034600e80d16030151190091003810004041848072502e6003040c400403000a080851a041000c030250040c8401031001251124181840f038043d0410300c1007051401160024250342a41d203010a061100d804044502c1160070f400911040e40300c92015005281c031489046540314218010440314161150010072030f500000c5c00c10482d183c0c800240b00102d030800303001142c00a41e52400f01c0607040d20380340d0030740c06100b841c0b250448842c40d40c0009001504084ca114000c0c002a14514260f90791a81d0801e211100840b040144c0c0d4480c1d400070518603207600c4012122a221002e05003001840c04140310030740e00941050049141c804030b44912185803a00411101c42c40355184015404140461700c0800c4200340d81c1c60314200d507050400c1c80300c2d062964a07a107410050380c01880c26007060103044000348008620716502c0c2007100c00c1e801540c8580d246c0d18240302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 712828534 1250 712827284 712827287
    0xf170601171f090905070b040b0d020304150504230a020904081e1215090405190611040e010e07050a0914010507140606011d1003020c2b09060305060907 67
    0x3440070b0911900040150403124414045200e66000f4001d5103801207900c140605041c0d240250076049100101d070704200410184502108844c40e0602109015889a5450808100d8003a502c0c0c5001140c504010402040107910740001c41c40c0c1c1e0021070304520741c00a000c1a81e60701d0304410340c000e41194071741011501040200020b0402c1c800540c0d403a580c890450008e0b20503e4000c41c520b070344140035050034081e02d03101951600d29070b5041558140090310f86620760b035540e210460444a4444d011030130000c18031909400c1618000b07848040c8a40d215522016250a80300920942001d0740010001c20301d2241314200b00c40a89005998076081c0394200380040c0340154204507100c1c1441070400600c800035841400752580c01120314081d040c6854100005042c2c2807119020500c1d0800e10b040140e126641c0301d00d003101c0c03103604d45001a100d80c00d244c01946400c0c11500c0400114480140707a5480441d0400300d40d0402c40f803a59020382c2030380c0c0e485040c0d069070b4090741c80c0d03540041d071034000400b200d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 712829784 1250 712828534 712828577
    0x30114070e06250f0311060606070816020a0b0d110c0a032a030e1011060c13090504060e1504030e01050304050307060c111501031a1305030a0f170601 66
    0x2100c04400603814994084042e0340ea101d400c050860721000009121390070f05800c010300255030490100a04203600d005c80001d6210301c2500c5000740105030210301202c100303603402c000c401071581c06881101c40316202c0c82c0d0300c80541c20125810000302e0030245804d030002e030044181e54040842c00001c10399440c081e50b0640710011442d803010b940d0311014120100c803000c0707241c1484406010751581d40f050012074090202940c2c10b0b904400510105110f02200005c00007612988808414400b5444480c61212012074400950100300442d0070101130000340909903000d2484d42e06004110b540ca3300d204010484109001c41d000390206a45038080001035010750015030380980301e94140d80c5803002c199151022a0000e582c41000101d491000c0d6811620401c040d080d0f1f80f480c41c0c90300c40c081d8950366a0140c2031940103d44150b018410004c5800c1166009001c0450341c1d01a0580c0e49903c2c103050002c00442450700c0f000c001842c400e07003030759286500180b5079002e02c0381070b0344120300e1074203a060084c0320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 712831034 1250 712829784 712829797
    0x4060618020f1206131a040c020d09150e0307031109010608090601030b0a020c160312030e0304050409020118141c030f0e0627041b09060c0c05100e030114070e06 71
    0xc1000c0c5050b030081700d0b44941360f20217410412485211241400f80000c8034441f0f030070901903500400d0003102194000a5180c02c4485507031110244014829040f42c00301100304181d50503220305a0040100180300c1090740d50700b0350690794030340aa1f0369a902102d28070000d50300c40780507070008001071004c241c2c10094140d00030012040940b400c64802d502c03510b0003041140d000d0900e040400103100b0840008841c0d20108040d24051000380f80d10b40d0441d440b88228805e030740c41740ba9502c0c018411a40100850110310302082e20180d00d00307039103650b0741c0550781c041d0108610406d5420984104602d460300200f104503056540d1910346990710b1401c2c1c2d84082c041025070351280050102040c142c80c260550824012500128044101c103e0240b100f81c0f0780386c40c038103000c3c1e490b01c40b004c00540d540041c1140846586240c000e5800700c50341040d085280080d0445908007820f0b8030b007181600c3d0000c61041e003034103041e8001c109491002038143d848103801d495141c001080c00390ba203100f0f403401c0c00140c0071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 712832284 1250 712831034 712831039
    0x507050f0f030714070501020a09142d040608100e0d0807050d0b03030307020f060c0c0a0b071101050f1501031a0409080c0f0a03022a13020d0504060618020f1206 71
    0x4c501c0c004000380c1403150003661084030643c0d000200303045c5441d03011415800608210404401142003500042d6078406c0c500e15000030100034507081c0070003003140200c2c2416003101800410065456030001c42e02c2e650780c1c2c4009068142451500510100c000070358601c40c00051b656000039840d405411a12030780311b201440f0301e207502e4020554550750705200035405444507030003e065020381e0344c4d119402d00d08000c101c400400814400804c4030040460041c944503880502091159121401500e031102c03001000d440b03941c44c00d001c00a46540154482c0d01034500281800385080a83c001141075840110038500200d0194822122904054100c1e640d038038410441c0c0c2c2d08003a508225030340b6080e1420920403a60b40030700080320502da010300034084500550340803056001151580d1102003d034598072540500c640400c494080541541514402c0550302003d210504040c103091010b00070502071140f180040340414200341c00540708840b16040381205160034142091500540954000c1c038543c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 712833534 1250 712832284 712832297
    0x50d08030604150603050a06120b01061103160606050f0603090c1905060c010b01081305070501050a05370f090b070206040b1b010b0603041a1005031e010507050f0f0307 74
    0x3000c004403401c6110244c8901e940004040c60148046010380e01c9079403101c404600c0300c00c1d40c100842d841d021014199005410066980c010724005a4594801c407140c00d0600c0b008441c5110400445810240849a003100c0108a500f911001c015242c07009032000039a5038064400d07450641403010a40f01170310092202c1d0850349a594000c2142e03036121800b0403079180d6440800308525a0000c0000d078000a6407002c80842c0300d000d85d503190342e410841c010361f0f05100d40131540d020658419012201844801046401d1100c2c0c1c0f0f41142c41403240c401c0c12040e03009041030b05404139521601c4094244282999031010017880e0503105102a8401601680c12507800c210106030044120f0007000d030722010418021000146c030f0700490071910710311400e40c1300701c0c010428400821507160031615122000c000d5004148c42c0e4001c000d002c035440b94009901070203501420100003910050710f0700405d865500a101c169507092044a05100b090001d00039014188504001402c0e010003461303111100e4103104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 712834784 1250 712833534 712833551
    0x712081e12390c010207030302030a06170a06090602040b0c0a05010e1617031b07080d08070804020402030603070e130201170112080c0316110f01020c130b0d1208040318050d08030604 80
    0x1405c0ea032000030241c0100340c000041c07114482140c4144001000c4019003420840085c007849c0780c80f4184510b0103003e5548902d0300038288501d80e81246c000b070403c0151150b481342076030903c0d51110318848050311554a821421100c0a00215058081c2c200b05600082520b04000c415100d040200c0f4001c0518441803100d81070540c2c80200040328111910000c3c4840b030b1500100d54a03243e04950164204184c03030b030030720078660341010380550000d0381101c002da140d98900740864a003001d25030100c240018072009004100d0b20001101c1d8a5a000b070f6102c0c05c0d80300e108a03140a40380403c0c400c802c2100072200d400c1d0f01240200c006420b03080700000940745030554440f40303041200400a010f46400d02d251400105920302007140710403811003800a40051910030000524142c5e118080070046529401d07084200e58401c00454010f075400074035114001010440100f001c0300c12141240801c07a444040200c02c001d4010100c2102c40041200305011415566422590400f03021740e07400645800c0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 712836034 1250 712834784 712834807
    0x9060b03060a0917212809110d02040905100510090b15030c1605100c020c090619120b09010c05120601030b1503040609120e030712081e1239 62
    0x121b00403421031880d10f440510f07200702d201c0341c5008040800300c1c85250201040025160510a800102c0c0c11100710300c003a18a0300104000d4500c680c801170190160240c901900901544018055800e8101103006181c440000000b03e84030070a180340e12851a281407280306070808020b5034028025030120b81002c1c03040d540c4038203051011504a81e6608080011035214a03184101ea42d82c0d0b48910084c540c40c00382002050245c00058040c82c01114010490a82144030079100001800d8080360480c5c008a24240402841801d9030703140b6107542481e500d0000140304000355a840703c00000724540544400c001500282031501106400149412148011038010405184030394000c03400811406041c0c5048058101900b42240501c680c00e180c41060f62400140c09094852450724852108558184140503015031091034400d01c0050010b0a031181d0718402400c000c140078444c203160741d102c1455006448041340030301d81241240280c445000e00051044000301180c0b0502036181c50000001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 712837284 1250 712836034 712836097
    0x20601091a1503040303151d04021513050a0f03050303010b13090603050f010b01180b07110a0609140105072409122609060123030109060b03060a0917 66
    0x3004003080b5800b01c204003d043d00b44c000e40200703505c803040e0050072901340f0003401c00044a03541d03d100c0d146050400101151a0084c07001100c10340302d100d1584413461014000201406805403034042d090591002a4522413180c2c98029070b0707405006141141e00b004040304035034100644044400782c0300c000004047d183d5128800155001344050010040b5207040d040c2074a221005460402001040082031451400703040f805446000400542c0c5400504021950811550714a54008040e032000145a90800c04042c111480b0b102940a08130002c401134030302e8041e07103c0c081c00071104680501200480d2554040c58044003540c00035000080f40c5030a14103007541c1c1c030703d00d01241c0c1e181586200050240d6200e518111214140301d074510f819403100340c4500e01072060181403181d070001c41ca90409040f41d518502c0754064001c100b094441c2c24400042e2440c010002e00070300920002c603c1840701405284080b41d0810710680700d816102d445410700f90700a9441d0140700040700e03149484800c0302203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 712838534 1250 712837284 712837309
    0x11206060b161a1006140706110a120615210c050d060f1208130b03040b01030c060219110a1805060f0d151a030303090d110706020601091a 61
    0x1c0c1c2e600b0040440c0d281241400f0144000c2c65000b81004080109214210b12040d09654261905003601b0030884071160280c092410300800c00c604090a055103140c503c405008045442c0e41d80801c00b51844418004550250041c81001c1c1140b0000b001d00c13a0103030042000f8000c080800c0c8072008035000702c0c0412200ba00c1c3e00400001d000040b03803d443c1039540a000060301e000718040c9160361800304020301d50ba03e0101d00420424000c00c1c140068952201d004c0c0c014081c0b800069a2032070145410100508240011908100b0000c07011070076510010342c800e0340c088000c04003c3c4002140d06c0d17980309444001c14959101c80c07400340c0400c3d0b0151401404400040320140411141040c404024502081c12041400350107090030642c003040f036400c60711030f00706103240e03000841c4240801e0b803000d032200110b00c0581510002040c0300e001c0c0c20029440c0c142c20103664500c40158001500140c881a10307209400040c1e1186005100d4041036a024a0a0040a41d50880441400c0c40031450114001c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 712839784 1250 712838534 712838557
    0x70f051c06080d0f09031407030b0c0a0306140303030711010b030d0309120302093d02030c0f0303090d110102130803130501050f18030a0506010807140303070b011206060b 75
    0x78030042141510030468040010701a0604001108203540d00415002c4d40c1c0c840984048010714084801c144144814000ba54200d1203012051804842c0c5200d1680b145120100081c40c0150000303000201540508260400401840c81c580342c5060860341c01000400112003950b03515a240360595042050211185258401082e9a2014109160300501150744801814010449810a90b50307202c52a841d030280b070000141d206505080703000d0004849c200b240a0528251680601140c00101a108030412003007222482441c41d0003058590000341d41d0766489a102e140101c1160b40142e549100255005c03000505006007a040420b5032403069101c110365400000e402000007560a500c130010f404e080c20a60f10300414855490140c0c441c0c82d04030b01e984041d49151820a54042c407a0302c4030b66801c0000c035240c0796103900c40142c5034141071064110440703c0d00c0e5440041d00300801501c1010307800907102c082782d82c649264a41994001c910454900c2e55652005c9900d05210010b4101d01008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 712841034 1250 712839784 712839791
    0xb07030e03011409070501020114061c06020d05010b25151d2b0207080703170d110319050405061f030b0103030509090121080a0302040e16021c08070f051c 68
    0x40c06c0001e802c449a003144502d00c40c0c04a01002b50742e803a00c030140140000200c01c4c200c0c0030041402c180c1e009001d888501c0c0030890910300000750180364140640400a07120101180d04500a8402d001c605c0c1042001002d0011a0b440c0c480c400e0440c0e40010340d400705003003130311404004582c0898145900300c8003280c2d9001041003203098602c0110785540007480e040c0014880c40703003040c1d2203541c0d171007051000034000040080403075501c106000941f4104404000c0c1400301109414460007942c000f1103042e545401b922a07a500c001d07d560003407074020f0b50450f01401440d21014000c0d881d14001c0940c0d940c402915481c000005100042c8040c02140241d8800707484200150400c1104181a031100031030f12000d00720304003641c5500c800c081aaa50040000c4e94508414030240c010f80030300e070f200f0340703100c0c0d15102046982d4040d243c0c01103414040350700355409800f0000b2600758044103401c08200043c500000504528040c0f0442c292900c09800c25500300507488a24202100c2d1015045610a84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 712842284 1250 712841034 712841039
    0xf0d0f0c09080f03070f0606050907030c0210140105100c1208011a070515060f030304170d080c0a03020c0a021309123b040501030b04031403010b07030e0301140907 72
    0x148400a20003a02e0520b01400c01a42e10340e1000307640b40111700c400341010081d18401c508203c0c0e282c1c080d0703000b444040c00050040c506018050010f061008903c0094090114041c2c25042a4820f0145012890321006205d1b420101072180c85c0384445111418051030001c64004201d0b4980801d112220503035540b480da40c180300c8003413140c80c1e40e20807401c0940028404040001e4000c00c100c00140712000a0824039030302e200004041c002e104a410350107020009010414010303281c070442d01002060116441101c442104a50740442110030f546c0401061020600c3c6a04ca90028072140a0703c004540340c40685400003107a03c5441a1410300603560384d40300700c00308422100b43c0205114a4241060100804940d039078041c0701d10540c0c942a800c05844d0f03e04000c0f802d07602c8510000024100300800d685a10f0400b0103104281d40980104400d0311048030400c10a030222070507101c08080103810b10040b80d03001e442034492844a1903240d52103600c000142c102e81c4c12100d204010500081843c5032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 712843534 1250 712842284 712842287
    0x30c1203040c0801110901030203060301060e2a071a040f0c0f0602100e0606011808030c0f06010b040501020c0d06090f05101823071d060a080a020f060f0d0f0c 70
    0xa0041e03110700c0f216418060080820101082074501950f020309015079070fa901c00c00003900410042d040892040c0140003400715602855103c402000a9105103911001c00030444c4606030103038003402030200c03100c0c062483c01031107526035403031700248a0141c20588402d25603900c3c44400c502c0e040040c0000c100c4108202041e8100142c0910817000e007020891040b600e00c000c4c4d110300b00204500d0510500d01103000300005a450010300410354007040c1c03511130b510b103102c3c81c1e00c50748041d000c0c0070329126460010404100c00011902100c1c0160024607000c8600000d0000c0b05451001c00d80b80c1c0340d03941e406030020484003000b03540d1503440740000e082002e002d000c00804943ca00c444000c48146000040800210055055480da000b040000380224500d0805113140032070030780203025409000c04140c0c4110104000507402001c00b114109065510b13014910b079200d0f100200a94400054882d06803a0b00b000d80081c00078400101560385018805c140310030507030b0724907140314100a90301d402001105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 712844784 1250 712843534 712843553
    0x3070c020f040b011d1201110405090609090703150e160e010f30050708010506130504050d0f020f1b120102070f0b1005091e0c09010903060b03030c120304 68
    0x40e004075410040501d107040000c00c0400d582c4c0c000f070f00c4099402d00c0c000140c0d589025041b00d503001d10009004822906610325010b81040c41070901845002c0d001c00e41518120030128841e07081e10000f07103a1a450764a030800c15082c1e104801343c0ba1642c414003100100e9091022024260f10050303600311940c9400b09004c1d140c1c3c0160310290500d28100720900c01c8001c070f40082c644101404001c240d000d8901046112202c08040d801030203441101000907140b141074110600c90300d021104038485081b4081290309840b0200c400401c60f4000203c810170090086141d403c29110074411900c61000058503a880c22410a883d01d1200c501c0040941c010714104c0071050202c51020020b500307180745942e410a02485801c4000c00c1401d90000062058208141410003000010300c1e0403024200101811002d611000001c01e081360700c41700040100c001d03803084501c0c42070182d650000c0320b072940c1c6807003004100115580d035260104015806100d0010413558480001030110035030740e41000d1400300c581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 712846034 1250 712844784 712844809
    0x1204230322060e150409020c06010314010c0e040e0708070801060801050603070e041518060c030c0810060c15112802030a0305060301090f03180501031a10090b03070c02 74
    0x7030009040184191903000d818409007400a41d1501001985240d490585000b42e401541c03c01c0d20102d01790f41c440d50b00052450480703004400c141c15001d42441c00900743e0b0110302203803010170211520a01e40e410503900c10504502400c080d01d605585650300541884816400040303241e44420041c460008203220341900710208800403d42d05290050002074603400400190000d00060059190344025400994803c040c2d0482a0140e8070f40c0e1410500070180303001c2c80300c0041d2038500120003040c000c10300c090083c00e0404403004081d1605d80304880c129005941110400301d00174249102d264280a03607070041c00c844c8641a120f07600000c0300c5003180c44810010705c1c801002914645100d40200c216120304c00540740109003503981d040403a01404040900418501c0328090701000c0c150310942a0081c0e03883c40480c014401c0c3d40d003004405445900c54240340102500340c480b610380ca80300c04400c24001e024200150f08950303030700ca00d1400390002c4982801003041d2218584c21271078100c201c0b000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 712847284 1250 712846034 712846087
    0x41a01120249051506123103091404051b03090a050f0106080c060304081c0e030a030f0e070503060105060a0207030c030807022d0d02062502120703020612042303 71
    0xd00c403070300f08201d61640380600f1024120031504080d20080a6100b1003000c40320a201d144c54203603807d4540105104054403583c5210341544903200422314182c05800e0007010800c2030f160310444d069a00c41c2090b07101a05030185441480600d000080c8140103198003403c0c0100005111442c154005007400507800701584104000c004210000d00e943d815101c04a440b54040490b1072043d81c0c1c80c000903c501c80c5610f42500c40880c213061b005501d07402c00ca00410204405211031044503e00c5a601c0e180380c01050307816000307000140514105100234028501c0766104903000540c0d00c1d107818090b40031032307041a622144005648020340c1040c0818040746210301b1035032200e40b4500020b000405500d0710036244282c1c4880c10010a544e035404c183e488011554550001c990559055542c1140d62510101d0041c464006100340c0c081000c00e0310801c03641c02800d100c1c684400e180e8010362030b4400610460700b08403000c940c14500740606180303030604004500210790b548511008490305102c030124212 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 712848534 1250 712847284 712847287
    0x1a060306010f0f05090d14010608010605030a03051809010b0c060f1b1c0c020304080705040506060f070609060c0e011b111905041a01120249051506 65
    0x40d40d0340c0c0030310304614050341c0e490800920401004111054840d14100c44e0b8040c15504001c414085240089805a81e480000300001555002d1003030a0b179080c0c7c07158580c190409401c0c000403900800081c42c1c440b400c103520b04042c1c5590000101d84140a80200781d0300d0001080894002c10b0801c00d01d9000b503900c005001135440d044403083c1c4008040040390113440d102007042100142c4a03003050b6028030040e0030a11400120a01c001d54a8209200c0c52303045225500c0002114241442068051400070f002d0070303d41108046400d40d181d12801040740d20030307561080304010401502c10f0420011869880c50140e00c401c0c0b0004103c44030030225103d981680315180740010700401c542d505e0100c8140d884004005801102c034052902550005411a00b00807001c2d518400c540040041c40000742c813080441b14003060300204901495000b46088000348040c1c20354074060b0150407000c90703072450103040706082c8148000600c04812084010540e1035109211400f240c100e4840300c003545c1514102d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 712849784 1250 712848534 712848541
    0xc010b10080c09060c10060e07020d050408060c0306121630031b1b1e0b0a03090c0330051c021e0a02160504110d111c1a0603 55
    0x2d49520074812900d2140000003242156900d013486040c0700d40c1040c01c030800c03005544840c14603108408407440300060080c5c5105940c0b46018a007502d041d59591002000c440e07498441034101540302800c0c40b40d105420a04001101e6003c01801510542c24400007017818a0403010312200640e0340074500102c0c807000302e00380350001100c180518540d0145001d0030701c1e210f40c2c00450400901100090140c2920050303600400c035013460f01c101241d0b07007020360840d0749091603a46200e4460380d010b96034101c201040b1896046100740c10488049000e080c3e00c0c3e040d540c0c0c980d24102940300060118200c2c1146081d60107650b2807107002c15540d8410760605a183c03140030704255540d41c1c541e10310180c520b503010078540e1044012300b07242000d191005e0300d030036038400c100a8065503079915800c8230740b0414041880829581024041da40c208400e4141c0903061020255101002e4408810360b01225502800700346404500940701c0150b007606c203200015040302038824202e4608001d0982d81c0100001c2043c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 712851034 1250 712849784 712849801
    0xc03050a030f0f06120203160e0424050f04030e0a0f091802031f05010f0b0901050a030e0303010609060908060c0f030a2009010f020d091512020c010b1008 68
    0x464014180070724000420303800c100a020000d216601c0f05441e4035280007030204445001c0685212201c0c001c030101c988506109520030240310190040e101c12100c244080b40004500c0083d0604c40c0c5504c1e1a6148601c1e0703420581411603108480100400e8801c406020a05822298040d4080c8041d07583e500d545050007440395113580c045c0f00d10000035a603482441c84200c3c1348251600d07200e50041c2138458882c0700c17808500d50880b2000d1001956840c003000044d03401440d00c10750045554170210305003466208001505e0a800c451145014980c075008030100100c1d050000718043c081e585c0f0b6400351582080c100824108407070b00034205951201c014804403000040035520310300c05d02d0003801d40c0ca03a01d45c091800034145d80c44040c69003040e01c5d80d035085050405009000750f00d000780ea52540850202e0403c1b640c90380c4900516020480703105007070050720f03100a4030380100845410600300c0d0710011000711040303030300c015002c000a0b590740900240520380300b49040000405da180c004002d04001c0396 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 712852284 1250 712851034 712851037
    0x41101110708070b1318050601111b21010516030f11090607020a090c03020318191e0209040804031106130e0a09060e0c01080a090b060d050304080714030606010c0305 73
    0xe5020903100405ca001c0340d4550003c81c80d000e050300902403080004040409005400160740d4240802c0001081c020b021600094200518800c06041c541c020385d0b04007070014014950080145108159240e460b01031000d000300c50054041c80b86280d0b0f989a2200028111101300800e40403043c2045100108109401e040d6000244201c038070503a50f10291000502521066100c010202e083c03194810f035664042d80039521500031954501d0981c2510303501941c4a40a11200040340d0307400c075101c0d4010503101114110440084603000780c1082c0c56400080703c81c81c1c101e41c2241e0700100054280108581a2401040c4620a5030201d05044a1041301c0d82101c0b200e00400c213902c205c250024040a165802c0805025000345c0d0400840e510345030b6940d201d400d840c0c59103001c0b40c0b003000842c2e00c0480911034080f96036007110311500305440702d40030031081950140301540c5030320061001146506013406143d00a2204000d8019a95615002e050800600500640c1484000210000480e40050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 712853534 1250 712852284 712852289
    0x70b1f030515060406030b01080d0315060818030f0f0c010605040b03060c1e19080f1308090a0e07020f070506070818130c020106050406090e0a0212030702060304110111070807 77
    0x4440e02d030700b9681e200124006000c41e034006421148050000502c0400200d880c0d110720b0a030b0360b010b00c50b0139444c400c1401c110714a0300c9a107001a04071000030340c40048468505c024120340909481c40c0c0307600400240301581003c40c0e00038099000041d080c0408100348a800c000b00400c1d9800d00c82803011400003911004001c01c4000c0103038000412302d009046086198509452026800340c07152000c4171203c017084101c200341408102d0840205a0340e507020b03408644107090310a0b01d012207001075511604a9007003c000035411820400b800700714204c5c0c0140d0517200f502d05900070019a9111200702c0c0c90141a0790295000f81420007000d40400d2a40d0100ca440c1503d0510034920354031540b01007072104082412200030b0303e18105824101b10340c10f402160465000322003e0280980b15a0303003408031102500c01034090761064170a80d00504180b01c0c07200382c561112054034200419600070031041d07402101c0407100000c002448601e10340c2c0101c0c620301d030881100001d2111a0400c0809031f40d036003850 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 712854784 1250 712853534 712853563
    0x90f1404031103070b1501031a0a0501120912030e10061203030b010c050d03020c0d030b0310090314160614090a0b0c0f04080601090c140f031902070b1f0305 69
    0x1c40e640c0e20102c40c20803c4511066100000c07050354503082416240040c0d1000006002074145424801e040c0519610800150001001c03542c20500d4240151402046245d40e00505500c1e12815008503003440c0d090250140161804511700e0584071040c0d0800484034030100c01e2918028040c8061081c1c0210f040c102981401c00141d100441e00040e142050300000007001c0740f0074a031403440700942c1074000d040c10040d200c040361400c0011754002d030180c800c0920090380680c0f0141e500c5e186180076800004101c2d005c0d08020000340400c5051010b107510003840c400f2100c05081c20001001103610a000f03455000c1c0700242098140300c10150303212924100c024006240070408960343d030107000221003001c01c0344107426944d259180c0f200b03902c0754024031503103a410b0720306800001300307600880602c0d803d0610502494640000c04c1d00c151141c0d00042e1040400707c04c04800345d02151403170320090510500504c0c01c0701161604201c100301c0f280302a8101d2031105450790080001410000d00002c612444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 712856034 1250 712854784 712854797
    0x1204030501140c03061509040504050f0607031829010914130b0f0606040b13050a050303040312030e030d11030a05010b0412080c0a020a030c060212040b030106110c100306090f140403 80
    0x3c9007006c2e03013113016941c85941e0003807800091000700600012440e840380703072980c1034481c00d54424000340e0840b55841680b41400001103d141c0000318134810006200420b5500c04010001c041e00580c0910000d81008000550300d94a6131102007030781c0c4219620442e5170850351400c080b596a00d0301c2101c006014240e20b002604c0c0482d0741c2d0303994041940c0c0507114082480341c85141c100780340c0907091120300c0b41c540200504403001c96141808006c55081e240c10110350010b5400001003140104141003c001ca41c6c0001d004c1e0340004e4460340104403028807a6241c003603da042034122503007220b0044e030100704802d10800c01044091814000c1e02c44454002141c0c51701c0d10010740c0124102002200300950062a607800801040507181884090710256400c82d981da007082c03128103c2c1c0d44200e0068107610602440100180c41c0b154488610501403401036811146070140450b820242403070004020949903030090181c2c03407070340c450440b80c0040100c0500446c0e4039206103460300c04020f007015080005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 712857284 1250 712856034 712856059
    0x110a3c051e13020307030b18070509131e060810050403120c0c0c031a150310111b031c090b01050f0a0f0f091407020d0e0307081204030501140c0306 65
    0xc50700d015100d20250b1110543d528503041038014020803181c20b4151240d034100941c0c0c843d20040d2015180314565036211107140c6180c0104101005045074440311500340c540ea518000e0340038403082c0d04407900c900c00000c24000d0400e00c030641006c0742c10305400001841c0404000104e503103c0d1a10b141c00c01500f400040300c200c180d80458000030341200c060140c80e100c960000c00c0180c2c0081c00300c81c02c21202e0541303040d0348998150f949840c2d0000c07102985507100c4510007940e03054030344c04900004808400741746081d0700051440c0000e40741c018140c1c52a00041010421142c54204035003083d400854104041c420507903800f02d060781c060094078010042001807000070740320514004003411501c1844410142d6800f401c445040080c0500410203041540b400494000080e10b10b00444082c0c000d002d000101804c21540145003a05007641b500c600e0f440002c04803024405159040c0700d5210196031942141002407d480e0340d203040b012545840c40400c03051441c44026250404c50407100c6109550 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 712858534 1250 712857284 712857289
    0x6231b0309160b040e0c16080a050d051302040c0e0d110301021e182d01050d0212010e0907060203040e07140c0a02210307110a3c051e 59
    0x2000d621806014480502e00442c2c0030301c1c1140600100c0d0080035052032130381d44520609480f07015100b02d0851301f02c400d2400c0000902340c1d2004e0308480540340b4003103050a21034001c00c01611015200e19403114455007442096080c41e0040c0901c02c012130404030000122100402d407005008100a800b055034803e04880c0ca40d4207404503404001f11131840020716407880c0f07410056520028503c03c0a0952148001d40ca0030a40031640c001e0001c04580c05900501ea8504000c0300501808241002400c10080242c0c4559101030450310705c1410544c1d0302136040135540c1c151000c001c1d10142c01d642c05000e0400003aa40041214143d45249c2003407012174850b410290764070b03500c0d0014201076000102e08480e03078040002e40341c410103000b1150703181900d02d5000038004442c00d20f07901c103860b038104022401c0803800c00600c5a10b2232801511149100340d0342d541515044640003a40c59402c04040c1d520765817005543c070544810f110360740c40c8814403440e040c002200011106030070000180c000c601802140d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 712859784 1250 712858534 712858543
    0x16031802060304030908010e0610090218090109290604120f0b0a051914070315031a180303070f0e120615151305042706231b0309 57
    0x156000e08610749a00f42031030043c1c086080c41c06298444d600c2d1940070001400e00103141ca0045a0041c0c0101e00e050420420401030740c069a10480800e001d095100010340b620030b0040d000b0211650001b400868080c1c1c5070b0403810114004040f8400c030903110501907a03030310007224100c0310246a004051b416618004200c0d6041c520701410121311a0700300706020302d1340c0d08840d20401c040e105070030302d00d8982000e1504592668600b40c80c40d1003c8800a0040f0340a540321344144402c07205124510366170380d40c1d11004080c810903400700c0d010106003403042c01088900c0c55601019614040c50944c40c0c103035001031941d20000003040401c00d285a000141d522803122080121460505481b001c0c902202650b40c4030004c2406103000740200d6001000c40703400c0350b0075142e90100c2607046092182c540030800024107602031401c59400428050050060000303007000d40c000d4451a404251315440f02c41070003050a0242d0f072004002e20450030000000d907546040b17240039128040c41038032915001d9407039190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 712861034 1250 712859784 712859831
    0x1829010e010e040507180501050a060f0206010e1902190906170406021812073f03050909040c0306060504020301030201053103050313170607052d211603 67
    0x20455580440c100349558007c0340c1038840545102a02d079a45280441c1c94200718121100103070000e0005106201c840c44a4940101c50404c81d0610702c00c1107084041280d21584907842c05001c00c800d8042010303001040b85000b03190342c2c24244132034410040c0d84050100004c100a00d000d46c00645080560348000c0006e003e00c030b0103011070b000150203080d8199506c1e014001c4510815140c030b0520403030712308900040440211403031010290010054407001200c803889044082c003406010780c41d80b503114250000c0c4120f000d10103441c00240395042040444030150000d030301881c010401880580d820404982054900848001c42c6400c1c91415109100c001580c0100400070b1003400070038080c00001074080d00083c1000d90b8002c030341d2240001c0c030f0f6410b070710b0301101c00341c00a100141c1a00c1c02000645100c8101c450391481001c0100020101d0301203000800070043c4020503902d43d8248002d4004c1d4140d440042101200c2c2002002841150060301c0c02100705522600320845001040703030b40144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 712862284 1250 712861034 712861049
    0x5010e030d0503091509033402010c1106070515130c120309030605013201020703020114040e01061e090e0a0b040e01020a030c110c090c0c011829010e010e040507 71
    0x81424a19480e40c7ca940c08170113040c40c200c1034207000030001613030031a04501082c0c00d0b1200203c04240381d401950100c54640c01552200381a55207442103407515401000014031070300c0074008540d00c001d0034400301c540103405a02e000034480c1101d000a016004150305691880d15041200a014030f003c80d1901025000106020f090400000b2802c60750401d0b1030500f220070484940c4203000c190341c889145c807011b00c4540107034402013080004d54042c01c2d481c4000007a46c00c690746002c3c2c0f140d44a40b110740007a4014000030300340d59203144c45d25501c10b60105040720039160460100d490f1400101101d400540418015076450440b0441c50341c1d00d60004144040c040300130b54840c43c824a0203801415419000008500c030b04240c8044043c0202c0d05120041c0000d10a90040e100c1c14100100b41e0400001c1c22040d41d81c540340c4104c4070600003200300c03040780700d0014451750000300c88010452130421542030400351042d8005104680321180f1442c1581c02d5420000099540c50030700ca80b600d10703117510807074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 712863534 1250 712862284 712862323
    0x1c090507090e0106060507080d05072d08091605040e03070204090f0201140a0c0b0c1b1c050c1b03030f160b0705030618070e1005040801050105010e030d050309 70
    0x40c0e0011242c110504201c0090020010a561490151142d01c18217000030f0a02034100240d000d0b4410350390240b80c01414a01d0104078a0030b212610841003114000d0211a0000c0c01582e031604550001d0703250313840a011405008281507050b15144010b00a0086610a5032589152118081b081003520240b540041c014000306420f420304641c4000a10001d90008429140d030019014a1804648688001d5620b074550390b8240c0d2240c000d010005402e625050004100c0c084442c55891516851500c01c03202412015201c40c904856500c44440207205122052061803a0a140442ca190b1113804980540e5a29544100004e0851040540c40841d4000110308558a404040e9505481ca88124a0300147d42c544a0064030f45000481d0b0f40c03a400081c00c9118460031200d455566080315050800e43c0c441d0307803c3c0000800990300c40c00e046000510104003000918424011980101400e0030250b00c031501880109481d00702c1d00007000180f100001c04901882c904001080b080c081441c0c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 712864784 1250 712863534 712863539
    0xb340c031202272b0f060c0f080f07140306030709020325020102041809020d0804350309150d02190e01080601120c0306180b090906010302061c090507 66
    0x2101c84012900000811000c3d1002d25501ca040c10180d0a410080400b4281c00d040d070401002c07145007002c1e4030100c9655000d1242000043c0560140050202580c0c81c0d1110102d032088004040d03010083c58685403d903120207126189812035160116401c0b03041d650340d5207a40304000721b03180044641c044a1610f10001c100407400d07400030f1132100d400d40201804015503410034012800c0c2d005034020724005060303010380e031404460f4035407000d404180f0243c403d6400680d1518cc0854079041580000440e000304e501d400000d10521620741c0e030a0010041c1e01510401c1460080c0e0340c0c0c015011454041d4032104040301203040500e00b03442c281041000190358900c1c03c00341c40e01c02400591407000116521600b0340c443c540c003e0030410322030700c4182e440d1214652402c5000e00031380000803040e400e01da56401c0c04204052903030383c2c030035145030080c8021854094050500c901e2940060400e50a9000480180010398400f801c8441e00980648a4400da07221044000001c04814038002c060344a8107000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 712866034 1250 712864784 712864807
    0x509040b060a080105150a140a030b090403091a070818010210060303020703023d1205130b1e040305181201090c05030d0203040e0907120b340c031202 66
    0x506068038000d50300554200100d40380005107020f4007c100010038100c800454550080c240582264503c0d0324001ca45540050301240da40c0d002650140d001800020040c821014160307508602d29103808074040c0740003aa5201c4022500481e100c14620123204e00c40681c0e11383c42080300500d00c00d44039108202c015901c2c5806075032400140f104a004442841d10500e00b0b00031181800f281100543e2540100b80b0841001f030840c040c586030324420b1244000135520a000540315203486200e02624180171304105080001081d40000d04034400d15201c0140010310303a450403825608550305090054603400d000c0503800310303510700a1a1541081943c1241c540451054105082c890300038284c0407031082d150000d042d1034550f07007140e201c050391041004004040089000e19401040341094032181c2d519018810040504183c040d103102c8403190a200701c0c20031568600301002d500007034484600b8010102120014400060101800251041c08042c14050082c1100040c554101103584403d540340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 712867284 1250 712866034 712866047
    0x306031a15010e010f0e010302040b040e011d1303180510201902090c09220605010318060f1e06030c0b0c12030705040801020a030501031b150509040b060a 68
    0x700028850030710950790420354096105000c0005060756034070030041d4005002d5640c410307040c480031b04040c0d0802c0300054007480407014002402c2e100704240d9665240401e110000000078030310081045500013841003100580d680714101c0c07641400d14842c148840c000004511001d64021600003101501c5a903400d40d1103030107035005a420060505074a41c0c605c48081d9100e040080f0160b228040d00c100d90094a030140741103500040002d0401e18104404011402c00e80c4004032035604403854600004100c000c500135030019040a2804002d52141c8440c4112203044d50360700a004660350b207000c2103010405820980304e4143c50b140c040300141d25140346100900061000380d5820345032100100b80304000c803040b10144800280100a91a0000c4641c0e5072540060030200501c4802c2100155004d000c0c00035100380c040c15140004c1545c914180900343c444d81c5000306011002d0740006100303070361001304124860f0350700386802d980314501c0c0008030b4001d051414a50360f02607000709403104207503807106 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 712868534 1250 712867284 712867291
    0x1330906080a060302030606060903160e09071406040603090515041b081c180e191d0a12030b0402030f06040e060405030a0305040f0f05070f0b0a0509100306031a 71
    0x35241d4405030b46120b150801c0701c01c9408001d50540003900841d05919043e80a4196014018240c504070701208101078003454590344590501c01a5008000d46018240041c00c002c100001c007011344545480d00180381c502c5940910414160740d0800c030000e00c1005c02c40100003014404004540c2d013413504003095090b5903c0d50f0290001402840801c003885d011405076510007a0602d101208055080309989000c0141342031030b5a0001c40e00b0000d000d100c840025030092104030310390101c80d4001071885040e58181c012040703041e07039104e080820400000030542c80b1203030402e0007024040c0440408401030812405103591240c00031050103280b00b00c403c01c0c940245022101005450351a00784d00b5180c00d000c0b14003410f0b5410600c000001e45009401071a41300707100d641e18065800b003641c2d03484603400ca040c60540740c3d41e0103e0418400301c4101c5880b480074104010b200e505242030614002c00c0b912903c6175050244906040c6840b019000e50000c40245070301c040c0241d0100c550061000e60040d044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 712869784 1250 712868534 712868537
    0x50313030c09020a0e060903010b0d11040513021f02010e0f101b050409020f071709013015090903050c0c06040b040302220204080706020c03070e01330906 68
    0x703000c0081c0040e624801c0360020803050b110300003004120410840d4580200c00000d03019501d440ca00800c0d65660b001c180d010a2060324040390100c0618140011203600408602840064410081c00343e40c924184068030f51f940c0203041c4041580c940224050320100000408512600600404003400070450013031411a141d010030020f00300c00e08110700c00b00d5007281800031400c00c000c144045010754005040c00c806440050f403038151241e6844c4040b420b0308620050880740443d40d1550303580d00c203000c0b000034088807400e882c041142503010480c415078030880400369030f03036106200748020352040c0c01d80040004e000100264807443c10043c00c5a03000e12044a5240102d00e4682014036000090300c081c0d5042481060801d070a55092041c188031804141c83d8000100392101d5100c3d105000a00240030301c80041c1103403518040340a0316000104500324802e8104400c2405884084400d150444800c14002910300c80c1d4814103c074503858080c25414110b1021540f46901600030090b070b41142c065 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 712871034 1250 712869784 712869803
    0x6030414010e0f0f2808120a0618090809011b0b0a02070b011e1208120c0a09050303030f1f03080d021b010b100503060411030a0c0305070f140a050705031303 69
    0xc4c4011030f482c1e4207215441c00990040d2040c0e43c1c82240d4442c2860001e5200c0c040f0b0528050101e044a1000001102d0ba4004140c65900a010200400e40007482d8502e0106007880392030703429982c1c0500c5000b0240b900f410014402c43e103501d00311490400c000313540d40142d14140720f410300003440d0029500c5180240da00c00190b200002da0700542a14000065840324885441c69040c10202d00140e0460001924100f10500290803982000d440720340c081c103030400fa5140d80303c1e10384001411640b0076a000500c03070780040c0b0400840c9800c2d04c050139880710801c81c6400a461200c1c80300c1c0300c912a641c0000e0801c50700841c044843c166554003e04900303060800c2050703191180742045080e90441515690801c1c0003c0e142c010791806078004d1500090020808a485a040c20b20044030303410031103c4100641e1209200f000c41901407140907000fa0161031719040551705903a02030405d9004940c1c0d601c05180008071016540d100d80f0961301c90036400001c5d81c2d600d4030900e941f000161072078041618075440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 712872284 1250 712871034 712871053
    0x207020a0f06020307080a140a03150503070e01050f01031d03030103170702030a060b0f04091a0a050112030c020d140f1e1504060e01060305030d0608120906030414010e0f 75
    0x603211160708803012a0700441c90000581d07152038164100310700c0c45060048094200e5501e954100c060701c20840d0b40d54000840400d41882e48600e00c480d41c2c411402504658414010014102c04440c1034882c191a00c034013649401c80103d006001c03180d00c100f4a0303a4207404d25031664a01000841c1224000d103074216092843c0409940d985c0301f00d50300250300d54410480480052101e800039074000c0001050118801640c40105058640b980c4040701c1030001030162868010b010034030340d500904d050382c0030801581030010108204144102c060144a00e0311141411965101c00203080381d2ba02040502d507194040615941e500e284840070300c003501232080d58a04c2001c5520b038211a1150640081a4040f500140c908080c0d10141c030640710261106100100030600340152401903120744011540c450000107008112030107604018429001182c02081c591251021345140341c0c0110f078119660307229032500c10341c02d10784007500528550800d03c0c100b59000300890b4402a68000100b90389619a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 712873534 1250 712872284 712872299
    0x1180203070c120c05070f08010510030f020108150a0308070203011b020c120a0210050307021603020108071b0512091201150b0f2107110c0a06030b0418060207020a 72
    0x104480c0000010000c188550103d6007215005203510150f0408082c1a651901c40c1420212960400910144000c1c02000700d03900901c00c2d50352064407003240000e118115a241c1a0303100f03060701c0103410030000704c020907082c1c041d410708200b040d20700034040c8403400e5803480e205210b40c2114205a205e541303811520852190b15156800b2130003025030181008500785010001c00d000e448400e85158400c0804002c01621042c840100c06541d82d22115200c3c980300c00001d00e8658907040b401540504103404000503600100356907004111808c01000c01a5091059103e07410150300182c01c5105120101201102a80080014003000c0e6002c000340070301c1c03030743c25400e072a10691100b1254010b07100c20007007821448041c0c2002005124064604a0003410001d604010007106c4031101041906115101d80c0020f080e984564112020348808034072000003522041141c8541002c1c90344070003680d1a03690f00c0f98099004280c2e030844803103040395135082010080d00454008c0303024102520000c00d402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 712874784 1250 712873534 712873537
    0x80a030f0513210f080915040e0703020d091e03030b040207110d02060c07060306080606090f181915060e01080307030509030c0411070219060c1106040518011802 71
    0x304403080082041440e190b503030f00389000244004480c0340e0002200c0d0000490341901007440c130f400703103403000d8131144614200021000c5041d08000c556004000c02c1104803071840c460740d031080d501e0500580720a01040300d107000d000c1c44500240003010b000c07054000ea4401c00b140c0f1840700d00940e0b081040700503082c2404200e00c124000582002920303a021802c80c541682c1a008070361016021506105400040501c0c01d0519006080401e4458a040c0b00d182410810f45610813011120380580341090007400d0589030001d400e894071600303459500300f2918000c004252701c0d0101040c0480704898941810343c40701c404541c0c054603045c10648001000b0f00441002d41c1a521170401640c6801203d680554169005140c01c60305801118200600c980d1f4510540e64902451150316980e601103104000400054058a00004e452048280002c5611103034000c1c0060303210700c0001c48034241100040c0300c3c0c000c9a112552211800d0714140d00c0c0c410302c0050904031180713026129500c40d440c0c81e00c0006ea = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 712876034 1250 712874784 712874797
    0x50a061817030a0e1b04151d011404090309032636012109050703060b100309230708011a0a0b070f0201260108030306031005010e2a0301080a030f05 65
    0x144100c050080f025461b10794490100c0401100801c2c500e11f6840b422401100150032004586048000c0104094000808100c000f10011a02004030b070070340740d0303014101c85501d00001c0d0000c402c0c1c07400c05604011110901800e181c9115000b500e60700144000c80462154801c00141f4420090b44005c440e8003040e20b4016140d01611098001344018134030519210102800800d0541c5074045400490000d0003074201843c059600420070080c0c0c0818490b1040c1000031a50030075140029007030107c0e48140000542142d5078905084208003070742164540391898200c00c01e59413800c406030000d05c02c0850006030700c54054550101c2140c0d00d40d0b1950003402404800f03880c64000d10440341c01503100780c1d000b45411000d01d201180c0d2494006940b000760300309810044603030f40000240b09142c13a00f00aa00345030160204144415070414a98808948000d0b150074036600e2201103036903900843e0882c40b070990350801c4050340c03039607919070403181c0c0e81c008482c0c00d80c0855040c0d4482c119081c8140200d03000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 712877284 1250 712876034 712876063
    0x801050603070807020a1406060406241209050610031e050d0806120d180b0705070b0705011d07050a0b1219060801020a050301050301110403050a061817030a0e 70
    0x1c550300d0030b40944a03100001d040310704501540161000040003507400140303a0420b2401000c40d0314000080c0409c42e8810f4000244c070300315400d0100e200d8a8000c050004030f235020314103039800001428424001d031440c40c50045c12806003100700200e82d99502d1600c01117078007884446048030701102d80855203400d03e1102802079004041a910014001c0400361380016010740504a80d01d880c1c14100e040c01c24510442000528200f00401c0b00a00c615585001d4030100502d0b80c50004107656150713841181d031151202c105404a120710900500790303c61460060a901401d01c62482c3d8611903803100024080c1d244100d0740d03c070020030209280030a841c8603141c071460003180c940310000301c01e8200f08204414461280c5850022400840a0018007207032540c1e40c0301c0c0387d00e95040100f0503007135820319212105030b21402d000401c040341c00061522009600000002000042500800724580045401900c1c1c1c01000603141400d81c4503d0055110740390380b81e403c01c030f14028030600d25101e80d0484c04412 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 712878534 1250 712877284 712877287
    0x10501050a1e050f070302030a11070506041217041d0a0c0c0b0603011d0102090406050904080324030105011d0703090c0512031603090e09012309010905010906020a030b0108010506 79
    0x4000700311168036560088203e007019420100031002c070308038079071011100b140160408148075003103c1d0021f042148090420010740f0341036050101240c03a038011842543ea0101c160845d80c0140540140380010400401d1045c0da80c4980364408503e942104284008030f500942e80014503920325442411280c880e032755107801d40184d440e29a140c000d074001e403030317241c2c15503035001c2c0c010316182002c0c01038099000f45400540c44200200401c02101c02c0c40c0e02a60040488004200010703203203008984c0e004906e0b00007003081881414042500e404118403641c0c0561800001040800c8901c1ca108014244034081510710742d00e1580c00c03030a956448134020700755401100d051042e840c004101103002000e800460b420300761418072450300d14904075025000310b040501e040c00601140ea80c0c8650054400000303000d03110800b288080c100d031040c0001d200c1c2c0e0f007044c0d01154003101d082d0098000243c101d0020302040c40d0a0402c00700952000402a010038030707000c1036150a5024440460480784000c0c4a40e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 712879784 1250 712878534 712878557
    0x60507140f030708061f08010617010e0604051b1309060b0c1b1207030809101b0305160209150f1005030a02160f0804181803111f090b010501050a 64
    0xc2e07404113400f0b0010ba40c410014030802c5d1080402c00d00301034020b402da65901d0401d5140103c00741c8a041e00350703d01030140303041000600c1480c40d10fa42c120742041050b64001401d40e120300345040d61220910785440a040d00150402aa1447da40080d00752006c030312040000d181c2e0f40c0b021900600c9034910742c1c1540d070040290500b1644801040010280e40500300003002e00c46841c59505280e40e85d001103400100104071514142422070090031003981904102d011600c1c085080c00518441000050400000094082c0d0030b804150111025590146c01d5400d40d04140810060800070070301060300034818250111840d282101c41e20301c01e2043c80c0c03203261468884001ca00f0180d407004056101c2c1201c0c0c00b0b1b0900020310030050f40e4036241d00a4894945076410040303860800d140b0940d0f03100321a41422070701080d100264000e0016142c0c94107145c1008013859800e6402c0854a859000c0a040c114004000e4001140c00620000307100d86072101c000da803a600192804e01072410072000241c40713107a0f131 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 712881034 1250 712879784 712879787
    0xc03060c030a060b281407150c0306050a150302070b1305010b06160209060a030c0b030702060604230414010203010b12061c0f0f06181e020627040207060507140f0307 73
    0x140c1450900500e0301502031040c2e08246c1d8065480003000700c0c1d4180100b640448504510301c150104216189810f021003803822000070865106401181c91140181c2100300416004c0d904881c3c609a100408030500c0c0f0700884190342403803c041042c3c40c2942004218100d91a00400326014444155440e00f000072481d000d006840300300814040e00541d60200110215a91200c041c1c01002e006998640d01d180851009007400b40150540e0701860911014100035080c1c005052482c2c10005401555550766082011040c4001c001502d6a0751000001180d000114401404802c030300a9079180d44c0c0c0c80751014407a19440107040c0c80464001c0000600010b01d00b0f8030072254840c042d5129803040c1800e074031158103c07800da0113240c1072101180c0c107040402c0407499148009101d8070004c03004429564000c1407180c030489041c1c03c200e001210481c01c6082c02d44070b1184d4600f20246c400c544440d258036012005010075070300e00010a403050503090003a4120070032582610034000d02035045032a00e240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 712882284 1250 712881034 712881097
    0x30c06051303080c060403110109150c180f05041d071a070512072f040c09030f05010c140316030f110c0622030903020d050c03060c030a060b 62
    0x81c060890200c00c0e5001000c201e010000e00395641481c4007a202a04142c64040c0a0400c03a02c0740151590401c4c5102000c2110304280c1e4001e107031140d01c041900a840301c4c084411b8000c00031600c0d041d00c041c103804554002c01031444020344409a030b081081458405c8060f4644072100c1141000f0b0b80300c2cac0301c18440c210514112501d0003815103080d0381040c4031545c3e1279080070304200c2100103114002c00d40b881884081803040244503d9800d0805203054140301d6404130015621456028507101c14458400a1050405c00300031500030805801d942c82038600140a087c4130030a4000140002000b01c2030640000210b0b4060360344040742d004044002c01060300641481003035800e0499483c590810320b207170200e0042880589d064082c210614044803285080310704c826010800d0f0030008004800241c1028140050380c0c2c0484103903c0d02140d9240061814504d52009a050701031441484810110b110145006000c0c21205001d800e80384e10181c8124002d020484580c2b2210b20100100d5149054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 712883534 1250 712882284 712882297
    0x10302060d270309050604060203161e06050f06040c0927050c090a060201060b0d0e0703050d0507030816120507031b02150f1303050a0203070c090506031501030c0605 73
    0x90000c150814610000211070408020b81c011250900a010081540c02030b9040080d08003160000d00702420850000d41d01e0164507501c0c002c12020388442c80501401c1c6030010403201240780c8202004041c3d2400030007410055a034484d820443c8004900c05240c0740c00b5503000c0761823555808440500d080345d260302803592584e402309201c4c1d807401c42103200d4545002d40c030303c1441c861313406a50f00d42140042c404980032682c409002c591404e1381c148500c10400307044518400e85040081000c0d000f08191500784030071540014903900c196070300d500d000343d00040a4482d1502076241e0b8500d680e1082c05032038a400c480481070000071810203110450380000c0c1d002c56080080391400040c8e0b43c1409400840c851401e00e007050260740528001000c9a2500a03080e5000c00321804a20352802c000e05010703419460b21070010180100414101a010b2003041915040d45d0800b8800d6491a80e5585010041c8010f4504500034011603522000e41c2944100783c90403a6806420b10101a00e014421105da13080032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 712884784 1250 712883534 712883557
    0x30105030a0f030306081b101706060d0e030403062301061b0615030b090705012a020112020706091109060d02010e3001180f0f0611030906011707030b01030206 70
    0xb0240450759040402c92194801030584018035025543c0c4100000d070b6140c04130b5001004270400641c540d85030000e950301d42003642502e503035840b41203240640e0007030420900441501c1c400842c002041c400603401400225005c0128015101d518403505024240d0034042d40f0085042c0303c8410300c07210314403541d241c00c040c000c0000040c0c1a09400e00201c2c000580e50051f54050700074010302201071030900008000f444d013401e04000701441c8e02503400d0f01105501602c1041c200710001c560540e40601c010104558000100315a02c40c054a00503000b4604140c064a0b82e6140031790003600e90030803004203401b402c00203046121343d03a280e42c011a00b00c91034034491508003501c08810701650310381600e00310f0340102d0707003c400301825070321002c1500b1103601201169804c070442869501249141d40b00040303d5801408000c0030410034103080016100c01e81051140010020030442c01480100c0c0c084c0c182c442c0205601c000c1c5801620881e948c030700f01c3c0005010141144c00400041c50103d00815410005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 712886034 1250 712884784 712884791
    0x120301031a1e1902030403032c06130302010e0a03030e162706090213091104061713290105060301140f030109061b0f0f08070c023c0402030105030a0f0303 68
    0x1015410f01a170704166000c9001c02d8031214130306401c4c00140c003c006d80c14030301400312400b002411041a03540c171015000500800d455581001854801e4201c4280e160440040702c400c09624900240209075140c40e8082c0c6000c0d19a81d030200e420206107040840f800e22050a80385105e126585e5a24010707080c203120707420354070100041c241e0114000b60410034075034001c10f8840744c50300205809490074164442c4000c00b04000600c103858012034001042240f20090b4082d581d161070080515503c070b0003026100000c0a0484002292100030101c219102c100d0307002116681c0c1c0d024050f0a000078007603524410101007030311070541040000700842182c02800807030070180307030b0f120041115000c1c48085080385008040e101100d8100801d4043c0070b0244c42c102c2c40010008600510b07600c0064030f090208100c450703686041d50364012510f0b40b920a601c0003128485109001244803092a1001c1c0c0030030050150441890301d003920176079048400c090044e08003c1403c1d960134203240e1201e0400c5051564 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 712887284 1250 712886034 712886071
    0xf04020d1506110c0603070807050a030b0a150e0307260304090e01021207020a050303060103091a07030218030109050d031116030203180306100e09070305120301031a1e 74
    0x20798220002c0000da00c5114181c1021a0203d0030401400800c9001311020802e0046203984500b1140c0d1106c540d01d0032a480d00b90110040303015240203102031b40d10000d001c074007103405901d145374145810742c5525200c01c1c1c45159000d1613140c24040c81219400045100310f05c143c0001403020f0b010301c2010b801a1380c9003680764030f008011075194100e440007981d4080b80360040b00c40782c1c407403040d002031650000f072000400540d912a0b40c4c0c0710080c1036030304040e00c6e039641c003080140c4049540c9046102c030842803c10300e032015004000350003015440c5c89174442c021031402241418420600d41e250400301900110001d08000e4014001c001a000308001c3d0402c00622a004041c910169241c442d42c080c40e540c210420301c011006842038441d40c03082c3c0065060240e15814800c503002282c64120850441d41c0d1034164442c10441c069201810702d00070301083e10102da1500300114142e07882010282d410034400704001c0c4600b20101c40c0d0b00b900350b082a070104030811107192500d501003400ea800b0680200f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 712888534 1250 712887284 712887311
    0x190e010b0301020c1b011b02041d01050f04031d130b010c0203031602040b1f030e03090a080609190302070b030a0609060e0601110c1309060f06181a0f04020d 69
    0x20b00070400d6a0064000e001450f401e81c1c140d005c0071041460918040d07401b8402c01110701c0001c128036200a03c25540c407141007018044030901108459481c0001300b0291a240c1c928459020741290b0880005040b500d11046042c4040381910070410007516600c50300c0c400c400b85070001d00140703003580d051003182d60310000181e071708000070200d614088124414100f182d1061101760390002d4900c1d84030303405180c448414140050f98424600f80c1c01d2070041344a082d9001024294800c515a11f500b02d031410001054024000803503a0040c000c1c0d008841403011301c100c4201121003442e01c0200140c000340340c1003180c00d440b00082d40e04950041000642c6656803560002100e1495100c8107003200101d040060b1581c11211a4290001410151060400c0440001c10341920a4000074055903240702c410248401a400446e07080300d0150104080c03616000b00010344002600903040550500500001c1c0c001c3c51241c640c603644018180c1c64441401404002c040e420000d4001c020a51b200524100340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 712889784 1250 712888534 712888537
    0x30606040e0307021c0c120605060603130204200415080f06010915090f060305400311010c0201091209060e270f07090902040b07140f010614010e030105190e010b030102 74
    0x201407c417070300c0301c1009142ca80042581d40003010980304140078810031001400360160b190780c1903812035000880c3c0350840c001081840181c000c071400d044010401007080450070a4000005007240c0350100c0036980e111000801076000c59805d80040c20222040081a0007078010948000039414144132050b1200300c49a89c41109620000010340c641d0140318100906d035034500e070844602c6d0320341c032000d802240f50b03c81e584880c100e04800d81b00e440090035041c584124080d03048200040001d2203002000f9600034082c10496605881000007010484517590244440804451607520b95042c03101c078038810440803185041c4080f403000c160b82500d161a18002c810030b4030030140d15010040c01d08191400402646032a08082800d034030400c010f101e640c0810065800681c2e00c6940900d40340004c004070f900b0310000e500024817640c02d0550103c1c503090501d00480c00a042a03030f40c00c4c082140c0380d04141c2130728002d0710303100003458003c824a55110140e400101207144101d002103200c07201c280110f401c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 712891034 1250 712889784 712889789
    0x30c03081c0510060906050c0615040e1b0103181110120c020106060e030f030409020c071a0901080606090d020103090203071e0302270c0a0c06140402030606040e0307021c0c 76
    0x43e203104406000c2c898102002c1c001a140d0703490054103002d5003142c07c940d103190217041c205402007421a0700c43c1d1035603690032158094200f0801d231460600a0308501400c4800c5c0301d0098082030500c0002072414004c44006c0c83c155400100001d4001d40c403030b0500c208005941e44000402196040d8104560310303074001d21224040c1c503070000410b146494001010f0344008031240e0300c07035007166000f546411000801d44d0140c913104100180e40c0d420b01c849403031526172143e0004900008480701d00d00c00c11926030152076034034000e0b01e0300c1d1800e64905041104611600b4001c961154207049200090752090f48144202031018040314242515100f1083d8000440c4030201c21030f039025481801182058640700e0b8803a03881004520722241e10602142411400030f1405080c2d0001082146040344114400316080b500000d0070403400300d420100d00007804c82290180c7c001d01c101804a80203040622868540311b035010051350526015134204009075410f00003010900410f1180ea00205c4e4011500200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 712892284 1250 712891034 712891051
    0xf0c0213050114100f0903140c040c02030c06010b040f03151e0903020c2707270302120705030d0507020402070b15030d0c081b010e011b021204030c03081c05 69
    0x11003e0781d042041e004c0f000c440050800c000e08a40006094203c0100320589900100503410620300b04082c2e0710780580600303600d0f802410201488641030b0080001e01215494200b550304a030380790300043c4282c3c0716070700c0f03070785071488810740108003185040d001448009040040420b144180a03040076103071072400d09400c1215940e900344000c00d60100804482034005455000780c1c1e0000c0d05102500700001b0341480900c40d1440b0004070130600c95000420324001490b881c010550700c3e100d03400e00030303843c9010890050035148400384504000150b840203c0300010000e20361f0f0303c8211822201c1e5044001c040ba0403a03020b00000300001c02003118a485907107880b4044900300c4e8a0810149001c10307038905002400064491100440d0622044415035250310442c01c14100080d1115030040610310703555100e5501c0e0400c0c0303c1d0080e02021002540340b60301d41c200c0e04422411400d5004901c10303848000d00420a0034000c00000d8a404050300c02825408200f91346040714505040070748400f02d62a40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 712893534 1250 712892284 712892309
    0x70f1e0c06090c15080103020f0105091201020403051b06120c0f0c060f390a0c060504050a0605100506030412140304030e19030503340b090c01020c010f0c02130501 72
    0x410242d080c281004e01ca401e01c1d045502d54556008110b410900101c03281c1007000025004031140c85a21201c88245540b20086545a5990a240f41c5030700d119040c42da00c070224000c00c404186001000da5007240041248a1080c0d1940c141242490713014040720007030b040701880000d204400a0110511070344400c00c50541c00d2400e0008061400d0210500c07441d160956600f1460600c041c0c0c500b1690b483c240c01c00a40d8948400c030701a00d00102d4031a0040c1080d04100c100810400c000c200210054812942844291103070000c0340803501b06405240d4003c0300c14800580881c070b032403074404402003035803e200311591103520701c1c041558002c54054010036054414600f440c2044030221181158003140490114155550242c07248140c2101c15101d2802c9a40d0125075140503210781c03104404240404060340c45441c00c0e00c098241254000c0444c010300b2040841c650004c65801043c19050755946084000494280c0344c66440020590f00b1141009a1034111402803256601a00300f210f5080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 712894784 1250 712893534 712893539
    0x2b020708450307051207150e060406020307060c1b03200303010807080c040603020607030e032e140702060601081f060302040e070c08090d0203010219030501030506070f1e0c06090c 79
    0x180f07441034a80c030542c0102652240d2414020001c02c03d40e0607036001c070341e00280345c1041400c11500801ca5100f01588a540090700013402c0c2c1e0004002d019451242000380710040510001786c3e031810b410030031060341c0c000c07180362600020710070404240302d03200000450658050215034985141c03c01d030012031070fa034400c010510045500b08210504454202c60500c142d0341075a010480074012120b0041c180001c0e80004640c0340d03014002c0c12000168040700c000341140010f820b1507000306081c5c0e1010701034900300c0303d82c25000c0b4450b003c5104002940040405498820044804000003000100159080d225201c5280302c1c0c5148540101160341e000741c0c58900b443c2c3c0c4a942d04001a10210030f01080c881801c0000b0307180b40651380c21103400c03203500c5030710407041c00440c1c0a0f102e0800c1550100d9190700a541c40c0a0300355000506a9028800300c41c080d684206059880c000d004d94900e020a1540300c0000d03241d0400710054442c84400d2811078140f840350340d200020b50360100c0f001c035074600700084103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 712896034 1250 712894784 712894789
    0x108060603150c0a05090102102f030c040b070807170d0609020901020d0f022416090803030a1508100e0c010f0507120c02062b02070845 60
    0x40ca940001c0e503000030300203414207200700f084030300c0741810030070a101001c5036203042a0b00a004011402903480001c0c03180440303050b40c4c5021100c002140030104801c0c0004640741c00501c105407072107144082c4520b85090b081c80311001e000c2e0405c68080300d42a0003000400c0c00195940303004402c4414009000d42c40d0b030007403486203095031202d801850009105000016103682d0018541c411200c05042042c40b1003c116812400c09841078440c0700482c0d8184003080c0003011441005124a00540c00c9800c80b81e0f00b40701c110780c04440d9204485260b40180041398241d080c40e840f40140300010203060a40075661004075041500d200c2620b100980d842c0e40d203019200c412320184405d00c0c024604009000f40c04003010b04140241c0c0c00c0501240803601d07081020034080c2450b04a02030700107011640b140b8001c407401e40070320107858130340700170507200d0007500c260304c040c1c0c0242e1300324030b0740401c01505006000c15940700703c0b03804500c000c40c40c072030040c0c03000300c0c00440026500784c1428a814001c464a40c6109 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 712897284 1250 712896034 712896043
    0x240d05010806070e0306190f18110306090607030216140f0d0801060c080d060b030405160905060108010b0904060302040e030d0605030a05151305150403020c010305010b1902150108060603 82
    0x48050204012144e0440d80d408241c03a5801414981c400071181e980417059001015401503040206207800c845004a4a40654140c0403902c00c8843e99060f1620f203003410340320030b000e44929500754060400b0034600b034002e4010300500c0501c8080c0850051a54075038851300954040041081d4029144120b49142d0501041c24480203034200202554980100180100e001c4c560140141e003002c5080481349203a600500c000304054400a912414107050054940012201d00070301180c0c42c00d000200b030120b80c0076003841500140c4a8196031303072030b0521a0489500101c40c25500656444000c00140e5640c464144100c102030011a00e40180d20b0f290b00441e43d0341c0c0c1101d84240d010509a500042000840c2a2001d00510340140f03142c44000308620b50044500f00140580925015803c6050210091510590180c1d007182c1c0d18803840e00054085880a0042e10300780c100800950044980c03841050200c444148103ca02c0c1080c400b0001c200c2ca442a0000c046c150880418045603280400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 712898534 1250 712897284 712897291
    0xa1706030a03050405040e03040e0c120708010803040b0705150c04171b040c20030706060b030411240f0304020f0603090307030318050a0507090f0204080606240d05010806 75
    0x1401040c50720381d50384024065004a02c5454850307034444c201070350310200500c1900c008154030084405a03090207907a010b400c2d04400c200010f0960718030002402184a210510f040720410301c055850a420040098119071080c803090310503110346890fa21140a4140b403c1c0e1180400e03a102d1134956041205845420000c0c4414030300d071390b00c43c3e00032110b00c0520180751032001604a0b00051100c45461090746c0291208120402c3c0c003810008280380c00001100612503144640402c018940e00c07003071b8400b0300340000c0ea0041e00720483e4403c0b800359418104007011480c21210001c0c0d2503540f1640460195a100f0750380303105e0140001c001e1104500b0001a881c1c520307042103039414114901040303001d599006464020b4100f5407940d81166115800410965619410a099514a0b10796050460303075484903200d0740078110301e071084c0c5900380c070081e00c01d036030a8449035009042d10341c03204803c0041d91034264600c02c18003485044a0b440a6004d480203200140c1c0b01c20380400d00e0f42c500420641450b0004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712899784 1250 712898534 712898539
    0x92f0f060f1c0608160506130b04080d0801170d030e0712150609140a090206120a23070c14010612051b011e0c110901081b0a080715020c03030a1706 65
    0x1c410b00d2a02c1442020818103503a8140c400984464584851086a23501c80c0c2c005c58944400280200342801e0200f00e86030690700a844540050f40d070340048044040314015200c1d100d03040600c00b08101c5120341c101010300400403040f2114251680e4546041d40d400560403240010143c03006403011915000e502c005113000c040402c0a9181c2c1d20079500380c030342c0043c056010aa40c80c1424406c541d514000d9030260002014920040e25145800c01c004040c419018002e00d11901a0800c0c0c9115000e030070361040c1d0082d541c500c240745880d520b0655524001c601d0b008a5501e8200101d42408008082c0620070b01800007004034007000403c1c2d030420f00081c1c0c81c582c1000884115500030055400319103007040c01c240b070405408a0281032000c01c1c60054001e856001106a0000a00c0c01000600a1402a01c056058a050054802c10035107183c140320b548515001400c0800c42051485000b810052031070040e1004154018000f90841c0d100114490206100071850365400b22400112030388107806 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712901034 1250 712899784 712899793
    0x2010e100f12051b16060f020702031608030a0e04060e070207031505040503040e09010902041401080c09130201030c1b06060e0705070b0c03150307030501092f0f060f1c0608 76
    0x1001c200e0401c0801c078075921020f130030000b441100da1600d588140620740e005542000030500402000f4040d60102c3c0d4141e20902c01c450030755800d0f10702c000715282110011001145808220320069681360304281d00d00d580203640b0000000d034107401c004918403800195016107022030461070b1240b08525488003481703805240104110008100000f01d41c2680e0340940c0c0301a003981c448001074050111100005d401908160360710800715807409415069821200590303002c2c444940500807540b0040b58007041e49a0714020140141d406a804040f80405903d04104150342e46024240c0e14552040c0c1140d5490381e40f141040480c0f10403a03541d40091071854503d260010548900410f12000740010039850800004a10740c4103044181c9242048080d0654144980d00c1c2406802000c50210554003444e9500c440071091001c440f00140580f0150400c10380d00c80c0340c10034881d160420012058000e00c04202060203100c1400141481800c1e00e00c0b0100000882c0d00c8050a4444035400030505511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712902284 1250 712901034 712901041
    0x17091009080a080f22031511030415061e0306053718050106030501050c3f1512031c020c070308040f0618030803070c02010e100f1205 59
    0x4540c85600700d0b00103d400f42c4600038603011010501c12295100b00d4000300c4540803074210078000840044900810b000440940c1207807250b020348002c0f51688060280400c0011b0001e000c048410380201c005c0b140c0043c4c041e41780e03c2d00e00d00c440c508010f88450703884141e408108020144c014503900c500508920304c0801c000740780b0400b00a00c44d081605103100c05081d00c6c070f00d20701550700031449541034008d82504541203040007402041580019600d079400d20002480c035605500c126a00308540c0c11140c00e0380b66002052109244d0001780c12514079030f91600c0020b40400f01d85295014040740c0e007088008090300c3d410000e8801d000d00301c501c45a00140b10b413401031003480048140d20b80c0c0e8143c0145c0e44001d0200712134100104d60704021b1a039900490089503a07105c4500034800c2d920f480c0c03a8000340d03a0401040038420700941c84003d1240e141040061209403241c0541e040e01807060404240078042980001e103500340f90030400700042c083c418403540c3c055101005021030100213030104050b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712903534 1250 712902284 712902299
    0xf16020d080c063403110d1e020c0d0c08070b041a0901050606090d02060c1209090c07120c020d020901060518040e1c050d05240108090a02130917091009 67
    0x1caa85844201511041d80e0310580301e07000341c000c0307060b08a48408441d0f030350207541ea0707d00041c501c00421000014901c007040390421054030855030344068410040141060030307001158007040e005001c41d0305e43c01c14040ca100065640441d09d0085203d40c41e01c44150444101c20010b00e81c0c014401e0306a030f03041c502446415180c45040b980d0380003080e9221454a141400880c0d818400d095107030080d03114814003042c00c24030b0f20014183c882c03401c60744d21081b81c503580d942d141342d4040c240014004120600d064a16103014035541102d9910191894844c00f17566000a0200b1100742d216501281c0d000400400359401c803202c1d180c05940417181044000a88150030760b880d83c84035190409a4480708604c601c0364056020381d2038580100100340450300c0c10500c030134080d202158041e501031001c942c200d100c43d8054103081e882254801e001700000000358007000f070040300c1d62908440b080e507140000fa01050812407c03001c6024196503403695001405d080c000d45014201d074240802a14500034070945 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712904784 1250 712903534 712903591
    0x70f030e0607211b11280b1e070606051507051e0f06040c0305060a14071d040f09020f04050705180117070809070e0c0f16020d080c06 59
    0x191000703208500703d201d409406461088074001107112161101340900100100c00300e8111910a041d60405000c0c2d0920b40e80e440c3e0071105901c0e16244145440d03042c010484010054449422031f10b0740c01c40780301c0c2e08540d0340b40c89074404d02c000c2d1903082e180c03c800d00c042d0401e80341940c2e46886100c4e5491030990303036484042e00e5884801c0c06140d41a882025010200402c110100c101c00e90802903514504061074100d802040521048036035008100c0042c910710101d00c01e0030350801181c10714040a641d0304104684010900d400d00f000c4002c05094000551910b00c60700441101500c8001544005801005644405c40d031403948168105030812a0860303014040c1d40d8503800d50b100404034640300c540181c820300001951b4420000c20f042c2001f54599100341268001c3c004c40c4142c0750300c992200350510b0024400c58410740215005c00c100306c02e049481c801000b203040f0581200e0074910441d070001d4080d682c1e401c4151107000380480c09041120047c400f194204a864032034800d04a5081c5155221 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712906034 1250 712904784 712904813
    0x315010915030b0d0b0c0c0d0807200717011a0d020a030201051b01181506080c0d0201090e0106030504120906020606040b04020c060901020309070f05090412090b070f030e0607 77
    0xc06854446410980d2503034a500c0c0c0c00c0f117030720014002451030043d50246064000c0342954190f0301c608200040d503203000b0011207014042d66541c4c0006c0104510007828114592061081a481018000a0600c0c0c10072864090818190b00100d403c0040e01d84a5168522003006240300f40300741154100180e071800d24150841e9821300301a5101ea039400c3c2504100d142104039607900d03508210301c201e490727180d00359007203100f0703100741a101d0017031070f80f416480304440341c5003c2c82903142d12000010000c0d1600c00b4174203c0301c510500d440d40140d9144c6001d0f03010540c0c01c3e408440800c0e00c5900b070004000001c13075261207140e5607282c02d20500b89845002543d070700e0083c1083e401076694844d080066200da404448401c0040021100d43d414010b20203030003980101c89e44840c80c003c8200124001509015410072202c0061001090307446a4072942810046c90030000709225820000241d480d4090025090b880d001d281d80d102190f401d41005880c05c100710540f148201c904001c040300103500020b07403264 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712907284 1250 712906034 712906037
    0x321030a063c030f060b040c030212011a1b0109030f08090303012303161707060c060f0207020d0803040309060305220507051302031501030603151802150315010915 72
    0x80541d400c03500402c0c0c01a4540025003050f290010980602c400303034120030028401960200101110744400b18128003e60410b100d681c0c0c1c850700100072884421007102c2c0e50b03081115100e840c162903841700701c04c4280d641c0b000c1419a5103480c81e80c02410f40040b04502010002d007820101c9142260b03807d1b4070fa1005004034144054a44000809503c941c06030100c450006070071289040420441c1864001c813a220f84030450b9079a04a1541d510404075082e011505240c071101c00308803190743e03454054260329042e081c500303500340185e02c0580e4508a850340e1b06405103c06958034104ad040040c29840c540d0854014107080a0030f2019490060b80c401c182801c1840340300032440b515191250403c0c00942c400c40e40114460200d0f83d0b4605503070b00075405408540c40d25041803c070390005400b9144188006040c030201e03540c603426508029004424240ca1656460350103d42035400034101d022443c04c0c4401380720012013001502c1084400d0058030403003d09280c2c2c1528608076980c1c58100135144800e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712908534 1250 712907284 712907369
    0x4051e0a050709030212011a040213060507020d050a030924090e06030a0606080705030c040912051c1a010e090f0115050910050c06010b160f020321030a06 68
    0x207549503c2000500060356008040155200d5408180d0380640701d003c010202c3e000d4000400d07280f500d418421144001210242c50010902d4007400b95000e4111039001e98004403032a801e84c0001d0300521601c03001906c40e8580310051820540310500c00200903840859002c0c80701007140c1040d0300080b4840450710300791510811340c0c0c0e03420040b900300326000710001c10840c01e00c4c4011501780008510601940c2c020b504481024000008010948032000c40c09030812004100084000b8481c00082031880300c1d81341301104050101084e00c04840c03010000c00d03420001c015a4410070740e440b040300d4101500c100c40400b42400e000e05041d18142040c85131920840400441d0140d4600031410764905000007051180c01012440c8058070940c030684a030b010f03502034880049141894607080d00c03c1d8561211000480300402c1da1b50446c882102c10003680d162088607034110b14000e080244091101c005a0748c5a22410500f02c88010365500c3c2c0c100400400d20309000e0300b12640721300444240d45060002c002d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712909784 1250 712908534 712908541
    0x30906080f151206270102072001090305060118140f0a05090c0901120506010b0310090c030902040510050a080f1002030714070303051b0a0c140102130e010504051e0a05 74
    0x508082d12099006402d015100c1085000f080d60014004890040c81c0941c00d6000c031741c0318082c206e11440f40c00800588004040c01d1100214141c0c1c500d2051043c1022440705880342c07542032038000c00742d0090ac505041400820308001050140d81103c2807061420710086c10322032015a00c4040081842c43e01d1651140050f090b40c1702084a421000000348c1482c07440c1d610b071300c090313440803401010959180c40b0380b00000410400100c100c074450740041c4444ca06890411803106c02924003180c1d02c404041c0c03a1004000541d4403445500c1c00b034010020404181443c000c2446030344021503000420704d80100280756500383c00400c6040c003030550b028005075203540f080310594480c0f005c170211101414020072402c04054041c1d12687c055060491040310108181003581d0041c0304416000300081c61440d5090006400c081041c010b40705500300260800e202d9101107107402400b640242000c05000c0010002420140315a507041b00580b0950105582119480084958007510900360b8540d80d8000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712911034 1250 712909784 712909789
    0x100813060209061305151201060809011e020c150712090f0501050c03041a061008040309050306091e07120b0408090415150f08070302090a0b16030906080f15 69
    0x12180307205030003450030b901c4070300d0240444d5800c3e1050103034038043c03aa42030b034092886103e20180c81c20200c030302a0010650b82081000c075000b104c0600458865903c440b071040c40c106100406011031980d1180060310f5820240c1c6040c82d0150807105040c072002c046081c4044140d104500c2c80d4528050200420454007900d030140503c0e81103000030b00207528043c14018440703403800c0150700880c040c940e41c0015070b05403420110405400e1385c15a52150740b1041c941c0d422806904100d50090081c18420003135655800424108442207800d8005600068140c1011881c901548406031040394001c0c02e14504281c0c1e015000105844040c20568542c0006420420003000b20b40e941540940144800007a10400d21342c0205079024984074811644200c091440c4103048895440002d6030381c0b0010b544803030905a009501070420f0940007404400c004c83d003800520010705d101080080c0320402400282002010303580690041420042c4d94014000d001e410b074203115070000c031056100c007240c00d047c200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712912284 1250 712911034 712911037
    0xc1b15020f090301091a01090c1d0f0d0c050a080f03030c091f030b040b0603070e01031808040305030a02071505121306090c0303020c0103092001020c030a061a1008130602 75
    0x201140c3c190309141440c4100040c003002018189460f003c0580581d0326400001e080d545580c6001d00040e1100c1c2403807403014401c80303410350140350152010080c0b104079804500300c000120015500111018810800c50601c40740010060810402410207150b01e400c00c1c9480e8407000d800c622004c080821066403640d1481c40d050020801c0900c2c4103103000c0d0301c0001030060002190528840c030714000201c5543d06100e421240300b03401c2130355900d0303541e440c80300150020031104144c04290068021088002411880140041d40c01600215121080281300034a0300d90a9003200902409041411580540090035203c6040e40c004a00f038581d0b4411a81124a0211403406007034681004820310500034000a00700a0344d00a03030070313580440c41d179000641c1519441c41c0000c02070841460100c070a20041c903402c2c81440d10500c141c400d00501c002c002494295010380a440c40c2d0340d82d46a9800005d031901c00d01d541c950003034429841c011012400905041e0000308080984040d0b0048103041003010b50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712913534 1250 712912284 712912297
    0x50c1201020c1e280204090519200d0203030304080706020d05012408010b1606060e041505130206040603050703060306060f0504050a060503121810030c1b15020f 71
    0x111400c880e84050041c0c0c4806280c5034007400c502440703080440c1808215840388914800c0410b8111307880441d42484020325400344161514050007441e440c42860401104800b00d00070640c2071001c44003001c204c0c2d1905c803000c480c02c0c070600310281380c5401a2408415a50b009801050f0b07151200d005041c514068401c00b000c2d140d01601d07141c00032540c0c071110700c01100b01105210400c054855078160a5070f400c0428095448880d0381400341c0605240c0e0422400c2640f8400c40c070103d0034035030f9810700e0a01c2440984044501a849805002d484d0310b952041c16401b0880103680e01a514aa1700481e0f22072103035006400400d900d41c0000340c0300c1c0780640c000100035a4048420020150b8608642c4080b46890140c0340c03049003802c001c220b0140840c0503070340c180d40380103026040416012004014560101300d40c840e41c032083d01c0019000340d403940901411800d46881c0402c0028003150f00901c08070310303510000d681201d201c03601400715446c02d42c8440b804902c1c440c0142ea9041d540d061203064004d06 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712914784 1250 712913534 712913557
    0x160c0c060f0e0907170a09021527010518010c0203010921020303060904080304110a030501050a0f0603050304050d02180f07030b1e040c020309060c031207050f03070c0809090a0b1c050c120102 84
    0x500e0108007041c0c0080080540c8026400c8040304101c1d6000ea03100c02002b0000e000340010418415031029880c0600c40383c3c07a203003050600c09040c40080e8003003425102e00100039100c8140b0058a1218294400781d60b042c0100c0c28030241d4954505903000a61061001e40f0190070202c0200024003000206006440703201c81c02030010703100d555640381c0140039040c1111708200480c200030b15100d0344e003950700030070b41980c2d4000003840c1060305041c00c1c040d0001500c00d05980c4a8800c41d14200c0e08544800c4090041747c28441d8060306142480014007511907150810340600d0092084014288a4902000300076608440200e400c41031300204074514020941c4a5a0141c00010f0080c0b00020000040003220358065a10750180da903841c05480e1402440d0001d1030310001003002404252040d5818048503214016150800d801e2a0201c0c403c000101c0d810420150384d140d80840c54680b2600c0a01108155141140d0b0040255a002d80300c1460703201c014002e4100310081d014002d42134069a40300c0400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712916034 1250 712914784 712914799
    0x9031204171b011b020606370819031b060b04020a020307051908040e0702160305010b090c1c05040204020d050906041205040e160c0c060f0e0907170a0902 68
    0x41c1d00384100c41e07411102d00448070350320b0080d80ca00d0070003400318a0360034075005030080c081d141e0302c00c0b052103e510240140c003400d500c0180001200b150480403000e0000d010300301c001c0d90f22420120f41c41d14100c040081d888141d071040c0e020100083d8800080603103118030741c07946070400c40b513850310b0405402187c0345183d1050003c2120000280e0010140c0455800b4a04680307000c0c007601c0307103090822600303600541360280401051058002640011f034220038144101c43e10406076114100701045280c000702c2c2c1c40c1e51240100803040c900602525004064100b005150111451000300d441130404a40141c40b0b07218400102556140e07410740c0c4111850090500403868100d02e19a150302c0f0440d401c60710000806040c22486110310240c40c160ba80c0c01030003c0d0240c948000c1000020240c1515808000c1013000ba80000b400f00da10020090005860703800841d0307414a0050007005001250600840070002007150055000101d8000240c0d40081c0b001c007515410302090180c90340c920080d401843c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712917284 1250 712916034 712916047
    0x210203120703020a180b1e12180c0a0f08010b01030b0102030a0c0312180c0e0f06040504050307230d02010e03040306020304030912111203031006050d09050106091505090903120417 79
    0x5010010303c4d207026000f4514140400c61154547c8600541c42d04001d103414500000d9819210381d107084140c440d24404442050046000007000c4280f00d801c0b60041d20100901002044802d015808031048242801d1041584000001350b0302c1c0034501d442010003110541c1d000505005035808502c040c078001d82800180365200c0d1450300000580421904070301c00300000541025000e0010f4001c4c0d031000000c41440d11072604101c094000a842661240810402100007034503003403903600e91180441140c0b5104100042c1e070380c208001c800411003964109848129107680c0401220705699100c5001a100d03100e505040341d82510940001584214201c1c20341d05011501d00c41e82c3d00c80c0400c96200b07400076400d0040b10b403030740015103017850310810902050003564000c9000d4542540018400641803000d40c0300c1c1401c0d111203a00c0700e204166610884900d4106441c018005440d06a80c44e410a05200c40c4683d9030344100751203850b54004640c040750412420f450000110304041401c29241d80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712918534 1250 712917284 712917299
    0xc210303151002190204091e03020606030c15120705040f09052403060402010c0302011107030e0901050d2a15050d150b2205030109210203120703020a18 67
    0x31400c82902c2c41400020304860445200155100356a12580c0050b24804015400c0c03002810361224121601c07912070b00050f041382a041c14841182c1e01a500404060030807200341800e110f0815400d90040414403c0c602e000c0e004542151030b01171071090304102c2035544100494030344c0a45e40021000300c000c0000014418499002107020300081000606071307401045900d24541000c180c4680c044c2c01400c0040c0140d805442000001400f900021400d9007030100d0b4029030354801c000880215000000340e42546c01c0010305203000d03080641c2c1d640d480301550b0301c80c03100c494402d0702c426112030202102c00d230030a0908940da00090400c190740000b08107a48a01900540104242e950301910300710403045900598540c01d0704807888030500501e0036602c0c414020050b0348810341869482d800140008084d00c00b4891540351501800201e00200c3d0340322404581500d2030f18034181154818030407454203c0200c0e201d40d400c8801800c00599070403e8290955228048150502e010042c9a000045c0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712919784 1250 712918534 712918561
    0x2211091609151202090f19080111070302060f073e010603021e01051b0c120303011a0a1e030203070e0d0c030f1509050d0905030f0c210303 61
    0x300c650388508480c00d894508803050420b03416a20b4000500c50b003182042908964002c1172025809010025000c3d0400007040c0440c0c0c08030503941d10080c0741e1004000780f90082c45440f00003002d4141d007a18184a42c0c400a50704d0702e0107001740e01c8036050f4801040d10075000d18003002a4684a040403901c002d6075101c0d0b08502512980300c2d900d142c003c03010010303182130107200b0758040d20343c000e22a00b590300c4916039004c0103c1e100300c1c405051103810800e049101001c680300c41300c0c5813240c80060802c10520000d202c5070300141c80081c6a07950042c00103009003445071246004010300c1c481d04c10384640000c14111a80d40b09d00010300307410024045c106406d981d05400441c400c10b07080e15400001040b80045c0311134940c0a40000e40f00e0a0000e6040c80000c0c00500140d40361809045000b000d041c9040800040b90b9078424126855807203001e511a41e560404808402002d00b10007a100700031420b601070742c4039001c10090702e11480c5403002e44945208001c1d114200800040f04690b10707407401120f2940c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712921034 1250 712919784 712919821
    0x405041d060c04090b0315160909020d0f111303062c06010303021c021e24010608010b180f01090f031103071a0d0207030c0812100806221109 62
    0x1218240285c40702c00d820005540c0781c403a021124a03010b282c0c1c521500450301001c02000b50700300007064400203400e1030180003030700f030309105a00009442d80c195401401260211602100e08071001d1040d2049410074040d0001103a8003c0390100d50780f051400c181c40e440e04c800103103801070064000f980000c0322001400c0c1d8180c074429001c0361f481104248800c1e1884020448040c010303844488084840141c1010b046c000500c40002c9407134020092040030707502d1686420412603a84210010001d0960240ca00d034018241c15950900d003051070114200c0481004111500524806010815a0f44925440b00040081b0400360030166224503055049442441d9194401d128511012855401c110862a00101100c0c02545040c2d80540070802035040303240c003907040c48400182036000c90341e0302c8010201c04090008000103403070240000d4880756034503005001c455102c1020064200c51180040e02180349d207101d1a1100e005038542042e90440c00f4607601c0e002401d00040c0402c012101028104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712922284 1250 712921034 712921049
    0x60d02130501020f07090e0a06020316020610050d110a0b0409060801050c0421082710030603021e04090c08010e061302010c02100e0406060504140f060405041d060c04 73
    0xc425590303800490743c4004c4e10583d0081604002410428000c1030b52000c03011719181019034107150b1182d01d440040307801c1140c42202e0305041d50022417405a06000c5540d00c16411000184014200360100d9011190184000c00702106330900300c0603952a10b60b808010b103030030625581e841b03803501b00500180590303100d140020b6007030102040d41055a10700391000e8030b0398604103049041c10301c8400c40d45121003c1055501d00810026580703000c0780100d02220810406c190305074641103010a00126810004250003011319190050005036601081c80350904001161400c080e04c0341800140140481c040c010309142108030000341c007843c10740190032807286080030380d005a85d8400d000007410b100240700a00242d408000c8100520f4070903401180300324145085480d0b114000c1c040303011110140c00c8170020401c04601003000e042e03220700b404295281903c088541000300740101d03100d4090340c002c0364840c036125401c00303c1006592841d0221000745000710740d62400c3c014540308940d4800e006084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712923534 1250 712922284 712922317
    0xc09030703030306180e0d080606161a06041b0503060105040905010909110d0b0f0a021902061b0405090109020c1908040f0f06050909070e0d0503180a0b070f05030702060d02 76
    0x6000603410700c00d880f001086030b0050a284407407d2400c0b600b4100061180b07502000520a02d4074100ca0540c071100c4051040700e800303401c07011001107000700d9440244064807a5081c0850364150380230300a8610a5140981081c0782c40b41c0321180182c805010740e0300401c0c4c082e8544000010406410b401c0206881c0c002d00011002013421018091210302400c0003802440c0341c07601203040441e401c4039469101441d010018100035000d803000d0300d031a9a422071040140e104000744240302410224541c64446002c49003032400c1e2400011802e80d603814401c4d04655079002c10314250303503141809440c0380b04920030745180c01c40ca85031902030b00b190054014900002c60082d400708180024405100548003d81c4600d0700b4a19003004110b2412030083c203041c10846d09144200342e40e120f02d01c0071082248aa0b01841d190340d6207181d09842c268884002e00e1050407076041c10000740c0704a004031441c054100a20032000729413810040d01d50310924100070741043c0d0019031011240b90355030140000340302c8040500d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712924784 1250 712923534 712923569
    0x1a011704150213180c02030307121d03091e180907240e0102070303090b0c070e070507150c2f12090310050f010510090801020304081306080705120c09030703030306 72
    0x200200c3c5d80c44251076000d03078410000300b00c0c02030140d104081600f8029001056200c44221080161001000ca040d40e030350011440c030b94985007144c1481d902850504c0075498519072400000c1801420000428440c0404008220080802d0043c1d80140501080b0b9135074000d8404001c603400c143e007003d1100002c00003050541e20b58400f040420440c0d0701641d8100c01c2508001c81c0c0482d550103007683e00502c0c0b21b4280000b45145510200e10320610407030f00c80c0c44d206c007030034145140c9030000d581c0444c0c0c015180502d140c101c0c41d0000d81410401450002003280440f83c80c00d14100e000c2d000c070040301c03070348201200b640040100c8130013811402c01c150251820f0900503c0c040080c1d032000c2d03c0d601c88452048005001c03034100010031001000d052714008a905680303086040c04c82e84191406da41c4000e001a0b0b074081640441c240c98020f00f25031415103071070318208800030050700a281d14200a1603001d0041403030140f82da8180c4071913140c01420f030f601c034079500c1c5000b0300101214400e65030007039200f00c3d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712926034 1250 712924784 712924829
    0x9030506090d0e1e04050c09120102040b190c052d060601020a080a02100f0e0105070807080f13051e010615021207020301060b0711041a011704150213 66
    0x42d1068075486407650400c5803401c50400072440101200c1034088445503050704419600c50003140d000d5000e0030181c60752105500300b844035106800203010151382c010041008072080d030408039403040700030400015030241140b41c129010f07c00c0d928054114440c5041448800f452442c0f42120030b01040f0003035080781d1040c01d546843e00310880d481400750300300324494808a000c41c0028030345610180f040d14502c0400b05610000c54421000219590755151600c1a0701c000900c00c603034200141c0d00b00600d10346442000108220310062004151148507404103e46010f40003462030b14a0b030081c140c42801030380e40224545040740310000d40596003021000200504030403048420305031690f02401082c181c3d580d8440791644460802ca070990b40c1e40f500051220241c90103000507a11454041a640c1c08100030001a1000c2e01088843c03103000111042081e070308800381600044910300344640b44e42c4c0710306254a56004100c1c29804590000980b0701710303140e01c20858015981400c2a40740180200ea02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712927284 1250 712926034 712926043
    0x42f0903100c02460203010b060316050f1303060516030b0a090e070e0405030d0b0907080a0903021f2306061c09020a0b0a03180c05150c07060903050609 67
    0x420009a005001c4c0c03113404840b180702280040702c0c04090301502403a4824803a0070360244071000090308038410504800c500d802c0c00b400707058110442e000d505504050701d21141c0305907403100c00b40510130000742034590301129000b92036900074000103c050450756410304002034081126030100e64009075025a5042c0c0c0680715100c01d028014060855039810100050018039030b0f03120000492051050018155403115209441140b013500519242c840c052a203509490345400098400c400310b40c02c211856030302c450701c1d9500541800c0c0c00308070103046050690814610001c5051103503001080780002141700d400c080181c804040064410b0b0f2410021044801810364190394402d01c10040c1c10101d51304071484046144683c1800500c06406600252814215a2100703030000d5002c1522850300342c0500c2128001025480c2d4040b10101e1591f40d180041d55a01030b142c8121052801610708440368001d5841048080007211324540d1641c030050600000b038401160319100340000105140800325 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712928534 1250 712927284 712927301
    0x2070501050d0f05043e13020705070f051002060912160c06181205030f0306190f14040e07030204020a030f0612170703020c04090807080711010906030902030309042f090310 76
    0x640c221243c10300b02c2c042003030302447c6005000d2000e4003440380c80c012500c140080030082c0048085112118500b000b4000006501002c90b03041d50460402c210081a02060318540503106010550399040154a0b02da003910a460028140240619010440c203410a03c401011034000021500d030913030360000103030301c540250381c010b24a820511890350030144000c040c58014000400c1aa02c1c0401c05141101d0107030698042c01400c00454030400250072a156601d080300c0c000c0d1000e004103408079400c40c0e503a000360710000340941d41c006400e05181c2e1182d440034000e1141d0500030b221007039031045004018003d0b52001e0780c0c040c4c104048a0010380c854821214450340c9078010701540c04500042100400806c10160303400d21040000e980081c81100c002e03c4190f00c0b804101c0c4005000c01c000400101c000c2c0c1040c41410f00d0404c1601c0940e5000041e101c60000032900030484030ba808440c1c61316468286040c01115880c07031550720f2903200c41c80140450113816000c441c2c0161124585606441d0b444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712929784 1250 712928534 712928633
    0xc10060b0a05070b182a1005090909010209040e1e0a030c0b060301060902030a0911090702030d0b060405030a03021b0901050d020103090611180102060a0c02070501050d0f0504 77
    0xc0009000081d012040141d200c5d00755618503842a4183d04498106810008140c2d000c242c00c60340c840f0098203003400340821507015136101c840b28540c0305c005030040c403408084c940729000441c0060168502501260700080e400f402c24069a040f400d81e80b03644013104da54603951000c02d20255040030f1400101c90f82c440340c0580e00c003d44030585032a0942c4030385001e04241d805548448020a001c2620b000650040703070021400038060015062031010000b08a43c10783c03091542c81d0a000216a0000680d80381018103100021450802400103c003031046900c2140c050041c3c0000c2c10a05030049003152002e50070103800718000035000b003040840321090080700c1e4042840ca080401551107036001844aa2040e88000f800c40580e041c011007540025500028010604210f41d0301543e06110103500941d05880c28051281c007117201a4842749240141c0d410000d0102d41e0304030703400032500101404860000f08100741e00f03007400c0004680c10031070400e41046a50044211001000c00c90010944600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712931034 1250 712929784 712929787
    0x6080d0c03140f04030305132102030f07060f11160906030c0801020304051b030a020910050f12100903090e040303050a05070c0c06050d0905060906150901120f06060b0c10060b0a05 79
    0x85135000e440c7c5800815014144400380c41c40811083e0041001c2c602502007414482c0c80c00c40b8030310405242020826480c003030341d04261010498690004800c2414100a0900007104104203000a1900641d00c0003030514040c848000a42c00180b82d004900742c0e0701821303107841504d031596030043c280d00c000c1d40c0003130075a44040e600110400065041d01603500d001001d44c1d440201b6078000503c0031005650f40342011000c2c1c5020489441c00391030464a995058401d00d90300c030f00c507148540d11070421041c1102e496071190074803000c16105004800180c5a68800103040b0b0402e800c00500401d0700702d903004490b900d0b10300854441405800801441c035441411280070390b041c403c080300c054200054000000d03031241c200f240010003d1101d0303480750943c180100703410302e0036a8640c80800c40400c83c0c24081e11f6203800520080c40340c000482486604100c0d0048441202d02d49540201210b5012160b50080410107036440380c40480c074404001b03042d4a0034401c07a6103518524075036104407907160012640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712932284 1250 712931034 712931039
    0x12070207030f030c0309090507030c0305070f0c0b04030c050609030a02070506040b0a0f021018020f0d0203031207050702040207060902011403010b090f03030c0111070b0108030f120a06080d0c03140f04 88
    0x4110f0130040c405100b45012244070341d030750f41c0c0310042d5142a0740940111380c5481041c0c1d12550b0601c1b52591000d0319141c8181908031181000e001c1401e5424043c0c0011016070008007414000d130000840719500108844451510308501501c0c0c0d0880010680140500d40c400034551605500713803800d448901000c2860000788240540c0c2c0c1591000640042d8003450110002400d900e100b000420841590922555002c2c0d10400103400e0352403030403078851242c0520280141e180001514841c540f07002c20b0b025a80ca4120f41a00e02d4007c0307140c002d50003400040c018040180503080088098070030b80341e419801660741403d4205000900604085100a106225580c50058050101d141d00a0250703498208240d00704c86c00d4a01802004400400000f00340d4100264600898010403c4e40051400d0a00754500d00d04144100f42c4990030040b81100803071641c01c919442640108501c10446240e044098005400c0300010321064001c10410729844540070340076001c403003000c840391b01030b203280c41d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712933534 1250 712932284 712932287
    0xa2609011403070903050709060e0c071707030c0b0126060c160c031205031b0c0d0302032d060f0a03020901050907111b0a06230c0c06070812070207030f03 68
    0x410041500f02084003d8a0001c0412810701c84071000d41804a40410040e0800001f03007603090001e001c50b0f8034010708102d05d0700400c04102842c2541003403840001e075900711909044850800381040500300210f440d0000448400201c020070045d13926000551b242c0c12500303005030b10303150101c545840242c010015145c07c4003030540900f0000344960703060320909840b07482e076900070702c03840d140100400d03000030502c01503c804140300c2c1000e44910001a1070002440396064032400d060700440107042d00403020594284103100c011010314110031030b20020414649140041300002d0310002d01440d881c1440079124201004060107580c0c0190090380c080c0d01c2c280501c4120f00004105504104000f44841c144500900003030a1000185c0c3c00e009480030000100140d402c0c0395440715003444030400685400381e807048507140303094203002c400649a85102c1849814100c102c0f848503804040000c0136010086014044d000344804a6600d40309035a0b01442640d0302c1040e800050408801e0007040d00009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712934784 1250 712933534 712933537
    0x40609060e090a1d0a0503040e0c0f2a0109030f0801090b09180c0a03050f0c0108041a0901060b0d0f06050d0f06020f120906040215131206020c0a26090114 68
    0x4602000a0a6012030400d5210300303007840f41d00206c42a801c000307002c00045c003115026640211080b50114034114112002050301d00c56851720000c0c104590101c4103141d00c1c42c60000101c0041c90000b80244921803500030400f0006c01011300101e01c18200209a6a1007441000e185031b4010300589001c2d10742c0390b43c140d0b02d803100c80501001445060200b0b4001e40700c1c5074640c0e0003540324000030420301064882d194200500e030f180190410011104000c04110301c43c44040c980c00b80b80d455541c0710b86584041c24050556074214002580001134804c8203003030658020b1b01c0403000080204000f46d1133008114407140c42840c00f03420390802001d83e40c0407a40d140d004108003040860b0322071524100a031020381c01c0b00116012009034100c4010801035007814102c034161001800c1809260035142e206104949216001b200740059802c1d80040030407502d51304a6440812050880d002c00010307143c48000552040106110062418120300c0182140400d503841100141c442e840c1011585114070401d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712936034 1250 712934784 712934801
    0x618090e0d08041e1a0c07021020061f14030604121b0308010503010e062206020c03040803070c06020106060e0f06090a080102180102060112121101050a02040609060e090a 75
    0x10001400c80f06130054000414042000d11515980d40f8848070a00c6000c4041c50080100145141c10400d01740182d48071102c8400400250030080c0300c0ca6400b0580e080d400d030340403101200510484040c8103044000f07181444e10656504403000c0382503101c0c80e041070503001400311b0b80e03015845400800c000402400c201400c8540518102c0396010540c1440300c43e48001d06002d8012500c9000148081e0900703000300e64a907a607200c004c0c201820000884a030b141d410900a10301ba000200b085000c1008a8040322445a9071000b141d489036100c032900c40e2642d10611084a5400c118100001c000d40107004110488041d901c2c0e100c0d03624010400c7c002850134407103040750300c03080c1000344941569968813008080e0100c2c82c0010f071102c58030000400c0301d030039141c81117065500c200c004000c004a058000c21010303510002132014041c00000940b100310b15110403081950803c0c0802216045560140084070744a607500c0a4455481c402651a0b07498200f10640040ca000005215030075142c002990 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712937284 1250 712936034 712936043
    0x150a150318080406081b1314130212071107081203060a170a06050606040f030809030102130e0a1a03061b1908010e06030609100906090b010618090e0d0804 68
    0x380780d003550751110110781c4144c01c110040b41602007842043c10403c0c90b540b045a42400d00c9614012140d10031510b2201c06100f504241c8039a409462016294100c00c8030f0b60004100080d500d460694044140924088070791100040504845c44462200051210200c861560180082c403036900d43d11152030780002d1005800510b4250b000540d0309000040b00c02c0001010043c0615101518002040c0c0d41c0c09081540302d05814882441000c81810f20802141c1e840340b540d1355908101d0010901901401102031050804900005000301c03110408a02c1185424010010004082e07085403c2da5400c00c0740c203406a1124001844900d440b046c00f02d40c60307170031900c12802c140350110781500010780300f0800b10004078544010891101c0c41010507400074405c030b000d01010b26141c6102c80c1d44050021a14060399112800c4000b4071200741d0140050301e8004245102560711020301030a4882010059251124040b500041007203c1e846061446220b1001508800d034060008030390600c40a8070a46 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712938534 1250 712937284 712937321
    0x1030504120f020c0604180501060302043203150114010c0c030311100c0201020a0207090b01051608160b0411030d0f0c1b060e0316030201050702092508150a1503 71
    0x2089517540e00242008150503003060082e84000d07034040c07040c0e80041c0c0c8800241401400103100c0040c06800040e455004004aa40102c080004001040007042d150030b806014000b200900348024100c030324140ca03460700b20180058131100c01141d540b0115030018011501d40750003880002d12800308200c40150311000c41d4200e1000c1d0301c408041321411245003001d40e50014040c8801c50301803001c807000388452001041a440c54100103000c038030031032091f80c0301d010750790543e0400c0000e41c02c10b4903402d0307102200d08146418540303003855002d03009940c156021800c5482ca40090300d0005124088010141c2e6411701e000d40034581921031981040d8120341d105548000000d0b02c200002072030b4024840c55545101c030080341402d050409880000710f258140d03014800f8000750340c104080f66141e59040d10044541c0d600c002c0200488180b80d50000c14461401110702d078650b502071010390080c08038035454200c05c45040200202e082d030340d12403071027000081d001080429000b94803100c2180d8902e003a16 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712939784 1250 712938534 712938553
    0x10080d140c01061725270c080a180203070308090a081207020103150e1f08060f0a0605180a05040c030b07050a020d050304051b03071701061401030504120f02 69
    0xc40c03e5640c107800503040c41c4454541044814010460030b05404030440c0f60743c0422081c105810789215a902560f103c000d444a641c108003038225114100d046a540b1302081820a4040e00801e0030800b42d0301c02101e11f00302801c00e0b560401d4445110b88066000b4002c0c0040e510710395800c03060342c011000903135100049803000103540c0d1041c0802003140301110030450f600c580d10b100140480302960340785a6032440c00d003418444c080c0d02d034405580141c480300611540c07600070403031001c01112542180c030680c01803030144034040104e04411402080510301c2404459221310034000d504840509030100200010046000c0c1601c40d4007143d0824010740403100030365240d80f52401d11010603558a4001000000d0740c401c042c0c1c0c1400542e030461103c0c0f829905e14202a200c00d0b60702d9442040704003140c60124901c07441580c042058000030060303011841582c0d4880d01919000740318038481c12240c0c1d4a01c01c60114070358404c1c812244150740c440000c200940701081b0484a424007065070005600ca49800c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712941034 1250 712939784 712939807
    0x1a160b0c0d15080d02060609010611011b020c01141303060b0d0614150a06080610180b0d1817160213062d170313060201060e10080d14 59
    0x90204948841440b50076103450280c60074900110706049400719000142842141e5840d42140d0303044441501d440c3c110708c1400700e1464010807259810183d90280c00d108071710340035008900c00c0070391002601c2d0a12064820b06608000d445182c01080b0a14001c100030f00c000f9070310354407000810780090010501d800e01d035a030700000c8138020149140c1d1a11010704012007400469207000b410602a550005c0307591900d1006055031a021340028070420440041907403251080c80181c1090048500c203904040d644c107007030342060b0f11101240380c20604011510440c4d004209140c0326003070f4031844c1034403010040c3c5102401c540041641488041444502c400540e40700d24a14058003108140025800c0c500154120f0070089501c01041440c044000c20000030904216001140d141501340900d10b42042c2c051402c51055002000300c0c458054004500160305520150031354409481392819500e903084440e440340028410080150b00024140300f15922904860900e40400d41c101c07400c040ca0400b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712942284 1250 712941034 712941041
    0x50c0f0304030b060a08013c0606080a0c0e060307031e0c1d03012d0e0f0a06061a071e0b1603050726040807020d0b011a160b0c0d 57
    0xb0075a0941c140c036092101c1440d046815500070201d04008101c0316420418103441c00501071207140c1c00b002c5011121007425030703000d9000c4800c0c00c0b5030402c200103622010301526005c010341d0a008404d1410103ca04414021002800d0801d4000c05a506580e00c1040803170103008008452141004101d40c00501d0100c1800780280400b602d44881480d000f1811041c945001211041ca1084e81410a40b01040c9441403482e0003054540c00c2e000c3c09880500c680724050039904001c40c1d0700344102160000c1d10301002c108000c0f02e61060b50180000c590741c0301c2d060895844800c02d494000b100b01b020708001401c0340c44840c2d0300e051140311030011203610780b25009141130884501010100800046070b01a03072500c10658401041d0408038400107a140703202001e4090000c1003190341e060b8174042010b200c00c170400d40f500c250307006000316421031031460300c128110000c0c40b03004640d940b070040102d44004071a0554040c1400c441e548900b9801580b260711190300b01410748240e5250800c51032104071268003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712943534 1250 712942284 712942289
    0x15020106030201021006180b0a0f0b0904050709030510090c150302090405011a090906030a05030f18060304032c04021602010e0d0c12061104121101080403050901050c0f0304 76
    0x10000a482072460001a0812043ca1485803c491a184047c06480319944003200b40041c0c0c52000502c0d0284074012405141e11a0802d1082c2c1d0000032000425002c114000d00030110262024041a160000180c4020620740402003ca41124440741c0e105a107036804111501c5c080c40e05030003140d603144404000c150001078a90300182e000106540641418000c10740104030000e48142c541e07060840d0011680158440030380b24030301c0030001c14001e41c0c04005010f00d80345c00c130b010781c1d94490b035038001148103500040f0041c0c0101c00548404000d03140406c2903d1043c0d40580321194402d1184c140e001c812a1b4001081c00ca00b010907070300710348544461000c0d061400d0840c208003401d070080c1c00003514100d07012401c988196900c1d02ca020024000040d2032003120030440c00e0006030791140c0b806401601c0c00f107000c62171031000803c0008005c40901c9488201c07500070301004580011900045400d641c4c215005400f14404102c1040c455100704000c000603140710007603d28481006507524215440303507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712944784 1250 712943534 712943537
    0x21e09040b010e070801080304060c050123041403030405060604050a09050a050d30020c030d090605250207030b06030a0209040803250903020f1503100e0a020a020a080f0415 76
    0x144014030860043c2c03d04503401403424200108250b1412000517640c0c40355020743c40802c0042d040c800104042504200c0d8540034a4000c000745030403203140e1046031034040b00c0c180c1d41d408040614030407100000c0202d034002c41e08500030b0242d42c0c0e074080034000600b401804403082e10f90f40e001d01d000441c1e828840d20180701d21a01c00390226001c4408000e00b02c1348003850890042c040303806d4030404240c8140b00f042e0070515000d405a01d0344400b0040b0b0b419402559107083d280c41c1850009004c0005d0b640c402882821104051210400314088100b5036402c5030f07040502580c0203d1050002ca401d0128542e4045401012260411503070350100e5148c02058170b08070f58020004c42841410004034100c00c041b45518101c140340c5500506001703251403007a01c0041d015503d544105e001584039900c80030511901c042c145507490038000c4054900007003034031843c05000b150401003010761900303008607400f1005990051140308041d48849030f03180d000d00c43c41d181c0000b04110008050814010407450020325 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712946034 1250 712944784 712944803
    0x1c050c070b19050105030c03060604050901021c02070209011203051602030c031005091902031513060c022a03030a0806040e06091e0319050702010c05030d0605010e030606010c021e0904 81
    0x18540c2a100f99841078104500c0380e007100c658114035440c00036001c0c8d404902150302090170380b551102540288269040c1c0030703400186007448005001c094005040c1148261109120b44e81e07101e5400302ea011401c600100056800c0003041c0c03401e05107484203000180014140c0f0480000d4200080c503214203080b94882c80d540341e07010070a6070001803100c040610109441012065440e44c0060385a6103403042d034400f81400303180880d00c00103d618100002640c800d0040006c40e12031100695900d1544001240b0071f107080071fa403117081c90000c0142c042501d000c0d0085003441441c450a54415070000c0c0001d070002e41d5a1280d00341040100900c034003840d2031102421007440e04000c0844803840c41d09508070305034030070400d0340303034543d2001c80d410702200c44d0f480c28644402d9207100484407245201409401c2c0c0c80082000c50340785000394085400c4030002d072079201d1518000c00a00d070310388004030f5005000c5007801c817552002d41003210002c550981441440f00b090100c410006203803d405940a4030300711803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712947284 1250 712946034 712946071
    0x1107060806010e030c1309050c0301020f0a12141e130201050901050a050f03040c081e070e1339080c09060111060103030305180c0f060f0c07090e01111c050c070b 71
    0x20280402c2d278001c403007600254600074104a5060161252128020411803044105042011a68400105c0581a200c410007506081e40000001904445a942c00700780784408100302d0100248103006165040c0c60382e81c00c100000c801907841e50400c14520003803000820006082d01c1c1d4100c0107602c0f031072050031b0380340c041070070000b01521b400e00b040d046107021324060043c403090030300015400c8210762001003403030b000380e8802e4080b003041e0b1510300008120204c10301040700c440240c4900c07103d13088060100d00041c0b180034803481a8040142c810a0b00701d03000b12003071506a061800710a41d002606041800c0800034298406203008026030064000a6862040c8202209000301a2921003c10401400540c401c07000003029041854045032098100048541c088000002a81c9070491110306403558155100150000350000d4800c3c10125480c24202e09112100c65080d2038030300d441143c80c2d4a1002d160442d03c0c0040c4800b404c103410003030b01446020000f84100c003d15110764000803208900c4403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712948534 1250 712947284 712947293
    0xf090e090d0813030e040c120c03060503010b010906090b03151e041404120f1103070c08101e0c03020f07050a0b0a1a061b0f06071107060806010e030c1309 68
    0x16005040f20218245800115021a07844050611441c2c811a40011400030f10103050394801c00d0080362044d204d00304408a50910b4041c0d000fa021180260001d01c10001d45100460f0508218054140800da89200c1486104001405140c0c000707008007141807850805000607540d1010950f150507560000c0000d0703d4581050f000b030050743c00714a0407907552410203079a40101c0d140400502c9007084101c28140902d103210b86802600040c2803003d407961014641030a03d545804c5000b00c80d068800c04500188041c0148220043c8040075002607214805413940e00c006890f0b00c607581c0c5c1c00c041c1c09002d545c4403c41503000a04080c2d02c180000c2c2080c00721441d00c20a104002071881500074948000c00020700c01d00e501d202110344c0f0454801c3d43e03030b0ba07100c000754660b02e186a4640501d44030301095008000300025a980c080c01080c3c480d940d0744142803007103540d030395403d0042c10005030800000c02c0c3c455010f0003c5401d42a801000d0b00c0c100e0729198040303107080d0700d01c00f084443c0540b035040550900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712949640 1106 712948534 712948547
    0x60906091d100911092b17040b040e0703050603070f05100909050a09050f06070903030e0d050f010f0c090509011202120d02030d050a14070f090e090d 66
    0xd00d04c030514104141c001a6049000d0980405103140616800703e00ca14141060400014071804668440308084404c4455130401841400049800520600500042c1940300c0c80080c051415002c000d007920700142c00345029401007030f401c4c055684580450340540d901610f0501440784640c0c01110001050b50190215501d03001c24440c1d50010307508000e010900420880b500c03084512241a01c911086ea5688013251a800040001a001d0090200185e03070081015450728842c2d2200c2d410488200e03c100c100341d6550104680e40381c0c80c0e00c41d08203d98250301d81080c5450a00012540c0400103004811249041c000e050085640e46054036000d55404016910b02ca081440c010b9070701e4020480003010141030400042c4844418400c0400d05588a4101c41898036000000e40d41002c414092808110750f0f120049001414004180d02406401000340742c011501a0000e056 = true := by decide +kernel

theorem cover : BRFrame.Cov 712769784 712949640 := by
  have h0 := BRFrame.cov_init 712769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712769784 ≤ n) (h2 : n < 712949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
