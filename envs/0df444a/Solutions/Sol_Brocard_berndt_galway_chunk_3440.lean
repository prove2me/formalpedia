-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:07.107572+00:00
-- url     : https://prove2.me/submissions/55450781-5ffd-4007-a200-36c5451161a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 618525179 ≤ n < 618705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 618526429 1250 618525179 618525239
    0x70b160e090c0f07060b0307080f3a0905040c0e1e06030c030a020c0a14060709050303030a0f0e03070507060207060305090a140a050105041b0b04031a04020316 70
    0x61042101d416035140e5060501440500d00d41c4503039902610307849003e10380c0071a201d401d0001003420022950004a40c94000320181c03101c00104005c1c0880c0b0044881c05401d425011013030201c0c0b02c144400c4102c640450100341c04859034452442c00018002c0248204600c409076100a4402c0203080c0030039026104048200202c0161101105496600903000c02d01d580d450940034a403d5000a040d01c140a40c01c2c0710003d134074542000b840e4034041c403404012903000c8003020745600e4140000c00a9040007460181408292000b10a90760080070425012500159400840000c0c0107080e0501050f03120100300383c0180440001c60b001201c100b5000d4500300e64070303040103c054600480c3d0b440c10551040c15518001880c001552442840003c05d0750450a85076a80310300359002070b01e09841034580d0194204010403a01d004a004210300d0008078038040c42c5542c3c0c00b001e10616200121305003d1100041e0540d142031040c040c00c881ea445012200e81d8030b4100101c698007244c40c540403e07201c041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 618527679 1250 618526429 618526457
    0x705011d0706081003020d03090801060b0304020901050f010f030e072705090a080712032315030d0801091d07080102190507051c0e03031201170601050d080708070b16 73
    0x10380c0709004051031580d014004d0309640900500c08451a400c07001c1241c0f0700380000e4021001c0c418200580030030500203607681030a0040000c54801a040980325441c0b03d04007907020f81c1c10420800400c6c0e55802d000c598034004019036030500d45542d0200309001d0f000540340404001d00109582210050030040050303488054072a65550ba140400400002d02000001d010640c0200307440c040e510a4a070102e0702032180080e00304484090b48840d20420350180c140892296000c59034620507800358010000c052800d10010f203070305011301c10444501e603504e01e0012142c910507492036100041c64219041140d9540f4601e001358000c0d100100c100700c81682c010607840c4100c0407920950780010040290072680400b9801c044404d0122205105014100e0141078030180050000b00c440d0720100200c0703616091b010b034080a0710328496401074004100602c031a944149003050419040415103407182c03024a040529440b90301005404d00381094104040385298078001c07001e61420f59100b00c000c031125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 618528929 1250 618527679 618527687
    0x101101050906070f050309010f0c0507050d08101403030702060f0c07051f0f020c2214040b070804080c100b030d03090803070c050c06070605040b011d0a0b04020705011d0706 76
    0x740c3d20740740050034010328900f1441c0b0800203190888410000002d0712403203428078100300d50701c1c401808046100070600005205007404105d149e0103850a0540881c039151022400b40f04607800343d44d8821040410300c2c00952002c00513101d5890740604055520148011507a0841d00f100d09801414424400007280c64186214240b04c0c40743c503d4029600c1c0d41003200e040d00e40304018a00802144a43c8141c080d40c1e0b590401c0c2c11a003c1c1120880c0d0070010012001d44064841c28203204a54282203014030000803401a038940d446480b5290001d100d446600e03002c03116105451a4181511074881d0001980f03400342c1c00301340e00180031000c0f81d04c0e00b8031514080e41501d00080000c1c1602200340001000140103010000b600c0b0b114606452158624800082d00c50308010410386aa640d5201004200000120300c2030140c0141c68130f02e20b82044520351035a20034001040c1000300c0751a0320302c525075134613560155010305611070020f0180c060408504490994110b400001034070446500003525400f07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 618530179 1250 618528929 618528931
    0x29033408010f1a091c0b0a051f0302030c060c071e0905010602150406050601090518070e1f2d1d101e14030f0108010605100c20101101050906 62
    0x2101c1c0c0c83e182408411020400d41110421401e402c115844a810780000c100a04d9640f149078092030020381818400c50b145191105000e0081074104008801d00140c1d400142c622050782d02182c00b10343e80c09500c0380c0c071703130078000030ba400300514004c6401540d4180e20005000010b954a901041049d80c1e40c03020200d95075050380556004601011002c10046902c9400c80c0742c0c4180181004840c459580c6c001c20001c0c2c078456404500300303a40d88203000c605039001c0c03101823901c0401c032050102c1d84014014401e0180714500400d0500030203607800c080c08081810554400310309044031804100c4542c202400060540950300740e810741c01c01a030f0101d40303050207501030a1055603403480304102a612120800b00020102c0600303012090321007003c49110324008602c550652414076019502d415600c03400d548468200c07078400ca82c41c603500040c2981c8000c609118603045440718003004002c545800b1821051314403036800c04100b0065040e40d68002c81214807080342c1c82c00800c456503030f5205668503490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 618531429 1250 618530179 618530219
    0x80f190f0b061c200a0503070e091c02160b030c0d020c0c060403031701060201020421020f04050c07020915030303040f03091e29033408010f 62
    0x10580038080358030424030359800b080203050410350065000180b4222504810112800c0e030807212034414079140101d649070202d005071080076106040c41c0009032260660b004510800401100160304000c04005240c12040d043d50b00390520540d03102d00075103c22114107070f42041c601c3c0000026047d1007850450340305400780780095080c030031002d00540c040d51008003a00304900c101600b190071903803a41e0041005501c281c0300c00c1400e980d0900c0c0802d400c10141c1c0071505591060108110481a0f100b481c2004c08903002c511416801900c0094100000201110342162a0404110703000c90141c000346030103130080310f4065a541d100349007800c48821000900e50190002d1000c2000603804101241c1d040b8440d040021085031900d0141c00402100c8a400750b4820b80d82a0070001c12040001e001034036200800d2f01680320007500c094642030301c000b420f584c040f50410345040e10f500300c03a509460144540301e100540d00089011000385503110030701601c0b11f486429100004c6075440c907920b410b5582 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 618532679 1250 618531429 618531443
    0x5090c010806010504060e2806110a02010903030309081303081b0a0c061b142b081824060301061d0c07020a0302030a24110405060d06050604080f19 65
    0x141c20b140048903004000140d60b03030040005480c0784800740190240c281a1f08e48185490724480c504140100200e100005464554014041160251f40d10100400a030390705420086401340300c2c0d00e4001294403c8620716901c07150820000700401544600400340215044800e05c502018148555114041c10310028424920950200b042d0f60180c1d0101645c2d03c81e443e01c400c038003402da0b103400c04a144280012909500150240c820b40003104846003040c1c0402030440c981c0642c210307000b400000000e0079501c02d041442e0030030303080c0100030840c0011039a00c1914034010344803001c5044103d01e0b01555560b21950a01d000841c941264481c0100c1c0c6601c0c0c41c00c114030315240c00f00500381070742c4002c40a82c2c11000b030348804005a2403c01454000622070110040c000704012140e501080d03002d01626025428007466800031060034055400f6079008942180d9140d00545030702c0c008011a43c84160011408540091441c00104801c2c0c41481c40c6030903a00510811007031961340c0c4d100340500070b141c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 618533929 1250 618532679 618532687
    0x604170a05040e130f0506070206070801080c040504060f0e071406130b18120d200a021306080609070f0815010b0d0608070f080c0306010e040308042405090c0108060105 74
    0x801020f011250000c041c0c41c00008240100e0301d81c0c2a840c0044002550300707034010800c1c040010350401c081544501d00340b401c0c0095504004c02c0580394006802814441c1d501c860118051000304da11040381503070001001c0260200d9088071175110007661007408806540324155103504e00308581141d80d000500d855021078542050007064003504400c650071043c02c41d82c41154a252140c0990120700d0143c80010070721026070040c01080c500c2d90804039140d01001141032042c028001502415065046403136030100c0c41c03003d02075002000700d80d00000f1070303109140500c50395040c00704011b01511400c2030759600541d01e410346a940d07140707052001d0815529803001081035064010140c46030540e0550086500c9a076a0403851a05005030405810a9081c0d00c04102d403010400540a144070140d010300995031400035440106540248094240401d080002d000c00c0004603000f1450812820350b1307603014100481c0880200400c907081c0504c1e05c144400d040156002d402054441d0300d05035206490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 618535179 1250 618533929 618533939
    0x30105150d0f0204051014180106051e070f0515130f03030212010b0c010b0d0213020f0706050a05070807080f06130e0105010305010e0c01051c111207020604170a0504 73
    0x280716141c242602e05003151807034040103035a5401400c3c0615240140614081d040c0450302c3e6016102050003485040350100701e40e088008000328a046411608040e40c03a92000c2e542c952542502a182d204200f034006500d20802c0100640616001d0103482201c41d00e508101c10741c01400001d86803e2101041e000381d000000b026602c0d1220110b00c40d00d40076042020310140c01ca6507210a8002c0700400340041070704540b80009108900c1c0003131048605040c0810b803074010032403550b0040d814411150300024207800410401c021602d9a543c8604e0800880c507205400800514080d16580300240300c0790301052510703124012480c0240a006540d805944a44040044520320401c090402d16101d00ea03a0034182d4081c442c0d80d008600440020800d0a10700c06800d0070b1020005900c0d043c44028041440300346444940b295009905450008608010003044003041c000c20b4800f03c1350040710700070451296400b04046004a2064143c5840d942d1122110115802141e0006000070070034001042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 618536429 1250 618535179 618535189
    0xb09090a110127050102251206060f45050a1808031f0e16021c030b09010b09010509062a0708100203011d040510050a060303080603010515 61
    0x301e08050404101001031501203010b85805481c506035400308440c003c005a580506c0b000c500c10720010f004c00c0801500d0100d030125400355005e0f58000001c210500030030841c1d07076880a400381900840b1040010303a95102160740c10400300c0790340200304d1038030381c0ca50b04146030780c3c40180103901031361002e26040e9050a608006104c020841403200f502d4a0310041043da004030078004040c0074100712a601d00d080c0c2030110f11078200c844600080142400104031030941070400d07980041024040e885c0306050144124a0240d00000d920165000034428080c21a0190b0002f820402e0907945a5156070307840c1090035050181e42003e0307001c60020441d52000c0e181100041130704110f54400d04c240c24584207210b9000411011b140c40455004031010300407990700304040b0440d0b512000c0f0640c40c540c1002450401007071312002e50064411040042010400c00307211040c941c00302d1072801c001a01c0d020a6480250032544010350109000001248541c10306014080c4200038440b0a0b015000740d24040c05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 618537679 1250 618536429 618536453
    0x71d0d06021305040507030902040b0a050114131a090f0d02030303060607080d110a090905040804090c020f1f0b03160e041a070c030801080a05070303030c022e0b09090a 74
    0xd00c048800c1180410f10f603aaa2007424010b00d01c40c0da0005030400c1c60705c148001c407000102594880c091003001081143e904c200360088218044280680741c0c4005051142a0500c035041200c0c480005013108102c4600b220142100c002c04442c0e500386100d0308070902c00d1a00c031404001c0e425800c03c00000c0ca10b07040c994000d14403240315040491900c594134840800322820070842141071480056000c1c0072643c04a00e1901030881c2050400860400d80d417800300510070303803180f000b15948404540c00c1c858000e125051600c0e0402c0c081d01d6021450141c1400d0001c07070744090b1100107241424005c00b9042c001040307200900c0039a140d0385c01d50b04080071030000b0a001401102d5020703011072080c6d0311803410f052450080100d03031100c080101491502412440c4142c01401180e44800b0a42e03010a500081c200c00301d940500300010482c00d03c0d83d049041c44407090b8050420b03017452680700714044200c40000490481040c0800008050070104042504140e9440c0d40a5001d442c1c00404107407041078034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 618538929 1250 618537679 618537697
    0x40203040b061216080c0f150301050f06090909160f05010c0219181a0d08271c06050114030d05030606090909010c0f030236041103071d0d0602 63
    0x80b041000301041390440580c0a400010481c4c10032582d8400c541803c0c03901c1441038100711880303004140615600042800140300c0d0030f10641c46c04803090080e88480d0111201a100940045924138240040c640d4540062034800413030030000310001448400045694150b920595484030720000b1a020400170344884180c902e0070b007000308d00024070194800c50750707101d03c07e2140000c00c0c0812521042107259007030b0321410b400384e0010100341340020307100411550303400040e000325890b00c6200c0f180c50b40c0c0c1e80702c40c05500380c02602c10000070310500e850f450581d5465115401c180103030781e01d40b00503c0d140d00d031481d5441c3c0c040e4021081107908a0080c2d000d1a440358000e00400d083c10403000000f00b080c00142c60106403650760703108072502554004400440c00f40f0b18101989030400d0805440c45102c0484280004c1e5881c0d4400403025410055a0f80d50041e8001d1080c0035410900c0c0c03003100958415a074403400f04071083d4060301c40c03010203400385402c030700010034800d28102503440e0305019501c00a05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618540179 1250 618538929 618538933
    0x1407020609010e072c10030c0602211e0c160909050c09090147130b01090902120603070e06031b03010f1d12090f1507080403110f040203040b0612 64
    0x802c000041d101941070f00c507800700e04403461b45500d0360502d103c114900c1e0700032030115004510f52042c40240c025101d28600c45000b92940c0e40c0300c0410062400004982200ba1043c1c030000d80f500342c6000005108496003010b107503166403141e03030341c03031840445500070401021508144611411458007116060307100040303200110b0180c4030740601645c14448400110062544e03082845440e407c1340e00010200e00307480c43c041d00070b0039201c00010f08240c1c0451071101c50f2a102c000b003112992064512100411020f9415900d0310724489128284020854015000c2e00c20400c1c0007c0d500200b541d0345000c0c0101402401d00e00c600302e078649000f00041c0c3d2042c0d4056403030341a020685150341c42546003c8e4007075400d0440d840c00b0007100c1824040042c01003002d00c0400d10550074035035141503440d480c810702200c0d50341e4800e10141007922180070303c000242584101042c0042440902004113207168003c9440e2209051010200302c100c1c001900c01404041051000441c18203081c20100e50400c03e03401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618541429 1250 618540179 618540239
    0x180f05060705072d090c0914040204030f0c091b12090c03050f0601063e070e0a060312140d200a02030d0f0b01080a0f0b041407020609010e07 62
    0x30300101c80d00c2089003144c440c142c45028060180000d458890260030181001d1200900543c0010005103082c024040e54919921052105964607030440c3c1c01142d03c04060032051415081002c1c1e0781115100740d4401500b400c99680a0940101442e807601001c0d1321a00d071454034240d41000204903c1508446c202082903020020510800031000e007018020020415036060800080004801c501000c0c101d82c00350030303600380e10740300511f1440880700201110906000c040680c2841e01d41d059114a1182d981d180c1403212074440c0382c00c071109583c000c01314003105000b846000c843c1c00e03411188001c0741100c14024400c642e601500700311480500e801c213030301000d84082000d0609a01c141401c4c0701580c40001e80c0c501218050041070304102e5610340c1000740e1141440007a0100400611001030303141d80308002680071b00c40c1d40c007000400c0e0b0040d100700480041e003810071803216030654440340075200e49400181c4008050084004515015001c0d100061030300d03c01030070001002c03600c4030300410801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618542679 1250 618541429 618541439
    0x3120e070b1308070e0f130204060e10290c15090a030e06040f0302060c01060e0907090b030a03201c09060206060f0609010e0418031707080103080405060d09050d0203040501180f0506070507 83
    0x1c05403c0250114407030078600d40c00c082d40f15103901400b0343e000d505c2207500b0401d4030110b035290581c1507511554220314dc1b03070350b11562040b15003400315000c002c0d4000c8000340c040c410880000150814654460b8403141030150b2104100f140328016881a24150b90000ca410300050601c48003524003510180e00208002d51180007000aa0f101150071a01c198460542000201418081c18504840903006480d40070304c00d490080c01411944408900010307641e032002d030371803810009420b50800120420401c800a40c500400c96443d40c4141401031090340e02054035490071140c210954030000340b81500e003001c01d90055400e071001050099100e0f41d600e41c849404440003115132203440c400d9941070000324042c0f0032175849040c090001010024004014070004044400f00c07020341d02d003102c00315240c01d0061060000780120900c001c1ca44d004d44020950b070143c0020140040d1502602c89409000e141c0220f1400c04406102d110380d42c40c4084010806800d0500c01410064002d10998685036161 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618543929 1250 618542679 618542681
    0x10e010303140d05150301060f030503031609031514070503130308070c0206031815041a1008011505040b0d050c150c060903070201030c05120403120e070b1308070e0f130204 76
    0xf115024a440032005c0c40309076a150a200351400391403211065005581141c03a501e80d04e0100404a142a06284882d10100e5025101c076400459008007851541056801c994001c0d10381400865240c041c0c00c00800d403070500a01c00e89100c1d0505859030750740c1400507102120f29080c007902d00c105020f007034480345001d601c2e1a4003c44c8644100c00e40706071000b81c1d406415240a00103800e0350700018602c01070000188030354121a40010490f4030018141d12a403e86111740c203407070781c040043d03036107030100d07460b5040300f18454042120302c02c1b141007085200308418050800001040101250001d40000c01180303400421541504c3c80b0300803aa0400940c034642614250090300c0c003088550000c54040c0c115030749405000510303402840c003039090a45204100ca2600700250008041c0301e080840b4404d400c0c0340381d10591901d01f6040c2114081507484c2e1300c400b1950300c8400c01314940a807012003c25000d400150100450b1400c4002607026640e0703550f6607132503000240ca05100d0100c03101d00340b40580d0707031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618545179 1250 618543929 618543931
    0x204120309050310020703140a2609060108070f0308031812070606050a0302060f220f060806060708030c1b0313050f030a03081303180b0a110105010e010303140d05 72
    0xc01e0300d07107440003030815003050301d0075160240d4031850314010842c0c0b400180c0e004181c00c48140b000c0090a0302c44078800001e6890554580c1c20901c403150300d40103002000404004240280e00d02402d443c026604c0795490b0fa11030106000328460f507040c0480070800500114029684113400c000c0514681d20091f800d1410f000f0741c54200110400081001000c0c8501f600c038082c000c04003260030010040c42c0d40d011841c58014031700041200d817000f0514a00d0300c1003540c50010341000001c0c40c00400c0c2e032103980c0c0d080415110302914000812000c009045428400100c0340300320340141d00c180c21596819106500c6500c4280c210180699850614507034000420162a003904050500d031500c0d428503082c41614064590b103103100b42d03c20789141011940103070605030018242c451342c4614921b1801d081d101d1142501941002c42072202c000107011020300090400c1140d10368807104403494070a83d030b03130a80754217000320840c92003000d00410010303006480c00707201c940200000d20305102d80109164103c0e08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618546429 1250 618545179 618545183
    0x915020d021c210e101a100e2e0203031e0603070e040b011a1815090a0e090f0312010e0601030f150501180806010306020c1513051c0e090a020412 64
    0x10b02c13035000b030981290a00c0941c48079070310018100a648410404900d0105c4200d003031500408454484440d018481c80040c0c03144c40c40a040c0b502c20400644100c2d04920710a9000a01d051108035a00c40051011040364000d54080141041010f114413617000000300242803158036118040d800a0034120120b1260310032030140508081c15803504020490688031115010f1000208000000540f4902c0070139030b41c00c0006a615142507404d1407050121440f03030b0110907511071a00280000e020000344002d921404610095586454003d10b006c1da80380103440700480c40d484410014003102d80c210b500030303a000105160118a1440802030712084444004d085003141c82c29900501140d40c00c07044448041e44941806480c07189003080d02503d8444c180002011103800098404241a0400200d10f1a0341d40074000b051506001c0d140c1c4a141148010459541c050450203111890513105038000031005902c40011003000d201c00c224201000804030141036900788808076841c250144a076004038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618547679 1250 618546429 618546431
    0x50d0e01140a1a06070221010605031e070509040206040303051e16020901050a08101107020645010c140d05070506010f08120c030904020a0915020d021c21 68
    0x90f001194016844403c0165005580030418800140c0300d0f5140040501d040005130542104c41101842c05010550322071a418801c990320103802c0e810324010340542c2440241107034802030b0b0719018020400022140a94481c20510003040440d02480080c18088040021443c200e55110596080754000030590034007030000c202c0310011402c2c40040c0340e001d0182118054611454503180707a03036401c1c0c180407440010740c03550224020440e807a0140c421903036008080d2a20b075a0042c125079000e820441c0305159002c881c074500c02c0c0c903c02c01500003404051006044107110030440064031b012440d110100c60354070703240074225140300c028007400100070625130719030390b48880707a0408918011040e001701d00c03003e160580804c808a00014044441158510307a251508020580c00c1d007540030703c00b54950058000190780140b10341c030400a0064480341030100c64904402007040380d40351a03034451540980d0050341d901040058a482010488072185080400c801c007003040082030300b4a40b03004907009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618548929 1250 618547679 618547691
    0x9020d0b160c051009020112050106050c0d09080a30050c010e03090a0510050f12040201030c031b03020d020c01090f0203010c17070f05090306160e03030a050d0e01140a 74
    0x3074880c400044103020114642900e000c5500c2d00c400e9122811105000c20b115134641c245411a4000d00348000c1c00c81101e041000307603607528003020700f40743d000800301d840350b000f640c004042081c0540043d409452031300c0c00034400182141c1da4000080c1896215035200e8107070407100d203009000c0010301074075004540e40f0305032100d4800703000707509464400c04042e0f4207400c144500c030416120002c00074100c44007290030000f40e41562030103035468822480d155484030400159440c080710f500d1a10b0b801140300381e804012030307200030800720103c44604c00803402030740b0240c00d644000c40c071a4014100460a80400600c2c10b100c0c21005421541d00c0d074130480e800303030044d2190825440d083c40b81c40b11035901c0f402d12901100d203100c10b46014410013894030301800103c4000c124a0b62007071040e00c0f400c85024086800c1750904a0302e030410012030348420307400500000d4149c2021309011080d58141002921003509000d100c0908502415075803200c0260b5650b0381302042c00d07000c41030310b40300e014008588001500d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618550179 1250 618548929 618548941
    0xe10290d0b040c05090d060b0424031122090302030c100f060f0303090b07151e15050616060b091003050c060f030402040c170108151506040302120109020d0b 69
    0x680720f101d1503040a01070140140c900300d071900c02040e0079995211034009401525080090003d20444c412200c00789803804142417191b000e503035400e0580380a074a0a00000d000b00003042180300721070101c41010000000b654880441c183c1124000a210b401600c1c180740c02415400d207014400e800c41040075441b480441c1903c0260310a0f070700545406400074050904544000d0800c803c0780c410394103041800100c0c20188001c045a03542001c0418009024100440d05c0390780c8001d01103420110681d1929001d80e0406580100c103800310b80e0003404c181d08207041d0798203004008280701800e50305581c0380c0c1902d03c030903560b070f850b003a1081d0100b07180c100c420360850030903a1800c4103c0e100d0a008040030804869095106c0c025264004e504450100e052a101c12007101d4441c65030f250341010142070380c004a0004004035008040c03600ca005841c4c21907480383c2164900d0400c64078030750b420440401081c0054205600c0b2760301c1e0301648400200314124103030701084030305000d0742040e0380356000b00c400d01030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618551429 1250 618550179 618550181
    0x60c0c0120030406140d0609020d0c080103110d030507060e0313081605061b120a0f0206010506041505040f06090510020d0e090a09150c08010e10290d0b04 68
    0x403504249007081c10007400e80c1c59003507640303201d80d018800911808003180301000b00b01e02c0c1200c64048100000340201550344804102940001d981c549106090014540740d151194070b040e4102e0350029401145c1040690500c40c4c2d1652b40c000613000c00000300010004030301c060007460b990101a000540d9140003030704c0e01428006e0309030020300c0250000941f00140404000882054501c11607a03955900d5101000d69280440c60b268034480c6e00443c24030711425641440549921101030301c030384000200b2900120f13141c0809008a0b5840b4506200502090f051011020025811401c029213407c3d212028044280702c150300400018000c0c21082c401410020766544e000f2080c0e0001300244007000a01420b015040c03545180075150389400100709580603004401e1b003a4102c81030860f0130459100e10000b0b400fa41440f8400318810000020300c1402c003c103090b1090951070040c4400d1414010800345003106403100c8540428680b80d030007084603196008014604c240d2100003003007010366080c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618552679 1250 618551429 618551447
    0x5010905030706230d140609010b040f170708070b031b0a051603090909110a0b03040f060903031d0102031b1813061a0a12020315010815060c0c01 64
    0x1400303600b000804024194006490818807210b280c000b00c01012004136001ea00e004044264141d1800d0514021980b0a803e6000c0d00a03001036031022134070fa8031022030202034480c51040d4030b480c02010404200d640001c1060324070b0340b1041c00581d003085994100061400e144c0da0440101c0240000611507102040c00650700302c00e11901d122410191602005806030080c1050500b01018031081d402c205445100410080c21004504003c0e0082c030b810850120441909401e0240c00c414001040028054040d00e1140b03904c51030310181214940c4d5164060010100100e003071603120424248001600000008003100c400700041e2607141080f068440c003048099401d1100ea010804202c4180038a6600300e0058016641e507a031307a190085005000302801e603c4902d906c405181020700b846603a00c02403c3c1e0307415a60381c11840001e004042c1c0101d1200783c5801d070b030700068aa021104c1e94090300b545a407200c3c90412282c6200000c801042e41341e40107051583c4c1c40e8018412010340c071740e0400141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618553929 1250 618552679 618552689
    0x503130e060a060c02090910020307180503030309060c0706140f0402010e090c0415020c060a02030901020706090609030204090f06050c03071d031506210105010e13020d0b1801020310050109 83
    0xc00b62840c81e00c1d0b0050311100b02018080d000300b41c84000122000b20810041a441d45144030171942c83c078001c0ba00074404281c0c1e280c1c1800c0c24501490000b59403600105880c02000c5400c0601500d03202c1c6400c0c06d216501c040000c0394010346980c449801030000380301091003040d451000400031700d8203100041c4498110001184914800e20600071a01c60050030748041d1403100240000d21f040c101070591030505c0e07944801e42e2000000401f9010140c1c0800030342074030203003a000c0340c0c0e2164a8031001d4883c004940502c0c0001401a0300030005031800382c0004c0e0205008119038114109240c41d1481905c0c401c40c6d8020704008004180300c4402d03800220705c00000560a240e00c84c1030b4032040040c1e12900002407172611505400003042e9251b031340c220100200300740c412820310401e2020b9940b501910091160901140d82030700003c0010600364504007005a00030440150301e00305a4500b0802c074009401c410446c00f01c1c603130340342d1204001d1004500030021420040c0d0b0380e0346803000040810180d6000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618555179 1250 618553929 618553939
    0x809040506060a0e040f0f15030201090e1302060f0f1201030b0702030c0c1201112709090c0d0c1215050c0a05070f211106090f0a06050a02070503130e06 67
    0x200b40d8540d03510080c88004d0040c100c2d4041041c3c40b1400c1144060301100d03140550712483c00010000148141e003005080b41e00c03e03200c1d882ea42d684c40f03030010f5030801d080f030700d810345801103001180040c600280144a031034100f0031b1003410b000f4007100805642e04001d1404500b07240e400300510602c4003c40300c55501450501c0154a00b10100f04000c0d01d5071020000980180da00b2030b1503c040b1042900030000e06454000045d07101c1000f80440d100c561039a540c0f03140303d0803412020750301c1e45c00c01d486021b2044207410028070400384982c00b8002c9a035001740080e25200c41d90600840c5290258002000003802149490095281c0400e07107000c480c00940030b07484c0710504010794072181e508502a580f0898014241c0c4018028500b45155801f01303051955904500c1c0401060409411000c14400d6460420444006a56948000395a5008615004081d5102e54203484c009070094012503481205a8800f42c2424070a0b80c52902c1d42d080448048841c0950201c00e100702101020242c1d40326600b00d070307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618556429 1250 618555179 618555187
    0x604021203090d030302090303040b0703180801050c190e030f030702040f05011a0c121306030c1722020a0306090b1b030f13121d030a08090108090a0609080904050606 73
    0x2c005030103141c0c0020010141900070030f11051598043c026a130040404072035490381d604080ca0000c15980884100740346d0f180850300045414401485014410301c001001127140c9a40790306501d1000541003010010021b400b450000e80b61001c0c04018040742041c8029a200d5150303104002c10341d06442008844a450100104070807501d4400700100c4514075099543e84101a000c600e042c04c08007132568982c820700094080700301100030703802000c94410344e900f008055003000044a00445580a212411007070300b000c0f0744016111015120342010f00d4010051007a002d41c003181d848043c2e030780b0a50b542070b41d0360340c01d03000c1c0207440c46081ea004e4400c61482d07003203030a8504909000e000180203490100c40c13030400601081001101826078603042020340450340f000c1d080007400140403400d00d1015201030002e0511600340040d0003c04191b00944280c1050024001107a406000402d043e03824414103415001080a9100d42c0324060300a1110698403100c20b81488290781c00940b20a0282c00104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618557679 1250 618556429 618556447
    0x616080c030601230a081b2a010e060c04080106060507030f050a120e100f0207020d140319020c0f0604080604020d1b060e1c03141c020c0604021203 65
    0x1034101d941c4010242400b034802120040301e54042c41d10307401c01c1001c1540004580140d190001881d510401000d105451340c07000c1c01c03001680502405d05010032500c01c0c003c81059080c641540c09040d0780420300001580305200c101286840d00544c0c8203da1100000350a10100c5800e000e01c40140186050043c030b0b101d002d03a00100840a403040741d00030880301040c602c1481388185821400113030525070a100e04850311751013940b9048481902e004403440e07d212901155a24001c1e500e2168004080003014034540c0c955840d147c50010300400c040c00300b00586800c0540c2c40308030105144580c0d00030024152140180300e0416078049000c1d2150501f4842080180e8000505c55402a0b0645450403000c80914181203070102a11206084019000020601c50b60001d58100d51020444a40d00f407500503200701c003070300345180c0310190014850100d0380b1703141041d01c0c0003403803c02e07410b2402410246004800c4412a00108654101034200000303000c02d500d07202c2e0795441120b40340780195251245c45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618558929 1250 618557679 618557701
    0x1f03030203030135030903010b0108060d020f0a05190e071403041b0314010c090b03010f03030f14070605010315151401020f0106060e150405130f020903070602061608 73
    0x148210130309100310449684002c100284103c0d8001c1c4881e00070002d0024610902c0c0d202d40060718214060761034550301140c50341c403031140c0d0b40c0146801742503075042c90815028090710101004a19800072040781000810b503c03080e080021918400d1026a015801c0c01404030744648040e004200300450281c0194140303d030102181d4100c2ea104554148010180818203401001d5603c0940202e26003581009510010740145c242071041b5628410015203480c04134500b80028090700400202414007440003034001c8a1003254006103007000c000c1180702007042c1207154046c40e0100c55040e1110300410411007000c64449005640721130038003402c044e40e00602c0984245128403010802040706500c6164000d1000745401d10b0000d00034412103071908000f5100343d043c003074480e01409454545c1401100e01105450030b40e040200011a0002a0341807030019160b0303070200046441d400c018014885d5020010300c070092903a40c000d42068030701580010096400441103509100130303207040107441c60340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618560179 1250 618558929 618558931
    0x10020c0f01050d1815110408031b03040b07120e030d0e041d010e03090a061b0204020d06050d0c0602061509010b13030b0112060f0905060f04291f0303020303 69
    0xc00e00e060b035212000d440141014004031410783d034140c90114003c00612a00c110070000c1d400c003290301400301441e488000f0300300b8070030b510031030295804c18007a00034940400c08001540200000c21641000d484044621315035219120482c0c407490044040390420750010324001e01c0800c1140500148144010080c2078810840011842142d41d56103172900021408903c1c00c9681c220710003003040e02000e084c076540c0c9a000c1408944a07246980000030f00761b00c5072600b815810413054446110448036070a01001e50084800245865100c180214441e22082000e414090145e0b03403038030261745002401790605002800101e480c1c250f414103c00251640501281103503c0c0d07289440e640c0615416901c1d051310b035a0001052a5843c3c400080c6160140f2000001d807401101c0400c034076404d5003120307011546e1601c0300070b05680000f00003035251007204c000a68098014114000b110484400d903c0b081646461152040c44245040c091041d1007829945010718140c102201c0560039901c004e580e03800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618561429 1250 618560179 618560209
    0x50111030a0f1b1b05121602150a0221040911030402040507030b060405061b150f010501090e0f07030e0d17060306130b1815010914010b0f0702060c06011410020c 71
    0x110044e0b0000811000b00003500f4454101080c2d941c503442c0c0b4070700c221980c40055505038414506080501c030391304000030403900441402d40040400350407a0402e0b814a503942c200400301050207200000d040f06080c0500310080f051f1a81c125920700d054410007080300d074090f052004140c5088040450b0761181c008603000e0798030440d503240c2c030b821102c45000c1890041180d0880c060140c1050640341500c400100b0f80500a41d4012018907a01d40d4011150786041d846400b140302041404140c1c5404200e44440c4c0040c81403030b002c075901e0000a003140c13a003160721800200141c00e0b03824010000d034040e141150801e10850241c00a4141a510403807101c01c0104083c0031064a040450f084241c2c0c400d6464410b8083c0d81680c1c4803200e0240361002d001c100b403060b6521581005080d00d0401111040b207410380d407108100c80c0c20070305050440099500480000c0342c12074000c1003a2164100101706a500030310000c00c6410340740212038140180d90700c00e41400e03015035108015642c0159900800c0c4000b02c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618562679 1250 618561429 618561467
    0x323090607060209060d0204170c10080403020a020414010f0f08030717070b090a110607121101090605010e0412020f06060f0d020409030c110d0f020409050111030a0f1b 74
    0x2103141d00b424402881214601e1783c0c01500000e12500d9950180c0250046800607800004001074800b11680c03070347c0e41d07120220790115000890101e468002d5282300c0c0c0040c0244100c2c0d416890b10b901081c101d0398400309516044641200400104401c404480003415002e2000e070a01d9140541c0d01d5600e006820b8002e241a2480c1c241141640341001650008c4e0b402c54160380b41c07414034842180d1603d044920a40b1407000c5568800303541d08000c8210341c002d5500c443c1c8030045032510b1204495075010010f11000d035549405090000c14201c0c06460702821178a2121200d42c10203107008131040d035400e6801e0055400a00d02525000c80106419600c031800355100b100e13400208001440e04e54000d20029071080c90180d00c10309040d4454410706444c1e20031011070000c00101030400c24200900f2000414104110800314010f00302900700d020054414800840d04248850000c03926800403076001c003520b699180c0340454411140168224280240c00250188003481001800c00c001300003204161 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618563929 1250 618562679 618562687
    0xc0506040b090a0c181107021309051f0515031515150438090621091606030209060304110f0a0612060b0405010c140c03070e0403230906 60
    0x2410700488422952004039410711030780304c203a044041100500c0e17504c20035241508940751803c0000031522150b40013800040c0e0309100780c2015014148550044605005140350020350804813004a8002e000811001c2400d10f030203013084416030910165540310740d2220b100d00d40e00e5020b117034085410010384210a203444175030f0401f00381c5100c080c0f06a50043c1c44000f800180340484654510b600a507003013038611310406841c18000440740318000e155403900d81084500d50900d044001000d03411400c0340003070b40c103258180c0083da40500444481e5040e400408100030418440b510102c080c040c203041c11424002e410703000c988039004c0204001c01c590310ba16003420035980c40d41a0309080c0c1000400d0402096110040103150860319600708101c282130400216040790920190b5042d908182d50f20400c0c010700e40c0ba081c0003007608001150150094030306240d07454500344011005008080b079070441c2820b2614004040e100e0308452504031401000c040c40105c0d0b28142101c441c10300882d803171511 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618565179 1250 618563929 618563941
    0xc072303070b07110f010b011e11070801051e0f0601080c13090b040f0912140d020a17090d0f050a030f0219091203080a020f091018060c0506040b 64
    0x303103100301c0078090314030180c9004021402d0b5100060500070103090050342c503901400342c0e400d800c0c0e4603010344050200c0c3c0076200c0d148244084e01c000c00580301071494144000d00d61b4088035803c09503c1d0700001c0301030351200300708842c0e850880d60200c00701e644220035440034074081540d4101040064a183c0c108402c03400031411001c1c04070182d80c40c03440c850744017004c82507403009002c1c018030741c0592043c0141d0802001040c6910346108000e08544c01c00305000304c90312048401c036258944000d003080c0f09031040c00140c0400c85a84003400003a5071035118903581c005a042d072500c1a0400a002034002e900405041100e25030046120810b84ca8030700301103460b4880040140c015041007114103070410b00c082181d540a800076160f556078400135444502ca0180c480d055000b414000c0070005d0003040201020600c800083c0c0d0041040e0f0b0f0441d520030781440030440000d10400c2194075020300040300c590380c17a1400c0c1075800b0a80000c1c4401c0c1440b02180c0a95603c103615684002c2005d0b20b00700000e400912 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618566429 1250 618565179 618565183
    0x3110108071e0c11040e190303150b0d0b09040305091e040c08040209070203121612111e0c0a02040f0603080a0c050c040203010609030f0501061a0a080c0723 69
    0xc8403241006000e000160b20300390040140e0103d080540f2080900320480320107041074071518954110721001707480c00e40c2544150300100c61480004404140da02c00310b440b00c0e05210b807240c00103043d00c0140d2641d503014004803002a40c030801075051180e007a540900002035080002c403903042c44191002c0341580034401d01c2c030302c10102c40d8084035040b90400b0340415140f85c4c0111a00d10407882180d5400940d260018100d03a60b020300c00b40e0b5200c2c03089040c003055603c0300201c055a284800791910503102040501d01509030307548442c0b071700c490290102d07440601090400301c000c1c90701d100020b607030300b031a851068440e03031071050380030180c000da0b0350b0f0144146100c065080764020b1030f00012041c2d03994075055001846020404e07070540302800707034003810f040303900e040d0086904954050ba0b03030042043c21a1541d541181101781c0840b102d66075807100041d0301120042c8403182141d0500e05a880c2c1e64005005454140010466040c0e41c0080040e1400224149003d0300f00c3c0c00c1c00341d901d8910142c0303040824 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618567679 1250 618566429 618566447
    0x703180212010209130203010303080105150c0706030902030c030a02100e04020906030c070b070e0109030b0c120a020a12050103020a150504080a050703110f090106050f04090e250311010807 83
    0x1941254544010710140101500108141e03441a24015010004282c2001c1280001c2c0001000502c0010041003035240c2283c45070024a00130310014507210600e00c0181c68250103130312050220707441b00451400d524050180010250090300506404001c80e07001a03031500800607042c06001500d0440481a200d83d0f0640e41c1262016201d19a2410f01d041845504d030002d500c01c841c41d1454000198507284103850200d1042c3c1c041c0c496044035401c656402c040c0c504028501e41907500280800c4213243e11950019004980355080142d550740da41000402d10507201121000c10ba05000040005865050030801110140204a410f403211018101d400b403046902c100345038410000030300144800400c3d1001228841c0c2c0d0082c411003107000c03e01a0f41c0e044001140c0d400003980e40100001d41c01480201503008180c0019032901d40c6480c0203100b101d01c0141400c00c1036009824488490150680214202140e41c4007280054a9a510641c240720701c246080e04209d030784808160340e507018001c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618568929 1250 618567679 618567683
    0x30a021b04141603061802121e0105040b04180f061508031921060f090504030210090c080a0305132103230c0105090706050310030311150f0a061d070318 67
    0x4498001b00c071407085011b03412216100c10014513110105607e00401c0124116038030344d41c08119880d03071a107070130031004000c400661a0040e80350840019a028516034659002d4403034580a094034245080004c21102c01110140001c0c000f001e080c0030301d040000565407200c0302d440c0303c58a41000140700701d48a181140f09003171280c0070074404211940c0190800d8081d60814060031607580e03942e00310f080035034034243c40160143e08101062800003032903400070907881d809034000e4010240e96010062400114070000c0c0d0000302c01080c0c00854401c0a95684000c01e050840343d01111006c408048890366a03a0340181802035001d034003900144000070004481035200c000c80c0d00c58210360100c07400380a044445031a45c1c0506140400c55a025000740c17405034035885901030f45c0c0c07411603405913044144e0030044c206922640381084030501e140c81d48180324a410080301e0035182413801007102070341d145400c80f24981d86001c2d5088810300700720b08295400352052a01142c60802610118910780c0700c1940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618570179 1250 618568929 618568949
    0x2d03070c020f0a0815091204030f03120626100605030316150203010f03050d0f050d020a09050301090f02190e0403050307121b0909050402060307050714030a021b0414160306 76
    0x6090812909542d4842c0301d109988243c7d6282d503e602d04005040c0301e140801401e075000c0744849070229100c0c0340c2611040c12104400148903455170484540c040e94a070949140a002c1d6199501d120f030244143c08100c506140c080c4072a5081100013900c80c0140c0088816415050264009014a002c1b044580314505c42c800c41d5a561a0209100341a0103800242e03120f01c41c24000361318051154201e2180c5010581e155800c01801c01c400340c003c1c0d40490082401c000c2e050501213403e0303a0a114030500705200d60f98400900d0924030520411114001107142800c0c180e40c4c003008200000e0601642c002c4d171501d0410390704d50750001c080d64a6420303c508410782e18075010500240840408101550418645030403484036510040c074402c0e00c0044a000350800020b1010a0900f8003a101404442d480b4800e14024541c92040c81459034103c040d400c0010392000e10300c141c11815a401c0a0b98401d0140c1c2e080c801555060140c58a40c0405410302e404035100b41c450202c0310b48680c4c007000280401c045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618571429 1250 618570179 618570193
    0xd020d0519080406270302011b020613090605010903150c1b23190206030a2a0e1f110f030a1d1f03021602062d03070c020f0a08 56
    0x40500b00e81d0043d014600115881c070100c403280366503030700a0f610160f00c8520030740c01246c1107a004440104000c0c2100104500010304c203c01690b505016041400d90811122450b03860100c0b000103594065124505102d01d05c5000c1c13010410900c2d50044c80e4000c070394080394299070b5903400c4803200c4048070507a242c404210310300c404016040d2a01e481684a40b05140c00103824400b13015151150301c291869a207182c0d42d4003d006061040c00b0310343c000b460140c0011026048894001007031100700e030a144001202c0044001f0b0340d001100c14404010554903145018070304228028861002d015203005c0c406120b05101454804000004540c038200c81580d4071010641c40261405000e10742c2007420603401328040c5900c1c00c00391046001511340d04640400c050706020709800940c0961a0040589528103401015071101d8004100002c00c24161200d56043c0d06440c104508460402650941007003090100302603000c03921110903a01250400c072410304900c0090904581680095024000e801e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618572679 1250 618571429 618571433
    0x6030a0905010525111510090501080c0a030602070507080d050d0506030f0a0b100503070f030b0f061e040216111f12020703181e0509060d020d0519 65
    0xd040349180300e2040c402481a9128101040f441d02c9840c0c4202c420003480011841c0e55a1045406805010740030302a199002c0701003680f40341d104411a85c8615407880c460040140d449140700320350051940c240a400f01c0d4864100046514140c0c2c40040e005680108007103050103c00c1c09900020709244088950018410002600d140c000c00c0d16030700320515050000b40d50b0304011441032200215140684040342c0d03240d50310301c1e6400340509039503401a80540081400d4400304030300805006250340051104e0311714501014072140003442910792607121400c0c0140ca440e0040304400b1080c81c28a140e04811510011a00900a0898016421209114403400d11241c0c40048078100401d44e400140300c001d00124107020940c6030014800941402c2d807002000d900d40c0d015114607480703031a2105010031291109411048241c005140d040700540340e800c00411f1b50740b0a4001040c0a407540e144a180a4001070007070a420f040103801440042c04917010418140510661081c1c017440301c100d002554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618573929 1250 618572679 618572681
    0x120d02091809010b120a0303051308030a0219050a0903030e01170109020703020d1106130c0b0307110705010f0503010519030b0c04030308070305010323100608010515040501051c080906030a 83
    0x142c6110350b56500e00a520101400c2c8132a40703150030b92949000703010003440da942c12001004004e1445803032105001d095000200c2c240c0095000c1c01031a103025854895008410801c40a056108014002c080002c43c0c001c030b0300902030008517034040c14020b014602450060b5202c5e520000307145062749080c0008146251568080c14059000c0d03821640c1d0065590b0303080e20b1101d00c3c180040141c0e4030080010340003a1079503a0390b80c419407150424000303043d900d111854058109441500204500c84405040d2010400104000b04400d01e07181100012030600600903200601541d8000c021908610160b42c00c10f0403520011030380b01c11402010301d0a5410f500c8a03030480e00080300000d2030032021585040c03103401594140c0350010342460800c0307085603002c0a8107413200d40f0f84985010301d03800c841101046108010003401d81400215491810010420301406030f00e1015119519007801488582c8481001c42da94411148a100d850b20950034200d40714010650310f00d82c0404000201b024002c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618575179 1250 618573929 618573931
    0xf0e0f0703061a09041502070b04030f08100b04060522030f030305010e0c160f200f04060b030c030405070b03070f031805060613180302070f1403120d020918 69
    0x82d40701000420384030160790400010700e0b4046a4003407445070108012651000014003400080500103141c0602c0c0d6070780c441d0014040700c2c10790100d40b00c0d0070715120003a0030403c242e600c400e00c881c90310441c50804002041901460090f102041400310b007040c0407181100c5031508039800140100c10b403942d02d02d032454100015007800c80000341840c00001d0300030b0404951034021294079040fa41481840300e00c2c0c01c1d2120740c040095031042680e40070031001c54080700f0360246030010000d0280c0d0001d280018406070158002c0454011881c05504000e90300c6a0025250070035110f21400d503480d08c0303500300140350440f1908810314448000084c050900d4000220324041c044a44052141c001c0d480b0052089060800b8050041e81002c80040d42d980342a0446485003a087d44c00080c0c60411b0720000345110f542d0610881c05684828024000c4819211022009001c0c0c040220b40240c501d41c00300fa1103410b10341a070b110760b0714042001d10b039805560301075501e038070360140c09000f01c1e01c4008500510210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618576429 1250 618575179 618575183
    0xc071a0f1e0411060d1d0304080106080c0306010608180f01020301050109061b260c010209030616020d050313151b0f081305030408070e040b0a1a01030f0e0f0703 71
    0x818480391100e41d2501001d102d035400114101103441c0450603c111a407008000c00744050b580e050080b003c61000510b4140303000050025600d0384d090101007421554a50418a510790001c80b41400740e903000601300d03041da002c4e890110203903250f00404880814881500c4109030080e40c002c682c8a0405601541c1200c01c241d0b100746280b07581315800c0c0e0740302000f85603050f1244020300921012401700c80c0490305158604558114501c0b00ba180186940c01501c0035400c1c136500000c2d030a0759840d0070003c603078002d0391342005104854500000a0365440910300c404040c0040400080c1504a6847d220003030b00350003612045107100034440000080071440c041c541c502c0600004140e0091243c212000e50b0030058a40714a03607224501074050807188018126500e02c020400032655101c14060000201460321600116092901d02407046d004000d1103000803601c0e280d9855158035015990703503103103d02170078000780703101c104e80003807010784141111000c040c41071703958054040360f0000c0c1c66001c4034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618577679 1250 618576429 618576451
    0x90d0221060c0a260a050601020f0106082d070e06010309080304060c02100606050a05161e11030c0616020406050a2c010e220b0c04030b07020706080c071a0f 69
    0x5044203203801a40302020102910413818400043c8070b544a40d4443d5401510500440e88007a071480403503801e4a105410445c0b050300070480300c12900b0840a4003095404040c8000c09400010000352580c64420b84201d00700282d8071070210322180d00a03031180b55016004080c0564901c0c00d400d14a0140c48045440e500500c2281c441000b000b44501c100b00c169030f159500d00f490000e41200c21265070304001c50184003802c5076018100080c81d10081560710114041c41c0742d403961050300304128a40c0c10280414000e03000108441415034a90046401d074404194800307030044841c3c004180107108907040260440020b8201046040300c0c0c80b0900b420710001003560b010301c42c06505418224400b071042c0900c0d22284030100344803030f015400384003185070b0880b24462000d1054031a100107040a8400802c1d04600181c00d0080c8600d103203010345c3c09034a500040100ca8900900180501401050380c561040d000c00c00804100c50324a680303120941c60307007075030b22182080e44044850210070780d0080410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618578929 1250 618577679 618577697
    0x23a0603060203181209190503070e061009080709021b01051503010e011b08092104050f01021501050f061c0e0d020703050729160204050903090d0221060c0a 69
    0x82000025004100c005d012081810400c1407400e0010380744002c5518003071251844000b04094404008003c003d0074686e220042d03500f040c40c18014a010b00038800c07000c0210b91b0005100d80800020940212007692400507900d20704004142da018040c810190ba0550900091105075144904040c00c4504110300030031005064000c0d4500b29416804914886402160b07107a403403600581e03a1951108500781503401c0291520f11213501d003045008007003180500814140074030f0070075030031941040c0f80c00c0c001130040224451807491466030500c40c0718820211248034130391075103e0300b040d2205100d02c4401d5200e54034003250450090079189013000128800c800f0040081440000c00800316030300306d030141021a0401244215080e00091a03ca404041116164151080e00c000b4261051450503100d10400c152040005075000a030290120354400d0040c4100c03940c485942c4103496904840e04000514000b88000c89103158041d5081c043c00b8180802081c01c8841d070040442c42102d6840c0004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618580179 1250 618578929 618578971
    0x9090f0201121406060304020402070b0a050f071103090d030212040f0e09070e010e04111c050601060311040909050114040f1202120a110a02060d0606030b04023a0603060203 76
    0xc40c1d031010100c3d984612020003003600c60900e2001075400c6400600054600034564403a0041d03140103403982c6568075601c1003004000068141d81e00d0b0810150b2902c42d02014030701c400d40b0303a03e01641d645548546040d100e40810503008025503190740c140209c00c0d58503140c0e1000d0203002105076110b03800c810400c91001400b030032b401140c2c1100f0f44128260000f40c6901740007440102c05001442144c0c1000c40a45150166079600d08a600d40e4902d1101001041d84614046040c81e03c1030b4040b80c107040c10144158945482d14080c0c400f42c4250b500c000510038101d0900902400010800c00b00c15142e00d0305000900c1040d040890301e060245c01c61038281e80b5844822603450301011a4044070705001e000c3c142490b44161440010a9804021507809a100b80c0004d0080c0d88180d03014245665076150070170180c3d0f0140983d20400e101142e0840c10156051103036542c070710103589814610071602607659403005c511a07409800300070401081103ca03840c1d00e80b1034002c1d403060b00c080440740d003c5840060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618581429 1250 618580179 618580181
    0x30b010e15040303050a0c0f08041d0f190207120816080402060403020d0213060602031309060323070909150f0b0d0b13080c0307020f0a03051c0909090f020112 70
    0x480c680740c50038140c03401d8507540341192160005030b5540c0821a2032038003500030611428082d08007600800c1c240e0341e550b04d8183d03c041200c051448d54000081d40c2d00800a01062401e0101d034003440d075010f90715032421004079140c000d219a0308010000c41e03111041a000a40c491070321841030040c558580c0d0a0303412000161b035483c004035802584007000b00300500c01400d184032030b65555440504064034101110504a042d600541c12400c0141d00101d0143c5166442c60213a000030840b1450411210703085459068070011110b0022840003100c908210038100c2c204407040c0101002901040440a1031902000740300f050405071a4441c14005d0000080c3c020340f25481d04900001c100030364004140c3d64151514038003c1c080d00000549010b03c2e00890818801044e00610361009950f45450350302c1041045000541e00600800f2100c50600c001000040d01c2d40f50300d9000f140101d0b06584104048407001c00700d8019130005401c1403c45030402020403040c1040380d2017604c0d030640f07178005c800c0c05c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618582679 1250 618581429 618581449
    0x6070804080a03020a030908030f04030815011b020a05120307020a0608130f06021303080301030507080718020c01090f03020d08090f030703050f04030b010806012c010e090a0b0106030b010e 83
    0x1414501c420401810003c0c0254010115020241400b207111041c0f0b807100c108a0300204c1d90440c000100400b00420036a1110809902410b9030310310120071140640002c2104141c010150500c240c07035440074040d9900c189144000700380080c2103442d4008050449034030ba400c000e5080380142c4051a02141ca14012030032540300c2e02001e1b020009a5006860b483c4203d18503403000d07110305a01b001096080501c1001201c0503500541d02c20750741c0e51440c500585002c020760700401050300805402d112010007040300b03035683c00c6040360150b12a084441d055006000c00d10009111406400c1c0000403d5004039005e004e10000b600d5a501c0ca030380b030511598070b45025040040c05031300104154070000e4002c2001c0c0c90700d04060f200b0241030944030b6031018220707902a0031241c6689e1162004100041c0442d00c205940034940503000b074503080c580b05175210f2500601542c80070000410001780d40c824100405040315410407070101079940d40d204081e0041524000305da0001d2001d9503c209141010b03180f0b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618583929 1250 618582679 618582683
    0x71703070b0c0703231804020712110309040603150506010905150f040902030a1d1504350c0c03030301050d030806030a0c0602010f0f05060a21020909070806070804 72
    0x82001c556a654140c1240e40c0003041c1202413200e41d002240e4544c50302a00d001c0a156018403031079807070b0000542d44c1000e045002904c1d10540c0100b04d5403002800e03a91103c0b07901d13140c608250360302c0310041043d6411400f503040c00340e801a00d0100c0001c1440198141441404581d0908005a4491800441d00011140520740d00305640800c3c44890802c042c0040032080071090040b410241c64014000590b88291050410540c680901a80803203102110a24071002c005c002c003419900f904040011600050019000f14200c8a0000c01c2c0d540520b1024214802040d86114400e40d0214984880d0021101040c540c4511452030090b4180001182e06035140184031401051040d503089070108402000a505400f95007004030000e42502d80301710180c1902e40000c00d10303002019820040300c41c2015106881030034031081c00102c0c0c5502040a05540304071200340213151103d0070856452501080007034008250100700641c3e541c010440c3c0007600c11140c2541d541741c80d11001210341040952740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618585179 1250 618583929 618583943
    0xc0513052703120f01030c06050a0c020f01030f021314040b0f04090f0516081c0512090c0d11040f0504030207062a1101080a1505190302040e07170307 66
    0x1d01074008000d04201180301140421246000c08490294002ea00c1c25110000c0110380840144104a03160b95084081c02ca286440e600b8616201401000c0c00b00f0184040d004409020304043c0304d034400d8221b11290307045d07080159560b5030b2000403045003011038455891058500c41c4061342900d014010350f02c4019000b803180140c1d03c030042c10400280b11004e422910056505520800600c00b40026921140e44150340e6036180d02d480d2030703203091040c106070b52000744511030100042d09030460155190110400c1c11030780d66590301d0144524001140d0242544811088090001c02c4240510188101c2042e1828032064400d40c80400603607406480c000d004d03800c01031007071000d070348980c9555503000c0046000b02c078413501c03462025101059014090715040c0000c0200e20b00c0d07580042d202c035001a060b9608200e80101610407900c1c07a5654025107100360107110040f10418600010b000c05150000d0040100c12020f0512079516260703403048405c504401d041d0800400408401c0d2011681c00940c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618586429 1250 618585179 618585211
    0x7050102031818010305061923072a050f0604021f02070b07060606030509070303020d05090d020303040b03041e0209010b0307110d020607020f010e071e09090c051305 73
    0x2d20580c220601007009a000300d40f4040a1981104425480d8002e42c002d5000c2c00550414002e1054003952080c400940c0500705401b4039102d659001da21050510b40310701d0a03a8940314801c0032501f56540460b6411504840000c91122100320349030110b00c40c0c03080307048600803034070850155100c0d04c046034045c0d0310001000319020602070103010300240d01000c0c4107071403103d500c42c00f00d41590b40100c0025502c1703d0f92240b00340600c503094440c05030400c5034800207090071840e40e9030080d40c450402c001d4000f00400815101c3d80e1703031502943c040005034001c090329199500c94030f65000f1500111010764554503100c2e1015614031003800c00145041d000341c2190540e030300308200000c00d6072001e000c5104002c0c60300c90000c40e0309001d015851500e0261340c050300a506040100038900031021100a241c0d9240003441104c4240000e071410441e06403200308a114421b06201161480c015845600d4182c1488000f80411200c030f0150825034908881c4a1204054024080c0c220740003100c0d00101049151 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618587679 1250 618586429 618586447
    0x101d010b090a090c050702040606021b04020c010e030304050a0c23010309021c0c0f0603020c031e1c0203100b0a0219060b1e030d0503040c060f020a06021b0705030705010203 76
    0x10000c0c80c184101802c1d2501d12a0781d5540c1c681103c940409240c001240404d000381107113000c2c040d4000802441c0700a00110342211549040103402c912a1b900ca140d00040ca507050207000e400c030b9015445590309581d120b19140c14055200d0b01b440d01d00f10f61800041c0307008103001c0041c031030304480d440764422000b036403002160040d4010881200c2c240d17401801501038014451100102400321407148095060b4140f9000740c002d050500c54110000303060051148180b001000004c0d6082250803d10007010341d0841c285205c4c4501c00c1c8409840e010040307007004a0a206950000c0d8002c91a0010380e442d11507890031420b4060040b400744600580091f59000012840d642658403007502541d0009440140580001c0190b01c404503020410020860200b180b89400d00070205038205604000d807541c40d159480f800b046286020f85800e00a820108581103882000360120265204604541c0c820190251032082200c107102406c0502c40d40c2c1c00854a41000303c1c00a044683c1030f0002c500b4402c0c0340d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618588929 1250 618587679 618587699
    0x60e01031b151d010918020f070f080301150e061219020408011e0e0a0311030903100506031c020712150504060c1d180901090c0e101d01 60
    0xd401884881c142101081c80c09120940400e40c0c0010740710144201c401400b440c514280da800303002d05200d500351040103130008010000c1d01900e6041ea0050ba940040019840c581c0107030302c0080c041142c007440313010821000c980103505803000800c14a010740c920140844520498200080d00404280543c0c42e540ca20b119000d03801c0701004442010a25280c9004400ca8119074049041c076910344140c9901c50300852145103850000c04400d10041000701c00d410369680d403028000701080000880001d1241041c01519500d510003070030b036144130004420f060068903054a04038403c0c042c0741c038076610328907100345072400d44202500501205480c000400c42696110001039840340c1481c204495030b100b03c3e01c2003e110328424580016907110105005003210407844610404005c10340518826035159420f80e10140070b200c0e400000d642e1050409405480c01e010014001e00c10b1180101da10480c1c0e5400c42c0c8140e011a13540807400340e84e908500320100c03008050140410403280140005640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618590179 1250 618588929 618588953
    0x509030f070f02130614091312020a0b0a0b09060108040201020703020f01020f0a080a08010501180b0307050f0d0c1107050108010e060409080307050d0b04050606030708100b0703021f060e0103 84
    0x612003103040050b2500410341014160481802e00c1da9100d1040c44801302c20b40041c025030344240c55680304c6240c240e100b0000070750b0084000d0140900756400c034004034070030014490000e61044041c041e40c10309401120140a19041c1603200e100d40e08002910365110308090761040360141d00801000e03181d502071102c03803001c188800341180214070090ba032b107110400040c204507100c0c81c2a41c0d61011020402404d111068100c1d0381008456070f050700810709603001d813000340c2d0b40003070005030742e92180c0c1001da03400d12940c50354050000003c0351855841c01942d000402000c0540ca07948910204448800e84030000e90048501181100300140500901c0c3c640c2254001c80107000050042039640340c11005402c1100d4810025000040c194200400c500510462100c21f40c0c05000f9814000b0026075240001004a0208007000c3e0004c1e41e04451802c100d80101720b80090141d0714000c0b0b05000b900d0b01c801c4d900301c0c241d49171041d24450310381c01c2da4442e180c200c0780401d0502007140d007150303034030030040e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618591429 1250 618590179 618590183
    0xb1e011202070b0411010f1413090c050d0c08010524070209010806010611010923070f080a0b06090907120303090506011d071d0112021603080612010509030f07 70
    0x149442003000c2000314401820030a010341a001d442c0e182501e0030500c0c20481400d464100700e40b40c0d4a508400341c00540c5041c0321350350315250582301c0709a10350071100e00203a075000340071071030400890104c000e812200030004a40c500c0000d02a45c0f040c0c01054440800a1080703e07000508418110300700726008904c801c02c0c0802c0003840b0301c0c040154001411b074240c20b0700075980b141c00c941c004008064008208800c481d105500034803a0718000c3c2c40d610040f500e100c80c0190418218449402180000c0c0901d101503c1005ca00350307403103900c9000d00c03995001e1a00c0c04441080c001004a40d0500c2c00c01c0241e44510000f00007000b88600305020045500d800040c00c6043c991101c0151313000400c144006806000e108003501401c2451860021440c1c40103000f013030921101c200d4090104402203c0c0e41413541d000c2c03d100e100b10250784203540081c0300d0064064020035075180000101a400340c011030140c02e007120741e070f03006c0c006c46d000755801c0761700070f803182c0b08154020401e10002405910150803918 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618592679 1250 618591429 618591437
    0x15030804091410060e01050f120709060c08030412020a0606090e10090816150c030b130b0d0209071701080a02010f0207080703020f060d09060504060c111509070f060f030c030b1e01 79
    0x50f000d1081911140c000300400100d072703112282080152540802c40c64010040c61800050304c866035141c4451030300c00a08050946504040c0181042d4000c002c085042c070b07801a400c00c507955803245108014800e4a01b241c4040c01529119949851980100300150313401548403032800303100380502081d41202280441d241c99a0701712441000c205403054440304205600c010035140400420007000d0108051101032891401d070000a050311a62110a40298140c0d84601c1e0303034441d42e00c141c40d91941c20110440800d032643c00442c4050010640031102072003a2074651300d4152004c01a62668198054201c6507408541c04001524050309441c0b6405800780a41d45003200040151098880000c0e040d1160364660090000300324540c4540c420345441490405000b8245c5550940c450717010b074000124480c000c0002c01c0d103803034090020303030001c042e20a5900c20311035441ca8003030007410011135007401107440c1a00c80400036019000c2d120300340034000d2580310040347c030152071100d032040030207014100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618593929 1250 618592679 618592687
    0x3150f0c041815120501061d041a0c09060c07031101081b0901032702011103091003050405010e1603030201060e15190f060905030c0a12120315030804091410060e0105 73
    0x402038003101c1a803441c2c0518000b0131103504180c540d4100c0d0608000280c50488c18200308004100c10490001708485c10041d00d1850381c0f6171031810313866409900d01c620303406603000890041949000400c0c00440c2c1c41403030240b585003c0d0380010b442c2c0040895030000d03180f41100988120200440c010f2031780b00310506000492450b401c0304c10f01040d0700d8110368401070000344d10080030340d07802901121000c070000c40110b04c5c0904040100f89040864280301e41451307124008a01000001c0d0040205042c2031011074503500d0994140c281c220340280700603805546810000710340070711600c44640c4140301d03595040802a006a040c402a00390504040c0b11302c49100700040307a260b84880b840d800510b12980d403a03e965040c44e00b0107003011214010903108524010040007034041c07101e140509240c001d050a02d00c1c012941d816009002980f41507a03102084010200070005d010300a001a20344031036081058030501c00d2680c00101056a00c200701c1d0103131040c20041980b081d030301407010301010b252103410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618595179 1250 618593929 618593939
    0x91314030a030605130603020f01120902030a0803040308150d020603040303231b07020a0b0c030d021909060e01021c0201110409062d0b09040b03150f0c041815 70
    0xc540010380e4000c002500c4101c03c0002d4505405403070810808080c040002c1c40c80e42d80050071600b01807119078184196801e5a04140d0281d500040301136030060161a03d110f80c0345010001070b401120203e010403203080111711694101c00d00300302c1075000509508499659502000500d400c004d00450401d9240c0d0f00801d5440c1e001030f8592440b0460160012090a11581441d0a401c004500750440507050104c040980d403032840c04030847c0c5420444903a80c0c80c0b459000c50071480303642215050315000103500040070040403c0490010401d0307950384081d0b51101c0c011140580d601d88064016840300d502010b20740303120155841d984044e4000003038006501343c0d1500d000c2e049a84022409a45c40c3e400704440c003140004c2c111010300c3c940c03103814500e00c00001d0303d15058641c000c03c4003100003c10403030001e0320750382d100c4051004010200c07110351a281e176248080010032514031484115060200700c000032044169410390702404c503090a000b00809900340107044054103084081246800068 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618596429 1250 618595179 618595183
    0x170d0207060b010e15030117070f030503130b0a0503160905030109051015080a0303020c032a0705010e180a14090d110601060e010305060102070504150305060114091314 74
    0x50903500c14500030408810001c005048602ea00c80000d015001916080f19242040c00407681910450047c01c5861000603440030314000c00c5800640e55090200001320078000c000010b4181a40d034191004c040ca0b8445031584110b0245c07840f03560224509001117154240c40300200d10030f181d010710301141d42e0b540d240c0c0081c4c00e4a503440400c1c0e8454025001c00b049902d600e0080c01c540712070f49003614070f003d89420000c2c1e9071016107110240816074040f07840d01007054140121403903c4480c0000c08201e6502000086014500c00b003640401d02c0381220010741d65001d4054007010b10402021642e00c1c5816130100c1070014001001d822903103036510b0350305e4020b185030320146010303441d403000a100c0c003403013407402600310380c0080c0c4408041c1c0e214900410644d503200c00100d204000c2171030b002c00e9540355100141c1c5081c580b40c0080342d100382481402013600c100e5407c0c03542282c0c041c508944850340d031402040c1642d00101400c5411189840c005465140003241c0030811602c50101868150660903081d8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618597679 1250 618596429 618596437
    0xb040e03040906060305060a0303230408060a020903010c0905090a09020d0821010e090601150339031e3305120f152206060603230103170d02 62
    0x210b20142d40da8018000207034580700b600c0c1c0c4054151003a100840c01d54402074566803044081666510191464007041741d09042541d00902c1958200c031580d04106d803442c0701030342080160078025031130041c60100807480703070121004444000d065102107881d0310350540003400540b04141e030414500315080300000c03900c0000745001c000c00100018a00520f81850010340410ba200c224412002070074414070340b070049031990440b18505109140d803803040b0340680191502880c07100400542071142070707d07904548140500d04444aa000c96030ba00f2040c4150100ea5030f00c0c070342c8540d901500c00b404a01c0c008a0340540a015a2110301c000d43d480703424024140f10000070340c01034904101110400c40c1e410f00f10080c0005100810240007041e40c0704101780e95444000c0c0d5030580b00600035011440f2240030140d801020150320313282e0b4400340b00c5820712402404482c82a4000246054a0304450744c071429101716000c2c1035415814880e9186845140c0c0442000c6680d101c2960100041c18003441c1d188020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618598929 1250 618597679 618597689
    0xe041d030301051f090b160b04030e0109061407110102010e0d270e131e0c1401030504080a0807140304050f0111090d02011d030102041d130c05040b040e0304 69
    0x115603030b6040c00140a9129884034120a007020300c241101c40c4950406001c00aa80c1005280307a00e4040070200001c0da0b00c00c1090181c00f50880703c0610080c5540000d41e074400e10400c0c1c858940c03090b07803240c0032034003140364290a0404600a20681c030001d4901c0800d07051035181480041041c600c0c051189092120200c112000b14401c0b030803c0320b02007280b41e400c1c104440003204940c40e440c035110021885540042007844039600c0c13410040d04012141c59880d9071110002c03007651003607410b460441c00c05c1c001e9018140950386200d8400059602ca40929031265034041e29075410510b1b4910305440405000e0549024040041c1d80e0a480c800d0280c09903224a0084009000112003500914211600903600c580702450400c4080900d4403212040d1181603030a10b41100ba52580c014203c02c1d01d0002da6602d80c2c154000100040d080071500121494241d00c141504519100c64007811101402c02c9001800a019520b08002a19040d401882690360181c40440c0d070955109070542142e02076000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618600179 1250 618598929 618598933
    0x19150203130303060b03040b010e190204060201020c10050115050d02090303160b0702160b16120e090c090a03080c0a060f0e10090f080306120f0a1a070f0e041d 70
    0x41c0c50145607042c01981c005001d80a00030b480c5092035200d101c00101c0500904501d04210f20100760040d42141d0b2540203000707030a800f1525903880d40301c000c1c040e60200807a4207191107020f000c0d0401c58140d2141c24100d80c2101940d00c001902c80c8007e440035001541400c0c0d90941c240240c14664a0620092a0b50f01041249460344005490f040e81c2c2148003174001c00443d40712003452a420402c082d41d0105840d031140c0015110f02c0c900381000e1094080050082442c17000b0102c00c1070b0680c21011000c0354000c225128274a0356950b10a0701004d015002030654807041303016041020900550007440180442c409403000c100303554036003e017030740d4006200102c0a95034000101c1802c0c0c1c14000c3c031031200c0000c0c1040c00500007039110381c00b2013801e5600c040e10280000000c11620b03a1180c0038103e1040300300302502c40313507101034004a0b02c6010b041020b81d80c4034031000444034514460b41d00c071407140155444005100c460b8610865200c0e51411407190801d42c0c486215140d041d0728445084015000700c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618601429 1250 618600179 618600211
    0x2103042102040e0309090601051305270f15010806010c08070317060103060506070615180c030f02031303031109190f0515070f0c090606080402150c19150203 69
    0x1041c402120f0b5a840070500f581c01c244010645584c5e031113071554003d00c00f4a42280c0b1030f004145e8894400a190740140d82c4521f1a102216690b640a501ca40100051540c2950f555031800b685035a1000100c42004018040b46400d074419809400495013010042c90440014081641d66505645c026402500420054000c03100c86a800f5100280c0c0710b50280781c113200240c074210104205000e0103000800690b200c45403103510403078039101038008240600552000380c0720000700740d0040c00041c000d82c0010303040c500e03a554801184e00840e4000c1c0703000300408040c103440391000c40042884c1c03840c0b10055441040008555515060001c5030380c4560300f01c40b8201443c001e81e12421171079030b0b406180169540000c0368090002041552121508117020340407507040340ca0160006002c03500803400c0c00e03290000210f046503001e0001403040744242d0784e9500c170240f5440195018001d4090382403c2e680805000e1801441c03903a9061215842640301c050300703c00051694060380c100302c0754845030006147d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618602679 1250 618601429 618601433
    0xa0614030705031e01121b0b0406121103070c050c15030604020d09020415051206040f03110703080a0c0b0f010311060a0e030d020625090b0c0f01050705032421030421 73
    0x401034481c01c0c00722159140c03858003e0848030340c000d41c440c4102f40404980074240b000302e55080b40001043c544007d0703030b481c504200b000e410610509015a098840e102000c461070601c841400b50f6418415015400c55a8200812010354803042d00420415140c0c03200000503142c602856109000100200b880a8181010300142ca242000007000c43e131300240c140008540e6080c03960712441d405203021401e100d0154500c07450300d01c042c0d1004003410000901003d240d035014050940aa1055184c00c040780c50300341d824070740d0b03041c20b02018111012101d140c03a068985040101002d1030b203814000d40340380907040001e040c00004122140036801c0b81d410400c8808980c0e41e40c00242b03c4180103203045d80400b0340020549443d80c011809012400500c42030344020400c159140002e88000903c81450007060080444d08207035400c1c010600b00c05403240e02c0d54507032000c6900549000c1d003600d07590592440c41c8122070720818800d0120340030030000855100c02e111040502034064141c40e522981d001c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618603929 1250 618602679 618602693
    0x2040504210c1205070c0b0c01050708160e01031a130509071505031f15020c010810230a050a060f1205090d2d08060a0614030705031e0112 61
    0x6050307a0410050014280c0000c2d00480c44800c4858941340c01a210a020325142203030b004030381c0158410010100e59400e180e031341500420700c40c1e0340c07a5845054685a1070008075000700b11454100101d80020901e102c0c0707510035400008007000628110b42040203c2000c9440c504001c5140240340762220100480360380100180c01c0201683c4125a410000c50f00c030003003160101134140403010140082003e064001c010006020300001108803000c1168100065a503640c4203148902003400c00700003401843c24051160100c40d805000c0b0080080754080b450110f100111300303142d00112140d0081026198041200c0280540e611000600440c89001a050052010b098411070b0305080030000d802002086200246050f4180200b10207942242900c2c5000440803415480e6603104803500c5035640206524040c26080e241030303420980b107000441e4440320b036051042d586681040402c0d801c0b0711a0004691101294400b00300341c00482d031031200c58407000e911000c03039046030018060034410710b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618605179 1250 618603929 618603983
    0xc1e1511041a0c0304030602030f100b0f1b030717030a0b19030f020d02030d0c0c0504020c15040809040f0f0b0a0e16050903070f06020d170a0f020702040504 69
    0x4030242142000e2800a41d60918420312406410b805070200d8844408502042950003440e4003030010740d203910b06600c1440d40c4203000ca880b20341400501c0000982800301104586034006541030503440c141800a4443c890289101d41e0340d8148000c00816020031031407518041c050030483e08107641c80c184a070b4140103036000d2a880b94802c003841001d0403494141c100503a42103075031100040400c001070b400010003d0301c1441c030194150141c2d00e40355a0b043c0d40311201e0106d0620520f491000310b41c890040c0b04c22070003043c100e141d03141e010001e004c2010704440e0303c0d164414440d00da041e1420710820041015500800c803044c00740c1d03844000d00244403480d40502074152800b580e43c80050342c903005400da01d811014108215480000b00f4001b800c901c036004417000c0c0039001e4102d0703407540d039203426640440d07840703216440040c000d9400381c684180c0b00f4141c401084500c0c8030708800685481300000010024046960380499003000403c00503226800355a2096006001c0010038000d0f800646d000b00c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618606429 1250 618605179 618605201
    0x303080117100b0301200a0207080f06130203120f0301050a0506071709060d0204080c280302210d020a06060602070612090212120711100f0c1e15 64
    0x20221001c110034900042c079802480b40d01500440c2c01500c00d404207006201203640d40540710100c80b00e000e20f06144c0c500510050306a0f60840d18140e5454903156201c01c5481134030440b9402180100d400c1c0450b41d440a140d507030005080c0c510300c4200340020120703544165220b02d21444084010006882c203040c3c290010a01a103200d445c2c06902d503655420a80c0d0084c007070300f000001003241103454a8100558084403004c0c801159950f45601c04144d8840c500305a2501c900200c900c0c0100c5414031a034411122111400c0610740705046a080000e00c4250201d409491400c10f200700101000030452844803500ea50040d000e00c0c0010b00b801c00a1341d859401c07160642d44624400c122403580300c0701c0080c3c9102d80840028140080344001510070740542c062007d03903c15a00302e501155500401013070030f030703128181c41c0307012401c1e20081c45804283c10000c0c4000c51034689010b0101c601503914a0806413041000c64040b0140803800321420100c1c02e002e6070030044160075028100c1ca43c7c071442000d80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618607679 1250 618606429 618606449
    0x6060201110702031e011e02070c050a1206050601170103030f0801060f0207050f06070f0804060801050312040302040903030f11040f0e1b0c0309090a050a050a292803030801 76
    0x20020b500420f590b8170f05840c4084034066182625080600298080f90490036050800c0ca14508001d8428001e50440d100070784003000405070000b060302d403028a06040703038256520b240c0a0f01c1c0e251a00310041c0001002c8a050100c1f1003c9003003203460201102c0d020354425200d245d0b105101040051a0f088141c10101c11301c0f0002030300f00d05080d0002844001c503513080790031604858012010612600800354002c10800c015400701040010200140c02594403e5403401d032140c5c4e80d001096901c21180d2045255580200030500260919401c084500d138003034240800c0c031280a80340d040460350044019030b80c2c6000810180030580c03503500c16100a00e01088480c0071410885140707440d15604607003804400c98001035841c441802881618090304006219803501e14095070f2000203090101e03281600e0600e407200180d4541d40c14410004d43d003044011039016100c0035030840003114148400340e94051094248000242994946052107130017042a8451035407551401500940060700024066 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618608929 1250 618607679 618607687
    0x151b020108010909051c0807140a080f040219030c181b1b05071e0519090e010e0102070809010306080f06070c1403070309031b0b0403080a020106080f010606020111 72
    0x541e91103403003981507445900c40064035007401d280440c80e180c20014803020203081c10140682e90703034200611520600e800e07101c03099200e807961716100780c0740700d0030040c03001242501d40458004280103200690251011b0905100c400890400c0c44041300690b00c101d811600c0346c8020b000716500d1440402c6400c407841c90034400110700d192281c8100c00030340341100401203000c02d801c0d403240800465414842e04041602c0000d601e55105040c13044412482800c1d1a042810005d01410000048405c080141d05240d07122424000580041e01c1d049050768510364903007030908060082880205140b0388200390540e52032076101c1c00902940c0c050b90060701c1a41080c075483d0702006000c03c6d036980c411014a800c0e112440d40349000c0c6140c02e102c0d81101c00c0c0d40b00101340e00c4100f54200740d40034140c0e4001c1c2a0f1280300c94001807040303100d03040d0b40192404041c0c14002000084c60007809410302c0c001500004c10503d40b02c0e0b02c1d40b13203402d0700b6030b50b1102c00e81e4480360104101074081c40b0b07a60307001c416520031a1030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618610179 1250 618608929 618608933
    0x50706032714120301093c0510081009140105011d040c09061814010f050d02031207210e0904030507020f1302070510020301050307050607060213151b 66
    0x501c011100010b000c50b805190509a90302c410720a0240e88a9500d46107134807940c450540c58005c040282005003079403a0a8000311200c402402c035000c0c0040e9858488416202c003040d151301030030003e1f0191000c00d03141440401c004600b80070000d680d00b1102000186510700d4101401c880142d84440b0f04240d14000041c4070150500c80d100c51100201d0304040300700c3d203461500c02c003810043d42c400c201507854241d003c40c2811810b2521600019441c0080c440c8904e00408000c26100c00c0c0708061a0400040c801c0055040200541e18600c2c0010b040e10346441950103040750507882034034102c0b03444801441a41e6141b018aa1750002ca441c1d91030b100b1988071030301c03011a030070300030161024081c08800b14845013199225400c41000a502501d10340d0001403202002000e074000940440365405140fa02d00b0360042107209603030403940018020480503141c030041c8103495005010a560454003000070f01523803020601040010404500c00d44502d42040704002d2558141c990300c411030102d40b000c5000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618611429 1250 618610179 618610241
    0x10180611010f110f0f04030807031d10020615030a080301140a0602010e0a0209040206190201020a0e09133f1116051905190e0117030708031003020d05070603 69
    0x5101081d1005503a031585c3c482e000840e03034050f50f0300050944000090a008050b4050003a80401c00041002580c48400c10204901406002d100c030b00140d01c0180000c40c94003035822006a40f080103015130300d20f00426100d4544a5000b40c000754500c003225000311845090000b4040014607291008101c1040d02c05a8942c44000c4500043d01ca26000303c04503040d950b83d0720131203944503490b07081d1460402140ca000390103500301003001d2022400a032182c0c0100d04007081d0140c840e600001e007002d40c4040c566a0341007855140c200d4020420500311440004076640400c40c0c1341800c079100d0f0070003404500722000380740809110310200a6001211000c0b46d00f059060b091040d81c908513850703c04402e190380000c1d074880d06544036035804006601c4c5800c1c10b050642c2d820f000d540c0500105003c980c1c035440d0450084010906184643d4010089540419401e4000d150008088a40d242440742c0e41d800089280d802c0140c01e84582c1c0200c0001c0007a2500341c07085650201300b44c040c00203154647d00710340b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618612679 1250 618611429 618611437
    0x1323090622020a0503030a0e131e0203090a0b070c0c14030606010e060903030f0304150207030516061b0203030f0a05010f090b0d0609051506030c0a0510180611010f11 73
    0x800d40c8125411010442d550103c03a0300141c80c024040b251140d0740030400400600782d100c4c44a0007a5000c141d51810102c1c07602030280b8028440c860ac40c1c5071507902d002c2c2c1000350b0005000088a005004205000404070000a4015034180d07550f00401c03161400e200ca8400307007540c8980b0122244d8400d0083e1a180460f00950000090034803900380441d28011806902c00c1c40300703041e8580000030343c03e4050310545018501a0f8040e101304c1e107203c00444e03401e1080f407040071000340204009011b1542030b40c01d050015141e40e44500c00111303139460049005c0340c1043d10b60f801600960804020009000601c0710f581790703c1215440148441c0d450304450110182d07441c01450240380d2103c0c01030009845d9000c480380c1c80b9074810340801041490f4188503480301040d041c1040b1070f911501c081901841c0001e80300c03504041c010040d003039003440c00003040b6501000d011500288010320700c0c1290041d4010b00d50000505aa0b251100f15181061819003100c1e2041c0e50390050501c0c0c000414054a4408103407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618613929 1250 618612679 618612721
    0x9060c060f100f0e060d050f0a1e03080105190b120a0b0a060e010f090b070602090310140a2304031e05120720011b03060b2713230906 59
    0x100415201e00020800c0146140f4007e00b0394030030b8000c1c40902420004407508068000c0030700141c0b40c000301c908500c8500681501500181140340188031a10b00b00b503071110f42c1c07100804002145503640c041d6107510380003407168041c2c04d507000302044404a1030b8029000c4518040742c4461a07030b42001360103048060028112410401400c1307403480c0746d40c01100d031000640520102c25480c1e40245c50708c2c0004e58481c0f60414007901401d600d0000301121801130b1085845503030454039160b0386540304500180703030901c00000f905100300314440e120002503004c54003441c065a40c0411402064240100c056190b840600810004100405568400e10b00e40e41c3c004244c3e24018a55009210401c220440c0c502d6001c91154a481107075000300f036000c200001d00000d162800e00c5129543d450202d1703d070280641902803080410420613000c3d007146045401148001c0c2406920b0a280e10502c085480903d5000006602840380c1c20407010840003031680650240d0080071a86010341c1c80b40740c844000205 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618615179 1250 618613929 618613949
    0x804140105160e0301140c09031c120917030703060929120a020603010e010906090b130c051b06010509060f1f0507060509030909092a040209060c060f100f 68
    0x3c0505540a4010b40c017414004e09a20035181042402284c4681c0b203846100d00c40c2c41030980b0b8103081903003410069a03125442d194100091104000d5070060300c20360310102d4644a84020f444481e01d820006103008561580d80081da403402d04080c6811900958062400c0c641141001942e000610822032100b440980741098410228034115240278500c1900070b40c01003001c4004964104958902e0341200c0034050144030607640c846501c1b0880b8040d021150b00700480714038286103c070207504100c0c48622589805440e0250081e501641c1d04100300040301141c02c03d0b4010009880c02141181d08804106c41c40b9400000d00d00000d441c07143c1c0071501708442d0791024005a45a4005c1c42516545500f1207420312152400b50034064507540b28219081c4155041400705600403400155212540242e08095180401e402c0000ba0310004443d1702c0d41c1d01a03000c104441c9a5103411001d4440c0e18944002440941050407c9030442c0c000200b0040b02c605809a0402510801c407800104039104440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618616429 1250 618615179 618615197
    0x114130320040204120302060610091e08030406031505042a030209060f1908060312090d0203010f0605011211090418050d1e140a0e060c010507080414010516 69
    0x3a8807070541c62a1889944140b02040008002c08608417901413684207a080d0b13082c03680e403203080050040345900031500007031506105011600814500340c0d10800d501e01000d28042c1d480c0c050b50300e1b56029030001000240c50b00052101c4441b00c01d501d40292104407801d00c0390818070020020407030f110800f00c4240b00d01100ca1403995a020782c1c101c0716642405407105996506041203058540d000c42003408800c002409080c1c0914822440c0901640d001001f42c105c56607a440c3c4841d0302d400c00d00c1c14580c01050034650000695003440b524014100180010640601e0f000000d00a40000c9403481c11490030900c0d02a088880d04048030300041044134002040b28107050848104001c2e144001e10600ca4450103004890b0807440a0310004202c034640c03650822503000c00c55440a10400040e14014107105041003540a030141040f03140003c0c01c0305040401d074200450a483c815200b0381c02140780c5005110038899100c1c00000703070100c1c0c54028851030602c0d040016805910910b10803c10800c28 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618617679 1250 618616429 618616463
    0x614040c0504032a1d04081b0a050714060406090e042301060807060c02010c020942010e010c0b0406022101051c02011d030a0605010603020901141303 66
    0x802554003554004e02403c103c8500c40c00d4050076885002c848000760300b1240c0000039a020068825007102a240c1c0007150301d40c440c1c0d40c0d800440d8201c84501c0007500245000007100250130040a0009030051006022040c80d02d859606443d40c51300c04d0314080e03e8100002d02c20f007038204d0840802c8030200000e217183c40d40c5a040c4901780c071020340044095090140c03052240c482e0705400440c00da070b220701d055403451595800103a030046050032009000c10201407090001d80b62a82d0300f203602000a07100302c004501c48030a5040345020079980c0712130f54000005c404601007400e00307014650304030a0804403400300008001800c2d00c88105002051081d84100007402c220302a0140d0b01118400e400b0f43e203c1c060344d10350110300c6400c03d001d528003440841290341c503549854801c103000290186c41d051550401400070f0300c500c5003103503412901407158581c004001840ca104090003054995001070700c440c25140014100e9444000d0741d000b105041c810b03407020140602880b0100da500c44034071013406d5001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618618929 1250 618617679 618617687
    0x10609060818030d0c020309040b01020118170403080a051905090a0306150b04142b03080408070b0a050906060108152106090102070b090d090506090d0204090c180614040c 75
    0x8000c5000c4c100d0f06004807a1089a0000b014000a4800720740500c1021b8004c0012403c844520103075020f4511585111404200440c0c1a40d4604501070a954034098503529a81c4071980880708080018100080650b22002d0507100021303026011300d0254540340380d000020340f0801c114000640305031f81d20251150b130a000041454014841c5100c5280c0341e9a4408413060340410384002640100c001c2c0b0b0209200c1c43c5906542084401150b00341007001815440444080800400441d1494405c10088020805a9034400c0c401c02d03002102181c0c40c034041210b07504003140544684c0c103112268040c0801c4042020782441040d205403080b41e403030b884240e4000c01030380e074a51034590180a04000d015072010103400501d909405000c24905075201e0005a503038504d0700c01860700c0060f002c408140094038000000780329100c0000d080200c110032a40004007100c07941d00301140d155001c0b8004106158060b005082e0014020400308030642c50040481079a102c002c04062080359199a0307401c02e40e0013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618620179 1250 618618929 618618937
    0x10e010e011704050d200304030b040c090905030a030608030a02061f051906021c02030306010804030c0209091023041b0b03011401090e06060a0c06060504111201060906081803 77
    0x1140b08032101e40c200740c2806078940d024060104009507a02094a07541051440f03240c4102d4442c1d80214602840c50310380384085500508220380780703511440c000861540342c0c0610a202805440034541d5030740c08150150881d8116808213929400902a0400c000e4020a80a502180040e00c0c41c1281405141c581c2440540ba044290702c6113205000c41080b4200048240c1541c00603000c489150303030b420b840d000c13145580d01030010069108000081d1103520800109822600c00d04090152442d2070340007912300c00b001ca48202c3e030340d80811042c0314034a80c03038025a0418010f000001015092900040c0c03228100148060084045000c40c0807090404213810030040c14010842074803541c552002e0700300d17440c0c8114000c0c002045610b0210310882e1282030030340141c8006000b06c0c60404001c10a4424000c5540c00780c4d84150f54036000105a00c660141c41c1d850502030015640e01d0012004040c030036507040c1c00a6040040c00d01051000c5504200300b0b0b500310785685043c40000540c49034091451103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618621429 1250 618620179 618620207
    0x901121112030705060405010e0c1509030712031d0103061a0c0f070f03170f04091505120106050a0801060501170c070c06050301050108090607080a020901020c1e09010b0306010e010e01 81
    0x840043c1c0720342441300101d0300901580c4114000d00014a11844880d99a41000d000301d40c80080100141c105281134001060300842c05010780380c5042d50f8001d901107860318a0b0b02540032400c40c12640081481c075004440e4103050900302006030742d0600c03082a90717102a00070442c16001d000100c00080041c100300741c600440d2080c045940b1152916040d440000d09840112540d46510080703040c4000803509452300d01c11010308107800c02d41b601954001500d01644e0101004020140c00328031030f2100503501c03003000f04001c004101c040c07501041c03101c6400203500a102603407606034180940d07170b0300c405040404000700000c4900c40e12501c0c03840886100e100350041140c80d880700001005900540a1412100c00340c0f9041039580c3d4074008292a0300048642c00009004d0b2000101e83d684a07a01800d1b0001041c4101c83e48050b11001003400e078045c101d62a01d008103c121690f00e01d140074000180581345460505007503042c003c0001e45100a540500e5050100d0880d403207a16034030402c02001002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618622679 1250 618621429 618621433
    0x10f0509060f19020a02090f07121506020705010c050c0409150507030f0f1803050a03020f031512030f0a08150925020703020114071e03090807050901121112 69
    0xb10342e02604000c1a4042e505581c050070003880007045950022461014542c1c024021000503a03c402c410f030b041440040c1051709110550342d1030b0088080ca80f2a0072400d26104200c03190aa06004002e450148958815410004208803590008901242000140358252400701d4440f40507d00007a00908910003984e841c1c0c5403104104501e68107070003001044031812030400021001e040010282e4001d82502c4d00f010303840700500070010f88600014081c17100d19180050070411a50840c582d0365006440c11100e0160081000d059460802a001d00c10010f000c021031401410898000850160390403020522043d00001624800c174014041904a002404546075140100c03002d566000c00650034107604514440300c04400740000740b0301c01560340507160800ea617958800701600962120354215035100441000151100c0807011140f0080d1090b02c5040c100742c28080c40e5880d00f101540650305c500c0500c1e0042003800520404407200035041500d00f03402c0f140300c13408202c00d4125514031030098 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618623929 1250 618622679 618622687
    0x1e0309080703210e1b0103020d141824100f03051b040b0d0b0c040f03030915020c010801050420160c1508190b1c1b0311010f050906 58
    0x503602007280000c41010720f003800c00c1d116080311000100ca560489034a0070354010041401c10380440f90011141c494140f40240c50310441e4031045c0c0070ba800d280021540074000000340300f81c081601a003002c12148840c01002c6440c41c1c1550b03031203086a850b5030a10b54402d404003184812040902d000c2c09412005034005801d640e07480c080303a6440100b1070201501c1d20001209020746458050b14141107001492641c5c44003e41c0c49140f51107101500550a560082100140c40d501110071000110300075140d120f9560b21384155036107100d01d1140c004c011074010007003100301d50707803c521128155401543c000070074003c0405004210b001c00c04800c508400b0114240400c208020808403400344a1044d902d00d55644805080624580c01030003000303e1a004001410102050881e4500040780e40010800e96103640c0820314980307100e486040f2000c3c4074060700007481801003a5107450006149095611861034486490303854803490305604100380c1c0410f160038103218100340c03410183c0050130300d955 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618625179 1250 618623929 618623933
    0xc050403030f12090809100c120324060903140102090d0807020102031c0507030b010305011409060a1805070818060117030904020f04050405060a060e040f0e060a1505030c011e03090807 81
    0xc51b000b031503500d4801d10103032200440080c46038010311050396100c408440034015014055028050b20070007018500454100d5081800220344600000c0078181c4400780010b0541c103000504480e42c0f103240502d0b07070041112889940b01c0c5c0380309044498000c0748241e00c84c401d0707100407821841280090003440000c50101203075402c50340e1141c5d004040c07548080182880d014015815a4002d10440b000d20385040c211b14640e0400340e0b881035110200a00c0c044500c1d443d07020820403034080794005001c803552032040025050708401e000360012001c0c498040e4200d04c2d192040e949a4050140c1582c044000c425000000000c000341c459006000304255159010030503451103a401134807440303116906040215800e07041031040a403d81350969203000406030b000d0f0a120150800d00011122a07544800c095110001400384a003ea008140c0204008641d40b082020030315080e02b015200340c103c0350765004541c1c0c202180d0b015806488609524151241c20203400402429501400740b80000401c0e1301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618626429 1250 618625179 618625193
    0x20d050915060301060602060604090203070b0406050a0905060408060711280606061827020711031e0d031a0d050d030606020a1104090501060b0f09130c050403030f1209 74
    0x20801c400c000d56007a56841800b0903007615014802c20000d600440082281402e241d008040b00f280050119083e803692110360707050692055110000013800403031100c441c0ca44c801020340040c1011510300c0e0500e0700b440c0401d619000080d00d02c006100340d00b907080190600510202c5501c00801d00070858001640c001c14440b0308401d181290b109140800215003240283e110040d102c0503482071581c82804d1a2440c0c4140380018000d40c01010030480c2c54048260a00007441142d10458500004617070301418180303041c80030700b034074184000021103228680ba07001860104903011480c1c0800c26034505085400303001c40c0c1d40c40540d00101c880d6408000d01c00005015003805155a41c05c018035981c40744200e03154030307c03100002d10b41c200f96045811340d071800382c004112541c00785000003070040c0e0352100f80701075911203401e1403010000416280c480f4174000e43c4144030305900c1d400520100e000c0c140c3c01410f6104501000f000d101d4070303032003694142c0d20030500103c0c0c41c0782c80b00e4200b0846204d410703c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618627679 1250 618626429 618626443
    0x721030915020d0e1e0c040606140705030c060106050c010b0a0501050f070809060417070801110403151409011b030204050a0e13080d05010323061b0c03070803160519030906020d0509 80
    0x32117540715411b00028603091070720802c0c0840d025a65001c032401c03503078040d0680310360002c00c0c107031410310040c480c0148001c0b0074803000d8000c1140b51a00340d91242203216107400d40d411910401e20900085604100507600310017180c03083e0290303140030f6503600c0051410908a000d64000250405c0c800b0902045900784007021085aa241b80e084031601503035035401500340c5484041c80400004c2c20701080002601270080c841c0460112100170510800c00c1134020003805040310b1401d0660b45901c103d00c940201d4150240d0005a03503c0c0c1546441d0408011500300d00039403050b41c1d0405240717000540b1028918204840f40c07a40244019940c0160740c40b1400604004e0005a54a401e82ca001c2118806203000e070a40354584031016100e55038079a0041401222842500040c2403070400030507409680c10310041020511500c1c240d17481381049000401d0846030002d02d081030100c00c0081740000c0210040c4000c0c00c524502d0080b03100340462404801030302450380b203000358604204c14041082e80229540c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618628929 1250 618627679 618627733
    0x90c0e010503030313082a061803090a1206021323090103031e0908030f03040c051005180a0e01090b0906030613260721030915020d0e 59
    0x1514280c0d888a0425489200554400703154080b000900000540c122003d00048020781034094080120640c0c0030303068003500e030b0b2907e83c40d0b00040204802d5204504450109e02d0b411002141001a400d021510845060084000f81440303000e071501006403580440e1345510105500c00314407551168584070040302000c5881da0051807010b0800b10342044040c56040381d8142e56000a0380b500c01030007402081c0101d03031407000c00420020104114200300005e066158407032141075540d10740b0b41405e00b045e50030380c4c000303a00c40c4480121494000ba4094103881d40310540c40f441011842d611000103481000c5903018031302d0070701d01c1400007130f8000387c6900c01d49070301c0300170344800c0902c1d13a80504050711000d0840740c0d0b00c0c07200c2c0e103e00e66030003040f0101c6442c101c100c3d585025011780c14030318a500080e80c1000300d04079250035203800c007442d0b400c00f60000e00ca00c3d00345608040c0b010741c000b0741d6140441102c80e00010040e035030101e040e08030a801c0e42c02400128500c0401da41503100c2c141c0800300310319003450403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618630179 1250 618628929 618628949
    0x250f111c0914060a0e01110f1906060e09070315060e181903080109090f0212030a200a150209040903050c070b040803030705031819030e060711061c090c 67
    0x10240e420300c00c0445455580700e680d00052428070728015564004404003245051203034074880106000b0402052940c0307039a10600219410103440c00303604bd80c21540010035800c0c911014080d109600240417419280e0240b81605c4801d04109050003c0c40d455000c80c5120040b40d0610641d0140b14196200020001040d00c0703100d003000e5102c0e000084120130050010749100b00410608200c1d6101c030301036a03c503c03000e003a0880039400084941d020791900d40a540c000250002403e030308a20040040c0c100b80507107200c88aa60b0146946801010801414511003c030b400d42e129076540d8120303055100000d20801061049050080098000721902c4180c0e00c1940004a10b03104a41c00391411140c0840056240d940d9401044449406c0540400b014454040a10550120500010b20700700c1c008040440c000c45242401000a4002c40c000b9000311020060140464202c1e0350031000b654040c0c80007503603100e000c46c412528003819480510024501043d000400c405485400105d03000b40380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618631429 1250 618630179 618630209
    0xc15110a0f0f0f03020d150b030115080403080a021e0c070e181e01020f04090203071205330a0305010e0717070e040c0906060305250f111c09 62
    0xb036078408818a28440407481c101c2240c41e1440c0b00f5001054078075030307201011814903865003000d103440c00140c01845d08000040b005001c05948040c2c3c00340000124540001d150501d038074080c144500150000010a0300000e81c1143e0a01036901c815203002800c2d0001da072203e03511045a10340026024200101c003a103004141034014400d400c2824000c0c280186c1000f0300b00d024901104507078910340b000b50795001d000c100d000b1381c3c07607101402c0100000304000d6a01d1805100c020b2624442141c4011894500424406001000f62540009456103a80e00302c101101c061091001d98844e107902d5404110140d010003000010f4001004218100040b184400e8659507030088011079402c1114841d48200020060a0b80c56440160007d02881000e00103a403183c0d00c1d07405842c020b8010700c0100e600d0340c0600c82c0004600040b805c8a000727808188005020741000180320f00156000c800c100010306038601d00980007071040351030860001d074144011a0502001401200aa1281c00c0c0d0340c1c03074504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618632679 1250 618631429 618631457
    0x702100e01020c191e050402130905090d0909020a2703031b0b0403200304030b0405240703021c090b0609100e07080423031b0c0307060c15110a 63
    0x190703803900002c4c07040c0000c03a50070f81003078281c03118400c000341c2e8070109808211001a4580301d900c01000711940903140c0003c03550400804030705940003d0681c4846611803c0c07910700c1c465000c02d130f1109681e10500007681e11500c82d00304a130b0700c1403580c280e40c078599888002a4150501c43c0150401c4900c652501c08502803180c0c288030003144202c0c0c024101001b0800010006445030318080454103460880c1824101a018070070718641054000310380913000c640521051160402c105c0c0034202404003840c0251940086044156001a03c000d041c103030041514401e250030b50800c0040308115070b60400c650215400c3c0104d45020503185079001c0d90441d00807805030868200070340140c0d070001010501e0768403000c1c4100d41c60403000300107803098040840c604001d20b9006102d00341200450700115119002401c100c4000d4095641039030300c1d030340700c0041e0300c03480d84000c160401200c0c1242000c084c41d074050b052106654800b10204200b01e894000d001c51010740c09406440521820356641604110071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618633929 1250 618632679 618632689
    0x15030d05040503030f0a020703050703030903030e0402090f01180302090a06031703071d0a030203150907050a05010827030a080103030f03090209420f030d0909020304080702100e01020c 81
    0x40c081c083d0150000c00c032900000100c40010203200700380e0310484250395540d03100c003403c010a0b90800c0b070014046813000c0082c5944551901c041c0c0c40d0858007145807000010008030a128403100c983e040c0141d140c10008015a8a00014011350b0040c0c801e84052900f441c00200420881c08100c1d2001900301c1000492110842581c0c85401161201d40e180c0c00254941c403200701025803a40da018019103801700c0143c03014041030f00540000c0303869030b81c2c41c02d050540c0ca042612a400c501d008020302101000b031a07900240d002d421002c11328901c91901c0c030f600f003001c50310b0340d00070161022440009034a202042d070203090756048a00954441e0791401d04200100c0a9031100d4074082e500c111414040351a0194580800318590040b0340300d0003200000e16125180b056451117000386500c3d404c825601c107400d01e903400029400301280a0801d05d10a40d80180c04a079040c003940d480e49a0100009040103400d10890701c84940003444005001c2248200810281d5115500b5005009449401c6641d0a007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618635179 1250 618633929 618633937
    0x7140f0a05070305160506270607230c0a18110a02030712080f0c03180d170a060308160c05040219120908090105090d060507020c0307060207060e10120515030d05 71
    0xc000c0000340303400740c445400c071001c031600d00e10101b0040f0b1240c4c0b4030200e5920b40d0014607141d1b119502e074030302101c014030864140b510bd02103505a2074011120003085035881c8090031080c0c505460381268507400d40a050001407405030004402c90100007182c0c07410940000142c8003951051407003042480c2030b80b00c100c6440c1d1003a00c2c9002000700c03a8001c01c1010300c1c060080c40d40047d02070070083c00d6000880c0900e2515100e0103409002c1180f0040100c140380c0d2600c4000e5020b10140814002903103155200045403181244071b66220445c919158100400850b0203c01024001c0c4259101d40004000000b1908000e1700440410100482c03845c4c0781c1d603580582071182c1d030042801810b040c850001580cdc03aa00244056602103081007030240015181c0c0f00312801007401e9801460800210024517162940a4100f58150342c4440000c125a59111122400031001524607540d0740000010544481d841c000c05100c441e42420100440c44440198601130208210126100410402c2e0300b030700c003031007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618636429 1250 618635179 618635189
    0x30b0108070b0f0901020c0a140102102c030f0304080a0912030e0108070302040f0306020408011d060610210f11091810031502030a050f0c07140f0a0507030516 70
    0xa00380441500c0007a03600207084c0d2800c040c0107803907400d00c40600169195031036030000c44032664000c01511075540c2c10090707020300010680e81040070750b1100818001c5c030020488454900c110001c0000c1084406006840d404100c0c1c1d04095242d08051402124940149100000203007048000144480c5100154403c05070540c039841c418050110044500d11001420072082c15002c020014203548900881402540112001601d80e81003002141c00c0d101d120002d00480c40c81090030f040d031500301299483c1c1010003201c413042c0c010043c070025141c04255618040e0001c00a03918006185400d400043c111000127200b080b6008035040d455000d0700440d96640d4000b1290903c0096103400ea03004079070000956290341d550940d0301e9032448a0040b840e0024400130f03030040280000031007103019544e0810321145004d4502c0c5054418038245004000010346000e0245501040040090265444044070710b801d507214052107051240c0e0384e40320345c80100e445104602c2c203400d81e01405c400b02c0040e20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618637679 1250 618636429 618636449
    0x2010506150316030b0a03030c0c0e0408030a1e0509060402180903090105030402030106050d0f06050f1302040209120f030a1202040605030117010b272815080610030b010807 76
    0x145440351580003454207003d549040c0360f0350385200e0f11381d940e903802d0103030056209a4590901244e02d140c050141b01c1264081441000f60b5020302c0001041002541d51002448400054001d0001e104c3c8001400d21a44103c045240100b8450125404540103100d9130003500e05401512001c10b04420310801180c000e40320350002c3c4035403115076200e071000f1504240018008034102e911034002403404004081c0072543c10070401246820005907024144d440020386050041c85d01e00b1444054a101840b14000c1c441d5600180c00601541d4041e1084406054002100d078a2004661101e9403a0b11100166000c50034000c541c198022081c000ca5040d10b009940d424116403a100b05c1c14242000802da4003015502d540ca14401610756118110038001021000300018816114030003821038086d00f007c01c00c806000c424964840b0188092148030000341002402101c0e05904c904540025006506180104428002c5941c00c0ba200398080e42d00565019156984c1d41c5100e41d602d03da24800c240c101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618638929 1250 618637679 618637681
    0x6060e0d151a0928090b0a09081b0601051e0a1401020a06020c1c08070c03140403020901030807052a151c0609060906060c12031b080601020105061503 66
    0x100c0c0d000c2d00200082c6001200c800d04141e00b8500140c0d1460f81242d00c040d5446902c48011070000080303810b450740f20f81c0481c1c1046010f0380d0352560000202c0081c0500d141c50740302d102800400c42d08000f1900700e1000d003d1a404008001301d80e0b142c44210a1180d503106000319a03405e0440c8819100c0c400c01068002d003d001d6a46ca4a06014110322840074183d042d809040709260215440b030004100c02e42980c00a005e00750031240f46184201000c5888070101f00040d02048621a00204000e00240c2c160400e0303205042d1008142d08035218642000f034024040200010400400001411045110b142910100c4a002200c181d2a05044c10a0040308c1d115404584480c2022902c03d40e40c071400790f64079441c100103004048041c0c030701c0c6402044415074a1a0410454500307100c0c030000f50032500b0741841114078001d0014160362412802924081c000e4100d604210b0280d03101c00300b1020960040c4032028803400c0040d05e515000c86140d4055420700001070720920340350650f0100c4840b403c1c2d140703040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618640179 1250 618638929 618638963
    0x60306040902030313090e0616021504021c0501050f150d150f1406010f0e0604050618030607050d0e070e04080c15161205040f0803040f020604030606060e0d 69
    0x50001081d059030140030030030071490b0440780c884c0d8040240450840228016410541561034044001e08841d048403820154800b420303400301e10500d003802e08840110180d104e0340009581d0040c03002001c6110f101d8966007104000040d00f00920401e03c5910403441950790303c515500b104c1040c030b8a680e01c940c0101c08140003401c040c1d00c049120741d0754034000465903080000032048404c8801c2c600c0050b5100304c1000000e40e4403201c90248214103240c0001c1c80004480030611a0003140500d038410a8080340200111060054401110f0b000504440c0b00b801d182d44040e105910a40000c4603079401c0c000102d80448000071981c01b1248604c1740394086950300d440b002c10382e81000c020b64800303005050140444540d2009c405000701100b54070401407010355203010304800400128071700494204030800022406002c0120318142d080002c10399280c1d141e14007040c2c0188e80c50002540b008002c02c0101c10b0205503405501910819143d04011003800310404c12000b00340440140700b40010010440c3c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 618641429 1250 618640179 618640181
    0x30c03040303092f01020c03070b0a0c0605131e0c0501081e040803150901030b0c03100b2a010915020a02030408061f06050a0206010e130213090605060f06030604 71
    0xd0311a01a1400080e4611580d03545003456041c10060b01c410030040048003007140f061610303081080802d0004005007507004e030120307441c0c0c4064405c40c80e500802107a002d4006000f0f41f01141da0b00d0b40420304110501c1c07d4a0400c002c1c130b20724003081d03035807001c01003403480408010801503003917581000d00c0c42c0c0c4e4075203800011101800014204580003074840d96100e1640445c981480c042d52180104584a103400c88104e02c84d0360280340d203684a4a207020040001c201c900c45016005525150798646d20ba0380c000011050442c1944450360fa00d000007502100107412036400840120f01003000e065190380c40c7c0d40542a2104050301411203c1591a40413032078210f03600524070040f803401030300d043c55940e01850382820402c84003280310a850585240001102643c0000540b6a03400c100e03041c981d0000c4001c1d55283d05010358010301c48003402181400490340321031480142e0060812480704c1c40759401001412859804481c05410030020a501e0301d001c061480000c6000303450f6900b50b039620350801c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 618642679 1250 618641429 618641431
    0x706090314040e01053109060b04150302042a020304080d3b060a0314010609030503030f071b03110610080c06030a020417210906030109054c03020105030c03 69
    0x6c08160003103078401468984a00d950350f054403400e000085a0a1a0802006840003503541c0d034852171901d00080440030611042c5019650199000035503480c07c40c8440040d10400c10007410258a0162040805a40000140705484202040c0e45543c0c0c045070741039800410400c0708948091080b8800e020881c902040c0000d104687c4800706d400080707000110703c1c5544404200740000352100c1c000901e5500c4e0a10780c500611280c070b80741107045d1654035031075104d000181410150070b0401c0080b81c03031284146156800040f188160300c9040e052843c025000300050b079000d04840c040c4200003400c03154071500b100c2c01c40c1c411a000e84421002c00d000c01000f40d0004110301042039023844007007445100c0c0c2000030655800c0c10010816144c0c02120060303604080741e154525a82d003004200d402e42c81c0d81c807d0324111860b03000d01041640320034038050480801ca000781410000002d0701310b40201d007820700300800c0e11415415115a6854025048050082800042c0c0818410404501000701c410019 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 618643929 1250 618642679 618642709
    0x921160b190c02010606030e03090609011b21020c01020d050409092f1c08120627010617060d08030c0c01020409060306060b030603060f0601020f030706090314040e0105 74
    0x200103107400280428200c603150030a02c001070395103d00078002c0540520500745000e004800550a0a01c0e04000034024407503903900c0782c100120b00c640f040300707000100a0181c0c80707a0b0101003040c600d41c2a015017155a006c41300900018450b1901480b919400842c3c00044034800750307a82e600e031a041c0150342c405020320341d00440e104151500c40d14244847c480c000c901505245e071544400380c01400c10008441088000700e503084400c1c2102e180003072130070022560000d212500d00001690381c18006000107442c2c002012000c5c5101007010601c0100a00c84c0303060702ca140d2107080b5140d910810100700b0003001c480700c0b80c111051171600c1c008140e400003c0c65002c1070030501a0301c5c05550b0042203007aa0030541c8602a882e889030070600420145003d01c4d000341c002c10101508610f08000040d81d40c55005e00007520441c6400041504c0c2c0e4428048405034000e600200d0b03580d242da07403500000038a4a8401540018041085048602a8001110210303609000030415507420082080305600d040001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 618645179 1250 618643929 618643951
    0x9090106181a0306010305070810121e0b04050105070507020f0d0609050a1b0605092404050a1403070605030c0717130e151906051b060921160b 63
    0xb003103a8400c1c01440c00c1207a000e0300684030f041110001d01a5480642803c052100c03130001c004440045a800600f02c412640320410310002e14200b44500350101d903a210302401ea105c41c0c90080c440c002202e1409240b044008000325903807070604868034011440000d6000800c3c440065107454071094031030810b0301440700011001c503503170340e03480ca020707008001240d000c030024000700540b44224001000030003180c10058a0140d4150004800b0340f001908000c1c080d60414946401720b0301c5800391009400301510500c0180d4403251103e102440c0c91200c240b1910400d40f011406505c0b80064030300600c6d4140000381480500da031a06070b0340740484c410070100b00d014407c0300d0520145000400080031544149031150900f51620780c404002c1c54103282c003030840c41811103079000d10300e1078070703001c9a1051400c0c0e5103035603081840040e1000796215100091140c40140845071001041c03900010f000b04081c4041500c2038070b144841d90180d054030100c1c0300305901e82040070a031541a100e6100b980410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 618646429 1250 618645179 618645227
    0xf3f11030f010606170105040903050702040e0c10030902030613080912030d050c09190b0d0e0115270623030f060108060709051801060e010c0503030112061109090106 73
    0x14001c2c0c01c40703a0a0b800780c0002070103650505446100450760380d02400b4143c605010f04002500d0151035482003100085c091682c912810121180c01e01c4044c200070001842182ea11742590001009050440d000345c0c880d008080100d000020b0018440545030f9004224905040441080140500e60154406203602082101c085692014400d05100380b5aa106194640c11008148112030030203020316205d114801800703000042c070310810f4520040310f80c580451034480c0c00d0411400b401c138640d80492070780d500900c045881030008d80800281f502858101c07450740c1c0342d406184141d03480c44c411161075030a0040c01c07240340716035181308010140000c1d00326040390f20344090692034000700341e000401d00e80202c0248240507901506910091a00701c07212a21151203e0740325454400620032007050000b900d003002100d034001c0012000b819005002e032a100d42e580e04d4402c0d500340c200300c401c844a41c0b070600300c0300c0e00603c0c08003580c290300e0000d0140b10f010780c2440c00940301c1c0402d105400c1c000030540b038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 618647679 1250 618646429 618646453
    0x9050f01030809060f0d06090605060a080a0c021f230c090904080f030405010c23030f04051903020705090a1e0c030e030406050d0f0509150406060f3f1103 68
    0x80001c2115121b06038001880c6032900d1a2603048507001c1d040584251401c008030011281e214003800e030808460400010460a0040181d01e400c20784540403a0313800c03d1080468021915620039001d0340c0380041c400c0e241401d2481c401c59030580468081c0071141d010703c0007a0b202c0c104101d0640c0d0142c85184154a800c0c529251664280c0089808480701c0e91524080d45019600180003100b6078281050a040c10044203446e4181e800002c1078040895003110008060100030484288801986808102600c450703003002900c0d04094010742d40a420740201041540c4d110b403056008040c101030714803070a034061442d00300c05046000100c604064441591400e112010b01c01000103100d10307168665100e41603400d1704141caa000d00c1c0082581e00d0082045480480070072920300da2010303800003140a6486180000081c00507030043c1800c128540c00105842c142c0540c212035580040c80c43c2a50640c1a9150324454180440001c80d00800d0a03042c10010303113034880c00ca100d010000d0036908051a61 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 618648929 1250 618647679 618647707
    0x3060a0c021513020f010503010b0d0510090e06100f12080a0e0604060e04060f0806010b0f0705060103060b030c0907022109090c210c0307051617040f09050f0103080906 74
    0x2900c003c40c20b40d409815034000c40c50014080203000301d0a0800382d085600d41444a1f0781402881400051240c85c0d200080100d080d031080c1001615000004000d03a290201ca5565030344421100ca0b400e5070207410b000704184020078244011291840507241303820b1507a5966002c41d1f0003100500d800e03c8420310105140341d81c0c8002030f03c0684290b56901c0700e450b0b00c480c00c100907551070342c3c0485003890765a41c00f44003410003c12840c3c1900c04005840b03507201041f6401d40c181e403003008400307011802a03100100401406030401d0142c000c0850840f0127030070050040013401d040c02d0b50120b001d45e00180f1081405030f11000d0f8100e07001c4044741c15500b02039542c0f0100c0d9030f1410031130b004150709000007000340a920203080d000c0c0f0300301485240c00318107107000800d172443c500c0003506401c00d000010641c4000599000407000001e0f40c005858003143c03500102046a03600140a0402e44d03040c48140030403513140b81d205180c170584c005402c081d50b9034a1612a51b00c6503002c0c0708820f411240c1000503040c0b034024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 618650179 1250 618648929 618648931
    0x3051810021b010c050d0e062205090c031303080910020c0f121905130915080105070c0201080c0717030c0304060c03020406020d080a0e010906020702091503060a0c0215 74
    0x880d00603042e251400c1030b18101c000c00c00305080d810b102800b950400442d400050381d07040c0d8101070070541309040d107580029a550040d810080140d00400c07220030900002d01910300304a410980780551541c50740040c10401380000c4070501902c1301a03460000c08644282c2c1e105402c80720503c1902c1201a40780d43c2c2a041c1d0f440050b010030b1030344c04220951070700102001003015581908082c5d134103001842010524415812012204100c0003146001c054a03a175a841d500400c100041000795070341c04019052810032a00c1451007a51034040041c1440740a4543c050442c1e505950303550480ea1031f400d03105540e030400c0c04161100d6a02d0001c0320b1426520360000c50049002031001512890701d46840c4d4103071068050441d04050060204202e01750300000c421071030502a00741958942d641003400c0004103421070103001e0540c20254040c0910400b030740100040c0380240c6000050350350345540040d00c0c0e014280c00340d805500c40000100030003600c2d800601703c0d0315188161280c8580078140c01c005150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 618651429 1250 618650179 618650209
    0x1401083106090b0121030518040606021b0405010b0406120212070c2f040c020a02030327040204060807180305150f1e0c0d0b0303220f050607030518 65
    0x203038448030b4200307110065074002e0042c049603121202012500c01000c1112102e203200070184500400c1d002070b42e0195041915603141c1c083c01c200205540c03414025a20351100c51403440d90b041d440d40220f05c2c2e0900e4010207050b0307108000814500381ca450303c02c036100807543ca400c030706a603420300100507420070341028613026558607a51840c602c1c00c1c9051026454094081c0c200f0405032100410300781075046944c1107044c2e40100d800080e01c14017920f003070382040c2c0d404070025454000019258511100000c600e43c03030192022001e90b41e00140c10600040344680c0c051200450074600018004905c21420300d00c11020314141d81c44621754036610a45482c4124481c8080301c0480030800511040b80034a480d800703c0000e40004c4882101c42000c01442005452000000b50000c0c40300c64402da50f40240401030000742c201d07075070303081e049000040356220703072110010751780001070002040b05400407440207a580040c00300c0d01c1c001069405994a80c0b00701c0d0404d1508840140506040d55858403503840c0304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 618652679 1250 618651429 618651431
    0x180319140d110d0c03051905031603020c0709021b060106030b04050c09010e060c01111c0605030d0e1c051f0f0c121104050306010f030c1401083106 65
    0x200062440c1818445007011990070810449556001003800003100c1d05030071828100300c1e0711100f075420110f400d44101e810420740e411079a40d0744d07201d81d0b61150040d4031450740d28550a04032110340008406a2248152070006984142024040405994000c0111b0340701141481c0c11400c030741083c0c60600c14240d2008011a5032042040000e003814040c00b5400728030f100c101d07803408a080b4006003c400c2500c2009005204c0400ca9086100003544a800c0b040b401c1c1800f60744445160f1034081a000c5107008400949050440016550800181990050440340c46154074400200188001c9460340c00f98440e819540501881c00f043c000d020505901c504035007182da14115902e150001e40b9a0799001205080c900491605610b03030007410400c00c0303c1c80680124000c0c2040711030f113803503004036007046515001d00c4c0000140607110701c048604a0b440341900c641040d903a4034504080001d0440042e012806c5000059514058104100c00c2210b1010004449086074280143c1c00da28000045440f9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 618653929 1250 618652679 618652703
    0xc0c030f050709090f060522110f060403120c05010908070302100608030a0903020603090705030114100b03010e010308070c0e07050702090f09150a060b0a051902010908180319 77
    0x201c4000e0015030041c02c1e0a510511a6110964422458085081c4041c001d03030743d660042045682810804120080e929030908600d6502e030030302440040e10b2001031807160180304035950007400c09070705076001c03660003d42c60042d41107040303802e42b51803007540b4013120607541e1945142c001a8084015182e0640179030b0003041c1a0543c0c0d4020011158a90441130b1030341e00030722040351200c2d400845041941e5041d51000d0700c0c0c0d220200340516191150704206d516508080030356070248801042d092040283c0c00f0702c0102e40d903848000e150607100c203002c0c80901e911035100500204203004000c240a80c4607030f140c80e2102d565603240c034104803000d4501200140000401100391b117030071811160801001d0321240c40d1800c207000c03038960302d00940e20410911342210b00007070881801d40e40321100401006410076039518070940001c12030742c0700c4a140000c0d295013010501520b4030520800c0c162a91284156292050b070b065150040d00c80d001606d6403522a40e10400300d1225041c08955025201b543c3e044a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 618655179 1250 618653929 618653933
    0xc0c03121501030605031b120a060902091501080115021c030f110c15040f1a06040f050603060117012c06010812030f060103061203080106020f0d050301030809010c0c030f 75
    0x12203201c0011940c10503040c10f00a000300e40d000b040d03007030480c0700f0441099042028000840c20705400d10714007695a0045170000c40034040d41f82c02601180b48200e983c81d44907903921100715640c1c1000c5007014006020340005011b146240d11245030100d003280100c656124032109010884d10410b026103001a885182d41c070f03102905405580c4c0905002d80760a800c0124415200e69520038480c041001c1504c0c03403010a0a0201c541c10401000d508003014410850f000d41441c201e02034241c0e40280074510302166511480b6084c41114056800100601445c4c0d1a001e544c040b4440d201c414110a5580d448816210358030b6280e1100054403448508145c1c2d0700c00318001e50038860140d01c01401c03508400b1582d03603600c091400701c952200d880e004201050b220b07400128001d2009412101840314110b420109164000084504823030180e401c5525100e6500c0842d80c440c40c80784005400301d58107200620000d02944003902c0491418580b0161240180d1a0010040003560054499408001440007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 618656429 1250 618655179 618655201
    0x40c270f0c0f0203071a060a080601030b100e09030901031a0a14130c020703060c0c080301090219030c0f0e03010b060f071401060302060409090309270b0f090f0c0c0312 74
    0x503042002c1c1c0040c1d402c0040320b45501200307009040c0014013000c2910b001070b91503603c0554070f0003d0700599084032501d6031a4940300710001c0050b00d03d03040d4401801000140072114090a6207c0c85a0101560601905000541c00b030321043d03140e4940804c090b22a55100e032074000501000f80030000001030354000c14001c0c0025007215102a0151a04240c14003440c81d400040310030480342e104600050880720948111078804000400510001c03002000285449247e005007860545024410f1103c407d4141c0079000c03605901c81d04001704943d0888095018000e0182d03140344003014001041501d503150015070550b01008409552860104801d420321411010034003070120707581e0017044ac490841e00003980b03d01962007941c0910341c503445002d0401d44034500007401446450b448258442205183d1004001400d0302c5141b0f0038680500407200c2d1900484580c1c11880240c10388640d511101031105c05070500502020350004100130704c0d10310301c07010401024281030301541d002035400c0c80c401e069 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 618657679 1250 618656429 618656447
    0x50613020918061801140f01031202060601141c1103162d1b0501020c011808070204150312020705040c020a051c0207050a0f0617040c270f0c 62
    0x39210342c00e54520144a1000040c660b030482c981c40a6141a4020303805018007412401048140b0707681c8910602042c48805420a41628810f00110003460348002080741c1e50041200d0290002c0c618420b0108410b0380000280500b40400b000411144034031100032040d10a1440326903c0e0300400001c02c0003003400c4c40004044200e1603c2d10000c02c00c85d80081c1c42c0720030071008080e0304500a01960a001034024089182c0341c9124082e60310b480384143c240f0364001d40200030014825400d0124065079400c11002c68180c10394050300c03c1d4100585a002d001c010042c1900c44850305100c3c00d03001c80410700d03500c04001e02c840e00e41e0041c0380310342c2480140401c0e60315a100b01800d66002c0c6040d030b0700050021900d003650000d1415034018440344180d04900d00540c0344d0004c2c0e00704480400c007040d550700c80710a800695541ea2505000c140d030f040151514440120341c064000b2070302140a11440c0d4010b070306450b200ba40644901d0210418001d514111420082244080b076a00d549180c4280d420030900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 618658929 1250 618657679 618657691
    0xf09050a0201111b0918010c0f0f30090209011419050609010c05210d0e060705160302071a0309010b1207030326101403030901090905130506130209 65
    0x1d040c5810120380da100c019404504c8040c07090203070100043c440d03600b46551003141c10382e4000902260240040152142001d01d00b0000001c1500c001c0700a4a40074040780c010f14a103403c0c100c0d04112512803249110404a00340c0e90a040d19510208003581c0c403185a2806404110741d0012100b20050400c12141040840e0312000e10300c0b00c9081100e982c40701c0a58014503003c2c01d00a201100c1841d1103410301c11061184a5158540d0814be051115100301a040c00020038404200207050a007460750780300300c11a85e8800150701002604000b9030320b05030b206c05c2e4a10a004480305661181881c0141d55103a4042138608013000c0104038034041c00b400381c56103440f07003940d41c80c2d070307440b0283c00310303600c03611540000342c02e1002c00031091031601040308125031006034080717400641d8141241a00d070117918500c18124025980003444085180c0070040703540740d820584940c0a810b184c1011030b8040c08000301040c5000341400c222402245050004502c200c4d0840d21400000c5054030401c025450040e00e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 618660179 1250 618658929 618658933
    0x60c0503090c0d150906060f090207020406050f0d031206091109180402010e040c09120503040305071a19030905070e06100507122a060b090601020619050a0f09050a020111 75
    0x1525011070700c42c80344813200d06052500498074000c3d40c14440c1c09085c0c3d66000c004c038004241782c0011404120781c0540b101610031103007401159a66001c010042e11200c80c0c5540c0480805200b20009000b000c104088d001c50080c04600b9590f01c2c0516011901004020310382040001100c0001d172034400300c256015a42240c013689241401d80008027001d0200d010603018580c2d6022a001140c09510001d00a148000601122242c18500151260810701c8115110f102d0100041000000040f4043d810929000801e082940d00300ba140183c03002c1d44c40c3c0b2014195a25100004241d0600400024001c103890490443c1041c07401c0c005a040c1d0a0240002c000040c440480040c804d280a01c0d50000d0518043e58140b5030282c0c40ca44289008516100f0300f900e00c800c1004010080c2c001d20b03110401115400e01540d100801680c481d44200c0d07100091010a00380c0e010740a01c1c80d40465000340e2808000030303403c8040e05e404000c0707a04129090341c16502c0f0601440442d0b03031002004010505d5540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 618661429 1250 618660179 618660199
    0xb1206041a090d0f14070c0314011407020a110f0603070f0f05090109090c200604060c080712090809030d081f050a030305090f1c03020105060324060d060c0503090c 72
    0x1000b040c866a4103a00340401040d800d017118901d5585003541c60081e000004151440e03541d15000202d180c44810070041e42d424440550a0342c04188c07000c030311400a5401518044890745c0e0781012001c22401e10325841411507d031010b003a02c0c0d02022714070504580d03d0b95144030301c2c0ca01000d0403904002d0122010003a01f00410714540c1d9100d140c001c00c9841040004c81d510b540c1003816901200c564004160110038403000c0c02c00360f4400600b060199003d041d0402114803c482d00300c81d100340880f45031000c5100300d030303101d801303881c40e03900c010000350003000880d003001c180e04000b130b00307140d2540043d0000231080c209000d400e003028103103005100503400c3e07100d80072498640494201d1416100240503c05c0c04036a1a80b9034407540038204245030300030310711900c0700c010410405500c2e00b40e001c1503005604e03002c00202d080c00c0c0058417011006806080c81001c0700caa221b4040c06d200020311958000140210080000b8003d001e041a03400a5848150301c91400603510b03403403d5501c0156601c00c0b107045c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 618662679 1250 618661429 618661453
    0x411150f090f0907120527031308030f0f0325020d02011503031e02010216080406081003051b03010905010212041a01180e010902090f011d01030209010501030b1206041a09 75
    0x80c0c0760626194168170101d515a036051000382034020740001c00c0c42403403402402d44403040011009051000380c541401501c0d98903001555564095407504101d019070800000540c9000344002e180c1c070020450798141d00c2e10f10700180e10580d00d03580303403104003580c0406003288210b138080c0503840d0080c2c0f811826920640c51074078014440001a41c9585085c0d8414a8a0700d08038400c4d0102c3d44004105022101190203d150103449036000e0b20074040020f080f40089240160030520240441e90040014280c03807100125000c0618100040258550359a00c5050001802800a800c8610300940c07075408074501410500d000d607490b41140b44d4440c1c1c0c0c401c0113111540d02c02003808040c04210000059103044064400d0040a81500c060b601001c00760400c0400000601070906894079030031100420a501d03458031202c0e00c002c0c00b00a6219007407100501443d40b180d4442e2000c035000130004005018501c8441c0d00340b0205a40550360240c8115032a2060f11700d540fa580c0d00002c2d0300c4000c20b81041c0c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 618663929 1250 618662679 618662687
    0x19060f0f09080f03071107060507030807020606030c13020405090c030109050c0c060114130f0b010e0d200a1806030209150102251e05030f010509060411150f090f0907 73
    0x40d03c00c0500e110004004031390000d01c203080020803005d1080407900c2050700c40f08068582d400c01d410850000d2071020008031040c2c030100780d4501400d13024008107468001d004c100069003940c01a0b1929150342444009851782c0c81006c580e00500c4180b060035602d5042803c2c0701e09940c401001100840750030003840b0140000014004c4c11662944c19480b0300c5031410000489018010344000200350400d42e000c40100401e80c00301c591400241c07200040c03c050700091000c0201800c0c1c02829892a03910f01c00c80403d00748000312806400101207031348807030319a6000c01d4055048082c0165290361910300703000310f00b44402c40342d4001c20000f4101c0c5144603c4c90000355204c0d103600d00d040050b0351000940c5294120751000a000e0000450344040240d82d444c103c0d000347d945407040e14828401e6440b10050000184640c6000b41280405000c80d603680d91100f09203c11103400c01c5802074050007200c0000350383c06028080322010042c01c15a191588002c2101240401404074445e820030401d0000290b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 618665179 1250 618663929 618663937
    0x2b0305041d011d1b07050d0206010f0602030a0e060f0403030f030c0309020609040b030c062d030124050c01060f0905152412010e010e010e060a0909020319060f0f0908 73
    0x21401107800c2561101d4404da00007a10244d001000a07001c00c160382000030100300101c03200c242d94200ca5090ba40c2d8034103840c0115040c840d41303000d60020051401450320811810b00c40f0704020344843e18145d4cd0f003400090780c3d840717540309400189083e403402e079446926000781e41800d14a450144204842500061010721035890568400d503920303681190180c8061000c410380490050079a520741032800e01003180118401142c500d00d074200d10191030480c1088003507a040e51203810344400e40c0c0070f01110305148042c83c0c90030f8034103001040c041103451810900801c0041d20340462140d40c094641015441520400b034000c55004020703c1000031561a20030020075241a91a1444020043e1038254601340c42482150040c0c3c40030039001180b841901742e2114106c0f0700080480455a80e50902c1509021003a904507500414050081140c04102c1c0c001a4941d030004007610840c80004021554903020b02000b200c0da0703512030340c0c00c5030700e002d8a11a1103055001c0307c005101d850010354501c80300c1c0c0b113 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 618666429 1250 618665179 618665219
    0x1090c140910050307030f29030a0503090d150e01021c020705062208031e0601052b0e01140114010f0c230601060206220503092b0305041d01 62
    0x10700440000c4d042c80c4030381c00001c2c006285031f008000d298440110406545100d94905090507507040d03031580c41c1c0c00c001031900c0c1e40540040c051800d11407444c00b081035029400c1c10030b6130130b02c0107851000400c0390144130b1103010032054400182d07540442c4501d01c07000c150303103021a601d0741c6c03043c400100403410100d50140e02800704540d44040f0540407035002141c82c0b00507005400d400c0c012081010312501e11901c0c0c00940410400140990383d6000115620f1040604010301400c03044078203154010303003400c10000c801035403d0100389041014007036401c4074500001c41c40e070f0030201c41c01040704d001c205001c0c0303000e16030a00c0c0c4190b1060a03202d0240450340000b00080440ca20201d14003030503030344649144004005039041d0b40f101d594031040256900e5050350b50310107049200718030151344d00f101c072110004613910030069400c003104081040085207030000c1d0960062800314440350034819820410350300612a4803060b440342e051880c59038a04d04600b1500e900342c4408401441203076000c0c2c04201d4110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 618667679 1250 618666429 618666437
    0x30b0f070816120f0506041503081206030a1a07080a150b0705070b04080601140a050f04051e13051e2107080d061e030803060409061401090c140910 65
    0xb6012030031a5248103c82507801d203249044540407003038101d500000c0c041d5604403000d1024060103070303559120050911009015400401c070719424500028092640810002e00f07070781402002d500c074015001c028290f01100352482804103c4260741043d24240c01028600c402c01a0721122122440f10b400c507070180d08140e140118883c3c0400004200e07800140c00e00040041c0c55640d02d40d1255600ca0302030160782807480d0300c140300354039604108000c50102c40d0002c00c8040501440700c01e01c030003000085c2034004005c10180200d0001d4210006c0070340145550804074000000c2c9084c00ca09090700058500201140300c000c94004450000d040c6104080a0100804a07038020030803120500c101500280b103103d0100c3d5002422005501000407500d5900060090b03803e00c240c8402d0030852404000d21a01c0248042412420a58095121036209490004000c0e00c000d051031071707420090b404804010340b105d0043d00c4ca20f034051507484070704d4072480c011418003c2d001c0000303a87d4002d5004000404c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 618668929 1250 618667679 618667711
    0xd0c0807110d180b07050609070902070f0602030402011b03110c0126070c1515080a050d031107020301090b07020c03120702010c03030615030b0901050303090904080901051b0106030b0f0708 83
    0x1c401200c3e8078002030441c0c1072041ea03107504901e001c03600d54100b1513604070395004202c0d000a41c030070140200ca816a82c440c2941403916455a0740d0303c002d4101410a0303041124124064507507000c181108041180682c4501034600c004042003442d180c1e1000000e81008007101041e408a80309c0400c0f0a0040e40003003141c0c08030780c0c6025049075180c0c05624041c001c0402d940e003402d01740c000c2c1d900c40c00883c094003984140064444515554510080000504541c0480903107035109109522005405000580710f900c1c01415400107402d5803070000e003c8e03a4040c004402c0c004066010400010034400c29006000b16003040d544c4040d0340d00400c480030b030601128405500c2058425484813014021460780035540341102c4c040103008024944031140205801f4002255906d4000152600d652004140391b0690382c60380e49000c11504400001814000b00748400035034604038811070800180d01c0000005d04529508115a04c50b40242c64201c8402c500402d11042c01c0d03010290950144c0005002c1101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 618670179 1250 618668929 618668957
    0x4050714030a020c03090a290301141e060a02010212220b06040b0a1215050c041703040515030417031e07020a05070f1a0906040303110a080d0c0807110d 67
    0x250320070075506c207038418181c00010034500c00c0742c0a00404c0c2050b46a0002c0c8101d82c4a0341030102d80300038095650003040c544000caa0303a00d040e001400040000290b240406c80501010550541141e80c482c000360b50045000000c90200703101c003a901c840c40808009041d00c1034210071581c42600c0d80c000c1d140c445c1c4074000803641d846a80090800e2040500140b0b40a5541c0b00b0018035481c40e018112030000f00d0b9039011106046c01c0c045c1c01c2c0039050841c415498249401c1150102c10f04440310354000d07001c2444000b420313640e551900b40803040100c000e5542d910f06031511001420142c10f43e01400a010303c10300800a4420308003242c0e0801005400186450f1401e0607881c181040c00d006126119521001c50300b203403203601940450f00110000842050400c40c3d031815070044000050704043c052008001007481064003010705401181a96090341c0540c40d1103403190b000c156207400c12a1144298001983d100c0c2c04280e00109030f01d0a0114250301205c0c0c0744d01d4104c3c206600d010040610180340c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 618671429 1250 618670179 618670183
    0x10807030b13091e120c170d0209011b110409050f0601080c0f180a1e02040f03030806040b090105040e03160b070f0810150c150b04050714030a020c 65
    0x804240010328070301c2a05082d641d004050400716030122000c0032003540c08a102000b81c030403010520fa0054050124105c407000446181c4141d0509882150711110310000030400e00340205400d02c1106005030356000d604001404400441e00d000c04103030203a03090381011520350226081d0340b240403030b4041144801d0342010b82c9070000d10180c060644c001c0c50000039860b07400040c402c40603001036031040710041010041100c0c503810354500d21b49840541c0005260140c0c66405006c0c13204e0000004074002c1041c608160890f00507400c090020350007101c040c03040c135070041c02850b4440821101484500101800f1032080390040c410140200d44510b001c3d4107409042c016210b40b49103000701105030002c203007032000841c0c038242c0d0510081090a4000d0b00c1c1d042c800c9000310f105061020017581a540b4220304487e52280744011002041100100d08001600280e40e0703145100304d420010038035600540c2080304580c8081c003240c041c010080105104681d90350152507000c05030304401030705c2c0e0046c3d0018034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 618672679 1250 618671429 618671441
    0xd2309060a030c0801050612040b0a060e100305161203031104180614180403050c0114010602010e01060b03070e0405040f0206070819031a0909070504020310061103071101080703 78
    0x980e010300302240001c0c1803641a8001c4050b0b68603540d9031a85641d0f510705104052107000d00e00042003c0020010b00441e0070b403803490b034000e80f401c41e002031040e83d94440c50045800584400085c0100c4e180704009120301041031b03810f0440f590030300892603460410007088000c0e090070024249030300c0d450101d03005003401b02958014001002d1764603010349802e98180003007041e4099a20304c03801c0c8491510762400c0107461058900c2035051808203e441d80d0b05c0c00d40e41360300300c01c0d6451a159282c151404400010304195402041c280d0004505204122085401d654085d000120b01020170700c10070290540c0320000403400001958001895280c81c00e10f61010107004c400a9044017000601030200a081c01c002c2a00c02d88c000c0015a41d40d00402c8100c0c10303160b6404400b0103150f140a02603003203180281d0f049420101e00350466140b141c1d2030000c10144e0f0421644224041007102040081d546c1080c0242c044680d0800918505180f80c2c1e14550a482c03a520564100a9036034000f41c0e089009902070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 618673929 1250 618672679 618672697
    0x1141002010f060902040305010f02040605070b09071206050723030601050a020c060a0f11070303050f1c0903120b030718020307120905030327060f0705280806030d23 73
    0x600581e13403500f103844040d50040c031044482d98688540303000040d0080c401c0d6030545009070b649619140e07554031241c00040700900684254020310a00280917412003115050b0350740f01c1c9101040d50300e4129005000260361010761440020110f44884000c02550100c0754480000d00b4030948171440803804a00e8206d02c1c84440760040c100151022405420082000d5410507a5464900380700c0c1d4011300719150744c41c0313101c0140030500520000f40000c0c91030001d4900901400c00031a200d2071a0a840c400385c44900704150003154482c4034100302c00e00d040c010400c11110980c01032280500d0400652030100721880c140004a41c00320100e84582c0c8101d00e01d00080b041c10109101a01d0300703052154130381d4015a01b02d0130a403071464500483c010b5030000038038040101d034054440369680c1c54944492940c02410702040000130482501400c55803058542c03103004560b020303c0301c0b480c01040a0264600902001c2c40380e4403064480e81d0981d80500021105a0b84600390103902480700905d541ea80918065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 618675179 1250 618673929 618673931
    0x30c05040806012d0e010902090402190c050601052205070201090510050a05010603110d0e0304050a0f0302040509030733110c0d1407110a0b030f160801141002010f 72
    0x142a80383e407001000011348003000307540d40512020703408500d2060b4854902c041040f040100840c003126030107088418130260025103811b83d8200c64041031550b0001c4040810408440300d414480104a0140500b000380e03030081d039a180360354442c0c0d48003840b044248051621070b000a29041d10139008038235456071000407a50802c00e620000d40140c982250a00f42a0b440c0c0000028014424020243c212007010622841e040036a07c402c400303045034007a180d0b5240310820000032141c54045e0000010311489442031140c500b0751041000369a0003400040e9203620500a44010407100c0b44070012482d09a00c144044000c500085509086041d0f881e4000a02d0002c030203804180480080c8205070010041c1c1d03581e40b015190613609005185241c0010034414001940041c0191140b41d4980744001c3c0740f0914581e86410300307a010760003211010b0b00c1e07082e0390003800003c0454007505203420380113040000c91903050075401c180700d00c02c034180035202c1d841002280712464000c1d4040d510b14212080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 618676429 1250 618675179 618675181
    0x4051908030718050105041217030a090b090c0f100201111824030a020901030608070815070504081f1e330603020309032106120105070e01030c05040806 67
    0xa015480790401c5a800001c1000031030880c002c000d40041500c1980c2050b1aa107082c01d0400405c410310b00c170120000c03180070303e001e500c2d0b58042d84a00080c51141100c40408688020b0030701c2c02540000c070203808491142d101c6100c0031210303911440343c400600802c0e1210262001480c2e0228094035100c1d010b80000c0300f000451081010056502e10603950041e10701403144929980da0b5032070080ca00b40c0e0301c805058280003181083c0303002c1c3c000f0800800140340104219803a0b58581e8241241544110b44a501070300c08a0301e0040344003540381d4010704605050341032a00d4003c0003612200c1808985101c55004580b00765820141d92005400e51120082c0c0070354802c0502c542d00040003400303000c20014070300000d01c001500110313200d2034410350a000c8201003580b61600660194001800c1200070b070009103c141c0d038664400b2901d45203c00300300464150303400c1800a1000109080ca0b90300302e036034108401c0000c41c41c0c0100b09080307466028a0006914281c07508211506d000b290030802079409010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 618677679 1250 618676429 618676433
    0x60306030b07081605090d0c09020304050d08010f210605041b0b0a090302120c03120306041a0607020f040e0a03120b030307051e0a080a0503160e18040519 68
    0x150024094900c6018044001d03110000c0c10340d400701c022202c101915515001d0400814411400341c1100700025000800034100c41e52102998640f64002840c0070342d001c4104800d0100801c11622000301d641010015541411002e60f401c510900881c1460800780c0b03401945415480c1840c0951500040c080005091500d0116201d40c110014004031030100035010954046880498800803d180c85440d601803a590a001084038080400442c1d8041c40c10780f04036a4406000b00c1c09400440500c4559034a4002d003000100e8104880c001d0450003039109010881d11444101c4550310f030101c81b2202141e40d43d41c00180a011001e12101c66400f525001c3c01c1010303001001c4070290858004d09210591050050603501e01030468007403e2640114070b043c1c07415042118445100c0316000c01d54402d012940c887c000146d201142c448001240007040001c40c0c01c1c02c0000310741401c1c413480d007029101c0041c0e000405d18409101e100e1425070146011a0070003808000c0c65240050320344013002d05032540c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 618678929 1250 618677679 618677681
    0x405070f120312111602040b04020313140d120f1b02070501020124060c210903050606041b1404090501090c1707080f040602270a0b161e0c0603 63
    0x380204a02284980800c040100c03203a02800300090f1340e0005290070000d14420492000003500c0b02030b600696039140000070b075203941c0004c522581000d10040c907034030140d18186148101501452240741c000a20206d0000d41c001c0c03030700c142504054004101c41c00d14003904402411075504450741d000304440003a0002d40c01040300011284240c00801403000c030b208030502d64513401d80c0c2603000c04441c000180080ea0003002e00d0310402d40503222401c07404406542c907849412034525900046005800100f04002080201c1a48410103a46c10700460420441c40380c1410909047c1500384140164803448085213001610020030a500e42880256920305000d001000b141c40c0410008054591403c90301101c010101e001d0691507031184501e544444403e01c0800b0064012105650200255250490360400c445003507039854007140320341d940d140c0400200041f0b40d400708425140a0054880d0030011500752665a50000388014403541d0421100c8103081c55054020311401000c40e001c1071443d81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 618680179 1250 618678929 618678959
    0x2031c05072601170a0807021207180207020a08010b0d03140c070e01060f050c15180312090c03010b0a050f0409050706030b010905091611010204150e09070810060302030405070f 78
    0xd41c482c506908100c911245d854841070300025220f60010440704005090900001070060b0041040c2c401d55a1a130001000100380605441003040d00412040d00307500d007481c0f022000307048040007003241d1640071021500d140310007540981484403011445a00360110342c115005442080c00b90b452064541c0b0050701015028064100020000c0c030503013403454010380460300710170481001008000d0301070146980c0c160008011900e4422100b09640d1356403420006030130746d41d444074100c01c0036103041ca2440d8136001048448902c2a818081c0c101c060351504002402901c10030b45240300800f013201c2c00718001c0c000d118030090140c0f050000c0042c050b0b80c10303808601403000c2680c1d56050a40d9903401c002003881c0585003000d00507101e140918000c0d0050300c00d040444059000941410340d138074441510580495102008034003060000401071600341084d9601c194203082022481c1401003801401c04400e0207040c06255001000c9400d00108101000080426141c0741c104107484410b00d007a0090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 618681429 1250 618680179 618680189
    0x206090402270114041505070c0b030405161a090d120c0b010f06080f060a081c03140f0117160b0c1005091f02040b040b040302030d02031c05072601 65
    0x4860b006070b40080d8410328215906180c2d5046203401d01e424800a2240c044071070030070303a040c418100b00c8403002403034401540d8010500005001d4581c54103003000d904060070001c0c5140481900c10f818007500c0c10f079000744007024180b03108072a00d03030700d04601003001412a81340252038031041f0f034040c0d018a03903c00d0304c0c0d540c51489980c0400030350740ea940b06074401019501840d80410321090001d4071001d1043c50b644c0d40024000c04041d0320340e903903000c0c590811055142c41480d040c4040317000c03240c0d00c1d054015920411584481a09145050700c420400343c0d0060240458801891041d02145070b020406801c20754580318103c40302a50354072850303030319612080200000d4005c007144941184510b205082c801d1136030402a00081c2c00ba54411943e240c200884d001000da800e020208400000c0c0b0b01400103044a40c2d00c40303581c0e90450041616142d600702381e0104540c030400c08503181d450030011302c039103200300280c011510352160b034030503a500c40f01c1003c0c1044074040c44000c0c040c1c15040a8203503040320 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 618682679 1250 618681429 618681487
    0xa1509140604150c05190302030108010c050c0d03050606120c09100c020d030f0c2307080d05120c09030f1b0d03022a1309060b0a031109040206090402 66
    0x2080400960740320380301240c002d0025244001c03a1200c070105500000081079580c6001480d152041810440d070140e1440c900000950210040c480720200744101c0314400c8407800e0060500d031205800320b60302c50b18412804100340e1240041341d002e803036100c15120706001a0520102c68600642c03400210f07003252100c9403040d5404903a00075071601889401e040e42d900035100f20100c804541301541d00c010821495030410130840030b00710120700d22001c10381c0303504c0503084030140921207406018900138007600480300300e0300b0120038020317495044030480b02c2c404032001d400580c60303807401001c643c0350064908a6401d8060440b010705c0300c880200710b10944901d001d400c0c50000301520140585807507040d000030007684c44103001c20840e07184d000c550300b01095411102c0070408200c1d00030840d03648a4098250847d62650301160401020380520400000281e4801020714070715103404100203031111010f406404d0050201e0155251034007180c05111003e0b005555032008180d480d040c403514040040d07405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 618683929 1250 618682679 618682703
    0x810080a150e030a0525112202070507030c06030e060708060f0d0b06041d030f0c0a02030d0203030a052211031005071107080106050607021e130204090b04050601050a0e030a1509 78
    0x1814803503031b075104400e4000c44031030170711141c040070301c40701da502c42d1340c406c40d1041c807940100da00100078001488a039200b00c014020309860341c54409094040c1d50018001d0504115084520050028442c1d6001aa03894090b00c1ba8640d44086200e24800079103807908000d0101d2440b046c0002550010300900d410b4804121485000381042c410f9a40703002a035100b50420449410241980c0005e800400e010030240c408010543d40000c0c0780ca880ca020000143c0c00104c1040700040a52040560040d61031000c188507204001c000d01c2049081d0038000d1420141401c840300036202084440324410300140c0400450800081c044c0103c100c64020681c00d208000d000b04c3c1c2044103015900403110060030795814800311740c0c2002222051038000c1c42c1c2c0b45441243c651010313aa803042c40401100350210060b42c5a080094450030b40350641030b103a028604200500c442640e016085441e175104500d00b821580181400082c1000e6040070701401d6000c5c0c40c2a429801c81c01c650040101a105031100070311 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 618685179 1250 618683929 618683977
    0x1e040318050d201e060d06091508060703020406021e0a0c06021b0411160f0f03080f01090905121c0213060201051b070f020111030c06070810080a150e030a05 69
    0x121009a00328556003035815081003041c2d040c10809455104906d403404540d031a120f83d4200e040320050300031034814002040c0c04004054040c0100c40c0c02520a00d02503180c80e041682c003a68a00807a440a01e1600d240f81e4080d451b00340612004038140d0340900144416540e80b40c000f5558400c404800310008801210001e00e0720301480360b000443d80b074410442c213210315848229040045400e00b52840b40103a43c1100006403030b16044220380d8407035110039095040c81800420710300030503040a00340d40c1c40c01d45840d0218100240408000c0303001c1c00c01d01d0b620840410340c0c05d0b1142d020061081e00c40c0c000b250700012040540d0306003040d184280d0003040726585501c1440003440c0350b1050030404a0082004401117001051035805190060501850f1000c8103c21145543e002d629001c20701c1c1c20010600c41c98076030001146400c01264059607a8090420800c242c40740344122000f0300802040c0300703548540b01a80c000d5240c4091450030780340c9482c1c042001a0030350f40188882d0b040c5440340d0740e00301c02d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 618686429 1250 618685179 618685189
    0x609050d021f050c09090a0c12140a0c03020d06030809030610060504120203010212011806080706020d030e0a02060412140a08040b07021504090207030201051e040318050d20 76
    0x41c000c0d015102000420040d0100d4400800000e07142220180b070400a089aa031a40c2c401c060040007072080000718070407101d0f0f0042c026810107c0c9d00308802d00b00000d00e10f03034010f0004d410b6040120385800090031f2500035000c2d0020f1043c0c98008460b02c2c10f01e48000203200007800940441e01040d8142c406940e1404c03402503000809008507008036800f1711041c0034000200034102c032030501c05000103181018621482c081d2002c02d911640115a00c0300c00d04400d01c900c4c0c0501c0300101207810062a03c2030a16501035126046801080201a503d4040805084040207903400c565000340c19581c2e907540340d250340c40c880f44e0070207801d0b107881c0b0107410036504d544000216003101300d800101142c145801c1c188029550352108205032ba00c4070b003120410340111580d00040c002085041e5005949451030700e40a400d4610003480107035031515504040f00720b03c05046030190320650503c0c10b0b88a4407946014010190180e81000340c202c1a129049000c2043c980d50080d00c01c1c0444c0610300000103a101002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 618687679 1250 618686429 618686443
    0x2100605090c0d0603080d020c0f0c06030112050106030605091501120f030503270c0f01050f03010311130510031a060d0308151504031a0f0c1b03070609050d02 70
    0xd0303080044100003400c42000100900b6001c0240400400d84d41d40c0c1c1d496200c0c0f2074000801d0405c0445d0300282070003140c20304000800c61416000080c01420801000240c0c19000510800c01000705d043c294000300f00080d8464000b941d030241c002c104a06001c5000d40c0c0d02d81c03040b40c24050082c2d0aa0000c5080e04150320910b0005030f00180e01c0ea01d40c400c4c4da4003120a60406010341e4805001460810890041c400c1c00000d407842d520001c1c0040042e400c1000b4660743c410303000c1414441c040044c1e41440001c0c201716415243c106090b039280c0002d040200300c0c0e44800e01c5000d55114541070a0041551080b0300300811640103401c0402c48241c868601281c01e00d0a880160340800c21800100002c0d02481030700ea842400d100002009100040203d80e00365090300716a0341d1403200140906c04c0004405007001d1003d070500c03140d1038030f1900c003444070382075040a4841c60001394045081d4001803220410342c1d40241000c02a44c0e1201ca0701c1c54103e0284c803014000311028003c0916a82081e440081d40e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 618688929 1250 618687679 618687689
    0x12580f0f050718140607081611190b0306191a0d050a18020f010915051209011e020705070f03050309040b040b0307290f031902090105030106051c0608010c021006 71
    0x381d400704d60400200151907001c40422500d50406001d408280c010210004003458090079800c0301c1140c4030010803642541c0030f54207024203e005031080c001c41ca8144d0030349620980c00e1342c00c5042800d81210394018110607070300c44155015406034601144440310007600254034003c1040c800c40c4c51310510310042d2000200e02c2600050b41030180d1b005850441c030b000110101c1070400c1e40d0303c192100054a440c0c4c0803800c02102007440044c50110101041a4841d13104008000821081d0501c507590b079141c1d46440340c03c18119401007860028044180520001084000c3c0d68140f025030301d107459900c1c0e070000b04100d4401c03450103c10300e01d203040034084c4088088008020b40500d6041410004419150700158000a921103452401e500d201c000101003040400d0b8420391203180450603003901c0f07002091075014840c0184402201641c208090b20f0641e1480d04200b038480c01810205801d0030742c40b891a04046017008400034281d8011b612083c00001203500f654480d4010708241000e0311002d21a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 618690179 1250 618688929 618688949
    0x3050609040213090206030a020702031e0715030e0307060615180b0d06050628020309060d24062a0c0b030912580f0f050718 55
    0xd0014541904009403e60608000040414807030b000300d246504110741d041c030440d41c00501c04e419813030100702d400071903060307070900381201641007404c41d442d0b04842c4902800c030980ba44090307203400c0c000c1d00814581e45510046070b46030380c09030510201511051103101d10f0140d09800f03480100e4458854507900110000d01100b0030391030550b074140150300c49000c03400d0740c99481001146aa031940010010307a840075101001203038141030b0781c122b241d200564040039507204004801c15a26a00246c2da0101c800d003030006031391004c08a24070704040001e0300b01600104059800700f002500f04281d50144082e030315024030003249000c5c2c4002030b00030018016204604c0408100840031540006582c041f00c1ea0f001d8031701203c078103038058205811080e110485540c89500c080c02051030b0140c0c0c081d9207083c59445110000b5602d80c90342d00410450350003440b510401c8100710480d81242c02c00000258491000c004440c100b1101000030942a204c2d4400a480550424131031280d500c3d1a00c00e40d895409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 618691429 1250 618690179 618690181
    0x30f0c0c0c06090414150405010e01031a0711100e0d0f1b05011d0a050c060703080f0c0c07080601051302042715061112270a0902130f050103050609 65
    0x802c005060308814900ca0340315803944000c498200c50004140c1c050314a0500c4054000603041c00c2009483c0141c00803c0845200001007000c41d4118911042100741d51401103180d4884000490f4600000013034101103200b600600d183c0c11b40d0701c0c3d11034445602008140d548a00740001d046943c034910b085030034006800d0482c44110950145414540d6078460400051000103e81240c0503140706000016840e800c8602c84d42c1c1406014028003804480c119940d62030100503681c0500100300182c07031003d17541c0c40c000004051004241c00c440400504c1c2e41200c2a0a64070461265111002d000351030003000c3c0c010210a002405001f6181034860030401c8940e00d154910031580c03c040c01002c500410f6803a15040400c10300e44101c10000741440750703503210301005402400740c13a04461025022030624204090606c200d040d4001c658203003e080701003e1304031303a5400092001e40c620380141080c184002008038107080341ca0120300c1151194101044550341da50f00550407140704448241d0800c820720 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 618692679 1250 618691429 618691453
    0x9080c0c01171b0c0c030115170102030708150d05060c071103070f0e09030412080a081b0301090c020f030301091b03090503030112030309060c180f140f01020f0a08030f0c0c 76
    0x8001d003d6030081d100172140599040c00c0020b00350340c0c1c000f0032000c0030304240c0000c2c8520300c000c10741103040401c000000e40c55414440401000100c00414401300441000c0700401c080d41c607440340002d0550404112180350500c4110300916511017441224469a0001c9a44d02c0d820007240e950100c842c03141d001000070b4541b0351010b5803450300034466882400100070100d5901c4161100d510070501032552a0385070304a140b00a001c1c1a009011070152800d480c070400105011582224151150008045040ca00800c400d07407604010221840e8280808000880d501c2903076407114100840031982c08a0310b00200d403040d0200d540011000e0501c1d00b00300018030070440c010500380c5142d44680780002c1e00c0d1107591136000840707a0028000d40002c003002010408010416070140c0940180d0000310080c0e40350408030305280e80180c0040d80100c1c25450310311070740d80c024031030016080a21000c1d43d8054a007460610a030750b00c100d600e1a030b02500000400d40100c20581510b0821007010010901d83c1980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 618693929 1250 618692679 618692731
    0x1b1103070f0c030f06140601030905070605090607080316200303041b08030a030507030e0d09090507030603050607050304061401050d03081b0c010f3c09080c0c0117 72
    0x1800c400e40d0400b642e0180000001c803200d8000030000c1c003c080c0000c0000d855041d0061201d009000c4504041c01d01a04201042c00851840210395003030801c96070710803c1d0030200300705004085c000341980801004000d842c0391102251245100696101600200c002041c0009500782000e03940041d4410310020f000100c50020604240640f0754040001c1e9a40320102c92942e401641c020001076254014032034440c1e090b003d40c3c6040c801050181c220a000320320010242e00b01445114100c4c2c3d180c1004c24481402030f80304074040c0d90030005464071450040c0018046a1080c3c40032a101450958140f1070141c60156450503600014540d46022010b074808940582d4040c1a1400403004090b0307140c0303200042402000300d40f92200003c5001400b03490503404482e0501c1280c411002c1c240c60341c0d01c00251419081d039000d02ca8403e0350b0a000e001c81b1080004001c4998003c102c4080083d08031103800000517a01c000d03c800f41e903401c1600c01d00c00002c0c03c3c101010780d40351041500d400c4091f8010145 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 618695179 1250 618693929 618693953
    0x130902210403020c120102120c04230a2d0b03040b010e0406110309010903140a0e09070c020a12110d0510020f0903060f0f0a0b091501031e1b110307 65
    0x2481183c3d0500400800101c860381c000e00c5c80c640170380d40003031000b0300b0a202e40c10320340c6d02003407030401f0505040c070341008280c0540c10710000c2c000544c960a0a01901e9448414a43c00341c64201c2170143c010040d080c080b00541800c06c0203002c0303160840e0b400120010507500302c910031399000629042d01c1e4030700086e00a1081e0003901c110740703c980380c40c407610600400101852043d41390b000042030100903420094403910120040d47d5950f001040074103c4280c108540400506080d20340820664072a2821039206604c501c001394000e0180c203000034410b1020b1002410b940c028100148c040310540d00b04002e0780e401c1c0d140102a50805641c840042040c2d9014159a883c01111035241080483c0040d060407006c45411030030030411000c0c04a20b609852a165102c29595410442d044800001034103841c0014451030102c42c500d411525035911070382007903c0001043c102070750030312100c0c0c0019000d0002c00d40c0503842004420580340040703100d103e075441d0311691880078500e08031060303d90701c80c42d0803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 618696429 1250 618695179 618695183
    0xf0c0313030c061e0c0e0405060918030f0711120f060a0b0109080703050714030a0c0e100b0a030c0210060b1c020c0a140c0109080c04090c1203051309022104 69
    0x1d074440081000d0fa40b1050810a045030000c0d0020340594480e01c00307021605200d0050b8042c601e0234040240359213410390f800b03030000240d000805000510b003028174a184105c440140703402202003401c40410403400310487d40c200302110101900c8642c0c1400075a25000400104050b50226001c5860000030740d0140760322903170624204044075103601850f0700d48000da13441190769501452081000c5139510b03038498030300d010440c00b9200c54240c03a15080400c100b60300032a280c124148001c2011041c940c0101001041441c819030f49070404880c016005111048882e03015000c0e0403204905498188107040130340b40382440e1a824132202c11001c11611403405c0012440da030b0308114001c220705d41007240480443c825000c0240b1307203420305405410710391003072142030501c406108280180c55012541107981c240660700015207c049090000482d0f146900c104981c0044507030a40c203059000340140148036285c842c08800340d0b52008840c04a01c80d48880307058484000155000310b901c030002a82e0001c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 618697679 1250 618696429 618696431
    0x20a0e090a20040c2a050706030f020729010b0c10050903040e10090b040c0c0f03031b09051e0d0206131d040506070f21230f0c0313030c06 61
    0xb903162000300d011240000c401002094000700d80d00310a0070900d40291500207007481e25800ca261564503141c1e540d9041c0609024103845109114250303516034160f0301c034103411020205141c12008103141d8903031244010800c05503841f2001049030034100080312034609001000b802c00009260204004010282c4030400c180030400c0000b8955044101c03143c05444028400c400651610717268004850140b800345004501703004240000c1500444507450450b0080c1103503800c003106241c00c50007440c2c03100c0801a01050608441080b650000710ba00a4500540d10054001c00b0f1102229481c80c59011440e40041c0341c041d004010308151002d0070009100701c60280c90161540c01041d2482403240c2001c101807a403c080105015080203056041080d0b4101400071170700420000780750752a022041e03540382c01055104044842198000340042070951811058142c2204614841c4c10701500c0c9801c9580e81c5401040700d444d1001c00320703030164450700045110342d005581c0c107942044116200351086 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 618698929 1250 618697679 618697733
    0x307090b060f0c01020c160602030d0c1e050301061d0d030c030c1205030402011b020a051509030f03071a28060504050403090509010b07030c11030a080d0207020a0e090a 74
    0x15807401c400740c420f0448840016884010318504149020740f0381c0c1d140800c404043c1810420310f5000300880b031060300a4180450710300681d06059400003043e5941200c42c110a190401c80300e5888800355058030a0366988808031a0003605078480680c150100542c480000c040310310001c0e004030084000d00c0d12038117000121a44540720321012000c001e812902003440042004215a402a240101c3c00f64107204205410815004200404158028913000d800e186881c241e04010020559030310707060042c104c3d0b030015443c075a615201e40190b4800c948407840180120240380304842030740c1c03140f443e00c07020000444181440420319000442d03c151001c1d600c1e032000c10261a60300402d8030030b50294a8564089240005200c1140416441181b108006000810000780c0c8180d01342002504421442e62080e25480080e041c402124401405910001119564058070313070090315009000b251151b071f020384e80d02d460f400d1040381120b5a144c02d8229061590004a1400c81103041d00828500c504174 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 618700179 1250 618698929 618698947
    0x5060f071407080a1b0630020c01020405040e0309060a05070f0c06020a0b0a05220507091401031103010b0f010c32010f1a13111204050d0e0307090b06 66
    0x4101498000c030f1099006045480c080c02802001c80c070401200740000500c030707864610b009010300c90494416102d030307107114443c0701c0614000500c0159084401c104650f285c4d07040100c14000c1d4003500c211800b9030708201c041e8030480d4010050300c031500030140c051807400d6056030044482d58017040040b1903a842d0780300802c0108500e00300c800702134410b0390006e058070403040c2424400700c9401001a65110300f40700401251185500000b000c01c6130080c207544507151a03103021030034600150044941c0c545841ca070440500c48040300d0034100c0c1d001d44801c0000c03002c41c2050609803000112955040075000c40010172039441074421084540c010100f000c0104d0395a04c0c0000300081c100066040c49482080000c01d08800303129209800300303420800c21243e81e0300a003a0102241e941785113441003009102003010801143c001111200d60303440a50380e01d0903203052808036100c041e2401c1d603861180c45004040c4900868802811610090040002d140350401d0180070384100344480b45c2001c000d11400e84 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 618701429 1250 618700179 618700183
    0x8010e12090d1e06020a032a05072a060f03020f161505161706090117100504080a0e03210901023a020a0f030305072601080d0905060f0714 61
    0x650030703105400250382ca801180c0c0003015592040c6110348500d01c001c00c10784041c92072006582d194006400d00700c1e128455401d10bc0c1105080c01c02001610548000318400c81e00045010002e449507502c0c1e005020303c2c1010101d0480c0900740d9109002c480412004181008541c1c0d4a0706030303445086104a84c140b000007600c140d500a0750030031000c1404140518080d9003200f4111320900785411001c0152a00400007281701c1010310580c20302e4103900035021040c40046c407401c01e9a02040b84180468100b0b85814078842d03004080d0203001901454001082e4034003c981c610444041d40e520360325500e52003410890035403202c101c45055210f400407484d146080322181c542c0c003007034041003441105061040401d00c0c50796070040204540181ca4020001070008200c48031441d09880d0000700359507100c0c8140d403980a10307038040c2d038121074080100541480c2c080d00c80d410b80d00002e059504408010500740c4840c0c00c20f016480d4049000c0c1300c0d081d901c0700c01c1c5010b00310320b41c0034001c19900c075601010708034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 618702679 1250 618701429 618701483
    0x90115090b2e141902060402090108010915051f0305061b280333090e030a0c0c050a08240106050403080d060302061c0e161e080601080708010e12090d 66
    0x40246e04408200429440d01c4404103006158920081c4103803426035071030b0601820440d501102848c0e0314000b0800d40108a281d0804914201949448450312402e10941d40c0000b01c03030840c080e88a400308003208600b51001e481a00f40043c0d507000540ca41d0011581c1405c000b5401b60042642e507895294118840b956003943c11000100200221022110383d102d40004580000c5050350601070044903c0b140081228600c1081d490a0300e0580f9581c0303030102044e442079202c40d030b000c1c1103e1404a0310080104080b0302110400060010701c0080502d04100c00c6401d02c03402c0041501440104045604035000b0402e422075840002003941e2260700040700b540141082d546100003101d00304040c4c5100d4440d00f83c000c2c41c0310700100780d041005070781014a0a480e01510140c514940748503240c03403124401403c0a80310000940d0540c0d81c540740c40750303a0780c0a20310a0788215820010140e00b0044003241d418060000a6260f6107004109414042c3c100200b0070100c0300040d18031907203100700d8030012001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 618703929 1250 618702679 618702727
    0x101d060a0f050702040e032b02030601020c061308120a030507090305070b071a0903070c0902070803061020250e010e0705070606150f0e0a030b090115090b2e14 70
    0x190160a503a5803101c2366809003280100d030001d02c100180082c6a80014002030042402c494499850340010000e050b04c0c83c095012000343d1284200c0700d905800035102030265002c0302e9600300025507894000f101c0b00c50300c9210140c41c40d00f10b14801c1c441e00201c803000342000b6002c0d40c06112224007030000544001c800f1584840c0d15000459030344204016101c1440080c91510307825800c0a58944410f4003c0c4401750005d44561401c000e550000c1d401071014050790040704800520700c1070880d01098039a1000407a0901c4a1409101445076501141072441610741030114070303666078201010a000d0783e0313019000c441401824400c1d0b40000e04107000e010702038141300b20b90504400744940041c01c07440c00c1250103810b11181d25095110740e00c1d80c1804004030780d00046000c1654a8966403035005210100c190051401308240124030700000e60040c00c4103101c180e03101c10003070380b600419a02110b07201400240707a0200c18560240e80d40308c1c00607103441c0d6141c02c0d02c440c5404101a40d0304c070b2268a84502c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 618705035 1106 618703929 618703957
    0x1701140f0a030203100501050f0d05031602041b0c1b1805042402030f01061806080903090607140105100803070f0c05101d060a0f050702040e03 63
    0x500055402806445c400b084444c51940076007800d00455018900b503540c0c10141e400c08d441d6240986400c90080c42c00d00e002d81c1c285050400d1018026a4416110703900b00704480c03034a65020341d10030469100d03d01c00300018036004a407505ca011b106a0b0610640d0030400401c041d04582c840c0701401d9903000100c43d40d440c07070000c6440301a058209280611070310f602c4103140d01c1d80e000314011034080c51881030903070765240d04440c10004811011048a43d482041290038050410903030041420707002d59017001c9039000410195045288141d40301d41280080b904d0920081c495030f504001050b81904030f04d801c120145649100300c21000309003400e825072800c288104151b031080946002404050703545070006005102321101c0000b08034414a410803201c4503d0070400700c0300500030588403d44400c42c00c00e4252190b8009a4040e07800030f444914245881c9400c2c402071480e4005101c1e = true := by decide +kernel

theorem cover : BRFrame.Cov 618525179 618705035 := by
  have h0 := BRFrame.cov_init 618525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 618525179 ≤ n) (h2 : n < 618705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
