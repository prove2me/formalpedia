-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:10.465913+00:00
-- url     : https://prove2.me/submissions/7f78109a-bd45-4f8a-b517-f3c55170c4fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819244604 ≤ n < 819424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819245854 1250 819244604 819244619
    0x21e0d020c1f110319080609090f0a0b070e04050115090806090601030602131806051c050307020d0318090507080705070f020f040b0622050f010215060310090b061306 73
    0x10b000010420040380c601d82aa91500601c25070305259200b03c2e140803409514000142400020783d0181d11a0400201042e0101c60010324070b2215000180a803c400c029903ca044030340b00020b00d043c1c284052000909015681c40c03040301e000e44010090360f00d000c9056400241407000e140c014100c0c1c1d070b0092040c883c59400c0000c0c0141129400325000d60354580708210021034802036881321001c0c00c01c8042d41d40038002a42c000000b500e80948042004c40c80601082e0492440b010024000e43c008101e00c1003d0f05110748440c0c2c0050082c108a080300c0100c1c240e0300d41003c0603600146400780e540042c0143d659002e036119800051030700d0300c1e90420b0b803191500000c000960314000c0c8146001d407c0c07681e681e1100d0308000b007203400c000c09071511000200d078140f0280c0382c2d80d07000080d800b0501d4000b00381d81c900100c2101c412581a40207060171125205000c15901d00503041c80c0d45445400300c01c1404103200d0051402d107038801e124a07101800e025050000901d810b8111038641c50610b401440800e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819247104 1250 819245854 819245899
    0xf0906050703290307090e010c02120301120312150303050703080105010207030c09150504051006111501050613030503031501023d02070f0c1503050603100903021e0d020c 75
    0x20f120003030700740003078028030030000745810721542c052044141440450180740e101980401301040346602541d0044414000080c1e0074030090151102126415614002180c4a00c1c0d12800940c14000000f840702c030031001400031240700d580304400082000403542d0816901c9900180180300c2030005002d140c3c02c42c1c0d942c56515800d130045000040d40c48582d041c882168402c0d40000740f00140c810000c90900040100401c3c50f87c3c004c0c038022480603040c01940c0c1000046000c08405100e807841082d07424481084000c1d841031008a00c2d4100707003030000c400b28501b48011801082110300e1600085842400681041c1c0410000407494200c00041c4141c504581d440303860340406054512086111260040001d004034a8060600301d583c0275600200603030000c0c1c0100fa03408100e215402110300e10422000c1d5030045640c1d60700740d000b0503066181c1101d29007100c61082e00ca40103660318040990644a101401c150440b4001e80c48803a803008920303014051162032003010360341801c4810301c4040020b2603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819248354 1250 819247104 819247151
    0x2409050409060b0409140708121b120d06170307050606090924090c0307030f030804020a1d0109061706060f031609020a0e120627010f0906050703 64
    0x5241c8800c001400c0200a90004045180003032041000c42801d007003108000303480181e0b40545100d01c02c404241808001103401c484007106070302d01d10304603141c01100c190401d498200c5a1034410800089181100400a015800e2840f040041c4462810815080c00e968440513828560801c0200e840891004141c2e141d00c40c001341d075540c03d2038603203801251a0188024160041c400c4001c00d00b2116000b400540f406000013408a80c0d2400c824802c041e20b4401500c0020200030a401c40307a00060b01543c19682d1043c0010000c12255558103480c24140c991004100d841010b05e00050080100e01e105900240c0054104580c0c80c141005919580c0c0c500035002ea481140354054a0126030360030800103100c0211590185015591000080040d41001e1b4032076000c141c50f91200c0000782801c0044603400319a845c002c000341d03140c0881d0302115120707200385000120480d0100880b60082400341940340300350002c2c005111009402c00504455002d0004410942016140703510603120700c0c4c104d0031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819249604 1250 819248354 819248359
    0x40c05070312150801020d051005030c060a2d170a271104093c0809151308011a0609101b0b06090f160e060903030f04240905 55
    0x2030543c41d4025a03030405030b2580c4807212640c00043c1b4440200110b801c064019000803c03981d015030707102c0c0c04168075455600611a00701c0310a0144800c440d210b4140d604072000904881c01c1c8000450600e0b0120b441c0c2d074803010700400c10922540702212a1203115030740c4504216010071000a0940c000c514500b03c0091010a0b2900411301005010700c6414629440b64000e004221030400340c942019a090700f120b200903500701a4111304101018040c031100ba82100603038003aa190742c140c1c2c0f5480c803600510201900912083d442122000080c802080110041d00f90784088524012501e400d4495800c40c0c28185078404044046c2e035200c40c405d49039040c504950000420030781a0040b40c0e0001e041720b00820800180316007000b031029501c0c0c1d0602900b0241c40550300d907a14001c00c010300b0481540c4003100400401c01c1450018841c0c041c06034074450042690380351003507441c00649941c0007104548009080007608205030340c2c0c084001c0700c03007481900030081c2c130302490a40642070401c20302c205030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819250854 1250 819249604 819249611
    0x201200303060d031206030b101202090c160b0103050f0f0309180426030a0f0903090302040b010903061401080106051e041d15071202070506041515090b040c05070312 73
    0x1041500442020742079041c1c03a01c0030800303d035588c285200030759400c1d81d181022900a18011525001080d54080c00c82d4014100305660344030480ea00085a1107008801c0900d8510940d1000041c0200303600d900840c0500000c2107002d0078022081c0c2800c040b442c0d00d402560080040342410b44070b40d614042c1410610311821882e07511420660a8844c103d952207100c03440c1e4145070440d080340040614000c501d50313081044041070100103141114520700010303005c1148903908100524013034015450598043c540708650581d20b82e0703500151102c142c1010a101942001485881d90901c00c0c40007c2600304c03045840c03042003100c0090603202c03000f15140207603100d00c1c281c80c0e6811090807100200d542c001c222000c102d005105442c0c4094140c03000d0340003408001481000c0400c500079609034642010140c8955150791f900e01c882071000c21408160345880e400f03605082d41801892a000341207071030780030070400c0c10340782000125a2001807800600a0500c484404a903210f807000c1854600182c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819252104 1250 819250854 819250879
    0xf090602070905091e0d0f0507020f0d05030c031206040e030f030714091c0c0509011d040f02180f100e01120204110a0302130f0b0a080c070506070c020120030306 71
    0x5810015680da03980b24003184c02c004001d05c2240050855603250641c0d903590740030050850116000d201d2204040d6005032402040d0b41c1c2864440c21401c50107215408991514902e042903e08680140581d445220401410010682000d00580280c0110301001e985040c03164807000440d0302000c0d103820200700c485180c0307065001c800380c201d4030061030040c241111103450710f44900562016940480702e200b40c07080005858200400c0b09030580340300200da20001d60b006402180c2c3d0010082c4182c82c4100c40c1c551070340240e1542080c003441c0c3c09120307904200d00e2038207480c0940c00c60005000b6048020116074100141130351702c2c1c41c0e541561503404141e881400a03000003405800940d100307107074117030f00042c1440312940c0540c0144214030104036040c9400c2c1c0e491880300c082047d40c0c8a403000380d44003000b6014100380b0680942e54000a0a801e140c106043c0391150792400000302c9210008c1841d40211005540c0c1213038140303904242c03240203072440318400c0c1c000c1d507264000a01014082c20707404040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819253354 1250 819252104 819252121
    0x903061401050102032a03070609111909022a07081b09040b04030c05061f09110f2101060507140607090b1b03030a0c110d050f0d0f0f0c0f090602070905 67
    0x101c600014400c1f40e8030303101141404030042100d2042200d000c0051117030111030b418a8001c138014846000342071010b00303140c1860b0700082c0d84a055040d01c808901201404201d00e1020b0b8400c42c156050002d0090a007071189062800c0c1a4800c01098484510010b640c9036071001101640140c0c0102100069199454155000281404002d20a004880c00c0008181c60106000302100b98980060309450340c524100044400a40d14105010403c001c80391f6080034650041c40d440c00705800001060342c0c200c10900c0714201c00c5c1c101d00c00080c80001c107441805566280c1c0940404008041c0c5041d06184002624581c0b480c856212003043c0420700300ca02040018485c03072995003083c140c039983c2c90000078507001002c0c8000044003240d841000071a94901c002010034000d507203501c0f0306141c0b2000c81c600243c603802000d01500300c0d6842c0c003008006010b5038060300018070a000e0b400704540da241c40f0081c14001c9110040310030800070030380c00c12129500241d0382040750b00f010400503032900c5400d071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819254604 1250 819253354 819253417
    0x31e0b0c1308010e010c0f0e18091c170c04050607030c030201020d06170f0d0203160507050d05100506040c170a20030a14010605041509030c06090306140105010203 72
    0x48401154030f0000d5290310403c1c11b40011011400f41c2c0d9a42150f24503211050f16080300b0441c0f10340d04114020a0b42281c0351051900e00e03000f200c50300403190b40364408a812104060041030102c001021038402440032032950030455006400518039600f803034101400718289018041e00a010059807082035800d05000b0b5044605010300d00c5000d0100903281d60681c1c4e0384d0700700b01c205000944152a4650581007000c100e07682c61030400d41c05103180071002c000e4907641c43c0310240d0541b414003624000003181d588a91100800724411005000791141c00c0000d041104c00040485001e0360a2601000c05181e009249036100d080002d512103c903140e600030346006202442e400d01c0b043c480300300100e01d021001030255101c1c0703c6400c805d100d02d8070864000b0041110078404d003408a20144024001c007858881e42491018940c81c08101565903500c0f0032400010640c08803003c6641c0c4c01041c000e020041c00340c4142802e83c1ca070301c55415454500002d5070f81c840c02210007a4100f01c20300c511708002d26402c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819255854 1250 819254604 819254609
    0x50310030803281505010804030e100806010206070f0e060a2f06090304030b0105011103071718040204080a031416032c090c130b0d0204031e0b0c13 65
    0xc1c0456124508030602070071100b41c64154410003181c800311124003802c6030141e14403015250080084061070708006581003903018101700d05118210b0200c46142d12041120510b00000ba0303507061190401360006810003d0140c5000700300000c0b8110940c0c170304c0c2c100b10703c8844914261601c580c2c0b09501c3d242201c10310310380080702440e0325828040c422100d590b03503081c00b04259100d00359640d58441030492680da100c5c61200500391012200100519800780007103410f00c004420949140018079501e141c10303001020b201203129000030031240c00c07500160b003a8000c03901040d5011032506050100781c568034900c10600400300300e00e400c45580c10358210801d50b5059070014070a4010300b40d0f1458060071890507240855546200b00f0004080c00403540c0150446c0d080141001e8101d032070366504048103500840189003000b1b48550300203140030700f15005040d5010752807801a151410b602d40200b070f002c2401245207003814114900c1010401c040c0c40d060300041020443d5a0703035914610b1240c4818913a5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819257104 1250 819255854 819255863
    0x80f0c040906080705091003110103091406130c05030d0203090415080601090504060506040b0f1e0d050c03060c0408030a05130308031f060305090a06051302060301030309150c080a05031003 83
    0x1600043c00f4600010690300b503400403106e0310707600c1d40c1c2c04e80d20b000d80201500c006881d11085c0da088a10320350103030740710202450180300f510b9400e022802c0410310304181510080030900022001c51300384014005d884000e0601240a800040c040840003541c902610082c41c2c0b00b01e40d5600600c26150b10791481c04020400c0005440312076070340e401d003503000b408222005e50f081428480000c0b25450140304165040b88014441c01603441d411051050b0300241307180325a12042c6c45440c2c0c100c1580d43d0608150141c1c4030728010011140790780185418054042c00b5800b402c0e10038403090001007400b2003074460b9401e0f40c0c038002e41c641f40400ea41e80c0c10014a41d10190031000f00000780702d11010a5138070030003281501e42c0322080c0e00d6502c40c0704030216a011182505290130010b010740000792141c01190700448109010310468a4a0700050200ea0080c0c0c022408030345560010400040c58044200480101d81410542402541c44045030744c0306070ce418000b0800e000000800340b000d104410070241d40c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819258354 1250 819257104 819257111
    0x9031e0f03050d320601030e06090c130e060c0d060f09050114010e030c010c020609040507050a0207090513080a110a0503090102010614280b0a030207060605030a03080f0c0409 77
    0x39410041c02d6644102c1c003441000c0d0400707425800304213695081510005094840c442094482080440180009401c440c10103072200c0c40c0c80080407041011500441005c40600041c00b0424108001000c04880800d10075090841080359901c01055156100d503100e07444a07522040b02414200400243e04005452190705c0c10101c2d0b94903443c0d10441c1170350380000c03078014400c69202c01551007034080850356a140e4010301141000303511031524854a075201500080c20070383c8180004e000c2c0c900465880e0000f036400304480c00c1d40ca50412440c0000c0c41c0401c02080241403084040b41046002c580107401441c0020b422280700744288110001403c0d03d00660710880101e141c03035512907004040d1140150300301400480c9010300440450aa01c500410001c900140080f20008032044c401c330305024059440d0300084c0740c84680000302907845295500503030303a00d130320f203808011a8502e40081d400307907024003c0c110029420210345600b01c410000540042d42d0340610b05c04040c401d0782c02c0b0400b20303400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819259604 1250 819258354 819258383
    0x1208030402120708060f061f050a0203090405190b0907050703080613052707050a090c03180c030501180f02040527031e0f070807020d0c080c01120c09031e 68
    0xb0501c01c6c010b120700040c20b890b40e2181340410622001260740401550b000d2001d1480040c000c80042c2607000c10b50055a00b0801208000f13401c4540448460000040e40d0070010140e00d041d10880f5410481202e425026003002080100310f4000c1850080900c012100420100e41e0b441c0c0c551004481e400700240860300d8074801c1b8551626070034203100082581403030019030761103022541c41c082e500e02600c1c00c481c05140004c518040d1400202220615640c0e400300ea00801a48d84844081e50240c80d5504201d803551030401e0844003008544803088100802b0030002a0040501c00d9100b44c04881c085250f032120710000e000f000cac101421120884040c00e25407a50f00e4040050850491751a52070a540c40c10900c0551140c814490501245c0c0003c12565001038440c0d405002102d00213020420502d00640e10340d514030529400c02101c643c40410308920f11741e80b000380a030480c41241401d000403802654007800140039800300520130b42e12200ca03c00704c51203002e0001400c2d60002c003d10016035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819260854 1250 819259604 819259619
    0xa0207080c0d1404051c1a010e10060206070c0308180133050d170405150c060a14150f03030d0b0108101203030203090f0a0804050f040612080304021207 67
    0x31003281114045031240080c03c02510b41041030310102c41000d0002e0038041c040707a942c4d121690042900700c40040001003010076a18400b5800c178041d04404842c1111418071101d11050240180c4c400c01c00c5503c0903080108041d481201481d0481d81828110050f813180b40114030081c40aa242c02e186629000f07072160341080781d50101c20300005641700b11744844000b014090b110120303801032907007101c1001c90400002c0c50204480e00322070307030301c00030941009e03290340c0015048000702850910303150b00410b4441c0700b104240300d01c0d5041800342034208103a00c404090180300803c014005c40300ea8102500d41071017511650707a5039884180090aa076074590f0099410340061105441c0180001c890200203225030300d0180400082d44e80004d1803a10914441d5401c42c081c0d44003c000e84450b000d40c3c04500e00c2e42808125610b50300d44100080c07a02d440c02e010500108101c076a40c15481942049810000b22103031041c12944140c11152040d03890b92503001080211604964407807103841821000910300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819262104 1250 819260854 819260863
    0x312051e0603190b1503010902061803100905070f080f0c01030e1501170c1c061a0d0302070812090d08070503040b0301080601091107120804031b15060f1d0a0207080c 73
    0x7980a4202c000e05c2c140b800b03060500321102200000d4210500b00111038040e56050b00501004074000c04588181d001d102c0c50030182c449058085680d50711000b000e000c2c042441c500140a441d110006000c00041010300d5036a400d60b1030105414940d031940c42d05020003050225908148039414180c03d103594900706075040003040da102c03500034007038030313106071050b2814890000b011711007003884000c103000329164030703004007154280082d0101f002d45d60300e010f0b512150020489180070740c01078811640f03403000b6141061080111100c2d0b1890411445e840d076036030400f90100c1c1c0760308201d4443c0c130b5024034603246146108035048030040282c00f000026041400040c1d01d410303114130b503c06001c440d40003a1088218013071004001d11120900c629861843c0c429010340358081c0c024900004181800c54641d1145404401c0580d0414985684051016002e00a0038014500c081003020302900e40320722101c10030030340d1228805004001740030503921043c07a01520402e1f50003800403507540c00b510120b00d551303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819263354 1250 819262104 819262111
    0x5090a0209063c01050a0c151d010e0f120d050903090603010f06020d0c17030604061802070c080f2a030318130b0a06200f01090312051e0603190b 64
    0x250000c43e0141c00d6501c00c50955a1004043d100c07070070954902d0f660351000700b40346c2114424090390f52a055000d0790203503440c418001c0d05000001000762600c0c0601d07082c020b41c1a902e08281c1d02664090301003240301e0b022904602241c000000d40c1e5143c100e1414103601c02c0072209540b107100800003003503018510400314101c604940848040c0d40340d544069890381d44621000c0d11580701c02801845901408000716485a40180001950340d00c0706242e0440e200031000119003554049188020070000c001c0640c050420325008044440740459125a03607c080030080d0090502100040400b400e03140e818100004020192515405421019088259805d0210344240c030390103002407028480e482802541840075109070304050500c2c5e0140c540b070352120100314444c45c01144480380d131813050154914005007640085000703155400e0060400310303c0c1110f031240a10b4901840b00820002413030315030124220b00001250754921340040d0801d0428800c101e14042004100c404102603448400c1c130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819264604 1250 819263354 819263449
    0x503011b091d04110f0a0e19020301030b06060c0a0f050d0e010309020f010f020a20010305010e090d1404150201050106020d0309050312040c03080c0705040f05090a020906 75
    0x865032610903416101d0040b892040400300000400d01044000c0e10301d45104102030525015407031402c0c041804103030540d00c40f03141140c24400b84a803001041108100d0450008025421541591108203542001400e02d40c810340000580100c1c03d101441000016500302120b1142d0940030305065465644907078540000401c4408014034039800f81c8190312000e80c01520002c10b031101480152440c030380003d520f00661050700c500a0000b164402080c03003082c540e1440606c0180c00400150a175441a0003075207025541d4010001d0582e00000c0c0d042009045244c640b4100d0035508a00c40c1510841c4c00c402d00e44ca6030fa0000b048440d40540247d070480b10340d13500300e40034039030b441130210112018514010505e804c10044410b25545188880750454015516840001d950b692050b403694480840d002d40794020000410880ca424400c0f413000301c0e0340d09030521851812008150715180307030100091060180c200814050f44074000c00d0703813007100e00c910791501d1000c40040070100c3c5940307a0403048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819265854 1250 819264604 819264617
    0x30c12010b1305040327230f0a0501050d0908040306051302030f03040605071103010f15080601050114030103121e030605131a0d03020c130c030e0c0919060503011b 72
    0x10001043c42807620917a056502c0048800000066000c81c900250f03640c084c0c0090700314046800c1901400d400b40181c451000071482c1440d010904c11030f014414406407040640220401803640c00c4401c0780d0b80b01032a08000125446a440c1c04292405136070400740800b8501820848507002440300810070300c0c0204d04945144808000701d070351b20720076800352800044052000d540010700740000343c2903008004001050340709041c441c0c83c0458086031034203c0100c1d41c0f01400c120780d4606009040c050502880c0c1184c04220352034030b0542d42d03c01880018000400c2c120003a880341d22a1a03048207941265600c40110746c425980103018000c0e0303004e407a10658510141c600180c9151103203400300e200c010005681c0c0b010080800940c88610102641075008500041c281c540e03495005c62000314810f840040c40c149401001811101407070b260510700da0007644c2148240c0d45200c0a00c1d4400e41840000844c0c40510500d90050f0070107600943c3c144d0b0821500100b1468416452803e54030303596541e2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819267104 1250 819265854 819265879
    0x403110606031b120a0b091c030c021237090e0f1302012610050103021e2d04060f0503040b0c0702151207091401080a0506030c12010b 59
    0x10f4881c103040703000143d1140300f48903c41c803d042076002c250036003059105030744401101e0f031a0b90b40b00c51800c544002c05174100f00d24400755000c076010400d4401603540740c100b11091140c0e0000e0356402030001c04405000300899018281821038254100d07c0c00766814203a0001040d0016036041c282d00040080400e6815602242c003101c0306894521603890705621004e00e40351100d21650300040010143d040061b454402d2402c1c084d0b10340e60b5034699446600c0041ba03031801020050604038603030445410140100200800301038041094000e07005402c0403503545078002d040e0352665121200f6040042c01d60960780030303a010a00c802500c01ca50340c584a5500c0d04040880440d01031100b01c80003001c0082420209440c01070030009004420700c060050b11320103200c050b44d50219000701d074030102c150070540104900d4550005882c0010314080c036000c1c50030072110740041d104040060080c00c0581e074400c001040f95a04000c4140b0000c0080d03c680d03607100c030100d80b1502800702a000a4001e5000e040c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819268354 1250 819267104 819267109
    0x80903011506081303081906080f0c041a1e0f0307090b10080108070b0c190f0c050301200d0b09011d0906060f0d020a050a080f01050c18100c05060403110606 69
    0x352001d44c0d0341035031030f1807086d030300c00600824007005180c020b82010758508000c50440d0041001c0705602058000a0501854900400041e0b982d20340c007d147c244414002c44850ba00c2b0020310030362a00a00640c0303000c44001c44080744100c1e443e0003040707a061149550025150005074000d8004007025a411032140354142c030290f81e124001c0c82461000d17072141c4810014000d11a0140141018903c00d13104011800807184602004581044c1d0b020030311611540204034900107508010b1409900a001e0220880d808400400d40700b55800e000810018040c224280268026120140001e00c460020750715002c000300408005d10000c840c480c18240820203002d030004a891180e8001400505115401c8003030048450080e082240c001600400118440c1c0c2d07030a020802800800b0300400211b151090002e0945e0000f802e0000346071030421520038000c1d003041042c81044020b58041e0824a003e1a00300c2d66080821405422402200c0900042680c0000c40e1030554100c00116070198864004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819269604 1250 819268354 819268381
    0x1d0402030105011704030507150b0f030a03020d03240905180a080301050409110a0605030a0c0c050601031101050403140a0c090b01080609060609030f15070c08041208090301150608 79
    0x41d00b4041124118003a0502c850b6800c1c0540c030038401d1401c0c6003000140d0780e9a04403007440d2181c400c81d0903240c1610ad162424100c0c0d03807040c5101c080300104288209900c011752142036660134182050345500101d8181116220311780107400b03d41c2c2480c1c402954840a440080c281940c1d0301c42d44a07101000c004603c3e000141d80300c0d10302e40000304640386074605002c0000034402040110740d6a0b0885460b207401d65a040b4105000301050346615681c0e25082803120111205002d0980c10320002c41d8900c4045040002e11605490b8084003d0104500443c010b8605028651008140d03d030b5509007000c041c500411038031200c0b485074507502c9045482d418501c044e00c940010b450700244680740044e80798a040f00e030494001001800c214600706005003c2401d00f404008408180e6000582090314110042007090b48101b0900c0c007009501c000d81e03540400784c07096202d44006074803103112000078019280221402d1000041c002c00c0b880080f0b401c01400343c00c0c18401d04003c03e43c010000b82c1e50203003940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819270854 1250 819269604 819269609
    0x1b0106080c01050324010306030206070c030528080d0b0904060606090506030c19090b1611060c0a030305090102040f1403010f06060e060715020f04080601050105160210020114071d04020301 83
    0x40707034410305e24044c1000500300404028080c105030303c0300c50020160b100c0c0d40040a4403030140070b00c2c0f10b0b61400c0d410841d192250044031030b0395900640111483c2c0e000d10403045107801d079101d15429694210150003102030721082d6a1b569000b0041c00078001040f24550001044407082d80700c0b94003440d070314010410356000071107182c0542ca1041011480303042c118800da8403052400e0402240080d103400c8000c02c00d0300900445d4464000c15660307002031200c5801c7c40d807003805044030303044d1524059481854941011080c0181407503103131404115248002c3d0142d6029010070540102c0d11981c2d400040401c1200301d202500951030420351001800250040c8401c0d1441a00c030251074170404014031031554881802034884980d200001062880280020443d085944200c2e64803141060401403e0910603802503052010400c001134403c8030040ca003024158040722448984180c08409074003414940782000403240c050350400c9041500f1035022041032041065030300541003c2418003040748030a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819272104 1250 819270854 819270871
    0x315020306011e120204060e090a021603050a2307020f1207150306030803010816081c11030d05070206090114010806040807150204080c120d091a1b0106080c010503 72
    0x2030541001c500300a060f2414080861030083c242440c800301c02001ca070015000607000451135a000c1c0b040d8904002110b8024a090034114a0700640c3c20b81417a4040540c03400405019010960800207130161101e5441201042040c10b0b0012062550021369801410224032a214450045001e0b0034090001400816060002c080c818180201820030441c44042c140800d42c4900d030210000b60041c0145000b0000603005125108800d0510302c4e803031402d41c0040002e42d10110b00400007101c0100d900e1036018017403c0c001d0000366014206c604622410540c00c1106082005101c03171594002078143c4500c105200070014900304d4908098020020f1007201c010341d00100201d40070800c80360080000f20310456005003442034508e40740050781c02692042065810a5640c000141401d08031075003890103490180000740116180504000d0320360159440030580c050090807400340c088200e84240740106044401c3c103450f0080a4060085030250b68001c0c0039010b82c030701565014805590103144030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819273354 1250 819272104 819272117
    0x26060a110c07030605090606060a0f0f030f023702100518120c01051e150303041a1308010908031914010801052401050708030603160807031502030601 66
    0x149200000640a41082411822020010700280000402c00d52009602c20070300854603192201c0c9550030700c040240310030f006100c104114100580d210301521311910303850410540c4c900040758114000d040e1030300b40f40300c3c8501c00200c3d13420421400c980a1100d114000b801d55151020308811142d2000e8020306a001d644034400a0444480a0f00907560100c0014100d44411000980305071405230f110881c0c1260030740005810102d00003e00038240d004007002544a400c8284a001c0c00082c20300901740c0c03445102c1c0d01d0b04a519030b6000d20468006044424603209425246404c5402c903a1201040d01c010030483c1702c00080c8850706000300c1d0001c0c0d800c40c10144c1103654280e02c015141c2582250800301d1342e41c80c111400ea10361407100842c0a04401000080d107450140d041440407031000304103070211751074004091041e82c0d200c8201c410559020322110740b81c3e240c11340803918001500301040070f80071221401240c0054002100700440703000c1c0d10040c00302162945000b0032072005480c160300003481e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819274604 1250 819273354 819273361
    0x5090c060409020f1908010603140618060315070207061d030c090405030c012a08010e0a150528090504020904060b0303120411030c120d1413060206012606 68
    0x4643c0c0030709200d80145907405d1030051201c0c04000000320301113003940421003150042c0310659161003201550200340c04070111604111000416600c44903070803042d195081e81c00940d903928140000905c08400041d406c40c030341081807019490310b0803409030100190740203202104503104e0141c04d076171013400035019107452000a000d01030034120080068905100803ca44038a4000900c600d4001d01c0d08100391142802c001d6070b8094032603230201e14003000c00821000600820740e01308040c03508201c0414000800d69100c40f80305082843c01c0d0700c00d540c42001560902182429803400141c181e010124141c08683c5690a9500301c1d0010b440c0030b074100110400060000e02c0030391000d03642081c020212404c2c10000c1482c40381100c8120b5080702e01c0c84c0d407466804c0343c50404200b015030b643d0044a0301e1018440f8580619079500030b0140d80010025680d419103504003255003102c0740701c4c5200210b0755a0f07a458450283d6242030a106155840c6400140c40b142d8558440340004141d01e80b0b00500410740307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819275854 1250 819274604 819274619
    0x20d0627090c1703071a1e040c0e0601030605121501170309060a030b09040f1226130f0f11060306060904050a02160c0e0601020c10110a02090405030d05090c0604 71
    0x82109043c0e104503c0100564000720b913020000d140441c0918804030303c00d181020f001c8100003400004542c1d5484c926051000140d80c41d44488299056a070f10743d285551403030300407005003030b0b9540710325040740d4a005a503240c82000705008030941580d90007840713180d81c2e0365030750f0017110301c1c0741a212001d4109000800261424030000c2c52104000d01e8003240161090001400002007900c0031600d00b40e07000c0041e401c210215888031a001d03e942041903211030005240c1d060740c55586480048d104207400003490900403c500c5c001206d422a0b1006000c901070300d40031b5040043c1d140d066071410884805cac00504e00d450f1301102d00c2004050803850800c1d01c9001488090320002e40700c0d049840e02806020701603101e006820743c0442c0281c9080214600c1c0c282d0f055075900c0d02500310740c11500a0056009182c4400f521025408600d2070f08142043c284043c403824a480c5010086d4450702c2c180510050140001c0a0302d03611201c40700800403034031395982d00c4d582c5614441c3c20a030448402d001c00c00049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819277104 1250 819275854 819275879
    0x30f0d1b150e0f010e06060a0303050f0c070b0315030109120c061b0210060504050c03010302100507060c0903110d33090309060906030b061c020d0627090c 68
    0x11481490701c05884044404000142d03441540c00307420781da002040c00c00010a090003121100608040a0042410443c0105010b010310b0f020140c00e000c2e0004840c0c00c50162401114540a40107003914001c940b9000740c00381c103910580d07a002c1005881044101136203018418110b0550740420b001143c04681070041e43d414400c2c20b0141c0321240e8514040b0302c21030742c65a9003811500d03150f01501c09600307203464503400c440340c1e508a980502d2034941004a090518800c42e415603030102c0d500f030348441c8031090403680c41c0300741c21000340810304200111448540040181c4141c91040d840407520380613036001d01c500109000006010a15420b884100b00850000aa0740e0f031980c030199400c0043d512500b5405a80081340201e0028040c030034100807143d440290f11018080a240a01c010300c40c4000080c0315020380100040c1507503042030350341d031685181d6040b11611102c0c007006000c2556148032070300c1c9a80c114508415403020a5042c800900350380d00c9151040340d80151018101c03410f003c00c01c80e40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819278354 1250 819277104 819277157
    0x1203170115032304080a0906050c190f08041d06010f020a120207050315090705010c0c0e0a060915090c0203120f0408090a080601230d170f0711030f0d 66
    0x50f00c0d2114042422508503808644241d0051400b29070719080d03507400508250099002004011061040c900e0025010a03007140d1541c1440c4907c1c0683c1e141d081c5070f030785a00381c039000078038071a00018006113528003240c003c078040300c818041c19000c1e5601001580c058020503000300041c0c001440a0f00003d15601070740305d55545d1441114449500c481c0400e10384603240b135045000714000c504010302e00d08c1c10481c81024000a282000c0c40e071045560b0114041058090094200d40000024030210010750165000f403034610814484180ca01d2840305420001d40210f071101800d0116010001d40004200c1780346040480c5030804541e10301841d50441d0030050000c030b900d0b04c001c22008900340e440040300400380c5444009884035524001e601c00c5041c0001c00302d2240e105000a07c001955a80350041103220340100b01c0325a2440d000980004522404100050001c0041a0170007800303a04150150135150a904070b402d690800340c04103a4030b051007040d02000070800c1d40302101d00200c0d04014100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819279604 1250 819278354 819278381
    0x105070b04032714030d090501170a0209060301061e0504060c0b0903070602071505070c08070b0709050402041811071e1104090b04051c0e151201120317011503 70
    0x1043c440d4a00c8411805510b90b0001c1e4031290081490102407800340160059002c01d03041400e21035140000180540c3c01040c810808440204005561108035404035000028014403256070707036850304c034050480041c80311020103ca014940c003000c09401081150700f540c4554580000c00c2a9555a200103618002c103c03031118001480203400003640c03030000c0c06079184104182e1000748245103080048490042c201c0080040310341c01c91001c55001c1701122129a080021072030266101442074602c1c946a07403206400500c00140001d0380d02c880d00800c891508401c80610450b05610f00700061802550406080d0a407260040c0304111030420b10780e029544140c000d0484c031602d00c00020300f222041001940d05440c1c0c6c01c00c1000300034040c45940c003079901c0110400c41c04903640c078009112040c0241440c0c085c5c1c14544440100d5480c88007942e10113441c13001d4884156031581c03000d00d00c518403814101c000c03a080e10300b405040e8103500c81d4141a1907440a07042c84c0000385500440182441c0440c2d000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 819280854 1250 819279604 819279647
    0xd080106030e0f060127050c0c120405011d03160303030c27060804021507050a151e0e1906140601050406020c1005120a0518011401170115060c02010e0105070b0403 72
    0x2e004100314040d1f58403a410325403030a40c0b2042510050ba0a003103200b58014008501080144003e13070b00030002d2098403500d10201c00c400c03000800030a2a0080b641c100c40b01a4489660001c00c041e0f050300040f4038000300f945c5030380e078a00c0c070000078411907600c2c03201110b000001405c0900c50315200700c00065001d40010015000e034940c901e42c036034a80d40400400da946030044207026050000c40041aa035424404208100d8450001004a82c81016070120341035140c0701e0614070b403c1c1f141000b4404110b190103603266508091460f09800400380440120800d10041c40026855030080060701e044135080c0d00909401000340e400c204035a19125245400d10500f4442d8a4060b5120380d0460312a0701e1800f00050315081c0700c0c800c0c0212150582d0b500c1c14a80c1801100e1010701c0e4200482c604441907541240701429051120318090080d08c2c42c068270075400e080c00000c0345544210304040c103034002e0b00d81e6032a0545500045403c1c3c426840d0140654100e80007140009104a140400401b100220035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 819282104 1250 819280854 819280919
    0x50303031f0e091501050f060d05040c05032b0509011e2607270314100903180902030c0a260a0f0608010203060a030b04140d080106030e0f0601 63
    0x30042101543c0044540d4032000460111100c4100c285014103402c030b03030a01700d81c801c400000d06941300e4248082c0c0d049072140040f404100801090201526004042c0c903015541c4e00400900b45100c800c822008400000341c07603802c54040c40c00c5a07007568040e0b40d11600116140000d00340e00035048006820011540b0700070000b01d02c0d041c1c10140d07041000068407940e05101e803006061107801c01c0940c21120094544120180318013480350f00f02c0364001c51002c1d842521401440c20708542003c40c0141c20300b021303200c0d42015882410303028040c16214040c10510384501440b022800101d0342940d8043d03081198098071406039040c0200c1000d08860000e0400400749030098210065694459154441c100750603440f41c070b401140090501103008505510b46a800030324820348500c400b41c0081c0c0080c1c046000d00210114211000d101c4604440386070310303101c81c01000c00c1000d101340c01c00a803a009908200c03120204252441c0e078031070780c01090581d09015220302c5103420140355880c81d42424038075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 819283354 1250 819282104 819282119
    0x203010f0531080a0c1b150e01170a020306090a09150b12010603030905040b0f060a0c14010207080301091a030c12010e060f040c05090f01090209182e050303031f 71
    0x1c0490b2003207079807440c40b441121301d1b103407802d25054a10344664a5030200240401c0c040e50140d46841700d182d290104240f810a0010783c2d01d2889882c080c40810b024404020a04260703800844c000d250559012039142d0300d00d02d1103c21140090030040c444000402c081d88051a586c000d6000d640c8020507031500c8843c2c0e0384000c0d086030240d5004801040c9411410041454a4401d822030030f88161011443c0c0c3d1000c0000981d20301c900b8000c03034103202d010408042402800c2414450004290300215038880c001d060800d1660402d10500d60030341e090400844ca000e540230040106208043e00506007400a20b042018003104407150a0083d941c400b414885101c04001280c0030b8600c44410009909160900e20150040740d08100c0c020325003c0c0501005020000d601d904550a54100503152218840050386444c0036241405114a00906002c0410400f6540e0307075000000082d140802000e150070b21200d9181c512550790315402c00d00028a0846030708941c0d46030754600e150b40c02c03440d43c6c0742d801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 819284604 1250 819283354 819283357
    0x9020406080a0b0402010f0c0c0b18100806030d050415030905030f0a091d09070603090215040603150f05010e01080a0b3006010b030606090d020a060c0203010f053108 73
    0x1050b68145048000c2c8001c4d560404410080011103103850014503c1549400303203d40d080d4403030120038441c00a07601041490bc6806150b2092000707145003082621088010881c140035560a441380c0201d0a640041c03030b0103a8100c40072100d248d00001100c81490000380c0081c10034040c256060300003008612a90036000c0d0041608101e00d0302c03180a4035040007000303500310100d040c421700d018001d401409800400042c010003111a04d207804555007201d8408103000c0564a48032010302880440d000c16826003540003c0710140c40c1c1d180b0003900585d12071800c083d0851038414503000c21074044641003e94070480681d9400701248101041d021b420070301003484045d6900c007204620034109085050400d085030b0307100741007000c84018902541021004655440050301d5184035500005204007162282c01c403903018507800514030960349a85401c041c01c21030091900f00c0c444c4d480e0850450b9481d0151003200c4c0112070f002c264080440041484208102c1c10710700319400451420780340000540c03841d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 819285854 1250 819284604 819284623
    0x6090f0303061e0f04060b13050f0a1502030409050c030a05130b0c13030506040602041a070b0610120507020304140303120f1905070201020d0f0515090c0412140c030304180902040608 80
    0xa4070123030348001c580704075107051040350041446010420f41c980c06a5454041d040250340c1d07280c401c00c500102340c0d1016480c0d40308517803240d90750504005c10888086001d10185125584402d0180105c0d03a80b20304050f89803421000043c050f885d402c0120318080442805080610840113a94094a40302d44800c1d1500c02c044404503981307500042e050154021822031200842c0504d0015820f080700395a6001c14540000c2c4014000c100100c4030800251141c01040b4021400d501d00b0031190401d404001d440ea80140116807040005941d0b180b1036080000c1195504100c1d40b040c104652118100310481140c06070031102e002c09000c000c280303814510310500e80a545a41c00040c1e5403200c1c88500c2d410789449222403e0481d1501042103108040c2e001c00041d4110b040b11003400540e11840001094000c0fa04501010a80280c0360410440a004c0e4840f140c8140800c840c0c050201008056684c4610300480030a9a14008000d00215494004000451000300089083c07511020418038151102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 819287104 1250 819285854 819285869
    0x5011a2d0408150402030d140f0d0906021603080702071a0c2103040b0f0906060d02030f0a030c060f0204150c05070b0715060f140108040c03080c06090f0303061e0f0406 74
    0x3c40a0100b103140c1040102e1000701141400750300c0d1000080c0c0810b06010b120a541640c04002075034042491b8160700c200b0010382c0c801401c40d02c0341c4c202481421540e484010817008940c00001080c01d2600000c0c0800440305600002d50030038a80102c160003541082d140601107200301c000821140003d6044c9880c01441c0d0b000e506d8503480d160910011440e8040c010205d401c10325428801c02d02c00205403268448003e940d800309410351480401e182449000c8242c001d405140c80c00c0040591081c2e001201da0b0280206012018200400001724072a5210704031581c07031020824a54203000b0110302d841c1900850030703961074580d030f00542d00c41940841c03400c40d2080005540c3c500004242d01c40c00003d00341102030034070120f00340050700100c01e40354641c8078140024080007404014800c0140390203554030070021620740380182502541d40505884584c450b0140420355285030400005880c0305583c004c1021000c1450021703071f07040007101e1381001a00405d1507004103d0a80b40c0307000d600000d1509 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 819288354 1250 819287104 819287143
    0x3030c0409110c2e0b0d1b032f09064f0c020a03020c130b0a0806040c080f070e090c12070f1409041407150305011a2d0408 54
    0x1062050100340101d0046445203030a056030717142e49458640d002c02e994007280c07260450044260b0307181e244c1c1e00d9a01c0200368121008241c0c01c0c0c4c1c0400760b50909124004090801c08800300c4040124144003164a907030000141c000301030340c0002100714109102c0798080541c14920851441c0b41104d924222001003030700328590840c41c2c0c6003075803250141134030003440540074900590750000c0d141c4114203203c074805d426030180050f04410b140e10200036a2002840860340316541d2030701c9074696000b2603040d280c03044040800542a1408640c40441c00c0c0306a015211b81400c2035040c1480000140c8402174030310407601e500307031b0580310800b07a503006c1c8107204c00608504d4545007640686030300c5d607080442d108061620906c1c3c0e40d180c4c0d4210540155001c2841c1c6441201841d4803860070750950300903000b400f80c01c2000041c958240c0d100c03a050b20708504941001d59400c94030f032003051040c1248020303a14054118107421858100700c202d02d00e01d12050791403400ba81c0310304840c50a1040d4a040000108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 819289604 1250 819288354 819288403
    0x70c08160b0f09060c180d0f0303060b1206041a030109030e120c01140a0302070503030c03010f091b030b0102010e0f010509071509090506040204090e0303061203030c0409110c 77
    0x400307920481e403154041c0421030385450300008198075900301800c1c1100000300401e004150441100302c41c1c81113000039041003080030903410070000c20010124190082031500700701103001c0c000304044580152038100c1750401525070300140001400c520040d41068025100000f009543c02c1c05a02810790181d0342d0703e032485150b00100140642001d0069406034800a440c4615036000b5418102c41e0f0b00e12051075894030186c1c01d00340c000c2c0c400c1d280020902c3c000041086038030400c2030301843c1a200cd030031007a03428589500c1d03094119124403000614000f25482850070f000d101e50411111403006200124016824081e081d140c00d5510340b200d60143d44440c1080403805041141800519407200c080d4020369140d507010b0100107143c041e00000c0750710b550000e00d060b140c580445004004060781008503509000840c1e4032500180ca60301d101c1d9810412224181d1b0b400000c0d2402012480d0055160900d444410300040544564140075446c007840300c402500d00c1841003441000c0d0000c1c0c517070b10300d05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 819290854 1250 819289604 819289613
    0x1515200a03080916050613091e0e0303010b0d0e0c04050a020703030b040c140d180f020f090402010801090c03060b0307022b080a0b0102010207140309031203130308070c0816 76
    0xd0440a140d84001064840c05a05594140844100750f48a50b03076400c0c030190592403034034a50800c400c500c0c102031242038020b0b10440e1402009c02441010002020040e00f040e469100a12507170f220102c041c02074014a61099003c002c16130400c078200d95442d240000850107031038003252030361070403540814520149034160150700038100c001c0f41d040119406218000c0c0c5010b4a4070007692100c03c000c00c0f04001c1c08165030040d20700c888040b0b01407482030710528003203e8050940b80c1c00c90240c620006842c456007040428503001c1c0d98161034000403a07080500030001003d130a044001013585a9900042a9600d480110f000d08001d9000c0c0541c041103e0005c0310250070103a00950888440e024601d8003548111050f030001c03030341c0201003441c3ca00385004030701a0081d0304000c1d0000701700006250a900c0c0001c0201114101030302074460503131010008403501c0c0011103010220100f01080c84000901c13512150b944184a8285078030303001c0703030f0b0b4075100d6240d00b12000700f0100b41503048d1944e0900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 819292104 1250 819290854 819290867
    0xb060c0607020d200304031101020313180606020105090604080f0708120a051e0609100302030d110f010603110f0103150305070e01150c020d11030a03180503011515200a03 75
    0x301c0c0700b0310443c03c079010f15104c65540e030300c00c2c1d2201800b4011008005165a8070134012201005018284036004544440d500d41c403141c901c2d003008003014608580002d041c1c4c010301030f1511800444020b040c40f03549585811030307503a0006440c000700c00c00400c82c07003000500d070342c1c0501695032030f90300d03050f0041c0380070056041194030161011081092070080700701d10a0520b0b4072164030007016940384005444d5002013541c03444250704025814020f004250004da50f1126002c501c0c003c00e1002c0352661210031401c542210002d000c040d090420840603c1c0407401d100241030380c002750614001aaa021192054000101c1600100c4107500000c108100141c540004580540b03030030340c0045000001454054140301420800a0188a5401424060201e901c0c0d100d408218041e0a40d0f806210b00c1c58018080090541c105615000081020506080520030140d2055a04420304009810002d036801204840704800b0200710039640546422640f09400312499410100285854219440e01a005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 819293354 1250 819292104 819292127
    0x10807181a031b0f03010b07060f050c0901080f130609080904060602030403033f09080c030a1e02060705130f09050708062202090301020c03040e0412030504150b060c0607020d 77
    0x1900c505102440544c0c1070740e4202c03411100160306890b550f404034030744140a0141d000d8101d55040c501010403031401d040e44014500b54109903110b807940d80c1c5001800f1440e500c141c83c03011072510300c41900b100189860f40b14498140c0500200b40c10030f081c00c40010240c41007504280300582002c1030400c00c060300800c2c80d41c104581c500280640700c0c11050800d09681d01c15244140c01c4000c3c1841c1010440c680c2d11954040f504410b005a581408000c0e0720769903030004954000082e02c5040702d060b200481c9646004a5a87d40e019204540390600c04441c1500b00641014050041d14800107000d07034282c42c2ca4004000c00e450100d42450441c20141c007601e0014401030103001e87c0813a04050421610b03609401c1b20706400300684070092314010a00a02039808075030303150320001601042c0070f102106010703c42d6204503000c4a540e00b080d142241612800e41d8010b140b0008070314012004034154014180c808000782c002410441d07444043c40c1782c068240d83c81000b68000d070410f81d062546c013803000000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 819294604 1250 819293354 819293401
    0x30b0d350a0c0303180501150503100203090604330519180627080903010e03070506060f01111005070906090f09110c0717010c0905010807181a03 64
    0x38041c0e0403038054481500184000c0401d507403a45101526200070506541058001e03000304420602103c20549107041c0f8040d062207403160100c42401c2828a0086070b20604009000e41000d40703030b0b5900c001d0380c444031811402e400c81700e01c6512012031080300184014100800b20105960800050034a0780e480c0e400c0114001e5800c0201c80d117003190149181945040d4042000070f4480154440442600600744180f10356064030411001409807040207040500c204074002c00c084240742034050750347e101c1e0800090044c2c012a001544a1030003100a000e0b09006041800880316015421402c0141c860240c1125139600d20a01160380d9000300d0183c003030040f500b4408080340c107000b904000840300e4810344002c1c40d11868500c0d49950108162140d4841389000c4506103030302d607008034101c01c2c844688180c0c0b541c60a003071070310382a1190901008031074060f11242203589605804407000400082565203a10340890f0005006503450000c0049203038500c4525124145000008946150801d8205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 819295854 1250 819294604 819294607
    0x21c060b0406080d0c0303020f1c0606020303061507030509040c031a0a05011202031003120f02061b0315040b09011415040303020d0f030b0919150303090501030b0d35 73
    0x3406100044e03814042c400390411500348245403804a019206580810340100b40119860850104c0c0c082d100000c20304034031080c000f007905d0704000c82e80d074007085802c2d551182c0245454a01421070314020071031030b40030785801c6107861000300c00705040c0c0d102e200300c0340002075985041c040c80388020000d5102481003199042d112074603000008014aa00340c80c0700e0368907940000413414502030b1017040001140c1c0829111010301c4410702c00b801784009421800054001c0034001070386110030841c0d001a480040c207106045458148040c1e00c01c12094040b15002540c9003002c0c4d00d1a03072205001d078028a480307145210503280070030034801c0b081503444143d00d01c06800c0c88240b00198002c207040355480c48030b00d40884090511001100a094218800c981000c500e00c1802240d001580040d003045400a8090100180004180e10400764612021f000103d80020a0005e50b2090304440d100750310083c07540e651150251901c070005030b102c1034850315078a00420950810300601034620180042c0302200c0c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 819297104 1250 819295854 819295859
    0x30c0506061021060f0902040816050109210605010b0c0708150f0403050409050403030c1412010b0a0c020a170d0203041a0306040603052d03180d0f021c060b0406 71
    0x40c2007105903007030f1510035080034a880700407040b0076400341c0d0081c8502e60410b481c079036a80503c00000d50282c0600e1603c0c0c01400c4031100301e180c44008940c1140c01c103030756003007007545888840340381031074420003510860f032003051840003084550003034901800022078035595651442e141149040d00542c4419604c2d040901501d0201003800b403030700d03403024074200b113a003d40d541c0c1c0c501150713248995000b200443d89001c050005240c2d05611640b4103102588803850062041c0d00112154001d007005240340ca800030340140642d02c1100d01902c44500181440301340b5022b20381c006503050309160407440c0040c585080011620708204194400890180051840c143c00c040b0141400c54410603445005540000441c055803100c1e84100010b640040990700303862404d902c0114402e030350840e002065180d0280c0500403200c0030040310012064012070b0f881c003c070a4418400c207101240703000d07140c2c0404940d4000c056102d0384500b400198410a080801c05414a48001161560040e00d4010b6191940030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 819298354 1250 819297104 819297107
    0x150905090609061807020d080609250504170f060a020c070905060f0a0303080f0f0907050f0414070503040b1506071e170406110c030a03050706021303030c05060610 72
    0xd6008070007660b401d016940c2d50000302d08883c0100c1141038858001d04204402242d010441030507110455030b83d0003041d1650b5041140c00340c070a07148005403100d00c49100d08104030781c1c401c02003005814108981000d0341c80b01805407140071021055440d401c5003c0c05201007800744030043d030040e01c245046040c54a01000c035641ca214038003510380c0342e80d541c0d400f00c1d00d90b64a0304c21900d680c0038002c1c10080030589901d0000d004207800e0318400c40c0281c000703020640c011281030056124070300c00c0006010080c9440c0030010010802031015411507030f45c03001038682900c02c10050340b00303410702e454450382da007458a03200b80b8400c002003a45441c0c801d542900d003a20b40d5884110781c401d075002405000001589805490340403a00480100807101011501c141c18083c10045d008a402c903440f0205280a81c500454071400310301219503154100c0281c2c07000284c0644007810350300e40104801802c11510005004200e5010b4005070701140e01c0801040c00c100040201c140d01c210b050711014650400601d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 819299604 1250 819298354 819298369
    0xf1b031e0f010f0b07050a1506060807080c0313021c05011b03020f03060d02041506020f01151d0c07050f010506040c031b0815030303130605220201200115150905 71
    0x140c514601d034005000e10a101b01040030303202194105114003100f642c074011400080103248034800200344981c0c001100c5134020f28000d0300c03400e442c2d22044d14503a944190301e800c42500703d2049030710000204445e00540d13031002015080350311450002400d80e88403640e0b002142c0000b9801d10030140100500d0322040c1058042d20b81203001910440a4800c60b407002801410b1610444801c4a40c0050001034080d40083c8401031242010020090307900e06c1c0c0800d42c0e9090890242c6c44242049040701c107600809100e9495101104845041c101300b00b03036688a003450140c20104003542c0d190414032025123490b2140203040340c04d0b401d04020180302d54542c416880402d2445009110060000079400080701c0c1c2d004200e100014142c81d500e10340000d4410003031002c90300c01d980491401c0f0008010f440c1c00e59681d140b00b080c0c8030075060a5102580111021407140810b20141c25a0020941501c0c0090081444c03d0400090010b0710070b0800310840300d004141c000d01010091180403c010b00d031500b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 819300854 1250 819299604 819299609
    0x1141c09080a080f2a04180519020c0c060307022b0212070b070f020c06041e050d020a0308071b240806010906110f0a1a0c0f030f1b031e0f010f 63
    0x6100003010011711011841401258072265092151620101d8000f109501c070501c80ca0403500d5942c5601101100c500c01c90154030241c10081d0300c00804228685840f038003456100e00240304440c1c103010720410600d8214140040b046d0b04440c4860548034403501804640c803100140302c01c0504010150701d941c1c50390440503107803006220301c00550003903c074420320031301d205010058a01550740f82d4401d40c0c55038032603600c80e84c030301006101207002c2140e140100d254002540c00511440195081d6103c0e0440742d80300391400c50740400440e9500400e0840d0800000003000c02c1c104d49404440008000e940b9910b4070195034040020800811207140e800011010a66503117240039003042000313845452800c00c02c096640c1041c481c0000c0c030300c20401501081c0b03c46140b207500035409a10f50494040311400b42e02c0c034169101c1e106000188040003507400ea280e0000c900140c00220190601c184400e5a000765140c0c00050424842400c400c800680c2c0141c00004030002c2c4011585010001d104401960 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 819302104 1250 819300854 819300901
    0x501140120100c0207170a1106220e0703050901140c0901020f0318010f1b0609110a090506040e0a0b010501031517010204090b0301090201141c09080a080f 68
    0x200d07009100d80700204078824020900b9101002440905400a5600e160b035204800d003144200c0c10407074480d0740110701c10031100ea101c280011070006034820023140b50001014200d41c00e90000c011071fa58141d01201600030b1070704818a81050825100c01001d5420090040806a05011180300e05007a440d40300c40c0e2240e4280201c1e9166201600103e042c11641c2c045440705110204400e0640000c2007000b60702c82c00241c03a039544400760400c050310035910000740440e80003005075024000c2082600400555889899800d03003074051900041c02441c00c58000d405081d170347d2004c128281c14a842003803291300d2100c0040c01c80e28184e59408840d44014041c003410180c40b0310140d1144000308483d41c0145c203070b46a400308400141d62049000f0b42047c803d0302101e604102020303400b420184200b040c0e003501132f913942141100c2210308a03555840605071a0241247d20181513803441d0034894a55001d00c00c003806551000d100e000140403090146c0f171341820340c00c40400e00c90120b00c0e451000c160481030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 819303354 1250 819302104 819302147
    0x5041101080a021308060f0f0906070c03030f15142d01020c1e04050a05010b1801050d090c09060803190c020a1203230f0405130b0d0c0905011401 64
    0x40041002c06400340c400003800c0a0101d040105500ca000700b8054891505040d84500c60f9031007a40002d07521000380c510f50100d07041140800c0d0700c80d1081c00c182c8801406400c01180313006200101000310344a042031034242c61a20381c018410100b0b40c000d141d4210340d0484080c07148803500d6901c15540d4100001600c08202d500101001c141d000380410080280d000700100302803941c2c0181400c4a8a242c1c10f00c0f482149041c000821500d550300c03825044c0c4001c03002180c200b0704080700c0c020a410031400d415050000a10141022074054060049501d114092032501585819062400d840d4950000d060039003040c0903400c14026180380c2c1c1d0101e4450341ca444040580b941c000700b50802c03071580003205010b00801c590720505030012141152200440800250400ca05a10500e64042c103d90440c4c407400c200010003030341c6800003545d008510711070000074207112070070000364001400c044101d580110b002c0d02004030146600c40e090040000524400d0020220000203154144955202100414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 819304604 1250 819303354 819303361
    0x201091a06310c0e0a0612181a0f040c0b07061407090305190b070c0f020607080a1b03020c120c09070e0a1509050904241b020319140c150a0c030504110108 68
    0x1074220235232260304007641803407a50242c203140808451211700d08000c03543c1d01e0302144084113042e404503c5290001c000e140c2d124140307042c0b01665031190100340c032465101c41c000d1b4010000100d0282c020b03070441c4c481140302c0e491444d025062004498458403c100c0194070040842d40c170484955201c0c4a52030103402655580c50404018809200065000316021808404201e040401813428000c0d07611848041140300140b0303024080801c00080040e040b074a100401411316801e080410507800081d50013100040001c41c0c50400d044176080c00040a1070800c105c0da080090f40348010301240e02407107060191410000c2e00d16031342d61258501400002001406001c43c1c1070b0021007116400d102070030001c019030249805441007002c1848840c04000c0400f071128000001c8501c04d0409a041000c814104501503803040001165104519410000811407400910190890286101d81100e050074144401c0c000c4610682c40301050620340000e103c041102c0102e8140d01d2002440c10070385554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 819305854 1250 819304604 819304637
    0x7150203070606030809010e03030702010c42060f231302030a05251d0f060f04080622060504230a050d0201091a06310c0e0a06 56
    0x82000c01c058152443c04001104010704100145030407442685c03500b45041c00d4804150f1079200c1e1010090100c0c817000140b400055118035007492500c1c0c1000c1640e0a0070510300240705281d0410941c001d610038a004c0c41d140017040c1c1c07103240054280349060001050500201104a20600448640705201c0703400c140c0095407203031818000c045100c04259224140428048054542513504444020075000f6424507000c2e00c03140b070645562180d41c0c84140f084c0110284607030150400d03003150408212480700750543c441c0c1c030003840300e5504102c1081e5201d00d880c100303a0805a002e0100032065400c0344078110035080311405501410b030801000519904c0e980391404010b813240840d400140c44900301408004808509500c1c418014019542d520400c103408a0880d13981d60303401000c51a60200018080a8a880040e8450340c0a09680b02d90400781d1441c052615101e9609801034402071140720a0052a0040301c03030140c01814500100c0b01401d000480c3c0300d2040c0901420070040984014524 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 819307104 1250 819305854 819305857
    0x3070f1103040b0c0c040e010209130b0a05060c0d180f051917070905060312040e070210110307180e0c16080d090209100e07050d090515060a080f07150203 68
    0x80001d641e045940d007414213000e9449214080c0314911651030550020f482410600880390840c000410042e00c840c0e031081488000c0050800c8541c02c201030740d10129160b1030b40c1004000703d44020005064000300460010001d0301c8003100d0b1f01204200440800c002c07900840040c040d00e008503000b141e01c0b01c801b1081800558158800203d03495190b1030316001c400c0125180040e9420b41c2414810b070354401e014169540d5042c0c140443d40042003000300b1689140da1803e513000303106441500c039129072903514081950140420f5207212134001041c407200380d400c4460204a1002d0001c0c07011801e00d04003c0d01c46130a4018410203100400066140d1100c200b000500c0721594010240c984484680180700001c004907041240140600804503020a2104c1c07070b01001c449040b01e01a1160381c0d002801c4601c3d410142c0000b200b10389841180d00004c00078081c103c8401000502900c2d50300d132000401400f8001d03507003c074000e40c00031041240b4505021a11405803103249000248901440c803080307145 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 819308354 1250 819307104 819307109
    0xb0a0806040f050c1918051504030503071a0a1404140a051f180f0201050703050f0705100c1103031f0e0703050601030506040e0c09190f0b1503070f110304 68
    0x280f9001c10481c0d02c00030500502080001805a0900300c0112013090b035503802070300340000d40c03001d0340b002c00c000500d001d1045190f071291008045081507680e80c0d0381340c9036400640b001ca5003c2c6100001581c0392401030640c5070f120103580700c24000c98982400d03140c00a640604060074614440c1c1c20f5040d111020400384015603480070440782500000307004001c5a4440c061201811400c0401c6101d5041c0ca0b040f564540e1900101030500c4210150b005440c039070300141e4110180719060025140490180e0007400c4414040d00207007030303400c2c004980340d021201e40e50289024003041c030a40c500b4121000040da54040d40000003804000140040140780c1c2a050b07120411506810040010241e81038001600408003a2000d001e5a00c41004000a0390441c070880703038030b0340d0002d41c1c2441c0a107000068a5042880301400761008600c00420806480148028600c0c050b12420010980d04180f80c10452050600d039409040d4105000010b1041c074000310b01d03100b005000b503200d5141e04000d0045500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 819309604 1250 819308354 819308381
    0x1061d0f0307091508282d02030c0603070c0609060e0a081905030415020a030905010e031c0203160f030f02040e01050108090115170a0507030302010209190b0a080604 73
    0x304a40c0d504001c400350200d90402589105130900005240c0c0000800c810039030700c0d02d03480001e080a114251084150b50813419a03c42d0b00d204003500d00d012102d40005045540707904045210103082c010305141041d440c0c2d0560080b0300070003c0215803070740000d403008104e5100c0c6011034101b000341080c83c080d101c00059117035a4000d5803007420402072000020080c480300000c6410a00020003010b449c0390104942c0a00f15500a20407599003c44583c0140607403c1c440c1400610311100745c9580d402c4030320910711019141c1c0300049400c64071400007491911400148401c3d403071850702c085200d000e0b20607010341c03030240041031100c02a018001d4201890000e40901f0454440c1e0340c64103540300f0f08400303229035804600000c020880101043c002d005482007000175080051340340c00c0107081a00c0c80510384c403805010714050750002a00c180034030401940280d0015890740b540030108103810401d442c804085400c01c00701000440d03240025120b4022513402c1a5245035200d0001c01c000c3c115040c400d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 819310854 1250 819309604 819309613
    0x90f051c050d0216320c060a0522150e0603011809081b07060908161e0806090325050d0c021201140403020d0c02030705060309070b0409020406031401061d0f03 70
    0x31103840e900300c4209203a0940d0420490501c900f8a62070302d031b01c58000c0040c2c20003070070071000403858001c400400711108807101e405240b9603800c92006055225411480d49070800029145106074050443d540c980750845a862640d454002295525012850754901da1707511401405d0074000d041064411100318000e14403400a120303a0401d482e0780881c05050040b07031600c04085106940010110081b49a06060b900190b08141e80c0f003806d2200429202d01d4000c200801017240041406404d0055080100458542995006005801d400a00894045803900d0080400f140c00001c84011101c901e0070070315207000c03075030002ca080c046008140810b0380d0309020750240f00e4030038240080c0c0b00b00e0080c0e0a442d031540d90648100d9030302d03c4643c00030b58180e10408040c04546420b600450b0010795501c22202c100795541c00c004016041584900c4003943e010038100105a010301800308208450100885c035503040c04000382502c0c0c7e015000e2600d0401003d03d406264075461540d0380100b000800304d9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 819312104 1250 819310854 819310883
    0x30204110c0f0c030d0c0f0b060f130212090d0503160203040f03030509030606091003060e01240f0e010e070c02040b06030901020406120204080c01050c0c04090f051c050d0216 77
    0xb82d8541c0303052103c5000b803103406001c0f0102071051010706c04869006103250241c0040e070305c80407003080300902074035841024410090050f41d01d0180e010070aa40201000d130301c030310003444002c11251004111095540209462480035548601102c0d80000d1250310310101306040c00040f480c50003243c100500300149007030044185138001000e000158811000c40c1c00d580c0d100003d003c581e42068588444945011a0500004400350041408078090400016900d02006907150702111300401d18080754003454002e0020100d69446400503000200c00440c0d603525156580e581058014801002c01003050390702c1c3c04554454200b107a4010000305002d403681003a41c8464000d5200e841600045043c410002e07011846500036181200c2c0202d000d403800b18282001035455900c54040c06480b801290b1404a03036640354480c0050709030043c8141040d001043c64070902d410002042c409141c541410409005c5601c0021140c0d05942020b000d030300e901038082d4640d40b0031242c0c08001e1504068400c6d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 819313354 1250 819312104 819312133
    0x60a052b120314100501050a030b180f10120302031801110610080d1b02010f121a040e03130b161a060307241b080a0309050601091104030204110c 64
    0x2d1000f100300411810036512541c1c429400401c062146502050b8140000414030b0b0003940300502040c0041c007003005c0c400f4005580c0f20288001c0326000c8403c02c406083c41800b502e50040da170b01809401d00800d411610300c1d10040d40e203008401e41d0701010f0400d106510031991041d800c031102c655083c03080b103d0710301b003e40b09031820605a0242001511401110800151052621652004842d01c1c40104000c1f59001117900c0c0c84031020702000c1c0004104c40e031601070364900c151541e0070f80000b40e0140340c0d03181c00c4c1000281c2c2d00003800041107620900502d0030f440d80b041d007108210ba100480d0030390703101c0b080304c640030022804403030142030b82c0c1d0825512005560071801d2a0302c105812402d40350300740d840e08999101c64030394050748030000400c4002c011516000c0d0101e030f010312401282c0030720200b92035960354410768011416140007079143c045107020001d04103c5036024010048081c4089902d404080c0c0301c0b4080d51001910031521000341520100d80c1200316588a0204400c4c2e4403100e000242c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 819314604 1250 819313354 819313361
    0x1030b0c0723060a0c0f05040306050a0603080d050108010b0a0506030a0507021018120314180a082a0d05070609080d061e080601050a053a020306060a052b1203 70
    0x10161151405d10340000030f0544a00b80342080414503465a905060541d29214010100245440c40d0241e4801c404000718180c40094188071aa032200070589605001440b82034880001c0e0580c082c0d8070394803040c44941d03540d0054940c00900414001195596410102d1400704402c110340f04462400301001100f0030042c058212141c000c10f11000000502d0404404441c00125806d07069407050f40070600d4050341e030001b1301c00048000c0866103410030a40380c490741640712900035907119042000710301155001c0701e0b01038420070076040070b026a41c8105d01c010342107108000000380b8865548101c4c00070002980d060303030661a15404208042ea0329031180d1581d070341c52284248035603070072241c001440140028140f81038800181002d201986440148000014440420131403452a003040d002800507068400341ea140c0b1003040111805124014582005c5000c0d14403800303070008a0b010321454459041100540c162140044200e0304103280a00a02034030440040641d10020060241154181c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 819315854 1250 819314604 819314611
    0x10b0a0b0a090e09030301030212031905182409060706020a080414240a142503090c06050306360a0c0c12030b040f0c030c0801030b0c072306 62
    0x701d44410240d1260400303116240b049540034003642c17040006000501709401d64146601c0070700116400c1c407080d40400c455800c030401d080c20008101044000e0f89401110140c0d04000303060320030300420f65040c07062024003044201d01480c0b280300012000101e448880c202c0702e42580120013107442b8407000070018011035090343c090f10030a14251202c0d04c000f1020816103815080c0700662400490078010300c070300315030004115980d00c2d5035981c0c0504c030040328404803501c00ca620b0840e00f075010102d0620085035030200da05040406103010424000240c0e209000390503150781d4206240c4030348d030300c000052044400d140c0025580c00d00d1001045c055000c400303203000750000d107490f5a83c2599945c6407282121212102e4500241e00001c1d2080483d05403000b81100609526011455410350000301d815588003003041810b1540c2c0d2803440180d41d6262155107510f910b280390030b031302a52540d22820400324000d45000c5054400141000800c4050005500b078211000c480c27604079400e0308104c1d0303115107044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 819317104 1250 819315854 819315857
    0x20a0320010212040201031d062d0406090b0108011e02031012050106050a23040b030f010c1238030c15031006050306031e1207150b0906010e010f02010b0a0b0a 70
    0x109418003000c0000c0d00e03003500c580340c0100802c0141d2b5a8a6000389111540000712a0742c401012008448100c0c4e00f110740c0305134040d00020079016010700d81200640d0059000707602591520414440e005500405042102c0c02c03000d0246e240d40700c0c18507000001c0c06c580e200008150a50f600507040100642100d030841c0c0d011540e07501c800b40c0c2c50b15074003002413103030241d164100484028991a032802e03611003611890f0140480e80c0c0e02218080c01400c46220b0914a0045012648441540740c118040c103080800c0c1086040341c10242c1d0706011030000301e890a0040d445c2400a10000e540c1c404100014101c103000309220024104030700c60404aa106551008853341612004584079024070200d034080d80c00030b0020300c4060050b8100700060000e00149500d14019507013404c02e001b050601401d80103018002c3e00180c181000500f0342100c40007250300b4050007a0032304120341e41e80c0100100030145020300b0000c0c80c6c0e02103010228010095944520f03401a8104008190084001c0151420407003d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 819318354 1250 819317104 819317111
    0x1908161d030d11011104050f0108100306020a170a06030f15020c15071106090c0d1106040e0708010f1a07030315090605010e0301050c18011412150f01020a032001021204020103 77
    0x40d1085d560052003217000ea20b0300300c00c003c1c80a10700f9511039030f0111342c00034402240000b0640c59a90b980241c0c0c1c00402c01c28001554000c01d20507540c0d5460009821601c0701c03a0800500b891a07649451000c2c054178090982000c1a0001c4c90f0ba5259804880136030804a00b038440c119811112000e00600660700900090400d550221300301c0d400143d40b500946d540401000301400c0d8004101ca810098102103501c0040d00752170080030b4850001500103001800c0c03094295240c5148001c228a13816070040801c103a0340d030000c02218a50103100c626010070410600d030703a20050308080e0b001e00702c0803107617a9003041d201d680013481c820700394011380c1030740c0c0300340e17203000e940c51030202050300341d440680744600e069400f0006104c6482e1401c4003c0c6045506050400200d0000c1709800003541091030301e000032080280800041500f0640c120350003940440e501c011701c0c2d240e000002d598059500d4014140082104440384505400c4010354440c05900e0080d9035840c4140e443c030200380c609039000c9003c2802c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 819319604 1250 819318354 819318371
    0xc0f0803070c182403030e090c070609030504050918011508030319061d04050d0c1104050601030e030432060a1d0909031908161d030d1101 61
    0x9010044808260300715060282c0c50781030070001c004002d42e184030552070540d1414a10b200302805205440c1e190301c0c01d520302500600c1c50501030602615190740760701c41d0042c0d00421281907401d806881d141c64101c82d0008030381e400d80c40d003561184260380005622100c401c00f000130498070354007000b0781d1861180081c42031141550a1405074100c070300800c515500144005682040b40c2100c040100c401080045400703591000e405480b00e02c09240d001c880c0e0403a008220030b100040111610b2081303181342c00b1190b444603458a000074001002154806d03926100429100c0c2e120782c100002606070f05e01030325680c2d41c0e2500342e0103000c441501c120020b41d00d8019107140044891400d182c50242c0941044e1600d42c1102c000c5a41c141c559040c0300d0310802e0790419804640341c402c41540b003618840300941e618801c0c2012096a0500040108104030300e0301d08000c1c1c0060320301c0000d80d8010480c2400c0d194200705c82c02d10903004144c0c84160f40c01d840351203c800003142d8815103008400d03540340c00070803a060 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 819320854 1250 819319604 819319619
    0x5010c02030a0e090415140106030c0e0a140a030c1805060321030a02040b03041a060306240d051002040e0906010302100e01180303020d030b0f0d02010c0813030c0f 72
    0x2228114804603c42d054281d102d804d0440002d9481440f5030610402c450050404004403000c03024406100c034540e800510a00d501823140580b00c2c155800c020301038002c900f00080704112a405115001a035684120030161113004c0f01c9809154030100005a20391550484240c4000600c0014002e80c10000887d02604020a01d0030003041c41ca44030a50100c200e02140200740c3c0003529240b0031b15420800046d040d01002c0240d03015a2103060104034402000c668040900009050a0300c29005042401044018140305010181e05500a244012648400070791a850b248001511318000c0d400541c84e102d51541c0240290380a6000e15042516403515031661200e003408000e401c007420381c284901b441d01802c60b2252828051418040340c3c1c4004000003d03401d059030084002d0b03484641c08011080d00b40c003c01d00c0342d140544088150200001c00107482000c047d90103414454208a40f80503c600078085807420420080b680850550f64648035503038842e60f129071008511220000319a11 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 819322104 1250 819320854 819320857
    0x9050603030901080c130608070306060f0207140118030b0f0c03070e09221407120503040e1e04080c12070b0a0b0109050409150f020a051914040801050405010c0203 72
    0xa0002400940c100b606400c01514801c001820300f4121702028820521050680c0704044050011070395180c03800c0c207100c0009402d5074815040b09081c022800e210300c0c02140d0008100b811a2024201202003200341801612440c82d500120046032102d108040140100a40c030a40146040b43e200c44103a990903090031070340d02090b03a9440001795100302140c1d5900d456040242c0004c401c0c6061644040780d2100000c2c80d02654504480b0100710b5824111030140901580c401001042110a1000b156070f403100c0d03e0748514041d80961040c848049041d02e00c081d0700f2003c803c10415040c071828103150800c84681c0d0411000d80c02a407088031001640d07040d41c00180d60340590300c000f21450365161410380c2c001170003c0381080c0c3d04000b058800019203507114040c01c5e10490050210314078a4003000003000545a204020307025240c010450714441e03640c4103084079401491048820900d40008000301c90212020710402c150b078401240101d090f41c1e040d44403030300482c4150020000400c440905988a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 819323354 1250 819322104 819322111
    0x415230111010f1a090403320c1b04180f0c050a06052235370503030c03090a122a080306150c01020a03050601020706021c0c031e180905 60
    0x510401c60f092301180c6c40b40c0034241c10001c5088410314601341703c01c60140940085c00c0031400d61b400300c0c4400c0004103601d0070505078150261014002100e4491810b00b00701c8200e4002811001002c0603002440012000035001d4900104203411503961220001c055401c400d2108060f185004036036204c0c6003400200808a5541826540c0c2ea00b604441c9400000d101c003940700c40e0300340d03d46009080e00b6420310410310355150464940303e01c8500780038110302c000d0142200011a1000a10007004a40008143d82c0c0c0b042c025501c055690b5107241c1d1860400418001c0144a070031007a48009800c0c8e0000403100f5a54045a044c0f5000c000c407a40c0c00d007070b20040480c058440324013080400d000b401c00203000500c01e02484c01c0d207842d200221a2140c00c84c1e1000101c0000681e46005101442d039051103404000d080510081184151499500000034416008501840b94040503102014051034800d80c0d00a007426114a00c403502640103030050b254070306e4680c2d0701c49000b6000b1a501c0d0461050502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 819324604 1250 819323354 819323357
    0x412021c030c050702210d09050d0f03020f06070201051b090f0402030a06120501020a090b0f03070e150a08060f0102030a1718070b090415230111010f1a090403 70
    0xd114106440607802440c140e841c0c84204501042007402607166040480080d107800400c43c2c0c20f00103800126424501e50300c4100080200104080055580d4558150042034108000d03800d4019249001e070303e80b1480000c10b00060145004200d0071580643c811440381c4070004116a0602850300390340090f115002c901343d80300c480302a000315241041c4c0c2c0036650228000100242c5d054585404032901640b40104494680d00020141c0e412079008544000a0018007040380c184a82c980c44407110340401031014081010812201c90990b8418007001045160a96101d03923913503120308000c050503c01c8078014001c4416624081303031075100100b110700380e51030355960b4000d011806040c0c03841910040e045103140d110200f14010144414132407000101460076040d41d1310f1480700213110590741122444d401c4102910710030454444cc0b103c000200065103806078208400020040c0c600c485840300c403008a6280c40240140d00e03d403648204c58075110301d03600300307980c80c84001081030034030089074000c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 819325854 1250 819324604 819324643
    0x50a020615061c0b0a0b041505032503090204091101140310380a090e1504022107090810020712050d180c0513060b2704060e041202 58
    0x542c114140110f82c0d0030780c03400311008945401888009040c40340c95401c00707482000001010048088280d441c4a5464000c0c00c21a0452500c0702d030480007641011010014208007880ba266440e100b035014088030b0743e0081040000080c44c0c1400b1210070291032096012500340034001464400d913200b0303284100c03101c4010100c91400e064007028054241c0c001e58490030f0950039a0300305150100703031410840c2c0c03d080c030781a11401003501c0103240001e00d0784002100000c06083c800d04a990300504092050292405039a540409030000c03001d240301506608038844680501c007565a00c4005081155040001c442c103000040c03444800304d00c15800c00803c408940c41e4070100c07140c040d00180c0745081c2c00b1280002c09008800341a100b404400e403040b41c410415180500840c6440c0c4a1a41d10825040f4100111030600034244080d1017929401e02d0481d8007000703000100d41c0d10391030801009501030070034000d50703a9840b410012803900380c4088a117414014141904030b4400075001030800d0b044103649 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 819327104 1250 819325854 819325867
    0x1401052406090a08073c050103110d0905010c140f070605090a0c06050a030509030c0c04050c0c0a0501050402030d1701030b040c030b091f020a0e0405060619050a02061506 75
    0x4070840c0c1c81802415080100342c900002c0701d24050001600810344400d0081c00019003000f240e070b80c8075181040d2840440e5895003490b4405040c2108170959a003801c1c0000c04010000c8240304600034503503c0c40c03029003041020002c121064004c090460859280e101480000035082d01e124064501011002038080c88541c01081c0250045a00324100d0819684001c5081d01c601c185140c03503420000200e140050492105549841744581c0600000051800c10b8030b02d4007507a84a40b180e2407040e1107039445401003041c00094104a40c84140d821080320b000280c14a040ca010b02001c6405911a0140c0c000001072140500458101c014a020700c511041e030070740c0d55003014a40081c10a0790f4800e200580400000c4032140e4090007000440001d000301000350680f2820b40a03a850401010f90040c040c98800d035800c03000e10700310341404680220395980c40d000444c0031800358025442c500b2520305041808660030000a0039004056425900b0581d41d0001c12880c40c101148407075009030080050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 819328354 1250 819327104 819327109
    0x50906090a20070b0f0903070320030d090605010e01050307030b0a140a090c06051c0f0b150a2d08060307051020150c070302070506040314010524 64
    0x355001041800001d88030100a21410001c10034a05144014200080503c01d120480c0300b1664841035004c2611640d244c0307011116164051004000c040c03150604649000700d08511031081407401c0d0304120382e22040d800c0e1301040a0540040251401803809001280c2c02c088070100358140c2e50050300801c05d040c51580c0c0c07001030b8400180811006c81d541c1504494401c03101011070700645c109000405e9001d0181440014401640c6c00070092010401480c0000c2450701e407037120700c818041001400c41581c1348210301030200031a0a513400141d8600d0302100380001400380c0307108002591103c0c40885120207401000321000050071003a034942e08222002442109000d5110074042d00751140d5076507510100e00051080d01131100070030b102c00003001280d8440c10100f50210007480c000c00b00e01c1c3c1c008d55010700d52140a031030078a016034001107260070715000b04132101c0140f001030001583c1c7c40d03a0341003c038513107401c0340c540f055103500340b4000c503290740c000c042d00820880c04503095840e01d2002c0c104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 819329604 1250 819328354 819328369
    0x120109180201110712121e1d06190306081c0e0f0111100b01031a1825020109140a0302060f1801020d050448091a0301060f050906 57
    0x203000310310681402180741c404403891017000d988981080030038840076007406000c5c2c1e072503e040d921000440607409200b90fa40300007005204400b046a10480404010109020707209482e80449042040c5201c3d000c2c0c9903042d442081180e14100a60310070b0b504031400c0d80074444a001c4000c0c00184040c0102e0150310f4000840d0002036014144004042d0410b046035081215a810b56260030b039035802c06941d296090301803906080e80f140b80440c3d03010580c0c00041c01c0e031203504481d488075041c0c140004031002d0040710500d40d0360f0078001c25000c901060400080c0a8048003a084400e8800f1880014503c80c002998192207a0705030094180c60f81c0c3c0101030800341c0d100600c2c0c0a800f01101c10300c0f48042c1800c0c0300a001d4241c1d0200041060b147c50f00381140c049281114001c00c4601940b40d8001d40c0f8036100310441000400d181640c14070041c001c0300140b94485800502c50a898005001702c4a2064100d110700807070250002d103c150b5480c19645144001c1d4442e41c1c4d0081c070b00100041c0c4625100c00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 819330854 1250 819329604 819329627
    0x1215011b0809041e051b0f16291b040815060613080105041403120f25050702030d050f09010c0c0306050408070b060a1404200f120109180201 62
    0x103000140d5036000500509203184c800201e00038080c0e4610a121039481e01c10415a581d00c020012a8607040401d03a000c029403141c0b601c800c00c041401c088010400c4058001c0b400e11070302d81001da401c0e00c50400c090700408401611700710500c0c4030b8100315002191401e4150341c1100c0d1004042c00016130030020000c1004070040005500c40780400c60252465a9030904001800141d000001e0ba40b500b880c0042c0803401d140c1214850354002d0054600320390450204641c4a03000041d01410381d00ca684ca50040d03660200100c1000c60254144121281c5c0d000c00503000e560b008804681207030480e03c400303607464410002d9021580c1c2080024040d80d500403c80035000510074805480255601c0d01c40000315101641c0803140d44500041006c10701440540064028508036458800140751086003000d20400d0440740d030250391a1855034131106c085023000940c9450642d00b09550741103602d818045503112602c1d2805942080c40085822400e1b40705511550040c0600100708000d035400541d4400682c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 819332104 1250 819330854 819330859
    0x20a0c121416050307120803040210030e06040818040605030c0d0309150302040303171009050c0705011b02011a060f07210309020a380702061215011b0809 68
    0x40303400d0014070410441822251018444041d0b014208010141010319a034402c00003584003000c200c01140d0000d044030b03042681120005031040120317406a000d4000c00408840602880007048203208000b001000c510100c10465120800c00c202040f003265146d0003101d0309640420a104043e0522941b901003280c0242040412142e40c1c4200d0394503c03061040e120000394012404108042d0091340d41900502d0347caa040d803051905c10a0034000301c800b445846106034a544c040b170214610b040446445540241c0240316040640e44100080c41124600c600198a4078104404446c0c0c43d0141040c030810092000389000114442000c0e103820846042e6103550b1034840c20484d00050554110700c46295407400720780d5a800e03004220311070140e640120709039013500408040034041c48900e001a202d5030811810b4800c1500c140f0001805242002500724000007420750406040c61840c40c411040c4a40524110500c20011500402207030a41c045150202c1450000202d00501900c0e404002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 819333354 1250 819332104 819332123
    0x50618161d04050103050c03390103110a08060906040e0a200d050a050105150303030a15120c090c0906020d0c0501090c09050a05090303101208120c0301060906020a0c12 74
    0x70200000c08540c42a03000f25070303d078804900700c201d90074148a488500c0c0e400e02ea101d908c1110316180240d85e11041540c16829404000b40b1028580c06a800f40d0742c01c41d90083c503242c45042a003009841d220042d100544111580400a1420300c0c05020b050040840c14000c0c0c02c000d01d10707030394415000310f042c015444a641088243c140d00d441e1071080852445c040c0c80288024205400c0041c00c50b00003500c0100300130b20000703110449440c000101d81c1c100d2103403080052800128005504000810380000400c2c07000b07481c1207006d1059407403005042d145441e00400080c2c203524000d40d10b900c1207203d400b0250b005200030908980c018003580c50914020000482e85205594414008480580091070010359072424400c038140320341329039940840d000c4011451400c0001d00d10a0f11402c0b44100d8408940150000c4104011942a198a4020001c0da0f4403035051a00c40a88290024040c60001410201e03000582d41e200040758100280c00468130310484d4182240c0724925192300200b501c0501c030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 819334604 1250 819333354 819333407
    0x1b0e0d0506071d06090901140301090b01270605150d060e0a0504110108010302010819180309030b0a06030305030c07022814062a1f05061816 62
    0x1414410a8400d011a9aa080c94040304040e140d091400b83c2140ba4000c0100707208000c00754135030a00d007070706440e80040000607064500e40028094a41090000c0440c40644000503818480c285031925034008010303281410352005110b00b04903965441030951015a0032203a0369103c0400005011a00b030b0b4500209a40341c8030300421307070f0f80f440c15a08075010300e50f10b00802c070612030040d481ea88400c40919210f40c6a502d5a0002020250302505003001d0010b8610003c03d0064950710000300040b6558418001504a08010349601414802520703e007000f03000080841e07a0610039807099079450f4841038156120f00250318000e801040d8202d0f0000300c01c01425140641003c0e8803406c000703100c04140940ea04140c3d220050b503941d00080742c0221410310040c50020030186400304444880d0706a00c2d10b01200c0403480d840e002103200c44981d02170001c031102505940e0b075040f2921405042d0751403182e807004c2021280101c43c04442007005100380414106205104040701c00503200c0104200c0e03500403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 819335854 1250 819334604 819334613
    0x405151c050106060c020f040b0120011404080903060c03160c02040f15090c03060b092701080304150c030516062d0e06041a060607060603140c03011b0e0d 68
    0x4401ea0840e40129a0401e240b4046240c4800403101f2030900b9201130148409860000c2d01005c0c912000b46821600c5181551714031009500000382115900352000a504080c20705501030f50008000768020300a01000aa0075002c13101140c1c0036804424404c000c036400c004e001c850701e0a5000c0101d80c419281e045864000172140183ca5450035030180a458862900b511642110032a6000c071017854100a8108065094075003902d80b4040b055a01010309159404000c1c285102c6000c144080c0c2401c00001c45e0710a00007003d08240d48540d4049080c121b80c0c0001659150845c060003400181c0802140d00c09141d91000600c1241c401c660104095180d81c24000c3c82c07294510b180400e2030039615444130311000b02d01810319107001c0ca10241800c0d04043c2c03103840d251808115100c00040103000030580d2600c859040b5440ca580280c8200401c548178030f086d040301c0480302840138607072150040c5854107107018450084241070382c00701d009a08199402c290385c044681560380f503100500c07404200c00708 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 819337104 1250 819335854 819335861
    0x13050115020f01180b15090405060f0109090f03050a02070b0c0d08160e100203040302130209040c09240201060b0c030301050108010b03040803070c2f0f0405151c0501 73
    0xc0201104080a51580c000000c0c9404007005590106070704141e080a001510146003030411034003e00c4007211562001c440a6000038205400303504502030900b00701c01e0007404910b444c040c40031202031041907681c4012650948062000207003000031602c01100000b40a4002070210281c6070040d140e4045c2d58410501d0560442100b03803405402c141c0c8810790040c0d02194496000841e0014001c1132455408001c5c40d42030070512140c0a542654132008143d4001c0040d1390003503130300408404000d804190404043d40100b644a0f001b40c1c02c01ca006280320b80a11070410988046c8405091004071098040042032100010030055560b100c001240940032000205108044180115a01d5162000040c40c400050b4007000d0044014028400050610002c41e03070002c0c69403400340380c000002c0c1001c0754000820503021019803034510481045004262038048680c0d030881717a281008421100740002d03948203c409810b560050710360b061441c03410000091643c4280c0c84684480301460f541c0a086 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 819338354 1250 819337104 819337109
    0xc0204050c09120105160c14030a0e040f0513060203060a080a1b0807030305040306020f0d09060e010506030d0c060c050910050c0c040c080a0c11120315040c0804030e130501 76
    0x109500051200d81820b1035103843c0750400409000300401d140101c0c5001d8400c07080b061102c1080039911184050042c88146c142c04030480805981d5603c0011070f01070302081100450a001d0b6040c07042c07841070000d5074400d05204190402c5880c4803222a5903d14000b544000e1080b80d00185540c2e000c22001c500b0400c000e050f62042107880c0d12442210540c0049031200c0c1c1c400d03c2a41e105440c10b200103a403140680b001c80368044005600c038150700c000220f075070142e660031007440c515001a240134840351b034020710000c540c000000c02090b1075030020300d40c0700c0c0046032041c0042200d051000000507901d40c0f0482d400609032610074206000040021202c0e01c442c4001c0e000100e02241d00c100b5110705004a92a450f02202d007080714040110f0007030641c2100400c40c60036565155240400b0300e005210707401c4030b400401e0641c0c034001e030300d40ca4240c0541c0054402c41030f4070540c0b104800082c24540b1070380c10f414429444114080e0b603143d404940b4844080c025542100c0014012114610356004240c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 819339604 1250 819338354 819338371
    0xf020a05160c0b21010f0315050a14090c01121109090c0f0c0304031403120c0c07030204060801020403060b06041410030b04050109061d0106051902150a091a1909030c020405 76
    0x40f519138075044079041d0381138218080d85040001c0410000c0c0c0d20f840f4280c025010741c6800710b42c623070391842040000c5c40c42580c03656080e0039240030002c1500740418042c02c00e1209880d00302c2d40c82694000318041340e00302a040051443c0800c4108050710704440c20799401400444180d190070301c80103124031160020750409019500103e418401c010b602420030844035221001107043c2205040d03841c9141d1400340144540002c00140300f0360300398090100c140950303005001880280d80d1891854000c0d8003901c800c2d03c0d40c80c070f40340340341e5868605001201d00302e41150180100c40c6456008001643c410a00710101313240d5150084211522140280ca000b03121004d00092120700c0d003000c95450800709000d00c18045c40031001448a29040019100d01800080c040e00c03400d1a00c502c160300e4230742c0c0403803004980d010100400034034514582048103d9441002c1003079007440680380b1101201426920304007005441c1a10034800001c0354000501c1c14080c0c5000c0400d9400c0d6008907040b1182941c5201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 819340854 1250 819339604 819339637
    0x108010521121b030a021218090c03070f02010e0c010315320f010c110111010f24030812270106080c0a05010c02100c080309010b040f020a05160c0b 65
    0x10302500540d0b62a0a118007283c01440ca040701082c0d0003500c07140c5412011000d50004a0700c001003071170000010307024500140c0300007114100303d250551941c204903400c0c400210200c0b10070b07400c2881801202d806e0003c08005202d01d0800c1001074010b44444005086200002d03200010304a405c0e002400c003445004001d08015200c07198035058540503e849035000f00444100c0301c016903030060340c05941d282c1080d0412403e450714001220318040060511141d5800c105940c0c030406040d134030002440103956000c046031102c0c07030080c07540f0414500c40a40f0401060109004204c400c0076419449480c0c079000140298811046422810300d1659050b4107a641d410705119030481005000009541101c0c1c1480003450800001c168500c1d4800017409021424061600382e070117514134040080d4000007003500d030302e82490b026000f00414403c00748101e08052803100000114802c641c21006190744061034076040c0701ea203508101015008480190040760300007941105079028001c51a8001c1092 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 819342104 1250 819340854 819340867
    0x409050f19110f1c05120a1e08060102071503150602010b0325060c11040603032106031a09070819142e020c06070503010503060f06010801052112 64
    0x1621903902c541490041406612441890b030b0382084c40c0484200108804a88030080d150071810f00b0b213584905c040c9a400407507a0392020341c20100e00310500c64143c4052300c042c5443d910403030b102c0e101680c025000d40c00585040c000e10114080300c041005050401040040480303104090b4400154040310052b59695800140c51500780320b42440400f8038444400e0600c40503c0c0310550200d584500d0043c8000811100100001698604541c0388000c208000703080d901d0801074a601508a48207440c00d2075908455a110760910621058a40202c50b0682034800d0259003c4e107488054054411480f480c07000151620007002448c0390518003441200c20500d0364603002c554040c10601042248d0400b0980e02e44000b01c02c4011652998400441c82c140300319011504020310810081c40418007502d003c0042858215005504035001502200e09596070025142000701003030f0784440c0040c010500410803032404005100c16602c1401c0c220026003500341c061450035000c0b455075804024089000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 819343354 1250 819342104 819342113
    0x1c02030609060d0c0b3001062712050109050607030203071d130504050304081b0f040507050c01020412020f04050702060f06031501240c0506061c05030a0804051c09050409050f19 78
    0x2d85c0030b94001b40450304030355410f1003400307001510315511103040041c0070085141640c0d2424070400080000324121403c2d100d050604038064044103005642c10300c00c0c540803c0c45030381b10348200c900c500d07003680c0d0b198681c070404444038408011600b200c96002d402e1011252040c0b1183c841c460003144508011503480e0310348a0303241c2c03c0200304030100c800000100c071405495100c1a8603002c42c000308990014142c1e1710b000e01603a00b400b0700440a51503620110300030521003005210240114002c80c0d42e140480703c0c000403c42959012110040181c20240204a42c000c84090807908900005d09450110a008200e154250005d070702c00d00507500f445104508015040012150b0314000386042640c100b910349501c0d65030107021300302c00e01a0010031b00303001e4a80f074400030140d03100e03034032000b5640e4134003a01800030320401c810f0340d003a6064000c6910900252400c1c000380190040d140e04d07111042481c0100701300007002402410313a0070307000c4d140044981200c2404541c101c007614443c4940b00740610b040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819344604 1250 819343354 819343417
    0xe060103060506061201140409140604020405010e040f03111c020c090601020f030f030a020d1802040e010209030a1e06050c0721050d090507080d051c02030609060d0c0b 74
    0x184500494040040807175170b0151500950548803406811a07000b1500008640204006d200251034905042c0362080d4080000c13035501c0c0290b008881c20b008590b01c9849060000000703441c0180f1655910140000103401840e52500343c032800400d84039100c6e19501008240300038141c0c480c0040c0c200000c01b510b1480c1000e08a40c02c50000c1c80148440003910340b402d0740d28440c104020604107004000176001c414150100c800080c2800c4060180c11040001e503440341c0180c582c1203110b1420109844d1711410b05200b074075a0703030400500402c100d04064856103200304081000c101028580c4801d000842c011b030088500969411051503580d00e6107040c19140301502a04054500100c0e030b0504070340c194030200799441103104e400001780302d810f180317411480c18016034442c05d014045c144503249034942040140120240c8140d40c002ca82c2c4c0c603800844120321080b00d83ca644100b0704030219400d03007046499140240c1c420001ca07941c0b583c0710500e28541d80c010000348010018200d000400401c4000c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 819345854 1250 819344604 819344611
    0xb0c1009030504120c081b1e130902010512011706090f0a080f130906300303150909060506100c030e0420041503050c0a090315020d0e0601030605 64
    0x15010000d29559540040c454821489403c00250710700c034464081c03103c0c40d201d5134001c02003441169a0042c8071150040705014200301035202c0c0115110f03003291303c031020030307031040c5084003c0200b03100e00d09a010000081603e000c060b41080005c3c00b40e00009884018000c0c043c101d0119038400001c840e09000f8500306004101c0421600b0001108490410019180101d15071020a558507031850640c4802280104103203181107174505403001a0401c1180c0c4044180c8c0c0003d05840d40074a003403455085070340e118014406c0d480c5001908000441c1c401da01c07801030b00008142c4c0b04141a0342e100020240c03203503900140e80d015130b510203121003450818001c17444140a0300b03042040504a44006d0a02142810300d1801240c031515848850014850a11052151009481c0d01c9a03120501300c040c600d40d5180c10781c0403a02c2c2602007102100001e040e81c146408941c0c4211220341151390b48c1c0e44141e2400b403118120344d000d2200b04030212150040d0326034041010f001702001c0d851410050181c40d8043c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 819347104 1250 819345854 819345883
    0x14100908070b0714030712020d020706060503100903021e0703050a1a060f090f0a0e0d09081b221517070603020a0507060b03070b0f040312032901180b0c 67
    0x441d1800200d00714131041d00e501104500f0140381100c5004c1072140a4401d80c0003c03542d942c80001c04104008440d401042960015401c5841840030440c201c41101c00050029025910110312601000e0310501c601240502081c03c0d40e140d030f46d481e0749051030148419012250fa0500003045120ba4018611450b8060002c403a00440b0000000209040450280203600c4801d240302c0041e0321070740180c0200e41e0f10350b0320360101c3d5101d011000006012500902500172a070189400f41043d015a02400b283d8000004100b1000a001003203031a4044400d1040e02c001503890301480700810100c09041002091070020a4010034114600c0d14181210354014505040c4140107004005500c40c05543d8100e0b80000009605503d01c00040d1800300194889014001d0000d1040c1c50645100050004c9034800c0b072915405041105003079068613200003078071205610260400c040c0c0342c1141d280b40d09484040c105003c2540c40300c00700601d1244039801001800c0e100050441c222881000160b0094858 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 819348354 1250 819347104 819347117
    0x42408060612040b36190201140d0e12041503060b0301060c080d0c0507030809010605012c0d081801020a020607020603090717060403080f1314100908070b07 69
    0x4070708070460b595001810181482c02c0b80300c00244400c2e4104611a00b0106403004020101e070a5840f114800a07010314103015805442007400d040a81c421100c00c41030340c140c49866041142c1c0200d00d0098103c00042040686c40f01a140000303030007405064211a040c011311503032503003043d60000d00300f01e1060391142010310340340d0101315150010713003039078151100c3e403411900085040c149010309009000c42030028624002e648000d1580001c0100f04003840b0b500d500d0740741d035074440c03059080394850b1013800c0c041403010314003c0249a5249420555125038170801c11850001004200c040010500440392140c000a580e800114148107040100300240700401017400780d40e0200d442030260740002802110088045403a04400740f000c1c0c0040c1112601c1b0850b4800d10300320b902c0e554035055030140d000c02d1310200400d00c9400e12000e214840c0b20300301d401c800f40030b020303542d1401c1080c404068140f1a002d040c0002c008002d6078054812641d0048556a882e1010385c01c05681c0050081d0510f014440c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 819349604 1250 819348354 819348367
    0x1e0c0601140d0c0605090a08030d1a0613030308071b03110f19080c03091302040e0a0203131203060b0c0106030b150d0609061e0e0106050303090105090409080424080606 74
    0x3e24040c50402c1d2505840c0043e290100c8101080106078980c1014007203000105110b40c2140c5980c0c0906808a5007401c0088081d12070801c0c44558801c60450b0044084200c1080c13000c00d0007810565000505442c00d8100c5403140b00745550150448070301240020b00310060910340c0c640030000108240c512801804840015041032811a003080034020b1100501042e42403c400301031090310704814010380500c104803c0d84034040c009600900401080c5100c0c4408a84c03154144d2081d01e102c0c8a00da1001c1d07001d00102d4407aa018404105416000c040d00e4003004204034494101500382c2c0c25100c0c00124070345003149020103002100502d5200445400650f59900b90b035031850400036942c1160700001d80c00f15074101000507020180084e0040f0b1041c404d150780d200300541c081d00b5400340d81d41c020889542ca5601b0181c403446001381d01400540c0501451041d49080d500c41c0c4103440c41b40c0a040c0c5020b54130b1a076560201c4d24145422006203407201c00c004403179040074003142d010004540c041d29210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 819350854 1250 819349604 819349613
    0x130b010914090613140703120c05160605040b070204090210050a09170c06071a011502010f0b0901050f010e030607081012050d030c03090f050d140309121e0c0601140d 73
    0x1008410b000d4006101c8030086100b0200034002c100147d07401c260304c0c0180b02d090fa0405002c000905008451500c90404009040d050105030034080c1c0e400c0d80e480524252504004007840e800481c07040e40d0155445d42940c0060744c03071030036410316030001d81c68141d290407540801400d484150352003192000a406582c01c0141004501c440d8881000c81d091034036101d5506005040c43d40b583d640d2900c4664020011980aa003105060300007006513009016050b040440b4505a0758500e02c055000781c0410014001840d24013051054514189400c040710750380348000919101003a01d00c2d4002c15999824029903408039032014014001e50b02c806085010180ea500340d80c2c0514455034420142d03030b8414040118400d0300145e030120340051070345c124100d003070815940700c1c0a14004d000100c1e940c0f80d444441d900403034043c1c0c0d100d4032510001d420510011030a54100e40d100103500b03d404880f02a6550310709007450003400c01100c0c514000d00311076040c4001c3d03520403501031640d02d1203190415000d80024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 819352104 1250 819350854 819350881
    0x9010e0d03210b0f121c020a122c03010e060c1e03010608060910050d140d02010e0318010905090109022d0304020d380a090803040803130b0109140906 66
    0x490059404940340c1ca00e40c2e610030300f422000015012841c0841b006240007650018940003240e000c1c10000c20a070351644810303110140e020840c6580b000d41078540803101405000c0c900da03001009000812510501401107003072980813a03c940c0070307440208810414860070310000000481c420f4031946154148030f4050011440145180e20a00c015000501d007030340d1200c1b05000504d40a026076004416030b01c0e00c00548078688500c04054415046260300f03192050094050341488540590714100101d0041c06152030310100b051f05201261034009000d80b2106031703440c02007214010058407902d050b44014240030501c609100820705007141c180004003514100c079001641181c143c0c40c52452031400400030740c81c06100c0228a0360702c40a1001740351b109034100e04800450201061190f4803074503842d044584032076004e80000410700006002600c200f0056030801301c1c6c0030011311000b200740d48180700441e00b60000d00b0aa0748680c0301c2c003408042e450407941c0050052010308640e01d002c00100041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 819353354 1250 819352104 819352129
    0xa0606020a08030424111c0b01050912070b0a05040608070c02010e0d03110102030a060e0c030f160e0a0f03020f01110d05160b0a0c08070f080c09010e0d03210b 70
    0x1c17513408282d40c4104400e5107268041c5642032401846031034485c48030f806444d001b145800c8038200707400035488090f6402c0e100c3c242c0302032016107401d410301c802031041c0301e44001064000010f6200340344020440021500280000140380da807659540e40c01c100b8024a2610041c08201c24088660403800060ba008802c46003080302c1aa2201c0c0741e10003d0904860a0103064040320b0b580d44000203008560503542c00c0b100550364504007100c140c0d00c4032010341c512031100700c0d06010182c0110003c9504064079050242c00202035190001d2840382400014041040b9a1300190749081007200c1002182001e031040b060700182403c1180b400841542c030b842d1216814850704007001000210442900c041d030035600006600705103003548624106245c440104810390200003c941c0400010b44d140b803040801441407002d41d079403051191106880307214160000c00e0f11b94180000d40c10032400c1520b89000c00d41d00b6900aa4031054000c481c182c20030170640344045543c000d6420b10074455101d80b500c1c56040300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 819354604 1250 819353354 819353363
    0x140a230a0609052a010f050a05120f01080706111903090f06210b0112020901021e060609010e0c071b08061e090a21051303150b0f011e14120a0606020a080304 69
    0x1c1ea01d841c800c00300d864ac03145080300400e20913101c0a1000c004418080c05040e035129104941c0310355100e05090b0b039000c480380100340c01075014080030700240c00c08518005480d031080c141400310540310f4244016120207a000500065003400c0c3d0480e0005052200c10f8800d07180880c104841c80c100800248003015070450310880c0c03500060514100d074401c205015418080e5540300011105581d9000d4680c1000d0759120303c10745828001269000c40551194022580301200340e00c0c24220b40d076400715400101c201c840d0302c00380c8a040066103a40610101d48075078000203c5820104014800485044d0050418100d66110f411040b0000b45040ca0700e0500207100c0480c00e513203101c50303501120075205461540403820010b15001003082051012082200701948050100c49128802c1c400b9103c088203100b070000f00d808480380035282d0814114400e0a2007480d0000180303403401c06542da1944040001e42964015030300700952841c50f807207014050019440584080912078480d0001800003400140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 819355854 1250 819354604 819354607
    0x2010c030311161a0c03101205010b090a050702010c11070e13080408070f05040b0d030e030c0a06210203040b010e0c070c03080403140a230a0609052a010f05 69
    0x4000d544120903600040150146a0191000c9103131480107103060482c00d842200811020507480500c0100b500e00c26500f0080001c0c1961405840346400c2d0401c0d41c0035911956555045102a2607000011b4030410342c075480170865040813040282141c00e00d108131020007016044c005800000480d850f011500e200c00c0110103030312540000040500f000200900c40c2000141c00522400042604401c0311119100e01c0700b16580c820601068600000c1e50755030021250b1f05690010b4092603010004007009000c079040303001041c012601c5180c0b1342e003043c030204222043e140c40d4199a16000c00c0b2142d0006819402e41c101ba580b0041c200030107000d81c901082409001a105000c0081680e00250b0030815440c07109aa80c10302c51880d41c01404280e902100c0d1840b080b1004800040c170542d00342d40914443c4800c1070726a82045000150214161540600300703010005c140325015a9026038021400360108501051240c403202d100c1c600700d114180404030b61180d650303803c2031b8142d502e0f003254200036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 819357104 1250 819355854 819355871
    0xe0d0302070b040602061b1c0203041e0b0a061a03061c0b010b0d05090d020705010807030b120c121c20060a090c050103060e04171611040b0d02010c0303 67
    0x203a0912605810002c4041804200003451590000e2040d000e03800075000510b005000c0f15242409114400c0d0400859240030910303031030929680d0041d6031140c05410661000416038480003401400303403d050f0b4582c0c00c0c442c140044005030b4070175000101417402c10400313074403040a062847c070f0000070012403007001c81440011004054401e13080e000740e07201140d55015a10703600d60700400d400031424085180c0c60040000c000d007400142011a0032200d8009103105880e00c0d00446442400900725800c02d510f680307018005803540544071783c9200081000c0d190201001061206070302c015a070581d59a0700140c0f400450b5588903021010000c0680703028200301c202c000e2007000802280460101c1841110200158400e0030f601c14400c03184a440c030500784c01d5440004400b519a180107041035861031500bc140040c05490f9000305040965441e1800c00c181c440500400c1208003005507654003a24081c01034900d0940315004220504680000c0e004c007182d00000c00403443c000005060680d01c0040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 819358354 1250 819357104 819357107
    0x6030603010204121b1d3d030b10030816081b0a0b0f07050f03131b0905010b0403030906181a0a14120c130503150103210e0d03 56
    0x11a405050074401344150321000385014089140051912035408481d10030102d640710b01500d11103188514000104959180e200c0c0303602240703a810209804581007a2403000e0819046540305500210a051104120340b450600c1914108004c1038444100c0e0240003c2c40080d140b44140c450010000424040041c01c0d460040d888d44503070441e14100e05218100040c80d8034000034843c11891181d6881001616040d4803400c1004e0107035294000704000f4458090f02c1c1c0b040c02e000c0d5501001c408000000000551201200038188800d007094004a01109109955150065038010510195100d207000d14589000700720040b036004040030005006c4c501e05060140b114448041e02d5141a0504008200d500046040d03006608140110302060080c0c04040c41c030720161003104590b070940340c4c2075075640d8055000395800504004a2031908920218458030100244810b18849164100203035065041a4088504201c1c402c0301d081c01c8139038001117641d071090384882c002c10107690b0202c03a00c006240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 819359604 1250 819358354 819358357
    0x30807020a0b01030b07030b040e0303060103200d0c1803120f300b0d05070b0705030706050a050402130c2c030114040218090c01050a1209050a0b0c040f0302060306030102 75
    0x70058400c111600010042c890140300190044240340c80c00c01c65106204103000907100031020303141603034000b403001412030b501a811040b0a4020a08c800c0c0300300e10055100500340e0400508450b03225079890101c41c50356003201100c4003030250000c0303c56040d0b1841c1c0e900710350300c0620f6036030700100145440d00001d218040c0c0d0300361032540294204448582210340c0d03160340301c1d000024840c85103800c01c081050141407017540c1c121580c0c0c114015001d0320b0b0401c101945150310444d01111544070400c2004041080752154a000d80e40800c00070030a0f06003801004800c07003200464568440c503100341200c405810000f2510341541d0702d07040a0000c1249410880e240349000c00c5141c06500b00701008406c0d4042619062240d0300c229407100c10103002c1ca00e801c8113a0012280e419143d030003840000010340c080e101414104529241c80e03580c0841000142056031255030f01214140c1c46400f401003001841440280d0048030091000d007403900e44a1008101100b503c8040d004900010100c0c1c250340b020340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819360854 1250 819359604 819359623
    0x180a17042301030606210504050f060103051c0f080a0c26040614040221010f0c0203030f070806010c1103030706020304031d010203030c1207031e0212101203080702 72
    0x90a086401e100300d160009040c0103601402e0009103801ca0224076140a00b40c0b100c600082c0d0a0342010303000000c04800000c010141003503542d032065550040100008000890182d4414005800051900c40c00e40006194118050042c44200000085003680c400600ea600400384240440c41d6102c0c0541a541003440b41030491030100300c1400202d2110001c20980c0c0114440c8004100c5c8000d0075503400300251003950002d62150a0300d40324036229556000c0c1030500c141c00400002e44081602c00502102c050f9044900035800101c104411b84640c0038115501c10b40328148500c4524021000030040100c45070014914540c21030504050b0b101041903504460307114030119940e060504020780307014444150055400011503a9100e90b51000c0306a9000f20990340d8094101480c030320301d82107035041c018054010150f0b10500710080ca1500b110000554881c2c020040c0d41d115950021300c2480b500070041201a03010840c00c01003048a00796041100d45c06144c408050386035520128101882007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819362104 1250 819360854 819360869
    0x945040b04021206100e0c0c0d051e070c050906120c10021c020127050d050d0e060f09071202090f101224090b01032006030903090306180a1704 63
    0xc04105d905107402002205940d02030000d0704080c1e440443c0902c152103001507124044d0003180001e4a06030065025201d940d91075600c1c00e0611a00743c0a10304150802d0500740c0b8214103021040100c0c1c1801a21590050320603649400c000507100d0180340d075030081c819a98002c4042103880c0044510920020f500d0041c1d02ca901c4408061520000307001e01b03101c049030b0300d4468030400360204d81c508c100725000036160f0080c058110102143c03808c0e5001d4108980d980e40080e1030b010109448041803102a12070f54480300c90541c141004e4015528006d0541c011350b4035615142c05410140c0d0b5903150a40c3d011240c9030001c0050f64400c2c40d03120f0700d4034483d4041c1003c051140f0b44101040810300050000f00e48454180d51040e010b1107100041e1018a0405002c2d400c5860060004c40e084a81040800d1302003c2e49010303004094020031041e500c01c41b10001140c0020a0f207140502d824840940c03c0307c40304809260440c4849001900c6049901c0002e040d1101440c2c07100d40901c00105481c01010348 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819363354 1250 819362104 819362113
    0x902130605030d02060106080a090c0b07151b09051309021503011503020f0d24060e04050603030408120a0c08190905060414040506060945040b040212 66
    0x81040600646241d00840d03100c2d0049011031070f825803000a840c0d049a000b6030b0f03142043d4840c2001c200050005840c00d560324030a007800410740c419440010031525102d036402950070100e00d60844115204c4000c2000c10107180510701e12030580c0600081d0945404451440c4620001b029010003007402a000940222906500c881144240d5024504072400b411001038001d500b000210101d1180b400c000849900502548220801c90350261280b8079001442c0041d4041188809070980100d502002c0047c0c2ca84e090141c80c0c3c2054010541c10540c150015810281000c09d4103840c0c07140b1500b6030824280110380c0004546c42144d101b0a190f410031a40c640d1101580701c0c44110300c1c4900c80003000306da0034078400112405c0110032103084504482d05550801c0d4031004000140a020301441d0b8080c03000e00c1031480359502c040030701c0f454009100981001c0d0708020804021a041c413011702c07a0a068802d6581c03851035401d480540e0065010b414901c01c0c2d540d51000982600c1c441008070030500c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819364604 1250 819363354 819363379
    0xb1503070810050603160b0a090305010e0d030f27060b150910022808130f03290103020f0102030c0609010501230d062007050a1a06030a03050d0902 65
    0x714049440091600040c0003561381c0006165549060202001b092181c064080010076909000343c00030210504e01004550359a8640e40d00391254000f221005403c0101d00070700b425014400c0c1c00c83c414184001f440021017110310007a2401401c01c0288200c0307040c8180f03c04008140d4040742c000d60004207921100030010300301000903005181d102d03014448091300022228000a03007502183c55994018a022070800c12441b43d40c2500b100403101700000380140c0e2800d0060401e80c10141c0070710700d1200422843c5040061040c102c0f00c2c1020034680410710a030030566081c94843c0e040d26010b4031038031900c0d600000101d1442c07040c4e0701c42c0703503441c0141c80920240000642119040342c3c0245141d0f04840383c5103e03440f4000d240d6002e52a4460240325418000855641107860142e06d2800d071b0040d1016410880050f661010b0002c454580101e4800d034100148641046012a0051084550ba141c55030100e40d40b42400307000035090100128059100c00625040b0701e0a0660141107d1040390 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819365854 1250 819364604 819364619
    0x40906031a0105181b0408070b032523091c050609031c1d03030a0608100b061b030405040e010603110d020d030e010915180b160b150307 60
    0x521003086200e900001c400002698908040e0342210801044840941c9031200c0310070f01c800c403020050404801000380400260750000303212003801000300f060360956910301041950116650780034245644200b040e0740507100380e4000c80030040c951500515002c010148448808e503400f8070500194400c511172141101d0040f10441054981d2007242200e0262310b4084480d03480f8019040340f0000c00c4849009682c0d1100c02d60401c18010003410b0303e01c20007480712030f08a41154411640180d14640b03d6204007c0410f04002190305103e8154081040181d07002c0028514030440c0c12411484c001900750f02c14140e0b0900c1110000c2c2070042c001c008842034425800e018150070b110581d00c03500541c0c1d48910504200190403107459004109000c00b0b4015034041d43e4601a010ba445d04100e560180841c0150303098105003080d0809407140e5988940d140c03058241e0000c15002150341c00024429580000103095103113454a034002d814259554a00c0c40d540380640d00e020b4043e43c14440e800e00001e005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819367104 1250 819365854 819365873
    0x70804050d21020a121d1f020f04031b0801110d0f0e0304080c181b0705070305010f05040b070c020604141309030906270e07030902031e10200f04090603 67
    0x411039a0001e00620210070300e154034021b02d0303801d603000c190070030000400c6449030f401d030800c11010444001400c160500e09013181c0c6070081e8100322407070100008144001c405c607960340002001c2603802800025807648046846000780e9030580e100701d450780700c074a25940082d0821644107165400f10380d03c0380d075a021100d985119046000b0300859100725040822040c521701c251045e55000c040100d0507001c0300c0718000950103000d0070b03602402030640200000f07100b0702910b0a40000784601003100d04140c1800d48120401030181401c2c032025581d0080140c40d217400352801c44070020a0302e03070406005400710301d0b481d40380c0280b02ca0441c6000c1c19503003010340003209102034544a5588160444122842100d5520a84072540ca940c40e110410000d144000c4001d6501008928001c5240841580032070b2900c8001560550a81da1031040703403141740410013211805860130f9106206961000001c1a0b42031a4940424183e200c0050b01c031024488820407980201148001001002e82d6800d00e07103c4c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819368354 1250 819367104 819367127
    0xe011403151503010c05090a091a012001020f07111c080310180c140a1b0303020f120402132703050903070f05010306060903110f04060b0a09030506070804050d21020a 73
    0x4100c444804109803640b4424091203640080c15032b160079a03007000640d02c003581b03009415000e0241d0a1800c484100a0010b0404010152080341d01d40754186880104690501c2c0307e140541ca034080200542c4240e000032000e40340e0818030090380c03501c440c0c414548550664201342c10b40c101d88003010726600060350291400c000540e86e5110f40040041400840d8492420520300103a52203400000340fa035080240c154030b5200b410014500090000300f2142d5411001d59070560100c41c0003080154103045100c0803200c060604200013a44554000c05103d00140c3c0b200c0c0c4244942407210410075014408641c500e15009044800c501c0d502e0300704040c0f6002134003419000a00300040051800c0c003940505043e00c1e4400320441807030451030700344110a00c240b004940e0154031800001010184a00103100b07020031603580c03001050079404d08614011018060f802040300c081e041102050303020900d52030309049458021108180700b0a41c0c0b01b41420030210b40d04292002408070465034010741412071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819369604 1250 819368354 819368359
    0x160803090c1f050a02070f060e09010905240f03120c011406090a020904110c0109170f040302090711010c030603030807170105040b04020c160e011403151503010c0509 73
    0xc01040300001c2c400c41480c05081042c0c2022168814034015025601030b001c9045680704507454507564699044040545500040110351154106134031414480012405000c1a070024001030400c12500d0785d0710820406d004484498042c1d915141b5568908880800480102200c018502013941c9824a0307001010510b0a980fa0070700540f614007240030080c0c80b4041c020600c0d80654dc801050901a520110f10180d000d40d50708618503902c111040a042c144000e4400010a2061854110240d40c1c8000c11a44141014003000c02d514206100300c90650b81d050fa00d41001c5e032180203040d5414134006007890751a500300885200680e0b07240d03001e0001c49029554500258546240c03e8030b07120f680f0481d500c50703000241d0050040381000d800281c600240a00014030707180d010155179040801110003800c234081c400104110320380142c06414050191a100400b031507240100007039447d00150100700942e500c80001030a01001190310200f02240a0001c1c001c0000e40c40004006901c082581413 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819370854 1250 819369604 819369613
    0x31a100c05120c19050c04180506071d24160602160b0c190e0a030812010611160306050a06030503070606150504060e060306040213080708120c0a060506030316080309 73
    0x8900d65800c42d9141013241e082409030480704036800034440a000503140001900043c00510400110304201c814420402070342c0340c0701540708115180340051205071001d84a25060100c0d8802110000107102da944840000c05039a8025a041e80c2c0e669841058064602d9101044000d40c010448860303a112500c10492050203070744001284090b401604090005900741a0400710b004c0c0c00b42c9002031a4100041412598030b650365109202d41e40440c0003c6080d01100004012030390b044031032201c811140c030b0040d05091031328158440c801d407918400900b0254403880071a151700c82c0c07640000042d5802500b9603607292494100307c0003400091281241404200e41c007088070340d205006403005d580140d51030780441141d8070b00300462900003030308540c0c0c4151b0802006d4200c0300e0310b071407600041100074054080e2a00d0050400d0400d1139445051000c81400c1003202c04400010480070307142030780a440080c95444050129286001d1400040100111408a10b01380f0190310003461080aa00080f0f5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819372104 1250 819370854 819370873
    0x7090b130204060e0405060310150e010617150423040309050109140603040611030f070e01080c030a180c0f03020901140d02060f07060501030c05040c031a100c05120c 73
    0x200220b200728410600040e030703e030031583d5041c82c20b40c11884e00004010100c603070315501ca40c0150100e5007140b6411592209030541048161209804a070040445041a4203801501c450280d010070005200c10400440c2160030f00e07142d84d856100d0400313006400003610400540ca10400381d001002e0314194013041c0c1d420000100c9600c41d040c2030b0f06807072085841103513401c90305042c003d00e50801751040700c0c00703901d40780480c0141e0080d401640c46015014400d00441c10641d9024042203100c038000340c100081c9000f0445200618011a0303049508417000117001020240e084002144001c00203000240102000030131540d040011401c3c0c034000c540700310040e40d8034043c0c440d204d0035240c5c01c50b400005280d0000050700d001c0c40030f81f40361400c90078110b00c2c00b01c2683d11b1108441c030036003048500003d144410300140c102482607131011102d0742410461441340340310b10071448a50416141c0f0441400d098815894490003070030b107009a102c1e046400740c641414860010381c1000818010038400c28810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819373354 1250 819372104 819372139
    0x60603060510050307090c05070818011d1c031206060f09290703050412051c0e03070e060d0b0a06081c05091504080604050d02070603060b03060603041407090b 70
    0x24011200014000c003170341c030b2404407050b000e40301c166803001c02c0c403509100800120f20004005c00d111811000d2000b0300005210001d001d00040070610b401c914010360003048151506840100102c48045d0541d298008030b00d01100c600c2441c801080144d420104000307001070b00192242d04031721850b110380100980f17800f40c080f00c0400c0e0401440800d80860010010060224000e14403e402440c00358903042d280d01e403c401d5280c815004550585c400c20309001400b038465000051714001d441d14181c11001100040e80e00c2d5868044c034800040d885011070521303543d0f1491200b140f5404507083c5028601040445d0007070126110b80e1125001d903181c1040c26002d103e803040b0b038a2100ba20b515007446082c5060010f611003211011124600821011401400800c01244503621640051614100345e02c8000e083c101c08e64403503024035040810500040c03400c00c0a4950002064940382d80b80e65440c24400e4120202d9030b41c4903400c1c003d183c1c02056550441c0c12500040c0d000b0f507211441c24080944 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819374604 1250 819373354 819373381
    0x6020d1136010804060b190e010602210307030c030f0c0914043305040524090603030a030506030a2103140c040308091203180316030f121b0606030605 66
    0x1c040b40028003883c0081c000803102c2c0c0c03148040342c002514004008016030310103602205290441c0820950050042012030b90410a410040030b0f045910810b8101034007540c000390101510302d00515031500451100c0c94480d50080100da1000881804102817480e000380031243d140c00342d18040140403140a1041c20640a103031042c1090800070303102802410b10070141072902910031214086880300c001090f0b91a03010306409031480440f070440c00c00138071045102d059400d080313803809001c85d84100000c654000c42541c4940c002424041469540c5400081c00d101040c0c40040c9441d140c1c441520300e02c03a6050400d400c4482c113031410030101d1f11a20744011005021101321981a034100424000500c618015005469020309a1407480d03002803402030440d0412075909465140465502c9d1080c40d08202c4194500300134065000068159101d03203071084590040504035541c100c03405814144200f10b50b00120f41000720100c1e5528040c03508601500c0742d40f205848540c140b00204186511f28031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819375854 1250 819374604 819374707
    0x1110d02070c1a070308041704060503060418021023070303270f140f070e06210a0f020d0f0318090e0d141b0c1c080706020d11 56
    0xd0414484e0703613044551010003001204d28484040d000e14510101c0c00140025003003a4403607640b60301c2c00500b4441200ca000d9001d9001c445c40c04144001358503803004000032000c42e4540040101080032440307041c42c0705124182c030382207400208003080c10741c180d20001e410300e001c400103540681d260040d01a850109803004c1c1c548041988200001645a144402c14070f131000140da200170507440360b490820000383c0c0142c1c81d482682d0108081c41c5404a01d07406440008902c403440042100700c40c65a47c08441002031020f19200614000d43d41c80798003411106d944802c8a20014129141c02004152a1200e618406403c01404a5502081d010300d502185100000b44ad80000030700c0103c8406d01480b821044881d0704110114010418031007040140405000030841013a07a20248032400c14903198280c0b800b0594881e00c00000d04600444056517040302e000358544011090f2580104084000e12401110019800300f51200c29045043e840422018560000380f40c0309075a4801503004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819377104 1250 819375854 819375899
    0x70c12051002090f040e0604050c010512010b0717040f1d0c030720070e09160608071416210206060d06150b0a020a0c05040207022101110d02070c 64
    0x60360100c4031058160701408915200601880707401c40350030f005c90101c400400e0030240d190000790401040c00010483c421842d1801c1c40c0c0b0302e141680b18015942c08201c18003610780000000100f010070300c00c03c080d00d6040820072008031603945030f603800841c11017403840c4100c40b41156070080d5401c44004001540d44541c00c140038442ca141d1b9070f000c003103408007000140070000084040049208007002c026a1014140401c4071040c0790508640340c03441d141100d0304412009601d01c0040c01007540c0840f00c00d0f04800d00c0e0a106000c0c15001320054014014803020009102c04e40040e001030140f40e0483c848810300c000b090f28440d0803500400c0380c85000880b40250402d58401000f00090207030b50048400c60404560f519000d500c0d030000900076402031351003000503031100020800f84007442818900030001120304500e041117650200e220f040c600c424400303410016061094040c0029003180f041c4605a0054564034014240518000d4108400685049100040100c0c980c0390b01282c4003040c0b03456 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819378354 1250 819377104 819377113
    0x1508011a0f070c03080f040501030f0507090519031a04060f1109010c08070515040c0e040b06060f0c0a0309080f06061c05071d04033b01020a0203030f070c1205 70
    0x3640c074101c81c503405200c00700c0350f11440f4003000001c40c1040740174004a514600707129580b6844c0800050580b1120070f00f003c2c40704d2801040c4030f8040d411083c9081202c0d82640e4040b0443d0108210424560107030303001078040a81c0c0c000a4071a00046410b1a100e20721440d001c021402e022102c110031039440c1e4503160362109041011061720340c0110340c1d10b981c440c8212a05450300c1080e542d440e0401d400c041140d183c0191110501082114660800024044040244400d0328241e00c030060120300c082c01d07c030301401c0c00184001a1000120445900294034801c80c5e03101051842c0081a8100510800c0be050040801c414610b940200d48103004140041c02401c00f03581201940342041030b1000b00b107a051080b0140000c200c48503841500d500d09000407122039518103424054007c5403a03041c0c42d90a40081001180340340440400541544011040705410326011001030745800c0700070b40013a40c14480070031a40c00005407070009040b8184203032501e010450f079800303c248075400da1540040a6810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819379604 1250 819378354 819378367
    0xb010816080105011b08210108150705070c080d08010e1803030613090f0615090216030c0302010e070306020d06050306060d120c230c01020d17040804030602041508011a 74
    0x410132480081000c103107a0245c6032925070360b400500d68040d5191018610b944407450125500c0c0103805801001c2e035501602d01c0e04200c0c64030651001e0010984818048003003800d200380b106401d01280900143c1045030303035800c03e5203070182401c0001d102c0d2140c903100c2000059002401c1d11000c0140d42c1c5640c00a41c10340c0c03190000c0000305498800c0100c40a5924048500850035080c00e81c0c0070f0b0341c0a008005110b0761003138102240400190004044a80100712032107005800e800a203174003a8241c6808880100286400c034098105005290528030a40c1d40100030b12051360300400c609105400d0410410766034000f41a103c0c00e0494800e90f103c44c501c42c0e60808540b034129003032040d400303600c1c1000d050401c543e00c40111040036001d044103542041c0300442800d80800c44a55511000d0004081c3c0c1c0383d038564002e00703044c204c0d80d4000b884c7c80381c040850104002607056502455100340c0035500c41c0d86800c49401c00302402d000440015403400000511220b804c00c4104d20720311910f81592816a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819380854 1250 819379604 819379607
    0xe070c1101020c0f0f04020f030c0c07080303010311061809150108060a080d0f030b03010911120c0a090f0905120a02060c030c030f180a03050903100e1506060d020408010b01081608010501 82
    0xc01400201d0b0304941c00304123540170b600300d13000110f1051640c1d4440c0340d124418400c00c2c40c0f03414410341024034180c0c410001030010410494090f09451360486859550f4250050b078030552074264004941c01171000001d01110b080f90b0a90100f80386402e0780e881209035144010444c0c096158450b001040d00303e016000b10040c41850312003ca81060700300803841e0800080481c3c2140c0003114166900d19501c00b01880900c0c0c08110000404a0040207001c50001a400182c01c1d99440c400c20740e074550395600ca98850712040d00110f064a801109440c40551032940e0100581d0200d0500c4006000e44000111201c40c05d0701540c0c020442c0008c500e0640d43d450305900891030b0090702150030780001418441c0170120811041d4020744c8246d581d1512503101d1001e062800d4100d0880000c0da07410042d200281c03902c00514211054410f03082210ba5840e2a0041a140e10410149200c29030000401042404054010b4162640280c1e2068000d554501d10b01c00400301d21064180091480746c010002503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819382104 1250 819380854 819380869
    0x17010605090f040b10050c0f16050916020c0609011103070b0609070f0804390f050d050c131404080c070b1204061d0d0306090b1c0303020d060e070c1101020c0f 70
    0x541a80c04070390780c10b6400b101c07403490200c5a14040e201510500c201b032015003003180321103401450914cc2c25101c0011413201a4a0b81c46603100c3c4c60140c0404500c08890368469070440d82c040c03228000ba41d42e60340941c2490869020300f12001c42c000d58400d0003080b840d500c9048070300d1382e244265070f0310303400c1c1d884968420b017900700480c81062640650b0341b40c01d061000100784403140c9883e20070385089050300c0c0c4800f806810265038031041c8107081008400000c03980108801202d4442182c09a5410281c40310b00001466030756080f07001d88411f10100000c10202c1c8000f81518040181103581c115600d050404072403042d10303101105400310340c000c5000a101904030341c01030481010320b070b0307800c07010303103401354036004442d0100000251161020080b024640c0b044441c01e00742610266107401d41c0c095111003c00b0000d40040406034000b5121080122641c410405460024402ca0705820081c0000b4a15540504151407138100b50210711150360000034280c44009010308011910040e035410800b10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819383354 1250 819382104 819382117
    0x381f081e16030f1a15040516021e01020409150303020c1e0603040218090304031b1d070302040b040e0702160302100e01020109060606020f07150219020117010605090f040b1005 77
    0x4061028031130745181001d1000c0510844625603803e010364401c00070031083d02c00107031419580c807403901005400c00340d000c50500c0310340c040c0941100a403043c0c0c503039a900a00c41d9038066500705280c00520012a101c6000c08000c1b02d000f9030840f40480626010040c2031740e569800d1054440f100620084141040000b456116000400101c2c0841090302031034803122085503010041e8100103014410070032400c104103074454040761141c50240c1002030460782d120300360030102c80140c0c10100041849100c1e80494015003400c158907900c0300e59882e902e070f81549080d103140c401760042e099024140060f003045481100c3d0000c0005078185030058040d03030312680c07800c0b41504654852090b40c0200702d050188600a1241d940103003000146030000030b090400c0c0d5080940d07070082c0020760380029540010280c1d42242c2c0501503100f92030251006a80c0507022180c54079510300707400c000041e65500b24001e0034405200f0b03210001c0041c0300e6420081161403c0d27100d13590001c4500300d10540c90f44100060005c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819384604 1250 819383354 819383363
    0xd0c172b0c0f060608010c0509090604020912070303050d1b1e120608060115170103111c0312051302090a180203030f0304381f081e16030f 61
    0x450242038580c550301c0118810b0903106151a004100314062003445000c0010516150a9081c41d1180001419045000d050b01e031003560007082c80034045d51901a01e451007030b208021682c0c21a500d150151058001c40b607010003d03444d0829162152a58a1440841043e42e65400c0b008017000801024040d620661000800000850b50050300d070540c40760f0340141c0310410007403d05602d1310040d008a21724403202401081801c204401c801580b0f006d446040d41d80c08250182403c2050300421207030149081189a2030702c0c10007440e0300b41a0050036403200e10380f050005100b1075075240360041c2c840b0340d620340c025040784803500018800d440543c040c444134649800a544503101f550002841d40c0c03c82181d00e03020302d10000c00d000070410050b804c2050071042a00c480210300440110000340343c500102000c1c022015400200c00030218444901e40300e04010145184d2138840d01b40564504090403640301745002c04009940307801c3c000070185419507940c03424402041c11591225007294000d1812107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819385854 1250 819384604 819384617
    0x501080a0b0a06150e1207051c0501090602180108010b04051815030102040e0f10180209031e0a03021204030c1203051204030c03080a0902090705090d020d0c172b 71
    0x4d0b41e0b4454100040c01c62800d55460400034000310411210030f09400d0703895200e600280080140c0e0b01c036800801c11000140154807685038450070040d0240610502c020440d0388002123038a020354102d4600d5418440c280e03601080c0307a0b02c0f03681c0c0f041070b403085026283e0b003c54641152070500a00c0074003540d00c80940c130341200080421402190a98005800500b03110900c1e03400c1000c80b1030554001a800099641c003880254a000000c600c1c03005289039400c0c956800088412a036202007002c03a001e0b18040d03444810322010401101d80340c2ca03140704200e0041c081e074402601c01c14009801e650981e50442504e01d07519244c040b00d0300d080b21921004a040c428140004048101300040d20b612683c007a84848035100100d04e030042c59000c005002c0d4a07000c0c40c00440401507112100040e50241d441c2c108182ea0340710344800981011442c1c0d000a6204200e203844a08003d0102190002c90700e0b15140d200c40181c0001e541500d440000104481c80c1c807038034085004078015000d08036030303840060034100f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819387104 1250 819385854 819385859
    0x403060b0307080c04020a09240f030203270a0b01080318060702031018050a050d110d020d0f0e030303100e10120b06060403141f0b030a020f03070b120601020c040501080a0b0a06 78
    0x2102c010b4a400d170551408900c2e41010030030b9002b0b1340d0500714242a15046255180110305003202074110900c007203031042c1643c40d0820030f0400300503901c000c0c2c3d00005040055a59026116540e0744110a203040700c0e20050440b40450516605a07841030354005e01a0007009402c0a1b03038001001100e04c0c82114100030100103000c40d070140b2004903d00d004034050040e2402d801c83c05410340740e0341c2040d80c140340c0c4a070ba003e15050781e001c00c241307a1a82c0c4519048080d004680c0c1300b100d42c0c00701a05181d034180000818800c10000c281001c00c2220309001c2010015030b18101d601404010350310032556548161401c000002d5a502130407035004100a003c582826182d840d2141c05458015540c16260310500305116040441c5510246416550074244100030b0010042911a21066070080c0240c01c52001c032002d903070b0f05010110140c04104140b0340c03110040700484821000c1558503a0240c011208a840c25090500441c1d0586911000600c1d41c03a80316941e980d0f50220040980c07a40e1035403680f01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819388354 1250 819387104 819387119
    0x1404030b1605190e01020607080106270b0d0506090c070209040305030604110313021503071d06090d0f031d1818060106020c010207081501030f06150b0403060b0307080c04020a09 78
    0x14646802559020f504c09032082c00a40b4082020b40381005009901d40100b00a0703501c070b5030380400008500d000549d20100028a010308543e150000c0c001008080707070440741c5106e60380c0b01500c0b03200200c600c0f502d00d48509402100c20b100b80d20001e5000170207070f400507010a00131002140c100d0006040000d80c090101d91500041e04151010000c281034103100c41c0640c0f91079404140200e41c0400e1192543c02c00f00c1020300301910700828002c13120072110409000c1e5079020250344480002405900041c4068a020b4010010f400d0b0100c006ca550240c080c2c202110051061045c2100034100c1202c81c10060441120608001c00c10300c10b4003200a102103000c0002e100850007404113400900300840700400190400c951a0094503141d0b004464102c010742d003854045046035000305040864140c00d042100c098882d000701c02d83d02c201c1600307001aa4019210041c42245c1c000c9400b088042002010151a080548100c86040d4081010100341c2d01c0d09900820100ca41418100000c60f80c5120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819389604 1250 819388354 819388387
    0x120712060320030c030c190308030c0a110102120705160c06111207050d0c0c1707150203090a060e0a090e010c03360c0e0a09031404030b1605 62
    0x20441d0030500d0b4030340d00c01c4001c1d00000c1c03810602000f103003d0201e403030354000401d40da66044c0b00540d00c076488001481c3e01075800505600c01450300f003610b003562858035400d6801994400c02d003040000f1507806003d8582c1c8818400c1d40e41f070512280b10040940c0b180d40080b00e05402503240340c851131f80788184e04400507018600e280014011900c50307035440d00310007882c10b090403558420038610f854100000c00c0001c00c04100780802e406181008010341401d0b0426030104040358200040d108c56030072a00620210029052003150389003012248150302d8680c007243c03031b4081c4103203a0b0b4129507800800d202d2203004803c8454130780f90150080070031a640b0321042c001c0d100b96030100503159564100a004003903043c003c1c0c1e00e165000e000c400311b20001d000b103c1500000203c02e12040c0034489402c01d402c105400c4454402004a440c80410354182036419000600d9440300441c0442d135040d0048450401c0d58064804480c2c110040915a6440300b039070401141280b28888100320003040300001e100340110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819390854 1250 819389604 819389609
    0x70f14061b12070e18010504050718030215210105100f02060f15130524010906030e010609060803031801180821040c0e0601050319230106111504050312071206 70
    0x9003201740951400013844101c0300040d050b00304010401000c1504060781603919400caa506441488642800003804c02382c5020703a0454607070001a08405840d0b141068540314161042228100b907030381060102a11b00c0071485031048056044200090040c0311040c1d0650362007154005401c40101090f0001141281e0780600045c400d591441400224108031009640740390700800c1e00c55038040280006041034100380301d65801c1645905a101003c403082d08000300078580200d040c03140c00d0311805000e850360004c0f01d040c03c1c034200303d007500c02c10040140121220054032000841885c03003180c494080704c1c0e0240c2502070300c025070440c801311201c0340804181d2055019401040304182003002468000c80007800090403c42e090041c000650300802c00442200d40c4604005150001d000310150500400e2030440d800c28001d5000045903608000703001001e06116080d00c09050351048250034943e0b060b10007401c158410300142e4025408003a0498000d86e907400c0151a8082074a0400140c49054 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819392104 1250 819390854 819390889
    0x906010305090703021f12360503031618061e1416031202071509050a0507090b0103060f0810021315030209040c02150a050606070f14061b12070e 64
    0x7038910746e080f40c0c0c41082c844182c40c0d083c10500c60130040314002a0441003980584103400b0720480710081020354034240306116a84001600d80f00d00d81840c1d1040c1d080c030b02500c1e8030003040946001d4880002e416041d0303420b0751007135201c510b079001480c04a00c20034140ca08118042c030041030f901c21000c0c6040307006030503014520110006045224071380140f6503041c0320ba8462245005000240000c0c201c98180b004032584500f00160600c403c1c180a031800c01d601001030040d01840030041045101c03600208588407084e02c05103c03140d075841904003035201c00c0c440c45903940c11420340285601d5054008000c4190300d0817100030066103c40f5899610001e107a60800420703800201c0b4502c5040c07074003502d0b0944a1900140c18801d803c4500000460300003880c145c1d0003550762000946a555400590300c04c103400c00b01c151440d0010786030480c004040560388076018491040081e0300c544420700b49120b80c151018841d0305110441002c2803001c50f0150030700c2d0510180050580d01900d8001c071201e00e80d00007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819393354 1250 819392104 819392149
    0xc0201090f0605010812040b0a0e1302161b240e100504051f0203221505071704030312090c0528090b0616020423070815090601030509070302 62
    0x401410510300309106d501c26100103c1031000700540007042e010303200032803124100801076a14141c0083e04018401400380322803403003c290b0f0b907918401d8581480d02d151040070003003c0c2c2100b08424201a410070300c140c1c001d55400c502c28622441e03000268140104081c140141240940000556030700d038030b001188006400845c00704494035120300a00520710b048646402021640c01009480e481a0302000154081074014003000c03954004e0f0b0300e401484c1013003c80c018910307210401059944001f40c25551141284490602d10784c01c007044500302c1e94145c031000c00343e5518500445c050520311400f500c2100440760005450780b91502d42a81c88140b82c1e50034607403414010103a224011442d049005000d140c041c501080b511140201c840d1094540081c1078901c8203480041c000d000340c00e07524280340c0c8142c556505e440340c025488500402503603c41116640d0b410141103060001428040c0c0c0c480103030401b041d01d950081d4003454002502d441500c2d15940c50f03402240d2400303144482e440110b041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819394604 1250 819393354 819393359
    0x270302010f0b0117090f01020c161a2a06010b0901030c02160611070b0a11060c07020a14040f090b01050f1909020912010e03090f06030402130c0201090f060501 70
    0x50a00c66440c80c01c241100c10407030b0341c900e0000203100680703604185074213403084000b2441400c010001103040e041e4200007955148400402035441e00d00c0810001130f400b201d40004541c041a581d90f40801201d038416040c00c01c000000500c030050710711000c80300800b880c0300043d84801c005201c00e5019020300c007107030b558460b06400014215075964010004540000300b225488600c000780c4001100c205290012011002c40302207403d04229500010072540002019400c25420042c0000e0001d6600c01352669582c401c6000cc00728416014020b5000345182020700841200c0b42c68840702c0d1034003134400203141c4074141c0604122074000c2820b0303d103000001d00421403072070700001100c24560103451886107004802481c0c2940d18a40c0151515281c0115580c901a12044d10300d0902c0c1c401600240100c8610032455506c0c0d80c00002c40c180070b071030050904206401c014049900403071b806000a603ca07840d80c0c03051401494940c002c10304554032201c0c0440820500184266290b008000000310b551 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819395854 1250 819394604 819394607
    0xf060201060e0610022d010e070e0916092007030309020307090b130504050f071d0a05070e0f01031107060203250504060e0109051e0405060619030b042703 68
    0x240010000791250450403094031101e5404155040d24907001c8541b10713540c00502800c0c0c050b5885184140034117610f40707441d01c0354601c00015904200c0e0910384410811307071200d408850701c800d40a4195240b514094000308200060b030340c0030524035a0703841c00400000d00a001c0ca540a58401074042d030010791204002801d510f01407000100038002c4040800030340f00c240700459903001c0c0e0006034030f060030b90b100e0020301403280c1403026011840e01e07401a189180d0700c48070303184840e906034140e803602110b61400040c1a00e03080c4c441c59000d1009521610560b0404804000d148864510725a04042d1204800040f0b038142c1c001601c041f911901c1c1c0941c40f45000342f030030b0007031040007581d030303208043c2281b0b01e2503d0b02e40100850b425569035241001e02000b0030001600c3c03815a6034403a6810462031a0480303004841c02c1060b03200210101c805000540391541003207802e026403141030008818800340c400005000ba44200300c1c400e40900042002c80224100c40842202c00c4421050f141401d0207200806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819397104 1250 819395854 819395879
    0x501091a04020310031704050a0b0d060812030c0304260a110c010c08030a02040302032b020d09210f03020a0201090906150507050307350f03130c0f06020106 69
    0x3204241c40031400d41c034000b4900307001c4440324440a00780740a6424a90300c07a50b107000488000d020082d02e1003100c0c55407441c0d04001640082035103d51030340780030780101c0c03401004030b4002030341444400c00328255202c54010343c41a41c4050b0003103a829401c14510111949100c565000c120030040400740c030345414401c0580b05a4012014008540201190325440d80c2c10190131240700d03412410f940c0e266601d01711480c00030320454001035030504c580c01800f00440b00300c0030101030500040440b044410903040041c3d03542c05c442041c00e00410500041440390b512410ac20340b49041c00d0608040d100d1106481b4400c0608107080d0560044e00500d0308e100a550308092510010041c05500700001480c000380e4140c030f0203000b00001c00b000340000d540001e00c14200700740c6000981060b8609000850706280129124540344a049110b980c0010450170040300b0081e80c1c5000b0071042e201c0e02d10742d18403a43d2030214001c0b00040f5070f20b07029001c1c04201d8042d131500900113441c56070000a904d6061a0300000c1c80c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819398354 1250 819397104 819397151
    0x8010c08010e0705070321020d060b0a1205090c0d0c03060b06130b36102115030c03050610120f12051c091101020a050d080403020a06050109 62
    0x91196800c010445680c2028007140d00a90603d080d9807a01380b40c0c03404940e900e4080300c1040c1c0c0a6246000e000c4412101d82c0142410303102c00d0020400700355a120542c400b40502c04082d03011510b07a40c0da07242216103c1e0001030b402800441070310700384035a41001510910344001c05481c0004144000e204104091045003001d801c2100c3c0c1c6803e00510321040990203216000d0080707aa24081b901d01c0007010410031404c680d0482000202ea031564a1b03410100d140c9428442912131420311a040c0c0070240500500030340340200e64550310b1a1182030600c0c1e0f002d40940030f54151814030401000001c2480300714050050351294010b003026081654030030a101c0305640040200d140405041000038401350743e6155102c0d8412500b518401480f4400d644602849119003810ba00004401e00017204941c41613903214810403101043c00d900c0001282c2da2000030f540180940d002c480e2505256000c1c0d00c0c1ea030307441440382c411219215840d13660071080d20000e034411134100380c40702c16099118241200c0703800d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819399604 1250 819398354 819398357
    0x6020909070e03061f17010e0610120b0c0705010e0a0b01050109180506220b18010803030c030a09051b03060a050903042d060e1f020312070e1908010c 66
    0x20150034000011341c980710041d0441d500f1500b8031045c0c03001c4041c0e1400c03d400074041c1506100d144140140380601810a40e03160025502481002034280d8880c0980041070304c00c05600513580c9205aa242c0c0022400130740f1006041100b8001440011801d00880f071608a81c41c0141070307007600c1444d02d0b006030101038104505100988009100141443d114400340012041c000f05040d1951030206149245c00403610740b850713914140d10505031040750088003d070102620401001480d072161102001828045c1508035041000401e06944860000e107400100c20341c0c00158004c102e542c0c0c18174040c04a4a5240318542c62021103070b00e0319050110682c055520f000603c03043c6001c0b00000e80b248128014070140055213104130300309041d06259000031018110405806549540015107010040170341a442521030480c40030b0080d0403c92103480300805600210f007480f40000d000c006566005004401304803030744561509950711301c01000c07aa0348100540083c4642070504107030946801408150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819400854 1250 819399604 819399617
    0x703271401090b0310030b091906050406090203121905072003030f0304050c090108010221071101050c030a1104140d17030f0105011107030c120503070c230d03021e16030602090907 79
    0x403525101000110b803a480ad00c0029543c1d658985880201107050000c1d416104802e08400382d03078214402810310a107040d1850310003407241d000850300c1c0e00c03e07124002c0650f020f041c800c03c4044000b0300c3c10883e1000090a80c2d0500310290f03e2128203400844090f04c09034004413041da824203000114501610881000b545070040e401003c600041506010b1000d168014000400c02031058410140301344c1c84800a00a5041080084046410a5a001c90740c1032170000805171070850441218104d407084210750300c0e5030b0141020001d030107080340c1e001d6481c03085a10f01841101003242c0154410b4104a016003095410f100004010401b8200248405d82c044441440031901803034103882104c0244800130500c54a500d8500d045001c2d40398000c19001303400c50041010700b100c3c0e101c56601c40c4010290341c2290701e203000300b2079880400400035025820281c0710b9068810501010441c01c41e210b803c03528842d03100060380312a40c1c040c2c1e20517103206602240700111860f10b01d80060700b0181d03601d42071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819402104 1250 819400854 819400873
    0x207110a14090402221505010801030201080721020f0703020606040b0a1202040b040e1e0109030f050901111c03050f16081e0c0703271401090b0310030b09 68
    0x100c207801d07401040544254418400901156119810000d0001c000146000420440700e4044003400c00c010008541040c1e80d6800305040d40b00c0c1c5c02c0c050403607070165241c07407641e00d8075072054919156090a006a280c040b0318a8051080640000c221500c007450300160b0b2010030741402030034000007501d95132166050100a0413259a01090201074401802000e000d0041d103100040051400103c03d58200b03003802d0221100e0300001c5402000042121140080b03080b1501200b0308840c116100240801c6440804802d003500c104060100c598040c108481421400d40c0d40e10b241460480e004030203880d03101582450558580201d80c0c000b02c1001c00684681441e1850341680540c141c1c22908104080d030000d4803282d4680130b41c0380100c03500089101c203030903d00143d9000380d00000050700401d0a0225102c0d05140305415040100d07060790030103a0040c20f0410b01a40e900a404186041140b00207011032425280f80007980501808074000c5189803640c90240340c4504010a41070440d0081d10341e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819403354 1250 819402104 819402119
    0x100803091207031401090b0f071b050c18090708030414100504030f030815010e030a0201211d120a0c0303021b0a2f01050702130204180207110a 63
    0x29104035520031920340d40807603140c1e06140d1404040d940040d0007816104844070440c1c0040d4480ca0a46000d0304000d0032581d00d0121140d06058252850380c0040c608060341039080f00220034190b005881501541c02c136020311400100000d43c0d00c42c1020300040c800090001d0240c04201840090450030007031400c091800c440c03c2403041c0308020300340c0102d8007c000e1041d5588548102c40c05150b0088012540d2070320390500400c10b40c07003142c03400c20310b000b4a0f2810101d503000c0c1c135a03050394900007030003007444ca9620790044602c1c0c464058404076010071042d0461a20f02240240380c8070303401054401e042e60b0952084145004010201240e000404218800c140c0380d121040507142d03030701750030050780e1020b080c01c152035010700c00704200e5060b000303803c00b6070200300d160002007205901010b0558200010b24072302c010312520b20481e40b80803601c00c02c03480c001810a82d00c2041c004030100c0005080582d1052090344800c4042807154030356034002540c004008180301c4a02d50100141c40c0601241d0030540d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819404604 1250 819403354 819403357
    0xf21200f12030901110403060c0207090b0f1509030d0e0a05010306060504060810030c15090b09180901060317191d0d1b180b030a020f01110109050d050d05100803 71
    0xc4514081c800000041408034250031441009071100c00340755660703a5906042d030050105400740c00050042840002e0348189602444020b40300091650134040302103010044850741790440710001074000c0c4540022540e0074040d8442250319521a542610b61140c2001105907864000505140ca0143c0138040c480e4014103076001d48015080c504010b407580d09900c0707060b14203584014009500c1c2800403c040881100404000415448140c2c030181c8600d0007040310f000b9807000300d42000e0906960000c07030442104003a000012000006201610f94860b41140f050b01444417108036000218020082c690160802501340c181c600384481c00061030508044005070440c0ea8850040d5150000c10b0219015410800803104420112176558030b5100c040100100384031001280d1500800502d42d00300402d581c01c000d94020b02d4052640000001920070120000f00e1013295940d4908a600140d00bc2107035030f00d0850107880b4603883d0644200c4143c1507800080c0042000d240f1f084080196810000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819405854 1250 819404604 819404623
    0xb030f0619030b070504090b031b04021c0608070528050105091f030606110604260717121e01050103020c030903070b0703021c08040f21200f 62
    0x250712191034144a075903110911425000601030300d0703001041c055101e82040c010011101c40c60020f001d8044030b030003016114005040d4070350504500c0a1552013529081c2c0c01004000043c0446001955009800601720b5143d90001101644443c00901031407400071610030b01c0301004d01e0a1081c40b4010700e594400d80f9068415241071250201d41138200350744447c1d1618941e41c100509070005050700c02d00501500d118070031200403da4642c0240c00e44140030481c184610f80040c0c40444140e42c450149a4460440741002174004d020b104000000308611484071f003004075081060780341ca00c0c042010030898005080034014104484039000443d800b018001d04503942403d005881c0e56601c587c60b41148103442d49240e02d8042c0d25004580c0e80e218001400d0050302039400c5130055006d0410710380030003030084100c00100d001341c0c00050008410f60103868010740b1407072084030407c080d80d03011144402100044800308001c00403543d084c038028907038100141481c800130030081185c4081c803920f03180c000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819407104 1250 819405854 819405859
    0xb040f030501141b030a0225030f0906021209010504080304180b09010312200f150a021201030f020f0402030c03091b0d03260c0703110102030c0a0e0d150f05010b030f06 74
    0x480055030b015031b280c2c159081c0d01c1c200c0c00381c0207601e80f02181256032100340500440c04548284000103400c2c2c4144041400e42c1d107107400416501c0143d200d01441c903041102100d041110400002c101c0d48424405400101342c01090402d50081c0320305081c0582e802000d0340d0703005801100040010604c001a20a0920440d0801d00d07800e818050b544024a040c002c0644034a101d0150ba0302d15440c000100000d01800290800c00c1c16220074004006078403a0011034004080d421005101045140e6400c480d82c910051070100d4804a4401190a90700100d50b04805444040100031007410180119001c00d40302004401e2074075a075000141c112403110718064100414046180c002418480120f41f05c1d10f060110408545820704c0700c02211b61000e40c040300007910040c0b5100d804801402030301c0c000d03c4c1510350641030010390b403c2200c2e10301c081015280d00294042c1c01070040340c3d859900d8210f01c080b140021840c448041162001e44a040c0d2000c0d9120f4400c108100d400c0c68440b2030640c021104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819408354 1250 819407104 819407107
    0x11010c080f0406151401030e010204030f0201110109050129120712060b0603010b071e0305030a090809040f0b19030f29090d2715090b040f030501141b 66
    0x2ca0800100400c05100540c2c8601d01000d0b000c10780e00704a00c03140070041c100b42e9003030101d03140c910562402c0c0c0c02a0b02c401014a03090b04039010040d0700903128140b49404200000030395000584030b503801c1d100d01812002d442d1207101760f042481010380e1610f0118020a6410355100218448442d6480c40d1900c514070f1250a181c10110400010341c2100c101d5907401803030240c5075611492a45101d90040344103ca04030244211000c10500d13050858000311340646034079003145c1c0d0710200e07d405054000400c44820304c2c10080b40d40d640d81e9512a8080b0a0380940b0001000c40e0f20000340a503602030b040701008031010b00001003001484800501c648698868546440b40850202e0b0031114002d448440301061080005c1201103030002980b0009075510303507a45100703002e034460480c01441100c03450f001945400401802820812a4036a01c1c80c2d00d02d250840c60b05548952100160700300b0317000380314089410711082040c85000d001d000040144009000c0c070905150290b00c401e44900e803c1060100790 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819409604 1250 819408354 819408361
    0x1b090612100f0e0f010b010801150c021c1a072a1716060f060b040302010e040e16090905010608300403140606011101020a0e0409050a0606031211010c080f 68
    0x15039030040200f0803541c00803198031281994a00d8041d040c003541c0c103400100c018000141441003004400422111a103806107943c0c0b85400b4409540303c0440b64964060740301030028000340c5800c641e03e0b8100c203800807480550615803001000380f03550766001c00413850f5411580050450a88021046a900507200101809282410041401111000380040c11520000402d0000700e410003011112850020420a51102512403041c007580c0006400910001c03529070f42410a40c0c80082c000340ca810803541c0b000d0800000740100b0b2840e03000030180a440b4201002001000d01605c8017070542c40c03019000c0d01030011203120603250b002ca020242c44142c4038580703841c58030000881d0051600840c441607050190b00c03610342c0d168000d503045800600721f007a460404240c18800d07a00c101080f540e801500c01d082c0b00070000602045081a100742c01068002c2000446e14030441c0011442100248800c410445021740511031007032500741c00ea41001c03a0307045000e038007407400d41c2e1080050092880944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819410854 1250 819409604 819409631
    0x60a091404060b0c030310092d060f08100e0c06090d060b04050a1a0a0e0a0c020f161e050307060f020c040c05090406060513091d1b09061210 62
    0x440780e020443c180c9002030480300000012000710311605002d00f280d06810354412101c82141d00c58050240411008503480d248002c58110084a003100c0207808180240c586079001e00358071080e404440c5503840115042190600350151000c0c0c24a42406001100c0c02c0743c2c0031540c136104c0c1580062242910f003e00d01c0070030441380c1c403101c210744010308108024541003800c600200188946495020a0300c500803241d441d0007603480c020b54181d4400c600d000d884007035400c800b80c8000c110081c19030294140026541030308201c220508507840e0203c001040c40e10103980c0c64a0300e880070480350307030017001010b0010342c40025002d0704503040341c940710001c01030001049007040c000d00f0b102079000d41040010505254000302812503800200c404200950340c2e410203440e507119400011021290740e07041080141c9482d0b004941c03028480259940405a5030176150410542c40c2c062800d141304404000005c0c2005455030f94048803c0c1c5000311000031020415903200080409054056102c04a01c080003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819412104 1250 819410854 819410861
    0x150e1008070b120402010912050a0b09030a020c01120609020d091115190c08120f0703090309090906090b0c0c07050105121b09030d11060a0903080f04030e0d03050c010b060a091404 79
    0x403d01e03a041100c844885140042c2c62b81405101541c08090f40d40206048141c00310444800301c0283d002007007100183c03001035840400700b8400c088080c0d9140303000103900e0b6a6000030a00510004000200080e003407904502c12140360101c1030003030f424103000501603000c01048540b4810100382903120b013080800201d07445141c100e00242141c0012030318083c0004003861807030050007440050809940d80350400c82c221298004003400040400004109681c01e0768030144a0074081c1402203110207803034680000c0f040c401e45400d502c80d540001c226110303203814400d0601516003480c240d49009981c0f11601d242e1038014000644d5000584480b205990002040742d0742010060709441c07c1e10400740d0040e00d40b074a00c03d0010b00b00c0c000d8000060120704144242128a40e0644500666440f400881c207403901006100318107111040211008503a110b40494940e54801c2c1da031140c0d07076995058000e094a4007a0307085401040c05000b0503807042d41101149082d00c0106078250304018803140041d000d13 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819413354 1250 819412104 819412109
    0x9130f0219050c010506030607050403080318060414060903030403200106090f0209030105060d020a0303081b070c050127060f17040c0806012306030a150e1008070b1204020109 77
    0x700000c044030018140c01402421000f580c03035000b0040703a540e41c0145030701c90000300c61800000b0300c10001030000901c49006960400005090a460311070742c010090714110080e034090b240540558601500d45104002d4140e200d459000910b0440c01d00d65405404401418035000c2d40101c10204102200025404980101081c02051140456143c00d4030300035448950310070f01079402e240c0016001c1c141114a00e124541c06010b140b0650301e191811210098081c12000409050074071078400710000034080e20000d400385241c003401518002c0003624140c104402801461121518000300c201078000c2c1c8422140c5505105e085807001d8042214040c0b003804c124644040050305010500141d503031101c06031940d00b0300702e85450340c0360321f0401e403803142c0c1c2e15401c206020640001030301402c000010b160001c100b90400701e4500c42e901407846c1ca400c41e0340c00001c001ca40c00d40c100034503061811894001040480060f00040d42400c0c0c502045200b100c981d060403545440c00314086911031030510f0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819414604 1250 819413354 819413377
    0x40f270c0806030f06010506030408031012030306090c0c111203040504060b070c0e0c03150d02090f070f0507020303070809010c080415030b042c01020d0c02030d060b09130f02 77
    0x1080e51800006040e070720050b60342c81e000b407081c200080325104000500f40d06072080105000d0031aa1796980d0084a41d00c0280700f0040010703d80c000080312261129a009280d03c81d4501191040c00c006801c011108000303031840800c07540411a0000c100000e041c1c003a402c2d41907440344854101001c0d05803a52107181d102c0c542080c9030801c00549802d4400181c01d2040c400e003121341542c0e070381c1e01e00700e05070840580303001c65131a070100040b0300198202c481d0940e40d0741e400f62001e00022000d80000300c011303030200c030585401c5c04840f0421481d180e02910060300e491490030151f007070581a0300807907541e0150318001040504009840021a8015802d508810b40e1010280da40d85031a2040c0502e104400c2401f4001f0906013030000e40c0c1d038034140c09150340c11248401c61400480e0b1200089419640087c0440e00b1b95508002001701e10031903000340c0c0803012840e0011940ea80d810003549081f56131560154050303d5051140c0d80d00c650314040089110200040d02042c0c04601c01a000024442c00140c0304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819415854 1250 819414604 819414611
    0x111b03090a03050109020a051801141c0303050601031104062001020412240b060703030c0c0510061d07021504030203190c0b1015200708031905040f27 66
    0x8200f16054001e9031840344241c0b4200503030b56440c1c0034401c84600161000401b890710364014801c251400a0000c0c0b8006c00501c441c0c0f0725060b1400340e040c080b07286d0760b0540c00039444400f0800c0558040c041c007000301c1140045645840e141ca2001840c0400c004a101da101c0c001211040e031202003501582d015248410b19032607414000c1c40d0107029103030014940b1407101e11305650032050009602c0b8843e8490006000346103860ba107a60704034010318a1440b0b19042c4003a8040c4440070520410089050070781c1c3c4040002c0d05810030000c071046442160000d5094150441041410360340072031080c114426640c000c4038242c5540c50140d0640c000d4001c4a1854000d410640c00201c0e8030140c4d6455080c0a9001404291940b20a6420705540780c0074140010300301c14090112a442000b00c90000d6074410b840030703500d200c2c3c80f0100d820309203154040c0840760300c00b241d080c0d9144c81d0320400d90504d400c10f062803440d041c070300711410798a08158464010158030714503684541102039050088842524042003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819417104 1250 819415854 819415859
    0x9050a150207150509070504020d2c010e060c191e0206010f09021305130209040504140c01050a09053001050412050a081b0f0301150e04111b03090a 65
    0x34009400c424019a4010440114a020f054080c80381c00c1c081c914840140000c1401c040600020b0751110426a460076a80c140c02010b40c032501207020005000200b2a80d42d140c0301c0310007542034070054440005079070440400e100c8500007180481d01646a820611009400014016500d5441c90040380032604800e003e40c0e100380d540416541d050b10000c2218460803a141c402d00c00480c0690001800c181440700300c1405145402c08035000c5e2858500400761800742480007113000d5880549080351040200107007000c0000c002e01076001a14000e10340301e400c0c0050003400a0001c801881083d00441c001040c1200910304402c03c2c08400e07400140c1604090301d01e004c0380e4000c5c081240c040d1007001049400501080c411801c6031601c1c10a035803482419101c0001401d08020041228030081404204100c0078000d540040e5000b8a006040400171031200034000c2c0000090180b0b407440365181031000b82180e01400d080d900040a0000381110405a509005107980f1400005942c021800c9100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819418354 1250 819417104 819417143
    0x1b03040b130603050c0c1b0f060c0f071a030c0a12021209070e01081509070e0907090608010216060507090512030406090b09100f12020f07050f0c09070309050a 70
    0x1420119902c07a6010003480d80d0781e000c2c0c44110f0003080e82000c415009100da806ca5540d81c42c04220070000000c002c00c0c02c0032070680004075140d0200804c81c0d0309411500190301c0001090010714000d10101180340051500343e01703024858030004101c00040c40c000700311040c19030312842d4010b00c0500300400c115540d18200803602200c4004407000c040c07510a005000c90404d44510105048500301002041030006030f410704100355138010700c070b000d00b0b00c01d801c000916081301540e054001d401e4003005d0403420342801d4145043d03038070310303004614207038010000110400758404004100c6a0004000101903c0741d40e07017140e007005a0f5000640c04502e0035814040b11030040014811a246610350500031030743c5051415040c00703040311459000100c1d00e03080551358010a62250700380081c0c9420403003404910501400ca800c00c1202c100c0911000c100c100130000104450000c0ca03490720700510b0859848400207416000041c00042055290000001000740400c18145070681c0042c2d1600101500c208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819419604 1250 819418354 819418387
    0x80a14040c1419050d080f040902222909040e06150109030b15030a12020304030201030e0f21040b03010909020f0d030e090c0408010f061e0501051b03040b 68
    0x1110341450b11030340c41d10800c2c41c0c009a200000304400980720780031490441084040700c000c0500359020b0703104104940a215001c00200f0190548043c0181c07210303007245103a410600c01c2c011050542180e00760511034043c10034014050001c10042c1d50f03130344e00d40400802c441401007410b1980c0050409144072608100824610300c01d00c0f00640b801d52200d0068011a4080d0341c4e0320000d00031661000124410401482d580000c055000e0212189000f69540303e4001e42b958055150050300081028411980d0500500b24011208801000c82c0072005200d552101c7c80341183c030b0502c2d207186038a5a00140110250340041ca1001c03070340d6490750b0350f42540c0000342207040000c91050a89060410700361814a44005025405540b0349032080085d400f4481390141c06070480f01c1059080c440000c035000c017406030a40b61350720864003054140c40d204031072840c5040c6030b80c1d03c44c43c0085030005001a036400400d4072003040c45014024807000d014810b250a61003150080c030109400002c0000240ca00d03200f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819420854 1250 819419604 819419609
    0x3180619080f070513140d05030705010506100c08090f01031104030606091b050412020a0e011701050a050c090d0c0b04060504031104180201033c1a01020d080a14040c 73
    0x800c2d50b10b07140d483d0300d8121118030030031200c01e00a01c2005428000300b480882842000381001c0c0486070300e0025074480c5450340d00a10742c211280e81d103d408000c040d04245254000c01412414005034803015640c516090b0f000b400806400b500c801d21600b60300c1c0e0b00ca5005820361201240c0415540d07603c90500030060a041d00415102c1070400d40c00b5140c60300850001e0101d0342065a502c0c0c101814122240841160000183da001030f12040c00320301c0d0010309481c24002d01880b0182c41440044030b10050940c0c0b0010b24440c406494281005a0b0000090807a40ca11104968645d20200a85000c8258184a80000340060000300340462002d0700030703000300107680c05080c180326011142030422040c0c0391412141c48540701c040044a0041d4001e03002030014403111000500b042e402075000481342d49109140b11882110410340c5001c1005a110b4403060480c002c0c6000204c49569001035903c400204200303041040078000a94084c80d507511402d0250314514868180c0c0c186410000108102c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819422104 1250 819420854 819420871
    0x304081608030313060605031209042f0918150a09020705070b1810020105061905100818011a130203060d110a0b030406090605090303090318061908 65
    0x11100103280d840c03194003401103840510045256a9401e841204201d03c00c0320308449280c1c944c00d01240a0307405000001c04102d0114009032110b10940411059a50204040020019202e045d000054003200c0b640304401d407640300c1d80d9580b8620f50100310109106880c62041000c8038080c008442c50f911416501000200e4500c40c0d00f5440d0f0050500f01d1140b20f400601b070ba8441982080211030000142035074030b00303040c82502d034200c400300880d11922280d214040140d40d51020817a0701d103018004c030002c02185003100f001160405c00480d4a1644000300c03130041c001c404d0002559074414203080d030b00709103140bc000e006403811031991802821410704007034131a4441180580c05c142d0302e03200b82c030311444000b003265040160944440d5803448000c081d060700a0900c0c603010070140103a80c029070180c2d20858000030b00f0000d90811500b15040588040010782082040c480447d90000540e40020207501c4050100b54080c00001c10f24030660391121400c00c4e15a0340010510f40013203441744121503d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819423354 1250 819422104 819422113
    0x213050903090306130212031305090421030f0501080106050d060216120c0209010b0f030403110304051915032003063d03020a0906180f031b0806040b010303080603100608030408 78
    0x105403c2c240c6074050301810b085c62740403900c02007003e0b240400109400038020b03620034140700741c1d10070742e21880c807074400506011944442801c0280c505510401c0e00400c8114001c002447c1082d00141e82010101d501415007078020800720103140c2d000d000310640f6644a05c4000704070b12100f0740648084910082070b48500e603440000103442900341c00700c4419094401000e4038580e036540d800e9842d142500c2d0314030312510090102240e0390322848800a604684214140c01e01890040f1042c140507101e40c04004140c2012001c01c185810041c100031107003200724416407282c3d5440080f03902402c075104a000040d0440e000640d034a28401078100300e42c0030032178601e0249240003505905a2084100440014055090400801d4420910010014054840d440c007581d075441081551547c0e607002500c554220b918148106504608001c2c02400c1c01005401070b8649515500d0310600144000780c00d014507000040c1695800b4070006600013540395080100302d4442241650f20780180c050f860040c0728 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819424460 1106 819423354 819423379
    0x150a09020f0d33060f080303131110030b1206010e0105040213050a082a010914030316050115051807030c0210020d0c120902130509030903061302 64
    0x580c0e05041000f50601424a021541d03240e200081c04140e10f9010094030802201380c80c1d0020a401d05410141e0041c104a08a4100924039546c09881000500c800b00c0c0c0640c0000c3c0030307600550320410515400e058540e50340e082805074658402c02c450041140d0314194004200b10610480742c140b0281c0e07144085940d040c0071741c1082125130402c00c0c805036002c1885900354182c08181c40902001c0c1403000000e4402060750103400742000d400b494003009034408104480002e80c1002c800070a405a0342007a50003483c00d6103400549114a4000107114a41003a600c00d6440001580441a031110030098005104410145040d0f0003140089a2803d65604c05400c00c0d40c0d85000200301c030966150020809901d0705c8074001c441d45800c070070002507190918003040ba006030210009250725405801c03460350041c000701507403600c514810003c401403100c001c0150b80740f080d03610440904 = true := by decide +kernel

theorem cover : BRFrame.Cov 819244604 819424460 := by
  have h0 := BRFrame.cov_init 819244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819244604 ≤ n) (h2 : n < 819424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
