-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:41.335379+00:00
-- url     : https://prove2.me/submissions/fe5ee28f-4704-4900-8e0f-9ae0c5ec92cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 563489208 ≤ n < 563669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 563490458 1250 563489208 563489237
    0x13020325080d0f030c030609020d0b1302130302090c0f0406080105101d1302090618090903070c12031214070e0402190c0c080d0206040b06040b0f06030901060b0409060501 75
    0x101c1d050105600e0010f020318014160551095100c00b504d015540303030205846990384410b40a0f604000d0494101c40c0d40caa0302c0c0302042c81c1c4074407660030102186a0a5051020722185c03420300096a21003c1d0291040e400010680844001103442c0c0b40780b041030b0592541d48650000700350310402d0080350700801d0b08150b0f103072070b00340a4170281104081c0f15545101b4688070300180800000400480b42800d6020b1000d20034179038402c4041c00071001d1072404400c1001d00e034070820070f01940180c40b12a45400400c608408140c0140364581507c40380142c04a00c2d40c0c8501d8101d1350036104c19420b0340341c50324021211203081c0c0c120710b07554000c072203030382c1c0368013280c50000700300402c03440f60a1000c0d8408903c1d02000064034000c690b81e00c4094000c800d0140c403695900348241c1000712101c03c4e10016003100c010001004054805a50841c1302070700c2c100b08100c1800c002c5004400d924004c20700c070341800f00025001e003509401040140560500d040d03100ea0382c03030700414040d1031540506404105140301c041c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 563491708 1250 563490458 563490463
    0x9050607050d0f030b0d050f070608090d030507140d050105130c02191a010b070c090b06030402090411032e0e060411060d092003010e0d081302032508 66
    0x5207801c00040d00342222001c1c4140c41d09041d0580c8201131540312a5114801d540b880003003800d49000e400034103903001c01618100d0070001c003504070409011140c0d05204914130002252000d24103d410001420384401200b6102001000c0024501c010006000070f040841c94004a04072507069581410403e10f03680f89905581d00102d01000503488000080700610805c400354003a580202d0414031403c0c490020180341c500c00340c02c506a0301c41c002558604009104444100a00d0320910030016882039070001501d41c440a000070b44144480b901040601c07449440c00c2c02e039014000c00f1030304190101c0d5107114060211174104500c070034159692940403151406401c0e9580010000740c0300a50320b44d6902a00482c082484680180083c001020710780c0c224414801d6240c0940460b0091000b0360307400c5004070940c40c010310f01a0f41080800100f41c080080c44044000c03580c103000c080f690b200b06105100c2c8402400295151042c150075041030303811503007074465000340c00240e03544d542d440b0409640d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 563492958 1250 563491708 563491717
    0x7060515101b03140412081206030106030f020f01030f0507022415010c030306030b0f0108011b2001140403113a030e0106080c0351040602040303090506 67
    0x8011104800c9400c0010384100a140410b0070000c042c85e0600341c80d11407010899940000803601110001003003140011405101507118070100c009010060859030303140315841c020000280182a10344240c0900c2e8000d8008190541122000300034a1510700402035640c4000c2403e08001d42c060724240744810b2241e00054814001e941e841e400b00764551004440450f81d0001c160101541c0d1600480080c20030ba24080c014291400d020705154103040750030b42190b80d51741001040f282001441d40c045500145034148010307400920141d0001422000b60151510300c0c2015a0420307034408002c201754100c1600344040340840f045425005030010340b441c020003000f130341201c5842c80d002e100c0c1101e07015004c0050321005d64070b000304d0b400e0714a8040c1c3d400d550540e006407c95801902e240821420200180038400e0414032010701210160300040801503440402d84044455070581c280303114038012a0400c0c003642582850a540c60241005802908540000c600050500c0320010740c500e0650207a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 563494208 1250 563492958 563492987
    0x50a0e0613031106070f050d120504030206010b090a090501030b010e060d1110033207020316060b01020c031b0a05040c0503240607031707080106230706051510 70
    0xc604030782591240e00030031105030300300c941c8400300304170f00c9002031610842910014410401400b40704888200601514500d042c0a10201e203040104008268009540e038110b4110105e190b40c0d405560b80400d0144d02c2c03e4000390540390a1000010400511b00d86190482c0e02c60b1780150b4881e00c5000400c14010200300d009401c141244018035802d1030240b405540303034030150034001000c5000c4502c1c04000400b142c00118081456880d14085900011403e903001d12540b019500d0405c1d40000b2001000700201d0240c0a84d64400c0c007844a80d008100f503850a01000301207851003c040e40d5a1441e6030280c0d103e0a02810b04074038002498281f40c001c11112114036103d103800c1d681c4500491040c0b0841801c041c2195201d00c0280f03440d5101c0a0013040014082c0e0303284900c00c0280f543c0745c4500c0c1400703030641c4104420700c001086030b50345c000b145004441300180500170400913149401a1406040d0f0041d09017850030b018000040b09000d45e1458502003501c1951542c2c0300110155480c001c285c2c1300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 563495458 1250 563494208 563494237
    0xc040c120b150730020a02191a210f010614040b0322060609020d0b18060111030c010609061409010f140105040801020a0203070c0e0c2710050a0e06 65
    0x24030000402040d0102074205100364500350710704c840d800d80498035001860319405030300040c1d5103109508241c6030f1100750340741d1480e4100002d4503080c100107201c020308d0340a40107140c01141c051070190700c1c0341a40c42500c65031542c8100714113106403811106003003031060801080d0400c80002d1820710910a4038100d800024a0780d00356a9009000103900c83c441040c455041c204042c2c0300c0000700c441c0701d01d0010700203441006884030383e482003000880701e41410f03d61107241044203980c0f0a10540e410164004803c0c81c002081046c40782800c0e265002d20900e40c8801d50a00c280030a510109030b000b41c040340c215101c940c034400b28540901c1030710b0301c0a00440a954210f400d0500c10b21111850040c40a038043c58510f140581d034800b450708a0f0064602400180c100241010a115800c0200800341204001800c001d040c00d02100130709218482e0410150742c0e03880300c0b8000c8024499010154808050078507520320b000e1400040895001070310240c0072030030314954020746050440c00d80c2d03698a2a91007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 563496708 1250 563495458 563495467
    0xa0e010f090b06130602010f1a0310020c030d111e181c0f0b10061e080a061203020105010e070e030c090c1303080a0f0503090d080403020c040c120b15 66
    0xd0307001d41000c10409800060810590f031041403042e407008010105e59000103a141c0e038604100041c0c92203007141c0c0c0c01c0d003454903a0308103959601140305c00c8296030300400140d883e445442081c1c114002d44404100c02440c0c410181907000d000c00c000c000c101003200070614040746600c200e500b24042e0064441c01c46941600118030f134100503e0361411180c081d041d40504078801c0da07400c05020032900b42210b20342403900c140710340007400c2e00f020310150409092501d03034410010502e90a4940c60754220b0100116540031443e1054250f1202d0041e001600142c40c030b416480c00e01070301802082c8140300d440c4200c040014501442408002200c481c004c0151085c2d1420008000d01c130100034105020f81c0340100300007451039844400c840004c0d445a840130f40c49425a0b0360241c00d2a28480305002880010020403990f014041034807030190704c00e41801d1200d51074a080032403078030b01c189283c5070f000703460a40c4100f81150496a12003102c1a280014807800418809004a004050b003002c12651000d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 563497958 1250 563496708 563496719
    0xe0d2402072a08030412140c01050f030a02120708060f04110715020909011502060c07112202130314071d070201092f090c030105130b03030c0c0a0e010f 67
    0x7801c07201c090b45100d9440340c1c2511218000e04552050b4400d000c540c420644120403c18003c003480010381c1030300081c00c01c003090400040c005100d1a20031040c1d2800000c00545007607000d6061780d00100e02d820155006c2d2074448806072410800340c4e501403052000c86024812444c103800b4904c0b1000c000205e40f0b00302410b40c0d540001414492103540c8d8066003d00114019440c0d4420346402001c00900b0342c21003c2940101078285a000744c00e868561804000610200e910b8140a001410b019078030130080d03800230405401100000f10080313903000d00005a6044800c44401201c0c16a401602101c0c2e280316803051091384c41c1410300c40c24854035a58540050411182d091082d170241c1107000110f1070705d00e00e0780ca070078125005c110a2141030001000c0103008001031884c025200d075050380e0607061360511024040690005200b000d228024001da04001e00c00260007044041a0241c2129190341422402544541c20380300e015000702c140c0c20700041c02e49015a0b62504940b01060301004560922 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 563499208 1250 563497958 563498003
    0x140402030c012d0c0311060903030c070807020a0b040812030f0a20161421181203071403070f0609081b100c020a11100e0d240207 57
    0x200c150400f25440c5102c003101e0b118507000200e030141c84603695448401030900d400741ca000041d0b81000110351015003000701441d0b002082743e030003000401005441d081c0700e290619292040c0c1d400250031501d10030300001c140f0802ca01800a507202802910768040c68108040c455000c1215080301c0f001c5004003140c6010500d070302c500b6009081600c40c28404a0458501109a2201e9280000161401d0101c0180040f000b9000321061041028002651074424680c0c0b82138100c0c000c142c80b03500c0011b52181007c490f1106019000000b40c4410b205100071000251282c0100c441542c0300c4940a664045206001c0b040b14044c3d5072160b00140300003030544900c0010030a0403004c4418400c10400711106c41d05000305c07500301d1040c400041480917280c50401003130b01c000358070040556100d500741c200081c45002c80170098207026603201c0d00340071181c0030445108151040311604040c0b00b174101000e1000380b1000481c140c004134160045414410341c03002c120f2091040c054880c01e04036255062818a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 563500458 1250 563499208 563499227
    0x1e0203030405150901090509070f1d040905010207050c0d1716020402030412020f120711030304090207030512010509010e130f060203100f0504020f030613061215140402030c01 77
    0x601101c1c18903480308041440001031500001404801007904e41e480e690120741940500420b030344100c01420121800380140700d44015180610403030340010705070302200100307a03000c00400030028000d0750b2035410007a0003980460303015030303490280c60a0960141803030b01d0600750480d441004015420410781d00003400750410000c0015444e070300078413100941c2d41e90025501543c0514010003009074101c00280c40c003411040d94003881d40010720400c100105c1e4000340e8202607081a00034401c82000380020b800c510550b04000c040758404500c0c0401d069212000d4130410840712014240e42c1d80724030400015140134402c500b6645030120004004030413601041072094412001c0d91341c001050381d07688007680c00440301923028140c00002041100300b128650343c000d000551f0110301d004041d400701c0346c082c48004c045074082c003404542169403420590110008110740ca140105031803007403504200b507000c0031400c105032a003000341050440c040c01d0502402903a00a008240b030541c0c2d2001510030701e02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 563501708 1250 563500458 563500463
    0x81b1906201c060305010f0209030607020c1003090501060503030c161e0b0c191104140c1603050c030301140a0b181302120a0e011d07030201050904090629030a1e 71
    0x2103d400000004c2c0090082c80301842da40d20300961038161200038185808401400301e01198400000300c102c0c3c1d10360383c940b1034a2100925001c507182803542080381c05404281d105d15058403000802031000c036404241010b4207100380c1000100c0694036415019100c1e41440301145507130f9480c900f04140d44440e001000c850b11f1450a90303000c008110340021000c00d054206894400d00c0b840140c031980303840e226107000b4010844200c3c0d21424104890000c6010f00c40c6810858048805540180340c015803d03611146226821a40c1d02d68640c0c40303414a0307022080080380241d020803c003084d0b80f021041911749515403000480d50400d82101000400d02d9034403500d40b20f040d42080401c0d20348024002d8030713100c4e90300c001e004224003c07151085401c45030210260181583d50180c2405800b601064042c2269024a842900ca080e0000028010000407200515561601c05258900302082d001c1c40d0314007001354080008040c6903014580c03500501c0e40c00a01c00341c910b040780c40d807220080798240e01490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 563502958 1250 563501708 563501711
    0x603180f33131112150a020403030912021206040303020d0b0904031706010504121b09050c040626070c0215030c0922050c041e0b07081b1906201c 64
    0x365041c000c07500c04084076a01c070041d0b4018000b8514044c0d815082c00c3c0d0410150501182380a00c2c50710020000351281c0118072460261590200640d40d82032481c0300c0490207441620054100b03490007600a50180005076440703814040d8200113403a016441500c1250152107031000340c1d8a24035242540c8000030b00d40c3c2d040c0b040502002c0b440c842d0390050703845410700c640e100000380108c41c200c1411684a60b4090742d80c550404040007a1451103c05640480384039041110f03034107404074021903c55082c00318107980b220080003000b440e41c1d4040204202c030740c001d40740003420b000f84c03650040c00c922046038420080c01e41049054058106081020707128040c1c844640107811840c00440117450081d59002481440402c080c000c03000a80f20104202c0140500183c0462038111a01104e00a018015100c014042034101c2c00c95038890740c0740004600642035890000712000414025250700c0b00c00d4880500e4281c50108101030355030103291000d00e08420a04000b1120348403065030511901006e0480d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 563504208 1250 563502958 563502983
    0xc1104090c08100501080601060905310506120a120e03070306060914070207060207050d06090c0f090c020102090901152003040513090b04020603180f3313 68
    0x107040920100141c04a5000780c8410360741d441525080d284107030003440d561303040107004001203074206d07610310200e460503101da14100b011080b207601100813114a00e2000c000300400d815800249502c51807003160100c4a901c101c003e40d19031941d4401a2400003080c3c00c00781440c0209050044182d030810901c02421500800c0c0c80340d960742c050b43c0d100d6224480e440c0e03c81c441111550800c00066038041142d01c01409100e1600100035902e0840e442928001e980003040c803c10700016401c1a6015500204a40c0031182e690319218850f91051041e0803800e460421001d03022031041c002c440e140d490080101e1450303400d1000306601203e06105480602c0303c070840646100b000740c880060b03803c072844051922145406c0500c0810000c1a4010080515096080000480380000c041c1c0117a01600c511307803695200c031040c40c44403042c00b0801806110381105010440310000f004035110080802c20301c1c10320098070400c43c0540c01175440c0046a5039500010b9454038280640208a83c0114100c00b9803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 563505458 1250 563504208 563504213
    0xa120e0f130e0f0f0601061403011806080a0c0f0b0408030d0c0309020a0609050f040608062406040306150902190302090d02090f07021b030d0e03160605120903030103030c110409 78
    0x2c183c3d03a4810240240c10a14030070302c0c1c000b01406064010301a0741058800c40d504598001400c1c40f05010703075442e0b0321101c1c0d114001311490fa072144024210803811100c00341e40506000304a0100d0384200541510801000300b1207100e2030f4181c134110340703c90f0025401c200708050500042c02030b4141d203508042e038330440d40000da52100e520100900440d15040f6496040a00344410b10764a01400b50280f07050680808c1040c000282140d413207120b40fa494100244501c010100d15607820011a9000c200460084103202180d4042402c05100311752071030105030f89002c480e081e4050b440240c01400501a041d103102802034004115801c00140504018560380d40000c18030003080c0c3d81e52001c440002e041042c042d4040103215401031620009000d001c0003040003030f44d00c404441280d010040f0b00c0400c01c049881c00c1013110301401d0a20000c41142d500c8110043c0700380c00046401d40400031140205641400120440f81070300c1c0c050f44c0741038410000c1d4503030300f400c108003005103904140d6804e403d002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 563506708 1250 563505458 563505463
    0xb0d021c201c110d1b09090e0c03030f0405040f15051e060307080f090a05190602130605030402010909021207260c09190509072f0a120e0f130e 63
    0x10070910b100302d4240c4a9000c044c40300f08880074400b5600e110044641140e08190700003007420b0031581c4203440881c00c0301c2400051070400c8041d1401036054440442c508004100140281094600503641081000c0c1044a028251a44001d40c900e404102c482d05001c01c0c1440c985600c0c210f000302e4407050502d107100000c80d500782d00071200c401c00101c454044c00080c0201850103604008004010210042d081d1101d9032203400744c2c203034520031a030002c0700711040000540684a103010512007401280303503a02800f130030b10360040b20f00301e0000c0c0340c1c0303900410030100d684255244080460910651a542c030101961440a2a0001820301d0030307076650448440c513000549072061b10380f4000741c0e480d8007985080c03200f9100900300380094003a11200c148116120000641c0d8483c0740c030b1034120203010550100b030800302c04000d80359649240d10740c10001c141c0f1000807440c00c1c60303108030b0355032015941c000000c661001d00c01120742d0b403000d018509442c00e441e02103903841d580c00742c1d41d0000036103000b2682040d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 563507958 1250 563506708 563506721
    0x718021b070f0501081f1413090f0b130c06030f1d010606090b04120209100305060c12180c1207090c0903020f0a0501021c02070b0d021c201c 62
    0xd400c582d00c1c003041c0a2564442c2c91a80c00485098070440401004581c1142005080c06442e461200400f01e0025642c0d48683c0d540c2c4c600648001000500d416082c0240c1407110100c040d1120455031004c100c0ca10100a10021541d402040d20207040d41414000c83c00341040c103a1278541d50b41c55401000c84410300c92400c0c0c442038115000003402d035292050160540c2d000b6440125041020301041081212644400341c05550480c0d4040803581d501c010907400301030540000d040c61040c10200601c421080005000aa01007050401180c2e41c0314044003180b1007000c21440580c10040f03031200181013041c80e01c040c0c04065402e0320341082e01c0b10008030440380c04215200c0010780751074080056040c14108400030721400d8440c1804642490000303959842840b6100149880c52084180c0045c4288545030180104400407aa610070005003000130750854400c11181c110b4542900100302c0c002e10035036110141e924420410714001c1603819116812100c40e030b40300450010480241c0801a1007801d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 563509208 1250 563507958 563507969
    0x714010c110a03020a2706060509010e130509100e16120f150209040e070b03070c050703021e031501081009051f090c0603150e07170a0203010503010b01020718021b07 73
    0x6424004e111417006c044a2400c0f0f00840d0030351170028188206507000c2c04079038941070282080c2d42e40c481c507038001ca00d6031a012040a0902440d05043c02408940491000c50301c07064440180140d800d0005803d480f4400080d00c181100745e500c00800030000d09041385203600b805088030801e111940e840d0f890804100450381d07280c161b40019080d100b403074544a01020130326003200070000e00f42003d0701000300381300c00742045040c055038080c0001001001c100490265901038841c01150219168060400406940c4a03200c4d0184600c00c502282061002c58120b4405d41d0044c4000c10380102c03040011f04030004107032201d001d8101604030b07030701c08588100018a28003900040342c2142c2d04201c00117403119004001098144121001c075500c56100e400151035460542c0b00440e114100260354402080320134240520140080006480301903014604841c800e400030303c8112880c8004980f0b42100d40100100d01c04464080700c0c0c2c1c01c41580c040c00114001d02c020303080c052000740c8614682091940030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 563510458 1250 563509208 563509229
    0x9030801060207080f060109020912100603060f020702010801051009120b0912120103080d0b0301050f0a06060906140a0e280f06120e0c060412050714010c110a03020a 73
    0x420000b58104a500020724000780a0044500c99a903010313254001849151419600420300c103c0d0f603074490200c20a2506180211006080c0da03040140c040d018520040d51228600100380e00e0101c15030084440312581655210076a07800d100820401180742d1010b80d003000040500070800c00002c4c40030100850041d100f035811f518100184a103400c0305003a200d89821410b100010008101680c42070640f0303030184101da151564440f01c10000e2994901c415415070900040c0400310b41c80d12200350003500603e10601615440b010181d0700b0880501c11540000c0a030001a0002180d070000703840b01c0b01040c03402e100e00c4a41c0100140c800082c42c80039610980028100381040144c20b203040d0700500044030001c01486c07400030003410b14101c2080403008182c032030900c02e41105c0c05005000c8420001400541c40307030b40301c414441010102c00380450f00b40c0704402002c55196907414170200c240c80b05035100340010910743c0e2002c041d02d0841c40c540d03422600000d804401070756203101c581c0160405c00c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 563511708 1250 563510458 563510461
    0x20c01020a05041e06021c050f0a0f03060b09010c020405090a08031806010e01060c0b1902040b0405011b0f0210020a120305071e08150f0d1113022a030d090308 70
    0x12943c8003d0f51404160301e103000e01001c01c01ca001c0d00410900303041c81c1410b403180d440020802007550306209480d0109d080c0308000810304142c5400c51041d000c9000556000c002c0c8a4035042c640c00c240c0308540d01180482c0400c081c14005140c943c0200340d0002d4110300351059000d499917248150380081c0e41701d8000800050303145061b422b00f00441c50040c1402c0e038440d0095403510b40094240c021140b40600612405000240060004030002c03807515074800c411541c0301d0303585000301641c2e0401d0040b107001441c0343d00110215003021180b10320050f040b0610068908040e4200b1403240c9150342050300703600407600b41c1d80104174101031908481655450218152414000c000c000403940b103000c18408003001e020109180e4806e0801d94003840d0700d0fa034038031130070030003400142c444d0741c1003424a40c42041c000c41001005005111141440c0c03065490380c070380ba01c5011041c0c042c0d001d108484041c01090b46480091a00f0710014003810101c0756054038a8610b03038001980958502c0350042e0080b90b008030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563512958 1250 563511708 563511719
    0x212040b0a020403020d0b0408130803030618010b2a060705030f012c090a02190303020606010507050309060310090203040c08060711100c050c03041805150919020c01020a0504 77
    0x3046501881d0404210302e003034150707800210741711403401e0301810b404800d10000d010800c07804101c4104c848110080d02c40c085d510740c9001d9580d4002c89a00c3d0041080c950420743d0880d00c0e2003114140da220102c8282030010040300a580030f10540c1c0102d942c401140b0a0317400c0c5803000d0080c079024104503a0f46665915050031319141c1c03804180e01a01d2502644a081890782118005070307603250010f0b06522406484581d440c1d4501900514003951015880d5000540224007204400c12030b0710a400740ca4540d41c0ba02d0040d00e040c0206400500f00740c20402c040c40881c07421034019640441c6000c09080313040e44030407800c4100c0e0002c0ba022613105080520601508104221155010070750389400c040801c04007200303e03107c440c2818100d02c0d00e5203607840042c072a40124180c4904440310030849450756035444c01c5201c0441e40d0034075514440d2602010a0084c503a0b054100b02203040a015401c290310b41c0c0c0c040100034451080e10714944c13603081c02000300f2203100380020184c940c020754405d038840f810b05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 563514208 1250 563512958 563512973
    0xc060108010b0f0f041533030c08040609060213090e0709021e0306030316051014010605030403080603160603020a080c090f06030a0e030721030c0918020d021204 71
    0x9101c2c94450340359840000c4441d910760040c02c48082c410394000c5010503142442c0b1900c0b0010b43c0049441000d10068009201d00c001070003c910b540c40b005d903c0019442c2c0c0c50540c2100e00070f90345080020304410029011400a4100051092261600514010f040148800c00641303a800080406440b40c189014040e4200080809440300103411440c0148151041c2620154000d22640407039001c80020050b541c2032003542c01c0d0780b200058200c4e01c04054a045a15074101a4400346011301e007480e00d440c81080440d080b4141e0360305071280c510319282c6450588218000800560b41031290740d403400311085580c0801d000070001c80d02d0250300c0300c868000c054813618000346070301004a42800014403568644101205407202036440554a844030702e4808041c140002c241c50030751000043c0401004940310b034001a200340000040d0354071a810000b10296072408141d50300181111509010340000355026034442c030000d41c40180b502c0500e004001c282c1e001942d0400052404000700300610088 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 563515458 1250 563514208 563514221
    0x70c0312021b030c04090501062606130203033c03011409060a0b09030a0c150324050f01090810060501020d0c03050304030503060a05041b031a0114130b0c06010801 72
    0x80710b80e41201c080d940008a9910001d802c0183e20032a2a24620801e000003035100c01c0203008501e1148220800703c802c5619499880103110b900e034401c0c0c9000902e0542c101e90745019084d80180514074000e013540718007410b00700c0341211103a07904203421039000184000c0c0180740190203400e1050303101c0d858405420000006440d060303000751818002c1100380d03612015004c017580c05c0b403500d035601e0f80b4910000c40d1420700c4040d8024400081c00801080503910140a03000900c0305036007d02a1003410b01110030f01c008144400045410310a8041c00b852a003065020103241c010f1601003146c0d55545d12091074004828003440016680f91400d012550f41800300803400201e5040c44a040c01250b90000c00a200040c000340400002202141c0d141d41c502c2192001803000400c1481108208403840b01c0d00506001d0041c0468500400d44070a041c007203004101480c0161942451485180384040c520703401444896004480740304007049440721030001d8544003861200030550b560600b6001800c6944 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 563516708 1250 563515458 563515483
    0x12050a140a0506160e090124030b01050304140120090a081c0f020109081215121513120801151701150c06020301060203070308010e06150c03070c031202 67
    0x48440280d010400010f00c4a420482d01c02c82c510340380e03d0b6103c2c2103a43e5419020101c1c0d220503d40000a80d00b008525074490710304030441010400204088181d0446900e03101a40c00b0520030320014010071651042001071140c1c5900100c1d018500034100400181c6148034810110004103950b03516040500900e00a800407000600303240c0a4801000c018002007012442080003001c0c60540ca0349c401e4000800082d40f0a044540720158040c0c1c80215150440385504060752a14410031186429456003c00c0b482c20009004020504041d4000d080b20040090351043c0003403d40380009803d41052200c030244650310341c034155041c00500d51085001c1ea20000800c140615404060304288110b6411030f1005132202e00c01c400180400e07680c48040e0100544543e20110000521640203c010042c03d40b00395107080d07640ea03c482a903003000c00e05451031038003d00d90081c0c00714225080c1c0700900c1581c444c901101d00707100341617a0b081c0140c005d9400440390160041152380d805501004580d02494 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 563517958 1250 563516708 563516713
    0x50a120b160206060d050c0a030b011404090c0902210f041a0c0a0e1809010506031905060a021e0304030504060809030702090f060d050304080c10020d12110412050a14 73
    0x6100d0000a580f510050640f912406503062100d0800c90204203905d036454000d0b00e16070595980313080038050310030248525080c0703d00c0c00403503580031716081c819003461560000003080c004c1e04061060700290060200ca041c07a484400280303040307030200340d01a4402c075505001004186080c1c0b030a00e00c41e641c0d0008060448032044103010074110701c2c00135101150254685001c00300003c0c000a8400360440c0300d628050480401840009141908070034800d1a060342103038001e102810f0882801582c80502034000e420020114081c00c071207800078054000d1920010030500326000c81d0030000d90090b181140813440c001020004240c01000603940107203e0009503007045481d4001c43d20002c0c00405c041c4803040c5501c002070003544c1d4801a40c58854200301103a0311641c0301d030300c0f02d5540c40000e81418855801c814400205610010b079070040d021265581c20f059212072900e001c0500440040c501c90020144804075204801400d11888140101c005011400407414840806a2007041a19903038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 563519208 1250 563517958 563517991
    0x4060911090c040308070204020f1b0613080f0a110706050409050105041a040b01020102130603090c0b070302070e15120a02041a010905060d0e16090501150c02040b0109050a120b 78
    0x21060809560444c0c0d00204031554808040c40014000c1c480d600781c0e51411400484c2645542c400d449404024841c08412200c55413964600011f185080083c01800b0200411144c40c24451004c00307814050b030141400d04030b60004d43c802c4c40c1801902c1d0405400503101080400242c95140a03183c01403c0648041080e111008008540032041500b40c9020b05d403540016482039100754103c580d00d48020600340c506503259040207010704500242a46c40030b02a04021400d100c0c004110b8a959905400800b1881c0c60b14010702099600101302030142144100c08050a4444a010340d09011854000c4e05150449104010860b081540d00f41c044800540748000340743d80284410341a01c42c02c841950311103900d19050320181c1207010180d90140200d0400b480107401611070309023a03460110042c030807070b070b00d5400320307502503080e1b81945002484a00c8a1405801e0951018a01d50018541460710030b449001044003007810343e124003494000c11140b6024003070b1589020790400800a0011041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 563520458 1250 563519208 563519221
    0x6190f081b03040f06020f040923071b020303040b03010509180d1d0a0306050601080c191b06060f21080a030b030a0b070f031a09010b0a02010f050406091109 69
    0x40601103140d4040d1070304000003203000e209901100c03620a0f503001c0c100795964060050b4054107500315110386460503040c501c5440c032445d001d107104e1030780106400d0701600075512001e0459a06864030300394440e007107080c020000580c42c00d000820182407200405541c07545020140104420018410702c03081070f42c002e91424240001c152941400203d10303054042ca041e65400c0706003524000c000e80c0c1d1120b0050800403c1000303940004e440395030262242c0a0030350ba180c0c10751380c081c030504841a9040e2000c050301e0b407103140640f0803543c000031007800c1140795100d1561204221136141c0c01071854600704080030003040003036013044803c0c8821003a44000c2c1c404a035464214a00035096003406240c2c403021408041d40f42040451078554004034180c8250420f00300142025000000d010002414807a10040c01c50300a400c0c085d00d0b08003e0080307045a840c00491480d9504800064401c43d5200c0131009451030b43c41c00707158000c901035040052341c1e003842c1c0b400c140b40202209203140103500701c03002c0255 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 563521708 1250 563520458 563520481
    0x20f060a08070f1206090906051f05013905060601050c03030a0221070c0219031e030e03010e030904240b0703090308071103010c1d12010b06190f08 65
    0x20002c04505008480c03070804002a50503a013400d0702d0b0000140380020004040a140d00840c004501030001001b0340d07103c25a000d05175491100c1e01003410f00341c0c002c040100794030440f1100c00c01f4144d032082e41150351007a4121004030303100d047d0020400c8160803000060020a01c0b68681051003400c0140c80c01103006a8183c50740002088070380d840d0381c04155030340805068481100c404160000348211751038000c201070186151510140d024118143c802204c1203800903502050f250010b1650785d10b130380480c0c040c1c1c41c034403070903482101001110f549002042c1c0b02405610b024910780005907859000b500d080c0802c82d440c502894146403034950391300c414403610500440954448544507583c0d66502c0c04e05503582800ea070b20040858500094103001d001448041d00346100c0110001d02100e84020300888202e424044403102c0c03c500020007864030b14000c1e4011a00c1c0a2000012980e4555000007412640042441d0403400032000c241d80009075000214000101140c1000403d03410003080c80c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 563522958 1250 563521708 563521711
    0x501020610170705030307080c0607030c1209030e13060303021005250527130603031b05010b060409090302070e07020d20010f0e01111e0306060403061404020f060a08 73
    0xba45182c8042c080c4450b01003400000d024080c040e04581d03540806150241240d44264410810307401220b011680c868800d010301c080d03001103991040307001900300e01c2420040c031144070200d0503c0f005041501d01790303c038940b18198661114000203429403071800c000c0c0c10528150564401c0b1841c0c0010000b207845402c519401a88815180300d02e0301c4508802602c8900c601150311049901348070400c4030801d4032400000c011001561082002003170800b1200950f8994003005000c5003072171000c0a401c15030342c8517956455004a0000c20710242d00c9010a01d0355210340c0207083d28681340c070780001c14140c0401140005040c0700345c42001528044500039220243c00340100108042c0c404c548100040c080050790a5040d02030007004100040c600040c02003101c5000c2d10000e508040140300303400d600340140d5802e1804105a900302e80044c09030000190f10040c4a1030307010f8018000400899000e101d0700100c1421f1620403805030900340100301e03041e0354081c141031195004105e160700d1f580d40300030203e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 563524208 1250 563522958 563522969
    0x9060320090118080105040c08031c0b210a02150309100c11160911091302090a12150b100c110406081204030b07081608040c1703090a0501020610 64
    0x15510707a03941030300490344040010100101031410309000f145031003065220a029502c10141541d80340c1c1e0f58840c03141c4070700940204008d03a1158000e41c03041055a90416006a0402466441101e405012850b50442400d4074101c2681c00807003014114102803414198080a81007018214035140080d2aa01c108025409c14499201c421a008850007080416151180c00003901c11620303540c0c0d01601b0101d49445080708941c00d101142c540c82000008a50102c0300150418280074110b544c003070043d60240d803200341c110080b0400007812010181210000e10700c60b0f1142840e00c50400c4291042c0c1d4002e07440540700d003552044108085401c003e102440710751113509000c0030110703100010002e2440d41d0228206000340403e200d80c80031450020300550384103c003180140d03250755508980c100700844040e40300d00c0340306d1805043c844c0181011070b03105116002044010740c9680800c2c44041a01d19400c00641c40410740c40c120f1b00d051f1500002800b405c1c401805140f07818080d0655041c90752181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 563525458 1250 563524208 563524271
    0x3060c0f0415050d0617060f07020d211107050f010c051c0b090a0209011b02090f0a1e0207141f0207080702040e03070c0f060f030c03021e0a090603 65
    0x4082000f0700840541c1c66840380078000300b29580ea20107110344810124010a8494050b15000070744d6246800d4041c0c0c01110340ba0300030540c094980b4001c1d070310096040d410f0b03100002e0b55911a2507464a80c00380601144038000e8842e01e968952900c50710b014041c00311150542d050404454040e640b00c1d06070342d00084580e10f101c21128907440014001c000c4051b9094003c070036078041281040c2d080d00184001c66083e42c80481c0c04108540e040346100d402c0030000e42c000100804602c4102058124980042c142040014800444120844800c9003151030444294000c9003c1092100d2641513131308001088010b4060013510041c0344004070410a5003400d10355000c43c07440280185801944c4400b076028000f00410140b000c4119903076000310380125200103002c000880c3d29048025800203c0e24261140030b4600e14142c001d80141418420440c20540d0900103144842600c415125486248800c038644c0c1d52032404005202c82c6c503070b4201e40113050400104220000044200c0c09648000100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 563526708 1250 563525458 563525489
    0x7021005060424050f030a0b0403050a170115260a0f060b0315040e0a110d14030316020607020f0a021005040e041407150f0e03030c100b03060c0f04 65
    0x10010004110808400040c803116080300d00c40c814000f0094a604685081d000d801d04d60402d5501c42100070000c24103a01d110200c0e000a015274040d2800d202c5504041c110307440c00c80008803091000764049408031040d0002104010342051020030f03401c41215a944050001d110b40c10680440500341c400c2d503a540d8003007005d0800b85540044060b10304114031039940e0030120900f01c03607041d540b41c0e514807440c5807500c0d620907000c001480a0304190f10500e000c01c804441020404608110041a584501040c9054288030780c1400154400c4610241c1a94000e006a82c000e103010360042003182035500c110290806c1190010b410700280d68100c81d03401d080b000090742196140240d070303c250452071079a002c1c4420004110300258055200c40d041391b0a15585803a00da038160006101e4001040f020004820800c0c440c8440310309408000d02224613001025900e545480000da40300e4140e03075075030842445103180034422a50000c0c204441e1a04220f140300c40045036114a10800c10010507009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 563527958 1250 563526708 563526721
    0x3080702010e0d0305090f01020c07062106170f0c0a0e0a020405040c050403061b080a02070f02061602030c09010503120c010906020415032316120c020d09060807021005 74
    0x10059101c2c0110542a5500d1011603000074000e8902600d40c09000d018080c80461691414401d40700c0081d0610000c03c81145001c2060f1071000c4100c022112154001d0103200081102d03000c0d090013004202902440b00c41031140184c204044048400008d030440c81081403180e031004549800d66071000b90070411500d4031115100203215960019801606101c03150344d43c1d9420038054030490f8040d2505010f644100c002085520101481210100314039030f010078000701540d400752500f14802e80c0201c4041c8001d0b000031700590880349801e2404100301c1c40c40d01c11801d0500c480c2c402480b0568407600d055050600090307e6012010705001c69813400724291800b80000d4006416031500084115681c50f180c1c40c50002e02651096414003090a2600d4070403041780414600021800a52000c0c0c4a621540640400c1210143e02c42d01088030405040c40100414807035901c000c0d00e01c0d0028540c0448407100605501140c0c0e00041c04c0c000d241c810802d18075004a0300780f030707000c8804600095681d0f800d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 563529208 1250 563527958 563527961
    0xf0106020c0f18011202120303221e0804150c0b0408210403020102041406090a0b16020a0f0303021e0307021c0b0a05180a030504050603060a1502010f0f0e0a0308070201 74
    0x2041410fa608900034000519540e51204881c4c22034001d1b28441c500070092040b2517a688015242d50744081c2c03250141035400b50240050301c0b0110310944a110f048001100c8140d41c600b400c0384199080303900001e0410881340002c1b01244000c03402d0a04142c01c0040c0d03100d0f0702d001c49000b040503152100c0007800034501d07418448550b02072016025092f000381800d0070000e000b5082409175080903408803001196a1a00006982002500405140311a410026081c241e900151401501240c0f100c402900580c1d5458502d40070f0910308200c101406d165080003458031305000c2c0d0081020354000c0085404440100803a15050740586d0804480b0800c2040380100d56500c81000d0b081c2904082407061110f855042980592484010342d6090200d0b502c0240e1203c1c084c1d00020f011540c00c02c010001810701c2070146074001001420458070035030f1060003101912484e54100d0050350f6500c1e83d28104030961003292804100900204461980c0c1d2240a50300c8200700406400d000314540040c0b2024802d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 563530458 1250 563529208 563529229
    0xc0b090f0603011d01170c10020309060706090c09180803041104051e0c03090a140c1801060f180e0a0e0d030c080a0c052223090f0106020c0f 62
    0x40c21640c2e4940e5a03000e61a406026107844c1d0304030440100000070264041402005642110005007042c0003284040100701c034030707182c82d520550006015105869075208003030890103000c3e10713000c110011680b62207040988143c01410700c0a1402c440a5080c031080c1660201056100d204507580381c44604100c48041a580446a4040e00302410041e85070950441450020030f070981c0e103c01525901c0f1511503e000845100792140e000d01d101201140c030460362003554840040503510b03000340100c00b20301c1e003070340c0e14150103541c035a40b10040007040c1c0d01002d1210300d030b00146492200e00180c415400080c00c0f01c0c1c0300701440b800d4441d01003110720a61340e000c118643c070020100e81ea9007942c100003030098450004681c0110381c0380400186920b545004140d400200d981c1c4461620805601503e803e403910745082c0101c0035a411b005c00c10002d00c2501d400340110241001500201c0e0208021868078010702e151016000b210040207002d4001860000341c0c242154058050750854011410740c2c0744 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 563531708 1250 563530458 563530489
    0x9050105070c0909060207120806091306061a040618060519020114040b27300a0e0f0409020f15070f080406030b060c120708070b0a0f0e0a0c0b09 64
    0x13421081400301301c1c0c240e0050401c03074403d55079141e00040420050314060411910b03190040300707403030000e0040e082d50400320590740d10600c1c000a140b526122103104d44a603540103500e1301100060144101a080f16803c1884017a1008821450381000001007150040303074140c8c0e8072070500300c240c0c94a8034000e40200e04016201e2505031110b150508200101c00820b0752042a0b030030400c0c41c84801444c11840c0c400059009900421000060f400c030704444c00348141541501d21b0b882d200c0700140d01800302c01005100d10594400d408940704404001825031a0380405200e81d142580c8000140c40c0da5038404000240cc803000c0d03031402c49000003001d003845240802403003900319521b074004110402010380300703413042a5020007a000c074400c1400202d100704900005544e1142d130403141c3d0710440b1001084084d108407500e0741081d14580e030303600b01882c050710701201c0380b6218007203910098218814001c62404101c020403903480c10780c881c0c0700004068056000144c10010302c0c8041740d1170354650441c1504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 563532958 1250 563531708 563531711
    0xc0302090d2109030b010e0403030e19020108010b0327070504020d060e1305060f0c0d0c0807020d0201230a0603020901060c0c0b0f040e1305071215060609050105070c09 74
    0x5a02c0c40c1035080c00300c00b042d1500404070b41030904640d0602c80c0e400c0005803035008101c48183c0e42041520884450001c10484c101602c60f01300c3c1040e0541401460448045d030401c07220342041b0741c4005005082c050300007610a030814002c00180d40582c0012098403143d0035840d1102032440c0d0a801e0920005400c042c1d005400011003203108041d5034802400c941051341440d090352680c1c0b03103600301c0182101010b4150741c0702c080424052865400001d400140c007100300d40c5094540406242075032001050080424144020020034540600440380002c070148005c007c403d800103040e01c1059003441ca060f40310123980001903c1038146a20100c013a640050a4140319a507402005107071447c0b404040b510064040c80000c0c038003d0305029a40398204042100b401c183c01c101c3e03000c10601c2c00403c03515003c10001c0c0e180012401c140501005801100f1145d80340504600380740a90300c55110340b4111061410380c04100b40c5501190320002e1316030074a00107903a02003a060410352803440790080300310765 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 563534208 1250 563532958 563532979
    0x1508070b04140301020a020703081309110304060507020a08030a0908070b0907150207050604061409090a0b041a100f110303091b0609010f030b06070b150405100312030c030209 77
    0x100361510240c03044030321030801c80c007182480506140c01e134014045400c0240c4d01c140c6003403000410341006403000e110b420707015040169a50703124000369002c000c0400410400041400140b0107580607040d803003815400100300180c0c1507a56182117200040c108004a540d505c504020031040c0b01c00c4640194100203421081c0c28003104207500c2c1c00c0f5500c541e020000113003103401411400490114100d0700018080b90134540b900000703481442c0c90a054040e04101088071948a40c2d45074040381c00744c0800100000d030f50507403405020855201c00c0300c00e041d81e1000c0c5540721803951b40514500c0021003a1512182141003102c060380c00c40d410f0001601140070100c100190218000783c20784900c0b21449400c4490341035002803181601c035026120340012106144020424020b400c4a103407503001030801840d001c0151140e1400743c0c001d403451072511030302c0348000f0701d60b18040c0501d40e0050480c28a00c0c80c16495079590a14071b1540c0389103a030505844240811a8600030343c1920841d080182810011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 563535458 1250 563534208 563534219
    0x312260915150f0312040e060a030206120103020f06090901090f110c0d0206010b070503090906030f0102070b060414010e040f02040207020d0b0a0e0304080d03090c08010c23091003150807 82
    0x82e004041015400b6015030300710f0301294540015048000004c2a080c0303482c00c0d081200040d41c0220041c0070540003450001e001006031110310080110201c040401403040d4110f02c100418041c4401c00c55110781028803c014942d5580d1301202d044908040c00002c1c0c20044001640180004481c00100c03c20301003808682c00c5000304805d071401050740e09503401d031313a03da01d0b98a00c43d001d80f40c03010704aa4000d216007030490030481c4080307400144c000c1c00c4880301d034041e036007040c00d983c40202c0480d4069110414172415042501030680031203200d044206596051034154901c44100400203429541035508030015503c0e5941204d05a98018110100340601818403500800080d904c00e6240c51070403d00c684640004400c0d01c0c00d40d107581c400f5200301c5500d00d100310003405c041d01e41503c20407a08403000034207080074490400f0030302d880c2d03c0745031400e0070110041110030601c82c2d401c602072104101c0c0d4482569104510b02d180c41040c100096100c0a04054041d1840d140d0840c042e50700c10114080750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 563536708 1250 563535458 563535481
    0x2404030f0c0603090c060f02100c030606111b1c06060e19090b0c1b07060e10090612020c0a14010509010b010e0a0603022d040312260915 60
    0x4100e4050300c506496036594580403000c50b48a894042d2aa0b4100c1030300b40300c80f511900725100e0f050300300c0c4103c03901d00340810041c2d41110f0800c1640d030007082c1d03500e40402100c0d401c40d480031240180f0303034083d085002c40b1202803064003c4000a00c2c0c45801c034050803000c01202d550760355031000c0d00044100402c54503a44688450101507601d94004900403c140c0060991400382802003607212418034141e0700c840000c0117664000011004000c03001da036600301040020002c0b034004110560b16400388031440c0c0e0905c050903202ca051141001310440303051081980105855408450094006030b03181e00501219081c0305419030018101c022043d00340c0c0c421241500420700032071418000700b00084001d401034500c4114a01460b420001b1079004000700b074040c2e40540541a9580041d107800380d240c1d5485400080026920756078100040742c2841880032103010301600b00302c3da08000c88000001a4401d81804481007203440c1103240d000000c00c908070901007075110440e0600910b000d820690041003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 563537958 1250 563536708 563536733
    0x2106020408030304021503060d08090607080310050f01050c0303270f060403031b17040c1502030406200a170903011a030c030105161116060c0b01060807020c240403 72
    0x1d114006c880b400914420b00e00d011640181c600a01602c84200305a035140e0590700940b04141d4490340521607140403410a40085124180c004d83c40007016042c00100302c03610701c1b950a1641040300c14007084080ca04d00004494215a114042110a045441c00100400a10310044c3c016001c0d21610705c0d10100001927407401144203407414845580c8140840c40140100d0502d100050003085401e02902c00d042c0d00c80341c00c51b0080f8030391820940c842c02102d40b0500300d0303288903005a0000808106a0b43d00c031010f01200700c1c0101440d035410103268520390f540c3c03400321005044848100c10454041140c402101d81d00c00028009009208080014110b01c00e4224446402030041c801f4598207481c040c400c0700e118100e522100075200c1c1c1c43d007108031070440d104000c0040700c3c442d0368280d4407202c00c5071602000078a041d81e00c0480304295450402c4d46041c0c103030300c11014442100d0900004940100da81c000c010701c207440580a00c98a8201010190360961040c14003c1000030080709000b007100c1d003030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 563539208 1250 563537958 563537963
    0xf050f0703021c0b0a030b0408030103110d0201080c1c0606210e0a080d090b1602011d07230603010909050f150c0a121e0e030708042106020408030304 66
    0x80440355910002503080c0e100d03481019583c6400e4520a40983d4035a40c01000e800c1c502800d09203840ea1203a07540c80110780c05490a80e1111b0002c801001040b40c000038110b56240b050fa41e200013400c86d58006015044040c003010700380b10020810700d000824003219058010b4030b8607018000d0640d14900541a19003080717020110104201c441031144000d0302039042c01d031001ea001460058a41c0e01c9400054100c0d15a0b10781e07860700e480c3d1a00220b80d000e410540607400e0b001088200380d400010103030031503078039021100e1203032002d8a500d45025004201001201c81107071985950740d152007400c03002e20800300485584020f003c0004541302105a1091000d03d1061086540a8801080b050f545111300140754503441c0c05d01c00080e144100030405008069840d04280103080080140c40003036940c942c20115451851254020103c00c45004030066400403802a40c50103c0b00d80301d0b013081d80304500803061050012501302d50b5100ca120620b610b5685c100b46e0854550391510592174907648152002e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563540458 1250 563539208 563539231
    0x30d0806030a200150030703020301090605030115052107080c040e0715122705010b061602040914070308030103060b06040819080d090b01180e0312060f040f05 70
    0x240b1031500343d03107402615011421210008082e170100c00c02c003020300e031440c0caa150342e401c01c030500d010740504079020317500640e500c2e100503860758108800d0604480c00780e40114840c0e03052019803c090484440010151a130a540d0308200d1501319059000404816170404280c1c0300d0b10000041450b0042588075000c04102e40901203c140902c4599413903a29000d10341000b60010801e210440c02032258410030104208082406103c1546650841a000daa100c956440751000007042000c280f01c2d210700c01c0c900700c0340d40341450584400d041001c0703c04407000b4016581e9002500078404040082c03140044580202c510154582ca0015407a401c20300c0304840c21410400300b50b102e450311206860554038041e00800700c000c20080d5030907203d40300b00402d4070302d110b0420484d13044076007500400040900402014815502d00744d8071440d4180705021400c0040d01c2d00101488491012003141d5178101130101c08115619400001010000014030441d8003e01d0001050300c80443e40d041944512104000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563541708 1250 563540458 563540477
    0x7080a1b081203100f06021c02061302011206030501090f0c12021c1104050109090c0b03040b0f28050601112d01020910021c0905030d0806030a2001 65
    0x1012040e1000d6000e01c8400d5080919010300800c4203030082c41c3e001062610000b94503070b41d2900030300c001036150000b0b401030b0410030103038a41e100e08403007941d6510028801080c2c0c0303182810b03d0704000882000001e0400c01d89051201740d1700220340010001d10740050080007840a1850b2210110280410442d14083d0652002038424000c030a02070f1071a40150401d40114007402d049018204a41c0c400c031b800c5c0000d10403424541e19a8884d250181c040c5a0000032481010706000c440d103282d0381c0c00140c10b000100100400a00302d1080680c12045040c681140358035100140c1940506088155031500c10311510040d410440e9080b45014040c20380364070003405000c1c3ca03c0e6455041070401c60400d40411f036550300d254013200214203402c2c00603070001410810600001800d0725011054840142e1080195070a80c2c00307108034200c85c428150519060240c500360100ea207407800389108a06004840e0000b0752951030912082e86800d40c4402c000c624688132200b11103d21084144580c002400c00d01b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563542958 1250 563541708 563541743
    0xa1a011e03031b02033d0915050604020d1e0f06051f11032221031b05060f010f0e01121518150f0c0804020d02182e050121060807080a 59
    0x1c5207640c8a83c1021408d108196040c1c600310217468090300c019000f544c200700d6039222a1082c4240900c03105655400380340013425410100c107440b511100c9036800c80c0381030005c0045940f400424a829200c030740e00350482031120300c4280c41d540d002403441e11503400001122603407070482c841c48596144460351030140b42620341907008a0b21311501c15024103500c0b941180804a4000c100c041c90641680012a01c080c1c000d40c4d4460900e0000c6d00c00c0301501102c84014000380640c4c0c0d0320a07005c0c000d100b000007520740c0340200c42d042480c03c0760070190940c5c1c184400d881e441e80e40d9401c100b010103404210341d18400e600b1714104203001c1143d01c1201d1180c0c50f000d0b1980504405005103800340e0203a640d04e0165490302d400b0041e2045d00074030700700d07804004070b060f0308030203282e1100742407081c0300b90304c2800b0444031010f456070040a040c0d140848040800305050101d82c0e085072840551304003104d050f0300e4a14840240200a05040e00814024803c0c030900040b086000500b4890340c9109001c032003004003201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563544208 1250 563542958 563542961
    0x3042706060519120204080a05100b0108040213150504020301031101080619301a09030406080109021e04090c120501050604170a1a011e03031b02033d 66
    0x11400100940303400180c030301d050f620400401d903c0b070414040c01071500f50b80300403003841c0c00c590481c00c4449400007180300c50070000a20502480ca5403e0a10000310307d007590009025113001c0100c00f26840d51070764038040b000801441500a0140680110355950710303800e0061200c07181241d414005081c80c000904242002038600901001c6c049240000908003d844190850f81c40742c00b031081d0701840c072050010301c01e860b40d002c0341034040c902c400401848a807480720034180041410084d03900410040000030f5020011504540c00d01070f005840740720044003000010f66089411494450106021590700f2850348460606030658a8071135202c5500324006007030320000d10401e54040414002000303540200c0c200e2017100250f4000740c1d01f9400940c1d842c0d6200352004001c0d070b130150304100e00501400d654024080c1c4c000d140c03c4126060302d031030360b60014205000b03d090810494031400002045442c1001049158100d40b904054690341007100d084000c0040540c02038540c809591320070701058035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563545458 1250 563544208 563544217
    0xb13030f080721050d02090103020d14010f080f1203041115191b0209070513080a06050105030a05060103031103280801060c120f050417010906150e0f0603030427060605 74
    0x1604c955090035002c0309070400a41062000c181496020404158502e141c0d11a080205002100d07410684d410000c003031810722110303040840f00780d011a200d4041150001407000c031052240411130742d04e0765149000700e0504611401d003038000c00c00c00b04240710009000c000e0501c43e0806c0042540c0b50502142c11100310120fa10042c401ca69002d1041e0054100040b04035804961410401d141c10080c510440f114045d035809000240c00000b005030800c40f00380919030060004a008140a05c1c850b00e440c0c0c1c40b6001840300909028a25001c6000c490042c41a0340c0d102034641001c042a48080600c1c03401136040d80b2210b00095002e400218855000300181d020064200b100c0185c0d1070345140c000e40d03650360311782c03040003d02c803041c0700c0000c01c0480d210350b1002c0400104000300f1284401d01d046015110305008240019402c000d0a0100040704142d0702c0d03003c0802c03070f08104143c640001190a41c80385401011143e840440c1d42c8821145901402e01d1214600d0010801d50355648000c8605014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563546708 1250 563545458 563545523
    0x3020105161b020d030207050904030507030e01050307080f04051c09030c08030c0703030e03071505071a0c1c0f0504210302040f0504020714070f0608010b09010203040b13030f0807 79
    0x1d40b02c405602505104440c201c0d000d100340100d500c0c5581700c0e80050031920307040320214001030000a0308000c040c0c1c098210303415020301b800d045e4114104003c000d4480400280516000c0340703400e0002d17043c0201000060041ca0351075004240654601d5401000000035010aa404220484000480650000880300c42050010190003280e0659074100c5030381e103040413007039890f10403a540070071b0413003029020803c4c2e15543c0d103c450f038805061504c400e0156a0324100c0c206d261020081181840240c0c0c04c0300e8618500c00c81c1c0c25503489440031107100070043c081006070b5840c94170041100300102040000404191341501c58140c01020104800342d204602a80d107100c031504000300010b06290b005025003500c1001000d40344501030700100d1501c0201c0c4d11055a2039082c0c034040204903002861076002d080f250355190710700f00403e00043d59904c69481030030303030400c1c00260511035140d4030303103801c00a1548441c444901040da82002181c5820080f025207058002c5c1500d500030003003100d5107507900407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563547958 1250 563546708 563546747
    0x2120c090612180601060c05012d02090613120302070e06010e0906011b06021e1806130b0309010609050c03040201092705090303010f05090f0406050c090301090302010516 75
    0x50740440d42c580c2c80c010309011089019030f16010040d10090021502911469643c221424580d04116003515860200010903072003217074a41e0582100d10701d040c02100c0c0d12603005a039400002010403e1031145509841242c9615440450140040403042019034001d07801c03622400d03200c1020310220801079940c2404241c510f0000522401c1c84480c0310340c0b141d814145100310514a11502141e00c01445044a0003a070000c0c4c520031201ca07409a091001c00c000141700c0c1400c04d06905c40e51225144100d16110701004600c000028428000c0c5c0006080745640460b03e07428801301c1640a0f000c0b501070355603020b040400190b5101c3c1c9440559103e160140c0d56104003d183c00303030b03c0c0c0880e5117004241c4070a50700ba07080007d44040e00d004107801006c407200115500e61601d91551240b54241e04001d02c600a40410300020750b0249510380e030420f810100008541d2540045a0380034491098010b4046d401d00c00c0781020300d60194056482403c000000301510325501800b11400c0800090b010440c0c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563549208 1250 563547958 563547967
    0x1e0d0804021e060307230903060103170c07030803070e150904050a0b030a0c0e07051c0b0a090f020d050907120615031b08010c03020a05160f1502120c0906 68
    0x1031a145082ca1404031034000e210903541101400700342142e10845210b00811803d5445001c00c603c175441c81e05498842d040110b0802c010301c8002529124184000707084c01c80c091104c9200c17a49104102c0d50f981d0401e00842d402c2c603581e407074150429081103030000e0110304051b000d46018144603a907e0764400c1140d1400d490a40720b5020007000700005005c0780c0d50346980d5100c020440c0c45c10403150002901810b034940300545040001501d40c80c2c011320b6003040000070301100c5600e58980903a804a0402c00300082002c49101c000b04442c89010780c0f05a000504151440d520400e065005141004a00105010a66600018550f144040d01c00c008119088800020202c3c0040e800011444040782201024551303c0c1c8030742c0000100341d445404c500050b8507003008004c00c01d10078281882498102542400030000c4007070410b0207803420007001c00d5140114201040310000806a800303030310110700e00c0391070102c007001c03402074101b820780690a41008021401a130034200c01d48480b240001c00841c540b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563550458 1250 563549208 563549213
    0x7030f06050d1b171506060a020c0d2406080606030a03120209131401241d010c1505070906030e0705060c0703050a0b061309021018171e0d0804 63
    0x41c1408608071505424a1000110320001c00d10910003880c0340e440014510360b200134254178811000900018860b010400400800702e030080307113491100d031003202e900c25010007905203940c0144000c105404401441e442c1c1c00b1885150742d20140640b100030044500541d91042415940c504c0803030094045072900650000c0914641c0051151444c06402040342840f5101410252081c80648403ea03071002001840b40116000e0081d45403203407082518101001094054400342400f005011150408410340d000759000380c0d102000345a0010717482200d01b4074103a007030703004040684d00c640004c4c0a103a80020258403034020424804403841c080e00c0510b14100410032544d0042c0426000ca01402c00c002000c200c09020841e0454024124800749281050402c82240a01500880150318180d510380160b03c2d5074481c072040d41d4490800c20251502100090401182e82d13201c0964102c0d01a00c184a401c3c0104200d1030041451000003002103d208026031240c1411b41a0070020b103860000901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563551708 1250 563550458 563550473
    0x3100e15040f021206090c030103030c0f12020f0f070605030a0c110607090501230d0504050709150312032a210b09150f01050714031207030f06050d 65
    0x10400606200526003598690204065401d107260074050aa4081500c5002a8150304c0090b03100c0d004454840092504402d0b4030124001801301070b040084800c0340c0c000f0000d051001c4200d050f0044061000c1211084009689201060398a8202d004500e00125034200001b00d110940d0b4142d240d03030781503a8030200313204010460000740d941000303a00d0466400038401803120302c1c06036950303a843c1012642010f0001d050f546c000591002e403600099000070524900d1019582c01c44403002c8049001c0e111410841c0c9004200e40000c0e00741c42c680b0340742c0603e0400c20141c4c101164809c0c0c2c05c108461522010075030440328000642c8800307400c8480820301e0380c0c03c005500b01003275209091100401e54551328280c0340d91502d0705090320542d912584a9920319200e030613942d02101241e0340301d50851510b4049409101c0300e010240c1800700100d4a0400c0118403240f44028074422002c694803410410071100d100c41069072410082032629290444e064401c0c010b034001c0e1000a4106030348c421031580e8244 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563552958 1250 563551708 563551711
    0x218010f0c0b060607140303181504020d03090b0c1e0304080c0d08040e0a051905040510151706071e0804170d0509031803070311042d0f050c03100e 65
    0x642c0414104000b0000a05031b90000038660a424020341c0c0720700d407020100e10b0300480b0350721192040d80043e00841640740d0920f04d0301d0384190f059a406146050501c0d0594400d2007a811a030003040000c64124140b040005035442c1000c180200340500c2d407402101c0640f00c5c8664010090b8a4122118000702410000541c50201e03129141a91405598003000c907280d502c250307000c0142030745031001c1c441c1202c240d80c60a004c140c50030382c0400141c01c0581c1e88650b44c0200c12420004640c4036501e1200c0702e250720030071100400c00f40d8120a01d0207240556203807584021507803140410030801060448030b8114221803a681d84070740301c5010716203c0c0e48441c0d45915050070f008030892420080100d0708103030ba0140c1030046401000035a15004407155450a030b403004c0203594000d40c0540e43c02c00100c2e42e00085540740610940c3c000034a18041c890004010b40034103554001020900042c81e1014140d500c42071100c07507d400d0411840d19082c166000c103100503107260441c0c1e51007001c02d215800b154a03015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563554208 1250 563552958 563552971
    0x20c100e0411030402030c2205091e01150501140c070b0a030e070303020d0305040804050414010503010e0d020717160e060906040204050f2110020415091d0604060f090218010f0c0b 79
    0x8402c0c148000ca0003506079042162100482d40011622f6000564a81002380e181002c0c54001d018080c0410b40c48c046d903c0303079885614104140148040d0310090001c0858041d41441d50903581d9a5448450309a03441d0b1010081e000001d14003480310a000c078012840c1c01c280c039803581c06400c0000e660402180940000750040e102140100b0001032240c0e1680300301d1040b00c034400d070f28205662400e400c0500319401e1544117441307030b004000d82e000d41c16808034036441500d842006194510116000151a080d082460700009800c0c515010601207010907400f8801c682c1100c0302803580d990241404243d010b180b0610f900021800244002c4e440c1c02907541d980814609071080614014448852402c01400d8418615950000b07041c404030303002c4003049171100c559081001d40e40b072422150744140b403064003100c200e4070b0303c032000300700b65641d241c100c50001c203200301180600c10f0302c03180240300a43c440034070310802c006940c007000e03115406904462084042e98440705184421500c55428018004000d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563555458 1250 563554208 563554249
    0x4140312070609080405090117010b0103180f0c08030309060a0c030213050103021e210108010b06030c0f0910030c0305070206060f0d110d06020c060c07150c020c100e0411030402030c 80
    0x4901900c0e4440c15034020001803210041200c00d40407594210b49032520bc060405050450040c645002c150300450f9007644250345044d20209803d0048a800098020304640c1c040007061010525000440e5405010050301c108101c1000d000e05404a10502d044070320b4440c11400d00300301030741c0254040c28118640300e00b20050140c0b01100d1044561041070510300138000d40804030480700e07501c22058007508401c802086240031010004100e400010b000c40107444000480e9000700784030b8070640b10036210246c20341c804104503d001401408410034400e00081c5071800141120348000740450003080007510300003414842c641440741d0224141d4050b00c20740d001c165500000d460706d440c05005c071405540016160054200c240741030000c05041c15802c400244007010100e090b44902664004129078006000000c505060b070404072304054150f0302801e2a60081001ca0f0031106221000c0411130f8100300c19a00780104281d2408251006500b55112410703c03100c90421150344241c03036554600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563556708 1250 563555458 563555467
    0x1a0a020c1003050a0f0603020d020f01180815070e0d020f0a12060504120c030219020a030b0711070801061d0c0f1303020f060f0a0e060c01020403080414031207060908 73
    0x214403a00034610220000a0380d83c000c00c10700020b00d01c1520240c40c05a2014801545982c0014001008501000c5e100301c0079407000c91042d030701a000da07081c2d003035110860342074440e90345070441c0d29080341c00e511407859154800011045441a05100c0c4500401480400ca10005070244408032600030f84060308800240c9004c103121945010a88050303115250103d403628040c0341c00301102c25000c00b58400d200d00d02006000003600410b060451100320a05005e24185500000341103030741641c40589000d040340b0500030400d51041060b04000d58140440d0300c982e4ad03807203c5a007262b400b4481d149401c011102d9140351060101c07143c6400605044501d420003501c0c40c442c03006580070101c9074080300d2040b0410011400d240c51880c1107450210b0b203c41c01c081c1d05031003c2801d81b107445201300811441c00b034100403517960202542c10011202c0c00842d229a164035211401764001d00074074507005230001c3c1c01e03410382c1b0300000d2848400d08070a0740c103403e15849546203809050207041c112407091040c0b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563557958 1250 563556708 563556733
    0x271030020d11030103060608070302090c16080408010c111c0513051203190c110904020120030c0f06010506071e021e040c171602030d050a060e0901061a0a02 69
    0x703081e00c0c0240b03140703440707680b5451480d19504030388555000d5405034000c0ca1003003001d6a00c00301000d0f4445603801c00c80ea901d509500041014400070100100390000110700801c290710158480440c0301250344543c003000001c401c846603180b080304030703404600300713078a00d004000d604c51070103040c0c84400380c0d01003400700b901c0b4000281007080b40d01c8441907560005c600300d40307081103180c40500c50130310302c2c20070292005003512a54265808820402c0c001c01c0000301260459100707030803816106017040848894940c441c03900649a41c0407412211103441080801019140c002c82d503613040b10300082c01240b410701540c0e07941c105856404c400c04005541d1042003005070311414964100c2201c00d201400145502074108800c43d81e2070340324070302040690071041400700e0b415012103811805080c0c4c68081300c3c0b04100100c0c91440303282410803080303042400307000e030036a50f5411000548140c0d102c3c04a00740d032030340001400c0701c0081c495020300900c11240280d104203c200104458299031041d40c00700400e42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563559208 1250 563557958 563557961
    0x7090504110108100b040303050a050d2c01020f03040605040c12050d030e0f0a020118030f06020403050c1008070806010e060a020705011101020a23271030020d 70
    0x1120305841000c0d41c1100080a50f078032008203603020340d10545075407007242000703440c03225409140801428024001100c400660080e000e4800441180206101c4012541e0110782d40036584407040000c003032030280e070401d001018000d944030302044000e001d09650307841c0c40d0b40014020181041d10381c032403803100204885503c526101c81640c00f6034000e100302035028500800b20340803100c940469070003411000d07411041c080361001040350240303802c040c8401c5403000c1d14a0b441070f95000a01d00001490310604105064000d041200d00441c04c0e142c8000101c1e0a001844524203061800108180300055004d030040d1107440e040001803405040c90601c0780045401544111411b0001d640420001c20440d80c0c848000d120305e504540080d4100300305a44003a0854801c12030031911a40307141c1c02401c0003843d8034180c880d6180d1042481d0f0032410030f504040c0b01d0360309a4190f07600502c10a104058000c1c0901c42442004c1c02a14401078800b6441c03540035030115155461130b05d081e400b04081003050703105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563560458 1250 563559208 563559211
    0x1005060a0b270a0302030c010804031e0908060c12010312140304060f05010b0f07110f032a0117060409060e01060f080c030a03050f0c030904090c03150e06070e03070905 74
    0x415501c903928914a8010002c2c0002048880340705840b05001400103882c041008140300d0b4082c2800651038031549815143c0d500940f071111312805031a5160030030944d0007000d0b002161921001d490054890b603107140d0882c8503092103007140e64080401000016001c0c016100e030101589442404250380303954034049903105a40a5800c0340d00c0d203040d4526890184142c038010480f0700c0849203800c100c00f04004a500506001420b22001000001c0319625800d100082001000341551403d600b51800e41404040005046a19200240100f1401e50241026a81d1113006000340c142c0356542d40200009455042400c94030070303440b5041c41091040c03d0091001400c06603254030360190030440e01900e0500b201d5180f0384240d0024081e00c3c0441d0304001240c500f0704800700700030f50311a5044040752851140c40c00c103603002442e01c20350400b8408c407045a0f0003170302d10807452010444414a1400191100e01840c1c81003a00490f011070302c054020080209030070b4018040e509050741e0b0381c1544044900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563561708 1250 563560458 563560477
    0x60a060801050a0915020a021c02030c07060918240306050105011403040809010e0a0b04060306090506040212060405150405131205071101050d021207120b030f1005060a0b 75
    0x22a2001849081001e00890740e000d011550100030340f1074980c40d000f01503d00c443d05070050751750000c1c410900c64801c1c401251910348035150702c10300fa002440c00075541d9122800c041c6445c0950301d00420800d2003000d100c011208040c05000d01c44011440c140020103102031010051410007820903d00340c001c1c070021000b0360003000000381941c901000901440e40041d4a800a1003040040000250032081907865448081c40d206000501c2000032a00f07400064000594482c0d0200c1c001641980c583c03c410190b9000a0003841507844590500085c0d00500d500c0c0318660f1600d400044d024100f650145070302c100d6a440300e40751400d0f4440450100c5100f502c1000d01d00c01c864051b01d01740410440f00c01e000840300c4c0b41480c60034456842d01002003002c40201030400100080f5041144082c3c0c040d0380854070f0308001c00d80503081810340940140d064039091006541020f03c0d940d014030380030642540d60740c001c1010b08210102e24065000034a0010980360b40300f129401d0209001405001902c8141c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563562958 1250 563561708 563561711
    0x120e0705040e0724140d0c090e0103021e01121805060705041212141204051615051c0c0f0908011e1d1f0509210d060305060a 55
    0x600344800e000950309a040c0e10395090f0300c0000200a4682440078100002c9107138101ea60340b40c06800000c0341d004004007020000500e0218004411500d20f500000c84680f0a864140005a0325905e10501050134030001e5400108403034100207011410782094124001403400c20520459980750a040b41c1158039900b4003088840600307010483c0400c583d517000320312414494102492704088e400d0114400d00c005004581c1b010000020034029200070300c0354440202100d4440040401803554040d0444080c0c907640314403140c0020108100d54000e060795030b00d20010040600410042c0c8032079115520344440030800c54252205072102e0300c200f42160342e85540b0741e07504134001c404c0144035081680141c5002d0745440d108188203e41a5901a10040c00c40c4000c103800300d280009400c80481009202d000f070080c1c41c908138201514200040f600c0c1e102c807000308030640769043c02580d1050000080440d44594000f030850100110002d02000300c960340d4081402a260307078480742407460580d60b02007050f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563564208 1250 563562958 563562973
    0x934030c0e030102161209090f0504050c01030506012703080301080f1002090109090f0f0507021014060a03020906031e06040c290318011b0f0f0e01050a120e 69
    0x596000c0145038116000324000c0d03040000c800301e8042c0c54050904c0041405500606c02030719107001721081c0c4010062510104400000160210003502d400ca504840c81c1c002e038926000c5647c040e204da02e001c1d94040cac2d52a0b02c01610203401c044500184201005040c04499000000562500043d4007a0040c10050300003580c010900c1860810013850110312030340107002100c801e0768022902000c6460380240864180c2080c6081801030a0109540309564108003c00007800d030005401d01800c42c815800b0040e22002c10030802ea4208251075503944042c071b454040002d07103801c2000075000361006054894010662a500450390003000703540075150840c0c01004140304040d1205802400c1600c208070102e0040c400c004001c000c8000c041d90f101c50003002080707030046480c22441c1841c80c440000c028800d03400004101da201c581c0c3c00a800940c400010551051041030307102c010a03910344607841c50410b81c2006440070b40080d2000401c004c44200302e42080103482c00742c440461520030180c140c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563565458 1250 563564208 563564231
    0x62d120412110d0c111c030f020c1e0d02031c030e1203040302060f070e030d030230010605300901051f050f0303090a060503090d030506093403 63
    0x390001e030746819850b0f0850302020228a8009242421440c0d2028101400a4480b0002503007080f000001c0b113030721400001210101504040c25244031031a0381c08131188103842104200320464130b162002c110a200e000950954240b082d10010640d01c000c0c02c0e0f403149501c0904280003c1006202039001075103d0044c5030300d108051000c000000e500380115803841c40e181d18040d55401024014804042c1501c0000c1c28240c4500a40c0d08102801415540703401c14a00005010350040d074038101048422184c0074920f96040d819251000c01016000c1450368a0000142e61036003040d4030402c1c2000817006244084d00201da050b07140031201d65604e00c4242081c4a6560840700010702c040b60013043e80303000d20b850003114903010080350001c40312480200e200402090071345c010100c07080e401640030030317007c10b5040e08080510700c107108280455001d112184411002c0e22410307501c6a4200b00d410300869940681c9401c217600031a90400300d504080d8100649403082c040c0c844040c00041d80c1c1d44161001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563566708 1250 563565458 563565467
    0x20f03100501050901080f130605100806060d0f0f1b15110105060901050609040e0303012c040201120f020705060f0a2a1809090c050f062d120412 64
    0x1801c820b00e00542401e00d1500041d01508000e0301b07120340c0b00c001600003038101400715401c902103540308000740300351700b841042580c283c102030203419500e00070100091405d0030000000c458480d00040703d80e40c003489580740c820b090408040c05481011070040641e511402e0050f00070011700ca020240c8006803010140100b10740400e014203d81a410b01052050b1583c0306003106054a404a5810f540c0f13140d000700003001032125203402c4215001c08000054004182c00c0101d41042c8016240c2c600c01c00c203003101401219049800a001c6a19108610780d860296807004181d2a90a080186002440e4036181c0c41c249048550a2141c2d1a020810115513414007071000c1c52400c80c81d05512074411000101c0080d900313601c00f00f0401c1614505904c000711b40f000c17000000c003280541040040a18180605810018007846011f1030080e4420740840c02e002d001c5030001c980c15024900004039201c040720201c03216200c2021030250074405890515091a100c41c00b940c8901d811148246015078043c0c0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563567958 1250 563566708 563566741
    0x11b0809121633110a0b0103120e0102030c0d030c0909150f21110409021504030c060906050901120e01230f0601081807032102010e060903040b0715020f03 68
    0x156010b400b000e5000c042030340f88464181c0a418203241118402c090314852420640010142517000403000000501088108070380450803103039a400c082000d03032030040e85e0b42e00c54000c280c002035200c414609140380c400c0e0711441250429140c05c94195a030341c581d0505440c040500703900034480d5454200800d081c44121200245540f010307030011414442c0b0101705c140c1c16204040c040f40c008030f9503014203650b41d030b001312255907004108210b440e10020790040290000c3c041190f02c2c00b207d030b0020402502620040c0304940d21540e50b1450541041d00440385116007219030070401e512100441c41d40d640c01c0c01040c20034007030300c640d030f80e0301a11030302c245c116841d0040d03e141528180b80e018801c0c1a40d00c0540c10303500414907c50a0050400000054075040650f800038002c0da44198114000c003600720300303410090002d42c2c0280503000341d04e0806034662000f6103004100794020007080060b940308a014241540c040d4148207001c44a601a15090364801480c0d045808000401c0002c9810806445d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563569208 1250 563567958 563567999
    0x151701150f020d020d0503040c0f0807091118010f11030d0b1809030f0717030406020a08090f0c01141c02090a0807060507021c15020a020c011b08091216 67
    0x1420501c04442000e034851390805c500108001d070000005041c402820b804800a0944240c0400761540e40c445203900d9144501a0241050400140700c05820f4848107440b45503940948100180310000015035032881841060024011118040d920100301800900501d48c100d4402244031519441000000951201300381e0580041c0014010017180020544410074a0300c3d50311039450300b280c14008003140c0403052003c5004000010801080300320b40250504e08820740364440e65031504040c59440d01c11b03000124020782c0c00342e120000782e58410078540030b2194142d980b00e46018400c1407449149681100c42c00c44040d00010105c3c400c0c00d003c1c01110080640c0d601606101d800d140700100644610880030b03102d462900d01c0701c003005804134903400b1a160f21042804c0c4648110803100040e405c1500b040d805070080e40302407004c1d54080c8170002c45002e003000c2164103221044d580d50909402c0103241d150001a00401180701300780803c0701c100c00e448441451404070f881c003100b500c3c0c500700c1c01c45030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563570458 1250 563569208 563569213
    0x151506020708060f0c0c011811030303070f050d02040509100609080d081902090301051003060f0b060d02161b0f060e0f040f180f050d030510151701150f02 68
    0x4126101c0042420380d0004058501100d031174640c02007202c0e103800766640c0c59005500e46003410003d40c001254012030b072449100c44d0070405640d0b0080544034041103034a8000b090042200d4200c55118000034108940c62410040c101500d4501080d48401c04803210b40b0381000d000414040c2d507811060a60043c60418010300c003006404800800300c0d4000f1b007840300c2040d0481c0d40100c00802c0b030740540382900d07005402040240340c07801a030444004203110a0b52640d02d0080300c03005000442c02541d902c190007400c160325007050260040300a50111700400003201441a1080c00160264400e4450000c01d00c1c4582c0d480b401d00714074040054841c9d0140c800d00100805040080d02c802d80d505907504000c590000d03c0e0058154280050514800b03085070242d80d80b0004010060b40300c1044a0850141e421600b5464585070280c0885509640742c1110744c2205e5020000c042094607000684955850200b0544074502e11802c0149070a07002091202c0d480440c1c0c002c1186e004640b0024012240300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563571708 1250 563570458 563570473
    0xe010c0e09060301060623040306330510081f06050304050c180711120a02030a0915141303050109030804060b01091a180604080102191817010915150602 67
    0x40107040d00b4001c18680001d03d81415048140c0207031700c415100150381094040c030039400002d113403007004bca01003404484440705c0c90b4003c04800d9a03100741c005444010f0242c29192602c4241540d104200074020015460528920500001d003104800010401c82d1625a240d0400f1b00d4600d08000d40d014a441c09444070301c10b52206011602010368020241e400c0a0a1480e040243c41b410088841c1d10344010110010307a152180390b00000070104201555102100551101040c410b100c5407070002a00052581c8440f080300b85803a0002c0c1546146510f82c1405650340740d07695425a102500c054020480103070400040c00f00e103015440e4425002d1030000481c1e4142100600c0c0e0071213814074080c03040b034003140c0301c011a03101080c2c051929500030800e07903e59964034a241d0107035002411a62030300b00003d0401c3c0080e80a8a45a241ca071003404540c0421410800c0c20001c1c2a000040c0304020344d200c00b05c4c0004030781100060071a040c682c03070011855400c1025464000d84481d070200085500151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563572958 1250 563571708 563571719
    0x312090c03020f1324080c0d060e03040e1518060d030503060406080304090204080f1f051b0d090b130b060909120d050105190321030e010c0e0906030106 67
    0x200100d0a581d4116a00007000c8159000f2480301a0349501c0044414a401034090000e00005da0340d64a01600e1100c1001d803a49642c504c5440d0011000501e0b000318000c980d100008940c0d4100d804216150001c072801c00781d50346081521848103968000c0700e01c10307101e00080c00c1d00389100e070031040d030003030310b0320720010303040050201d501880c03041c40c05410040d011001ca2887d940391742100006040030350840351260303121881d4030002d510600c1181e54520642e012450020f40102c1c0c803219a0007181209040006a0341006000d0040202614031010f200c4111060110460001d00305184d40a240003a4030315040c81c00202c2103501808058480300001c2c10b000004520a600540c0030b1804d403401c8905481d0340032114074ac0003440018016607034010420000000c51940094101c58040f248041c5035401040011020a0b560002034140c2e005440301390340d014810180701d0749004241c46c0000d400b4685017a0380e421580c0a204980c0060f210940d4541c83d4039203d06140e410007405c03002005490702e4076 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563574208 1250 563572958 563572973
    0x6120f06011701081e12040308030f060f03030301090c05040f0303120c02340e25140f0310080f01020d0b0916120b04181406010312030b04020d020f0403031209 70
    0x440303100340385c0d401010348003c4e242402200007840c401c1030100e480b40d440c2d1410700e80310381088441c114403034041000104549489404003c0e842e0028002d18510b9080c055244064115800f01c00c050010411000486a0002c01010011030081c0e54030002c50000d00c9116090b50f110009610440d409841c0c0354408810050f03a5040170031400030b641d9904508420034500c0c581255110010300c032001d20801c40c2080034130000300032100803040301002442da100c00a82d42c500541c002c40450302018045952040d402100440e00442c000da0b0301c0044030f0351441c4040c6400d41d985070001c201d940228420005a250380607120400d00116503803c03503444d010a003110039410f030907003900c20400e5070f8890820391400d030b82c03001180b018082c00c1030041c170700e94800c111151800b10744115440313000180101c2e42003001042441c1600e40c080340c0904442c9410304214040d01021050a501c03e5081102e068038170440e100410040c0010501070342c8561550a000c0c04031701d20009000d0300b650a03e40c0035030018060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563575458 1250 563574208 563574223
    0xd060e2d070b031503010b0d0f12090605090607050a0f0501020a0f081605070813030b0402100e010206010512070b22050d1208040c031e0b0703060608040b0606120f0601170108 77
    0x44d007018051030320a000009014000d00418a5005402c0c01040d0003444891800034229502600c000d41100c0c820b6201211506c0c1c4500c41c100020f40e091209034458034141c1e004203d03683c09542104d044e28002d8648180d145076580044605a5000840304100b980026141280c850b5900340b100c1c40d80340c00b00b09921842500307240a0100000000c1050800c041c0d481507411041d500340c3d11552080c4c5918008590800582d801d030300c0b401c070313181c401c80f096842000072000350318042e40a000340da4600f1050011070383d500d100194003070151400200b6010700c26005400c801200d000906e4400040440f810801d04864200300e0290039104480000328120320300c20f03001c441c000e20b0410000c0d82c0c0c4e070402c003142242c2901f0083c6080c05240403503900c07071010012041801d020303c2d13a01c11140c8920710160700b00c80c890310490001c5a079040001d40421001444903034811405040c040c27800c0c0320210303918aaa0405c480c140c00d00e213503080a10400b941d100580801c59400d001d4120401e5040c211015aa42074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563576708 1250 563575458 563575471
    0xa0e160e100b0a0504030615180506010e030f0304030b060102070602030a3b090c03310f0b252705030303101a070b060d060e2d070b03 59
    0x81280205003401000348400c0002c002e802881519080c442c071005100d07610030320003591041e00f04103440c01f142c40d01c8072030b0604a4581441d00d0080c0c0300d80744c11980282000130f0200f81840700134484d500c455107090010740f5180100d00080c599850452600c2d21a2050203000241194810301060040c160000100c0700c81c5443c504208910b1256a40e281000c110700d400d800c1c0311440a8040700b1a1280c0c0c590b40d00c12812000c84540b02c0603503800d4002d0036280002c40e404010381002c080d00102c00034640f11140b0000c5040044881310f00702d03e4035603402400d020602100d031540035401308200f40403083d4280c100540241501041044084402061070075800e1000012045142e015441c8550b8080c0c0e6500410001d07003a00d4492400e10030488010182d80305d84601000700c4024011440e250608a0b9200381e806020b0407030503294a011310204220490007295115583d0303100407070b038400c200500d0101d07624082094001c0708407020318240b1619000e0801026038003050041c0300d44c0300d1000544e0350080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563577958 1250 563576708 563576729
    0x90c08161a0c15150a240827010906021206010206011703090f130e030901020c010e06120417041211060c0d08100b0301080a060e030301140d02040912080a0e16 70
    0x215015020012404c08880366540921880c00c000b400059010b2018512108480390075180e80201c1c100341c548060841d1408112500c411424195800312030003440c4681c0f01c4000001c0e01c46141d502c80d022070340911101c1505820740420803020b50390401030766005d040034044910304202d08149040c0d403800740751000c91103580742402d0040d040d00c441c8400b400c41c403400c880502440103260320f81e50320790b1320855009005000d003e0510700a54055280241500400f81500745130811036107d02090740760141040b1214980f00b8130056200f2614006000500094018211b05403003c1c40c114a40703d459400e0640a0001807080e0011400301180b403410895440c00c10f24025928100188404090b90300f018103000c0001c000810401d800288640c010f61154900300320460407100c140e0750304d0009114485201401c440e4100003424030038842440c1501c040c001040c500c0c0c00740d440d420009584000c410000b6a505c0412400010714058403426109240c05404200e040b924140494450b80c0034984503032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563579208 1250 563577958 563577961
    0x390803091f0e010b0a0f0905150612040c050d0321020f0c07080d0305010e04020d0311011415090f011802040306020406051206060a050f031906030b07080f060f04090c08161a0c15 78
    0x2004007840c9d0719808030014592550703294800e04503646000255000d5580c1c055800c008101410a001184030b00c0e81c02d07480d03010060000ea00d178000020408020071144540034028440e1001d0320310058001488100c0140070300c141001d050310f140c1840d814440080500b400c00401040d10030524868025806403032a40c03000b4a1400c0c10b4078005120158185150b20f44180c40207144100c9503401d00401444801001e0790720814208211400d00351984038901c80b1076001005880c5180c2d00100303143ca1007900c05800c10360350b900e441c41281c0140e80081d0108000043c8120207402c00c01545a00c12070803100141842c2d2008401841401100a10707030b0b0240000010a846001c001000d01c4540d03080003080c400142c07685030049180c10143d80e01d0740440c1c04400850000303610030b02c03e54400d08014000001507041c00342007001400300d84070117441d094401d20021410241c244500001c02c001c04104403505440d0400c024041c0700c01c3d00003100d05031001d205544039143c01090b4020480c80c2456080460b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563580458 1250 563579208 563579221
    0x60b0403021c021314181c02070e040b2a18010903060905010902030d0201050106140d140a05151212130f06390803091f0e010b0a0f0905 60
    0x60800351102075480010700140c0c0c504804c0d141c2104c4000c071201244d0f1603a80e2501105a410000303240c03540f005640240f02c02d500c80305002e668810201c000341c412107544560362030103851404070039507080c0c0c0c100c2800d9007004107400c40302200e1141084104450b0160000f00310a40c240c602403040001c81501c80c0c481c880049a11428400000c1d54100000b002030141c6864024020a0346003002c0b8001d0140c000f11040d00740c01881514107c5001761119331600405000301d100c5540300714804482c169840f8400d09469003201c592522507202d0743e500050608242c0c0410f00480b40aa030304a01ca415039081c01a841e010100b8a402007070300382a070907a2540c8000302d840c000d02451360400d80914119140014086610402e45042c00180c07c072102e60302e83d0100316201c0c10f070b100d00070643c170320040181001c1d00082040004542c401940d42c1501e00c1000c0e0031032241070500c0d0101e07810461688486a01510307804c2885031030100035040f1400c080720b5260214043c010051071064800c869900c3e40080c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563581708 1250 563580458 563580499
    0x7030311010605060c01150f03080a0309030507050a06052a0f09011b03030504020f3c030a11120d020d0c030c08040e18120d05090a0f0f060c03060b040302 68
    0x3e840000c00e007645070024211414005c0501103148120107041c002d0001d0b401c1c40721443c40f4103407034012141074600100002d09074054501145c0840801c0303010800305001c603105020600920b481070001043c41e007404200c044038a01d00350703410228214800b095a00c0c0000020845211881100d60342c1d85460401005845000084000c0300740eaa4041c100c060405505510681c03240c0d208031403042000c24400d0a018040c1c1504a14452031402036466514610f16000e80e40524030802001040c8101660082410b0041a140452b401c2d400c058807051300c2e25008555101408418004000f0300f2100342000350707659080e10b4140c081c0035004c03180b40d00781485400c40c0c3d24420f8210644c1e43e07480e56601008074901d84101d9030712800000300c41981c03c100401240d00d041000070416030506004114056100800b40908021494401c8080d4140000d04640d0040703102400340c0180e924030200c41c2415010345000c0c2c0800000c161400d88240041b180c22400e43d03058a4040c3d03546c1544502ea408480d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563582958 1250 563581708 563581721
    0x7020307320312011e0306020715020a020c03060a0902090c280908010f05040b0c0c030702130c170f0406240311040f0207020604090b21010c1b0201020703031101 71
    0x540103a68401c0c414000c00000c01401e104814840409080c0c1c0d0b1001c2655000c0d032082617801c040d030501081040400e040e40c007e412090b000f1806113904007d450311060481e40000802805030700850914005450180030709580600d0200050102003016070000300c01110040c0442104500032402c06415142070100c42d01c802845280d50001c4412414040c0881410703101e151215800d01d8490300c030200c030314002d16001d40d40c800500c0000340c80d103072b81c801c6242e08100140303065844103116800142c1d50340440c541c160201c107030001515019401005010300000c0242000100651007404100864108690b40c00fa420079400a020010410310300143c1016104401c00320300a50004000c3c8880e640152101d810110b40030004004090310400590090b17240c06940010b040c0000c001807542500a0800d480c001001d1728402420341007800b00c4070f20f07110f0008505a646152a906554205030403140611f540c02c107c01c1101c01170340c0000c0d681d07015400300900300400346414540b02c003425080503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563584208 1250 563582958 563583023
    0x60402030912030f15010c0b06130f0f090b06030304030c0603050c04260f0c0d1101030e06071101140c030711070f06021614060a030504020a05092a0307020307 70
    0x302e589003000d00c0513107546030055441a0701181034403c4060198020001520140e41c04800d0031610b50b61401000031a940e0141003510a90b110150314150141910074500090041000000d00100d1400c0030405007000600445c002c0d4410042800481c035218000b03c100c4080d4500404c0e03690ba1340c50401118008c0342c0c00b00030800d0400300e500017118034840c11130203103910b01030880d48441c1c03102514070b56070f0460011441d00804171aa484000c529807403000c003003c0406040200e8513400d6124214500070003211b5100010340c0421000c080d04900380205403107000f40f031010450b0742c2070031603a0081502c4042c00c40b8060010242c080b100b025810b00290000300800000f48000030354662019443c0c00d05008140200441d0b0407004c22100032044401c030904401507c024144030015105030000d21000d40266072012155100043c20f0740d4080707885100c0e0240441c42642101442c0b501c0398480414100c440e0611000c0c002c0180e920b50000960780c4d05a0400000080c0c108408420441700a02d030321704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563585458 1250 563584208 563584243
    0xb150414010320100905061315050711040207150b0f15120f07091511060403051c090305030c130819030f050705211b0f10140604020309 60
    0x9225a10f09a0b245542c46508401c9503007280d0001c000020610400481c04140588018016400c1200192030b048022142c0e00b14243d0711100400c202c69462440000064000a5160108140110400350504090b10190f007020b10a5546002c4401c1c40c034a4540040c2e940c81e0080d0341075451807480d520185014012400c0100c1c007000154240c0e100e5001c2801180c1c42034082480000005002480f5801c82e5880030307030040c100a0300c01810940100b03c00e00b0030842d0041261900c10a00c42140039034800d4a5080d03603809246104156211600040100589003109a50120f500602202c0d4006d1882d07020560300c1e6074035800e400392001e20303400030b100c28415842c2205000019078070b8100c2450194a8401d101040141c00301c0b082d1246082c01003140d00700c40e00300f880d400036120b00350b05000e000b03030340a42c200003041c1101181f403900c02c4d0030070705654810340f2545c1d98440180600601542407180900c42d08c00c0400c2c07000306205020b00344600a81d8000001541c0c402d0602000d400d41494119 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563586708 1250 563585458 563585461
    0xb0702030a06091b0b03060a0302040902121209040c0f0210020c15010905040506011a0703051b0d020718020a1e090302120106080d0f0206040b0c160606150c0b150414 73
    0xc040784900d0301c04c8011210400c50000200344a0901425070f8455000141106561400e540c00d10025103280c003012600094501c40750500d085c02804480081c0c94500402902ca140301801c0100b030f5007095a51009010f02600c4903004d00da404103070501a043c05400150342d0318001c1c0c3e40f0500e0f0280d000011810514507a00100c3c0340d424903080706002c0d0b40503004882b62a46c070350340d5242c81c908024411001d020700030001c2c81c000a020310301610000c0400c100c9500d1140c404090707141002012b80001c8016000190188240c8070b081e401100101080e0742c2c214244541c50f4005003a8600c1c41d2007a1200c4144081507804039445250360320080c55018005503c19401d0180c4107010781582e00401e8001c2c05003401c442515131051002c0002c464403a8010001911603454401404001400201e030a24081140e4002040c1c6440400d102d244521400244549407404105100c0300754910b0208010b901400c80001c6900498481c0e0002001c01c100101c1c231010b4000200240541d0380d40e900412041070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563587958 1250 563586708 563586713
    0xf0e211e1c020408100b1809060601030f15091a0a12110f0616020102100515011403090d0537020c0909071202010507210f14040b0702030a0609 63
    0x201804850004803908904401800e05074000e901890082e10034640c8402c0c90381c04600d009400160156a02034031113980314100038034100c903050b130856405c013480d803018080c4101035a02d8482e0101c0c402e0020810000c114080e844c8441188c1203104540c1b2041c1c40300c1482c1c0c42d14034150030b00792400700010440002d0b80e9031402b0050b20001e001200303441402c885e05010b4030506090382444241c80340100003078030344040700c020031805400009051341140f003001a40030009800c0c0c030849000da903440b03c0301010020884001010a0302450340306c14a0503082c824404070030800a00d480040b60141031140d1101000080c030fa54080c40d804625800324000c4081c07001000c9450030480c0e03800c00070b0b4299988074050381e081c05001c0c0b2083d1040321207980400000c05c9821071404080004d548140f501d41d1802d40c3c60b4445840c144000400d0201a003190503a0940161300320711307508090403040c1010100e12501c000d004219000b288105800244005001c004554090101054503a44560200301003a45030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563589208 1250 563587958 563588017
    0x501110c04090c031209060207031e0b101502011a0918250902090d03030509010b09040c06030c0c0b041b03050d0f08130222110d0c030f0e21 62
    0x13840107a030741c0c0d021003114104440c071131050f4209541d40c0703800900200346180d4903030790081501120700446000314030740304001546c40120180144494640c0c0c004c0d03182004040d4a44510942e08981503a16080380000c81c1c2240560038201030300111a0349066a540102c4e92800a980c1007030b4031898041e41488000d400102481510b00c404146a10706a6581324450b10049104918200398480100c0c405980000d2094200a074001041800810408030b200d003c01e5520106480481e008016681c007884400e0341803240e50291041c51510142400c66501c030407042c140301500141c0f03010f40b08003040c0000e03054140c0c00030066620204496041c5116840201100300081400001800340808a420103202502d40000560010800307542012607400d0541010190504100780d0b948840b8551038810319000580014400720384041800c20034202c00804449038030708041c22180c0380c003d04d24401718002400c9100c60060540c0e1250601e0440c1d19040c103030041c105005081c90580d1f0004c0c406a052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563590458 1250 563589208 563589233
    0xf130f0b0918090c030a0b070e0405071b03020f072303121e0f0309060601020606190b16061e050a05011208031f0f05030f011103070804110a03081210030c0501110c0409 74
    0x1d640c0f00045070109e20100f109481e41502e0907000141590032040b800c1d400f140721302c3c40f0948070740102c40080c0708003e40b1504010181d40110003041c07800e135407070136a6204400307522000b0900f10003801810464541d00c003414082d550400c0355803800d140b00700380411090401c4454182c2c4c11848075403070b0310f0441c0510369100c0049a00e14010302640d4045010b0781011501ca1001591081e012400b2313a00344080c1000070b801c00300140081c3c030030030018100401c4c401e2113071003010f00540c0d075a43d802c2c4030001c502da400e0f1200a80840412441c1800400003402001101540168400c58499032a21070500142d2542c04408102c88090064000080c210303211680c2482110010f4080d1040d01e12103010307243c2215a400c0703440b201014100700140310310f88181005940a071251051190043c3c1c1640892024121a0401c440b03559001561861440500c0c080641c003001e0703210845400341c00c680d10050403400c2ca104150502040d55218000b64a05000d02e0120541c050002c01101c0781034104100300014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563591708 1250 563590458 563590471
    0x3020d110f030d0e0409050109020604080703030906050c0c0f04140a050a0c1409040b180a020307030f02072a170304031101050313020d06020f130f0b0918090c030a0b 73
    0x1e8000d03048003402c010880014034005a00c40d115036065040900014000d03000c03045a281d56162100707001660703101c018001800f5164000c1184a06510b4043d19104454024a09000080c45828000500021601d500480a07902403440303203140700110780508514035040311304042800070451000800d900c424850030440c0390920103008a4031090392035400d2120890381030801009000081c1c01d1075080f40502d03550250904489502c00d100b03011104005840810403150004284101c3c903500d401100c90080324007404500e442d60725920780311400038003030015080030000340a5000c181005980d8500a012441e8400802c0524401490301c2c4d50140c0011a2500740801c0c95280c154480c0041ea446184100900ea0409517580c0802c850380b00618000c481c1d1035003c020300c1807107074210f002600c040c050050a10002da4100080201c410942d41c01820720b00d0001e100100c07441d0341d40d105440c0d1640d031010021a89844228446043c505214060341d09881801c0c00d810802402c140030612621 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563592958 1250 563591708 563591719
    0xc020102060a0b0603010905060d12080f060609060d0509030c030d0b030601060905062b0f0506030d23090604030c0303230f27090112050601090c051c020403020d11 72
    0x2d845071030b0603040300d08140e00726400140500c018012610140e00898128200500a40ca009440c2d55050f40d005882c0180d80002507010382172003070004c40319000355003140d0308070307101400e1220704000b1500c00d014408440400c00c0e00d8a01045e1039050900407920480440011389a80b0f105002c00a0050302c110101c02d0b0281c851000001000e0340700c0c0080c00f0580d40000c0070030b841c1020703600341d065a84c6071030700f0305405800000c0c1e40b6601181704d40c801c5d40a4105640342c045514074040c010581081000340c800c01c00d101141040da000d895040d40411090b410660800d900c804000000c50703c98000d9800c020481646010040181a027181203110100d42c2011080700d0001380c0c0c0003e42103405150030307032409000c06000a90075840f1400d051401c0865920360940200c180000103482445d0a0344a01404544030a04005100003404014050a4090f10520840701c8010005010307208100c04292941001a6610125a1140c0444000310740051002c0905007160403c100c1005540443c18883d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563594208 1250 563592958 563592961
    0x90102070b010b0c211c050603010e0a020a05011412072102071101030c050d0f0606020d0c020f010f0c0c0b0a03060e0f0c0310030204091b3c050d030c02010206 70
    0x3e0b0140081314000c0e42c40401510300c0c10750000303c03510aa210b4150300f8503c08400d00619554417501001d43c0c2460149503000704040c10680c05040c211940c40d90704005680006107544090703100c80d10000f04032042841c2520398100d440441403402d01441c040e42c0d001030b082205200c46030303034400c0c0d002c00d002c2c82154a8103040e402810036042244645c200040c402004800c0c4608203600079800f480c1000c2d04ca042031454281140b603400104c0317040d84c84142800b59203031020f01c0720070780c108188114840c20381462540c0140580010340703203005012400341000300c181c84034002640f00780e0000800710352040754808126202c0c032070101c640d0081140040000d140400c0021084940800f41d4016818403102010b6500c4a680e040902c2d03100030444941c04509403000401602c481c0310ba407040701c2c0074001c0603505044082c1c06100c00c02c03150340003106000300313046020019542030004c908040074161640d0001e44410710200c400c1865984041c1d44420140c201c1c5041c15081302d02404414400d03406d56400703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563595458 1250 563594208 563594219
    0x60203040f03110409050f01050103120e130f3e030106051b39030706080a0b041d1615120e0703022709030405090a05060109030b090102070b01 63
    0x8900540c8101e0000849407101040403440c81240009826005040030030fa404107522070350300d440c0c035204611129a650310300400500480740600f024600252600d1080507480c2d000007402c214484407090402da42c2d80c05a018010015880919112400059100c00c2d502140c050302603803003080500c03a148218101030700c022588010807207060302e9480d1521410803044d030314500301201405000550600c02c2022400f0300d030076607030070043c03050b400440406070310100350519501c8000505200d5003c2d03807100c80c0c20301c03401b0f4221054981c484c100d0030000032050303203420000d4040e114a110000e8008110700b4072110b8410f01244021204071442c0482910075601c0313a0145e0380c95004051303500040d441c1d4100c1280244240c0009040030380750802c0f02d0542e9201c0e000145c24501106030040349a03034100190380142006000b0f140e000d41c2c114050f5040502d45008142900001850741182956a100040b5071360700840200d00a19044110801c26150224802d4001d5110020544a140003000001030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563596708 1250 563595458 563595463
    0x15050120032203030f03050f0403030c17010b0901110a051f0f021803010b01020c030c0f45040305030402090402030102070506010b21060310110c0307030314072610120602130602 78
    0x40c4208c545d00b83d601d40c1d40e924110010042d501c085020062000944000c0358500e51031240030b0004406039550303d00c2d041740094020703140c040d510161394020075020804100d0200310114145088007290320902640902000240400c40d160340d0100e20105010300c0020f0000c0e0302d505030102c141c000304060401d100040e80d50320402000c02d68542d0010007058814100007a803403180000c0078005246480041084100105081f000b884071320101c0c0310540b01401c12a07281b46900303911b1143d01a00d9003082d480003841d038440240003034040c0030f509011900b1500c09504550132150480180ca115503190030382d180a0350b02c03480410228090803400100c2600000400b00c1c010880103006007140140448594081c0c204d4601d8111a84011f00c41040c2e00d2a0500040c0b0f08140f20b91b40000721007003442c03803480b010500500440708108a50a404400c01400d074504419040c035150008801d5541404c08000031032282c0101e50b030714420710007000806c542e5402419255441c00d0b007100c000c945902049a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563597958 1250 563596708 563596711
    0x9050d020307060e010c02060d0b090711030d090f1b06030f1104140a08070b07033009051207080702090601051204151503140115050120032203030f0305 67
    0x3585900b04480802c00daa004061041e502001030400c1c202c21011900082c40030b80180c41408001500c405a0104529040400c25401100c07401c082500c8000324885503524000c501c851000799945011043c107005030701001c801210b0380f013030070201c240c848045903040429541c03141b580420700b80100c510400c00d40e806074101c6201ea5851407820300740b44c01e4441e410f030000109150b4116841200105a071078090117408083d00c05c0703004955480c0143d150003440b030b0400482c201600411400c0c0d0200c1e0170f0386648004802080040003244c103002a05203242013402c280041142c1c0301000a800e01000701c4000980f81e114000c4070a05920354481005494912a6250012a222203040040e000440000c40c83c80040142040001c03801c496002c04031130f11701540c005a40c0c0300d52101481d00c040e13100340500660b24400ba8841c210480c58400060010140303501c0c50401c0c401c07040c1c1813038144001003040e2024400444c0001e0a00d140c05c111800c101c201c0c900003500091245421400d042c2e0190266070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563599208 1250 563597958 563597963
    0x10b010f091505090f03030304030503160c02010c291005040b0301090320030904020a0e030c040b0306130611030c0a090b030c031305031e0301080c030c030a26070501060609050d 78
    0x10b1140c40300c1a08030f8503640203140c965404400e074002d0902c0c03902c080010314480c921940300c090707890400c04040440302d2100a1914108250025100c0050341c0c8a190340052661008104844da105001151500210b03400404200c1201a0400c40c481110110050480d04162020420400400c051509903034030941c02501041e840d90310b05401c0030354071600000c0a1094002e0700d042905900005040c2d90000c5c184200003890501c4042c2c4615041c0b0401c440c0000448041241820090110b0b4075a100142070041d81e490810842e014000507401c00f411284d41d085140d9070728600200380064035000306103d400061900400410000a030008403401000c80d00042d6065980c0e00380642c1c8040c1c3e2a0104941901040c402059450412200050b010050040b0243c6030360504103d030303150071620071100303209900804203c891a140450a03401c0c198100e60940402e41e804501584000c00f0003c01d81414403000680c50184070301036001034140c90340b0b80d460b00710065540040041c5024080d502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563600458 1250 563599208 563599229
    0x90b0403080412030903080c15090105190506062a150112020d02060405041d120901050f09041b020a050c0a140d11041409011d280c0602010b010f09 65
    0x2d10003948011520302c0c883e440391a01040d05a102e60b288500782c0c0101e05107114070ba2048841003800c4240c0045a544243c00d240200a103291607038010302181401601204040d82d00d0002c60101d441d0101121101003803900c6010b10050340754503264040f03041000f010300d24099462815200301900c0c0740c681c104e52104032400c65024082d020403120703080410707049070322007002c01c400141a140c07030003400d00d42d80bc006c8111220100000c29141804c4c80e5110106240104000c18000750703801500b42c0f054004004c03012500c54003450301240081990b034801c2102c9055071aa03044100d680010b070390b110380703200e40b041e10140007010f001d100c1864580c0c0203000010303a25000f03400c03450400b5900d5079051070150540e903940c40e00000c00f09084a100d88840500c3c41004002c111764280f090252408000007000c80581d2000103010030dc2c0c0ba400780c450049a901d00074501d0b018541402d6070b0f00c0000c1e5801011108403a9a1048043c2c0241018560706001ca4050030b0303800c5d050f501444180c811034005030803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563601708 1250 563600458 563600467
    0x10501020d110a211202091003050604060302030f0a11010e1003020d0b0a06090e0c1813020702090c191107150203130909031407050703080f0705060a0507090b040308 73
    0x2001d499050001800030003c0c4140d001043c04183e008806081040003811110804260383c0002000c8501e0319403000b070218010072951500303840d04a100d03260160203140024868594200107406041282d0000e07500d80306d800340c6000c000e000441d60214244c41100140a1518604010f403030750b100c20a44140c2c0103103954041f002d4280a50010100d5211145001458000e400c001a04185068100c3c0d000122240c1d02405214142500340d034000071079038101da00b030500201000b06420b032301000e01405542000401e01c0c0100640d01a22111031380100881d80d207203010b5203000d14075000509829039607440c14000d0030b0058052401d51080e88240406001c8071401c00000c180718405408a1a0031448100303c0444445031041002c4080c2c54000c101140101450900030300c52500750203004851001080309500090700040d4000440c2c2d4410600c0d51070318540162000240100d44d40602a409988100b04d02d640159008601c50f694503250f003181c3c540c944c0000c1c04140241d007c003c280d02030030003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563602958 1250 563601708 563601733
    0x50a0902070201031401081609020c060c280503061f080a0510030209010b0c010e0303070f0c08071406090712030518061e0306040c05070803061e0a060c06050a020301050102 76
    0x40040030010b0041c1804110002d40d4070014580c003200364040d904a0f005080340f85400003d000b1050000c0100300740c01d5060001c20708a464a4120140110000c0c1c4000030340280605000b1203201025107c07401840040b640c1103401912aa03c121100c5200e00c2c5070a29120380001000071001900409554030443ca580e52074010008000103006d07458181450079001006a0ba40700d403c5000e000090b042c25101e20509070b03141d00b5558101414603480d0800d01c20000d05650000000301e01c0c4c141c0385014100756919045c07a44c45031040010150089458507008802503100107003850040d0b04110455000943d50f88401a4203c8285001000a076081020016000305000801e04030b80000f000a40340142011120491011030b10080501031408810814240741620406412456030f040080c6480d2150fa9114801e2000400d6984150f0002540342e10500c1070280c070341c03d6444c0142000d41443d48444000c3d148a4400740c08880150504000548030201c0f030003564121601a0014522510010f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563604208 1250 563602958 563602961
    0x210c0318180f020904020d0b030708070e0f07210902120303151909050405060403030c0e010f050c07050a0803041a13051c0c03061b080f0109020d0b18011e050a09 71
    0x2c101c0a0381030303001c0c009043c1568070341c40109140c00c0c6203440010404130020905043c021564032841c41c60b00401001c00640c0d00e1070500c2070303010b05424065181c0b41c0c0c076400240c0fa120070355100c00314041c58001c880c200a90080d07104640d0070b0f0088820350144030703e51014a64a102c00c59410340094100c05050560b401d000b12140040e003080e11845c12880e40f5403100008842c000c8400303803801e030b02039070501c03060640521075100810258981500c40301002000680400e10190500080000000e080009802d0900042c00a07202c02041000e1032641c48500f142d4a40241c050b04071010800d01110130f00981d92012030310842c0385051050301051400e020400000704045590400c4050480e40a00052500804801961242000081c0074000036442480d100d00c200d003040904c0100c1c001d000034100d680c400c1c981100da5145026035a172403440c000700041c001191000d908801907180003001c4500d0029882c0c161134401d040b040c000710302404030710070000f414402e03d40c2140040500344414442c0c2d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563605458 1250 563604208 563604221
    0x6010809120f0a232d16050c1201020a11010207050d0302030408120108030d061413050c0f12060906060f0405040c090b270a0f050d210c031818 63
    0x1400d244100d04280310403c641441d03a004050310840c0000303181c003991014a444501d1403031740c0700300b05058a2640807520302d09100718444400c0000c140f00e641030400500700000041c0b400c1c05441c02d010304400c0b0300042c2c00b035000720203640c001c540d00240e0900fa1040510a80d00f51703981290040400e43e00d0036074260000c0d4005001501ca07024100507041c0c0daa0000710701f41e8000d00a020043d940e4030180b00e448012102c40340c03c1104140d01420b100c40040d1717200880e00b41000e03019075001400340c0f00c0700c0ca529007601c28203102c190301440215101200458030070089209000c00c0d1484c0c2d0700e55480200300903c0e48100a00303420986018002407006060580c840117002c609800d01d602c0c05611500801038070340061120b80b11a00c908403a08815402480b412511540240c504000c181c0c1800031030217003001e05001e01405003401c45858014441414602c02c0503044401c2c3c520103c580f4101e0085c5040c4445000b500890b5200d1007103001d00080c5884041110a04005074810408116915000d480f8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563606708 1250 563605458 563605477
    0x20c030c15041707091103041a10090c03050f100503030322150c0905041107061e050f07230a080a110319060803090d030c06060906030b06010809120f 66
    0x1810b020214050080001e1814103943c0c40000303010075071130400c1d0903041e55160225280c5040003070040c00b000620000c2503440d18440c1c10158003842e5204020710892040c41e511000c1003906284c80d00302c4103078040d401203019001350250000386507100144d5a440e828036214042d016441040013030b0040944805c15041c9400f18002e40080c0c0e09545c031416140081e1031010088196680010365900c2e0300070340020014007080d201440020b5040c40040558020210082c010350346a8003041e185005c0741d0f008aa550750034110400c00d50801c1e0a03000c048190448600022074000c40303040c6c0070900b0841d070740551016000150b62500041c40300441c0c104030301038160340600d61100010390502c540c402c040d5200c2c040e035003505000c0712440b5030200c040d6070b1b140e40f100c00c0e290401c02103200980c55005034084a9038060604890361010303031920340d00400301340e0303c00900b03540b801c080441040703045402070380104400d07039031180c1c04e07103412003d5a00d0305501000d4490108080080c880f40202000290040c500b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563607958 1250 563606708 563606749
    0x5030a0804061e1a010c0309170118050c010212280210060e1f0b041a040f030804050f030613030e0a1701020c0106120506010302060325020a030e01020c030c 69
    0x10703400c80103107511003c2c041d81c108481d071128588084000c0d40704c0d2420300e000007441c211b604a400c03074401400754006070003a02c2421640b00070340c1840c01825009030111a088039442d00c03e00e2214104262501448a5401d0040c003448800201d4080c00b0010f132510030452001d110b0740e0402032107050008a203584042800c2d03000d03050080100950740c3c03044400800c1c001800e009113103070083c180703200343c1142d0041c0307000503a05140c2444503000e000150f0301600c0207040382c80d496021031642012107000e41c2d40885002403024401004110200014108460064540c2200085960201906e640e41102c00c00791040c4402e22030408030b8803540101180c81806050710620b1519418400109102c543e00101d841c4e4000800b00452482441080f00502000740103943d292a00c2e07492030b80b01c0c4418840a4032400f03011001c11945106800e590720040c110078800401d4080c2d0721006502c40301021415008906206c0f46000c181d40013269007500c1050050240522040c07410030824420545460200c605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563609208 1250 563607958 563607971
    0x170a0b0409051c0f05031b070c0f060e0a05220b0402070c030b0105030609030f0a1407060c17060d0605090102040305060708040b010911030c0901022503060e060405030a080406 77
    0x303803900e01c510703419280034101601445000216001007080c1481c2200704020000c1d16001c802e6900409503074000280d0000e5803000400c03a21026407a0050b60720103407034007144210000700c5d098035500c01800c481c0a078680103081001c002c108041c02042c0d2044070f070800301001c100002e0340d05000d00700890707074170b0760500003a4603600f00c002c07a0487c3c1242e10200d038050b0004405000f800f01c80c0881600610f000c500400302c910700048075988074020b0704c40583c0380c6000401e0308040b10340502c00c00540710141100840c2c403510681030400140c4104901c51001c56000e0410b81584808070f11594414840a08880142c0140ea0386000041000500d520015542803202100041051207014050707092581e503e40d40d03050508144030100410392080002030f00c0c050031508041440030650394000c10b0884002e44907402000140c3c00d01400d04010300740fa1007010401343c1280700307948400007903a020fa0020850150380d0b1505036076501c401d4030040e005900c00d200b01100284604501c5901511915021450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563610458 1250 563609208 563609231
    0xa140a0f111f2f1e0403060c2c0307060e180106051207031505060306040912050c100504020a05040504020604030b0c03060f0d230106081e011407170a 66
    0x9501c00900c84140d5490708007000f40540e02100c2203d511000043c410310364141c0d60b03c90f581600c1626011a0b9030802c1407221001c0c89000d800b550b0042d0b421460501040c1080300006148010083c070801641c4902c10105510440c0d003985160b100c4000381c020a00541400c9098070208031050305190300c850500a8440e0120695007840d000b402c058903642d44940c1da140030740c10000e0300203050804151600781c1018500b18058180011031b036003035aa465980e12094045005084403407030107064103d90400c0520180d5200005141e4500d1031001c0d904005100c0d654541568030941d0302a42c4051000800c0c40f040c6080e500140e04540b00900703441c5403599a07a6080d485510440b1440f90b00b86000c420400e060400420704640001c0441d04481149215602d40da000c125441d43d21030071450300840342900e14070035402840588502c204440810011445800e0743d44c0800010074401e50810780c8405a04801041c524000e25440c4c86071a003500c641e0480305402480100740407011500d90005090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563611708 1250 563610458 563610493
    0x2001090e0c040f1401020d230703030b04090b010305070609140405090c0d05010b040b04020406120e07050415240801060302280e0411040b1b011b050a140a0f11 70
    0x10512050810082c804d464006420480050340d140b0601c00000c2e08042e805140148064001401408243c0c840d982410b01302d004010241000b5001468842c085045c80f9206054904a9101d40c0440706695220042200c405c0040e00c01e2810f404809007001c0e4007840e0030342005922450721400c48028030ba11400151a98030303000310696480c0d640b02560207150515014803417207200c1c143c90541c6440d1914000900e407640d0401c5141c02a5541c0240d81c101c1c0005020b65001000002e00600a0011030355807803490306194452462649042846808c00000c2c02d20390186c154036540360381082d60300c1c02400303402075400080a0b100250255200a114510b400d542c401808015610160b184044070301340b10454012610704200480148020846040442c049940c01d100c0c50085500101e0840c503d54050000e1910242a003030880395988016907200c009800314440c01d85c4e4002c0c2543e200c0c541802140329054462000404507494080c507213000702080c0c650f84203008122412040c90118001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563612958 1250 563611708 563611739
    0x3050c070c06050d06080c09040b04060f0e010c080906010e0115050f19030f0b09070c1103010e0f0d03050108030304290a0c140423010207120f2001090e0c04 69
    0xb004184045a640c2c6145203d12034a401341600d10004d041d800d9a00e8000361140000a100800c0303040d455002a00b000305980000800c140a10000d0180040383e01009029040c02101c0b5030000f17281c03000245007000005100d90484409012500d0103074240026040360040ca80d0302102030040800400c40e50914210090000d40c1c1c030018040310242c1120700041c190f4070015540458075092801000356070b600c00c4030154001a241c02c007103542d51442d10f404071020280015140e4107500c0d1551098090002081903404104480d080d2a0002e401246c19030482d2000c0c060203200340d10520004000902c4041d0724409030b54090f140d4480041c501404600360f03c1c2c00c541480e0385607102e401c1c5000054115200c4131803841c440744100e0070181008280400321015601c41004207003216808215a4000d000b5500941210701c04000c124000342014040c2644010046940f00983c0702c03201c0d03904000d4100104140016980c0e80ca269207454101204000c02804c81e142410080100044080c2a01e5a22 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563614208 1250 563612958 563612969
    0x90d0b0901151205060105061308060a0b011b0b270d0c06060b0c0a06020a03061e150f02060f040302190b1b03010f1203090302060c0318031c03050c070c 67
    0x802d000920201c011022503403544020081c6605442c0540041d6010411034103541c410b80300035480b0019421118a0540561302c01881406000c05001c1c81c601c0340e81040c1e8962400381c8510003114050101001e103440d0107800070305010008030204d035002e601f10220f03107078103a5040c89041107440e1010031907040529800c1600041403802b14010100315850085400904d039001c8400d0906468640043e210907030210020072107a030008404004a0113544070b00007410b410700d0302905000c1c001010003010300c198001c4030f0202031a090f01c440c0c00d500c119601d160005980d4003504454075140d2607003c52900c0640101e00b54000e414a46014514000d511441e041c0182d0003510b5900b00a4030200c2c2c0c81001000c41d030401901000144945210b0040321000c03a1401e40d62511494500d04045401203d541c1009600c11400100032408000000c0a0046482411703a1060000121420141d680c0c000b4480c1c0c20b0301c0103040e13003031520b90390188d0b0103950b0003907070b6503c164580f03512903445541d422034a8211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563615458 1250 563614208 563614211
    0x30212010507030506101704060e0d0804030914010e06030603070503030c0d090e07020a080f0c0601060906080603010603020f0d02060f1902121c0b060705120306010e090408030c090d0b0901 83
    0x10410b0642c2c2c1401059002002074410f4460a00f45040003450380703015044510343c3c808a80003240030081981e00505e1030701070400540b1500420110b005141d27200544056000402d00100840d0a608004142000b844140c6607031440341c80d90390600155800007019540c0c1070040e420005086d0702c1c1030004141c40140080600b45440102074054210440750300714000540c108000c0051050700007411584490300415034540380e84080203082c049108004640b070050007040000581250010600f00c1a11180e48890320540d43e003d0a00d4200e43e05840301a41c0954084007051450802400c030b8400e041c0060300c02d41c0362444400482c0001c1c0d01c815081c03841d10301c507140c404281c42d50501950040980480c10f90b45008901a024001200b00241e41070440c0d6a9450403041c5965400c00c86800e543d0101c181da40e10368505d003086045030411180b1034003041c40014010b14921300618014800c95104410320b09603110300c0705060950300002c001c150084d03200b85082000c45c50004041c3c1c4a42c100000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563616708 1250 563615458 563615461
    0x606020304090617061b0c120405040c0813170c06010b21150f010c0b0f04060e0706021e01090b0406020414040902060d0c14070c14010e091308040302120105 69
    0xb00011112150700c95090b6459002280740241008a0019040249100c81c246601100300880341c107440340040c6200d9510030152001d1103854013001400031210f08550801070707c1171528043c1c0b0007a0341218070440b21442140803000043d42c0301030b2850b0a6242c02841c5003061600a0350b5407401ca03007070300805115000440c8040501c050310f0069a0203460001000101c1e0508644120050710103c030322610421311501c814140fa4030400900c125140c001c0c072002c40c00c1c10020000e8402510551342928207a003030040e9066a90300008060040310181e034010942402c6626042e040390040ca203094180355290f04640c408281001c0c006405079008030b20040e41d5504e48035401541d0720040d202e041c02582850545d80260f601c000540b84808450308021078601c850a500f22020141b8104800040b00042190824440d51001d1101070726501c04d01c00d08a00428401503840b024400c00140d8444106400100407099441911650038802c035511810a5141c3e030000c0e8400030000070585035a9560300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563617958 1250 563616708 563616719
    0x14151c0506150a020a03080a09060914100b130f200c0c030a02010509130609050703240e2206020a080708100503072c01120506010602160918060606020304 68
    0x1061224a810a400000d00d0f060a505001e51514004071018003800800d1001070b82d500c10580110746c6441d4028401c00240007140b5006104e0b410b0500700e92a64070030981003075004051441141200d0000401e683d01385103040c03000d0000390841c04250245241c4441c401d0003041c80401003040000c9511503415115100100c1031864294a274400d92301c254400445180543d8225080703c5840742c007901d070808910030030b07040c01d4050044c66101a03007062410f82000066a407662150210384500222140b44c081c2003140b1401c200028055805c55074800d40100d15400341e2103642a4810f0700070118511030081c0351b1100c1c0200d8100041c8000455100c4c42001010f5a01c07080741948240d803901181002803c15020076a01c003110300507890300701c201d0f90707035140300086082c400c0c0c85024641c0e00109640da12950071586400c0c06600c01c0790180309800c004100a0300104840074144d8402544504041c0f400004001520384da83c505030080d011907940402150300f900580c0c0152100342c00541d0b40340c0c41e15 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563619208 1250 563617958 563617969
    0x1502072a060f14271e0f1509010c02030f12071101030221070e0402040305010e010501050904210c0203010207030f020f01060f090203150d03020606130614151c0506 72
    0x1c4224001c010300d040e00c0d041c0301000320702030700e503008a00d4454070340c41110005440d6004916010455000f0149001c01907205d0b200034600c2044182a0b46195041110340d05001d00101882c05c0d492214005000f880c010b548103400c4460003d00042c11600c9240707101003502c0c28000d003240b5000c09000300081a005011001e01c0344c1e4000e24081c0790131031801000c811095086200000207200d1642c0340404140d101d4071850107000b0600008004654440d070341d150041c028070800700310080d41c0d42000c00000c0c040c07804000062069400c10500703070781340d50400c4950000840360245c5405102c12441c541015031024406820481e11a840d02c03401a02c1c02c60001e8580300d01f403d4102c16681c1081c10610183c8030f5150000212040100056100e85034050078011603e2415002c0e41c000c45000908070600d0350000742c0500980c030a90324400001584460a42039030b100f4043c003014600a05048000da0401c21fa00002444181301268107000c8050480b00c0e007602840c2a40c5030644d100c0007804294600b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563620458 1250 563619208 563619227
    0x90f092a09010f032f060c070302130501050114030406140405101506020318040207020d0b01090c230a0c0507060201091a040c1a090303070605010e131502072a06 71
    0x9580003085583d2442da075000960340020300c4012000441810b451407a940e40c0c05510384c80b54020b01447c1c69000340c1079010355980242c40203900ca9450141d80a8140f511840b5840c1a1342069640c0c18803401c9081884c007182d0b0011340215080c2d40d5034070740b1100318080c441441c3c2c002c903c664041d00440780d4101d030180645207001c1c4038104403c0c411a0421009400104481340190381c4040c030b1800c42840e030005002070084420203904012003006c0e000030040c1e1045024185c3c3c001e803108010341000920308840c4000c1980b800032042c4045450200c1d40788500d00039008844052038490381550455480f10704200580c0d2046002d42e448240c0700040014001502c0480c080d0f5043d0030785c05203015125030611107641c1c414072084d09654240c00120043c03040403214100f4005d01240d076644003524002000b04400d101d4550200c401c070b03004c52a00041410021707904c40d0040480c00078a01d43d650300000a40c00050200e030001c24020342c00382030b0300f903c818051000c402044420b20107440d20402907c025070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563621708 1250 563620458 563620469
    0xc2f01060b0403062327060a140c071109220b240a0e060102030712020d110f10110d090804091401030b0f0c2106011d090f092a0901 58
    0x40c561000d000c40b824440305582e01414802600d1000360381e0303442106c820003140d402030303400740508800c00100860319001802c1c60070b0402403000c4999207510419004d4000c0280c0241182c07524007550342107140c2800503541184600040c040324402031504601d102072004400c8400600c9041040440002d494501310340e01119501000c4040d06500050030489181c00b9080c05080900b000c01c910f030b44200143d07002154440d03c1c903241c1100d404da01039914190000f20b4400614500c882c05401c05001c60012040c085140c010031a182c0401014009042c0c441d541d101c1d03062041c40000c1d4280c140780101c0082900505605a070b40e8140801030307041e204100200112907a6000c010000100803542c0c07558010f0104a1600060300c2d42c4031180414480d48070071004030591080e600354403042c40c5841a0041900b41c880302c2c1ea244c0c0e9000003040400d80314aa407503108145a0020359000c1c1650815a03102c10000300b580e45205890080d2400140004600c500d15090202c0301001c604100020b0741c050903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563622958 1250 563621708 563621741
    0x10210b0418080f0f07140304030203060c0c060a0506031f0b030d0309020a03080306180718091b0c0c050604060815300f010c020a0c090c2f01060b040306 67
    0x200e598a0b82c501c50f1107030a02084841d82c00241d00d02944404105960311180c1c00321010801c1d54590103203a41d2500107000c01d9200340560f5000c22204001c140c1243c02a0100c04003a00e080c0d030b904c2a0401c018040100069054060751030006031922944103220410340f070560b400111054810245488d042c0107044070002d1500c1d04050740003595030400300c030b021a07620004056480da104800300d641035200700482c03400b1440c494140000325401c51001e80030140014408103499039119481002d0f1a03c2400b00c000d001c0d0280c1d4841c031b030b2030701c20f60350f400e90a4003445001c4001540c92000c00d22541c000c2c5d010100149122b41409034180041c212060003110407100c0d15021131b4014940301c0c80c081300e20411890a00300302d041054458051280c2c41030504c550000304800c070380800c03000c0d4580d010404c3c01c50b1030181d2071501143d49013403031280194100c03655440c01c0c0300717018100f210240d544890b19420116810340c0042041c1050034007a90380541060100c6e01c0d190b80c42c42c80c010b403d5910382d40120401c607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563624208 1250 563622958 563623001
    0x31b0917010b0f090403090306020d0b0325050d11181006020705060406030f09020409050c030c030f0c060a020709020c0d0f022e0b0406080d0915020c10210b04 70
    0x1640c8004030341192800c04c41c0c007001251991b107400d8030f4001495200030041400454010f01d40705013984000514807003a01600d03815440250081d1201c000e034152402041c503c880284031a0030b046004441d01d0313119040c00e02c0c0311401600011240520b0488080c0113441b600104014180c140701c0780340040c40c00d800105412804c04000401a014900954042581d00c464001c10022590000f1801c00e40143c01000281c5440c280340e030711031484c110490b01074030600310382120f64100054940d00ba100524090901d40b00c1e03d50400c0080e0b4040c0d0802d00840c840c400340403c5d2416144010a00c2e0b8241d07030020030041c0b083d11006005443c203441d40314255000595000100400002c0342107901d00400f03124692501600d10020003080c260381c0380d030340207490060046008280060380701034800f00b58880164444d40d51031030002e24465540e41c40010b030048440e041031420400b110010786841400c10300b002403030164515444014000e1240c1000f03843e1f07809030202d8109486a5031022220107030f0103004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563625458 1250 563624208 563624231
    0x40c0b130603112107081e0a02030402010c02091503060609010e06010809031c020d050604231306050c0307090e0702030f1e04060801091419050601031b091701 70
    0x400300309224010034181c64501c440c0481d04a24204c40d807004a03d14000340c201c040e0104c140d0741100c1100da1038081001e65012171440b00c96440c0b080500203440070312404540c1d401d11802d019420181041703041c0002c0841540050b5900d0318070510034a15800301c5c08081308400c0800d0b24045004e07042ca0b006904c03c1e4010b000035000d65080913031020081c241038545440d14040c440c1317103203e0227803401c10046000c18015076414140d00102401e00c0064428003450b161941044220b9940402d9810f02c40c0d0091b40c1226482058000c0340c5d482102903d0300d503400c211030348a50054610485441040203000001c000c0b00303a8205040c074024203808403500010746030402001e5030300c0c405d8401c0c01c10501c102042543e034101c0c422948060030485000596240e941d0395501400901080c00760444850034081d24410b8110901c000e18401d4200482d8403d901290782900301c024000680000d04060b141c1410080c10741d03084010340319161860b950f00041c10300d88509004031000c054100c4c0020307411705582441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563626708 1250 563625458 563625487
    0x3170d110306011205060111030a03060807080102121306020d02030c0705010c020106050a060c020a0b12270d0e120111090117060d060c110607020319020d080c2d03040c0b 75
    0x140a602c413000080e40e4441d8030041c0c4004c00006e407a944580300c0051145080c0340d00d41c001a00f1034140b64100d0700301c50340312640d1600340d0098441c00c1458820340d400203180103090080e4104441c3c05040c00602e002100c207820002c0c4d1b40100ea2510440e0000030302082004000d11030400200c07a40d100801030107081000140344a00244510400c0025108281040d07540f0b40840100810200400c580d03226400c50701c24840e5a02201d040b015003900b100800781c0e13a503110140407021110500908888401c1207000e664803002d80001540003500d041006500c95030920914501e10360520711103803160128000104801c6440c2079504030100c0507418030620362600c0c4031220605078810b1011480c015030403000c507200728a07500c840c8001c0c8135400c18031080c0364021006000d903d07156040b255203031607104000da070340754a0346099200192500000510600c1c10f9405400704108480406003000031071480a51031481904e14481000c40002c1480104201384c80c1000c010132600001c1418000c6407500d0303c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563627958 1250 563626708 563626727
    0x705090c120f060301110309072414160501020703080604110705120702010c0507060f1418040e010e01020a0908011416032c0607030b1507140703170d11030601 70
    0x141c281c40d8840104502e69800e4106c500c180044100c00d41d00d0380707070100c0f401d5030b9a00a441205a01012441d0300c80d81040034218070001140b050701d941c4548a04040c98251a5003c3ca0100302c0501c0094105400139000b03000500516000b42e450b20a282044070400c0104c511682407072624035800c01050001a50118084d010f49180508668480d01c107400160b65182030f00c6401481030261003004980d0079000122000341ea0407a5441c0b1482e00e03105064002c1c140304000e0890162040c40840d40064a080d8001c4408804244004105c008000c0d100c42d0990300103a44c190302003a40c2240c1409900e2092158240c4019007054810040c28910007042500150130803100c100342e103c0d6401544034074850000041a0240403100d52160803074049652100416140c00000078100880b100c2ca42c50101d0551105a025102c61890000140c1da02040b45030f02548000080c0528080040804c0c02591a1001550316078800c42d526503985007020100c1300d140d48c0c804107000c420301c180701059a000c050074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563629208 1250 563627958 563627971
    0x14011403041406010e011409010303080114030a05030408070311040c0504050d08130b0a030c030606051c061205030403030909060b0712020a05061005120f0d0302090607080c0705090c12 81
    0xa5640d44450070450500c41001a00504520881000040c2140e81c0c881c00c2d412111411040864019a001001204502071001400244400c0014009400d840743c0f1001e006800030201c0e01c2c08100c9030b6501e420350700b20b40e110410a80001d0780803c280705c130107000c09400301d004a40801204c0d031646030103480c80c0158000c450103201d0740d5502804201c1c1e110111480440c443c0f41100b41c642d070300c0e0100c2e1065400400f1000000341008040c46240d4000e003d101c045e101c01c0d4841e01e0809101100411a017070301007240c48440c0303031102c0d030005007100d017a400100c03d540180701a60b62a1304604000c0c0040c80c20303910203074149103441b404000001c580d2090301c403201d82c001403050f4031034504d1008170700c0d241000c0c02c089c00900030354050141d6a4944001c4c0000c4032015070706422800580c40307030680c844050244001032500180d60300c10b040f61181d802071141401c01002c4031f060450f6602c80c180300c0d410103501c0407895400b20760103002c00d10b030401c003c680c040058100145804100c401d07684910701c1c0507020707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563630458 1250 563629208 563629247
    0x302030f1305070801050f0a06150906030e030d091a0c040f15052a060702010e031c14040302070305010501170a12050906070b0415020702011e09170d08011401 70
    0x41e41040403e0021100a11424000344540d05041484550b004004d03560f88680b20300c0c200c00051518103000d20070003402243c5d00d8ac2009079280500079400703002403c1c9079040a0101f00300850b03000310b4900c20051028090641c46000d035203410200950040c01405143c1a040180030400ca20b02045452000303558811480d04103480c41402c05a82901450545510030b03045014800311040c0d0201c01002c0d0041040104c070500c1c1c0320074078140d0803580300d50281600c6030001c10a000780885007800b861011400d050b0001203170071101106d0038408909940490058010b03074420030500400340503890150018550f0342e03006454105c00c1680c0c544c0302120003003004103c0b2804c4042d140c0110140c841d0301c0710160406a030b036480e614050742013507022641107503075440200d0030580300b1502c1d20966042035410707101c41c40400407e02c0580400344102c00c0b0b01d4108108400d01144070208062400c9180032000010070300509150030103810918142c1144800070b02c00c1d1481c0081d80c0e03012a0448000d8405181d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563631708 1250 563630458 563630491
    0x12060402030d0f03061d150103020f0403030806030f0f060f0906010510120e01020316021605092202040911100f050a050f0408031908130206030c030901020706060e01050a05010302030f 81
    0xb500903021546c000709480e4504a000a808018003080034454164805460001d050060054049000c0e600b001a9540ba05200c2800000d0003a180e507908184020111460007110104980c5050f4440120f1281500304001740030303440744940805900b2485c0712000d00903940c14030011401d40b80100190034100481003880e180041000c0c2c0c000c5050341d0042c0c00a40d50303850941c5183c1100d02d1500c2480c40184100000300d07103e110100600e40070707900024840c41302900c800340b151080414207140b002081d004500300e000160f88500c2889c2c81a48555413140c4551aa40e0801c50704003d059016010b10050b80800001258004200d442c0100d203801c00f10340300c0a03040c1c480000d0b4085c90300070110500c400030f1051050403849144404c01403ca40c0c03543d68070360300c5102425202c40d26070780c000d40080050011035180c031001c1c0c0c040e42e800b40c1d9030700c001410030645031110f03c10f6820660102400400039001809076003001403280019001c2805c0941ca542000c074080d02c0d007008000d02ca8100c801d44c0c9070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563632958 1250 563631708 563631737
    0x20609060306040b04090c2c13031701260a11060c0a0f0b01030b010b041a1c0f14090a020f1c0c1805012102010e040e0304120212060402030d 62
    0x2406481d80d494041c10030010b83c6024a08110300c11050300071b03c44402308080d0f1103200d003121462440424a00540300c240180c803a645085911031b1031203000c9041c042882d2040c8049400204124000c1c400303400300110303000950740c240b01010700070400e91606801554080c2c02081d1001c0354500746a03c10350b201741c2c0d03500c0400c166908101c6520300040c0348125291540003401080c1c0204c0e41a03d01410442c1000d980e90302040d24248a1032165602d4818030442c0f402c0c0810105000e0103145130305900312140010010b0209044a000300c3e14140e0842d5070b01010401d005c042d0030031a0b0300610300ea0090400d002c0d99000a060b12903d0f004281c82203104010900440031000301d41f0890079404000c2c00e918a07205c0f201050340d080340340003140580e85800700004008105d0710109020000c8100c54400a2940744c0044600030009031041d500701d910385d94134180d040c0040004000030108042940da19144a01c100038000e55002110860317a03201c5000d200161f9004502001d4200007820550b04484201c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563634208 1250 563632958 563632961
    0xf04030f09121112101a0405010503070b0703020309060a0f030b01031107060f060504020f030a0c0516030f03060503120a03060b09031507020c18040b060102060f060f040603020916120902060906030604 88
    0x7074100c3c2d4500403100f805d29410780d0f940010f00e12940120444000192406c10320044403024031480e41c0c540e02c042010400c00001c40010103407a03000c0e00c1038901d410400d0020601951107020f6003030000c0c40d404e113200344995151007241e500e0350003443c0601400c04e01403030381d810b45cac00b0b4200c000c3c024a40d10200e009d9091610ba100310001c00014000355141c43d007404042c1c90540007180c80e441c060381031600584641d07110b003085030103140d52070b00700320b14110550701c0071584283c03407214150a040c0d0312140480c950380d0804c030b007110a50000901555840e41103a000382aa1860ba1217010f8113041807151030015940030540348040302d00a061124070380c1d42e05104901d052000c2c10010b400a40005032003101e170352035110452003a4001c041e5400e00f0f071101001243d030351008a41f11505142d01d440400c2480c6404d5103070340943c40004001040380780c2c50342c00003100d0140035140c0c5c81022070280480c6080c69000a0030181441a0301030801140b4102d4000c10920b20800b603440d032281d00000700107407690744c3c0c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563635458 1250 563634208 563634229
    0x807020f330421020604050d080612160f0b0c0714010909020c030901090608063105010e06040b010207030515060604030f0309060324050909150f04030f091211 70
    0x3400c00c61080e9041900300f16641c090440b40880841c418030078903119040c0001100d60140c1d9022004041c1c0c1189500708560230f00f8050890303644141100188080e181e8100915a503902c070401c070130280146420031071700300b4045039400b40b001c8031801e00145da05400081030840880d000e9512070315070b00b2a42c5004940800d0541c0042010900c041000203080708004003030003031044281c0b544094541c40f814141d42401080ba9038641c4a1520290f03001805080402d10b030a8244140d40700d652240003440d02019100c00342c11009d480d4034400c040101500d01030058181320042030002d000340c6810b40c1c03200c503100c011070240110032421f0741e40421520788a990803134000b10f070402c0d070f041d082c02c210b03180007040f407a940c0c485d0b500000d060106654100b1031400300300c50724a80e20028495200c0c40d01080c00381c034030300090428140d40500322060f850181c241072028400d0f00b071851185050725040c81c015108401641a0100b00078218400707200422102000050040c1c01905860f040405400050f624440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563636708 1250 563635458 563635543
    0x9010312020c03063306070f030e10020309032e2d0c030f05131401020d0204081507051305010810090f060e0609060105121012120807020f 61
    0x101c20400c07a903060101d4441c1c0c00442d4a44031700700d911100010700740740b000d5a01c001d164444820014000021041e040c5405001e10078102485484024000078003461140031000d001f41c0c00000d81301c0b0300e80c54140b010040a20011030400078104004d04524502e03e012404c4050841d5104941c807110b02c910819600d40b210b034101d084070500301d0f1404003400f4000c802c40541c0401d00300b8600700d482d405c039030064500c140907401070145011117035120441c001200ba00c13680c0840d50b0030080741304000c103540010006805040012304035140e00c4c11701c41100541c0185480c0411106024542c9100201702204007114400d20304050151550151910812500d43c00042102d29202038803800b002e0b01d4000c40304075011091030010550300c40b4203100e035080c8111002070015a080102d8448507a070603440d144c0044c1100c4000e8160780d210031143c025807480510a664100c000f00703030084280d5100311160742c44451072000c0e03c0c0440c820f07440181d48456070440900002200c940140507082980242c2c0304560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563637958 1250 563636708 563636713
    0xe0d05070b070f051c0e010318080d02030103140a15110c1501060f031104120f051902040f0b0d02060307180b091f0c030509040e0307050d030501050f09010312020c03 73
    0x142d0b140f4141c0c1e901a102901181c00d17002d0410440154141d45002846404581c0c45164503180c0000044000346194240f00d00c41c40c403030740079610101b4041e4010f4001303900120001a580e5040d410700204c03000c00703190300c02070075400f401045002078401800c4603104018000c02280c854512a0040301c50300400180d00118450359400641440305562110b048401d203480304030200608010440641711030740100029000c0800080110b070543d580b5030300e03590b80159280000800d10342c0d03c1604080c0b43c40700c45280030052400c03580561419104284e40d0b1194404100078030116000881e90407040040c01074847d0b94084002a000e80c003a0701d4440c4000b041916003c4416181c1507615469081480039500802001000030388091803030103400c0350b640603900e0b01c4800d103540d50344c119450351014070842d0304280c81d034803000400344042000d44200e81c840e4000c0c1c40c40c00200c0c10002c04840050303201c10311807440aaa40303c2962506110181500e4010030070000c0c0002e414070691900c00e403050881e4241c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563639208 1250 563637958 563637967
    0x91f11070605090601090b0114030c030901061a180915010f02030c0a1407090c1704030207030f060b010815010905010513081905010c02070f12032a1505070e0d05070b 73
    0x200f1001c03a0f0709040c0c40d2852803c2200350f10b141d0044481e5184100700b80842501003010940c142e1040000d5548900e04400115045446d880c00307030540c10f18000c0e40e204c40140480c0b01d80c160000390180e902035420981c8c1c6201246480c00342c03101c801081c003d02e141030000310042d02524502c00d10403940b01c40707138a20480344003aa440c07a18840541904a4030f5a081c02003540105080c42640950316070340c0003668030700c2c00030b0b16081c54001c241d11029000f2030542c03143e1907002001502d4003030360403101d6014443c00288090004005092904010300303c0c6a0300c104500f03402c62580e0400600c100382c0d2420302c4c00716113600c0c1c2c880d042c241010b42d94210a80034460340c48514803c80b04140100c4070248100001c0c4810100404140c2c0c0c0c611741383c02a045000341000080c04550600f40c1e0082c1c146000749410a250342c40108008081040345108007103c10740007168030b083c0880c942e2503185000d0001410480d83c03034000b000401d14040325100521600001007401c080c000104610000342000451081e0354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 563640458 1250 563639208 563639221
    0x308040f0e06060906030106110309030d0809010e0106060f181e051c110f01051c0f0e0c0a0b1b0d0f030f1b03050705040f0b0c06091f11070605 63
    0x40e14158441da0400440e440700040d458144501592100c060240129086908107281074031000c546002c10340c91031105100091003640c040026086006481d00c030401d40342803001a80d800c1d20a00d0901d441c05038100700040000c13a078881545080544036240c50384007804036086000049840b40d000300c180d00640442d01d100c410450b82c0312400c5400441e030000d0928008c9400f2200c24020ba030020b07041ca4600080d6102c641060000e0501d201e0051505502c4c14107202c1200b042e4003030a003c1e803c0f1342039540304015070032072061050b40d0a0b2400d030701c000c0c6000103051000445100e0b107030041c920641d00104010324245100b95104585043c20015240001c0c08000c0007804500901c68440010f803c03c800d0990075a070320301c90761a107411120020b42080da003442c015000b40c80007625440802c1000c000c00111850601e0300c2a01800109440d10356401080c00d2580c9083c0011b8404070268118a6002015100c0d181c1003001080c2849004501c40d02c3d4a41d0800d014014880082c14081c100b0040062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 563641708 1250 563640458 563640479
    0x171018020a080f16080706030c0309140a05060604090503091203091c02011202311d01030c0e01050303030a0f020409050403123b0c031614030607050f0307020106030804 74
    0x203100010700204ea190510b0850881680d4850b40300e0032030180c0290070103014007842a007151039040403a06011a102c0340e0b541d9113403480c50580505102c00d030441094681001000e003e0590461000c403403e101440303045e298180c4910407a940b9a01c075503a4170302e4030300540e041807060310800344c0010561400c410b807903c01034003140f2107200100e000851803901c40061700c155100303492084500030380341d0480450f15802d250400d8600c6500301001e040b43c91001440b03081c049500710329600703807580c01201c55256250800e0a610550480088401c450380180410303180041902d03400f10f65030001041d8070b105560740303070000d200395004048014201810007041c160450520400018003c0b000c0180c5400000080b028500d04a80000681500710b04c04025501e017501030818200000c2c00e840c805025180003a2030401800800b500e00b011000003084400c0c00d41462408a02c0d0503030251113030703140100004040d8032841558841d070840c003002040d8001d1003503000300061540b00440d2642c45807212650744 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 563642958 1250 563641708 563641723
    0x302030919140d08090c0402040b12040606030c0611060a02040303080412050705100203090f0715050f13031a01060e01021504050c0a030302010b030f07120f39171018020a08 76
    0x2d02131146c1490003003c0d0500d80f08580840f4501805242408034a1244540b0100094000d50b0501d0712a840800880e0005c4206001040680c4440c14040c000c1d052041c207001c0010300e000461072060204001080c0c000c540c3c142c1c001d9200340c40d1540941241801d480c54081c2c0305014065100750129a01861070310f03030046000c0d40c0450308544031000c540c03824641c7c0d03d03000d008008142c000c0c1e80d10201a503025901420907490364000d154181a208540808048441d40c802d617401807081c007641e4403581e5040301150143c03500d803400310113003107001d40040c1d030710401c0c5001c0131218030080000609214081c4104039048100810800d081d56803420020301070880c55002e180f2074082e0102c07162074100c0018201044070484002c6101d151440d89901a200c07030135280c1a00d90142d00c809050b8480c0b08060446d210031122420745150800450100c840c4681c1070300401200803420141070300c518800110054406800c1700e0100f191050501240f1401950400094020351070640102c0c4800700498200f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 563644208 1250 563642958 563642971
    0x70c080705120d02120904091a0f0c030f0f062d04060b0a0207032a06081e01120605071e02030705060f0c04170309131b0302030919140d08 61
    0xc0307481809000c525a02c4211900d54140981c5c0050040a04044080e000e020100001000004d00b00020784550300d652809005047c14148681c00300040f5214040605421503407071172055042d03180c607196103105040050540402191b600000452070341e200405a250844600b28511803965031b82d10704c0345a240103012552249041c048049910308030001511180c940f26070080c000c031407860b120350154107041c11035000000700b00810f90b40703180100032469000f0300440ea141809890220411201e03c403001d001a1100144c1c41e00402506000c80e541d0140340703030004c60004107512840e0003550f540c4901ca0303003192103018020340ea0b0444d54000c405845150700400c00d5411951341c809000b44c00840c200d40c0c0014440f818001440241d61000b40c0550f0103001d803045034549618140054010400c0070050b034011a2242c840c0e050041a0020004110103a4201503041d4104502c0440e10b90040e2030707040440d08124070f2408180580c100403011041582400e41d00e1020102030700410001040b25030303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 563645458 1250 563644208 563644219
    0x15060503150a0b1803160b0d0f05070507030e010503270a0209090f0708010903020d180905010b09182202030c04050c12010b0f271504050a09060506040e070203070c080705 75
    0x602d00703081c08104207000b0b050520402c40e9650030046002480d4122940c03001519030744208180c201480ae01c91540100126140c2c3c0d904e0b0318091034010041144010b129041003c1070041c40b03041c04020780122101040e19085a090401410100e858000146000307580913121405102c1c4080e80030402030f020961980694121640f6040b195083e6445c040c0b0040c01a8040c0019404451244500d10620805030480c80c0c070300c9a0750000300d019100f00384c0100d1107a0f007000988a609182c109204410111481c00328072013071800c503410700c605d00c85c40710603550500c1801034603008554041c400c0041d0084024010480e90804040323162284d080000940e40c5441e1120021440c10320300c01c269000d501140066a14081111121700ca401c81c00c00295122589148600d02c244d65605010040d1610f04004007600c480c603003003c0001043e1341d948054070b000c0c940a0705001ea038170381c842200c05960102e5200d5407661101c0c1d01c1285184200e0300c001c0c10100e541e0300081003182d070100b2100d017110350441d079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 563646708 1250 563645458 563645497
    0xf0603151401030506010b0a020f0a081215030c0f03011e0207020901060c0b0c2a011a1903080703141b0606040e0d180510090801060915060503150a0b 66
    0x4941c460110203001c040e00c40d62001c801000f11a600300b0040030381464a2040c7c0b1682200000141d1400680303581c100d5400b0b00104402030041c403480385041e4005030f421002072000300301c44007294a584001425030300400c2c4030f01a42c1c2d101d45003500302d010307511204090a0301440d51002c001c002500700400881c403614002c000064014407400403061f141e40c001005122944496071000c0c00c0f9409441506000452142c02c3c0110b0030282c5c0c5030b814030904800004c21400c08080f40c02030300328070300a40584070300c00c109552801e5810104402041d01c4d40485607640c0c4031840e040603510a0655200001c1c01c5000241415403d122191100e4414500c0411034046441c0c0c0f1040109a41c8504444000d660140c024180c1c254032034901d80341408102c81d842800315841d40d002c00d03211000408501c0118040d480c08000d6050b09205500c01000c14503003c0000c486651130f20641240c0500c1842c080010100214140303521408000b602504003c080f410300300c0d40d407640d00d03000e600450000583e0180f0b001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 563647958 1250 563646708 563646731
    0x2010e0d02030f0f0d09020402070503070203011b020a080f040b07030908011103040206030408210a1409071d070201060b040f090c081513091406040b1f050108060102010f060315 78
    0x9443c81000a10229070500841341108050381d000300d888035240c5a207800200000d6115803004111585c01580556901d040c580107160039034603c400685035034081503040c503902170b03408110003d00680c040c500950b102402080340c0e03064000d030341002d0000c0303070002010401c250308018580700b144c070707000c00034403000d409000d2242c0b081c0400c0354042e401a004000003000039608400510407648845200050880c0301454158032903030032900e03c8038031743d500c00e21700c44060100c188595000c1862401081d9203410002500c0d00309403e603010095040300c28010034400d40c000e4004030701074185030b80d01d107446690b1912202c5003070803280700d8a00c559241c000540c01440c421140300d0b1043d41c0c0d03c0004459881940140000c044040a03400e1080307075150a40307000100b03500150442e000a19000f441942011709001c400d941001d844401a04800b0301190681c05049054008a44003409c086182d03941d0480141d000d172441d101d6441c2890316140b8040100204070703900c01e20b0300303890320002c01c9034940f200c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 563649208 1250 563647958 563647963
    0x30306031209010c02130f0c03020309150105131d0a0c0f05010206040c0513020d02071b05010c050a03031116060510050301090b160c0b010b030708060109120308071e02010e0d02 78
    0x301c0c0d481c0c0010800e130b243d0b00250401542428400130407150000302d1445000e003280c00ca600558210340000e070004203100b80c404080222204410050f4081503032549000005491000c21840105040762140403000350411000c01c06d00c05418200180c0c1c3d5072004510303004a443c0610b0048030001070001038041065480098000e109990000d4041080da09040c10030002405c0401110500c9030200003001020326030b8005400c0c1035200c1e000c0c400e030342c148525140d40c001055820660401c80c5c0f404080010030400240e00b10540d406040c005500001a14102510312482250780f1a5075807d040302800c100c466400b41307104403d0013006a4100740c80c0e40426007681d03404440601800071041c0460240c4059040d45902d51300f81c1e05250102100740d030365498408600768840040000c021040101003a001000139500405c00d20700a20360f6400c002d001038039883c3c01c10f4054200000d000010f21924040c100311140c981d030301c10113661111120341000780a020b503802c1f809294002c601840000d107000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 563650458 1250 563649208 563649217
    0x90901090b0d1b080304031b09151e09050702060717090304031407120503070b071403011511010e010902010909050c1603030b0904111c03090b0702030a0210020303060312 75
    0x3424920000d00301c1c3ca40c440f10b00003907110091290240b62002a03000d03010030081004601c14600450309001e900c415442c141c180358402c0b143c003406e15444004800c1400306d0344050f0340c1d0015403001407862403088001882031681145030100c0c500000d02100c0f94000a0781031142c402d90351404240b0003650700b40720360407900340d40c151440d50040c001800010101c8000d01d0701d82e084141210a034070307641c1a2200d40410412000c2c1c405800024501003803100203007806501c0303101410280008240c080001284c1d100c14410b01d0000d8421400301100184281e120b2942401d40380004d11510b004010b03442e00808402c40c0480c003040c507500001032a40c00f40d0041e98401c000421001d0b0030840302401b005208103841104908269640449207020743c1c171005014051801000d401d418040000240450000701e80424024080b2105d64280001d5003d81108240c0d075001c0409611224944040f902d030413000c8000139400b4550b280d6402c1c80d560b00101440c4102130480c1250700f41920340c21642c069129 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 563651708 1250 563650458 563650481
    0x305152403030a030c1e0305040302060a05040f0210021006181a090a0902030f060405060a1a0906040c1101020d09030e0904111504080613050106061b020d02032109090109 75
    0xc00d0109643c1c036070003a484000c991000e03040c01c024481303100990032800e01d142e030001da01080c3d48400740018181c1c1000303035640c44206a9001c21079410143c48048144d01040c0c0d0080c4561080c4006140c0e0b13071310034071280c4255041d0800a0181e2901c840d04180800d4031080720741041e901e00301c40c08003101000b5500108503000600209042e454106812000d13000c51a01a07825100d0842e00c19480d03a81040030920981c0074202a0031141040201074043c1c6510040031027030700c102d0380504103580d40c172000c079250802c9045074001140c0030824410b6030560130481a2000700e51010031603842109540e0001f80305203120f03030f80300c600b07038034254007040340c50401550084e01d0941d45407006111410800000e480081c1d12200c000c3c1420354070080d00b441e210003280c8803801c1d404030740ca0800400030240610005841170342440ca40612011054924034105c1c6c140c0644502c1040d624001076450500854800c02200294640700c0da03d010340e12001a071080c01803a0003007081c80e000043d001c0780c510400f80d5840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 563652958 1250 563651708 563651713
    0x403030f0e210f0f0d02071403091e010f110c0a180b0a0806131110020c18090309010c1a0903040e2a0702040b0a14011e0903120302040305152403 64
    0x7201d80d100182e07034102148117250540d0030020003000c031360b1012030f9081c801d10070710065588580c0a000d01042503402d08045021a20300d4241540f04da0b00070140540d103d00380e2400300c480a50410843d4a80012985080c0d0810343e002c0300400d1140e0745600c4000c0c503032038204051040540b40340920070400340500caa20f400d50000c1021800364140c412250311041d0141410158078076034280000e003200d011a21410150340710111640160400c1206e4400340540219092202c0c5042c4403072944034401c041a19041200c0c0c000d0520800c24402c80300504980204151061498036400300e9070307250311074010002c8400e10000003646002001c078990700800358071a80920702d02c0404a4031150b9400128007243c1c0315482e01d10b0310b02d4070f454081c001801000840031580c0b4404d204c01c0090b1000d40d1101c0040718100d0f02603804603200780c000002c4800c0325440740240c0c0c10410a05001c400900990308020050300541c0450034115801d40e101a02841410403103c98005207581c080b11008400008170f07401d41c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 563654208 1250 563652958 563652967
    0x1f0f1a1306050c0a080415020616052b020d0b0a090c09050607020d060e0601050112020301030b040b040c0b12150d02130b0604080a05061812040902030403030f0e210f 73
    0xd510400180034420361800883e044c904072581d50f010b1940050300240103201d601c60703221941650421141c2d400c400c1c40314203a0b581e90321140c00113095100d080003c03d005080c4202d6510440300e142e012515038540b02c4411926403040c501c2902c0505501800a0310130350003040c000c21185542e200f1520f0410380358603039682c12803503c000d2185c0d981250405903030105031000300030040340e000e0080000c0613900101915243d81004c002414022080780000c220078030610042c00040e204a08598005402c001c6e05000c9a8991030300c0c900381101600454110b500c042502c0c00704400501c5000d003c0d5500d112030007400c481050902110840c0a8806980b2280b40031111803030300000c0d841000355042c0030742000d24140d00d5440b100d151a1200f82d044440f64016410446800b200d100390980a5140310040c3c503100444140c0001180107902503482880c4d4000046020103009500c13403a1102d00b20320003480a92030031803030542c68841d0620500840241c0017080302010410308222844640550100c030b050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 563655458 1250 563654208 563654219
    0x21060901080a1209210501060b09131107200f060c15190e070e160503040b0a091208180c011b021203040324020a171f0f1a13 55
    0x110101030100e0a00800c004c01283d00d289807078095011101c141a0200d014210349000ca0840d01e4580c03114015081c02e01c000c014540e240c681c08041e0314110765000c03e5100c4c0407501100d16100b03040c0c0c018001e44442d915401c131072000d22408600c580c03044441143c01a070a000b802100c3c41024000401500000c04040042030b0100b82c0d940c0018901c90300068400d048200348084600510501c83c0030f91101204201c610350300050706601000300825100d0b041c01000024119010144c0010110018440020003d5010383e002402f81500405058004642400040c0441c1011348a400c100d65200100c503d41045c00107095040b00010f0b581c5c04011549130018845242c080c61007207910018030840d0090148040010700003860240740e0b0380340c03102c012004803091260a0341560012500503c5840c2a098201544200220b02e04048004a650301c1d4209a01b0b01845007402414460601c0702182c4484407040e82002c1d2030b105481c490f040091103010329480d0061060180300c0842e242818000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 563656708 1250 563655458 563655473
    0x312130f120b0726010f050a120f02060706090203070b09090702060906010b07032006090f0a0b040b0a18050f0d080c040b070507090c0c06050109021806030702030702040221060901080a 81
    0xd10250301d000050f13218010110080d9030f00c281d002407141c07941c0300c0042c071075480c103500071030010041070414200d03507221a80c401442d074804100203403007420045846018411641c200e46003107a030040582d08a40d440c1e104c10000c41d00034210550189280000007a1303080c0c0009610340c080c104500007842d840e80b070407600756455402080118200034242c00b912a892030302c049000c200160364400741c003040c40c4c180c81c03203450701650030040041b5034407000200300401c4045003140e80081e00b01c0c580d10a10341d240e90409025210458107001d5041502e142101800310105070780218000710000d660b2440c82c180c8089902c214151004403005c2802c0200f009044030315070041c10b020744200c00303499440b962442114200c818184c1c040000c1000c81c0020401c001c0a44961805804070000460410060444410145847c0b01c2040e004690020204900c54002c0058950250b4024403e65580040b03841d16000042100c95402c400c0c1c1035800402d009280c141c030803d041c0c030f140c80c0080c01200101d403600c42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 563657958 1250 563656708 563656727
    0xf18110102010b03070e01051507030f030914030a030504030318080d050601200a020406150e0120010f1b050307050a12110f070b06030d050901030b0312130f120b07 72
    0xd0656503112540b08140d142032080000901e071280c01c0508648c50300040c02a000170b4134540c040340308805c2240740000380d04003c20350400e900e20300c2c1c000742003511440c0c03054545010340401501744c0301c0030170300b0b0140e1030303064200c0ca110b10b11a41d400d1011002001050314029903401c00208078900c00c0c4500d815034081da80c0610b500920500d001c080100c0d50480100680300f5144561843e030304001480000d5003043c0c024080200803520030a000c0c910154401020443d90030501410050b05c014010a1058400392241070303080381a000300400300103e600030300241030480e050220307017072621a0040a24018402d0f82c0c032841154440c18602061074604460701984051310203545559041d40c08144031a60014010100381c1840f0b00380c2d0307442030742040b14552030001c1c00148648c0c460341602400d40d6104040c0e8641031803e080100d01300800000281c285510413007000ba54400103d80394003c0c40300301d2500000c80d41000803200c11741d03496111384201d201b0000d602814100312180070030b504900c1000c40c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 563659208 1250 563657958 563657993
    0xe010e0f040204080714061e0705010e1e0106050909060613061d0a140108120c0f0d050415020c1807020c0316090c02031c0c020a050d03050a0f18 64
    0x1603011481200050102d80154002200e95800000c007032003061020b084405c1030602c1207480034200f4500900c08000c81000804940d03400300089504020000250440e480c0c41c00c2a5054695900c8600000701780d10b081d280176000a90700f407400019981c242018180d0080700040b0240070565188814802c04081703101c10b8001250ba40c000004031102000101019502502080026401c003103012032b0540340700e06140f14080312500010031110100107041200191284411521a241c078003055040940060406039140540001c64500c0769201d4020000d440742100b03c0e014101c19070070104d0b43c407000c2c0c3c00c0c21a00076031600342440319900d210301c0459000300140304481c1c0b804400030100f424480000e41000711705c6200d203000d00108286c1d0041400d000c2261008605204201c0e1700441c40c17102100c080b0104c541d840d942c000c0c0c92031080c0708048180c0d0700306080300d5241e5800c2100038000d1030100e81118a0500d8016110f0180380103019900a503040824000c40040349a00c8461480158168a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 563660458 1250 563659208 563659219
    0x50d0f0309081227010b0f09090703140726011506050f07080d0207060b130218190e040b09060601030c0225120b0109140609011505070b041b0f05010e010e 68
    0xc06a9204d40190700d0f140042d0020010039281c000c40180b00349904003a100340c1c81280983c0070006d8418001800b04200e9400c003129409906180c14043d0401041da00030310305805198409180201c1c1c17040c241c0b60781940c188001c0120640d1120000040034181c000c040010b042000041100020176024050084c05115607900e01050380a180007243e01441381169280c1e01d59002e103040d4034100459004800164009525000002d412a2001d030365249201c0d204801108100c55003030000ca651101a2660034a0f10314030303003014203081c00e1400e01145c00c11028401c81d000200103510a025917070b44040d25400424196540300070a40c18403646e403c44102304c0d41d014000040380700d0328004011689000c0e040da010154140341c00780d0140d034003225940209420030750602a43e52140e08404c0e044404d201303801400f189401604a8a500c5044400b9044400900500c0103000903000080755108051b000001c0484e69030741c2d0b030302c5580440e10a16000c5402800050095401064800c1c0d405600500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 563661708 1250 563660458 563660491
    0x10c080702130f0b03010e0105010803091201060f080303150f010e130e010c05090103050a05060a030b0403050906070803091e030d020f0c0f030405181306110702040603050d0f03090812 81
    0xd4070300711036a250201d20703d15120001c80c01c103400c0030300c00e201c00c44290b0130007484603604018411f03649202d49143d83d405141c00314842000c000c3d0a6001030060300d0f4030b400d40c505a5690b824a1943c82d041a6910780740c2c513101c0724841160703103810b02686202502c1a1a40243d4407014401c1224810424044201940d01e90492051039042032107404581e4503540c40303107511186a500010120340d001410798003090314000503c081c80d660711610f0008c490740300845401030b50306c0303140c00c51752405a42621a00214046220010807400e040590b2103181c1c0481110700090300c0c4802c0c11200313441b0844210594208000101d00800b20703400424201c25000766039458500f00700c000b03918022915900f17080c10b4001140a00662500414005000c00700b01c80075030360380c100b90750041607040740113400608195544441107110b94075102620307281a0010800c21919659080190701d4050b8240f4120008800720404031141d40030348241858241c001461340d0401418000184106001801e80407100d0202803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 563662958 1250 563661708 563661739
    0x604021c240f0b03160207090921020d08040602180612071b031b020a030206030f0a062c040309030c08010f0506060a052a0d2a02010c080702 62
    0x5104030702809400100c014041422a0103180849600508490448102e0800006200d90709481c1c004041d48004020b4420203a8240c2c58000b5551000d0039144c10700300d401050003240e00ca200c01440c1100f00418550f800c0701e9040340c840c100c0b03100c000301291035207000c10041021a4050000005548400c0d4400e007a0380c00000c13001d030801400201c4044008007007280c00c540c4080503001c84084d4001c0050b03800415a005048074000c3c00001416440d243c03489025556640300e16002150003914950381d9007015845c0418062040320f4000046040480c00204400810280c1c00c130030704c0342d80c6c0710314203807140b400e40c440c0ca00c50150040e4108180b400000c004640d02840d942e00410305d030800052080c0d000c0040005580c40103220310701c9a113043c054031055a4008d011a070700d4401031101d800c00a07001020110b80340082e558580050712421801101c1160003003400560031142c4412a00030503482241e10007030803001c2200a0000b0345280c5d6240c0040ea03510040e0140d280b0043c00500410001c0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 563664208 1250 563662958 563662961
    0x2040f060810061415131a131a0906070203030403080f07060c0807200a05010c0e19120305030403020f010f140f012106020904060303051309140604021c 67
    0x10780022403a60000c00728410a4a81441080d0051040d04000c650450b2a1400a05084d8401900350720f00c2c0c00002e208031581c82003451240c094850130718031706488190802c100d00136070049010112030a914a90104000d007100070801e00c410080c40079546030802000502c4050b410182080b60544401e1001000080a0380c004d42204003000321015140c54403420040d05640c0082002014000e4010034403002c9640b001c80100098020324202012480d0b0481c1d42d4540041c07580d014086520340400c2c1c1e00c00c0c80c1d00030021038015604071507400b4041d003020b902c094445194070480540d0350f0f4040c0b00d0800030307000d1400f03980d2050090060b07030a01e80025009900703503509900388100403665508025070000e5020045034104240d4000c13803105605203200441d1310034006124080884c3d6141e02c0341e013003040b103404640340c0304000b41007070207990f40d60f02c1c0241254012034159401c44800c1600491b1040c10b034072034040090042e6640c80040c0e2240c0c01480300035402030000c4111801a00c201020180c0c19 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 563665458 1250 563664208 563664221
    0x702030a05030304140d051e0a0c0b010e070f030204050d0204090215162108011419090f060b070305030402011202071a0a0506010c05072c090c0f09090a03030902040f 73
    0xb0802d400c00317183c20b00d140701e040640e01c3d040002880b02c14011000383c03001030700d038081500341c21825896540c40140020ba40e9503003d10b100501e0004490300101e040062001041e00030300103610b500f09680707442d202c203506038003481c001ca5801c00b0660240380054900b0350002c4400e10300240207141110740926150503540d202c07205904104010038001801c11035500f08440d0b0341c020460a2000c64800980024403c0380107114041070fa4444070380ea85521350703808900004034180302ea062034000d82c2d508202005840c41c074410544070b074074041d000208154003804540500e81d25a440030325641e100d43c01551004200440d81c4030103603003400f104000400310650100080b00d403801d01c03011841c2442d503010035910000e1076076041082c03200c455000107038001051015030301c116250446001c071440c1c402c0118004e100323190310001101024003500c10ba01181d8943c0c0e1100c1910300b04090984007085c080111020344000b1801c0c1d0100b444200828071980c043e00e80e00780b00600202c2c5844118081500340c3d4072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 563666708 1250 563665458 563665463
    0xa11040c0e0108040b070314070c1b03031e090512060609060603040210030c09030f11211e030904180c080a03080a09020a0e0a0605090112020a06080c070501090819020c150702030a05030304 83
    0x111008038000744a86406d070240030540c110f07504075007533045940007019064400c1ea030240b408502d0414000250003040510701915001e00003051200700c2c0c00c0c005685410a54040b4080c1c000707280401d045041072000c0707911a0341c02402e090381400120504034002c26003644054100041f0441c0803000540f240da10031101406a01c11504103420102008001a00481d01542001c184411000e03036060100e9088603d08440320707030f4020950802070060441c0701e00c41c412507010f441c111202d0140c41004c00103403000b50150700d04042c030b20b480e038000036230f00e4000700006000300320240001008d11049030005031403144050161403146503244244000c0c03000a9603001140c035240c5c0c6d800d21032030400c0318046005081c007840701c070780300c00341c5030007007007640030b4501170701c4104000d21b40003c041081030381c00c45201e10b40c400e00805c1002d0840c106200da94100b03040191a40c40c9241c0c800c5605480060201c3c26240010809403500007070f400b40d200d4a6000e60b0042760076024042449011502c2840036521030b50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 563667958 1250 563666708 563666717
    0x1b070e0106080a1503111e12160603020c2e050703061503061404020a1b030309061424150316020f070f0b030a0605030a11040c0e0108040b07031407 65
    0x42c0784200d001034a01084c460b4000c0300c940d5408102080440550305140801075600700d84100115622061000c0e040c114560417803400c4038180a48580000c5940c038403e01c0040c4082010b1315034104405078410000030064a60120302030300300700300c060300510200100c0c0340010400003100003c0402500d100311007034404207940b20001c228402c098407a003608600c081c902080f0150500501020000708030305001c1c06154086070401d80b03940a83e8948480a64568152034000103e1030014043c107400201140e11600740b1040c50006500501038a0003620408080005805c000e074032100f2011810100c180c0c000b5000c0d03004001e00480b03000a50042c0742d200d05010b0105480100a031030141c3c1c3c100b500e01d0390351003010204220441d0820042c10746001e020f1030340c1c2c0da454660040028000c2d41d04a160716004000c5030008000401551044100050f01d00703001805540b01d042d01c4810003c00d8003808a50309000103400504440d031420b60210341410002900c10b1035a070800c01e50b1800f200d1140105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 563669064 1106 563667958 563667961
    0xe0d060c03180b0105030d1407020108040219061106060d0812060301020f210906070c0633030b01140d03050a12020a0e09010e0108031b070e010608 65
    0x640c00c058002c01181d6070307040c110301c4034200784030f03040c42071090700103500c0f1036409030440c50600c0488243c02414603000342c00545104038020b20803644000c000b02040d1100b1110148400542000c3d5520034480074202c10080c07034600042c2400e4170852260700100000b41c900c0040310440f002411000381e140e20f035600800e01a028401407192502000f00d048005400102100b41a03012480802a55500c450f5007031901c4000c2581c040000584c0040d2940214155801c00c2500d007001001e08410b03600d0312004640c0f00c0c3c0000040340e680c140c88042c02c009120080444901512104600600000d030900c0090020090301400605214010540603413041c0a544400d80d1032400f1142556a442c03046801013848103030720074140c4281d00300c00020075018980005075041e42e401100075841d1000b004503440d882400003c48007000c0c4168040424152000c01c1e0103802400d132511404010b = true := by decide +kernel

theorem cover : BRFrame.Cov 563489208 563669064 := by
  have h0 := BRFrame.cov_init 563489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 563489208 ≤ n) (h2 : n < 563669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
