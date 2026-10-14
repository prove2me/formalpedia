-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:28:22.904846+00:00
-- url     : https://prove2.me/submissions/fe00af04-c625-47a1-a601-3f01b9a3cacd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 240827338 ≤ n < 241007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 240828588 1250 240827338 240827341
    0x40c091e0501030c090c110c1c05030c01050f09030c06041e0818031006080703021908030c010902030705040c052a121207090e22061a0a06230c0a02030d05070b0708 72
    0xc80d0316138500c001c8c0d1034050004042c2414082c40b501d15100790041d40101100d5668501100060081c01d0903150840c1141010011840c03000001080e078110f555207002804050f19665540d40d8482040105901c81848114071035003c2200340000d4800e60440403e40e203140b0340040d04260405175075294020b840d07450701e03009000c00701f80000c54005481d81079074451034640115610030080f10069004040c40d10002600c01a090f006400840900740309500311518191600104003d84200300600f00000e2018000300001c8415070080e0360700b00400c0c582c10781003400c403c5441402c2104461142e101080c0008004d010403208140003a4480303610f1601908542c1000c07969004900041e025a2140003034280410250011807907044801c2d501503400c0003125000150304115442d15081c103885100c100200040090003617054803001c207241c8011242d0315050250300b24484e0001400c0ca5260b10030690a0300058404001110315030040c0c1c0c65813529044585002440340b540185040c1c10010b0480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 240829838 1250 240828588 240828617
    0x10203130e060d060504032006010608060907031b0c0341090a06030f0b010c0201080703020c07030c0602031e04030503040608090102120a051005030105040c091e0501030c090c 77
    0x31006025541c80300031110140d103592001501224074814080c105a00c5d110500042540000c0b0315104102540040c1d900e41448010240c3c0f91b2030240305510205041000041003071804045266005165040c00190b84c0040c609070002000d0440f0440040340c0e807a4992030506800c458a8101000141014001044032202410260300e102c29140d2003282c02c0c00502200c9500c8205070b0b8814900a000b502c01c6965603807000703001e08410000d0881c00b610384490700400b0351003101e0304200150180c464401c1034550f501c1c22402540706455583c52801007039004400120410403a40050003d0740c000c0d03440c0c14924004c0100c0c2030791004020b17942c0900304410400528084252001c481c000e0401e10496640e0082c060701a200e8450000c8180503c81304000c000300440d40518001d03c48203141403181903d81040c5400c0b650140c0700545005442e4408024611054000345c070146480c903440f02200048088507400d5031800e80007220140901d40051201030b14622070b050701d404003454010001c2d038021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 240831088 1250 240829838 240829867
    0xd0f17042406080a020d030203040e0703020711010e090123030102030a0209010305010807030515181914070509130206040e040b07031404030f030509030910050909060901080d1d1e030c010203 84
    0x340c4c802406104a103000c0010305000348240c070014030310072084000c2850980d8000703000354080e41044441c1c89078082c1001503548102001c0070703a04c0300074028403566420102410351141c84110060f146040341180e1858649080c000b03103010700c1d8122070250300d6812050000d030555505800c10349007076000e03080400124500182640300700384260f0441c5050348919100000605000f403c04c0c086100b4000d8281138080c1c90110001e0543c02085030801e108403015010392905603074440c1c41e900c0a420404240e2802034130b45503085040c402044145059a10031085001c1c0300c08a6090711500d406100300010180c240c001c40001405400c0f858070f8074946550003501c4101c800340c10208042c0e40d1400a0841c6004100700c0b41603801c02400040b04105003c002841c91303215242e03d41c022003416000c502c1e6800c0c0300366000d0507500204094410144403e0b001c4500c1035180c2c602c1010751072a101c0610f4281c40d85501854103582003000010310341d800e4402d00d031405880d03030501811540201b00070304640100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 240832338 1250 240831088 240831103
    0xe0903070f0303060905071809051302061c09140d051207050c121b0f0f071206060b07080a020c1008010909050a3903050d0f1704240608 60
    0x8801c0e140300c030486090032001810a5044108900c0c0341c0801c0c0030805070840003602c1103054020408071811380b210a50001d8840036100004000c19602903940185440c6001d018407d0904d6111102030703040d0106c0700180d402a010a5400f4100310380c21f184100d00a020451180c0c1190500034a0860a07003545240060001c14100400c94089001640c0400a100f4400e00120b071188882e01d0322107c00003a100c0d08080c0b41803184920544105040ca500c01080309207115180c0c0e23018107a0645091920b46035050140340888245030746400100341e040d1b0303201c0586032450280c41566241c3e003800d5000b920309180b183c1261300c514240000703034881c254404c0c9094103507284c6400c0892070b8103203403520701d141c0180032100a103886202e4941c00d1203070380704c12107181071404c2c0e01a4138003814004240e5080c03120b1485c04041e00d01e4102001c2440c3c0580039410108040009140445c489140c040e1402c00c00e03203003900c048402140d0001c051440752001e40062442c661001e0b0f04021032403400c8200342e510001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 240833588 1250 240832338 240832343
    0x19140105210106020c011b020d030f2001020901120b0f060a021e030c0106060906090605030709080f070312090b07021c080301030606080d030606020c01080a0609090b010f0e090307 79
    0x6069500004901e4072460035050180c1401180d61210000303512010340b8510b0a00080c0a14020301d035401d5a03461142c80c84d50094040c80c3c00e00000d0f101118040682c0c150320091060306c0d40d002ca101c44d51090b607c204907040400050f15222140001480c840030811b90b200e140342018603480c804d64407800c80003c100400c9500c1039684402d01c809900b851038011442c1184a0b810408501c40f50010004026204014000b00041ca0325603000780d4000c4047c1c09002c00180c0000d40c00e01105000f0001140c00c40f00c0c1d810700c841c486a482c0300287c034040e0500d401d401d150b0030012040007004940514040703922018107000c12254248904c28043d800f134840c01a100e4402c00386503002e00000d10590001064210301d405a59685904000025000b54896502c02e445000030101119229110f110107481c0240d0240c00030955520044035541d102400d4031010b01da440704001095042c5110310b1103154428009014207624ac41c0955100204070b600100c080c000369020407810220110440c3d01d10b80c1e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 240834838 1250 240833588 240833597
    0x180b070b0f22021c0c0306180302060a0c09030803010801020d0605060a0203180609090f070e040b0d0f050c10030605091e0103080d090f06090204051302031b040905030a0806191401 79
    0x220383c00098010010345a84210394010766941c10140708030080d112080c0c0c1d00070b28040c0040202c0c3d080882e1580f071045030290040c0c001001188400c0d0780350304a00c0a44100349841c21415807170340c80d441e449520030f900c0409903a42c0050300341645c0040d4002d10b00105800c44180342010500b1401a40b00d00c220240c10042d1807203224456180e84e580300903501c2090004c1c00801040c9029040321020581c141c8040c400705005030720114070b9190900810800410182c518481581990348500540f0021641160603018a401c110588d807122100d06440c441942d0700030414514001c14071020fa007020305801090f034911000c40b40c2140f00180402e044a034080320b2142d51740c440c2080880240007841c1e008000c180000c00795020321480d034010654103030084070100f181340c503944036481910719aa41e00941613080b03c10340d03a005d4101c2c00c4401d00402806007022440140b15070300c2c0303401e607805030701403801190184080c0005410300c007419022080e0300c00c2100340d900d0b00703100c03030016100a0308540c41e0410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 240836088 1250 240834838 240834901
    0x1d01050409022803021c050114090903070605040c1508010b180a0306060303081b03060a150c0209041208091203011a04211502090916180b070b0f 64
    0xc2540d51601d03545080c800030351005a94203920002e000e136010010b001681784d410406c0b203560302072910a03141240c0c1c150700140941031008003030056001c2c008103102c40c0f90205010250206034107001c0d0701e106511581c86404140d00f4491201010342c40442c0010801a42100500c21451418200c880322130004002040c00e070103030400540300c1a410703080103003441c0c207100d0000205500400003d000300450340c08040d0424030020000504e00040715102d40c845041c5c10200054819224140300f80081071604071008021a00441c04001d0184c030304403600c3d00c4070390b051003001c0d0f480303400c4c1398000140001810300a900c9101421a6010600844080c1e070100104824000c2c041c000300c078000e0051070700380c040e05048068011124003000b0820303910301400c0021034a0310079152013200e05007580140003003043e0301d030181c048000390109020802880300302c0980e104d681c090800b40000070714000400039912006841c00840d044405807120081035099800c1c041889404001035081034041902551035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 240837338 1250 240836088 240836107
    0x702040515030d050d050a091e0203031b0708121603210e031804021617090a0e01140a060905010503060d060507020307061107020603010e0a02041805071d0105040902 73
    0x30548031011035051051000e4420100e8004005e0302ea50700c02c20340c0c00c10155131200c5942c01500c1c603801009000c1a00108103520300490243c080c202c0900240440b07003480c0503400000440300a40b00c048001e944040c000b00407151041111b80d140d06d4030010480e041c00c190f00014400240b501400600388044501d03000c550030301036000300030480d00d454000d0022076440c0006079100d502002c248118030012413030420040c1020b00032540404906d146480710510743d52640041070030408421140080200001d24482d030715910b00001070625107481a449525203081e51201400100c805805050030004c20000b042d00202a0002c50742c081c24425520742c0c2e200300050203803201c1040241344e24548424081d04a60010182c030750280b141c002017007017240040001f1883c0c020300c0c01c0254820400c100510489400708045504518a440c001d0308050300c405c0c101215034200310804295980d9041040100c6074480c8000c44941c1078042c131420a6000c1d040020944e220740d0040802d00c0740c0000c1c0c001350f03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 240838588 1250 240837338 240837361
    0x2041d1308030c12090a020102030307030e210316030501030b01050d020f04060e01060906020f03030a090203031b010209090a05060a03020f01050702030f0c0907050a020304090c110d0c0c12020607020405 89
    0x419621040040ea24500810f6100b0550002c0b09000d0780751080d080042d035003980000342a074910342c0580045043d80e842d01c13011800340c25000c51a0131503000e48248942000312020000d01d421140060180c0c403450300c009596100c1d0703450300e101420507040c103004002107064007840c0ca040d00d005481700345181c1128008102080704407c6a51b4000c0d18040c0001206001d04035442d058400507a6021601c9944800483e0703140c803000c0985260344c20030008989003000d1944003c3e4840d1010f815203080c0a214a25140182e500c840344081a0350001500005072500c1c0761602e6110990302820031030350a10100cc51341c412070780d000007802030110364103513035550380120f00350f908080d4003c0032034000c041a43c01d03180d02d0b02040080c2d24001c003810b1011564072030041060300c111890340d60007075007410710300700d040405401d01c28505802d1110051110305518003e002011021175180c40e40d07031100d6018505030741802c699500c8092040c408003000c80050760703420100d07205540c044030041001d071118000d090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 240839838 1250 240838588 240838621
    0x8040b070c0b18120d050d05060a031a060f04090506071409130b030c060306100507030c200117060616060b0409050f0c041802040f150b0705070902041d 67
    0x300c244008180c0c449001c05550200f628004160341c403152000b141004207640e1411741c4080008a01e0a00803d0899001c0d9440164040c800811034148190b607901c40300c0041b1042060f40070001401c4041040c507050650040e07924010940d0100001219a2266a00c403480900000100101100d03030040302c8040800b91040c80c00000c0c0071120008024840600400d14034610303d00901840000d10f17024500482907078030445000c1c010f50034035131500400b00d429070300c5140205c0501071803010340000714810309500303030b008030b041c661740348107840400b001505018064201c6034450218004010190f01c481043da0440100600000f0701381c002840d00001624820042030b810900d4041c0240a01000249403104100001c065940101e02c11051109607500d410000f03000418000351500181802d91000c86002c034040300c00a2001403e00441103040a40e6122084548000c6000b000b8000103100f01401403010130021441c0c1032074241200c0440d46d40310315001200e6800c070000380801d00400400f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 240841088 1250 240839838 240839849
    0x18060301060b1603081803190513121104061802090406091a12060f0705070204090233090a060309030212040e040c05030d1707020c1203030a0507080408040b070c 71
    0x840d103c26840c0002c0d503c002c1003100a500140031072000c05c411001a01e01032183e105400003079441c2c000034450340394041458030b41c40c404000c1704004060140c482c10003943e0161080903444150031001c2d04150580903000c400d501e00c10740c942407040190402d2010420901681424096101c9500e000054000d0503c2d83c40b07c5c0c080d078100700c00c43c54548451001d9095103e822100420600008204241e6544080351038000d00362100002c02d2805005034040d003a02840200045110802e43c1d02240d180c018107019255507200041c65010241d100241031180c1800c070591440c00c00180d000003400d6980e241c41181c081c1590369903d5420303d8400c1c442c0d106c0d02c49402164643c0d0303d6a44040d0030148008581c15290071000000101d03140c507001c1003c0c0b40e41d4806580b0140c03034211134000d854a00c41d000c0c00800a5100c0c04034030524603150200890020b245400c042c0d40c0b289030151070324054134801801c2508009a4008000009882209540076070303c4000b00d958680240e0300d8006101001c0350800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 240842338 1250 240841088 240841109
    0xb09150111011d0706090605030601120e0f060403020d030902240f19031d0604200a0803120106020c060a0309050316080702030c061303020904060603022701050f1806030106 76
    0x1010310038070280c1c050120a1403d0b0040340d80040d81d600d0100c034545228081c0340001202000425101e601c1007166400e101d00c02c4100113001e240904040b8075040790151281060340021040205140d0144010b01e2001d49a003010701120340700e40d001138040120710b08103060314245015540018004001035849951101540690b00d100d004d8010000a100170f6a10000a0606042c4080c4001c28001c1d884e4a0201e14010051a225a030300d039900d03031240407424010030500c44c03444042c0e980c6040d02d400c0101300c4074005e150b0f00c0c1c103a480c0031440c54a050300100195400104011191b8507054121a0509001d2500081d205000e180650561151030581901e20110300c400b5800d2050781d90082c10503510840803205001110740901c0f00d207000303254094250081b100020030250038002d244a07800fa12903200001e146859070b0004d92044040034000c0c1362070b40d81c20010350340248003c9009000d850200d40802c1001304c01c00004440281c00e0030070041c5c2d00c2508000c5000c2e6202504030344058200c5051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 240843588 1250 240842338 240842351
    0x2091012020d150905070e060607030e040b0d060c0507140f030403030f0207032009090f0c01030c03020d0f090b0c03040b060f040e061602150c090d02010c14060f0108010b0915011101 80
    0x10080d9450400380128200d442c907c81c0850850301d0184102c401240d810380f030301c0310600b100104200041c01c00c1c0b444c040e0004071444500000868610415001400310388540b522070449080880c1c0700d000c03185900754647c1c4001174400d00c4002c000240c400f281e505240410008030401c000300d050985541c8020154000305a50000b001c001c0c03071044c105d00c1da050718040c55542d1680303e9070740d65606621856034150001038540c501d07540b21303401030f206d500e4150501502d0305500914580403603000010f1000060f54510520040001c0203031001d070020318080c041c1342181090380b10b0380032031800500310b0391095208003c1000310f926190800c142c0f03039440009440c45460310b42460402105d0044104005004070003440d0200d2802088081c0035161140c0102c0c2040304400601c16034500f6248141d040c004461007000004036800140030075560501c010b0202428031550300c09000d0750680040a032a41419030281807130b00e56200e51130348030481c1486552040104401030320008071020036802c55509000d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 240844838 1250 240843588 240843593
    0xe040614060a4a010c0312020f03010e060120070504180209070f0806010c0c1e050a0305030a0201060605091e1c080702090c0304030f3902091012020d1509 68
    0x40d0f90f0b500d80281e508055030140090040d0405806290f01540441c05450720240483e01c540c54400040a000d40010f24101402c0141c0c000d40e08243c0c82651b121340c90f1810444196406106422918601c0d44074205400080301c0f050f071100243d0059a008554503802c1203c1c61044615900fa40d80d00605080081e08002900800e00386c2041813036404102040045891544241c0c040e40102d50044c100b0708c0b00da030905244c14544002030321441c95510900c00c2c0894565034a044881c001d5200e4402195071302c4141c2c2c00030b425540c241c0e10100c14064240100072003030300c4041c01c0c60720790320800742c42800c0c0baa00000001c00014150703018054a00c050101c80b4100040356008007080e6000701c40441d2143d503135094084803071008407402000508050248030405024402890601600d1488404a42141503100d40407040ca0300004005480804c581820350500c4035803541c01071300b05000b2003411401c106181202c407003400c0e4000c0c020560342001c4010b00c0074410b41d03424142c0030f01205029180890 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 240846088 1250 240844838 240844907
    0x1217031e011509050f0109030605060d05010608070617010608160c0506190615020a020111330f011a090a05040212040b010e1e07020a0f050304060e040614060a 70
    0x42c0081c0010071010480820340d460110700c4002c00200507541d0744d030800d04681e204006020701401300c1d50000c0f110f46a150000e0000c1c05094040c01c2d480300281146807074160002d001c401c0f040488480c5c44044001130212030360100d0a664401e603440b0191140d1085040125200000103901070072500982040c00101c240d2801480e07801c203907107841800241c1d12002d40940c2d901c42c5441090151740170b031164078019401010b1a02d006002d0703000303a07900a5a2010f03280031641a90368000c01681080c071a051407421141480d0740c1100320844031540c20360411301d1143d15070802014400f01407a01040e110810b643c0c51a0b01e6001d440041c0c010740d00c0b40044440507141c00b109590481e00182c0d004004241e82505000300d83c0300b810302d5000d06420b0080c40941141d03507040034180301d085004041894020400b801403d089040c49203004543c0c07645400c0004041100380f4000600ca076051410030003010b0315040041e450303d00d003103800e155a04040781065400c140780070455006010416800102021207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 240847338 1250 240846088 240846119
    0x807081315050a0b03070807170703060f02070618020906040e0c150901030507051e0319020c0a0507060e09010e0c0705100203040b0c0702060d1109120c0a1217031e01 73
    0xf500d8280702c030a8500d000c041d1220428011811203a000060030040700026a2004c415502000180d1380c3d480d88030744540040c2d9280c0d245c040c1419400180f8541004054131a41603c00b10000000b0007c0780668001280e5400c05001203100756101c0b940c002c03003250f003440800403014000308001d04030741102d0680c014540105a9403404a0700d0000000c20b90344c0600c013265143e80170004000044165002802125040035003060049011840c200880309007920040800105e4031004140014261a0440c0b41c65219000b80e405c1100398100c000d09034a41d0081e00341580c00ea4610f9451039644c903100034150780a03400c009130591142c00f00151b10241e09a0003180950b006001101e03440c3d550160f540a1703442034540c001c0d0030a000b00b002c0d8505419560200b131000c417200618520f40140c0070001520700f0242000c219454005403130b418458640707454010010600c07403548110418090700c408090300404414441c920750004001166081400042444001e005154040e15615092161010001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 240848588 1250 240847338 240847351
    0xa181d06040509070b071205090603041b061e030207050f0a120207060311040b0c0703021306090f090320071a0405010e030c0a18090203030403121b03080708131505 72
    0x600b03404909079220116039507042d00c0500200034680607807a9142c20a4090111b000c4080080610101da0320342e0302e8100542c09140164085000001c21038003414410b401944a04203001741c640c44c80703035503031300c406885005000a070a00507191a01420aa400c00041300314511182c0202d800880070450b8054107110005100c0c0d081f6019191120001d038100e82d0210764011030590148010412a12014000c00c2e000e0b8010082d283d01e03550700c1d07000c1030100d08080c01e800c4c00d064a40000748901c51145c40b4001c10902c0020040c094a0b00c541c03009440d914002c00780c180f40d40c90110396114000010044d600041500a001c459625142020b44189801c1409060300088408083d0806490002041d5113022070003070400200c0c0c0e01c1d02c201c65003a0030b401c041150525403079100041c0965018809800114061304c0c04004484144800034119800d010054080b403804072400408298040c001c140d1042980c02c04030410345522800300401c410400005040c021043c04101c102030980d042140145c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 240849838 1250 240848588 240848591
    0x110c0a050f0712020303070f03031503060c0e0a0311060307050708070506150d05060a020c2103010302010306290904020f130509090d02061605090a120c0504020a050a181d0604 77
    0x50f10f81c0c4400030109000f54019606901c10300c0361030301142c1401504585035102e402c000404800e1489603402407900344d442030b5a001d40d2280c07504240c507085030407010904000c8036180542425561500c41c01d000043c412402904003000042c0460f00070780894084c0c1d41c11603a0070703403078040c2c03071610726036a0341c2c210b514200380182864030900381c0c2803803c0b0390140541d0081c00f41690f507842c482c40c04000d40000c2c08000041c40f84411143c02c240441e03e0304030b0a051009a182d66a40c10341c0005800c1e55000c0d40f00051507001c02400070200c0301c103c0852011004c80e5001c10340da4a14030340016000c1d00a52603580c0901d10006400a031032030104050b801240e03400c0e5a41a500d9407034107401502e0300c0c1c8005500d005038010b600015440d600391400c03225504d5160820030300b04040c1902141101c503050300405440c0154010080600140d02c1500e0003d00c01182c0a40c60020780c982c0040890080024010501c5411a1618201d800a000c2c0b2000313442d03030641c903031072010301920300848135a802e4a00301c0c042d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 240851088 1250 240849838 240849853
    0x1d18010b0d0f0c120f0b1003091a220201050904060e040b0705160b041511040806060301021314010903052d07050f010804061e0219090e0604110c0a050f 67
    0x842e000d01510302c6540030381c0c4508911801c0c8078884c2000c0c0c52103070754044603650758050710802980ca20a00302d80ca2292076400090070009403400c1040b8280e00d40002c41c2980e0164101309484d01c00d03001075170796644c450300d0482c00c41109100680d0207020300c5104580c42030910350085011003104000a1050380580000440360f00e45100540b61031083d904c0f5513481d07120700c0c2c1041c000300c0c514444658100d44241c902c410503080362080c03501140d40c2c24a444070441c41c00142040081410002c80f034218100703c00840c0b9180796251200e40c007a0881c03080c07440d0b10081010f0501c1d40c0e0300490700900155000019103075244c10b99004a07003070420034806c4600880803426060003503040010a8000e0710005804880c00000c0c0304010340f10190010000c840e15a1281040360080c0076001300c15021161140e00583c9072406880c042c6140c42081040100300300064100700100002c2c0115280c0254090f200018215144141c011051081d154011071030700c2848444010800002160340c0e2168070a42944d645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 240852338 1250 240851088 240851111
    0x309060c0c02010503060f010504030b15010908030c0601060809010b1f021b06030109092906090708040309090c030b03070f050a050a030507060f030f0507081b0405011d18010b0d 78
    0x80c0e40350756006400140248000303486410811680103041805051450038141d03207a0301c600c1500d50890b61a203601201400c4545956000311103080a40ba003900514101840304180c59075981c0148a07500400c000f0402103001d000d001c1d48a60a4048040d0584d040385194a01240e251444282e100c2c0052140090092011640705d5040850000003000d8520f0359181401170310182c40c00244c1a95803011216030701d800760002c2e018007001c0c482e0505500000c0d00d8500100200f46170000c001c41d0901511804100c0000e41c8921442c098070f003441000245005e034418112300408084591940511030144041541c60010f0790f003c045440880301c0700782c5d02e6120303000e00100c003006210007032040d8800c10341408130394081c0e10000c107844260b00d0002407500414581d0010f03524140c65a8010604440c1172210790551003107015010001005203034500b074a8200006c058400740042c1203001e15a90200c080c0990301c40803039911002c40702d80e5114039543c540c42c1d0f402070b5078007002c20703420003503d0455401c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 240853588 1250 240852338 240852347
    0x6410706052a0f031e090105060306070e0d0201080907050a091a040605031504020d170304020f012307080c120c0f1b01050903100501090c12090203030a0c08040905070309060c 77
    0x90302d00c18002a00d040020001804205802c05003551841d9003510b90442c4480034400303c420b00c5009464004a42802e25000349410300f54081c260701d04002280d02d41202c0f80d00d400e00c06019096080c42c29101a6452100c0d03d41030403050303041154800c04d0070200046000712504030580c000c01c608440303180c2a891070100301c111203040c890b260f0107030850102d48001110440700b10382e02500180c0a41000501a80c948008401d11000c1000d410404400c0c40300354180b81c0740348680308400b800c102c80903c03400080084d184450554105200d0070000c1d000080160036015100c2c1c07407500404541c03020350422110601500070f52845403640c418003450041c1c035680002c110911200d55075400d084118400011205175100191054161181010203c4162424495a4001c002c218400610307a80b03a224010300c10040c5490103941641401a40e40240c3d0300442250075156240c103020705915101e141008090103035030f102c83c02692414042102e4030b03406800c2445c816114443c20400c5444100b07060b503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 240854838 1250 240853588 240853651
    0x60c0309071503150f03030216030c090f020c031b0d0306060f110a0b090303150f090c0702030a0f0b04020a0602011406220504080c070641070605 64
    0x1415503001c010100500300294101a0082c809460040340030101012555400300c1c280d44a242e00040d4075404005156040c411a0804c1c1c2c0410018550030345541c880d00c51001e01801030455103540d03500320448a81d182c0d412070302a440840305903074a52107489452040d030294110048458003031100c1d19a141d5101c2d03c602415071343c140c0c0b0341d40056020b804e411189250070060902d200d00c60f00079040f001c02d00300d00c1024810102c0c0401150760745010030350441d4078105240e42034001c01401040c00f07104d6445002c4250300c02d845180c6503071180e0b610300000e8501000008003910b50180064804103200a09550511460082d591020055900c0b1422800c9403012801154030740102e8020580503d0b15840800b10940000c03500d2003104101c0c1d0700c81080740ca0580e001c403030501c1d000507140301002c400e01001005103d01d0030007403400e00e0840c0329401e4010f07401d01c800400e0103c0c00001d03000c501091059280c004030850040b91071f1216031400100400e001d03220100e031aa0302c0305001d10000801d030b2107034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 240856088 1250 240854838 240854851
    0x15040311091311210601090b0d030c021c08030705030103060c05090913150204090209040e0102030f13170a0c0308060301110a0305040816120e060901050f0702010201060812040503060c03 82
    0x500c5082d00d2a12a0800b581d080342e10035500c8071018002d504401c03141a241007003404400043c004551505041108a448603e1803602400c4040b424102003908241c1c031281040e01034441c1c030070303e20012488055240c0518030050003203c0100031721401c980e0001c091816648503040030004c0c0e05c0001c030b040d5810f01507241840e41c080c0700c860010f502007000c7c1150420491081001d203241c0310154540c041660000d4020740070b255400320f1040d406141a01412a00c0c013205402103207103050605c002c1401080042145102001a4000104100b281031096000b402d050343c0148e10ba49080000914030725400c0400d40c000b841002c04034100340740610034001d084010125040c6000310035001075028200042098405070f500744541403c2e030112410520aa0b0f03c03890030039203200c560384009004103c0600c030150052100b0b010640459800c0303421240b646282c800e20b16112807035440101d0240007030f0381000070315001e0b03500223034003030b044402c003402c2515012030075145142d54403800b4030010300081307442c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 240857338 1250 240856088 240856111
    0x6010f051e011103041e1a120c130f09051605090d03030b03070602030306030d0207050109050f04020c0d090810140a0207140601030503030106082805060402091504031109 75
    0x80641c044503200c11010328001810804000c01e58560060304540050340012003440001d410100c0034000d503940d4070040d0010b0845104c12030b1303011200540754082c510720b4030091346040c070210719150860f10596900101641020f1007481d1a10032015240b4044c2c480c0b1040103080ca03022804921403205c120443d0149583c4a5051001d203034200070604102c01c4007a018980e407038900241e140c07001c4c09184064013054004641c0e82c204002030516000603a42010119089810103000681e40005000c044640c102d42c18040785c122030000030028440e0605070039403842040c81080382c113500264620110794460040c0e8030344060f21211b1000345c1d05500324800b0102c4d4007a000902a450702d171b000c5c003690342c0a04551040078031100080d81c904502a0070581e095800407004005096000c2099944688110345007103840200102c1c440d8198698440c56030202d48450009020781c94560540c0d41d64400202081c1c0c5600401c1c8060309240e10038002511a02144c0303c821115080602106000e00380325800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 240858588 1250 240857338 240857359
    0x30509010f020d120507030f111b16060c030512150a05031b0409050a02030307061e0c020c1e030d030209030c030102030f1302040f020c01050f071b031101020f070308040506010f05 79
    0x1802c1005100c0200480c00741079917044ea014004a007441101510271500e00310a680b0b40c03130b4070845844203c04a505240035841808070100c0b13134140c55480350488103030381014907001c2003518003501c56015101d0134080341c00010b070030802c035800d5104080400e40c0d0b0655200c2503143d294018161038601600f10440d051441141c03103036241c101540300a400300c1c06007040e140c0e60046c40e40001d041d94410107003581c4139030701c401110218000c3d030381e00721b605041c5c5101c003040510035070180a901c40f541070070076910074200c403013010f10701140c40383e541c40360340000505403104600007600c00340007508281d4810340244a0102103010b98201442140d00074002080c621800307944640268851008100003240c00c07580300c0502d14a0900c1d070b40003412169448c1800412145003400c03203441da00000408403410003c28000e0388641d0071501c0b0010000c40e17050701c2e01d540041c0440c800c46005e4800c03d1a4030485403030000304282419404a445d602446c1324030190f40b0345982c0d44011121410a5000342c6a11002106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 240859838 1250 240858588 240858617
    0x110c180403090b0c1513051911060405010e0616060c0f02010501080c010c12031e0203090c03010b090c130308030109020a02071a040902070614150f2b140307030509010f020d 76
    0x24416401101c02c0300d086c4c50300e8596641c86050140781b1042184031701c40402603008102d003604080704d202c6800d4411504103868000020400482141d42500036040080c06600f220b803000700c1126003030340118050068144401004154410b140d8401c03006500e08000860200c0300401d6125035028165241700c0909079684637946880b9003c01c556090542c0e6070043c50720807aa100040c0d0800c59444801601c0b8038024840d1410641c2280200e8826450309000d030503142d656210301600021041e00c0d40791030341d600c5061080c2104c9107802c098100e44000c800020509607a8004142401d065030954225555507043c03440f0500d91681921410307442840180810001c590113020800d0280700d004c80c0d080002c014000c5802403c1d07580a100d1a000d600c4a00796040c400003408840409650302651104085103102e1084d0354490305074595201c0101403420700085101c43e8016110b81c80a40c1d54804403450302070820f41c00400f042d0f010410180b0600962400421030f2210745e6040d0315026003c06c40d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 240861088 1250 240859838 240859873
    0x20c090402011103070b0a0b10080f010e060604030605093703051c0f0b12070b18030c0303030f0a060f05130f06080a0606030c0f080d110c180403090b0c 67
    0x140a1046181300c14003005c0041026000b0040c040d01d4018000100103072440180030070311001d071800b03034180b000c01c3d01030141940704007a01d05d044401162244140e601d0f000e00240072889243d01c090010390030901441008280481d941d41210034100c00c070b0121071388825680b520300c40c8106000b10740110307030000310000c01d0140d00189801c0800c0301c018141920045285403c0316010401110055034640600e002401c04c02c00c40c88054a10a004002a81c03070f004c2009003d115000710004409090882610182c40c100000070407144000c091760344910384882c02c984c13040c10440d070741c92507541040c9000419803107100080e0f040d00e1000d000240f403400c0c0b2000705d00c05406102d0008040b541c0c0d6003000100703e40e00340300c42940c01d48541c00200d14545141001502e9401c160030181801289580400c074540c4000b5091034840000e0401000302c1da0407840141c107040e20b503091541c02140004010f11400000146a172107903100341c541105081c0c0f610840000c5024510307040e4401d90120021007414100c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 240862338 1250 240861088 240861107
    0x10e0114180603031303031e03020f091302040b0a05071208040f080304020f0307120c0b0301150809030d020f07150c0207170307170c0607030e070506071a010803040602010b01020c09040201 83
    0x140c04c4a10380403210041031185c2d40035900940000d0640c54010a0f40090802482c413150030a140a500b840e0808035003100758441c0041480c400c078940312550588000c143c040e035004010b81900162200503443c0c01512036800700c0b00c100c505280100c01c2545280c0100b084034015904070760304100c142070a0b5180c1030581d1024005a80c00124a415807010707a601300241c0c0083d000e00c055020043e00c0528010a204100746c0112000300e005100501204908001d955808034142c0341046c2c1c00c0e100d0b4400c1a00f503110345070101040c0d5000041013034460205030003c1060718030611038200a8038228450400f1104003200d94801030700400c10412a2402c8089108080c0c41140c050741d1818210341d0350054132400300c4503c1448004081036241240b50180070a0b5841401801c1c240030019403e60780301e444600f01d01510f40700700d601089a0007403141c07003491200008000704501600796145c80100350340381c0207403089c480107600381581c00400d54404111030054020141002c0e485407950782c01500c42c081d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 240863588 1250 240862338 240862351
    0x309050607111216060806030c09040c0905040c210221100e0a170c1c091e050f010302130e15060d0b1305190902040b060403050105010e011418 63
    0x790840616003943e030340e80b2804400001d076070091550b103900303401d107080010455111800f40050700c4104540c80e01c01198010984000f00c8805010350358610344480e00b002b064109001e02c0b403074001040f0400103024141002d8404445805014400042c04180b000c40350010081d00320848a00000541d03204000003041070f500b00c81a03500d040750200425017242c180c0c203a0450300f0790040e1114814007143c1c1c602d0f050b40460f41e000042c5028030240312196038050202e850000d0f1415044240303d200d2140e00e1034406000c40313240319500d4002e6018010042d8442d030007080d20800c049400545c0039800b074401c0b50740100b1400302d14002c041c41c001014112050003440082031428140352004580da91340300078032140882e0000010040c48900500500d41c291141c00780c070040c6000e05010300740d8402c41e0304021200882c02c010850613250310104020302280c1c1143c5030420300200f40401045819004541030701e0440088188a85e1f0702d41184038042c100e80c0300290030182000511250201c00c41e103c580c01003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 240864838 1250 240863588 240863603
    0x4030327020d0c0b0a0c110d0f12021c03050f09061303030e03040e240d0b0f09070e340801060c0c15030e0d11060114040f150303090b0301030309050607 67
    0x140c1e2130107141502e43c41a0449400aa1041d928808121180d10f595940410035075400404501c29603d00c540c4065002e0301802e02c0c800f11600841540c820402030032003284034070342c04e004c0b131840401c0030700542010348a8000000030f100c0060130b01080042c1141c4680c02d90039101080d8001500c05034014030345035031240c07000c2c00300700030100e14001c22a0344c050281e068a400c004001d1003401e2003100d281c44813580944034884088102c0041900703096025080074051107480501d484564180e440c0040303d0b030201d4030707403a000000c010b003e40e040c6071424012844e00354035800c1083c1a0110b48225010131019030041910400180b055900c10305d50ac1d0300d203a1127902007c07620364840d6002ca9803001c01d09100000a03488aa02803e844070510480a40c030495061684201e80d41c1d800d8103031205414021035841042d00021041c456803a500201c0310042008410080c62802c4a91407101904502040d00410701560000501144040440c1c0c100d0307070142d940d20403007403c2c04100039440d0b00c855415100c04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 240866088 1250 240864838 240864863
    0x2060f1b12070207031703060a1a0702090c0409060806100e06120f06070f110c01030c03090c0f0f050303040b0a08070e03010c03090201080115083103020604030327020d 74
    0x1085607058660141109800400b8251328600e8600c1642c01d02000050150790180140013143c0c0f6941000b4080c0c89203403421168801c81244034000c507014166010358040d0000f414002c0310300c680d100400503100c002d903081c03040c0381e11841c08941c3d581d8140c80300401d40704581c00401a807140540c0450308580018408400c0d00500140c0d103140112204c0c00380d14036000744042c0400560042c042c000100400e0400d42191003800310802d49401002200c01d0605498081b511881d82c42a8841682c06500155078803060b074070350581c0d0300608554010b58000d5410300d800424146000810f80d012204030014142c601010031608450503100940200e0034014030502c1400150390a000c0e40411504590300024800010b000041c400401a03126154150f854044c070040c059000f000303a036012010b807050060b0010819408960680303019950307082041e001c03001c501010b6000c0f940d24007603070181d41c040c0f1074030545425011840720f03140034940c000c10411140d0001030400064403241c007401030790b0308401c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 240867338 1250 240866088 240866107
    0x40b04060b03030307110705150d05100f170c0409120f050f0403060c09090213060c0c030501061502011b090311040f0e03040501091409060108090109020a1202010f02060f1b 76
    0x35130b00141c880700081001d001c0c0350210400204041002032400700e03032036403541c0704001c205140742c0b0038110002c1509899a0003e9074080202e40c141d0b00800307030000000d0805603105181c51502c0d45400d0200703014040c0640c80f08052070640103445646400c90300003610081010030a907004285a0500001d04c00c2c2408203261404159001c1d100850140c3c6010039107000f224801008103644d03401c0703984101d10610500c3c00282080c888013066410b2801c02c0c0b08106000e04202c2d51008a0b6800202150b0070445c0108001c0302c6041801c00d0741c0e071190028401100502250003094403206100c00015200d0181040412201111000050030161000460703684241c83d070b40541d40003e4030148960300001c0c040080c0e591282900c070082801c903003280004004080018000b1a010309880e0410092402282c0090002e42c00198071a5000b040441d07555a20b8104070310421451405901058064a454050310f00220703100303108441d003501d103041700e0b41c440d070340d2400a030100f5144001140c030a000d404007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 240868588 1250 240867338 240867343
    0x90a0609060b01081f0603021e0409090c0b04080d0e12010f0b10170106050702030f0d12060506070b0105010f0207031a0916060206063f01050618040b04060b03 70
    0xc2402a07001103010603041d400900841000707030003245510300c40340b4019600b00c5020070610a895031031030091398981021502806407003880e1100880504001400500280b4550221000c14170442e002c4c0c0c10b1641c6c500445000c2e01a0307203c2d0014a0700001d1046940324401c4814001e454401003026031101c00800c5a83d08540d808500c0200040d03583d03900da10a031074018041c240c8128945032041c0380c00440c0d0b01c04040700c030b410b10400051101c00b240810855400340648140f00801c84115114402d03240001054500e424030f42505242c6048404501e500344030b4103c8001603005288005141d1900e00111521a420070000085000c0e00f4800700028080c4045a1170f40c102400070b80341e10341010f0b121581400d0a00c46100000400304804111654003c44d9003648100c0494a5003022020040d0000c03083c402e4500c0d08580d070f42180d40d0f400340c0d1030b04020f0400c0b0741310310340c0020049565907406210260600102c0c4a00d800301d20700c00100000c150180e140d502511a500209181650101103403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 240869838 1250 240868588 240868601
    0x11803060209360c0a021c11060403090905070c05060f070504050a121202010e1f1b0807090f18021c0507050a030b0a0605070b072705031c090509090a06 67
    0x110040c1140c500021040f11001002e41016084903914640f000700c42001c0e40d1480340c200700e4a802c000e483d4a111a190103000d4083e24044988241c603214509494000c01903155800307020710b9285040c0200b60740c544500d030000000756000d0005d24407078803042341c1c107040e605001304400c040140c100408100e507180c0d040c441004001030030401180ca41c0c207141c00b8030441c264902a404680c5003903404000e0001c00501f01485c02a10701c0000903a0307600e0202c20000e0301c521201c1c141582c10512610395400d5014540500c2071405580d120724040c2c03a1103d9005448080c420050211040d01300c1c403444580da60f0040500090030f10f03003000721203910041417060312803c441100100e040407880e00b600c80d415001d01074000c8422a403070890f0300e0030100090b03e030740204040645107142d2080000d402c1400350010b506580d02c41404040d080440001201000c8403d0203814041d000e03d072003010040607070740d130312441b1005a91620500c0c941010148820240010040c0c062840341c4140440030800c28480d45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 240871088 1250 240869838 240869899
    0xa08030c2a0c0906122a09040308161805011d04060b0a080f010b03151c050c210c06070503041503020d06080318120c09090a030e011803060209 63
    0x9018640050301081960b04005180754045c16004608170a8040041010003004001c10f2800d00c04e6860466072010700f480300110a900882000c1c11301c024590400c0c041071140307100e00310031b0500468807041299040803201c4140101c11001600b4040703580504248882c0303080e1100722091404803507001030180d451590040000c0f40d40060b1295080780d005104ac4e5204030f02d0700f00180b5030351404130200b01c3ca210052840095818581c0018115a9600c224030b002c64022550ba410701300c11800d02544403001005818420b0340c0f9459110800c00a0030341202d03000d1916009464540454001e0100541c1f220300f00700e80b02d0008110101d05000c10798440005030310956001030f1544143d001003070848510b50050041030b8024000c8000802c440414401d001c0010303900251480868050720b403a115031543d210b0351142071102042911040041d8000506001b03131303580c0b9000c000d10300041d602121890710654802020b0102030000c0340c42e9800905000034040c02380358020308006800881946050880c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 240872338 1250 240871088 240871093
    0x2070c08060106020d08010608041113050105130e0a080309070e0a0606300f020d0911030c0a05060304060e100e010b0f0f011b05030405060a1701080a08030c2a 70
    0x3405941000c0010a0140889000400c40d00010b100e000d01012014460201007055940c00030303041116201c2140311058024201100816107200d200d80074103424021540103a003190304010b100e01e80c0d400707092130204801001d0f007101500784c3c48504896000815280c454401e0107000901103003e070010910408a0355000074080c0c1c204600201a032540c00b95039501c01502400114a4010382000700d18428a51003001030200c150540f450301130301038200c010440714505201c03501449017200390300c2d62002080f030580340c00800c16010042c5071103842c028035070040c205100140005d646a880700380120344a0781180c80d11023132850f521065800104088089944489004085080c1002e0044502204548140c103160041000a00144004842c800241440c04070f400c10300c8002d00884024141c040c24895450f680c8900207030202043c030020a040b64000350000402081c0032078035401480c0d01844083c0b560300c0342c14070603003140c12011400180d51403002060890381314011111402400c580c02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 240873588 1250 240872338 240872363
    0x90112020909252d03092108010503240903072301200a0c030504030c0b09181303050304060e0a05100b0105071a1b1201170a030c0b090a02040207 64
    0xd071240f84522105110501203075030b801c9601d50610310300200c000c680821100e511410074000450240401d54405000c0c060000c80f0100d20880780e103180a4080ca10b5120039450b41da8407010305546d1a030001e20179550040c0382029100c00328488d81402c0c1c000510901310783c02d0210a807200f080d02016050369108043d03a0340003822444200b80982d081c001c1d01c204c01c0140c840d031401c807102200e100d11490340f010001000240010140180b050b2400395400500d00090349440b42c06082d1141d00c0030340968814000702d100c1000200151503124410801551a400c2d200b50541e8182c6031034101500031541507403a8620034400c194108624101c0714002c00c020204000d440c07107560704072140401e03140e042040820428011401030000c3c025803841c0300403e800300ea95200550544410005011a01e02c071740041c500b401d01e100180424140c0b00580c02160011454440e150354070661042c0050220342d80c1c02d0007102080da4201e6981e40103d60100750b1712103502c0d90340028103c1c5d0165104460119003580f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 240874838 1250 240873588 240873631
    0xc0102040e19020304020a031203060315050423030706050a02090409120e0a05011e050903070b0903070e040201120c0306081002041403030901020718060f060c060507090b090112020909 81
    0xb604180200c02c01041145142810380200b03a40c101103010150904804115105980d4800c1e44048019038000c548110b00c101d012140602408069900b603840d542502403190000104021b040c410120700c10003180f400d0b0240e0748a03405048014424031040d64241314260301c81c1c4490082215051103031804d158511180c100103400b400d1200c55890080c266800c003804941d81000c403035445400c95925542c00c4241070b0364112194071075046000e805010300d040004490862a024103441c4400300c3c1a00c8266803078a20f2010740d00c10445000e80011440d03503900b402c020180d40241c04614182c903006c5161034440000c0351034420244100d59586038001001c0018000c4280c91b1000ba1504801a5182c02d02000000b55134070524000c641ea6035841a80d11104403201e94485c07001408040c00019a10381e40301000780041c4220308003581c2143c1000002040180306001006c00c0c0d132041d0b002141040e070f15400444403c2507128540900541c00c228000f260b0740d6036940c0510841c900103201c2122019031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 240876088 1250 240874838 240874861
    0x21030406061e140d0203010c050a090e191d06100503012007201005040602010c020106050114090102100203011202010f03050f04060b010e09012d0f1401050c0102040e 73
    0x754000300110a210b07841c1c03549140448144400c035075090060f035000d0002480000e0711a4941c0a00960545c601825032400a4001e00070313124049540d22a04c000503a03500d4001c8401d1411598001c03412903a003240c00d810b04e103e40c48088001050240c81a905841140c185d20b040b00030341d0070500000e40c0000400551070240208220b200c50072a43c2c071450004210f030718019002c2c1920040101c0d144800e014105120354070b040020140c02064400d202044140190140e481030040b54015401c00044002503801400f5803002c42e00180e458030b1781104c01d0001c104081c2c000f141914118041c400040c0755503881c50000d94068015142d50140400e0030780b00240403c1414005403003454141000c200f04155184200e99006400c240082200d55039030b401280c1003c1c0e69004141d1102c102000031861001110240a0300c4040480c40c1c03000d41e503c0d41c11260709070468858008980980d074030074451504501c69a04640c003044c10a54282042d062040782680c11030b4000440c502004404c02c420314050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 240877338 1250 240876088 240876101
    0xa020301140604030b04020d050f030d020a0e04050f04060509030d05090c181b0904020f0706050108010513081803010209060a0c1703042f04060e010e07170a090521030406 75
    0xc0b140546400c1c80c6a0f1006002800184041e205110500e101018002c00388044030121103550140ea50711515031690200940100410b800010190741e40d00c569030910b03100c2c650140079021b040c18041d941c0c03640c2e0307100500001002c840780c0d80001d01051500701c0c440e009a40c05400c400d005440e080110b0010300120100711136120313060b11207080a2209003960340ea0081c040011041700035030b0340c114081c045006807240070380d4003820705400503541040c440c1e075502c510306035840340000b0300150315a50882120b104400501405044007003040811106240748043c21605c400342c000350038402d8807000144590070029100c40494900c0c0f0380ca800300221048040010341558080d0f03820360620351a44002035034117950603101008010104c1d1140c1c02039004424940c1c400500900581c1c1c0c940c002301c1c25510003841102c0201c680c040104260301d0080c11101d508001300040111980d4a0715a030300e01803e10307040140c0d098041d0488100049c1440e0340112001c0958600007507880c10310f8a8214200c0382c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 240878588 1250 240877338 240877379
    0x10c0801082b030902030a0b0a0b12010c0f08130c0623030c0403060903140309030403020f150909100302210f010b061c140906160305040201090506070305070b0a020301 74
    0x26025080105605580c00003141c0016a00d0f00103100041880481d250542ea080013030301c009106000c01500b2846904001080382095074141070054040090600f03807003140b0b0030343e4042070400d01c548074500d20031211130358410f4000242d451441820f4132105d0682c511500140001480503081c18840140c0610194100031600d41e49481e52411481e4881140158040240f505840341024000d0612813009045501101012143c0d40d081800c1c1c529960703030262000300e001d5007880110286500c1e01104140340c4c0f02c08140414504000c0d201040720400000b00340c100c03021030003135000c40540c0b20642035000384d80003014016810b545081d800e925080b00903140b058582e060062070902d170740740e80042e90701404209a007440d002c1004031904001d02084004041c0d4140c40f8000c0044018000540f280036001c00900d02c88000050783c0e0072825100c0494000c1e0104136244001c200c141040c100a0801c01c2c042d2400e181460365558400050711400d030ba4246040380c000c0014001010702d00107010310f199 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 240879838 1250 240878588 240878623
    0x20011805151e0402131b090f080c090604090f060e1605030f07060f0509032a0612070503042904050c0a080601090213080601080303070e09040b060f0111010c080108 72
    0x300400c20700740700b8250050009001c1c841c010006480828180c01603903119188543d400c40300903260390300800390342c1140318850f01d0034001140010503034801700d11095490030250a00d10a603031210184000b8150340c0004aa1712246580001c021a1262082a09201d081405007000c80e407200000d641012158010301d1080e0841d425407800300b01c000680070102d0715241850040080101c07411754150064203001c3d078150040c1041c110381d1813510741811810601180700d03500032a602d0700a0182601809015080d124030350701c04564100c0c05240074541c06071241c1b011441031b0000c0d41050030701441c5406101140d441c04805e21040100600c0800c0e00b80005654112000c3c1c504482a6074440040c402d01d0012a4001419180ea12409030741c030026003607040840745103595641c00c180d901d5008035001d500195014480b56a5881d242c0501d40c000c6800c841250042e40780c00d41004190b81e44140c103141400702c0440c1c0003504c00401c1c055169000e815880d081040e61400e0f1f481402c1c202d04040051810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 240881088 1250 240879838 240879871
    0xc030b0f0634150c050306010324090501080d030204060c151805030903070608060f0909030f07150c0e0108010b130f080106060e180f100306060b0304031d012001180515 74
    0x1590080c00e499007c603091a0111788030307a02c070414407210f91101c1d5800400403001c01c00413400d52080d07000107040301c0b90041141c945519100b0210120b015600610780020b40b03000d480c034042050386000c5440580c3e81e24002034038007095242e4960112131050304981d5504080703409411407070300b48140c100034402c0e42840d075403d24040d40010785000c0ba40a911b03108030000700120b403201c501041515502c081c11a103039076964000e400c0007092454262007042e90341741040b0568824034424500c10004400c1a10303074000c164207102c1210215041150300710380960030020300091098000411b00f00078540c85000040007814104003e00e204101071003203000340050380200580400d1220120f9100160030703107004161b11918542d00c51020580d1000d441e190030000702042082134113008500891203a1500700d2075101a1140704010b10b80303942464003266042081b0594500c04a1b000300042180c80e00000c2c0c424000301001d0851302c401c200031395840e44050030340b170080c1035030756500d03a0000406038018451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 240882338 1250 240881088 240881111
    0x109030b1b03040c0e0a0c1e0c0f03050705210414010c021509100804050c22022206110c04180503030405010207060b0607241b02060405010c030b0f063415 68
    0x8d204402c650f02c0001461100006403d40f03d1440d64200d1a03100488a05004540c00c0040564108510542d11b50280d9405060301d01580e40b0071803160718841013000c2c141031a00400311648000c0c4004c2c1818050400d41030001079036045224280b4002070200e0035112044501448240c0c0004000c50b414000d46105003c00301d00e00045401c505407048800c920010001071004001c10380c1c0801c03c80466002140c103501c0d00c4403000e58003a401400700c0541c0041039480b4411602c900244100c2d0129400ca1024041c40b801c140d08044541c420725180c482510f006030f52010318690040701e083d100c0ba54089070744070030003145002d00c0391071043c100c84142c02c040d500e40b629000380c04900710b403952151034207214401d40d103450f8002c402c0b005a410818041002004c10194075840c04940031241075190050070b2038640c1c0284114960450081c01901c003036101e032814401b10f90700c0708100482681c0c021154502c0c0401c203030449000800b0b1103404901444603454150508486610100030950400f03000701503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 240883588 1250 240882338 240882347
    0x3090806040f0507091512051f0606030c050306011e210204050307080c13150f03080d1b020a020d150c0c05010c020114040206091f0225050109030b1b03040c0e0a0c 72
    0x6c0d01c7c0b00c08030762901e0810710b00d013440ca0002e1681845401c007400c000b43d00061415544010103c4219480a00c0082c0a4450451301c40c4821a00300d40030840c80808026140941841c50003141040e0400510094200651004030944464082d0b1103a4000809100c1070500380203a078020403c5400a0001c3c3c14020005000584903101000600f0360f40c644d140b05500c100641c6100800e0184001241245c4a0428001692045d104050418101082c0220103482c1c01c9410b81046d135560301a00d8100c03003550030006030b01040f142c15108140d0034081004000c500340300d803121001464540440c0341000746091800c1d645a10124001d5900d00603091465961080c002580b01e981150031a0340c0b6002940041d020280e224055401000d0040b21134541d160002101024180c0007120321801c00050f00c01b6850320b1991b402010f00241c58840100001001c8407002c2d604080561100b480c119003c030303c2200c05805c03c41f400c0c1d420041c00103003001aa010f00c2c82058000d80c0e40201803280d600d0200c800750 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 240884838 1250 240883588 240883631
    0x304080d0b060d0203040210140a03110712080403271521020a090806090705010305040f0f110109060e010c03050c0c06031f050607050a080703090806040f050709 71
    0x4011a500058400540c6003070341c0501c05402004000c00d40741c014620808009400864040303024050310b41c0390100d0380f4080c0da0002c103035507850840036140c4240340108a0290207880c20103410640184001c00c0021440c403800d036814009503403602c85525181c2001006000d1880c0e902c0c5580341444208880000311586038001d640801c62580c95403000c126084401c8031a98040741c460307a002042042014040c0c0d002400202090381c0d800c0084c03911032008640301e4805036280d01c90383e444014100925402a0807081d84213001c0c61003420310307000c142c5550544c105c80e08030031140842145104080741d038000c60b002c0d0141c8524034014040c01b08c8038001904000e49007202034240704002c985141240030070003c101c41100c0c00b03001280c17242825059805001c6081140310b0a07400703a00c80100e500c0c08d0410a0b40d000b25008001072016080c1038641c490181d00214003074040180e2080041a110340070400035010760b101d807482c241612841c1c10f100b81040010f1300202601803d10381004102d031031051200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 240886088 1250 240884838 240884843
    0x903101d010b1c030e011b060509060108070b070609080415120c170403120f020a0e0a09020316080405010b090114010363030e030705010512190213090e030406050304 73
    0x2c4040c1c05d0050016a40801100c01d8038200311541d40c80e6400b0000c1c650441801124080111002d40c3d032100b0f911611551076028131449030b8800c0c03100f20702007500342d04418516809803030320500d02034a4045068968a01e02820404078400160144903d4038a01c02c1090411092030a00582448650340b46402d00703000c2d0002c1c04100c4041e0001850360160750003203022140c164070441d511008448054004890000040e00c00d2a0414001031403036180d00890f4401c4040d40301d042c4039078541480c15280e00101034010b50300340d90b03502014015a1500d08030f890191074480315030a080d445150004080d078450300440711030350442e500b12014800134030351004072055020840d03070f8214107000c4640300f01d49c5d00403901c2d2a080d18418101c0744c609403a00d010742c01160085ea2034040c1030b00c40d0303c117140d1f4410300d5203d26800260200a402c2e08451400641d40d0040d260008000f0300c001842c4281d4280d8104d09030100f1529924001000304054503c210009030108030061410280707442d1029015000081c8007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 240887338 1250 240886088 240886097
    0xc0614030412050a210b0906040204240e06030a060e130c150302130b04030212010b060414040b030d031b03050f13050a0f0515070c050c01050903101d010b1c03 70
    0x4036490240111510400b000403006038002c0403905c0d8101102400c92642c0440c00744041c4000310320142084d00846003900c840d44103900c0c880c0441148180c058003441445010003101e41c1c0404e940d44d03104070046004500a4601082c000c4c28494040d01400c4040c0490441c41513407412003000405a052100841e002d0010080b81121044402c0d0042e02c0750300040341200300311840104000100001a1040d6402518000340e131540301c0801c0ea08940111034010f6000c03809100070042101d59a030102c80d00d11000c0e0002c00d80c50262130100707142c04442021500480d4440c1c0e50406400070030362003000543c82d00e00e010300440c10101c202141d04480584445652074000401d00140030040091480941c0d001c40d0241c008400750a020b512440c07038070200d0b080464032002041c80517104a182c40310803500003000d054503003451001500c581c0c1c401031015805000302c0849410003d010302c6035062910380b00081c4c9500f08c154503170050031260240e40792407207020440001070a11501401900d24503504d42030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 240888588 1250 240887338 240887347
    0xb10170705090c0c0a0c0303030c0c03081906030b1006030c02150402060903150108100b0901060807080a0f020a02070312080f0a0203040501060b0c0d0e010801120b0606090d0c061403041205 83
    0x242c0c3c2e11030b004c204502c83c46481218420001c080901c00c08990090350204504810004d0840361400c0307144c809800503119001145507000801410404c0f03400101e400140e5650700c2c0d907003020381c1004850720b003031301501400e00304650340d00750250306e140c491284060020400c070132704040040e01001c5c02c0a03000302d90106400c003c5403010404030000d100c0402d5604081c0da91a41d000f0f544208441c0400c01c418100b04140d0010304003000c526042c1e90191b1259036803961001c030221500381000385280141501c49056400d460118801803501500540c060101c0d6821420310558200c13640703402d101000306000030010011403808446810459082002d640c0352a903041403409070826401032640c2401c000b441d2a542c00000842072001c15503030300c3d1907124032003000055581300400d00c504480203000b2242c00001564120801d54420001000d6034101182c0b000424503078001b0034021240c05d48100d03001c0c03018a40000c4c8880c0a0404561981d256103480d0361041000c00085d40100706100002c507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 240889838 1250 240888588 240888601
    0xa020a0906050c010b0604080a0c15051803100c0906080915061c1b09140603060726010914100303050a0503071209051b1203030105090718030b1017070509 68
    0x1005100038045c020038480d2503603160f401c070b1912841c2c9040100c1d08030365601700c0014000f188405c20098001c05071a03650602071806400d0148222003039040d82d150040d110034403000c260b240301d02000260070741d9401d0141400c0400181411a0140c94440254032905520840d41d44149000ba4051400e4502d6109509920b90100c0b02e01c51038039005050040124207880b50030800c80481085810000e030500001009c3d00c0c421010f800701b80e4a25030542c0080700000d01c0325002c1c0318071420041c94080180e140c007201d080d0020540c0400c2e0040c0d18019190094042c01c10400d0360160740106510000d0342c12580341d40c0c0d001c0c10074482c044414050020220000c0d2009001d20755008800481d000c081c06800c00514006854901c3c2143c956050000703044079015905001e40b14030310301c02c1705100843c9981d08007402c0009180004200104004c00181001d21788242c0d88462001103100e10003c0e801420100c072640c242c4c041c260403600c031090507114440c280d01000119441112825690202c3c1512260f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 240891088 1250 240889838 240889841
    0xe070e0105040f140a0e04051b06040b16020a05120309090a06170a020103061211060f070f0501020408011a090711010609060602060402030607080c03040b060d02091302090a020a0906050c01 83
    0x2039014140e4503e03501c10000394420011045903404d001128244a0982c503600071660010f800d440c081c0940e440301e83c0082c8507010500c40c24849030341c01001e203401c1c25565818211594491010162452140021101141080034162000c0e19045844400c610000f032810341d40d0f030150880940c400d4400780042019034029500600c0a0b011110752500192110044265250490041240000d01d44007001a1110307100a03500080e0303030710030f01c0c90349481e8000d400c000c2c8a8001ca10302c8140d1420800c044000103d00c10032580d1170354421400503860341c4c03404c408a821034042034245150b0120550508456540b40341d0444e5208540341400510b0300031141c0482d0052100750401c10b12145800360200340540c0008207103104620031000c803092551644403c072260207050718003078280d8005001050020340c054051a50001c8060216464440d2507000a100a481902d03c09031003400f1010210640c1011406241c1c4480000e10642c50300c0f02d10613005080000521442e070401c07001066605040200b03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 240892338 1250 240891088 240891097
    0x61d060a090603080304030906090602030d15051801140102070e040f0c03020303030903040e0a021608070f06020313201309020a050409030206070906091a090d0c09020d0e06010e070e0105 82
    0xd4501000003540f6442d0030301141d0b105a0b82500440c0c1c20080000d44c041c41401c0c12000d8420690103141801003515102016000d80c40926081c03110015004c92591031b103082140440b0110001c0b207811754548928501c0d001071404140d4115040780b6400c0c0001d0095003401904a64008200082a662400c041100c04800e4100070351600000082c0b004214001014200380c4510741001680c1c3c0d129100c07510100d10030440f00b00b042d44030b0348010a0101e00c14002505500e13019403100110102241d0752402280e00c12507000e8000e064126807402404103507208084a0040c03441d00c4d0307a503501140c0004050782d11204210301500d03143c021000843d228180440004e000250091203144d40900d4003a48459040301c2c03460001d500351000050036032059180b4000c450549103e0301c14120480038094070303075000b00303104ca4001e0f040c56041ea00142083c00d600004041c031b00001600c0d100410790b030409480080001c102180e00280050000000c4a410301d030b041581030800b03401d6a442800103881ca4044d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 240893588 1250 240892338 240892349
    0x4030806030c09010602011b030b0f15040e0109090b152407080f07030206090a0312020315060c01050a05010f031a06010e060301030c0f0609060215070219061e061d060a 74
    0x3c0301c00064060340542080500e06210781400850202c6c00c2c00440888014160340c0f540320342c80300d540c40c3d21820005a095244117010201529054550f50365202c03518081c1c1c0400012035031801c0341020301c00c0800f8a1134001511101d03000d019141c060000f00d40c040b4281c044036040d01e0652120340e03035060800484003019808508541c962144007400301940d00071000c00d80160080e2000505110404078103008641d9064452503040080f1605990094200924644812402800480043d9180c1000d4005410701c1000030582d032800014880640b10b040c0c1c8210041010070344d0030f200040c40d0316500fa845c0c07070034001403c049030707140c2004aa4203444842c03050b80203071000001100740803072105088140c0b4064400c1c0750345156620811241100e03107200319001600200402640058145061904100340d84115a2115410140200f091031882d5040300c800341e445100b24a60300c3c0780e003031221010000b00e5007048075500c2c00f40c0006402e007982040c514240402c00001d81c807543c40352007503130140c417 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 240894838 1250 240893588 240893599
    0x1140f030c0307180507050a050d02130b03010e1e09030405010305100e0f0a2901030902011808150907030b1308130b040815010312050f3a0207050604030806030c 71
    0x240d8070201801c4401080001c00e04c51420403001800040c040c80460340100500c0c0e070342601e8495041c200c1303002034205440010031161000d0000855801c244099800307132180640200150034180a00094503070103604c489158680c140400c800c8160100581d001c90f42c1c20308010405566100c2c840b40519151380003030f8641050314050101400e10140c16a1003582c80310002c2100450b243d00c3d111180a030b11710200f00807180c0d03603003043c11948250071403100103206050400c0c0040340304d84c94880200e50707900503d040341c1c00038284800950404505a80200c613410141103440d081d51940b00d10a4002003020f01801074100403901000010001c454450340344010b00c14030591903804160301a0301a220318046c0c5e00c503440d44485241c80142005040b41c1d4016281044d098014005907090f03080300c0030320800202c080c06003100745030680c05200f0603280d8058000744289000e010b1030308200720407945031803454410721201000a4001591030f4006400d0b042c031081076641c2a0000e03213002c00650541c0c0d00117 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 240896088 1250 240894838 240894853
    0x40905010b030f160513090204051816180203131a160509030a0b0612010204080c010f02030a020705010e060903101e020c03120601020f0604050c0102011401140f030c03 74
    0x1020640c0051107031101141036074105404164400d03a00c0c11000309000b440300d0340780c2003000a85440e014202400e606117402065641c040d40009088403012544034016030440b0312051a0a802801861202d20929025250450034800440f0340b09030807400e40c41680368004040b40202082d134850400c07903580050404840c4140c032050b081c40307981c29114032035000611900d1141890045041d038a009001034000c10701b07600705854242e031b50754005d05020f0700024410040c0c5d0b8801400e00040028206450003840031480705c0c1c0004022203102c070042402c41d0000d10030010040c0e80411600210b406c03d290400f00c0000c0d41001172402d2160f2a0455030610400c0c2140401d5903154018902a480000320701560258030b14040090f80328492010700c05410800c844801c8030740000381d454205406104594200c1e035000d94151401106980946243c0d02541428050750b9090280344109105100d10140700c0d49003e5088500007050f0a006100c4c091800201c0c0207501c00b0040714a40780710080c11229030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 240897338 1250 240896088 240896093
    0x3090206040f03030e060c03162301020405030f06040f0f0203100f0c03111914040f060c0b100f0509090a061d12040b0301061103120f09010c09060e01050703020c0409 73
    0x144400c0d44002c401042420881c1203081c94000247c0e6924501c44001c1c614099020407036201511102070700300d0f00240074540006243d4903000803280107034442400180e650703041c54109440c000441d00700f040140c6c005820040083c42d211284d101c150341c003030361001901c01c03d0304c0001c3c10010340b094103689040ca000b2801085a0040d00500d0218800d038030104403d40003006800304902c9425a0440c1e40c841040c6803140583c81000000107004501101a080585546003c0d0651115602c0a0002119604000305105090b05466000300c030a4400e601c07500d1400c1e41e0081d1181c018410144624412400901102d506201c0041c0039a8020310800c900d20708140d5009103280848006d160f85d110340301141030303000d26800444040d9104c00c2d002900b03580c030b00f0f0300446084003181013901c5503010030f020030000a0b1050041d2405102d03080e03888655854030840d041d003100c14201040e020050301c030748200040c2c1d03042580108004003e2801c26540d04140c102a441d1500c2c2c103d00c90707081031a1900f100306 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 240898588 1250 240897338 240897359
    0xb030d0503010e090604020a060e01030f09110102120909070305060d020a0305241005090606070c06230304030e060d150f09050c0a1e1704030801050f0d11100309020604 74
    0x50360602c3c4103000712511403070005030761801c0488000b500f1207540e40c1c01340302040c098021400403000506d400700304410a285140141c608409080700c0d486201d0981440541e01842940100c240990b0003d062100c2200000c02040b00500f6080034140d5450225a558503040500e52540340c028002d41007041e074902d802030b030f00e0401000001d852064003a103030402501d0300c00c1c094001c0d442101400321150401d020000341002c0a041c2540c40b1004105150010300b4030000c8034024046d03034881d41d845040f54031080001d54003140b090040035500b00104000a034004c1c40c03241303d141094130a10781724030885211708000c048000096040c0400d00742c0001e0501c28921886007900c3c1c500605101c2a01d461005001038040e6000c10f03008642a07005e80a0401c440d69900741d00c02102f40750185102c01c4030300d501d000c030805c2505d00380d0001c1d0350000103110a040c101c1c200c2003040004c1c2c80098002da415100e041e43d8007280c0d15060710071161180480f05071446900007980040d0000c01e42d50b43e40355180380d03c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240899838 1250 240898588 240898591
    0x209040b0901180f0b06120706020d090b040308160602221a042103090f0b0310050306130b060303070506090d0305100b0d0f1b0f021002030c04180b030d0503 69
    0x18010b609002c00700e040320840c541c40040c003941c01003035014a0003460b9200006800024000740d044001002e40c0d00004c00100214801001660007510a04501c0c0b0801005100c640e002071440702406c01c0704200080d055000c8072100d1005500d00011b8890f5450150301a22034103200712085004502c1c6d05018500e84444c0070112051b401c9152801a0010288080342c09248550818402071800c402c0070031000b81c061442803807091800c0d482c0d54ad214022604440707145e4002c196091008070410040a51003004034001c0c01d0201d009002e540b824209000300c1010600004005810720404160140c03070402c10742da0516841000e444507494544581c5585100d07960640000ac1c2c280f801040c11000d1058a01003a9140c1001080c601510032030200068012844543c1c5110358074442e80311a2201d0070261003c420b02c1c0c1d501c1700c410074403480c00245047ca64041c0c1d05c0d0303172900c104140201560b040b030480b402c441c501c040034000d00b40c0706182c0c01d00509604141e2901400f5901da0600c4055000d401035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240901088 1250 240899838 240899851
    0xc02060d0c03050109061a250f03270b090f040e0c1306050102030904050606070c03051f0e030d0e030c12030123030a0305090a0b1303050c010819180209040b 69
    0x2040a81c0e41c1d0801442540c00354801d080940c050901c0b603000032075252009003c6d0810b56810000e0b10030440d940034003501074020054409d459014401c0c001c041c2e00801004003500480e0100301c1c003124184051200e0045840790001092000414040d80d4444803c0d0741034413500140100600ea40032400d003510345040707801e0725104030090b0110f050304d54110f100303020640700180e0086040a2038501404014100540300d5136100106000e1040012260509000510301c2107003e4142c9204020403542c1c590307a4890721006140c10668490030101000064540865018401043c41e038403a1415a003544901034a851480c06403080e180070206501e002541211406048145000b1803107803101507034100081140e525801009420000ca881580640340203030004010300d0300340366641c50998260f03000d040c44220480e403081080083c05824408000000401c1c01d20020360303d44121440000b4034001d01c0c0400140d80d603402102c0d00358103441000042e6038041e10202c040e0400d8100072010460407100c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240902338 1250 240901088 240901091
    0x101101060b030f011e050d02041d0c120a111c080f04080705040c080a0504080405131406010206070507060e1002040303030b040f020901090302042a080405010507090f030803070c02060d0c03 83
    0x541445c100051080d84460002c4070744040c0c0c2004108009400b00038020f0740d01c07584440d1030340000d0b0b80509a81c2004210b02d401044114800300901c11210100c40340d021580c0c00250000000c90440d60107500b849104445c03888801c5540c60890a0f507030214000644400b4010a40303a14602114008006035945041196907196480c4104001d64009110f074000041c0e0340008605c445200d90040c42c0c01030301c15444581080d0300c500221300c00c107c44072040c6c10070359240c0303849140500480d244260000702c01c0c4003400306403134500305c05005031140d000001c1249076210642451121300380f0050b2295202000705640d0f40c1c0e92424010050120482800d100e50320f0034000c240207020510031965645411384490b80d0032491078003000001c040501090b00d445030103a1420803465406610300c0e04200c100d494800e001d08183c100f4030300b1030b00d00a05c0282842080402400440c12045020040341c0c1c3c0308840d04e5a9030384561084985440540c00250040004140c039907818406401081034130000d42d80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240903588 1250 240902338 240902341
    0x1b290414060604110d0209040f11040504060e09120a1206060f02100507090b16020910081005010303020303131a0709150206061026010f0905130b0105101101060b030f 73
    0xc10044880b01002131010440c00c0010003007002c0141c000d4061203a0003003000840c0c0100036403081c1a69505420010648000a024000380c03a081c86058050180e403600e54000f450404000e43d992151000e00342c00e615004952050041c2c858816040c034250564010b000050340e408000d4a41c003440c402140c09409405030391800241d01744074040c0300c2d284540c0c4400440785020300304541c40c2d100000752040041c0641341800583c841d030101500074010400d4106c0880d2a10f101c40f41020130001c202e4008a05100c01040842c2d030020603290806000300c0c1d01c090b120075510b410064020151864503076a2180f104104546e6005414036045400c00c031805e48656007550740c1242c4404013100d02a0340401c0614800c500703144200d00c4500380c0e02030072216004991801040110390842603000350a4980c401d03006020350152401000e400020740c003511401010aa81c4070100b203101401020300800410300140c0c6075a100d41c0c0c401107020400b600801c03400361903000d030101a50088071030202c12a460f40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240904838 1250 240903588 240903601
    0xc0318030c02062502042909060102030d020c03071a130602090d20010f141b192001140912070504020c0709060b04050a03030f02120a030c0e011b29041406 68
    0x3080c90300040340d041c407c031010500c0c0410440c01c02000f41100d81184018044450380d444248000d01c110320078000115110401890580b400c50300c191015103d0900c034100303020484403018500c1216680c00315015845408000210f07190480084016104900b02d0381c41c0b01d01c1011454406007a4039080e44c031030003848c4105034184c51039401030b442e684907103030100b0461880d03914040540800550003800d451805424000c40244904204401e550054000280040450319100381c903548400a00b04510003824504098041f8000d1401d041d0040888140d0550606000c2c0035200180c00010011900c0e03184549026540300014010426001d1526a0110b1051508026a4110348000f8a609203050030b59034100c2daa204180c154070254401d946880907001402d00203802145100e903000207090f418214001d1503004d4a0050302e044c4445101032091880355986944800b9801400426003507810344680c0c17036602c070b20f0300074503030107007800f01c00d101c01c01200000046000d12004101ca4242d211030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240906088 1250 240904838 240904871
    0x1a04050a0218011407020a08061911040303121b180e063a0305071209062307020603041208011a070b090307051f0c0318030c0206250204 60
    0x40040c030b00007a031404007001076611035101d982c20601d00c00c1034582804200e03804a989a40700381c000c040b05400c80401c002604c1c110214881158104540502100c600044169131a210300e000c06001c0044840e202c40c5113000c2030b000b00300c002d614400d00156070840c0000007000f010084c0f045071807007540d0301f80c0020340d1140404040c0c062140140690180300d1340d03480ca8600c9021070122011016a9100c40d0482c104091151100d07513070183d1141d036a615114608402007507100500342c000d1101509007406015440032001c070b0003902c1d5500b03042900700f614040c0030850042072002544007000108010070400840d0b00c01d078843c0c985455903401641c8401c03e07500c060041c81e06034400101d00740000070206090441040e00500c102d000c1da0301d40480354a506040820041c41e28405005a1390b01c00e402c40114415000045980e180401000e220031501103402c64501c0c101404005440c24000103554a200171169081d110044030f50410000080000804252580c240c0c408c40c070301001c1403504901c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240907338 1250 240906088 240906097
    0x82d060d0507081c0c1e020d051911040c0f031512060204050a0815041b0504050901051b0901020312070509190501030f1a01030c0e120a050c0d0308070e01030207061a04050a02 77
    0x40018000c06d405095108010a06e0321010380c3d01020700e0b400600413640a10550340e5081142c04c1d00c0c404482c082c00c0440d030015084070a180110310740503400007810350000c00e00290704100d2a0100708510420001c680ca02c05075000154100c068000000402100d0b42c010412200d0a44910302800c0c2e89800654558444240300c24008110707070b00003000280b52a03c803c1508252001c1164010788900208007220701c2191000d5090f9540c0090241d0404e41e000422003080d1003082c2c02d03142c00304910000703499002c0d005032000f03522042c1002c50b41d110302a0b02a650140d001514602050062910103003102300c09101d11804685844a01144a410341c000c4001c1000d00c0e072030b071714554203580004600404030000001c00700226a1100700c41952401d6070a4001002d51004141e44250750800605040414032080c0c4201038025418000035000501123034003655508004c0a04011200140c2c041d2041d5400101094a0140360303140070340c0040300040ca4084140c4080209980ba81e00413402c0b88036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240908588 1250 240907338 240907343
    0x40914090a080a030f1a18011203030f090503031303090f1d0901111b07080f1c1211042903010504020d110c060403082d060d0507081c0c 60
    0x10a2000001c145442e00500d004400c61400040c0ca003c144050012501d007801450f000d07410307807600c04815107811440d114500c4107100134100e19504d088000100943d05040040a06403200440b42c0300d00c00591080c1780f01d0303400c1030a80e42d0341e1401851200c441c0410410481c00f18002c5a80881d044040d0a0043c0c150348000ca48c20044220301d69840340c0a007001490b0200540d2a915941e14003942180a41031160300100070300c22030390000c28020700f003003640d03080b0b0651548002464420b020000684404100740c043c0c48150742164000105c0d0303850384203500000f08134201000d400c403888e400e00040040301d4100e24070004145005800c0c0924500f9101042e1191780144018440d502c0c0643c000c20100c1004c00c1c0008041303040c4683c81c1d082d90080190802c07150400b01c200f00905030446051130f44445c2d05100c1041d14882a8010300d291070b00401036413044c2c0d841500244243d00c030200c1691031150450212804203507101c03811a564000031528128403030b922007503800c1c09070044204440e0240d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240909838 1250 240908588 240908593
    0x306010e060303070b090309130606110105040f0620030c072109170708100509160308030403050a0324030203070503010c05031302040605060d0f05250e061e04091409 73
    0x40b0354a80b005c03407000c064075101d40c2c0d002c100b007030080540d42c904c510b001c05040d49001240e002d05d070280c05016004a0343d441242031b41040e0403c0300061a8804442c105648800000750101c2000e55030b0f01c0c2a1002e8114400c80c0c900002400f40709100075000d40340081c0b04856486512078406151040d10748400410408105500000c0c003003003021300c11101c40081d250007120710040d034422000703151213103001000b0051a610000e00041000a000512107110f00c0700c12101240e10f960307100f55071448010f201808000d4007041d21402c82d0f20030b42004811f0030f00720010300ba00301130302c060300c441440b5244001c80c80b81c4210071000549080601840c01030b00b0041e2992401d40da1003919100e481e01100c50100c0e4010f940c1c040208059654401402c01140c42c28000155100c0350700107a81203a81c054001c0b00c0c50565504095115441001c0e1071740342d0300c00c628002d400030f80608040384440c00358220040a00c101080080d02c20422003004e8411075814200622a1a00e503030079682d00440142d4864a0341e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240911088 1250 240909838 240909847
    0xc0702100c02010c26070c030c05030703030c060e0304180b0906040c050405040510030203060f0a060b0f03060d02010c0c080114061008131407090b100906091712070503090306010e060303 82
    0x2031011740e91801c0c061181007084490701c00ba84503010259002c40d000b00c070b080740084818800e0003d411600405031006800509130b850031600c0c05031003400c0c509030003880d00b910b4a40506d500309051064a008107849070f2961844070401d0300e820094500145240d020700c0c1074000103070a601d410700988196080c16202e403441d05d401c04043c80b01070b1000401038071036140d95410010040c0c0b4100400c070302c28684618124014201100d40b68180c0c0d14030341c803070307015040103210286200d034095048a4000c9400c8070b000382e801c011440140d444404244e40501410b26007000040c2605040d00310f0507040e0300c00c0d005e02c2943d595000800c290203005901600011340c04030001491aa50394040c120b0142c01080386d60324070180c0c6100c25150060903001050034540f00c43c584002c41c104812143c100c0755060038a003903301c0c20030b40000e000d182548101e00750340300c5003c45006d03070f14028004142c00c00d885081c115560022409c080303903240e103d605010b000c2d100d4000002800828941480c0c003c003001005075240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240912338 1250 240911088 240911093
    0xd03200a1115070512070506010e04080a030b030f010c031521080313050303070c0c0518070e120304140a050a0602060a0504080c0a030e0907020114010306020c0c090c0702100c02010c 80
    0x20388142e4078000d01006400c000c02c2c40400e00411a40391410400340f802c1c1e980d1a0107203002e034245201a8001340c2c0406001c3e0030300002609903416110002464030340003684c1258240064a0520300c3e94541e0340b5546015003032250385504d030700208110600111480b070034550b0303805848070560180d8038980818008170790240001e0056001183c10080c01c4290300c003203507132a0300d88909541c0151807090102d00000d03003c00400042205a0000784001c50300741060845a12705041e030918024103000403c170342d034880d80b2210703036840c08200524013001040326145d646500d0306039120001888003520403442568000f400386040488401074608550240103140c861840c840c1c060603001c0d0003200c808000784030400005204109610801d07000b0342c2c03034081040c0e03203005105a000c40548100110b90500052840389c00e64203011074116940164010380e1028a8101503081213880080719601c18860418040343c6030f944000307002154000c840e81d211000d141d01c000d4036044040748000f030125454118980c007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240913588 1250 240912338 240912349
    0x81605010c0e0a05090702120c030306010e04020712200a0c0512010603080403030e010509300601051c080708030c070507060203071e0f0c06050c0618120a030b0d03200a11 75
    0x800030b2450044991041d1388e281205900d400004014400340c2c408820052030350b07402034056582c003105079011842e007952502c40e84004184a003a81c001c0c0007020b05600c0038600d5881c0702660002440d002e84040c180300346000c030b05040c990b02c691b03446217030203507010790400e8010300c04c400131a039100c1d1041380b40a24558041c1d40d0030802d024401c0c10702c00207000400040e10383c0301240405030071045080301c0301840744042d8680094001d4868581d54030210060004e600e41ea800b0314050424410505039410462400b00150700c0b9040004201c41c07c0482032000100500e0081e01c1c109100340d0070f60f06002d840c1c840c100e076240190700010b051011103084c2050010380c02ca40c000c50b894060800c0c0c00c01040e003911074020780f080c1c9a024200244000501c1e111200003440100e4001d05600000c1e0034039003010071042e645507116500710340144400900585054020b5002505100700501254004445428040d203000004206014242c0e0048055001c01002203004a411036200300f6080000340c080c4240a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240914838 1250 240913588 240913591
    0x5060606044e02090a110406140d0204060903020307090c020c01030c0302130b1c0603080405040b0111010603080a0801060e0a060509150d05090f19060506040603081605010c0e0a0509 80
    0x4055014052403540c407014220442c0a001252104020840d00500c1401135000e40108050a03092070600c007141c0d50030300101181d003180d4051900380e034008001c5047c222a0720507040c009004500c0010005102a040040f40c01102d00840c00d40c0d801c90340e00c0018400783e8030b4003c54840140c01001440c1036a6003c0c0d880824601c901341740040c189081d80e025441540800e4020f10364001000c41c01001c014544295001c40b034650400c1403000601d076642d0089103015900500e84900d484071003591240e40f04c1d00011120310300301002408415036030b082503921a030050050800044404002241141c041e01820b01d0f40305000e010a04100e1810108039900c0e0003d040496000c4400490000c41800035006000765228206000070036050001c0d03c186000b90307162032043c894004c4241c004040802624140c0d005802c05000700d1503a0700d0788001002013555410041c5600000b040d03100c500000030002184880c070440c020003020031f10f004141c5001c00e4541849a116284003400e1241d410002c001d10b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240916088 1250 240914838 240914909
    0x50612071d1e0406060e01080103080d0b100507030f0e100c0804090213080c03160e06030a060c08060109080106151404081917041a1c05130506060604 66
    0x4540189002039010700b40407410352400e0044080c0d6418914141c82504000c002034203180c003540c240400068242c080502c009000700c078002c521100641c0d903507006104107200c010090300c40b50b05581405001c85c0c12006040c0d0016020344488111103025140b54101e0b170f240241b5510769400402e0049810340181001110605010b010010b4294494000b507c080e280c40801e42400b40d060100042ca40941030307038824807962102000c405224403281c01c400c20b480ac0c8140c0070b54141d0750203020a1070280f001c000280300c0c0b0f180c4000c0c1c1c048182d000804c1d500900d8243d988094650f0303100e00c0d05080e1003460007505111400c443d0500e420602a2820003120303026403148908041d9601c0300241041a00c3c84000c0030503102680302c8040101035202e0070a080441e01d8568109400d082002c48008001000c1120480c8001405090050450040107007200c0e829070502040c640092500c9640d000c8540c03c40b00ca01c5040c02040303480c42c148080e81c0565244500d510fa907030310401d807826103080208184 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240917338 1250 240916088 240916127
    0x50a03090506030130150903110105220813060503010311090906070f0c020a150f08160f030b030d030f0e0606060702100c050d081501021606050d020d0e0109060605061207 75
    0xc100c00240306c0c50705910140e00100d40003032070703440500b400340c442642c0004500b041d034589420070440850020580e140345619071102e61202c00d45141c10303801c03445034140d4003400480920000034403647c01802141030b20b05c9443c40e210500741c02e809200800e001600e402c580d5401036000200090f10541c80c90220940914002d5800310580d0003007900e5515982051800d841350041035103141d80c01a8076680e510860340742040c80740c9048603813800901c440408601c10002100440110740b40700e50445c40c1072900c000c065078010315481c80b0250041100002406450703051040030021540c0102e40c0c1c81c4501c00c007503e103d244c0344035642044480460302d5155814001400403110104904110503a945011a260820541446064486505e040703c14550455100404c403841901d060001507040707821604083c4d44070f0030850020700203801001c1048e88e0311440c0030411548000705401c030710241405480d0802a5688681c24849140305005940100303c403418082143c641c4910862151602c503500c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240918588 1250 240917338 240917429
    0x302070504180b15030d0f081515121506040305070b0d060e0c072006070b070e030f0703020f010306060804080310030602580e0307050a030905060301 66
    0xc0c0c07001d2a010030768512102913100d05410000d41400c00c45400c0079107950030312212403d00d104000384030f50b60080a0b8280050150b1013525241ca43d102d03403488071003d08030b0594032440d20750b142c03412040081710f840c0c081c1f203400c0001c1744c00307400c0c248101e070156500503010344241d0341072185545065222081c050400b60f5070740c2c0000717030315488040251300400e513103184c4030341d903d8850074092043c040c4400940d81c0d010035604d10b404660b5494046130850365001403100410f07903611000b950361914182031141c040c00341d04007241302d0036070104524065a20884a000c0d4400030319004400729100d90160364042000c0c80e01150104410a02859105900300d0503455007540765958001640c000d50300c4490b1030a9000da22410200f0441c1013410620b442c01c7d0144021125500c00d1000c0411284004100481000c50703100f49076090382100c403130003a000085a96440162410b46d0b47c2d440288815000a425040045087d1a12008990407141d2a0020701034508201e0024080002041044610703200100c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240919838 1250 240918588 240918593
    0x20c0c091308070804061205070504030f0311060117100507020c0d050f031b100905121b0604081b0f120f070204060b0309070806040c060f11010204150318030207050418 74
    0x40c01032030001e104122058179646048406003056040c44603d0314403904100070004c481d5840001d036070499811441410300c84000f0308040d1403244038800080307042d009200000c070f541501060786d5110030391040201c64181c1d86408071001112410b40d1180c00580046084194034a010f2070112515402881540c0c5030b030010038845840d55112010117003c48820060b04c088060b018004102200b00c2e0b20010300135a0705580c3d41c552036004103030030507990701000709540c2042e4a041580c039141d00301c12400c8840c107081a05041c410350f000703040b042d4440311020441088580010032200c0f0092800d03001083c280d80040303101c41558200a00002a15070140091005039030b5600480000744030401003181e50f424500940c500380411904010401c0c0d1040c02408000b034540c10000084039900d18108580c0b510b05007007103d82c40c0c584e282d11249036001140200f6808542004000300061a13202000200d8444000340c0010a41c45030140240c0c200190030003181c281608103a14800b0303c0041001c6418040e0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240921088 1250 240919838 240919853
    0x30f010501060305061804051203151503060a0f030506060d080d150f050607081903060e0a0c1d0303031605041a0403060507090509040f0201021507030b0112020c0c0913 74
    0x742d110800180d01ca03c18042541828001d143c2c010b402e80d8980d03900c510705a121150368503414107015404030400000079006200444074022045d90060841407810b440350944089501305071020b42c462148204006000024a240316044a91180185c030041c2d8801d001c0080901c40c5007016070b0000d100300512001d125140c81035807170482151041081c2c5c142071044889510034030360025801510b00308586000300350f003142542c86402040c00110001c5d841600d04502400403944060b10740d18403070342441007100c2c40750070665010b409030b600d0050f00d21142000707410007080d004005030550820008640c40781503200300900401e141c0c0c10414039050780ea000c2c070101c800840c040400d60000c046401d10420065006150f0008039904d0b244007800c2c00c050000318080b401030f00c01004c038981c8000c0d1408690003404240e14291111520b51510f00d400c1d03078003402901070740545c02d0010b2081a17507100250210300c00d03034401b401840003c00c03580b5080c0041c0200190003500304001d500c0d2626070f0710001030f6003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240922338 1250 240921088 240921091
    0xa020c040608030c01050115051e090a180506060a0e1314010609030b0108162106022a060928050a1a100503030702010c1e0308190501030c0311030f0105 67
    0xb0000155a5940c01c0840e50782190f00607041004248040840a042698014190f40900074800c0d2900c0c41c2e0040300b000010948900c1003030b0758100c502200001604284d031003040c4180403480c84240141e03950101000242c0c41060b841c0c0c4081640c1d00300301703801c9041c01c0b1001c210043c59001700141800324640c02e00b1141000b64421030000384020b0040c000c1001c00c0c02d8060041800360010400594401203401040c403040c0030301d038600c10f22407040b501c00b207940221a50b40f66400200841d900c40301c000f9504610b45246c101500b03002d01514006000c3d8000141c000c1c411002070003d05950666070b07007000342601103d401c8604c2e1140703217481c09020030320500c0103105462003940080141c82c0050000308186400516010007141070000030030041e100031048a041a40c24a04072650301c8a80c079000c086812004000ca12000320152940304042d0010186802000341c69581e0402403100d0800c1000e071072003400001d20031100040200f0004070f00e80d511130001c000050a43c0c902c01e0700003080c103084480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240923588 1250 240922338 240922349
    0x203031b0d0e060601020f060c09060f0d0f14070219120e03031201030309080613110a03050d0306030203010506060403021c030201110a030b0a061e0804020f0301020d02030a050a0606140a020c0406 86
    0x20f00140a001d44e010804c0780c46c40840703071000d00641d24014100940b1406160320035401810001070062200d2107038030451f80710400c0404108411043c0c1b59401004014508040780c00c0c00103000402c1d19540006424001c0311025869403040041d035507504d1120880404128040c4803645800e0011560280054180e104100c040d071400d640c503508005140c154140c0c459000fa410940c180716850f05a68241039141e42c01c41c4a09480c0c6d1101d1000c10007500d610f62020300341d40140071000c0100c5615410040c1100c1c000c46c008d024035180c69082100f02e20452000a511140c0024006940d08100c403039201000e009000016800400d0f42075030b8415400b0141075000660398940300042440c2c08071201c0c02614991800990483c21000000001a401c903903241c00d011000e00003c0856440700082c2040100240081d0744407892804280040c1d08195000701480e030030f100010741c0550092080108540722990341000c3c0044100315440a6485030200808500650314a400c0b540c80303502907a0010324 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240924838 1250 240923588 240923593
    0x50402070b19050702120a170702062e09150308030108060405010c080f010905090a08040b0d06050f01020c09150a0b04030201030b010e10052107080103050d0f0203031b0d0e 76
    0x140610301160000c0d450101609203d2500084c40305444d8001120300080303615122460360b550141c10180e81c0c0c022441c020a5110200c03804010b201c1b5030110729503008041c0c14a101000d0500360042000316002e020000f483c540c4002001c028003203041d00280d0f0078400007000d000300c0c0c60f22921802c0f03680c0c2c026040400c10307078424414041000b200744501da000c4461072038030007080e05240d0140c038560340061040c0f8010036140d40c0454031480d0144505d41c24154407074011944c2e2903890003500b4854002042030340e90b492a0000000e0389090030303d0101c484000c141d000d000004410b008110406030098040310072590682d51a09043d15501d4554001d00010381c0c103036841d240b40d0301c001030544603c110f03088c1c108070303d11045200c82e03210980500d0246183d4241503031a480c880042400360402c00c440094600c8441c801d02600e02d40010005041e280100c05540c0840d005401c10349200c1c108003c408010382c402c1000440b00502100790340b180700003001056107020206001e01c3c041d40c140c10074440154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240926088 1250 240924838 240924841
    0x30905060a05010e161b0b0105030706050c150907090c02010207020f0402091003180c091a010212030c0f07050a061a0a1a031f0602030705060f091b0406050402070b 72
    0x8010003245a00001003202071146604040e5029403030080076001010400d604814802c1c00c80c01403010124040c812a80c1c0030f901d407583d0030400102da03070a01c02c0c2c074064013803000046545445401200c10540c0e5600c0180000e4180403500c4041c402d0003014030446018a4601040c5e000c440d0190320304411082e40096203c103200d0041200940110207024402ea2040002c00081c0d2100c0d6161801032100e03080005210040603003280558840c920f00030401c00b19038802060000e619030200500322030301c1c40c2c0441030040c40e2005a9544003c1c1002c4084014240001144c440b06c2c00001d01c1d51100105a0609005069642c40e04e000201032003102c001e502e5003820991051001e03a17640a03014125040541203240120581e800000c0317503417007101300d41c0000020703101544206a00e500f01600e0340c640c484081d0764500080d22500302171070840c0e45001d000c2c0400c800c00c13001140d003400392074000b001d0002c84006d13101c9a45540c000400c413a40103034841e00001407903511440034005040c090840d09601d0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240927338 1250 240926088 240926093
    0x1915110c0f070b0306030a060903122c121b07090515090c0f0a140c0a050703030f020a021c02150d151212050d112701020706021c1b030309 61
    0x3001016008151400000e04c10000507960004032100d165802500000d42000107041c112001c18203043c8401c1c2e801d0500c000e404040750355071001d07a081d4038482011880e203403a100c007a0344c4406054001803040c1e00140a04102810b100142090211951080f5084a5503811120040d588201c441070501c5802010000c85400c02e0030409500c403050302c4002d807418060200c0021a8040c036220141000301c10007551110b00803e20883d0000c00107001141c40c010f01d24580580c3d212820300084001400344122040c200b4000204c440510350b00a240c95038949403500d80462000080d00c0503030340050f03038091116501d0992001400c600000b141d01003000041c44840001140807944080e510340d00d940d00000100306079800d551701071500c914240f951200000020405003c9001c01c0d41c60070b0400140781c0082c403070480c00c1c00380c88910041051035a079040e4001640c82e04094400e0601580010312b0985181001d1040b0f008042d10a00b080641c41000c1c01540300b183c42c00c0310f0700300d0100b0381c0d07950030105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240928588 1250 240927338 240927343
    0x421050d110c0d03050415020a051618020306060304081c05240603040c0515070501060b1e0a0806041e1a09010e010b0a0c060f15090507021915110c0f 66
    0x1100b400c0e94410380700c507501d64000b0083c1c0301e03504c5962007600c8680c840324041442803003452201c5405c0821211100300040008032000160301c030385540c0316031003c11044103456a00940e0303c1741800900944c115607036500d80781400d6000001c26050740f90080660407505285208085c024224101d0115181400c0b418004a04100c56180c6128131828000c01c000124107482d120140c80c42a00c07240f64400740000342c910709004030b001c000c0c565402d1040100d0000a0301010b00750340b03008013007202d240d11031210038042c0a00c240415a00019403240028907541426000303041030510390b00c00e851681010b10f0364a03044840700c0c4021001c8c14100c08692587d03191003005240075000d4011102e90b10b5241465408042c42030410010a00030314401c4841800800d90090519800d041c10500645e0038240018810b0150381c040c20251525160204004c10700c00102d01036400171410300b04d0b070401001e481d40c034441040d0049104915481d082ea013801d5102d01400f902d413030007a0100500380c3c0b00d000b091150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240929838 1250 240928588 240928603
    0x40b0c06011511060a09020f091509010b07080d11210a0c030608060103030f02072303010f020412030c050a140f010b0d030c29010605040303091a0421050d11 69
    0x41148540f00c44144403804910b043d009181d0a60004024a152011407140d150301010b0300d901140a10400a08105203039030000748000448400516a0322020404564080c0304000381400500707100040300080346901a002561004865030304001039031040c1400d02810030005c0c420302203440180010b034603860251250b040d4641c2800e000140c00e15020325a5510148405401c028035801000045030091041d080a00405d4119400d186880310860909114a8400b030b4001e41c6080f1040300000c001e4030030344054540d1000100401c48041d02c017150b01440380c0d40151480e004420283c000a1131044131a40c109818401801f03007014075010103030031514084d02d01ca0041e0b40b0b102c045000a0350040c6103030701c0d055000c408103480424400c0e08003250b40c0581030030806000600004100c00c0d8000d00904200c07442a9900b403616034541c1c50720459200b010b82e0241c1607503c11700041c401c130720441d180521014800c1c5c0120b0302c51511511680d1a00229000c514046501030b814289001410b12824 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240931088 1250 240929838 240929879
    0x3041203090e0115050a11030a08040317040b07030b0102070506030a090b0f060901090f0b030703050c150408030d0207030212071505061f050307020a0b0c0d0608240c040b0c0601 78
    0xb0525600d01000e4030b000111100044e01007181c0000d114059902610301d02c3c2c600f07100c8038102d07134441d582294041d141d4241950250041074030351350a0f901c0d0280c400b000600c500d074445d1540480d61a016802e0b0040e010599580341503009440001c156a211400958440e443c0403101050349a07450600b40b1180781d003d40540183e44072201049010b03110201040d045402902c0002014158840950000c144441045906005407540041401307400140200154821280a10506141c0c000c400c0280304074445c3c81c0040d0000c0c0401d40889072560302601c5814042c5c0196010800c1c4401da0400540c0004030403070314040ca501000701c00342d0302c074800d09038014800d443e800312001410503200c0d500c8000382c07081420030000000044040e44288030140103103a2058100c030403400c1c1000c100030b00b50030904071656600d03d054400544008006010a203011043c0c2e1080003001301110070900c3c0d44801010f88810072020000007076240040f10090040317000c0d00001d05550350406100075100c03d5440741c503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240932338 1250 240931088 240931109
    0x60c030304061d0d0905010804020d05150f060105090f060a180602010e0111040e0609040c08030a030b091501170a29010e040621050a14100c0206010e04061a030304120309 75
    0x40c2c2c1138039001500c0350291002404d20340341c0c0c2d0741c461000442c2c2216220004003903004000a80000c200b14401c064003c100c041d038805403d6664034011500c0d40202c540569001464541c00c44040c14008010540b5812a1070b0083c1111071003560903d03d45031940c00000140c2d51107084151205003032040001581354a054549410700d00440e42c07000071405020b03284100c40d180c01050420400215150090981c041580c0e200d1800d294090003d00318142c101d8050702c17030000010010801c0010882c02c05030140c4541d10780000301d206100080d07800501c440b0f0000e50361800160262451a04200341d150340f2901014000030132000101040361405a0174052800c002050141b0422560715000c00501d4a5800d180c54640707092441c5041d04031038014000d0000c03d010080d0340140030400348029004291700380150645c24030f040341d5a000920810301115101c1012400044050f00b200615016402c400c001315110b03400002c3c103641c0540d11240007249141e10b90410980c000d00e0358001041d003080c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240933588 1250 240932338 240932353
    0x30c1809030905100e03060a06050f0d4706040e010b091603110a030605090708150105070f02120d0e06130302011b0c090b040509010e070302040b060c030304061d 71
    0x10080c0601d60381d0f0085030b00c03800c000c4030030f061030342d00c40d81c0b1280b00c4e80340003400c40d0ba090030240390150080c000d5002e11409401c1c0001d802103d400d20600340040940c2c800d4024181c4105400c41e002c84014040c052010604070048501440700350754905d4498000940010095080203020803003116804240d46800d42d04180074030981c1e0340d41054455001c42034088010a4210801c0110300600342804414110038011402e660801c0c2c0c940c0c80142543c0054039440036039107582805503041078089500700d010f032403003c001c01801c1d48180c000e002c145201c0d8409014038540ba50001e1103511034900388498651010b003800c0c4281e540110303000c101c104250303002440e1107c105448a40c404590001a06100510b070000e08000d8442c0a480d0026800111f20064540c43c0c81c101130243c801100300c28400c1d4200008260402010300c142204074842000811210f440c55092101505001c44150380c841400e02c4054034884051005511561003904006040d80c40307540310682c202200c80c41440d50380d00000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240934838 1250 240933588 240933593
    0x40809011e0c031103041a040504060816050112090b1608070905090a09141c0305150f0907020f0d0509030115050108040605101508040308180304090e030d020301030c1809 75
    0x4100b03001550b05403400040d0070808801c514a54803aa40c440d13860880c04000401529006001078000c0c0c2e001120103109a0f6980d14070990f4070400500501d4080d08010300400c840d60256020030b0f03a00c00c00210205a216071a00c0300ca11a000448903040031402c01c1540c40f02c82603015451740d602110a08000405600f0580890280000140021b180e16a04c0d0114418459915140340400039aa400c8400c19040e00b01d80011800783d0a1032507004c00d0a2101081c60162000d034044030b00705000c0c00e40040359a03220100139001074041c110001358050312001c091048810f002c240c402e10f103d80c581c0e41d80e03401120285421503a00ca104101021550101842242c2e4800541a0010b4200101069684039030400e905c0c0c0e5511680310240c0010f082003000403060300261480d108034080d8943c01110707611740056500307032070342541240c606800030441840440300c03950040900b8001e05c400c4a090001c00c15408081741d0080e042580d0418030580c04009035a00355444009480c903da03c02e00c900807056 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240936088 1250 240934838 240934847
    0xa0603020d0608030c100e0a12050712033810050421230118120815030304181e15120201020c0f0f1e040f0209090f07110303040809011e 60
    0xa28401c0900d9101d10200240f0b40c2c0c10805206065007001000c00444c000142c058102d50210314100c1d0034841e2a05843e80c62400703482900302d033b4480303c80e1007024501c1e08502c6100d0004280303045000035000e480b60071025210400b00229000294071842d030b60b0303414000055010783c0c0c80500c11020b0388100018800103240e0301c205940070640c0140500b415040c280949014042d1002d41251034003000302d14105001030381940114030b03840e03501c03850550340341c0c400030030420400c004031160580d104200820407800c803480d280e0072102a40100043c1c40c10503071b6804805880072040f600009072620310301c0c503840615403c403500600550482d04104070b165070020f502e50005018561007125145640b2001d80c48000b46020b540c00000e094612403c5810744440804c2000366050340900c4c03501800d00400f0025208454107100c0060021103203a43c1d0060700080d07020010b00715010480302000501c0d01c02c0d42000610700661140103915100c141d15400100088001081b41c049408503101d090104c0c0d410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240937338 1250 240936088 240936103
    0x31801031503080a05030a050108060421110303010b0409060e04030c0f0f0609051b0a061710080708030403170f121f090603110102030403030518030703020a0603020d0608030c 77
    0x2800c011442608240c0340c425031142561028240d141e0001d00c07200500e034004000c1d84103d04c5d24104000036602c1d80310030390340c0d140c085a00600200500c0300e01c20421a000c3c0f240f0091a800e86814280321501c070307040c00d080d0b030400e0744080d1602002050074425000d40e4020301014104005220000e440c0c1900e0040020b02042c0010b0104001a0313102014402d14003c032003465600681e0920410946141881c0c0e83e01950644465547d25602e1900d4640b52140c0d400b01110515075a008510395407004044032401c002e801403140d0010302500180300300c8180240401030001c50080c507119403460804481c01a1021052801018104500b000348184441903c001c4000003280351025a0380d0900010006040d90113018190345842001601219a802000aa9109844018010b1401070040e0703564019804000c0102c1c40c28880d5010040c2e5604a0f14040403004084541c2641d481e00440e00c1410607421040000741c0021b9072602e044414000c1c10000c0020720020b51401c0c03121401d06845651 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240938588 1250 240937338 240937387
    0xf180f020a08011a04090501060809060a1802060c2404030801080c060d0902030106241215060c031e03020a0206060a0503031c020c0105072115140d140c0a050303 71
    0x111341c0281c150300c070001c02e0b50081c1c0311220302003006584a1501600002c4102d50480701441998001000d0f880c1c01d01911104035000d8082481d405025400c00941d500002d00c0100c1034411100405040e001c07601d416591400318207516a520705041c18014195903050f00701030800e40c80180c55071000c0e243c0703a003111201210b8140c0046c2c404e407a8800203015000503400b03002d50001c424540e072000b0a40220344000b14441e1f49034030310707010520500002500d074401100500881ea43d4070030054907020782c50408205210380b9103004031542c3e010aa030700380a60041d40c640040c0d408501018450b80410065402c6001100c0340300311140742600090792403190900c40008400389106000211f8041d4050f2188408148004d000d07602d0f0a03103000b8038000c4588444440e6510490300b9011405d85842043c1c1c11205461844104d10706008180000d05884410b007504071000c11a0040844c4ca48040e50312208071405c00341c4051255002084075260064015510070f400c00c0040c240001c400e004101c00441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240939838 1250 240938588 240938609
    0x105060102030301062a0305180f06030103080c0703080c0303060f091b0d020706060e060301140906010b030714070321060806180703170a1814190f180f020a0801 71
    0x109403c1b03118040100852001c04201504041c180030540c000000d0000d0f001148185980b21009a0400c00103940c026075017034001c2810401071010440d0780e4020000b0041e504202e610300c650766552481e26501203e074811841e00040b0501c1080d107852014401c0c05401140c840903d410848542c221078551101c822038130f140009100704003507036950180d82e0550b8110a041065680e10b40903009a501c08841c0d16201c0e51902d914003a00f4800945e12600030b100a10080003168201104a041540003502c48020b0000c852000e02e07102403000d00400095209036201c0e45182096549a000c1c40e00400800211508102050024440009603a43d101d441031800d032045d81c4a0208440c03c2410036040940000707150303100062945020001400e907510141d41d450303408907104030010509412401035950702c5044031600300d803a2400c08a8040d00488041000390f00ca9a51f904601c25044594400178400d42d185900c43c0350300040784500d1520164100c3e00f98a401c0c40b52400034002c00d414000c094105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240941088 1250 240939838 240939857
    0x14010c031103190608150a06061407030804030e0901091401151d15040e0f0705070201091521060303110d1b0c080106060c0615030503031308070c03140f010506010203030106 76
    0x900035081034004008101c240c81c041106c0c1c0f82800328685085401c0241c1d241081000104181314240c05095901031007409405d1a40c590b40880d601d8070050b001783c0030081000d50300307102640e031030400354001d00514400103080c15188040c3c00c1c4100c4140c2c070581c60415090420030703030150860078441c2c03038803503148201d02202d033b1080c00680001c0f081140d0151402c1c001c00e0101f00301044265080c01101134101507000780d07031005402c039514810b03064020f0002c2d042c030300200251481208107041750b105504103c6001ca9620780040c000004680b55080041d880e800c1c2003042c550007400b55015903000c10003504000d0320000010344402c0d100c000f0040322808500d08a0184107460040d1005851000b00034040660395401c002d040e002168002d440e030034600080c0b81c1d12804191010b40c1141e80c000080c60550f1384d100c400301c840c840d240c101620456010010704001424400c11900510301c05c0d0f0221410024012205260448070f0a0841440e0b1400b014032250742e80010941e4110b41e141d18081048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240942338 1250 240941088 240941131
    0x1060801050609011418150403030f03020f0d0e03030a1a061b0a05100b0901060302070b01050103020903010f1112010b0a0207050f01050c0f0c1003020414040905070305070314010c031103 82
    0x200080ba207115045c2c140301103403901c04915004440c0d0f81218084588010b18100c820f060207840c40785100040c00320354200c0011120300d010f6000b03040340251000121f8204404400c5100a07640803900c21080c5400000821240040b50701c40c805007038042d5446940d00c02a2000481c14611030140c0e50350720302c2c418001d081b20b925410080b07204129404010303540c681c182e902c0544090010407140c5407040d0b0341c3c140041142442803090710641d0381c0040020009900e40320040d002540300d6214103403d5521303411a518685083c0c01800b00b02c00080f14800d56545020840b210310482c10780220041c194100b14280ca030750b44c00180c103800e4841c11109032100410140040c0d520740f0070301d078941005d8002c0d0501c034405190b002c1204c072003200040d07540000d071050143c001c40482c41607025405030303002122403540c283e0410707070300c00000d0501c290100c1e1f003046c0c1c8a44074149400b031540d01c12030f5185480c600184a0781c00038019040440003900742070112002e1581e0309113642c00000c0c40d121046802d800410b00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240943588 1250 240942338 240942347
    0xb24040203040f14030301030312021c11040b070311101e051306060e07080f060d170403140601030c0f0312030f0f05150306180601060c1403030c1903050106080105060901 75
    0x503920782c06440d540380b8903500304c0e915440742c000744000d8021400841c40c02c020030900e4000c903000c080c0722248644415083d42c9200c3c0040c106904600c0328180140f00c00b046e8401c3c140020314640c0e000b80c45541d40862041a564640b203d400f0074400700c14207017144c1101100c05e003a040b11030440807400121b5107075035004903030201d021a0030000d00307002e08001001407908078402e0050701500042d55105c0b500e5450b8580c10b010450142d0304c564200c42d462580714007003621441c81102800746418414941a680c0d242c0c0150f00c1403009005600c0e80104004208010142d801c0d50000e2543c264503a0505107141c444640c00710520744682d05040d1038140d05986005107074000c044848094108110364200070105038121010580038600030310030440482c0101d52601010060603112200610361a82092001c850882c01c0ca6422902c060050f80c5000c5401414800340d40300700428007805031520708200c00030f88082025000d14080c10b14103070041c0801c9038000c980c103040d203000382c0d00c195130340c510350340100c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240944838 1250 240943588 240943613
    0x5030d080c0d090f0210090f060f0203120709080d0f050a03020c1f0506011b0c0b0f120708070f180306020a0e0a03150b03060c0d090c120606030b2404020304 69
    0x10b0078540b41c0760b041001c01203030003500c03600a4000d5841c0d04542c100b0f050b054170041054012400b00241495040240620a004669090341d0354411399003080b41505002c00b0400f01178034110007080040100b40101d50041100f102507103a20302e00310714040141c2502420328441e108000042580000e00005089020058821114211400c05100050506e400c500800040e140d182c00500e040a805004044184001007074640100c1400110f1b0f281415040d0154040c070581089080c0511400e44c0c4150b181d10018450525612080043d240108004010400300a020310030b00214400110300580ca289420f02925800030006a944000550a4900c0e24801004507480500d042002c403c00c201140340480c0c2c4050020117000c0d81111008050721002c044070041e0301c02400748007855208800350003100e5810b010302e0003011540c0c3c4424a08243c2741207a02c0540d0404d40b9001c0070400c0104008940e984000114401445070441113044261040c084810398895500840458140041e00c120354 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240946088 1250 240944838 240944857
    0x4050c071110111f0506150409021b03030405030a17040308130c1e0503010c0c0b0703050406020d0513030e01020d020a021207050604080d020c06040e0613140901020d051005030d080c 80
    0x7107400d8810000d1001310165008051380109050102040d03160510304c0506d200140701c3d48800d0b00f081c0c1440e1000c0000e41000b040078aa0758200202041080300c00d000540c0114002c4010316a1410a00000340408014900300e88400b1014010440401c0c0d0000f41c0307a407c0321282001c84102d4001b0300300201c0102040c0c004280c444000400d10304066200072056044620540003030104001d88141981d2040c066000580065000d8002400d0f01c1d2096001c183d000e4070541f401824400520141e40841e00101c56404603501e60b020003100341900465a4060840d0920080c00414106113000f5114003020800070301584440c194800c89800502004028080c060011a229940d900020b6030b155030041c400790140c0200c074000d9466051006c2124140c904027141c03400c0c40e0300d500b018030030780d61000300c0c21083c50765580801c00e5000d40d140c1049402124814000340e1122010704194044030750103020b00d034002c03454071020003460300d000c100071004840506012802d0307035410602c180075208402e0f51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240947338 1250 240946088 240946093
    0xc12070e0303041d0a0507140a020a05060103061d07050102100e0a0b07020619022a010e1b10020c0f01051e07060f050c130306020a050403060905030904050c07111011 73
    0x2c11100b1071210000705811490326861303d6500e44100340c0d800c40c2c0d81680c01c07000240c6691842161a10248000e2420003003e104a990010258840300e0900800783c10848400f40c0b103d54180200c2d0b450107507501d00b00940d002800440d840d010000c0c0d1380311800310f07010281c0c94445546145102c0240160312520f50844a4425a45003c0030001d40300c2d0307400c54000074040c2c3c2c402c4466020242520a0302c1c1e05421885601c07501c4100955820345600303068446580c0343d03403150705d10b200003881400424400f4820215204c42c0c030380c0880410840a00c207040f142c1c02c56100005040e4a50fa490341d440181a200703080c500c0c0e80d502e0030030240158010202042c49a41c20014001e020400c541d0b21843d6680d00c43c00e010032043d114124803411340d110b40a40490096800d58092010419540c024240c00380307241051458030342e4031740d950002c3d5803240c641980d868001103401079003814180240c2d54400300c201d81c264900341250b69941d2080c040c0e551114004c0e008048005005070041f01018094a0007408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240948588 1250 240947338 240947347
    0x2060126151005040e150c04030512030c07080a0207081b060d02031510020d03140609040303050a02090a0909110306060a0e042906040c320f04060f03060506030c12070e0303 76
    0x102d155440750151041b03002c03803c0c41800640700c10034032010b442c141e95000c40a40031149103040c103c0c0e11a04054020444403108010190001700c40f00004e201031222078001d80340ca41e1901e8070b6a0300b00001c425210342d5172415041d141d0b010380e9a8804440d40b4040f50b140050302e0f034803060b18a07400117040d1070543e134004041034008008241c0009801007940203d0f03406100019040d1402d207a40300003900c006420212000c0030500180c080d40249078031000c110401400c01c1c0500c0001100e00b1840e03130284c0c8070720781d60f400601c00380030003418801612601074008107e541407110105244c22075030320500742240c500d40082010000081d100e041d20303000c00e9030f000c89038041c800303113800705003c0554031a8071076850000e125030760390b01903884540901c20b0001d68104c42030200c2c0141e400782803a91511144100200408918290072601504c054890340c3c0c1d0700c0701064142c103005402c41c0c0c21034005500c40c02041c410066440a400d0840e408090300b820300300a40d031900c000988031090305400d413551601001c103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240949838 1250 240948588 240948611
    0x316050d020c03130e09010b0a030803090a051902130614150702090c1804110f0703090b04030b010e07021f090602070605090313060314060f0a090c0206012615100504 73
    0x60b140c070a49034217450003665030b240c40036010f080310851801617420050384003042002c144014040e40e4000c010a040c1d89110803160b41e4103041c01811281c1031000e5540e8404e88042d428000310f00c01c50b0a08080b41000040d0600100241607481201c00d02c2c440d2584a02a45003d5807620a481c101640038000039440e04048030441b40340c3d000040700c3c6020310300340c103081d00c0145002e004203c502c03d00b000740340d46021b410b540509480c3d4011a4258240b02d078401c000551281241c0090000318040c0b001c0c6140b55051141c6444c115002806c41c10440d0700003078007036036090f01c1240c401c0350580d99800c001540304007601c1d291010b401800d0024240c54a02010800150f402000610b01400031081d85804261208010303411203030094010f00056031448001660380c20401101c0d0140742c2d004108444a40d51180300c2c0741502d0031a040703100180c010f20010020501c4c0d400c215262003e41e11131611202d4200140203a0706c00b4510625181541007201140c1c81c210000c15180143c1805403051004100c041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240951088 1250 240949838 240949867
    0xc152a0403110904030f080c04030519050106080f0309010c0c050918010c03020a09030b060a0b0304080405040501061b110a0b0c01060e1e07080703020d06080c1003020316050d020c03 80
    0xe100980e4011085030100c2c89500e40404020f12950741a00d40120504d105141114003160081ca8040000700c100000700104504201c40c00c0c029002c16480b4642c000703146001401c4d640594824a1543d10810030148550004401c8c0c600e03440080c81c1640d030310280ca04040007d00340582c41130303401c5111b4400744102021142c524240b189a4000280844020342c1011000ca205072001500028441e04042c0001050100d280340c110300700410355550b442d2503400f103100642c81a80e084460b080005420005410580205401406d44d03083c5a85440c02242210300074200c2d4210017841088400403250007640c8140b41c16002d082c151042170748400c04030800314000c00441c010061140c8101c8000b5100380c2040003107081e0105928040302d81500c0b2740074241c0d440c0d003000d000503080c03503001d0203800c501e0301c0148158002805900c0040000086810501c190b07440d5025200040500405c1000103010845014000c20805c070310340305607140014001000280510348100381e49000000c0e458000a201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240952338 1250 240951088 240951097
    0x30714150f18120405041104082d0c1003020a0306030b0c1b070605191b0c050f040b03190510150f060201060302030715030b040603060c020f030c152a 66
    0x61040c40e0b50056154070680d036841c180e10201c24071181d01000140242e040c5900b010300f410445001590510351102a1141080e03400740380d10044128108c11440036030403d05117000d120003070b1005441000e10380808504c8032681c02d01c00c0403c0c59000542c0d040703041d01c48c2d0312410045800178004042c3e03003480260b640480d40303d880585000030034200c052484510104405044405503210a40380c0f014401c031011013081090101801d00880840704056120050b84840381c1d030f031041c3e130041d85150511040142440600c01014040d80c5002c10340381c010f44001440c103404034004e5280302802841454054074025110603100105802e00b40f000070704185414405090b114041c00c500a8161952800c07800c903801448042c0d0b140c3d1200400b08100c483e900f042280c84065440d001c141c0b014100d0100701a82d805d075104441055842c540c100c81554107208064000c207060300550300d03040310402c50950b5544240c0b6486030144406021039070914001d8400b050107034510000b90707190801c2ca070000f07000750030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240953588 1250 240952338 240952351
    0x919080c010f0e070314101a010f0f0921140109110303030c04140103060b180406050a0803030a05070309140a1101050a050a0c02190902130801020c030714150f 70
    0x24100100c03140c11481c0908038031190303c08000c000451540d01c2e11110501c0c04030018a06000769200c1c002841c1c440e01410031a06018409504822000700c0010040110900d440042040b1340011004080e840a107003002c03140305d600d8240c06050a2640586009003400009010701d01c14280240212010340080003158003403405500c00034800d409047d04c070b11080714000c031011001c01c01480030201c0b80f0b200c07041d00356040c900020b2031900c82003124610380c45007590200042040007441c0441c9050701600014003130079030741114200d15206400790390380400340c48040c0f460789400005210300d10980c001d01102e608101000101a006440e09071950700865050750810001e040c29640b0b940036100301e0b02d000a4170390f42c0e80c0c0b406240e404102d80c0e0b510803c0080340d001d11a800c2e0710904c0c002522541c0003612501e03c0041c1d807540001e0003000044000d0f40400280d90050081904203000841a50540c1e82c00c450546010214a0701c50380c10030301c620308903030801e141034003e1250f607900303042c0514807454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240954838 1250 240953588 240953591
    0xe060411070203190501150305031201080115050f040f060324050f0601030b010c06060b0c010506120c221103060102061e0105011202070506010b0901021c02030a080919080c01 77
    0x89001108005512a201d406501580400103407540344000502000d4454092400080e034a141e440c0ba5154002107903005440d1603002080c0c004480d00300d52001801480058000c0144032900b1009080b82c102038450310340304902d01403810302d56890f90f0300003c07000c0c0e40c280750811049480740f81131080b00a9009005d020304208180005246500303200e0303030740070b030300030864451140c0e441e8001140540f50000704c030b13410404035080180c001542c5014007006480010529519611101c0060f401c42e0802032455100d80c01003040300681040219280078401015118072403551610a8012401c451142921490700e1805407055948a0404003840c0980000da00351886e503110024440c01c1a543c81d5100d0a045050000421071b079030140c82d1004011391035545c054184049030b03d585040840981c484040a0710010b2a40c00315030f0705100d8030b951500c06840c0d42d845d110441300c0080d40c82c000d10813100c0a005c1d1070f401042d03955000700211120318402050700b07500c88641c6e1400c0320381c507000b0882503541517 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240956088 1250 240954838 240954851
    0xf050a02100630150c20010218150a180317030709050105090306010605090310181406010602060112110d120318030c06020d020412080a0801090203061e13060e0604 72
    0x304143c09100e0040da40140c107a40c044841240e400000303000e01c5803100c041c00056116040c201c280445040c003000e0f2894001a16114401964204568030300a4a8882c0940380030108880c8034040a8035030880b074600d81849022100c0c0c0039041a0001c3e60400348c10401e0f0300620404000a1000540c4200350365030310004a5940d410040d2080c0c000c01480d42c0d4140c00260041c085207120744040c0a07004802800c6030002030340522540120792000c0002c00000c500070400a0602001c004000e4120b01d980f0003c004c1e40d894504000d46400c41030094a20305c0b16203414180c01d01081e100c0c91f40c04424010085001c0c8800f80c13030700c0312004059a8250001ca070500e00c1c900f1911b4140c80b0071086454240d180e061a5079220f0f07650703200950003c03214200084c0e0902000c0b801c4441b1460010010344144c034002d40c4c880320f01c0b2000d49942c2d416842845280e004004001e542e803111000302031001e04215040400c50308a0b000036061035005015260488c1ca000d80004a941d0f0401c031950103042c0030303a4204041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240957338 1250 240956088 240956159
    0x9030a0e090603030d0515130609050112080d09020a030c080609010501060f1b1509050a150501060c02061b03030a0b0a05030606151b0a0f02010216060f050a021006 72
    0x801d101141d9265143d0000c1c0400030100100c1d400c03040d840806940c5144969010000040d000036104025a14050b0364000c00d0040b196940300f002d0250655211103007140e602c80d91680e80170b20070130039182c03011600c4060010131500c0300a2103101450340226001c0a403611001d240e6038410007203521a4071366081c1000069903600070082c42d018071150b6a501d01c04280030340303040319894400580403101c03115000600308040005100c0c45586910440c01307490801203038281210304c40c08900e01010740501d4540104280380c0c2020040c03040f03681c142d51690315508101d145030b4982d000503070703007040d40e00002003000030100e065848141128011182e495020351180145036403045c04a4281e07030003140509840c4071901940014001c400c00d41d818501c08048100140d605100d0340140440d01e9441c0b26213100c08560701446003806c10004410000c0340b55180420082c9904003110360340040c082d00251503901540300388002d00342ca4101c0a41805030950303c4641e2103808171420054152410103e90407200d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240958588 1250 240957338 240957349
    0x30c0804020109062015010e180d08040809030a0b010f0b04030803010b16061407030e01050f071d0d0822060206190f0f0b030105060301062301021509030a0e 69
    0xd58041c0e481400403400e000f410b8600481294240041020310307520640e031042c00304001c251010014003000340a5140c12454138041c00040d282011036100060410500040000c0b280380641e900e1404815603101c80c20031802620640000a8140c0100c6150000384003d45103c50b04860000c1e00b80c050095072040ba00840d4091408014110384c0c080004106004c0220003800031a54000c07621034507035400365503001c11940185e034400031001c41e0f00200310115801d0300c6030300c5501d61103100910a500c0d040c00391036062032008007038405001142034000210702e60740001001d201000f800380c086804081c00e00c10460b0304000c0f80050100c0c1304810800c01e8030a8400341c002101c0507a00245029210001c00458840c80345c1c0740045100c0d55202a1841c1b4100340c082c2c0d001c0144070600c00582c0c010202e0505096400041c001d601a80c1070030300400100403010300c417110038150b0346603404040c0440e000403810000f0007103465610b404080d0a2040816010005003918000c0351a0142c0d038a030280c00340308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240959838 1250 240958588 240958591
    0x91b0303110c01020c0f030f0f0d09061b06110408030a2001180b09120f0a02010c020316020d080c030a05130504050c04030f0309050a080c0102010b0303120c0d110703050901030c08 79
    0x500507080000481480e0038444600e000e1960007c060b9600b8400c804210380c944500c80400050325407024001711886608090190090b08952170285218225080070f0380c040301c0c00700d0004000d166540841c030383e0800340f10150303005484408182d80d43d0f0144c81c02d00402862940f10585406203030071120014000b014441c0003040306031400341100c0c64219894802034140010403040180c040c0b82e040110300080c00e001001e100c0c3c81c0118881c0c0703070695180020b003180d480200740c000355481000060140b200c209020203140c0e60440e0703010f40408070784c9814003880c05002e001180038030021850b203030f400760801e016141040c6000c2a079071881e07950742c040000b61603054401c0340308080108414030103e01c0d0414000e69003806402c2c1108000e5554010641404090307028a5050300101a05103d0390707030a00400003032120440c01182000c4044005176403814010b401c8c9002e940300090384001e20002c0d074001880f10490042050b842e034150342005007080d4007140405000070b00e4201c0290001d4050444c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240961088 1250 240959838 240959863
    0x6051207060e0d050a03080901020706020301122312070609080705060f0a020a2a020315160302030c0a0f090f0e04060b030a0336090c020d0c03050904020d091b030311 73
    0x85c5802c48064506844801d805828580595002c1111101180050000714020b12403230200e03000c031280608080c0390048452070000c403203002554010008103000500f0031010242030f0320301c40d503d150740d1810300000c01d85404010146040890f0200501c240404c181d44251034040c0b01c5911592044124400c0784100c060a1b4082103807402c409041e80300242d10080201400244840b801a0680001e80b61900841150400d0f079001c0c0100b10b003800d4500300025660314141410f5003181405020340399140184103002d420084002010000180b140804d4001498008200030006031104294450007400b10780030343c3c01d80c0c1040012180d5040024503003910381d8060760f62503002c1e000d82c440c568034062003103001140d2090b45035010701c8281044c0e451000a010908002a410304035031070103401e10702990902c43c00d00170304016500200341c0207011941d01078000c88005039100401030070600100303659240500340a140c3d001700900e1120480d4038400f03903402621001d52507140e60300d202c4d0307440c4a0103001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240962338 1250 240961088 240961093
    0xc0a050301030f0212031308010c02010c0e19150e03190f03032406081905070c0f05010f06080307020102100c0516080c150a050c16140106051207060e0d05 68
    0x100040742000700b0001490380f000b08501c5c140301041e007141c0d1031900885030781440201300440c02c1242210074400e462090780180000d2048a451100c050841210040858010354141031250300861003801c0c3e907006030901018144030f0410303002d8000d00e55148520340364000c4c407504001e000c581005d44421300c1e03490340c050b44c55152001290340450180c180d00c100584009040110b4250440cbc6034019880030b040956510307600b520b84145500035000c0c4840300408440c2c0740600307000d041980490800811a0050381a00a10f401e6103801401420701041000080345803400100300824044028002076000741c2c2110402040e030510101140c0407500c0c000049130381000701542800810403082c0d141c50191000508152a66020904100103503040042c030107000300811003c0344451241c40e4000b1041e0085c03c1c10702c0d8401184549004040c0005007060581e5141d112510001b50045405001d01030805e03002c01d0302980c412551003c0a0040101190312405250900e013001c0c0780001166400000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240963588 1250 240962338 240962341
    0x61802041b12020316110709051302010905060708030408030405160f05100e010e04180c120507090c0827150a0b03010506030d0323190b030607080f06011815080c0a0503 74
    0x415902c1401b0070f1140f42c0d2500415800040041c414840d0a100310308008100c541c00302c01744001000412a900102d101d94014850140072803404025207038450b50040c5c40c5070b580d868609102c0c0c0f070220000c1c4203000c1900d00030000b00301003100700c05050848209651480e03074a624a002a030780c4407071280072180000c0301104894600d10b00354100b5075140c0c0c9643c62910018040b5140c642d10b4000b5500f0076800c6031400c10361141003203402c00c1080010b15480c21f040103240d01c0a14018100c0e04050030345900c00030192810304000c1e40401e0000704211211045071460081c5007030181c00e2035001c81d00707482c01c10f1520300551070906060080070700c12900107014120070400c507070054005000e0b01408462044004400030000319038022030601941c115081040655a124a04020b459203544841e000c2c0d0400300c1400010340e000100190006034454111860365103000048484244612549110450a10340060041707030440d010100c110480e83d6400c401d0350358400d00880c500c291520940082c60800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240964838 1250 240963588 240963631
    0x5101d0f0606150f0c0304050a17060705030c0d0e0105090601050406080a080a03060503030a0e040b0f0105160303021e03010e0c040302010f051606020c0303070216080703061802041b120203 83
    0x70f10100d401d5900e0319904d00740328401c3c1014456801080e08072205600020301408a8544100d5000040807491400306c1c194409120b260740b6001d0152009040c00030200c081415103044a040e00c402c107403071000c10803022000340345441c00b8003402d4403120114043c000c00815903013002d000d60000d440b4508004d207101310255440303220650116003180101aa20340003c500350358280000c01d90140030f50385d042049021441080100c4131400b4485119205800c004c0d40c050341c00c40107440c1d03402500d5881000c120a1824141c0280c4958032800e854005401d0400000704072960181d4107841d4401c030b00111540c0c0d150100c0130244203a02002c1e001c640c1d9048844c5005210b04001d100d9514030220540c0c0c1c0c0d07030003070303841e003059800030071113200c00340c201000300462942c0c10001ca40c1007461001403841007500e000b100d103490703224030300016003059100c26520041700c0c0137000440c035196024000304242c90400311816140080c01d42c1c008001128803075050726404960095074001c0d0106503022009407040d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240966088 1250 240964838 240964849
    0x70312020f0a0e030102130806041202160909060b040f020417010204081e070519090b030627160803030106090b12060d030e12010b030706020102130306020306060705101d0f0606 78
    0x1880104d034959000c011001c01d0703400c0a06a98010400c00c401403085003064a06260101d0715400d1a004660180e0070200541c2c124540c014200d600080f4006110400d80c140640070300181c41030207420509220003a01d0640c4183e00070004c85207092075803810200b44821190070b0303111f00e2044400750ba200c11203c200c074050100d5000c8940f4480d800303c0d03481c0c0e81c3e5030b0041a00c9100d03076a8405206521968208643d8030300b4007900302460402c0303000e02028a0b018000c130820751030180300220070342d5a00500e58450312080108100743d82909000014003590b1b5042c1c95a240c0c424090440000c00d565400600e44d1540015a0740c1052a030031110007603130316101401040c0420700010317800c0019120480c50300752210071804e1030030301600c03001240e9110000c00b454606030707483d80038104680c07042003180240c50040b5003080503603500c0900903a40792a42000200c40d400740c0c45015129004950352500b54030f03902c2c0e200300c49114001451003101c00512482d1030700c2e00c025190440042d0001c100064052525 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240967338 1250 240966088 240966107
    0xc020f0c04020f160305091f0807140c0105010f0302041128090e0a050406060b0a1e14040e071205042004020c030a08040b092d100908070312020f0a 65
    0x203900318608059000c0fa0b130208254158505070701149001030046401d050a0440c3c0c078090000b0740b91200d0002248000410000000740007208000d0b2205e0078501d102c550f1400c076920028944020300c21541c40f062545400015840228803503803820b46514446201c440944002c0790303070b51001c00906001c0720320802a030840f0f18400c0041000030340c1c1c003007030f5500207280040c007454500000048514052404004490b840d402403590f0600038000c4010880e4091141da106070a0030194684c140c04800050720108403140c0140000100880c002c00c415010b841c0980c03080c0700369540d5151000e022101c0c84100c6000b5107001e06100442000c0030303111245298203544540020308014644502c074040203043d50001e415142c0000c24880c2440b05100240103503d13000020180507042d60100e20b08222003128034801c028807003203d80b00c02580040010b015208061416204c1446994814506a141503102810840c00f1641e03004880007003003032a10a030f4810000787c041c21840c007100d4040c25900403d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240968588 1250 240967338 240967357
    0x301061a03150d0f03171b0702041a1804120309030905010e0a0e010f0f0509090303010302091003120905101706011d0d0c1809030212030703200a02010c020f0c0402 72
    0x81043c1e00c8000103280e8821451001e010f41e40f00c601c1000154090113000c880989071903a00724150308240e80071801c100444402a504030340018100d020003e41040e100c0b1201800c582c030064051071050070005051840c0d110303d114844290196111030011f40c00c6921640001d000102009414800c0354050440d01d044d013a8003c000520107555030240e5030910b6800d8100c0310500441c994100702e00880000f066000d4141124101202c2c982141016564001484060f100f4242d60740800d003408a00005030000d144c110500116940c1c0307030b80c2c01070b10903403e9101d07842c0141c2e84407210345a00352144c080d540343d0300c04601d0070017950740b1407000446038445600d20503d1880c4180c4c02400b104c1d90f03001e08081c40907116108541c14246001007214000d01440d418400140c142194800026800709644422060b544095600c07170311811000c40040c2081428582d1519143d483d42c484000403c014103201a12680207105088060340c0c00c90f143c070b450b000780d1a4590301900c0c070740304245016005044d1000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240969838 1250 240968588 240968599
    0xf1c030c11010f0c020706030605180c161b0503190311010e0a0b01060f050c0709051506030403030b0f0303040f0902030c13060801031b0509041b1a090301061a0315 72
    0x10700701200e40d0850700f044220242803030b692607021214a4040c04030800810f082c2c1000c00c031031403401c0d0115184810a0103960451400c0c0000a0078030221001038482201039100d5860f0315000703500d060300002c218403948000101e10881c0020341c03442d000130309145860164281e10f41d0005155410f4440e800d10090980c155501d880c82e00c0d480351010403a00607407601900e45005554500700f0080c080c104103d0544040103020410200b01c010f0002d550b42c01c5a440389000555642c41e030007001e11000c1030300946075212000105000605034550440d102c0140304582e0420020722490400d80d43e8802ea20801d070100c084100e042040c4051a4040c55100c9807000035030345000700d03005031400c0e1407020750414008074400d54018001c1c0400000804500c29504100c1d001e280c1c102000038405420040004006268040c4148144810203e0410041c0303a02d0307200b8180000846600b4005821200364036000350b103010b40c0010a0541c0c1e04000100b1303147d0758140c074990b4684542039807200d1000340190341c010703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240971088 1250 240969838 240969857
    0x605090f01081b030f030a08241807050904061206060509191a0409050d1b0b060603070e040509030a12140c0c030717040821040603090c03020d05010c020f1c030c 71
    0x8000b48000c22a00450366101c0e0003034030b404c3ca015a210328682000700080300c690009c1b51615102c040301203401819042c0c50200302d0b501c1c031200329500c0c0300d44903859070084d041c004002248980c9464114001d4440c05090054640391002d01c50240b0080314002448680c420203c0403c40350781e440547c2800d41c041c147d00c044000760000c24140c4040e000200c07256845505103901c09a44a051994040740528610241d40b00315241c160500b00d001e80894866074000005c00d941074003e00740000c078902c001c0d0041c84145000c8003120348a80251061201160b6400410242850140b050f4101c0d0050300320300194039110070741c81c03284071303000032540c6445484104441804201041958843e10034240704055440342020885802e100d0007008218000010300103003140b41940e007040d46d082d0703080d510740000d000c005401c2c0365228500a502c0a50088050f5090b50306000040d08110078101c2079400b150100c00c0d00a40d4503580356000820090010340b05816004040d209400080c0b022007149405a400e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240972338 1250 240971088 240971113
    0x1002010f0e0c0108090303130b06011b050601210503070602070812102408010b0a0201060339030c030609030306080d0903020a1d0109090819030605090f01081b03 71
    0x8035581020030300d203190b010140500c099a48041803560000520000c1c500703504201c004210040c031b000400910541e001400035030701d41d1289013a01c545841c1c030343d621070385203c160911703070b0707c0705e0081c01407414103505442c441c405e206101d8100110564044000e51030040e482d1140c2d0000d40000108484801c000c10948002074005100c1d140140c3c103086000f0f0056261000c1148804e07002016858045600c0d003048131001e800164441c11a404a025103a0320424940300703d0042280b03402c000d081c500604003065500311b98080c1a036040130303d03084d510380640c1482a0703004900540c1c40024605001c800007400003403015080890224800c0c20003150304c44d2104c1880c0c2c1401c049221650004090260402c10741c41d0211509004120b1100e0742600030200c04c480003100c070b1b0140569403050740c9892865040066850403104000003540c0342202d03014081c0e1008014080710700c2014414908180429002e270701ca840e9160490f940c820003000300802d2000e08040114021120561500642c45031418 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240973588 1250 240972338 240972341
    0xa1e150909060b210705150d09030509042a05041212030b090403080f060103180308090f150709060206150f150a021513050a0807060227041a0604051002010f 69
    0x4c0c5400080c662404c01c18001124134001e52039000c580b241c1c001503189540c82e500c10f011240040f1030442e01140078100c80c10182d07002d2088903000e940291801182e1b1540b400b07101c04c10244860b103040105000507140c039046609009900030900c81c1901d202003500001c82080c0b8110484880c4d0401080701d41d60040050039004088409401103007140040005400c0c600f60307242e50000007420304000b090310051146c20088030700c000080034040810017060202004000000382a4844001caa036003001c0360b0305245010f6000e88070f00d40455420400810f140340081101803040600400000c4072000240030002c8130680f9620031500070f100c14400b80d41c0c1d230300510014107131800c02e40c0003403250445001715141089001044c4d0f0914468142035640021000320b240b502254010110a40300e00c11400e202c4000e11415909a0180c042c0450b480d0904030410b107020110721046500f00003214030800100c0030140343c19401e0354450700410090200345011008844121906d00c000103518201a204a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240974838 1250 240973588 240973609
    0x721091503061d010e060609041e090308010b0f030f060111010e06010518040c0501030509070e10090501090c0807110102072f060406050d180b0a1e150909060b 70
    0x200082d2114028089520b80c1c800001101d18080b04003d19589403000c0c80407200c13030240031103101d040c000507004019a603940003e40a100340107841d00005a80f030160303100a14030103078114081641c9000000c0c1180b06030050303440300c40403802c42030701e1552103030b0045486820040407181401a81d00303041c1019132092007000442020300c002000381f94100000c01001070700d412074020303200d0410820080006c0801c20210110f68082c2000309050303c60310f5040341048400d402044441c0758150400c40240c2180f43c0010898003200010400340c1d8840e03d215040d1640e04030000003003200140410545840341000f651307107690340400142011215034070a850415100700c1c400b00c04403031020001d280000000900082c0030f00700c1f192403401d850950081e0081c0a402040c0b0007143d0740310210100c8003081c00401004070303405402031146281c0344420b00002c2001800c0748680d00d5042110008a039601d104054807145248040041c803440c2c0007a40c4003805203000c007207980944914145119458280520 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240976088 1250 240974838 240974879
    0xc030f200f0d09050f060d02030403090302060a0309020f1804030c051c030506040b0f090408030a18080712020708030724020c15060f090a0b01030b15070512072109 72
    0x81103071085200008041522a0704124485c424084021000b903599070304540c1162410a800750b00c0e50784908007900c0d48800b591001c0d4102c0c0e80042c404007800e0307066210b101c8940c402ca03244070304c0507074800c107101e10002400d00c003602c1d003a258008240440c0c000e000602c180c0d8412400c40310b00b03140ca41450381d240801083c6030001b01c1e8850050003450b2502c0d020310702c4119015650b8203900c0205d640015201c100190010700b0440c8004082107401c80c00e50449803a030805c602d410251540b0520b0300b504c0c158080b4105841100c1e14104070103041c0d1001c291a41140c111100440c18412507840d8010710f200107101903900800541008010041c1c0e50001d0040002c0400161114070f4480744108034103080281254400e400000414240303070b5607004995008002c8500004001001100582c0100207111606a00800340144403c9000c01c200042046511590588040c105420310320b034801c2c085c1001c014001482c045000e00305821070510307400d080046240901149a684c0303946040c055480440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240977338 1250 240976088 240976093
    0x90f1909091a10061b051603140714010f020102090301050c0c100c05030a0902010507020a1806050306090a0f210801030c0503061003060b060909190c0c030f200f 71
    0x4600a011501c0b1007181c1d840b5020104485520341079a03400d81d00c440c24000c01c41840301c0c2c50840102440c200107034200b81d960000c111100c129481620042c1e6141c0303440100d81c100c00340340340c02c05004408110300b03040381c5404051b484e60201143c015180360ba540101f5100310765081c01200d40c2a6002d00625009401e40e22505a654550b20001c50030414485900e160850074980b61001c003e90100440f6441503070820001480c1c480740c80100c440384222000030354410488400400c0c05001c8060503a9080103441c010450940d486091644604c0100c031035100a802c03540c8600042988241217100c1548291480700403004104602200305c0c81d005000d20004502c05e0060040001c58464180a03280c00c0700200200d281103010f607490302da01400010121134070f4150000080e2a4941034518046008280c115685000380d01200c1c1c080c3e0701010f5900071814101c08100d55030144060742c0c0629015500c21004528803c0706641b400302221284100c0341a4a2400302100c0051250f40b0038000300102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240978588 1250 240977338 240977351
    0x7060b04110703020601030b0714030901060501090602010b010e060d060b03010801021c06271803020c10050a080c0703021c020d1106011805060d140703030305011a090f1909 76
    0x280811100e5104241803034081c10440d10700400d80029a445c11242e21030300c008155901d04400b200d0100c21002101034401d000f0060202d0300704107420240607502d084c4d980e002100ea030703130381c08a007611400c01029020500d00c2202c03000d5402d041005064030b1984440100d005555000060180e0b4003da10035071032a54041003001296040c450040110310300c41d84203010150070000395900381d41c1e115a659100075240b03141e8135a08070003500a042000c00d8040c4110420701103060113034940449400d55403103080e01c40107400559000304165030424029540300d0b009561410022517181d40302000030b4082d48030ba404000f0203003910680c400010711455014210302c600c0c1c42c07006461007052020349410790300a60014000f00c0b0b0040e03020102c00690550214040d11100080f1f11b052020703040140020f04924040c0608410000740441100d102c2d98040015030b90761001d542c0220310044400080f10001c0004200130310f04200030072141100288480151540c08060b40300002160b070200402e151140e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240979838 1250 240978588 240978611
    0x91401120b03030310090b06030709060c050a06050702070e0c0a050406050a030908041818031b0c0f06020601062a030c0510090c08010b01031418070b0d0b09060f090403030b060d020706 81
    0x1f401c0f202c076070192651400d41c01e01c900041c002e0310440c0030301320400c00351011442c00e0102c1000a501d915420207004c00141c00d0078a0000d407241e02c0ca00600821405510102c0c070355102d54000c98401d99415030701c0d00c1c100360030f02408559a0b40000d16400030103458080040100e80154001c100900702c0c902540842d41200c00c482e02a5000c0d0114280c40d0f030042d10205000c281c0199048842c03401c3c50321092442c0740189442d40312106580c029184480c1d24100220f4900d0300014054181c0d160380c3c41d400b8005000d01002525400c0c19588120681128145240020b000c1d40074500c0d1903120f0310079100010203201c5660101c031b0542c04c0c280d607000101d410410640317000f803058810054082c40c0a2150404031440f01c0200031000e410b03000c504000b020200481c2c0401d00c854809000710566581e07980c1000c0401d01d01800b020550b2900c504c28000c041000c2c0d140c02844000e0460000c2c1045100d561580c4095004007061b080740303a01304004200001c0d2151061000300310f011302c17512000440d20f0218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240981088 1250 240979838 240979841
    0x1a3103061d06060105090a080102030a050906012304051b0a0309111503060f0f030a0309080c0a060c030e03160806010305060a0509070306020f09090421091401120b0303031009 77
    0x981d40c40c481524040c041012440000c02ca09500c44801c5c01d21079503070703003003000400c07204101b07541f050919502c00b00901c20302020304d0f040207025030281d904030b030700382c2e40c0315407484c444204141d0034a00440740101041c040b034240754105c15400400c0705010b0121030b0907984410007a90150385510b0001c1d48e914452000c02000204892141106592103070f18040e1449520b04180f00241c102071150f5840c561460551b6070340b81881c40040d4000d010381c0d01d240f44624001c0c0814045004480060003007a004c2c80305402c054092100f2900310755256894801181c0741074402c04903840d90b40f40c241c069040c4180034050795084110041105400420096256043c07080c10001e0181664800360300700002e11201400000d00002907030340084c001039456101c203c0c01d2100380319428803d81c00c8a01e000800c403e03c24481d040001c406c481741d4090f9141081000101c0304e00d4180c1c007da4102c800d40e6000f82c03201d54807841c500d010700859403900081180c000000603145400403030318001c0d01e4000d554140300d40d00c4617 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240982338 1250 240981088 240981101
    0x150612010b030f09063304090803040c1409070e03010b09010815090111070b07020a1a0f060103090b1b0408030c0c01020d0302040b09130f0e030a0e06041a310306 71
    0x1902030700a6062444540c03401015a43c80c040c50a15180f0518068806e541b000488500009000b00209480c0f0b01e4007240c1c64200710350660b0010300300d51001030710380c07840380e400301a82c2c6005002c43d10958812000b40c40340a00d455520381c0565941c000d03042c1c1600d80d066002d02802e4404024045222030b0f480c480c1c51014010402c240c164100b019400b100d00c03102c01552003440c0e000503040700665030508100d1400b101c05001501c6044449810404a00340054250045400c1c111540a81d41d5560054003520081d0324000c040055840c00901c103c05904100303500072100c852510b203025a1446882c2c60b6070031601d00031a490300680526866903030104800c0d48614000e00381541030902d00424401c2c42e0241b4144513019040c010ba54100c5140154803211040b402c1d44020480e41c0249052969250010f41d0301e44042120741980d18018502032041d1000c4401c040c045e55000d052a47e102d01d8680c1149507500c02e140b603c201101060b0122062040008218841007440c891441c02c100094450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240983588 1250 240982338 240982351
    0x504090f150f1d0a1205130b07020907020d0905040b060c0114070201050609190c05090607060b03070501451523030a1104090903030f060518150612010b030f 69
    0x2884000001480008144c0102c0142c03c5215100240f0b001d031410f440510484103410151043c1e100d02040340314854000d0203406000384c0e50500140d86604003a41c1c1c5110805444c004215580c00030440d92902d50400101d42201078071160808000d034041070300351440742000c402c17445841030800c031155a091007050b41c84001214440b0523424030004c282400c9d5005040c0d859255120b840c51002d80e03000304200d54a00c00058407840e6261402d0400d40024003402081a20070b02890200003400e610448003460590700013108841200c05c01381d00c00d81507d00543c5c4452603c4203e001c4c071940d0580e80418880200280c1d0710b000e40746180e400c001803805201c0002010342040080300c881b41401840252640290010000a6010329209850400d401b80d6481190b00c1820010800101503054002c1800c4d20304258003406903030344071800c0141c1e03c10511014244000c807507000410b0a44d800d8882070f000000581050300e40200c200010080d80000d800800e041c500c0001404800f85000600aa1144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240984838 1250 240983588 240983621
    0x60e040b060d020d0303020a03090215070b0901020301081906060504020c07030b0a090c0e060d051f051003081c060f060f02061e070e060408030a0804050706050f03010504090f150f 79
    0x4a0f40c00108035130301a4030044c04042d80491040c00e40c6010f84d01801810344c0081c00c01001800300402c02943e50700580040710355004040c041683c000e014000d40b8141c5450b44003802418182165980880e8181a8150740940c0ca032800016540c5591004080400138000584440c40c01c60030311180c0d0100c058541500d080c5495040300c0418240803420041d41d0490019034000d444d1000002c003181c280c0340000d0064011083c9403014003a9141c0060204042c019061180d81d40300d000440e41d1611307a1002405e40801008045402660740083c44610007d20400042180d21101c4c4c520032011203411040104e04003a041080d0150100105e9500c20590b00c01e1400c1115500050303190706a000d00090300740b1607125a81c00365039990381c05a401034039800c0116034070781881e2940207084840c10f40f815034003405003690218500d40304100312540c00100d0b8006c1032850b4a000f09001c0100002e8034145c40b51741d810560800010541c501c189644411204d02040340c0884003690000c4680c1d102032886040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240986088 1250 240984838 240984859
    0x20c060706020f03010b190906050f03090a0510050612060f0c0a0c08070303150905040c030816020d1208011203090530061b0403031407031106010305210301290904060e040b06 77
    0xc0d071b10800700d0b400c00d240c00c3c518079225181cdc003103e14601045071000a0040c043c00c2400c200405040d4402c42c40741e0030071201034072100c0740c07a02e00d0b5440c0c981c01d42e0030510a03551000000c070104880401045400503500c4c105a02c03046036200c40403660442241100003903203c500601070848400316180182240ca00100820b041642e1413180481c103034480101110350114400e10700e504e49008450360f0741c0d0050150000716031035141100050041600c0c400208004c0c7c400861031207d91442c05451a82c940c4400000c0340c02c1204000c0018a85e11f40d010000d44104021022484030070a042c080d008003078010600c905258024030500c10200c000307640e900138140010000300b0707032242c0207c24001c5200301e01c03640c41804d410111150748150340c00d000c151040e00b00000c2000340c0042d07080364505074148003c8021076107200003102484284103903640010040c02a1490b401d1800800c807100010000140c40d00c15002c010806075880f95002e101111010820071051103490b201d4181d00503021a84450710 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240987338 1250 240986088 240986099
    0x90315130c051e04050403030b042f0901020a031d0a06030e0705060901021513050601260d080c0901091e030203120a05040e1009050a0e010c080601020c060706020f03010b1909 77
    0x940c03c1d6002070762180385c0711008113060600aa02080c0c1094010300f0500800c00e0a510005c0c0d00900c243c00180681c0c03414842c1001000c0440548000c0c0405170b02070440840d894900300c1d40701e0000e49044120700d441c8019281242d40f0360100c0e000a00b11506c000c01d200c442020b44a00b40300c42540a0340c01054100200b004503a03011800352641d40301055400e899490700000101c06a061940043c181d01c900c0002240b4089032203000010f00b980c88030890303071030b0302290070044d01c0e002e0310320782c0758081008038002c00d9504003004060640d185061624001c4070f940c13036a0840d24024901072850760612400c0d400c4c419428103200e8050490b1180d00480d143c0f0341c40f840000c0603032180d4450009128911404250f1910f01000c8034030062954502c248410b05002c0e498500800504000c48000e40c60300c1a102e0106001c1d00f52341c3e21072481600074020540680b010301005c0e6015143c102d48150b8208180c07601070481c04081c6000c1d024110103561500450f40610001c00c0a012844084c003519040802c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240988588 1250 240987338 240987379
    0xb0601021501060207171207050f060c0408030d0507020a02030624010c050303010504020a0207030602031906050d1a09070e160201060803040b03010308180d150501050a0803030c090315130c05 84
    0x111b6004500c14610440d03507100a9042002c000850500d114001a580061080004580c001948040280c03011030f1201c01d08241a8815807068010300d40042c0a1502c3c01c0c5869441240c3c8801e40f401a1401c00a0603400030b4103100c011601c002c00144058403524103400b03032022044031304100b800c2c00e0120044070b4440541e0b80c0414402d49108940004225020070f20070301c141e900075940481c0940d1241058020707800034059001a02c00e00a145c0180000c0e41d00e4071034000c030241a0000842c5000000c03402203207000c00001814800c00b4898a840092400746a00442e03100d85141d400000ca500174201c0003d094030080d6001c020f40c0e520030300050111030080c00890b03044943c0910300c83d50b1406246541204d1a0028490903403041003c019002071010030000c44101c2460400e0400c000d84c2c0394010088040f2160141101a81c000d200141001085400038199500000d04031a2404211078203207084041c00c944080722210800c10060030056032050002c00782008131680180100104002e02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240989838 1250 240988588 240988603
    0xc020d0909091a0a060e1b120a1803020f0606010f090608040215030108030d0b040606020a02040f0b060a020d020f190f061b0e120601120f060204050d0b06010215010602 74
    0x4450581d180b100804100c40100c00d4216425032050b1140c2c24a8102446402030440740b0664440c001c1042c00103100116406401580341c0d141148035007800c401da0050000b03150001c03c0c10a60a6980e0380351003051441d02960005036100e68000c2c480011011030040c24401c0c09004035041c0031120034803495550304a83c0880654415203080e492036a55400060803202109406000001c00000080b8281c03401000529600721000c005106090860b824002203c81d580718150040e0014a40c01e4010700d46500140d00051814002140d602100d500144ca0760303114826500240c3c1c0708508070b00540f0340620034a9410103014003e840c3c1c3c440c4079200c4289040c0c200d02c004115a80200e4203c0800680741d1007895416440b150b440c004900702030700500010360089005200b10310308000302121010024134141602c02c24502d0b281035511036901d420102c01c80e004211035141c3c090001182c90b40341d00018040850242c1245d0440741401400039082501c0c403820885c0ba90f0f254030061121070380009101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240991088 1250 240989838 240989849
    0x902040f0e01082a09070804022e030b0f060a05030106110c0102030405010c020103020d06060513140d02060f12100f1d0403180f0b07111905040902130f0507030c020d09 74
    0x303041c3c02c030900c140c01307030300180d080f5801c0d0340284c03090300b440445940701e001984118400d07a0303425013001910708120b01c03c46540014a007090510111900c3c0300380720307403c600c4c160fa401038482c030744800c01040040c5c4103811a00c504030014401100400070150b00008a0381c07000f2485024000307050803800001d449105d0b9010b664144211400d000b0f045902c0f80c0e0440741c4c101c61b503950401c00c0135261040189554821000803800c81c540c00d801068074200007142580480300103120031844201e41e424030900d500030803186440010b00703108a44040d50b1480d14288a941c64480100e801ca040440400305100e15402981040314070300d58100b284456680f180381c2083e010300700031400081c0c0300a003e4101a50750440d45100421540000c0c0c401e002c032000c2d050703040c0701e2480d0448007040707041440300c42070106c5600000da11121200700001d0600b42c0c09036001a00181c8800e40b00078030114102c0c00d480504d502814a60750f82e00c104a0101d6151007070450954503440034103031103404030100501104160080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240992338 1250 240991088 240991123
    0xc03050f03070c02091005040e240a0e0610060306060503070503070804050c0a03080d0c020c0901093b070f050d060e0f0f0a0605060109050d060506010201150902040f0e0108 76
    0x31031241c43c0070390400d0070740903401003200c2c0c034610b8161010301c1624a14800c8a0140c0d0518007641d03034000f004142e010011207008901c880700300c078000f8a140d40e090060072468030680e8420001c104403409001c040d00c031309000d41c01c0c481140d1500c6001000c8a5442d484102001000c1c824442050f6011044035041000c926051490b07880e1401e00504001c071420380c0961000103007000008020590010f040e00b455426020408801071100c140e84484142820591000100005004001e8260b00c0114995a9440f010340d40554109001e02004814800410070322844031445540000420140d00640684440030042ca80703004085841c1c6d101e001001000796880b101c81c200500001c00078942c0aa8010b4129041045c001d1641501c5024200c4140e58181c2001c0c0000c000b94002c080c0c03142116070142072203100c4c04c20790303c0302c1004100180c500d904554a4007407401520110728a0f60000d00200000103a5841c0703040750407503611000c2d0780109021195440108640c000218440d400b42c2d410090303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240993588 1250 240992338 240992341
    0x170a0809190503010e0d2304210b070c06050702011104061b050d050301030b010f0302030c0d230f07060e060d0e0307080316030c0206040f110a030f080310060c03050f03 74
    0x4841003107070040e0030840d015807a21450020a034000580981c268402e0340b2014404004156030281c100c1c9600807810700004100801c029400ca00140b404d404109400c0000c5101c50540d5080300005040c0c1c0d2010015000403c018240a280d00c291600200240020807000c01c0043e4412001d0160748650707018840859040f810003159029111a03481c4d01105071107a8092030f81d00036086420a01081d02c1201072040040f1b01c401d00750303d46030140c136001001000e0b0303078401000304101030040070822a44000d0706000c0d8628140007011090004070750300f018121140381c84207018a80109a44807400f0440c5400c9608140d4503400200e4080107418203021824000d481600c900e035101c2e01e4401001104000704011341420b5520180d150910155405e00c100c0d041c41c00c040703a503400151409003002d140d4402c4080000e440b804205007282c0081d200c000c00586d2921000d58681a0780d1003900e900400004000c40d10020b90082800352065081c07a24810005032001444c50162900411746c0c80400030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240994838 1250 240993588 240993619
    0x10c061416030b102003040801060801110a0c0f0c1203020105061f0e13020c060a0f0f0c05090f03070506160203010b06070c140d060603030e042f030a09050f07170a0809 74
    0x5c0314029000c1240045a41c3c0f541c2d00c03503505000740040d00c00d0000c0d651800c3e60300003440100b442190f40d000d485030b46580341c000c01911801c0d150301c201d110484901000c101e00203501000c00301011481c42c041e4000040d280f400b9424081c40603100c1a111144a480302400c500740e60300000909002c40007034840c05008a142180d2000a110f14000002d15110f03400400960101036008040c0c446126001030000d850355201450030341d07080c100d1440c0801c40a1020060a0502258103050454010100c51030079a8070030200e402a0312840f0705860303400e1035115580c194282400348502d0301d9000d0390110303c0c00d45141c403540361805143c055030701716049900b845441c6035101040e140703106070002c500300141542c1c2e113000b401404104855902540c20010746900851102100501c0d542d0502662030302c02071000e4142d4003950000303025218a50b611354603c00070410030404140e403484000000c11980f81065030412007a01d4100d0116950307441001c0d07010010752141c0542c1d01d803100903241101d0f0300800d075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240996088 1250 240994838 240994877
    0x60a03030516020d051e0c01050316090315150f0509060907020708030f04140405090d0f0903060608030a14031003060b063a0905071202010c061416030b10 68
    0x100700103944031a81015407400c1c00390100d031601400042e2401421b01d4140315581a8640d4070701612035021440900001d240c14007201030598820382c862800c07007034864496071103e070310000c901200c8226617558018031002084407040d40b8003611100c82c4110030300b4609000178086060040810f80100d15900c00300c0da620b40200640d1000c0c08002c0246c80e101d00790f05034000d442e50824819540044da103414020a10308240c4603090060328031030080d0000700210f200a8842e4454902c01d101000280d0305c0000124045126040180c400700000c3c40c4d861142c01c41c014810500c4c048481c501c1c1c030003081802071004480021b00c0849074041c501103a032003049070000d03c103070044000c1c0304001d000f2000060b108209941011217100000284512518074182003030045410a0000802962016000b03116068207024504841e1f0710501d00588180566910142920f105034011402c0400d050180f00a8040c44001050240198038081050801040021701030850300030203881408149440e40480300101c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240997338 1250 240996088 240996127
    0x308041a0d09060f050609150625060204030303050c210406020f13030516030f30020f0706032a0509040204121b0f0e09011b210203060a030305 63
    0x1001d010050001c10307060a01c09400c43c04403c1c3e94085c03038903000030720307529003124a00d0298140320740342000b1500c00400c2c02110703802159800300c0d2101d50190007219100494942800b2440744501588980c95444c0140c19550007612070b1020201c11320082c01c030000b050900343e0f9180d00c180110031554540c3c0c01c0c004000e2041c035607000303000180000c0c48800e2403002207007001100d06c02d4040b601201e111600030406142c0501005000030420740486003c100200d6030312007007015155560130285480014150000c0401030100d0158000170b101740c0d240b8030305000600c01441d160409100e4000c072441c2031b8202241036002400c03030191414140100c18070950559000d650064000c560300e5466042401e540005004c00715160010039180000c080f40d880d246001315419450304040c840c0c1040c1c201c1d1000c500c0100903240b0740d9601c03088003a00b03c0f0340905402d1990119181c422100d0420b4580742020a020010395031401d00400911030715443e034815038011246c041c5080340d11100404900b5800059 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240998588 1250 240997338 240997357
    0x60f0609090f0c0501080c0f13051c03030509011509020c0703020901081b030309060909040503120a05180a110f0103060f08060106020607020609060f090a05010e0f1002040308041a 79
    0x30300740080040000c4007400c42d400500500c1c42c919030f1aa200011107a010080380e03506d014400612004001c0a195405085c2100178203c50842c0a901c950110b214610380032a101c070120080d04c1128140b40d098030500350000700c041c0081c0f00390889080b94401004d2144503031032129900041480640c8008d00002d00036590003400380f0786a503500c03451181c3c1e444004c4520f251060440e00070964626000044900d003640151159042c0301d10170041101e4010000e1080c0c40d540000c004000c0d024a200381c1c0d1a100d000801400503843c00e11420911081070125408041c81e070040190701d011070700c02d10800a50400031a560301d08031207841c00480c05083d140e8403042049003140c401013007a03080890706905a403010360031110203a0f200c6800300d940c0e000965010805420000218546104a40744c19500410000444a185a0307070703a28a800c5417004c040c141800d80281008161031202032090841e01d802c2840e06500749810758881241c11f1085118800c810b0b511792055000110a070401d480d00e041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240999838 1250 240998588 240998591
    0x10020f060903090a09020306091303090305010e030d0b0f01021c0516080703021501030c150c0515010e06040905100f180f0204050f010b03040f02210a15050105030307060f0609 77
    0x800c44030950b0759400064010703202d6000f0b500e0208100005209603032080e42c0051003112230382c80300300201c2c1003203803e0682901000301e100b8002c00820004d008200c403c8550200440e0f80741c010780240c030110741c4004400d91207000088000f02d116a400624404203840d03400740031501c040c14800079034052003105860b98103400d04462103418400a00d0181c21000c4c02a000c0d82e0111503042c900e44074402c42400020100000c030303001030107950310908101340741a1480c14000040b810913121710f4030788041840490b446c06120001845540c40007024140c01c00421385080c05a00d94a58070580c031910410081c0c168603903540d80c6003e214003160002000c04149420340a112850b07400c00c4111000207a4043e40250b007050301042010310b400c244141280d0742d0442107800c5854503039407035101c104008002d0340e00a60103d060032070500b8914001d42030780450f50041015403c0d9150410a43c40b0262965400920f040010404c070384021044401d0180c4c031220000e81d001605e0020307402007400b50044081079 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241001088 1250 240999838 240999841
    0x30c060e132a0306031e0f06050c1314032b0e270f070906050901080a0b0907020a02040f0c2709020301060f0e101d060d0906050f010e04020a0510020f06 67
    0x90f00b65000b00300f500d00408401403584000181000f603541c19800090402e1444c10a1301c000c545160300c6190000140503c0700d00e40403401890700f454125580040c0107040114841c00b44030318040194880308203c0707507020030718034030403400010703100019148500a010305c400e8410b050307503100d00c80c1c03140c051307400b6606102100307049010300c3c0c901200725803c2d40c000764680c020684581c055000842101e480d9078a041c40c041c0c40000440d02e110002d414461459200c28400700303190355061009214001c9a401000b10b900540100300503680c0000030b0301856440d00c0840c841d850781c0300c03801e208070070b121072600d40d040d410035a140f02e100d10441d84031410451000c0004107000d64481d07500303140075401c0c0da02d9030b940f001890100034036494810300c1300c004039010394458084e0012540010b541003100802007030600a44461000685100c404220f4441d561907040040c1600450381842c0074001c1d84503180d103145015408544580c202d80102889040020b0701e9290315482000305407480d00d20802510042d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241002338 1250 241001088 241001171
    0x80d02010e0d080108101805250b090f0906030a150c0e0102150a0506011103040905040c1211090a3b0d0c02040905010e070f030c060e13 60
    0x9080340c01c0071141a025aa901030030891041c905036068030a500050000c0303480305031080004020b0980e444980400415058002c0350060141c211802c81805030b1a085003090ba40c080303507109083d000b290400030305122565035502c84c245100d01004059500c12881d1f140c0400191600c41c480764000c00e02410303800b07520200c44842d0401c02c954891074079080b900c043c81a006a0720f45c4020142c004d0303203a040400192100704160419900a81c046c100ba5181c08240b101d007a00f16171140d0007042c1d9464580091000300040403150074024146010707002442d401d01c0d95500d0352242c0400b60144101000d101043c580d01583c1e00450015500d42c600e11001105001a8181c82d0030000001440d0006a0380b40300c41940041070f4100b28880f076a89899090341d15030700f0800203200c010410ba549641e54038440201007002c100b20009820f4818418420314590314007045c07071820b42e402220070401001036440c1c440e102c5140c02c2d00c851101c204003041d451b5a8000500c42c0c0c8410505880e060b50407120310050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241003588 1250 241002338 241002341
    0x72102030a0822060c08030a05040c09060e010e1302060304080a030615020c1302041d0c0d2408010204050901171005010b0c0f0a0210181229040803010b090109080d0201 74
    0x1c500e10f6641c2c440c0410751383d400643e0307248031403034020302204803c00002d10103240580c40554880e1249001300e146948501c1107104968003a0070000f042009a00180401000891801c0e84140e0640103014408619400300e000d030b00010704002c0140304042001ea0002c0d00a4010102030300300c8100ca1000c1e9528203000035039500100348074900903103136900b51004a04181c02280e09507581440b0500c0500a2120380e0400703034900800d9024041420701040b0b078002518040d407502007859002e180102c1e4480400100948616481580740c0c4c0c1c81080100b100d40c9035080264110f407088040304000d0410b51920b41c3c20659680b6072407a4072441c3c40000b088a0301c0c038501804207020404129481c01c07211040309030350f03030780d003900d0207075020024030460301040c2e2041720026a004000c82c10070360724170381c0c40d5440e42e081e50804008548a02020320b0100c1440318540c0054400c030110940c101203400c01e9103d8040f144010b0255074100d49002030000d50a9024000140007402070001310307641031019120003030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241004838 1250 241003588 241003627
    0xc0903120703031505150903010209060307030b01020f010912111906060f050604080a020f2106061509010e01030e0102040e0109020c0601121101050d060b0a0f0908072102030a08 78
    0x10082458041d0340d000c0c80103503140440544202402008030108021030b0b480b030b0b1f81c100e900080c2c0c1c9503408004044007a240d103405140180c086490100c0c4a0584070006418105c044008850682c500070340d8078003044e1443d01c4080503040605200190801a542c001d080840f0703030141a00362040d03003038041c00b00200c0b50700400458101320200c01c080e50702d400170440c1c0c520880c0b08008031507012003040c0000d4540515071164080000342400c54500c4042c0c8000541d4008020310002e9420410401c2494105003400103000200d140c8594607081c61b98002801c4901400341c954101541da55514840a50950448000e8050502a00041d6a540010300c002e54014000785c4581e0080400002e0804841115500e510343e0255804440d10459001168070f50000520307148095105c600000d8102e59a01c010141a0003554421940c1c5076030310b10207840c042441c0d2200d00e480c0c0c8614001c00c1030603c2d03c1d0b44213044034500e40211943c0342c0a800002c1c0f03000f081200c041c0038004001006003004000c4c0c403212 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241006088 1250 241004838 241004843
    0x40f0213090b010f06020a080405041802030706121109101101021e03100b04120303020c1501090905061b040e04050f030412060b100504330c0501050c0c12030c09031207 74
    0x1500130350f2103080c1241c40300b84401c0300070080c502c184070070303c282d03d00794010b01141c03050400b25a0003101c1c0f41d00064500300c034a52169001c5094409544042d000e9030107650703181c1c0ba444200c00d1a200950002c500d5420f554510503003000007184c03a15464010a40407030303400c65121140ea01241c2e4504509030229842034588440c0348044038030009218007e041074500721440c501d1641c284210705e45040d40a54020b9220640b14000c0e002040d081d10810903000303028025009002640c0007107483d0103071070810301a008100b400c5414036403441e01c2c000c0000321010344a0100d480304803901e4610f0060b180407041c14020500340004100860f0300951010344982c01c1d03000d584c00384055407595003032003004075110701c0403000504100420720104118040304a07e034030003048080110f540c11483e02c059460300701410750003e2004d280da0000e01000b4055030741c1164070300d0349940c607015032000a03039921121351400910700c070b40110001d000c502c049026500000005003c3d41c604042d1704807180401c4d84103101c08c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241007194 1106 241006088 241006109
    0x1120c170108010c0509090a150603020306180103050601060c06060503010c081905010e0c07050f07140310020c0c04090221060711030309070513240e0705030708040f0213090b01 78
    0x50400900d07240d62f0040c0c49090160802c41c0100c4000003101000313800c2001440801c0006c243c2c00e04403401400c3c0103081d0804c41c90124080d010310361102e5495441c2520b2441c980c3c0c1c1101480e44618401140d035a01c800c8200325004c1210800c0c02010300721220303400000c0c0c1c4018144001c1c40814081c101310384100d007048591620b4055560400543d080034070100c0e980900701040070039542d40e8070440c1075003040010024aa031b601c1c42c0f140748501c566264541300d001c0d0b45034601010142000c0958030309051100b20740d02540c410050f0b440380c001880b2010714032140d010200540e40209660409000300070318003010003414084170350741222208d96600b907140c1c2c81e00074004003034003c0306506404280c051a0149440c120003004006106100003041004119030348240c040c1d85c0f0507800040b416140322140007080d0318020204400e680e00e481c1044603000d0160208004d4120b801d040b96 = true := by decide +kernel

theorem cover : BRFrame.Cov 240827338 241007194 := by
  have h0 := BRFrame.cov_init 240827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 240827338 ≤ n) (h2 : n < 241007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
