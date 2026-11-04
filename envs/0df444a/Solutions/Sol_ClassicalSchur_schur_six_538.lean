-- Prove2me | solution 1 for ClassicalSchur.schur_six_538
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-11-04T05:40:16.063137+00:00
-- url     : https://prove2.me/submissions/23abfa29-636c-4844-a75c-fdb043b2ce2f

/-
Copyright (c) 2026 Adam McKenna.
Released under the Creative Commons Attribution 4.0 International license
(CC-BY-4.0) as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# A Schur 6-colouring of `[1, 538]`

The main theorem is `schur_six_538`. Its statement uses Lean core only and no
definition of this file: there is `c : Nat → Fin 6` such that no `x`, `y`,
`x + y` in `[1, 538]` have one colour, `x = y` included.

The numeral `word538` is the word of the colouring, in base ten: its `x`-th digit
from the left is the colour of `x`. The theorems `colouring538_val` and
`colouring538_no_mono` state the result for the colouring of this word.

`check` is a Bool checker with one bit mask for each colour, and `check_sound` is
its soundness theorem. Kernel reduction evaluates `check word538 538`
(`check_word538`). This file imports Lean core only and uses no `native_decide`.
-/

namespace SchurWitness538

/-- The word of the colouring. The `x`-th decimal digit from the left is the
colour of `x`. -/
def word538 : Nat := 1214532151415455221412131223442151413435231512441225413135322515141312233421314255522313123452214421513353131415524432213122432215151435332141216142453215141545512141216362141216145641516161626666141316564651614166626616161626666166616666666666666636616166666666666666666666666666666666666366666661666666161666666261666666266616666564656131416666261616156465416121412636121412156451415123542416121412335141515122342213122344255141313523151244122543213132255524131243322131415152235313145221442151325343141512443221312141225545141512354121

/-- The letter of the point `x` in a word `W` of `n` decimal digits: the `x`-th
digit from the left. -/
def letterAt (W n x : Nat) : Nat := W / 10 ^ (n - x) % 10

/-- The bit mask of the class of colour `c`: bit `i` is set for each `i` with
`1 ≤ i ≤ m` and `f i = c`. -/
def classMask (f : Nat → Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => classMask f c m ||| (bif f (m + 1) == c then 1 <<< (m + 1) else 0)

/-- `noSum M m` checks each `x` with `1 ≤ x ≤ m`: if bit `x` of `M` is set, then
`M` and `M` shifted left by `x` have no common bit. -/
def noSum (M : Nat) : Nat → Bool
  | 0 => true
  | m + 1 =>
    (!M.testBit (m + 1) || (M &&& (M <<< (m + 1))) == 0) && noSum M m

/-- `lettersInRange f m` checks `1 ≤ f x ≤ 6` for each `x` with `1 ≤ x ≤ m`. -/
def lettersInRange (f : Nat → Nat) : Nat → Bool
  | 0 => true
  | m + 1 => (Nat.ble 1 (f (m + 1)) && Nat.ble (f (m + 1)) 6) && lettersInRange f m

/-- The checker: each letter of the word `W` of length `n` is in `1, …, 6`, and
no colour class has `x`, `y`, `x + y` in it. -/
def check (W n : Nat) : Bool :=
  lettersInRange (letterAt W n) n &&
    [1, 2, 3, 4, 5, 6].all fun c => noSum (classMask (letterAt W n) c n) n

/-- A point of the colour `c` has its bit set in the mask of `c`. -/
theorem testBit_classMask {f : Nat → Nat} {c m i : Nat} (hi1 : 1 ≤ i) (him : i ≤ m)
    (hc : f i = c) : (classMask f c m).testBit i = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [classMask, Nat.testBit_or, Bool.or_eq_true]
    by_cases h : i ≤ m
    · exact Or.inl (ih h)
    · have hi : i = m + 1 := by omega
      subst hi
      refine Or.inr ?_
      simp [hc, Nat.testBit_shiftLeft]

/-- Soundness of `noSum`. -/
theorem noSum_spec {M m x : Nat} (h : noSum M m = true) (hx1 : 1 ≤ x) (hxm : x ≤ m)
    (hbit : M.testBit x = true) : (M &&& (M <<< x)) = 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [noSum, Bool.and_eq_true] at h
    by_cases hx : x ≤ m
    · exact ih h.2 hx
    · have hx' : x = m + 1 := by omega
      subst hx'
      simpa [hbit] using h.1

/-- A mask `M` with `M &&& (M <<< x) = 0` has no `y` with bits `y` and `x + y`
both set. -/
theorem not_both_of_land_eq_zero {M x y : Nat} (h : (M &&& (M <<< x)) = 0)
    (hy : M.testBit y = true) (hxy : M.testBit (x + y) = true) : False := by
  have hb := congrArg (fun K => Nat.testBit K (x + y)) h
  simp [Nat.testBit_and, Nat.testBit_shiftLeft, hy, hxy] at hb

/-- Soundness of `lettersInRange`. -/
theorem lettersInRange_spec {f : Nat → Nat} {m x : Nat} (h : lettersInRange f m = true)
    (hx1 : 1 ≤ x) (hxm : x ≤ m) : 1 ≤ f x ∧ f x ≤ 6 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [lettersInRange, Bool.and_eq_true, Bool.and_eq_true] at h
    by_cases hx : x ≤ m
    · exact ih h.2 hx
    · have hx' : x = m + 1 := by omega
      subst hx'
      exact ⟨Nat.le_of_ble_eq_true h.1.1, Nat.le_of_ble_eq_true h.1.2⟩

/-- Soundness of the checker: if `check W n = true`, then the letters of `W` are
in `1, …, 6` and the colouring of `[1, n]` by these letters has no monochromatic
`x + y = z` (`x = y` is allowed). -/
theorem check_sound {W n : Nat} (h : check W n = true) :
    (∀ x, 1 ≤ x → x ≤ n → 1 ≤ letterAt W n x ∧ letterAt W n x ≤ 6) ∧
    (∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ n →
      ¬ (letterAt W n x = letterAt W n y ∧ letterAt W n y = letterAt W n (x + y))) := by
  rw [check, Bool.and_eq_true, List.all_eq_true] at h
  have hrange : ∀ x, 1 ≤ x → x ≤ n → 1 ≤ letterAt W n x ∧ letterAt W n x ≤ 6 :=
    fun x hx1 hxn => lettersInRange_spec h.1 hx1 hxn
  refine ⟨hrange, ?_⟩
  intro x y hx1 hy1 hxyn hmono
  have hc1 := (hrange x hx1 (by omega)).1
  have hc6 := (hrange x hx1 (by omega)).2
  have hmem : letterAt W n x ∈ [1, 2, 3, 4, 5, 6] := by
    generalize letterAt W n x = c at hc1 hc6
    have hcases : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
    simpa using hcases
  have hsum := noSum_spec (h.2 _ hmem) hx1 (show x ≤ n by omega)
    (testBit_classMask hx1 (by omega) rfl)
  exact not_both_of_land_eq_zero hsum
    (testBit_classMask hy1 (by omega) hmono.1.symm)
    (testBit_classMask (by omega) hxyn (hmono.1.trans hmono.2).symm)

/-- Kernel evaluation of the checker on the word. -/
theorem check_word538 : check word538 538 = true := by
  decide +kernel

/-- The numeral `word538` has 538 decimal digits. -/
theorem word538_digits : 10 ^ 537 ≤ word538 ∧ word538 < 10 ^ 538 := by
  decide +kernel

/-- The colour of the point `x`: the `x`-th digit of `word538`. -/
def letter (x : Nat) : Nat := letterAt word538 538 x

/-- The digits of `word538` are in `1, …, 6` on `[1, 538]`, and no `x`, `y`,
`x + y` in `[1, 538]` have one digit (`x = y` is allowed). -/
theorem letter_schur :
    (∀ x, 1 ≤ x → x ≤ 538 → 1 ≤ letter x ∧ letter x ≤ 6) ∧
    (∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ 538 →
      ¬ (letter x = letter y ∧ letter y = letter (x + y))) :=
  check_sound check_word538

/-- The colouring with values in `Fin 6`: the digit `d` gives the colour `d - 1`. -/
def colouring538 (x : Nat) : Fin 6 := ⟨(letter x - 1) % 6, Nat.mod_lt _ (by decide)⟩

/-- On `[1, 538]`, the colour of `x` plus one is the `x`-th digit of `word538`. -/
theorem colouring538_val (x : Nat) (hx1 : 1 ≤ x) (hx2 : x ≤ 538) :
    (colouring538 x).val + 1 = letter x := by
  have hb := letter_schur.1 x hx1 hx2
  change (letter x - 1) % 6 + 1 = letter x
  omega

/-- `colouring538` has no monochromatic `x + y = z` on `[1, 538]` (`x = y` is
allowed). -/
theorem colouring538_no_mono (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x + y ≤ 538) :
    ¬ (colouring538 x = colouring538 y ∧ colouring538 y = colouring538 (x + y)) := by
  intro h
  have h1 := colouring538_val x hx (by omega)
  have h2 := colouring538_val y hy (by omega)
  have h3 := colouring538_val (x + y) (by omega) hxy
  rw [← h.1] at h2
  rw [← h.2, ← h.1] at h3
  exact letter_schur.2 x y hx hy hxy ⟨h1.symm.trans h2, h2.symm.trans h3⟩

/-- **Main theorem.** There is a colouring of the natural numbers with 6 colours
such that no `x`, `y`, `x + y` in `[1, 538]` have one colour. The case `x = y` is
included. The statement uses no definition of this file. -/
theorem schur_six_538 :
    ∃ c : Nat → Fin 6, ∀ x y : Nat, 1 ≤ x → 1 ≤ y → x + y ≤ 538 →
      ¬ (c x = c y ∧ c y = c (x + y)) :=
  ⟨colouring538, colouring538_no_mono⟩

end SchurWitness538

theorem solution :
    ∃ c : Nat → Fin 6, ∀ x y : Nat, 1 ≤ x → 1 ≤ y → x + y ≤ 538 →
      ¬ (c x = c y ∧ c y = c (x + y)) :=
  SchurWitness538.schur_six_538
