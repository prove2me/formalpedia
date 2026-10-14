-- Prove2me | solution 1 for Freiman.gap_upper_checks_21_24
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T20:46:31.972069+00:00
-- url     : https://prove2.me/submissions/3f70d730-0a2c-4b6c-9ed7-24ee47eed367

import Definitions.Def_Freiman_gapCertificateData

deriving instance DecidableEq for Freiman.GapMode

namespace GapChecksAux

open Freiman

/-- The witness `k` in `gapWordContains` may be taken at most `|s.word|`: beyond
that the drop is empty, forcing `w = []`, which `k = 0` already witnesses. -/
lemma gapWordContains_iff (s : GapState) (w : List ℕ+) :
    gapWordContains s w ↔
      ∃ k ∈ List.range (s.word.length + 1), (s.word.drop k).take w.length = w := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hle : k ≤ s.word.length
    · exact ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hle), hk⟩
    · rw [List.drop_eq_nil_of_le (le_of_lt (not_le.1 hle))] at hk
      simp only [List.take_nil] at hk
      exact ⟨0, List.mem_range.2 (Nat.succ_pos _), by simp [← hk]⟩
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- In `gapAlignedContains` the centre equation pins `k ≤ s.centre`. -/
lemma gapAlignedContains_iff (s v : GapState) :
    gapAlignedContains s v ↔
      ∃ k ∈ List.range (s.centre + 1),
        (s.word.drop k).take v.word.length = v.word ∧ s.centre = k + v.centre := by
  constructor
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, List.mem_range.2 (Nat.lt_succ_of_le (by omega)), h1, h2⟩
  · rintro ⟨k, _, h⟩
    exact ⟨k, h⟩

instance instDecWordContains (s : GapState) (w : List ℕ+) :
    Decidable (gapWordContains s w) :=
  decidable_of_iff _ (gapWordContains_iff s w).symm

instance instDecAlignedContains (s v : GapState) :
    Decidable (gapAlignedContains s v) :=
  decidable_of_iff _ (gapAlignedContains_iff s v).symm

instance instDecBelow : (mode : GapMode) → (x : ℚ) → Decidable (gapBelowCheck mode x)
  | .forbidden, _ => inferInstanceAs (Decidable False)
  | .upper c, x => inferInstanceAs (Decidable (x ≤ c))
  | .reduction, x => inferInstanceAs (Decidable (x ≤ 2263914769 / 500000000))

instance instDecLeaf (lower upper : List GapRow) (mode : GapMode) :
    (s : GapState) → (r : GapReason) → Decidable (gapLeafCheck lower upper mode s r)
  | s, .above j =>
      inferInstanceAs (Decidable
        (j < s.word.length ∧ 4527829567 / 1000000000 ≤ gapCylinderLower s.word j))
  | s, .below =>
      inferInstanceAs (Decidable (gapBelowCheck mode (gapCylinderUpper s.word s.centre)))
  | s, .prior n =>
      inferInstanceAs (Decidable
        (n < lower.length ∧ (lower[n]!).state.word ≠ [] ∧
          (gapWordContains s (lower[n]!).state.word ∨
            gapWordContains s (lower[n]!).state.word.reverse)))
  | s, .upperRow n =>
      inferInstanceAs (Decidable
        (n < upper.length ∧ (upper[n]!).state.centre < (upper[n]!).state.word.length ∧
          gapBelowCheck mode (upper[n]!).bound ∧
          (gapAlignedContains s (upper[n]!).state ∨
            gapAlignedContains s (gapReverse (upper[n]!).state))))
  | s, .terminal =>
      inferInstanceAs (Decidable
        (mode = .reduction ∧
          (gapAlignedContains s gapSeedA ∨ gapAlignedContains s (gapReverse gapSeedA) ∨
            gapAlignedContains s gapSeedB ∨ gapAlignedContains s (gapReverse gapSeedB))))

instance instDecChecks (lower upper : List GapRow) (mode : GapMode) (t : GapTree) :
    Decidable (gapChecks lower upper mode t) :=
  inferInstanceAs (Decidable (∀ sr ∈ gapLeaves t, gapLeafCheck lower upper mode sr.1 sr.2))

end GapChecksAux

open GapChecksAux
open Freiman

theorem solution : ∀ n : ℕ, 0 ≤ n → n < 4 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  intro n _ h; interval_cases n <;> decide +kernel
