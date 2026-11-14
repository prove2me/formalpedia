-- Prove2me | solution 1 for FullForesight.Randomized.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:53:27.874083+00:00
-- url     : https://prove2.me/submissions/8549c159-688e-43a8-bdff-9df5bd14e11b

import Mathlib
import Definitions.Def_FullForesight_Randomized_IntervalSelection
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_consecutiveIntervalReduction

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

/-- An interval-selection instance of the mission, as an `IntervalInstance` of the source
development. -/
def toInterval {N : ℕ} {ℓ r p : Fin (N + 1) → ℝ} (h : IsIntervalInstance ℓ r p) :
    IntervalInstance N where
  left := ℓ
  right := r
  prob := p
  left_nonneg i := (h.1 i).1
  left_le_right i := (h.1 i).2
  prob_nonneg := h.2.1
  prob_sum := h.2.2

theorem isIntervalInstance {N : ℕ} (I : IntervalInstance N) :
    IsIntervalInstance I.left I.right I.prob :=
  ⟨fun i => ⟨I.left_nonneg i, I.left_le_right i⟩, I.prob_nonneg, I.prob_sum⟩

theorem gap_eq {N : ℕ} (I : IntervalInstance N) :
    gap I.left I.right I.prob = I.adaptivityGap := rfl

theorem equalizing_iff {N : ℕ} (I : IntervalInstance N) :
    IsEqualizing I.left I.right I.prob ↔ I.IsEqualizing := Iff.rfl

theorem noninc_iff {N : ℕ} (I : IntervalInstance N) :
    IsNonincConsecutive I.left I.right ↔ I.IsNonincreasingConsecutive := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, fun i => h2 (Fin.castSucc_lt_succ).le, h3 _⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have hanti : Antitone (fun i => I.right i - I.left i) := Fin.antitone_iff_succ_le.2 h2
    exact ⟨h0, h1, hanti, fun i => lt_of_lt_of_le h3 (hanti (Fin.le_last i))⟩

end FullForesight.Randomized.Bridge

open FullForesight.Randomized FullForesight.Randomized.Bridge in
theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p →
      IsNonincConsecutive ℓ r → IsEqualizing ℓ r p → α ≤ gap ℓ r p) :
    ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p → α ≤ gap ℓ r p := by
  intro N ℓ r p hinst
  exact ConsistentSubmodular.consecutiveIntervalReduction α hα.1 hα.2
    (fun M I hI hE => h M I.left I.right I.prob (isIntervalInstance I) ((noninc_iff I).2 hI) hE)
    N (toInterval hinst)
