-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:55.015568+00:00
-- url     : https://prove2.me/submissions/c6da0423-c8f4-4409-8d1f-6fe52576cdfd

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution {γ : Type*} (s : Finset γ) (w V X : γ → ℝ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hw : ∀ T ∈ s, 0 ≤ w T) (hsum : ∑ T ∈ s, w T = 1) (hV0 : ∀ T ∈ s, 0 ≤ V T)
    (hV : ∑ T ∈ s, w T * V T ≤ 2 / 3 * r) (hX0 : ∀ T ∈ s, 0 ≤ X T)
    (hXs : ∑ T ∈ s, w T * X T ≤ M) :
    ∃ T ∈ s, V T < r ∧ X T ≤ 4 * M := by
  by_contra hcon
  push Not at hcon
  have hG : ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ 2 / 3 := by
    have hle : ∀ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ w T * V T / r := by
      intro T hT
      rw [Finset.mem_filter] at hT
      have hVT : r ≤ V T := by
        by_contra h
        push Not at h
        exact hT.2 (hcon T hT.1 h)
      rw [le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left hVT (hw T hT.1)
    calc ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T
        ≤ ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T / r := Finset.sum_le_sum hle
      _ = (∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T) / r := by rw [Finset.sum_div]
      _ ≤ (∑ T ∈ s, w T * V T) / r := by
          apply div_le_div_of_nonneg_right _ hr.le
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro T hT _
          exact mul_nonneg (hw T hT) (hV0 T hT)
      _ ≤ (2 / 3 * r) / r := div_le_div_of_nonneg_right hV hr.le
      _ = 2 / 3 := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun T => 4 * M < X T) w
  have hB : 1 / 3 ≤ ∑ T ∈ s.filter (fun T => 4 * M < X T), w T := by linarith
  obtain ⟨T0, hT0, hwT0⟩ : ∃ T ∈ s.filter (fun T => 4 * M < X T), 0 < w T := by
    by_contra h
    push Not at h
    have : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T ≤ 0 := Finset.sum_nonpos h
    linarith
  have hlt : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * (4 * M) <
      ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T := by
    apply Finset.sum_lt_sum
    · intro T hT
      rw [Finset.mem_filter] at hT
      exact mul_le_mul_of_nonneg_left hT.2.le (hw T hT.1)
    · refine ⟨T0, hT0, ?_⟩
      rw [Finset.mem_filter] at hT0
      exact mul_lt_mul_of_pos_left hT0.2 hwT0
  have hsub : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T ≤ ∑ T ∈ s, w T * X T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro T hT _
    exact mul_nonneg (hw T hT) (hX0 T hT)
  rw [← Finset.sum_mul] at hlt
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hM]
end Formalism.RankGapBounds.LocalQuadraticParts
