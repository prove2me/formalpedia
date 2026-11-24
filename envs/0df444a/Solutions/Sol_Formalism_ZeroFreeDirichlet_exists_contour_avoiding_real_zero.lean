-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exists_contour_avoiding_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:10.842294+00:00
-- url     : https://prove2.me/submissions/a7cd1d1c-7885-427b-be0f-2f1408634204

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsContourAvoidingRealZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by
  have hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L))) := by
    field_simp
    ring
  have he : 0 < c₁ / (24 * L) := by positivity
  rcases Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩
  · exact ⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩
  have hBs : ∀ β' ∈ B, β' = β := fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ
  by_cases h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|
  · exact ⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩
  · refine ⟨_, Or.inr rfl, fun β' hβ' => ?_⟩
    rw [hBs β' hβ']
    push_neg at h
    have tri := abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))
    rw [hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β] at tri
    linarith
end Formalism.ZeroFreeDirichlet
