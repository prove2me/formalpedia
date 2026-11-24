-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.span_range_eq_span_range_of_eq_mul_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:35.845543+00:00
-- url     : https://prove2.me/submissions/cae69a68-9639-45a6-bbef-d3f66dfa9795

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution {A : Type*} [CommRing A] {n : ℕ}
    (y z c : Fin n → A) (hc : ∀ i, IsUnit (c i)) (hz : ∀ i, z i = y i * c i) :
    Ideal.span (Set.range z) = Ideal.span (Set.range y) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    rw [SetLike.mem_coe, hz i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hc i
    have hy : y i = z i * (↑v⁻¹ : A) := by
      rw [hz i, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [SetLike.mem_coe, hy]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
