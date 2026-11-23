-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.exists_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:44.509322+00:00
-- url     : https://prove2.me/submissions/07bc4a84-e3bb-4c09-a27b-e0fefbe2098a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (Y : Submodule ℂ H)
    [FiniteDimensional ℂ Y] (T : H →L[ℂ] H) (hT : ∀ y ∈ Y, T y ∈ Y) (hi : ∀ y ∈ Y, T y = 0 → y = 0) :
    ∀ v ∈ Y, ∃ u, T u = v := by
  intro v hv
  let L : Y →ₗ[ℂ] Y := (T : H →ₗ[ℂ] H).restrict hT
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hi y y.2 (congrArg Subtype.val hy))
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hL ⟨v, hv⟩
  exact ⟨u, congrArg Subtype.val hu⟩
end CompanionTheory.D.gk.admitted.Gard
