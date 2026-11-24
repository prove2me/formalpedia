-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.integral_mem_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:19.607231+00:00
-- url     : https://prove2.me/submissions/f9938d6c-8467-4d08-a3c3-047994a7f77b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure α} (S : Submodule ℂ V)
    (hS : IsClosed (S : Set V)) {f : α → V} (hf : ∀ a, f a ∈ S) : ∫ a, f a ∂μ ∈ S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  have := S.subtypeₗᵢ.integral_comp_comm (μ := μ) (fun a => (⟨f a, hf a⟩ : S))
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] at this
  rw [this]
  exact Subtype.property _
end CompanionTheory.D.Upq.Sm
