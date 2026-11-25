-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.SmOn.exists_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:24.462826+00:00
-- url     : https://prove2.me/submissions/cd0524dd-a69d-4975-91b3-401ef126ea83

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
namespace CompanionTheory.D.Upq.Sm
namespace SmOn
theorem _root_.solution {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f : E → V}
    (hf : SmOn A f) (hA : IsClosed A) : ∃ F : E → V, ContDiff ℝ ∞ F ∧ ∀ a ∈ A, F a = f a := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
    (t := fun a => {v | a ∈ A → v = f a})
    (fun a v hv w hw s t _ _ hst ha => by rw [hv ha, hw ha, ← add_smul, hst, one_smul])
    (fun a => by
      by_cases ha : a ∈ A
      · obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
        exact ⟨U, hU.mem_nhds haU, F, hF.contMDiffOn, fun y hy hyA => (hfF y hy hyA).symm⟩
      · exact ⟨Aᶜ, hA.isOpen_compl.mem_nhds ha, fun _ => 0, contMDiffOn_const,
          fun y hy hyA => absurd hyA hy⟩)
  exact ⟨F, F.contMDiff.contDiff, fun a ha => hF a ha⟩
end SmOn
end CompanionTheory.D.Upq.Sm
