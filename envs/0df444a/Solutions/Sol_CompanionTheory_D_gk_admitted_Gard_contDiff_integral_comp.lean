-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_integral_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:30.824026+00:00
-- url     : https://prove2.me/submissions/61579d33-2862-4c02-a50d-328750b72674

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_continuous_iter_partial
import Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_of_iteratedFDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open CompanionTheory.D.gk.admitted.Gard
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a))
    (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp
  have h : Continuous fun p : P × α => (p.1, q p.2) := continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iter_partial Φ hΦ k).comp h
end CompanionTheory.D.gk.admitted.Gard
