-- Prove2me | solution 1 for Formalism.MainStatements.RankOne.KD.int_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:37:25.650273+00:00
-- url     : https://prove2.me/submissions/e6608f38-bd67-44f1-bfd3-bc2b7a1dcee1

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


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
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
namespace Formalism.MainStatements.RankOne.KD
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure Γ) [IsFiniteMeasure μ] (p : C(Γ, ℝ))
    {F : Γ → V} (hF : Continuous F) : Integrable (fun x => p x • F x) μ :=
  (p.continuous.smul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end Formalism.MainStatements.RankOne.KD
