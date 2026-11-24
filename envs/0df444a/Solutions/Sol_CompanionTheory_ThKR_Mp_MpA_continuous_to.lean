-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.continuous_to
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:29.222398+00:00
-- url     : https://prove2.me/submissions/27ab0188-34cb-47a4-80d3-284d57ccd40f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA
namespace CompanionTheory.ThKR.Mp.MpA
theorem _root_.solution {X : Type} [TopologicalSpace X] {F : X → G l} (h1 : Continuous fun x => pr (F x))
    (h2 : ∀ f, Continuous fun x => om (F x) f) : Continuous F :=
  continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))
end CompanionTheory.ThKR.Mp.MpA
