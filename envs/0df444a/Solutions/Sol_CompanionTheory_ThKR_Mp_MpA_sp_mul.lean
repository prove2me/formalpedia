-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.sp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:37.959872+00:00
-- url     : https://prove2.me/submissions/ccb8adf1-402a-44e8-bb67-2a3f17d1cfda

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul


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
theorem _root_.solution {X : Type} [TopologicalSpace X] {a b : X → Sp l} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))
end CompanionTheory.ThKR.Mp.MpA
