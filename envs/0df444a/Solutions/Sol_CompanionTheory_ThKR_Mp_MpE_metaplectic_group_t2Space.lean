-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.metaplectic_group_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:45.791408+00:00
-- url     : https://prove2.me/submissions/6a70247d-838d-4a25-b268-2a61bd8edc7e

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_isInducing_F
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_sch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE
open CompanionTheory.ThKR.Mp.MpE
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution : T2Space (G l) := by
  refine T2Space.of_injective_continuous (f := fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)))
    ?_ isInducing_F.continuous
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have hu : om g = om h := LinearIsometryEquiv.ext fun f => congrFun h2 f
  have hU : omS g = omS h := ContinuousLinearMap.ext fun f => by
    apply injective_toLp 2 volume
    show schwartzToL2 l (omS g f) = schwartzToL2 l (omS h f)
    rw [← om_sch, ← om_sch, hu]
  exact Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext hu (Units.ext hU)))
end CompanionTheory.ThKR.Mp.MpE
