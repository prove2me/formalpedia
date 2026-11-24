-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.isUnit_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:19.83493+00:00
-- url     : https://prove2.me/submissions/216e7202-36a1-487c-8b40-cfa8facb2edd

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_ph


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
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (S : Matrix l l ℝ) (t : ℝ) : IsUnit (UU S t) :=
  isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)
end CompanionTheory.ThKR.Mp
