-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.iso_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:56.739338+00:00
-- url     : https://prove2.me/submissions/a7cdf7d1-1493-468d-a3bd-52a1abf9024f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_ph
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_dil
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_fouInv
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
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    Iso (big Ai B C c) :=
  (iso_ph _).mul ((iso_dil h hc).mul (iso_fou.mul ((iso_ph _).mul iso_fouInv)))
end CompanionTheory.ThKR.LL
