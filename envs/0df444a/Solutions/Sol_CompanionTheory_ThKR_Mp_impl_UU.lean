-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.impl_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:21.777409+00:00
-- url     : https://prove2.me/submissions/5a638820-6bc5-464b-a91b-a0d4c634d985

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_first_diag
import Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_upper
import Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_lower
import Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_second_diag
import Theorems.Thm_CompanionTheory_ThKR_Mp_intw_UU
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_ph
import Theorems.Thm_CompanionTheory_ThKR_LL_pPart_mulVec
import Theorems.Thm_CompanionTheory_ThKR_LL_qPart_mulVec
import Theorems.Thm_CompanionTheory_ThKR_LL_rhoFun_eq


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
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) :
    Impl (fun w => nn S t *ᵥ w) (UU S t).toLinearMap :=
  ⟨fun f => (iso_fou.mul ((iso_ph _).mul iso_fouInv)) f, fun w f g hg => by
    have := intw_UU hS t (pPart w) (qPart w) f g hg
    rw [rhoFun_eq, pPart_mulVec, qPart_mulVec, metaplectic_unipotent_block_first_diag,
      metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metaplectic_unipotent_block_second_diag]
    simpa using this⟩
end CompanionTheory.ThKR.Mp
