-- Prove2me | solution 1 for Formalism.L2.DIV.pairingRational_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:03.592781+00:00
-- url     : https://prove2.me/submissions/bbabd209-fabf-45eb-9e13-003d1c831e16

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_int_mem
import Theorems.Thm_Formalism_L2_DIV_fk_blockAct_mem
import Theorems.Thm_Formalism_L2_DIV_fk_fock_mem
import Theorems.Thm_Formalism_L2_DIV_fk_extNorm_mem
import Theorems.Thm_Formalism_L2_DIV_fk_gramTw_mem
import Theorems.Thm_Formalism_L2_DIV_bVV_coe
import Theorems.Thm_Formalism_L2_DIV_bVVfun_int
import Theorems.Thm_Formalism_L2_DIV_fockL_apply
import Theorems.Thm_Formalism_L2_DIV_pairK_apply
import Theorems.Thm_Formalism_L2_DIV_pairP_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : PairRat := by
  intro K _ _ ι _ n lam K0 G hG i j
  obtain ⟨Pi, hPi⟩ := bVVfun_int K lam i
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  rw [pairK_apply, pairP_apply, bVV_coe, bVV_coe, fockL_apply, hPi, hPj]
  refine mul_mem (div_mem (fk_gramTw_mem K0 lam G hG) (fk_extNorm_mem K0 lam)) (fk_fock_mem K0 _ ?_)
  exact fk_blockAct_mem K0 _ (fun τ a b => hG τ b a) (fk_int_mem K0 _)
end Formalism.L2.DIV
