-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.norm_one_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:04.448195+00:00
-- url     : https://prove2.me/submissions/7cf64238-f528-4fda-8619-5d8ca7b8816d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rename_mem_ZP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coeff_mem_of_ZP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkProd_mem_ZP
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution : NormOneIntegral := by
  intro C _ V d _ T r cc a Orb _ tau J _ X F Z ga n L pl _ O m
  exact coeff_mem_of_ZP (rename_mem_ZP _ (blkProd_mem_ZP _ _ _ _ _)) O m
end Formalism.L2.FormalSeriesBounds.RF
