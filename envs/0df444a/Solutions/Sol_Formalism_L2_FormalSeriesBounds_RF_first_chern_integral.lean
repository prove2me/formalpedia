-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.first_chern_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:45.615295+00:00
-- url     : https://prove2.me/submissions/c0b6deb4-444c-480d-9e7d-59b864bcc644

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coeff_mem_of_OP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_aeval_mem_OP
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkProd_mem_ZP


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
theorem _root_.solution : IsotropicToStdSubstIntegral := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hO m
  apply coeff_mem_of_OP
  unfold subG
  refine aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)
  refine sum_mem fun col _ => mul_mem ?_ ?_
  · exact RingHom.mem_range.2 ⟨MvPolynomial.C ⟨_, hO _ _ _ _⟩, by rw [MvPolynomial.map_C]; rfl⟩
  · exact RingHom.mem_range.2 ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩
end Formalism.L2.FormalSeriesBounds.RF
