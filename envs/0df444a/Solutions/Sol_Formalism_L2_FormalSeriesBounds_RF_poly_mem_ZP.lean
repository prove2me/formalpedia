-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.poly_mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:39.693205+00:00
-- url     : https://prove2.me/submissions/6134e367-09c1-4640-884b-d3e95a3423c4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rename_mem_ZP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_minorK_mem_ZP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_minorMonomial_mem_ZP
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
theorem _root_.solution {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (b : GlobalTheory d) : b.poly X F ∈ ZP C _ := by
  unfold GlobalTheory.poly
  cases b with
  | bi g a i y =>
    exact mul_mem (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
      (pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _)
  | ch g a u => exact pow_mem (rename_mem_ZP _ (minorK_mem_ZP _ _ _)) _
  | mon g e N => exact prod_mem fun a _ => rename_mem_ZP _ (minorMonomial_mem_ZP _ _ _)
end Formalism.L2.FormalSeriesBounds.RF
