-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.zero_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:58.644808+00:00
-- url     : https://prove2.me/submissions/471dd878-a013-4d80-8e01-99753b8e065d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_mvExp_zero
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_one_mem_IntGerm

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {V : VF C} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (g : Fin 2)
    (t : ∀ g, I g → MvPowerSeries (I g) C) :
    upG g (mvExp (∑ x : I g, (0 : C) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
      IntGerm V t := by
  simp only [zero_smul, Finset.sum_const_zero, mvExp_zero]
  unfold upG
  rw [subst_one']
  exact one_mem_IntGerm t
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
