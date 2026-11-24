-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.one_mem_IntGerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:04.801698+00:00
-- url     : https://prove2.me/submissions/d4b38679-fe6a-4943-88ff-3c5ad1723ef9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
theorem _root_.solution {V : VF C} {I : Fin 2 → Type} (t : ∀ g, I g → MvPowerSeries (I g) C) :
    (1 : MvPowerSeries (WV I) C) ∈ IntGerm V t := by
  refine ⟨1, fun μ => ?_, (subst_one' _).symm⟩
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact VF.Ge.one (V := V)
  · exact VF.Ge.zero (V := V) 0
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
