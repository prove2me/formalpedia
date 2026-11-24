-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.one_mem_intGerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:55.355305+00:00
-- url     : https://prove2.me/submissions/8bb53b70-afb1-46ef-b1d5-1294344bde51

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate

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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C) :
    (1 : MvPowerSeries (WV I) C) ∈ IntGerm V t := by
  refine ⟨1, fun μ => ?_, ?_⟩
  · by_cases hμ : μ = 0
    · subst hμ
      simp [VF.Ge]
    · simp [VF.Ge, MvPowerSeries.coeff_one, hμ]
  · rw [← map_one (MvPowerSeries.C (σ := WV I) (R := C)), MvPowerSeries.subst_C]
end Formalism.L2.FormalSeriesBounds.RF
