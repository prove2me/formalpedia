-- Prove2me | solution 1 for DensInertW.Sub.not_mem_perp_aniso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:53.228774+00:00
-- url     : https://prove2.me/submissions/93c32f64-1adc-4301-b8ae-af1cb51b5aea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (W : Submodule L (Fin n → L)) (e : Fin n → L)
    (hee : hf q M e e ≠ 0) : e ∉ W ⊓ LinearMap.ker (hfL q M e) :=
  fun h => hee (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h).2)
end DensInertW.Sub
