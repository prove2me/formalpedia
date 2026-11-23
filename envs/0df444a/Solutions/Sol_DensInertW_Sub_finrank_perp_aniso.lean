-- Prove2me | solution 1 for DensInertW.Sub.finrank_perp_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:08.073921+00:00
-- url     : https://prove2.me/submissions/0e9e9ecd-7024-4433-8ae2-f67758b68076

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_finrank_inf_ker_add_one

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
theorem _root_.solution (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker (hfL q M e)) + 1 = finrank L ↥W :=
  finrank_inf_ker_add_one W _ e he hee
end DensInertW.Sub
