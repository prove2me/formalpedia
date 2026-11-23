-- Prove2me | solution 1 for DensInertW.Sub.hf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:37.837699+00:00
-- url     : https://prove2.me/submissions/8284a0ca-006c-48b1-bec3-98880c76c95a

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
theorem _root_.solution (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (x y y' : Fin n → L) :
    hf q M x (y + y') = hf q M x y + hf q M x y' := by
  simp only [hf, Pi.add_apply, hadd, mul_add, Finset.sum_add_distrib]
end DensInertW.Sub
