-- Prove2me | solution 1 for DensInertW.Sub.hf_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:44.772293+00:00
-- url     : https://prove2.me/submissions/bb46764c-0245-40fc-911a-4d4b07e70763

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
theorem _root_.solution (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, mul_pow]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end DensInertW.Sub
