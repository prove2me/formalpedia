-- Prove2me | solution 1 for DensInertW.val_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:05.139473+00:00
-- url     : https://prove2.me/submissions/645adcf8-1c5b-468b-a68a-31df16453611

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW
theorem _root_.solution (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
end DensInertW
