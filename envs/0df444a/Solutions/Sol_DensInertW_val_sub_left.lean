-- Prove2me | solution 1 for DensInertW.val_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:54.870162+00:00
-- url     : https://prove2.me/submissions/b6eb7fc2-a836-4a55-a6fb-72db8f54dec3

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
theorem _root_.solution (x x' y : Fin n → L) : hf q M (x - x') y = hf q M x y - hf q M x' y := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end DensInertW
