-- Prove2me | solution 1 for DensInertW.cg_comb_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:27.851492+00:00
-- url     : https://prove2.me/submissions/e53d8f5e-545a-47d8-af9b-d9016cf987be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution {L : Type} [Field L] {m n : ℕ} (P Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) : cgComb P (cgComb Q X) = cgComb (P * Q) X := by
  funext i
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm
end DensInertW
