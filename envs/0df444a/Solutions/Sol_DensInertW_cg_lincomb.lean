-- Prove2me | solution 1 for DensInertW.cg_lincomb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:29.224838+00:00
-- url     : https://prove2.me/submissions/0b6959a9-16b8-40f0-a203-3120b2acd3e9

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
theorem _root_.solution {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (g : Fin m → L) :
    ∑ i, g i • cgComb Q X i = ∑ k, (Matrix.vecMul g Q) k • X k := by
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm
end DensInertW
