-- Prove2me | solution 1 for DensInertW.cg_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:06.312805+00:00
-- url     : https://prove2.me/submissions/fa03dc11-7cc1-4142-b7ca-701925e44acb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
import Theorems.Thm_DensInertW_cg_lincomb

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
    (X : Fin m → Fin n → L) (hQ : Q.det ≠ 0) (hX : LinearIndependent L X) :
    LinearIndependent L (cgComb Q X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  rw [cg_lincomb] at hg
  have h0 : Matrix.vecMul g Q = 0 := funext (hX _ hg)
  have hg' : g = Matrix.vecMul (Matrix.vecMul g Q) Q⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hQ.isUnit, Matrix.vecMul_one]
  rw [hg', h0, Matrix.zero_vecMul, Pi.zero_apply]
end DensInertW
