-- Prove2me | solution 1 for Formalism.NG.torsLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:17.085372+00:00
-- url     : https://prove2.me/submissions/e7a06802-60f1-417c-ac62-36dff5f76772

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_lenKer


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
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatTorsLen := by
  classical
  intro O _ _ _ d _ δ
  have hmap : DistribSMul.toLinearMap O (d → KO O) (δ * δ) =
      matQ O (Matrix.diagonal fun _ : d => δ * δ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [matQ, relMap, Matrix.diagonal_apply, ite_smul]
  rw [hmap, lenKer, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    AddValuation.map_pow, AddValuation.map_mul, two_mul, nsmul_eq_mul]
end Formalism.NG
