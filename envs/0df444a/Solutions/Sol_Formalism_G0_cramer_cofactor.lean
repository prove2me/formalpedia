-- Prove2me | solution 1 for Formalism.G0.cramer_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:07.259236+00:00
-- url     : https://prove2.me/submissions/0d98c835-0981-42e1-9eaf-07b7fe9b356e

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_CramerCofactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Matrix
namespace Formalism.G0
theorem _root_.solution : CramerCofactor := by
  intro R _ r T σ a
  have h : T.adjugate *ᵥ (T *ᵥ σ) = T.det • σ := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun h a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
  rw [mul_comm, ← h2]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
end Formalism.G0
