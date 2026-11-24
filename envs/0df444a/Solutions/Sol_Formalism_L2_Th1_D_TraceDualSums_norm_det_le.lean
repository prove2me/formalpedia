-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceDualSums.norm_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:45.405388+00:00
-- url     : https://prove2.me/submissions/86a94f6f-6bed-471e-858c-f93cc984b500

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums
namespace Formalism.L2.Th1.D.TraceDualSums
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _)
end Formalism.L2.Th1.D.TraceDualSums
