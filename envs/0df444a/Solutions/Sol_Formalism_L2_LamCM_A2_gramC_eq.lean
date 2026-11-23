-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.gramC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.269612+00:00
-- url     : https://prove2.me/submissions/36c92dee-c5ac-4c62-a712-604e2706d4b2

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by
  ext i j
  simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
end Formalism.L2.LamCM.A2
