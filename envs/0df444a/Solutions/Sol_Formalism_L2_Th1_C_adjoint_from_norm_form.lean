-- Prove2me | solution 1 for Formalism.L2.Th1.C.adjoint_from_norm_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:07:13.777198+00:00
-- url     : https://prove2.me/submissions/1f8b7a32-da9c-46c4-8be4-aab39274f53f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ArithmeticFrobeniusAction
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_symm
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_trans
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_sub
import Theorems.Thm_Formalism_L2_Th1_C_Calc_phNorm_pt
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Pts Calc
namespace Formalism.L2.Th1.C
theorem _root_.solution : AdjFromNorm := by
  intro K _ _ R l linv ph a b hFr ha hEa hEa' hEb hN hZ σ x y hx hy
  obtain ⟨h, hF, -⟩ := hFr
  have hy' : IsPt R (fmul l linv a⁻¹ y) := isPt_fmul h hEa' hy
  have e1 : fmul l linv a (fmul l linv a⁻¹ y) = y := by
    rw [fmul_fmul h a a⁻¹ hy.1, mul_inv_cancel₀ ha, fmul_one h hy.1]
  have e2 : fmul l linv (a * b) (fmul l linv a⁻¹ y) = fmul l linv b y := by
    rw [fmul_fmul h (a * b) a⁻¹ hy.1, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  have c1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a (fmul l linv a⁻¹ y)))
      ((a * b) • be0 l linv ph x (fmul l linv a⁻¹ y)) := by
    unfold be0
    rw [← fmul_fadd h a hx.1 hy'.1, smul_sub, smul_sub]
    exact cong_sub (cong_sub (phNorm_pt h hN (isPt_fadd h hF hx hy')) (phNorm_pt h hN hx))
      (phNorm_pt h hN hy')
  have c2 := cong_symm (hZ σ x _ hx hy')
  rw [e1] at c1
  rw [e2] at c2
  exact cong_trans c1 c2
end Formalism.L2.Th1.C
