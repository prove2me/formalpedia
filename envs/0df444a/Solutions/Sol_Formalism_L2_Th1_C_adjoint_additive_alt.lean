-- Prove2me | solution 1 for Formalism.L2.Th1.C.adjoint_additive_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:05.117705+00:00
-- url     : https://prove2.me/submissions/098d31fe-c88f-44f6-ae5e-534a7fb1c0fe

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
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cong_add
import Theorems.Thm_Formalism_L2_Th1_C_Pts_addDefect_comm
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_add
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
theorem _root_.solution : AdjAdd := by
  intro K _ _ R l linv ph a b a' b' hFr hF1 hEa hEb hEa' hEb' hA hA' σ x y hx hy
  obtain ⟨h, hF, -⟩ := hFr
  rw [fmul_add h a a' hx.1, fmul_add h b b' hy.1]
  have c1 := hF1 σ _ _ y (isPt_fmul h hEa hx) (isPt_fmul h hEa' hx) hy
  have c2 := cong_add (hA σ x y hx hy) (hA' σ x y hx hy)
  have c3 := hF1 σ _ _ x (isPt_fmul h hEb hy) (isPt_fmul h hEb' hy) hx
  rw [addDefect_comm ph _ x, addDefect_comm ph _ x, addDefect_comm ph _ x] at c3
  exact cong_trans c1 (cong_trans c2 (cong_symm c3))
end Formalism.L2.Th1.C
