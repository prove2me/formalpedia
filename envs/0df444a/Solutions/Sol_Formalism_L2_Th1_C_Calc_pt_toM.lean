-- Prove2me | solution 1 for Formalism.L2.Th1.C.Calc.pt_toM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:30:23.738747+00:00
-- url     : https://prove2.me/submissions/6d1616c1-5de0-42b6-8fcb-caf82eafd973

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
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_linv_l


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
open Formalism.L2.Th1.C.Calc
open Pts Formalism.HermitianLattices.IntegralLatticeDensity
variable {K : Type} [Field K] [CharZero K] {O : Type} [CommRing O] [StarRing O]
variable {R : Subring K} {l linv : PowerSeries K} {τ : O →+* K}
namespace Formalism.L2.Th1.C.Calc
theorem _root_.solution (D : Data R l linv τ) {σ : Type} (x : MvPowerSeries σ K) (hx : IsPt R x) :
    pt D (toM D x hx) = x := by
  show PowerSeries.subst (PowerSeries.subst x l) linv = x
  exact subst_linv_l D.log hx.1
end Formalism.L2.Th1.C.Calc
