-- Prove2me | solution 1 for Formalism.L2.Th1.C.Calc.phi_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:49:04.573985+00:00
-- url     : https://prove2.me/submissions/8f72dfbe-8cf5-42ed-aca0-5c216e0ff997

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
import Theorems.Thm_Formalism_L2_Th1_C_Calc_phNorm_pt
import Theorems.Thm_Formalism_L2_Th1_C_Calc_isPt_pt
import Theorems.Thm_Formalism_L2_Th1_C_Calc_pt_smul
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cls_eq
import Theorems.Thm_Formalism_L2_Th1_C_Calc_cls_smul

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
theorem _root_.solution (D : Data R l linv τ) {ph : PowerSeries K} {α : O}
    (hN : PhNormAt R l linv ph (τ α) (τ (star α))) {σ : Type} (u : ptsSub D σ) :
    phi D ph (α • u) = nm α • phi D ph u := by
  unfold phi
  rw [pt_smul, ← cls_smul, cls_eq D]
  have h := phNorm_pt D.log hN (isPt_pt D u)
  have e : τ (↑(nm α) : O) = τ α * τ (star α) := by
    show τ (star α * α) = _
    rw [map_mul, mul_comm]
  rw [e]
  exact h
end Formalism.L2.Th1.C.Calc
