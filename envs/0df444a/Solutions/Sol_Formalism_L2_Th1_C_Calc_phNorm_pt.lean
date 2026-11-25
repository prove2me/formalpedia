-- Prove2me | solution 1 for Formalism.L2.Th1.C.Calc.phNorm_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:20.910048+00:00
-- url     : https://prove2.me/submissions/639e9814-df37-4f4b-b57d-8c933822720d

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
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_eq_subst_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
import Theorems.Thm_Formalism_L2_Th1_C_lGSubst


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
open Pts
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {σ : Type}
namespace Formalism.L2.Th1.C.Calc
theorem _root_.solution {l linv ph : PowerSeries K} (h : IsLogPair l linv) {a b : K}
    (hN : PhNormAt R l linv ph a b) {x : MvPowerSeries σ K} (hx : IsPt R x) :
    Cong R (PowerSeries.subst (fmul l linv a x) ph) ((a * b) • PowerSeries.subst x ph) := by
  have := lGSubst K R _ hN σ x hx
  rw [PowerSeries.subst_sub (hasSubst hx.1), PowerSeries.subst_smul (hasSubst hx.1),
    subst_subst (constantCoeff_mulBy h a) hx.1, ← fmul_eq_subst_mulBy h a hx.1] at this
  exact this
end Formalism.L2.Th1.C.Calc
