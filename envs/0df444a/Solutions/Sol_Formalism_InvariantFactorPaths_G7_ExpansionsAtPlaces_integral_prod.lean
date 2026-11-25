-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces.integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:23.695227+00:00
-- url     : https://prove2.me/submissions/d94c31d1-ef01-40ad-a388-f34bb13159a2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ExpansionsAtPlaces
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_le_one


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow
  integral_add integral_neg integral_sum integral_C integral_X integral_zero pinv_le_one
  constantCoeff_sSub integral_sSub)
open Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces
namespace Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces
theorem _root_.solution {K ι α : Type} [NormedField K] [IsUltrametricDist K] (s : Finset α)
    (x : α → MvPowerSeries ι K) (hx : ∀ i, Integral (x i)) : Integral (∏ i ∈ s, x i) :=
  Finset.prod_induction _ (fun y => Integral y) (fun _ _ h₁ h₂ => integral_mul h₁ h₂)
    integral_one fun i _ => hx i
end Formalism.InvariantFactorPaths.G7.ExpansionsAtPlaces
