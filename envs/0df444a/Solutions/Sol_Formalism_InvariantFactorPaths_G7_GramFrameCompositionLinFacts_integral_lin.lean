-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.integral_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:44.587499+00:00
-- url     : https://prove2.me/submissions/ff646959-4cd3-4737-a717-58c91454fc42

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_pderiv
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6


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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution [CharZero K] {τ κ : Type} [Finite τ] {D : MvPowerSeries τ K}
    (hD0 : constantCoeff D = 0) (hDi : Integral (mvExp D)) {b : τ → MvPowerSeries κ K}
    (hb0 : ∀ i, constantCoeff (b i) = 0) (hbi : ∀ i, Integral (b i)) (hbD : subst b D = 0)
    (e : τ) : Integral (subst b (pderiv K e D)) := by
  have hb := hasSubst_of_constantCoeff_zero hb0
  have h1 : pderiv K e (mvExp D) = mvExp D * pderiv K e D := by
    unfold mvExp
    rw [pderiv_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hD0),
      PowerSeries.derivative_exp]
  have h2 : subst b (pderiv K e D) = subst b (pderiv K e (mvExp D)) := by
    rw [h1, subst_mul hb, LogarithmEquivalence.subst_mvExp' hb hD0, hbD, LogarithmEquivalence.mvExp_zero', one_mul]
  rw [h2]
  exact LogarithmEquivalence.integral_subst' hb0 hbi (integral_pderiv hDi e)
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
