-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:19.0458+00:00
-- url     : https://prove2.me/submissions/f0756200-aa48-4012-ae87-717fcfcb1cb1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_coboundary_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_last_pair

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
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (a : K)
    (H : MvPowerSeries (Fin 2) K) : d1 F (C a * H) = C a * d1 F H := by
  have key : ∀ (b : Fin 2 → MvPowerSeries (Fin 3) K), HasSubst b →
      subst b (C a * H) = C a * subst b H := by
    intro b hb
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul hb]
  unfold d1
  rw [key _ (has_subst_coboundary_first hF), key _ (has_subst_last_pair 0), key _ (has_subst_last_pair 1)]
  ring
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
