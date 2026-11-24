-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_lgF_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.836778+00:00
-- url     : https://prove2.me/submissions/c77b86ed-313c-4b55-9dd7-c853bcc40439

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_pow_parity

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
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ i) (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (pow_parity hp i j)]
end Formalism.InvariantFactorPaths.G7.LemTwo
