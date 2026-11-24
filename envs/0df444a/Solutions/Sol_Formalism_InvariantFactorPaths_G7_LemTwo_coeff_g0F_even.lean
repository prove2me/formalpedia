-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_g0F_even
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:19.907656+00:00
-- url     : https://prove2.me/submissions/6c104408-0456-46c1-a8c2-6b7799129d95

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
    PowerSeries.coeff ((p ^ 2) ^ i) (g0F K p) = 0 := by
  rw [g0F, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (fun h => pow_parity hp j i h.symm)]
end Formalism.InvariantFactorPaths.G7.LemTwo
