-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_one_lgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.814804+00:00
-- url     : https://prove2.me/submissions/b28b90fb-c93a-4e97-b640-cbada19ed5de

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) : PowerSeries.coeff 1 (lgF K p) = 1 := by
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
  have h4 : 4 ≤ p ^ 2 := by nlinarith
  have hne : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by rw [pow_one]; omega
  rw [if_neg hne, if_pos (by rw [pow_zero]), pow_zero, inv_one, add_zero]
end Formalism.InvariantFactorPaths.G7.LemTwo
