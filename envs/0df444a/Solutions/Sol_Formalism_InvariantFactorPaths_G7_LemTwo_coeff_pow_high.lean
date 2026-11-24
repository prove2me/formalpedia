-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_pow_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.654934+00:00
-- url     : https://prove2.me/submissions/dd7190e8-fb08-45aa-a401-98b93478f684

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
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    {e : ι →₀ ℕ} {k : ℕ} (hk : e.degree < k) : MvPowerSeries.coeff e (f ^ k) = 0 :=
  MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf))
end Formalism.InvariantFactorPaths.G7.LemTwo
