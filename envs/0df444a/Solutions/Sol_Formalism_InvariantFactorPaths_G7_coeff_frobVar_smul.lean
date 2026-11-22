-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:06.807736+00:00
-- url     : https://prove2.me/submissions/eb55062a-d121-4130-8905-5abe5a63e639

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K)
    (m : ι →₀ ℕ) : MvPowerSeries.coeff (p • m) (frobVar p f) = MvPowerSeries.coeff m f := by
  rw [frobVar_eq_expand hp, MvPowerSeries.coeff_expand_smul]
end Formalism.InvariantFactorPaths.G7
