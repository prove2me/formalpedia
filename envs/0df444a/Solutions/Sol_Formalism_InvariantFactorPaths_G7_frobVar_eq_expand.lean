-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.frobVar_eq_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:36.423793+00:00
-- url     : https://prove2.me/submissions/017bee67-2850-4ccf-a3cd-0c78e5b7774a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA

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
theorem _root_.solution {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K) :
    frobVar p f = MvPowerSeries.expand p hp f := by
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  rfl
end Formalism.InvariantFactorPaths.G7
