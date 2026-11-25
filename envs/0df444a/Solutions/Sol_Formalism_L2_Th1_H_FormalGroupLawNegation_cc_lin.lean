-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:18:28.730223+00:00
-- url     : https://prove2.me/submissions/c5c3ad92-9fda-4f04-9b4c-7b8ceefca209

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
open Formalism.L2.Th1.H.FormalGroupLawNegation
variable {K : Type} [Field K] {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.FormalGroupLawNegation
theorem _root_.solution {σ m : Type} [Fintype m] (c : m → K) {u : m → MvPowerSeries σ K}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * u j) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hu j, mul_zero]
end Formalism.L2.Th1.H.FormalGroupLawNegation
