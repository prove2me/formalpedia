-- Prove2me | solution 1 for Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:14.276333+00:00
-- url     : https://prove2.me/submissions/a9c6a4e9-4b77-4ab0-881e-d0e6afd7b0a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
open Pair InverseCommuting
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
theorem _root_.solution (a b : K) (B : MvPowerSeries (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    coeff d (rescale ![a, b] B) = a ^ d 0 * b ^ d 1 * coeff d B := by
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl
end Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
