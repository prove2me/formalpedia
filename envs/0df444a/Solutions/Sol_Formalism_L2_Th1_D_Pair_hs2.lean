-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.hs2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:17.281312+00:00
-- url     : https://prove2.me/submissions/97f265d6-2e7b-4f19-8bca-44914afdbd9e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
namespace Pair
section Alg
variable {K : Type} [Field K]
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
end Alg
section NormedLin
variable {K : Type} [NormedField K]
end NormedLin
section Normed
variable {K : Type} [NormedField K] [CharZero K]
end Normed
end Pair
open Pair
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] := by
  exact hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]
end Formalism.L2.Th1.D.Pair
