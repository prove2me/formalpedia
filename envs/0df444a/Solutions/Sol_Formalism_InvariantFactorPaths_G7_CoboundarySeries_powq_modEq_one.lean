-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.powq_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:22.116842+00:00
-- url     : https://prove2.me/submissions/a3f2ae4d-88ef-4f20-befd-9e29a94ee4b2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (x : ℕ) : (p ^ 2) ^ x ≡ 1 [MOD p ^ 2 - 1] := by
  have h : p ^ 2 ≡ 1 [MOD p ^ 2 - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
  simpa using h.pow x
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
