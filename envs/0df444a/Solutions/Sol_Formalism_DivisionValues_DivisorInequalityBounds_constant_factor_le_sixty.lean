-- Prove2me | solution 1 for Formalism.DivisionValues.DivisorInequalityBounds.constant_factor_le_sixty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:55.321867+00:00
-- url     : https://prove2.me/submissions/91b10226-9769-463b-aaa5-f34729185ce6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds
namespace Formalism.DivisionValues.DivisorInequalityBounds
theorem _root_.solution (C0 ce : ℝ) (hC0 : 1 ≤ C0) (hce : 0 ≤ ce) : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := by
  have hC : 0 < C0 := by linarith
  rw [mul_div_assoc', div_le_iff₀ hC]
  nlinarith [mul_nonneg hce (sub_nonneg.2 hC0)]
end Formalism.DivisionValues.DivisorInequalityBounds
