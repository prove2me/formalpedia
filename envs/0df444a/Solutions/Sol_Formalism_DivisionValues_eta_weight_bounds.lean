-- Prove2me | solution 1 for Formalism.DivisionValues.eta_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:29.565864+00:00
-- url     : https://prove2.me/submissions/939cda4f-3443-469a-a2d7-38bdea86a352

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution (m tt η w'' : ℝ) (hm : 1 ≤ m) (htt : 0 ≤ tt) (hη : 0 ≤ η)
    (h : m * (tt + 1) * η ≤ w'') : m * η ≤ w'' ∧ m * tt * η ≤ w'' := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : 0 ≤ m * η := mul_nonneg hm0 hη
  have h2 : 0 ≤ m * tt * η := mul_nonneg (mul_nonneg hm0 htt) hη
  constructor <;> linarith
end Formalism.DivisionValues
