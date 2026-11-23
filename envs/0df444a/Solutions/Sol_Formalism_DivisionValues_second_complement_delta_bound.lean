-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_delta_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:04.208556+00:00
-- url     : https://prove2.me/submissions/626665b2-ce94-4ffc-bd4f-7ed2fae60422

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
theorem _root_.solution (C0 k S m tt η b w'' z dν dpm : ℝ) (hC0 : 0 ≤ C0) (hkS : k * S ≤ w'')
    (h1 : m * η ≤ w'') (h2 : m * tt * η ≤ w'') (hwb : w'' ≤ b) (hz : z ≤ b)
    (hν : dν ≤ C0 * (k * S + m * tt * η + z)) (hpm : dpm ≤ C0 * (k * S + m * η)) :
    dν + dpm ≤ 5 * C0 * b := by
  have g1 : C0 * (k * S + m * tt * η + z) ≤ C0 * (3 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have g2 : C0 * (k * S + m * η) ≤ C0 * (2 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  linarith
end Formalism.DivisionValues
