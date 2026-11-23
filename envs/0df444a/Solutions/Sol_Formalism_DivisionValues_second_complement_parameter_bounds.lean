-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:04.313284+00:00
-- url     : https://prove2.me/submissions/3e0c2b64-ca44-4f83-b1e6-2520430bcdbb

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
theorem _root_.solution (f m b L B0 : ℝ) (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hb : 0 ≤ b) : 0 ≤ f * b ∧ f * b * L ≤ B0 ∧ b ≤ B0 := by
  subst hB0
  have hf0 : 0 ≤ f := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  refine ⟨hfb, ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg hfb hL0) (sub_nonneg.2 hm)
    linarith
  · have h1 : 1 ≤ f * m * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm) hL
    have := mul_nonneg hb (sub_nonneg.2 h1)
    linarith
end Formalism.DivisionValues
