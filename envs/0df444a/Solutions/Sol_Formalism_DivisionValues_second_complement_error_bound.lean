-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:04.253018+00:00
-- url     : https://prove2.me/submissions/15f6d77a-daac-490c-8c1c-c832181ef81c

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
theorem _root_.solution (C0 f N tt m η b w'' er : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hNN : N * (N + tt) ≤ b) (hmη : m * η ≤ w'') (hwb : w'' ≤ b)
    (her : er ≤ C0 * (f * (N * (N + tt) + m ^ 2 * η))) : er ≤ C0 * (f * (b + m * b)) := by
  have hm0 : 0 ≤ m := by linarith
  have hmb : m * η ≤ b := le_trans hmη hwb
  have h1 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left hmb hm0
  have h2 : f * (N * (N + tt) + m ^ 2 * η) ≤ f * (b + m * b) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hC0
  linarith
end Formalism.DivisionValues
