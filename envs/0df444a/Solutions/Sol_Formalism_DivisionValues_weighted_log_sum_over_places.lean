-- Prove2me | solution 1 for Formalism.DivisionValues.weighted_log_sum_over_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:22.911195+00:00
-- url     : https://prove2.me/submissions/341e35f6-2e36-4b6c-8b09-c5a8e4f7c70e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_finite
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_finsum_over
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_conj_nat
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_conj
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_sum_lw_vw

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
theorem _root_.solution : LwSumOver := by
  unfold LwSumOver
  intro K _ _ _ _ g hg
  have hS := plOver_finite (K := K) g
  refine ⟨hS, fun w => vw_conj_nat g w, fun w => plOver_conj g w, fun w => lw_pos w, ?_⟩
  rw [finsum_over hS]
  exact sum_lw_vw K hg hS
end Formalism.DivisionValues
