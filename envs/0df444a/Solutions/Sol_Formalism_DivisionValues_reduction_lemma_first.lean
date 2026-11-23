-- Prove2me | solution 1 for Formalism.DivisionValues.reduction_lemma_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:19.977017+00:00
-- url     : https://prove2.me/submissions/b4ae6ca3-a7c8-40a1-830c-0589cc1122b5

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_main
import Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he
end Formalism.DivisionValues
