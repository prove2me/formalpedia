-- Prove2me | solution 1 for Formalism.DivisionValues.cm_maximal_order_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:19.185966+00:00
-- url     : https://prove2.me/submissions/d30b4dab-4795-480d-a9c9-ed8f4c2f2ae0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_isCMSub_cmMax
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_le_cmMax
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_star_mem_cmMax
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_mem_cmMax_iff_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : CmMaxSpec := fun _ _ _ _ =>
  ⟨ConjugateWeightGram.isCMSub_cmMax, ConjugateWeightGram.le_cmMax, fun _ ha => ConjugateWeightGram.star_mem_cmMax ha,
    ConjugateWeightGram.mem_cmMax_iff_twist⟩
end Formalism.DivisionValues
