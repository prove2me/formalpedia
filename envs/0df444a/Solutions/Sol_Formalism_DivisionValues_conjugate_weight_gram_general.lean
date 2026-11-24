-- Prove2me | solution 1 for Formalism.DivisionValues.conjugate_weight_gram_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:04.680657+00:00
-- url     : https://prove2.me/submissions/d457193a-622e-4369-a29a-9c0e22616588

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_jwGramW_of
import Theorems.Thm_Formalism_DivisionValues_index_change_formula


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
theorem _root_.solution : JwGramW := jwGramW_of index_change_formula
end Formalism.DivisionValues
