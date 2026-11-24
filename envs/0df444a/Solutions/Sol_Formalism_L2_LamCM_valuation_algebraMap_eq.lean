-- Prove2me | solution 1 for Formalism.L2.LamCM.valuation_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:31.475115+00:00
-- url     : https://prove2.me/submissions/3a303e61-0a46-4e29-966e-dbf91933df4a

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K r) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg hr,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]
end Formalism.L2.LamCM
