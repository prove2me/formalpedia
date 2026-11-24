-- Prove2me | solution 1 for Formalism.LT.LTL.prod_const_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:41.201354+00:00
-- url     : https://prove2.me/submissions/7184653e-fce0-484b-a23e-63cdaf54c323

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution (c : K) (d : ι →₀ ℕ) : (d.prod fun _ m => c ^ m) = c ^ d.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
end Formalism.LT.LTL
