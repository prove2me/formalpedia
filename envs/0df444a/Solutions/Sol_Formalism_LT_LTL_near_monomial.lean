-- Prove2me | solution 1 for Formalism.LT.LTL.near_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:30.926261+00:00
-- url     : https://prove2.me/submissions/70987532-1d5b-4363-9432-95f5c974bb2b

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_near_prod

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
theorem _root_.solution {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι →₀ ℕ) :
    Near m.degree (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  rw [Finsupp.degree_apply]
  exact near_prod hab m m.support
end Formalism.LT.LTL
