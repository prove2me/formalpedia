-- Prove2me | solution 1 for Formalism.LT.LTL.seq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:09.763875+00:00
-- url     : https://prove2.me/submissions/3f8d8f50-699e-4d8c-8c4d-1d5012348f40

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_step_inv
import Theorems.Thm_Formalism_LT_LTL_inv_seq

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}
namespace Formalism.LT.LTL
theorem _root_.solution (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (k : ℕ) :
    Low (k + 2) (seq e e' π a (k + 2) - seq e e' π a (k + 1)) := by
  have := (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).2
  change Low (k + 2) (seq e e' π a (k + 1) + corr e e' π (k + 1) (seq e e' π a (k + 1)) -
    seq e e' π a (k + 1))
  rw [add_sub_cancel_left]; exact this
end Formalism.LT.LTL
