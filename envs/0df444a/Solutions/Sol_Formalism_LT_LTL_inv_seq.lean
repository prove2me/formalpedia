-- Prove2me | solution 1 for Formalism.LT.LTL.inv_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:52.576265+00:00
-- url     : https://prove2.me/submissions/7c1f7103-2bc8-4b3f-a1ef-fe577468cdbe

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_step_inv
import Theorems.Thm_Formalism_LT_LTL_inv_lin

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
    (ha : ∀ i, ‖a i‖ ≤ 1) : ∀ k : ℕ, Inv e e' a (k + 1) (seq e e' π a (k + 1))
  | 0 => inv_lin hS he he' ha
  | (k + 1) => (step_inv hS he he' (by omega) (solution hS he he' ha k)).1
end Formalism.LT.LTL
