-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.norm_sum_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:58.737375+00:00
-- url     : https://prove2.me/submissions/719605d0-ab10-40ae-8f3f-cff8a7431904

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.L2.Th1.E.Ser
