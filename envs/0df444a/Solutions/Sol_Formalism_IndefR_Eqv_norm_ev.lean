-- Prove2me | solution 1 for Formalism.IndefR.Eqv.norm_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:58.966934+00:00
-- url     : https://prove2.me/submissions/ea278abb-b64d-44cc-a8fe-0df3605d06fc

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterEqOfRange
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {k : ℕ} (j : Fin k) : ‖ev j‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp [ev]
    · simp [ev, h]
  · have := norm_le_pi_norm (ev j) j
    simpa [ev] using this
end Formalism.IndefR.Eqv
