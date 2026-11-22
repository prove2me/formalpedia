-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:28.03696+00:00
-- url     : https://prove2.me/submissions/f8469c41-547f-4e41-b22b-79f34df2464c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Theorems.Thm_Bl_general_b_fact_second_last_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution (B : ℤ) : ∀ {S : ℕ} (c : Fin S → ℤ), (∀ m, |c m| < B) →
    ∑ m, c m * B ^ (m : ℕ) = 0 → ∀ m, c m = 0 := by
  first | exact Bl.general_b_fact_second_last.goal1 .. | (apply Bl.general_b_fact_second_last.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_last.goal1 <;> assumption)
end Formalism.FrobeniusOrbits.ThickExists
