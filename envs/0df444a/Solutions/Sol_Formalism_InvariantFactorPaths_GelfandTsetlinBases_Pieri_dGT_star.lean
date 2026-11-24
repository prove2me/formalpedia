-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.dGT_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:00.655636+00:00
-- url     : https://prove2.me/submissions/3a55c47f-ef05-4773-b8a1-3639ef8eab96

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_dGT_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_star_star
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_star_mem_gtBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution (n : ℕ) : ∀ μ : Fin n → ℤ, dGT n (star μ) = dGT n μ := by
  induction n with
  | zero =>
    intro μ
    rw [Subsingleton.elim (star μ) μ]
  | succ n ih =>
    intro μ
    rw [dGT_succ, dGT_succ]
    refine Finset.sum_nbij' star star (fun κ hκ => ?_) (fun κ hκ => star_mem_gtBox hκ)
      (fun κ _ => star_star κ) (fun κ _ => star_star κ) (fun κ _ => (ih κ).symm)
    simpa [star_star] using star_mem_gtBox hκ
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
