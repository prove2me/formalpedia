-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.one_le_Pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:18.310842+00:00
-- url     : https://prove2.me/submissions/77882d54-3138-4bd9-881c-c7e06d5fd78b

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_one_le_sqrt_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real
namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by
  intro i
  induction i with
  | zero => rw [Pp_zero]
  | succ k ih =>
    rw [Pp_succ]
    have := one_le_sqrt_e he (k+1)
    nlinarith
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
