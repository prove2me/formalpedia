-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:50.804228+00:00
-- url     : https://prove2.me/submissions/ee0e0b54-d890-46ce-9ae0-d093689d650d

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_one_le_Pp

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i :=
  le_trans zero_le_one (one_le_Pp he i)
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
