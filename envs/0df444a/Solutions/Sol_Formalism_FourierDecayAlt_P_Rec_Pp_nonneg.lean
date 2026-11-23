-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.Pp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.769228+00:00
-- url     : https://prove2.me/submissions/c0d7e0c7-35f3-44a9-b07b-e86d559eada0

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_one_le_Pp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i :=
  le_trans zero_le_one (one_le_Pp he i)
end Formalism.FourierDecayAlt.P.Rec
