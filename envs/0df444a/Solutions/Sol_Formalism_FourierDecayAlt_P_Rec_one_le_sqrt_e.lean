-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.one_le_sqrt_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.895332+00:00
-- url     : https://prove2.me/submissions/be47c67e-b154-4d1d-8529-d528e9601895

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (l : ℕ) : (1:ℝ) ≤ √(1 + e l) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + e l by linarith [he l])
  rwa [Real.sqrt_one] at this
end Formalism.FourierDecayAlt.P.Rec
