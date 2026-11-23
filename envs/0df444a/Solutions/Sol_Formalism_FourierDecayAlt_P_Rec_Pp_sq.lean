-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.Pp_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.067813+00:00
-- url     : https://prove2.me/submissions/72d05441-d1e5-4fe9-b3a2-4ef810bbd011

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by
  unfold Pp
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  rw [Real.sq_sqrt (by linarith [he l])]
end Formalism.FourierDecayAlt.P.Rec
