-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.one_le_Pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.132899+00:00
-- url     : https://prove2.me/submissions/ff852181-38d7-4672-98cb-71b05b1872ff

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_one_le_sqrt_e

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by
  intro i
  induction i with
  | zero => rw [Pp_zero]
  | succ k ih =>
    rw [Pp_succ]
    have := one_le_sqrt_e he (k+1)
    nlinarith
end Formalism.FourierDecayAlt.P.Rec
