-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.Pp_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:40.847898+00:00
-- url     : https://prove2.me/submissions/7ebeab58-8ffd-4f25-a17f-4db266d47eb8

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_one_le_sqrt_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_nonneg

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : Monotone (Pp e) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Pp_succ]
  exact le_mul_of_one_le_right (Pp_nonneg he n) (one_le_sqrt_e he (n+1))
end Formalism.FourierDecayAlt.P.Rec
