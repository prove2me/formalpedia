-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.KU_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:45:56.102005+00:00
-- url     : https://prove2.me/submissions/d5f70e32-1088-475a-aa9d-f0b7f1cac051

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_col_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_mat_ext_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} {γ κ : B.Mat k r} (hκ : κ ∈ C2.KU k r z z' γ) :
    κ * gnB k r z z' γ = gnB k r z z' γ := by
  apply mat_ext_col; intro j
  rw [col_mul, hκ.2 j]
  funext a; simp [gnB]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
