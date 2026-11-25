-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.Phi_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:16.670378+00:00
-- url     : https://prove2.me/submissions/2d30d0c1-61b3-40ae-aa9d-e24508fd3626

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_map_frame


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
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ h : B.Mat k r}
    (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') : IsUnit (PhiH k r z z' γ h).det := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  unfold PhiH
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (C2x2.ut_unit hU.2.1).mul (C2x2.ut_unit hU'.2.1)
end Formalism.FourierDecayAlt.P.FlagGramRestriction
