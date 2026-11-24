-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormEntryBounds.Hpk_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:37.126941+00:00
-- url     : https://prove2.me/submissions/eaaff842-452d-478c-a73a-ce76e5b194db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open Formalism.FourierDecayAlt.P.NormEntryBounds
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NormEntryBounds
theorem _root_.solution (y : Fin (2 * r + k + 1) → ℂ) (X : ℝ) (hy : ∀ p, ‖y p‖ ≤ X) (j : Fin (2 * r + k + 1)) :
    ‖(Hpk k r *ᵥ y) j‖ ≤ X := by
  rw [gn_Hpk_mulVec]
  split_ifs
  · exact hy _
  · rw [norm_neg]; exact hy _
  · exact hy _
end Formalism.FourierDecayAlt.P.NormEntryBounds
