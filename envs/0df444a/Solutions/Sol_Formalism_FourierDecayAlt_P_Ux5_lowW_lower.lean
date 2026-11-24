-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.lowW_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:45.37397+00:00
-- url     : https://prove2.me/submissions/edb128eb-5c7b-4d45-996f-a27b83f5da0f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) (h : a < b) : lowW σ v a b = 0 := by
  have : ¬ (b < a ∧ σ.symm b < σ.symm a) := fun h' => absurd h'.1 (not_lt.mpr (le_of_lt h))
  simp [lowW, ne_of_lt h, this]
end Formalism.FourierDecayAlt.P.Ux5
