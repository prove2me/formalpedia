-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.shf_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:18.065836+00:00
-- url     : https://prove2.me/submissions/7b004e2c-eb4b-4e35-8e08-f718bb051bc4

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.BranchingSystems
theorem _root_.solution {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    Function.update (shf β M) i (shf β M i + 1) = shf β (Function.update M i (M i + 1)) := by
  rw [← shf_update]
  simp [shf]
  ring
end Formalism.FourierDecayAlt.P.BranchingSystems
