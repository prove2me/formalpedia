-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.shf_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:55.620527+00:00
-- url     : https://prove2.me/submissions/f7d3a4de-3cab-4f2e-b97a-c06b846dfd44

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems

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
theorem _root_.solution {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) (t : ℤ) :
    Function.update (shf β M) i (β + (t : ℂ)) = shf β (Function.update M i t) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [shf]
  · simp [shf, Function.update_of_ne h]
end Formalism.FourierDecayAlt.P.BranchingSystems
