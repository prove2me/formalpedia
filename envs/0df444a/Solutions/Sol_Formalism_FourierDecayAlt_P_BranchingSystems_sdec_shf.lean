-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.sdec_shf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:56:37.775728+00:00
-- url     : https://prove2.me/submissions/77da701c-a3bf-4f42-9fba-ec1ab28d8d8d

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
theorem _root_.solution {n : ℕ} (β : ℂ) {L : Fin n → ℤ} (hL : StrictAnti L) : SDec (shf β L) := by
  intro a b hab
  have h := hL hab
  refine ⟨(L a - L b - 1).toNat, ?_⟩
  simp only [shf]
  have e : ((L a - L b - 1).toNat : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
  have e2 : (((L a - L b - 1).toNat : ℕ) : ℂ) = ((L a - L b - 1 : ℤ) : ℂ) := by exact_mod_cast e
  rw [e2]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.BranchingSystems
