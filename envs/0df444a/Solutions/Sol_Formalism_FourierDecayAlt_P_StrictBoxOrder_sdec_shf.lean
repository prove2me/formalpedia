-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.sdec_shf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:56:39.672473+00:00
-- url     : https://prove2.me/submissions/bf22861b-f218-4db9-84ba-9a060e4b1d66

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
theorem _root_.solution {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (h : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h1 := h hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  simp only [shf]
  have h2 : ((M a - M b - 1).toNat : ℤ) = M a - M b - 1 := Int.toNat_of_nonneg (by omega)
  have h3 : (((M a - M b - 1).toNat : ℕ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, h2]
  rw [h3]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.StrictBoxOrder
