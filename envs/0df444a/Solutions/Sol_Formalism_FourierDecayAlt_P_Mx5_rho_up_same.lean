-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.rho_up_same
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:21.375512+00:00
-- url     : https://prove2.me/submissions/91933d9f-1bcc-4ffc-a3de-e0ac16adbbd8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {π π' : Ty P} (h : Up P l π π') :
    rho P π' l = rho P π l + 1 := by
  rw [Finset.mem_Icc] at hl
  unfold rho
  simp only [dif_pos hl]
  have := h ⟨l - 1, by omega⟩
  simp only [Fin.val_mk] at this
  rw [if_pos (by omega)] at this
  rw [this]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.Mx5
