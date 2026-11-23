-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.rho_up_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:04.220357+00:00
-- url     : https://prove2.me/submissions/516c0dca-fd3d-41fb-9a87-01a34850d38d

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
theorem _root_.solution {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) {π π' : Ty P} (h : Up P l π π') :
    rho P π' j = rho P π j := by
  rw [Finset.mem_Icc] at hj
  unfold rho
  simp only [dif_pos hj]
  have := h ⟨j - 1, by omega⟩
  simp only [Fin.val_mk] at this
  rw [if_neg (by omega), add_zero] at this
  rw [this]
end Formalism.FourierDecayAlt.P.Mx5
