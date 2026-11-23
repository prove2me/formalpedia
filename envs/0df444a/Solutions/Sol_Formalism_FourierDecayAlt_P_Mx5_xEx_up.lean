-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.xEx_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:32.69129+00:00
-- url     : https://prove2.me/submissions/504461ef-9a3f-443e-9d24-db08c0a4f65f

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
theorem _root_.solution (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) (π π' : Ty P) (h : Up P l π π') :
    xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_sdiff, Finset.mem_Icc] at hi
  have hil : i ≠ l := fun e => hi.2 (by rw [e]; exact hl)
  have key : rho P π' i = rho P π i := by
    unfold rho
    simp only [dif_pos hi.1]
    have := h ⟨i - 1, by omega⟩
    simp only [Fin.val_mk] at this
    rw [if_neg (by omega), add_zero] at this
    rw [this]
  rw [key]
end Formalism.FourierDecayAlt.P.Mx5
