-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:11.573797+00:00
-- url     : https://prove2.me/submissions/5b0e0f76-7963-4a9d-96e4-92cac6de52fa

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
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {n m : ℕ} {c d : R} {f g : ℂ → R}
namespace Formalism.FourierDecayAlt.P.Mx5
namespace Lead
theorem _root_.solution (hf : Lead n c f) (hn : n = m) (hc : c = d) (hg : ∀ Y, g Y = f Y) : Lead m d g := by
  subst hn hc
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun Y => by rw [hg, ha]⟩
end Lead
end Formalism.FourierDecayAlt.P.Mx5
