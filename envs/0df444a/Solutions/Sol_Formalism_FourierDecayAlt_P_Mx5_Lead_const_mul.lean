-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:32.886931+00:00
-- url     : https://prove2.me/submissions/3e0b8cc1-3718-46e2-92e6-35a26f54a058

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
theorem _root_.solution (a : R) (hf : Lead n c f) : Lead n (a * c) fun Y => a * f Y := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨fun i => a * b i, fun Y => by simp only [hb, mul_add, Finset.mul_sum, mul_smul_comm]⟩
end Lead
end Formalism.FourierDecayAlt.P.Mx5
