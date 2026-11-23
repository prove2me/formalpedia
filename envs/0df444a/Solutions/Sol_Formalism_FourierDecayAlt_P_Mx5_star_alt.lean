-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:52.418384+00:00
-- url     : https://prove2.me/submissions/1ee07227-2aa5-4119-8ff9-2417eaab5e26

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
section
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
private theorem star_sc_lemma (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  rfl
section lead
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {n m : ℕ} {c d : R} {f g : ℂ → R}
end lead
end Formalism.FourierDecayAlt.P.Mx5
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution : star (zA P) = zbA P := by
  unfold zA zbA
  rw [star_sc_lemma]
  rfl
end Formalism.FourierDecayAlt.P.Mx5
