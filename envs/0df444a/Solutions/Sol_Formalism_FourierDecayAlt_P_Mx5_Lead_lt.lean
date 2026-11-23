-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:25.28408+00:00
-- url     : https://prove2.me/submissions/d673a1fd-6eb6-4374-a228-85f1cb36e16f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_succ

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
theorem _root_.solution (hf : Lead n c f) (h : n < m) : Lead m 0 f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  clear h
  induction k with
  | zero => exact hf.succ
  | succ k ih => exact ih.succ
end Lead
end Formalism.FourierDecayAlt.P.Mx5
