-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:34.013832+00:00
-- url     : https://prove2.me/submissions/f611b74e-32cf-4708-9121-d0f055d4625a

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
theorem _root_.solution (hf : Lead n c f) : Lead (n + 1) 0 f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun i => if i = n then c else a i, fun Y => ?_⟩
  beta_reduce
  rw [ha, smul_zero, zero_add, Finset.sum_range_succ, if_pos rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_neg (Finset.mem_range.1 hi).ne]
end Lead
end Formalism.FourierDecayAlt.P.Mx5
