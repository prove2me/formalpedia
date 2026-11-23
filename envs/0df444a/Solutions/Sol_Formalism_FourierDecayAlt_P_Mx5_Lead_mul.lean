-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.Lead.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:05.950332+00:00
-- url     : https://prove2.me/submissions/f65123d4-b274-41a1-b2ac-97389628a3f4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_iff

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
theorem _root_.solution (hf : Lead n c f) (hg : Lead m d g) : Lead (n + m) (c * d) fun Y => f Y * g Y := by
  rw [lead_iff] at hf hg ⊢
  obtain ⟨p, hp1, hp2, hp3⟩ := hf
  obtain ⟨q, hq1, hq2, hq3⟩ := hg
  refine ⟨p * q, Polynomial.natDegree_mul_le.trans (add_le_add hp1 hq1), ?_, fun Y => ?_⟩
  · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp1 hq1, hp2, hq2]
  · rw [hp3, hq3]
    exact (map_mul (Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap ℂ R Y)
      fun a => Algebra.commute_algebraMap_right Y a) p q).symm
end Lead
end Formalism.FourierDecayAlt.P.Mx5
