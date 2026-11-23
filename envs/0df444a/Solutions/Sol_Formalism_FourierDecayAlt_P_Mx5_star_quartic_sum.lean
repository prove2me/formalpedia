-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_quartic_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:29.548747+00:00
-- url     : https://prove2.me/submissions/4069015e-8467-4e0a-9a71-965964f9e73d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_xEx
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sss

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
theorem _root_.solution (Y : ℂ) : star (S4 P Y) = S4 P (star Y) := by
  unfold S4
  simp only [star_sum, star_mul, star_star, star_kap, star_xEx]
  rw [Finset.sum_comm' (t' := Icc 1 (P.k - 1)) (s' := fun y => (Icc 1 (P.k - 1)).erase y)
    (fun x y => by simp only [Finset.mem_erase, ne_comm]; tauto)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.pair_comm b a]
  exact ((kap_sss P a _ fun π π' h => xEx_up P a {a, b} (by simp) (star Y) π π' h).mul_right
    (kap_ss P b _ fun π π' h => xEx_up P b {a, b} (by simp) (star Y) π π' h)).eq
end Formalism.FourierDecayAlt.P.Mx5
