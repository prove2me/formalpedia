-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.euler_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:56.508627+00:00
-- url     : https://prove2.me/submissions/9352b8cf-9bcd-475c-8e4e-0b183b873a44

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (v : Var r) (f : Fn r) (hf : f ≠ 0) : euler v f⁻¹ = -(f⁻¹ * f⁻¹ * euler v f) := by
  have h := eulerLeibniz r v f f⁻¹
  rw [mul_inv_cancel₀ hf, euler_one] at h
  have h2 : f * euler v f⁻¹ = -(euler v f * f⁻¹) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h.symm
  have h3 : euler v f⁻¹ = f⁻¹ * (f * euler v f⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  rw [h3, h2]; ring
end Formalism.FourierDecayAlt.P.Mx4
