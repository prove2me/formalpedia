-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:02.171926+00:00
-- url     : https://prove2.me/submissions/7b838840-1df2-4471-968c-8e99017aae28

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_coeff_euler
import Theorems.Thm_Formalism_L2_G_Model_sw_Dop_self
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_weight_rowW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    Dop R a a f = (μ a : R) • f := by
  rw [sw_Dop_self]
  ext m
  rw [sw_coeff_euler, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [← lgraded_weight_rowW, hf hm]
end Formalism.L2.G.Model
