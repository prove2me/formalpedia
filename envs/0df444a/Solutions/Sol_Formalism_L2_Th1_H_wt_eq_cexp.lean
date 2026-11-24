-- Prove2me | solution 1 for Formalism.L2.Th1.H.wt_eq_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:40:03.415808+00:00
-- url     : https://prove2.me/submissions/6493eb41-f40f-4591-ab4d-bfd92178a7b4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Theorems.Thm_Formalism_L2_Th1_H_herm_self_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (H : Sesq V) (hH : IsHerm H) (z : V) :
    (wt H z : ℂ) = Complex.exp (-(Real.pi : ℂ) * H z z) := by
  rw [wt, Complex.ofReal_exp]
  push_cast
  rw [herm_self_real H hH z]
end Formalism.L2.Th1.H
