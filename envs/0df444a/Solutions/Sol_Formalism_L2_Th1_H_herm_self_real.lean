-- Prove2me | solution 1 for Formalism.L2.Th1.H.herm_self_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:26.265419+00:00
-- url     : https://prove2.me/submissions/d7d4b151-32e0-4d73-9acc-6b6bbf7bd8e9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces

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
theorem _root_.solution (H : Sesq V) (hH : IsHerm H) (z : V) : (((H z z).re : ℝ) : ℂ) = H z z := by
  exact Complex.conj_eq_iff_re.1 (hH z z).symm
end Formalism.L2.Th1.H
