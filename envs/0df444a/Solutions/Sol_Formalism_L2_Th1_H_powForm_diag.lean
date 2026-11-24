-- Prove2me | solution 1 for Formalism.L2.Th1.H.powForm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:29.255805+00:00
-- url     : https://prove2.me/submissions/ecc5a60d-2f27-4e40-8ec7-deb96f0491ef

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (l : V →L[ℂ] ℂ) (n : ℕ) (y : V) : powForm l n (fun _ => y) = l y ^ n := by
  simp [powForm]
end Formalism.L2.Th1.H
