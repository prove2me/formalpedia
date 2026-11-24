-- Prove2me | solution 1 for Formalism.L2.Th1.H.SemicharacterExponentialLemmas.altE_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:01.595879+00:00
-- url     : https://prove2.me/submissions/7fd82b24-605d-4c53-add6-83b437e75ab5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement

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
open Formalism.L2.Th1.H.SemicharacterExponentialLemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.SemicharacterExponentialLemmas
theorem _root_.solution (H : Sesq V) (k : ℕ) (x y : V) : altE H x (k • y) = k * altE H x y := by
  simp [altE, map_nsmul, nsmul_eq_mul]
end Formalism.L2.Th1.H.SemicharacterExponentialLemmas
