-- Prove2me | solution 1 for Formalism.L2.Th1.H.SemicharacterExponentialLemmas.altE_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:20.062245+00:00
-- url     : https://prove2.me/submissions/8b46e08b-d49d-4251-bfb7-eed1c87a5e0d

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
theorem _root_.solution (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp only [altE, map_add, LinearMap.add_apply, Complex.add_im]
end Formalism.L2.Th1.H.SemicharacterExponentialLemmas
