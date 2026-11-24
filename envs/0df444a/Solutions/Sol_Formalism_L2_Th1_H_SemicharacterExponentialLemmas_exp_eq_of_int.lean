-- Prove2me | solution 1 for Formalism.L2.Th1.H.SemicharacterExponentialLemmas.exp_eq_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:10.943131+00:00
-- url     : https://prove2.me/submissions/cb493350-19e3-418f-bfe4-06c21444aa3b

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
theorem _root_.solution {a c : ℂ} (n : ℤ) (h : a = c + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    Complex.exp a = Complex.exp c := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Formalism.L2.Th1.H.SemicharacterExponentialLemmas
