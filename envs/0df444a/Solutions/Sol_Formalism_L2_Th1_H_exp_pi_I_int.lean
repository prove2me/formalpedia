-- Prove2me | solution 1 for Formalism.L2.Th1.H.exp_pi_I_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:14.008306+00:00
-- url     : https://prove2.me/submissions/f09d53d4-bdb7-4d13-b61d-4f22ae1e5344

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb

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
namespace Formalism.L2.Th1.H
theorem _root_.solution (m : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 ∨
      Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = -1 := by
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · left
    have : (Real.pi : ℂ) * Complex.I * ((2 * j : ℤ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · right
    have : (Real.pi : ℂ) * Complex.I * ((2 * j + 1 : ℤ) : ℂ)
        = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]
end Formalism.L2.Th1.H
