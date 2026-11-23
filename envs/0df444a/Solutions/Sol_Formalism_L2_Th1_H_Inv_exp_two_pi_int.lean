-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.exp_two_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:22.066472+00:00
-- url     : https://prove2.me/submissions/620f2f8c-54ea-4f52-99c1-2742f7cca33f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence

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
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.Inv
theorem _root_.solution (m : ℤ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℝ)) : ℂ)) = 1 := by
  have h : -(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
end Formalism.L2.Th1.H.Inv
