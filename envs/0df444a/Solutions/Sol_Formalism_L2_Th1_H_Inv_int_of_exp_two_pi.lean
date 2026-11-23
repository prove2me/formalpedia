-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.int_of_exp_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:22.456815+00:00
-- url     : https://prove2.me/submissions/a524510c-6fb3-499a-98c1-66fb7f06caab

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
theorem _root_.solution {t : ℝ}
    (h : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (t : ℂ)) = 1) : ∃ m : ℤ, t = (m : ℝ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨-n, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have h3 : ((t : ℝ) : ℂ) = (((-n : ℤ) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ h2
    push_cast
    linear_combination -hn
  exact_mod_cast h3
end Formalism.L2.Th1.H.Inv
