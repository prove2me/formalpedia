-- Prove2me | solution 1 for FiniteFields.Dwork.coefficientField_valuation_p
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:39:09.258262+00:00
-- url     : https://prove2.me/submissions/be0641b8-5339-4d33-83b3-cb1efb68ea4d

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula
open Polynomial
open scoped NNReal WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem solution :
    Valued.v (p : CoefficientField k p) = WithZero.exp (-1 : ℤ) := by
  rw [show (p : CoefficientField k p) =
      ((p : WithVal (coefficientValuation k p)) : CoefficientField k p) by
        exact (map_natCast
          (UniformSpace.Completion.coeRingHom :
            WithVal (coefficientValuation k p) →+* CoefficientField k p) p).symm]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p (p : CoefficientFractionField k p) = _
  rw [show (p : CoefficientFractionField k p) =
      algebraMap (CoefficientRing k p) (CoefficientFractionField k p) p by simp,
    coefficientValuation_p]
