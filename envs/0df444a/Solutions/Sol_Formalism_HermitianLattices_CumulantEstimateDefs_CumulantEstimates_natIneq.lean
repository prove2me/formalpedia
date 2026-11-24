-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.natIneq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:44.603582+00:00
-- url     : https://prove2.me/submissions/bd6de2ea-32d1-4c44-bd9c-f664abfbf0da

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : ¬ (p = 1 ∧ q = 1)) :
    p + q + 1 ≤ 2 * p * q := by
  by_cases hp2 : 2 ≤ p
  · have h1 : p * 1 ≤ p * q := Nat.mul_le_mul le_rfl hq
    have h2 : 2 * q ≤ p * q := Nat.mul_le_mul hp2 le_rfl
    nlinarith
  · have hp1 : p = 1 := by omega
    subst hp1
    omega
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
