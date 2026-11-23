-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.584003+00:00
-- url     : https://prove2.me/submissions/89a6db28-8c21-46a7-8e0e-332682bd7c22

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {l m n : ℕ} (ρ : Fnl j) (M : Matrix (Fin l) (Fin m) Ω)
    (A : Matrix (Fin m) (Fin n) K) : (M * A.map j).map ρ.toFun = M.map ρ.toFun * A := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [ρ.sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, ρ.smul, mul_comm]
end Formalism.DivisionValues.FinitelyNonzeroLinear
