-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sfac_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:24.3356+00:00
-- url     : https://prove2.me/submissions/f5d3eb9b-f887-4e2a-a48e-4cb9ff57c3a9

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sfac_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sfac_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} (s : Finset ι) (j : ι → ℕ) :
    ∏ x ∈ s, sfac (j x) ≤ sfac (∑ x ∈ s, j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sfac]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    calc sfac (j x) * ∏ x ∈ s, sfac (j x) ≤ sfac (j x) * sfac (∑ x ∈ s, j x) := by
          apply mul_le_mul_of_nonneg_left ih (sfac_pos _).le
      _ ≤ _ := sfac_mul_le _ _
end Formalism.HermitianLatticeCounting.P
