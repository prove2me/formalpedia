-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_Dg_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:33.63221+00:00
-- url     : https://prove2.me/submissions/961059ed-9524-4ffe-bbc3-e08ef283e3df

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (i : Fin d) (x y : K) :
    idxChangeDg i x * idxChangeDg i y = idxChangeDg i (x * y) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_of_ne hk]
end Formalism.DivisionValues
