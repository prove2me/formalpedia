-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_act_Dg_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:23.99739+00:00
-- url     : https://prove2.me/submissions/38522282-cd92-4e7f-af55-9b806f4b382b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_diagonal

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
theorem _root_.solution (e : Fin d → Fin d → K) (i : Fin d) (a : R) :
    idxChangeAct e (idxChangeDg i (algebraMap R K a)) = Function.update e i (a • e i) := by
  rw [idxChange_act_diagonal]
  funext k
  by_cases hk : k = i
  · subst hk; simp [algebraMap_smul]
  · simp [Function.update_of_ne hk]
end Formalism.DivisionValues
