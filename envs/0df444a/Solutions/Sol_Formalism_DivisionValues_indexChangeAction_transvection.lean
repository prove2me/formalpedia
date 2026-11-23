-- Prove2me | solution 1 for Formalism.DivisionValues.indexChangeAction_transvection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:01.348067+00:00
-- url     : https://prove2.me/submissions/793ff65a-12af-4f44-ad64-1c18dcc85078

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
theorem _root_.solution (e : Fin d → Fin d → K) {i j : Fin d} (hij : i ≠ j) :
    idxChangeAct e (Matrix.transvection i j (1 : K)) = Function.update e j (e j + e i) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, add_smul, Finset.sum_add_distrib, ite_smul, add_comm]
  · simp [idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      ite_smul, hk, Ne.symm hk]
end Formalism.DivisionValues
