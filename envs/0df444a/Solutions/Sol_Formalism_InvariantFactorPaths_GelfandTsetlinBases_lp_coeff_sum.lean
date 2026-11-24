-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_coeff_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.564379+00:00
-- url     : https://prove2.me/submissions/c7d56f10-558e-4733-b115-2635ce6ad79d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {A : Type*} [CommRing A] [IsDomain A]
omit [IsDomain A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {κ : Type*} (s : Finset κ) (f : κ → LaurentPolynomial A) (j : ℤ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
