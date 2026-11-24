-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.prod_laurent_T
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.53281+00:00
-- url     : https://prove2.me/submissions/23eeb8ec-9df7-4c1f-8f99-c83ed5da18ca

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
theorem _root_.solution {κ : Type*} (s : Finset κ) (f : κ → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (f i) : LaurentPolynomial A) = LaurentPolynomial.T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
