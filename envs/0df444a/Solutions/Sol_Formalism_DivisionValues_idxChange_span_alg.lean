-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_span_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:04.923053+00:00
-- url     : https://prove2.me/submissions/1773102e-bb87-4544-8e0e-04d44d4e707e

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
  [IsFractionRing R K]
namespace Formalism.DivisionValues
theorem _root_.solution (a : R) :
    FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) =
      ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ K) :=
  (FractionalIdeal.coeIdeal_span_singleton (S := R⁰) (P := K) a).symm
end Formalism.DivisionValues
