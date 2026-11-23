-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_cnt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:21.893842+00:00
-- url     : https://prove2.me/submissions/20beb5e1-34d5-4c02-bc51-d266e7675fef

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_span_alg

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
theorem _root_.solution (v : HeightOneSpectrum R) (a : R) :
    0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  rw [idxChange_span_alg]
  exact FractionalIdeal.count_coe_nonneg K v _
end Formalism.DivisionValues
