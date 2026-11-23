-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_cnt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:13.635173+00:00
-- url     : https://prove2.me/submissions/cc5b58c6-3217-481c-a9da-c047d627f2c9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_ideal_pos
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
theorem _root_.solution (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) (hp : a ∈ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  rw [idxChange_span_alg]
  refine idxChange_cnt_ideal_pos v _ ?_ ?_
  · simpa [Ideal.span_singleton_eq_bot] using ha
  · rwa [Ideal.span_singleton_le_iff_mem]
end Formalism.DivisionValues
