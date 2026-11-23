-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_cnt_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:06.725513+00:00
-- url     : https://prove2.me/submissions/e4139de6-d1d6-4960-be2c-c3ba60655166

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_ideal_zero
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
theorem _root_.solution (v : HeightOneSpectrum R) {s : R} (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  rw [idxChange_span_alg]
  refine idxChange_cnt_ideal_zero v _ ?_ ?_
  · simpa [Ideal.span_singleton_eq_bot] using hs0
  · rwa [Ideal.span_singleton_le_iff_mem]
end Formalism.DivisionValues
