-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_cnt_ideal_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:03.99826+00:00
-- url     : https://prove2.me/submissions/abea5c89-c383-49d1-be4b-94f1813d407f

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
theorem _root_.solution (v : HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ 0)
    (h : J ≤ v.asIdeal) : 1 ≤ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) := by
  have h1 := FractionalIdeal.count_mono K v
    ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h)
  rwa [FractionalIdeal.count_self] at h1
end Formalism.DivisionValues
