-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_cnt_ideal_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:33.685811+00:00
-- url     : https://prove2.me/submissions/1e7d90d9-5c95-4ad3-ac03-89a8418de596

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
    (h : ¬ J ≤ v.asIdeal) : FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K v hJ]
  by_contra hne
  have hne' : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by
    exact_mod_cast hne
  have hd := (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne'
  rw [Ideal.dvd_iff_le] at hd
  exact h hd
end Formalism.DivisionValues
