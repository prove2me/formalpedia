-- Prove2me | solution 1 for Formalism.L2.Indef.isUnit_det_of_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:20.798552+00:00
-- url     : https://prove2.me/submissions/c516b420-bdbe-42bd-aafe-f137d565156c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
theorem _root_.solution {F : Type} [Field F] {d : ℕ} (φ : Matrix (Fin d) (Fin d) F)
    (h : Function.Bijective φ.mulVec) : IsUnit φ.det := by
  first
  | exact (Matrix.isUnit_iff_isUnit_det φ).mp (Matrix.mulVec_injective_iff_isUnit.mp h.1)
  | exact (Matrix.isUnit_iff_isUnit_det φ).mp (Matrix.mulVec_surjective_iff_isUnit.mp h.2)
  | (have hb : Function.Bijective (Matrix.toLin' φ) := h
     have := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (Matrix.toLin' φ) hb)
     rwa [LinearEquiv.coe_ofBijective, LinearMap.det_toLin'] at this)
end Formalism.L2.Indef
