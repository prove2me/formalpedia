-- Prove2me | solution 1 for Formalism.L2.Indef.finrank_comap_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:17.15602+00:00
-- url     : https://prove2.me/submissions/e1a88c5b-235e-4354-a5d3-ff680896e5cb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_finrank_map_bij

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
theorem _root_.solution {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) (A : Submodule F (Fin d' → F)) :
    finrank F (A.comap φ.mulVecLin) = finrank F A := by
  have hb : Function.Bijective φ.mulVecLin := h
  rw [← finrank_map_bij φ h (A.comap φ.mulVecLin), Submodule.map_comap_eq_of_surjective hb.2]
end Formalism.L2.Indef
