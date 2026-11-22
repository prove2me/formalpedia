-- Prove2me | solution 1 for Formalism.L2.Indef.map_iSup_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:47.772886+00:00
-- url     : https://prove2.me/submissions/f6a4c8d5-13af-409f-8b82-f020ff1ceba8

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
theorem _root_.solution {F : Type} [Field F] {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) F)
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d → F)) (ht : (⨆ p, A p) = ⊤) :
    (⨆ p, (A p).map φ.mulVecLin) = ⊤ := by
  have hb : Function.Bijective φ.mulVecLin := h
  rw [← Submodule.map_iSup, ht, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hb.2
end Formalism.L2.Indef
