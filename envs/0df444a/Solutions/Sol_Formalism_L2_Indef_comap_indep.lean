-- Prove2me | solution 1 for Formalism.L2.Indef.comap_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:48.328852+00:00
-- url     : https://prove2.me/submissions/5c0caeaf-4cc9-461f-9bf1-5ea694ec78f7

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
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d' → F)) (hi : iSupIndep A) :
    iSupIndep fun p => (A p).comap φ.mulVecLin := by
  have hb : Function.Bijective φ.mulVecLin := h
  intro i
  have hle : (⨆ (j) (_ : j ≠ i), (A j).comap φ.mulVecLin) ≤ (⨆ (j) (_ : j ≠ i), A j).comap φ.mulVecLin :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  apply hb.1
  rw [map_zero]
  exact Submodule.disjoint_def.mp (hi i) _ hx1 hx2
end Formalism.L2.Indef
