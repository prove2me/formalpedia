-- Prove2me | solution 1 for Formalism.L2.Indef.map_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:42.3458+00:00
-- url     : https://prove2.me/submissions/4ec24d47-e9f2-407a-af05-fa8470158bfc

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
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d → F)) (hi : iSupIndep A) :
    iSupIndep fun p => (A p).map φ.mulVecLin := by
  have hb : Function.Bijective φ.mulVecLin := h
  intro i
  have hle : (⨆ (j) (_ : j ≠ i), (A j).map φ.mulVecLin) ≤ (⨆ (j) (_ : j ≠ i), A j).map φ.mulVecLin :=
    iSup₂_le fun j hj => Submodule.map_mono (le_iSup₂_of_le j hj le_rfl)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hbB, hab⟩
  have hba : b = a := hb.1 hab
  rw [hba] at hbB
  rw [Submodule.disjoint_def.mp (hi i) a ha hbB, map_zero]
end Formalism.L2.Indef
