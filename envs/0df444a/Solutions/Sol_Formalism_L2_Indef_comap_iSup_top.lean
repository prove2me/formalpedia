-- Prove2me | solution 1 for Formalism.L2.Indef.comap_iSup_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:36.181174+00:00
-- url     : https://prove2.me/submissions/177ead9a-2a0e-45a9-b7a5-3dd16aaed45c

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
    (h : Function.Bijective φ.mulVec) {Ix : Type} (A : Ix → Submodule F (Fin d' → F)) (ht : (⨆ p, A p) = ⊤) :
    (⨆ p, (A p).comap φ.mulVecLin) = ⊤ := by
  have hb : Function.Bijective φ.mulVecLin := h
  have e1 : (⨆ p, (A p).comap φ.mulVecLin).map φ.mulVecLin = ⊤ := by
    rw [Submodule.map_iSup]
    simp only [Submodule.map_comap_eq_of_surjective hb.2]
    exact ht
  have e2 := congrArg (Submodule.comap φ.mulVecLin) e1
  rwa [Submodule.comap_map_eq_of_injective hb.1, Submodule.comap_top] at e2
end Formalism.L2.Indef
