-- Prove2me | solution 1 for Formalism.L2.Indef.matLat_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:17.92321+00:00
-- url     : https://prove2.me/submissions/c0b60346-2d9f-4f7b-a517-9384b3a82c85

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
theorem _root_.solution {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) K) (h : Function.Surjective φ.mulVec)
    (L : Submodule (𝓞 K) (Fin d → K)) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (matLat φ L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h1 : ((matLat φ L : Submodule (𝓞 K) (Fin d' → K)) : Set (Fin d' → K)) =
      φ.mulVecLin '' (L : Set (Fin d → K)) := by
    ext x; simp [matLat]
  rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact h
end Formalism.L2.Indef
