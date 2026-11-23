-- Prove2me | solution 1 for Formalism.L2.Indef.matLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:54.029939+00:00
-- url     : https://prove2.me/submissions/458484f8-a968-45d4-a62f-f028adf6eb12

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
theorem _root_.solution {d d' d'' : ℕ} (A : Matrix (Fin d'') (Fin d') K) (B : Matrix (Fin d') (Fin d) K)
    (L : Submodule (𝓞 K) (Fin d → K)) : matLat (A * B) L = matLat A (matLat B L) := by
  first
  | (ext x
     simp only [matLat, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
     constructor
     · rintro ⟨y, hy, rfl⟩
       exact ⟨B.mulVec y, ⟨y, hy, rfl⟩, Matrix.mulVec_mulVec y A B⟩
     · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
       exact ⟨y, hy, (Matrix.mulVec_mulVec y A B).symm⟩)
  | (ext x
     simp [matLat, Submodule.mem_map, Matrix.mulVec_mulVec])
end Formalism.L2.Indef
