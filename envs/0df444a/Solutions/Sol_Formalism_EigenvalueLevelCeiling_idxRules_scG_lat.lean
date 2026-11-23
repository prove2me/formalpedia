-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_scG_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:07.964975+00:00
-- url     : https://prove2.me/submissions/457f5559-2f5e-48f0-be63-f054a8d21753

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_span_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {a : K} (ha : a ≠ 0) {W : Submodule K V} {A : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) :
    (scG a A).FG ∧ Submodule.span K ((scG a A : Submodule R V) : Set V) = W := by
  refine ⟨hA.1.map _, ?_⟩
  unfold scG
  rw [idxRules_span_map, hA.2, Submodule.map_smul _ _ a ha, Submodule.map_id]
end Formalism.EigenvalueLevelCeiling
