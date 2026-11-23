-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_scG_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:18.752859+00:00
-- url     : https://prove2.me/submissions/3171085c-e9b8-491a-a53b-6c5e3c8c0b09

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules

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
theorem _root_.solution (a : K) (φ : V →ₗ[K] V') (A : Submodule R V) :
    scG a (A.map (φ.restrictScalars R)) = (scG a A).map (φ.restrictScalars R) := by
  unfold scG
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp
end Formalism.EigenvalueLevelCeiling
