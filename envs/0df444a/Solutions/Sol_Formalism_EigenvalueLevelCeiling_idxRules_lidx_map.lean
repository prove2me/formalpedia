-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_lidx_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:20.991825+00:00
-- url     : https://prove2.me/submissions/71a56931-6e90-41ac-9fbf-1cb8b7985b54

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_P2M_Formalism_EigenvalueLevelCeiling_localization_map__dea12fd01409
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_len_map

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (hφ : Function.Injective φ)
    (A B : Submodule R V) :
    lidx p (A.map (φ.restrictScalars R)) (B.map (φ.restrictScalars R)) = lidx p A B := by
  have hφ' : Function.Injective (φ.restrictScalars R) := hφ
  have hinf : A.map (φ.restrictScalars R) ⊓ B.map (φ.restrictScalars R) =
      (A ⊓ B).map (φ.restrictScalars R) := (Submodule.map_inf _ hφ').symm
  unfold lidx locLen
  rw [hinf, localization_map₄, localization_map₄, localization_map₄, idxRules_len_map _ hφ',
    idxRules_len_map _ hφ']
end Formalism.EigenvalueLevelCeiling
