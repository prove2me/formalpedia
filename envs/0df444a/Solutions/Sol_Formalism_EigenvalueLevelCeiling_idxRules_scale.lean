-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:59.375245+00:00
-- url     : https://prove2.me/submissions/98effced-f683-471b-b3d6-463921dc8f42

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_add
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_lidx_self
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_lidx_map
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_span_map
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scG_lat
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_smul_inj
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scG_map
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scale_std

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
theorem _root_.solution [FiniteDimensional K V] (v : HeightOneSpectrum R) (W : Submodule K V)
    (B : Submodule R V) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) {a : K} (ha : a ≠ 0) :
    lidx v.asIdeal B (scG a B) =
      (finrank K W : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
  set n := finrank K W with hn
  let b : Basis (Fin n) K W := Module.finBasis K W
  let φ : (Fin n → K) →ₗ[K] V := W.subtype ∘ₗ (b.equivFun.symm : (Fin n → K) →ₗ[K] W)
  have hφ : Function.Injective φ := W.injective_subtype.comp b.equivFun.symm.injective
  set F0 : Submodule R (Fin n → K) := Submodule.span R (Set.range (Pi.basisFun K (Fin n))) with hF0
  set F : Submodule R V := F0.map (φ.restrictScalars R) with hF
  have hFl : F.FG ∧ Submodule.span K (F : Set V) = W := by
    refine ⟨(Submodule.fg_span (Set.finite_range _)).map _, ?_⟩
    rw [hF, idxRules_span_map, hF0, Submodule.span_span_of_tower, (Pi.basisFun K (Fin n)).span_eq,
      Submodule.map_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  have h1 : lidx v.asIdeal F (scG a F) =
      (n : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
    rw [hF, idxRules_scG_map, idxRules_lidx_map _ φ hφ, idxRules_scale_std v n ha]
  have h2 : lidx v.asIdeal (scG a F) (scG a B) = lidx v.asIdeal F B :=
    idxRules_lidx_map _ _ (idxRules_smul_inj ha) F B
  have h3 := idxRules_add v.asIdeal W B F (scG a B) hB hFl (idxRules_scG_lat ha hB)
  have h4 := idxRules_add v.asIdeal W F (scG a F) (scG a B) hFl (idxRules_scG_lat ha hFl)
    (idxRules_scG_lat ha hB)
  have h5 := idxRules_add v.asIdeal W B F B hB hFl hB
  rw [idxRules_lidx_self] at h5
  rw [h3, h4, h1, h2]
  linarith
end Formalism.EigenvalueLevelCeiling
