-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.localConditionsWeighted_trivial_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:21.35197+00:00
-- url     : https://prove2.me/submissions/ba559eda-fd4f-45ac-b694-bfc5a3ba64bb

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_eig_trivial
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_map_id_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (φ : (Fin 1 → K) →ₗ[K] K) (Mj : Submodule (𝓞 K) (Fin 1 → K)), Function.Injective φ ∧
      LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
          ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
            ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) ∧
      (idx w Mj Mj : ℝ) ≤ 0 := by
  have hcut : cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) = unitLat K := by
    unfold cut
    rw [eig_trivial K]
    simp
  refine ⟨(LinearEquiv.funUnique (Fin 1) K K).toLinearMap,
    (unitLat K).comap ((LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K)),
    (LinearEquiv.funUnique (Fin 1) K K).injective, ?_, ?_, ?_, ?_⟩
  · rw [eig_trivial K, inf_top_eq]
    exact LinearEquiv.range _
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, hcut]
  · rw [Submodule.map_comap_eq_of_surjective
      (f := (LinearEquiv.funUnique (Fin 1) K K).toLinearMap.restrictScalars (𝓞 K))
      (LinearEquiv.funUnique (Fin 1) K K).surjective, map_id_restrict K,
      map_id_restrict K, map_id_restrict K]
  · unfold idx Formalism.HermitianLatticesTheory.lidx
    simp
end Formalism.EigenvalueLevelCeiling
