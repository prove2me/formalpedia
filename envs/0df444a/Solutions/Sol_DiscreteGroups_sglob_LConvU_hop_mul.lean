-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvU.hop_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:46:14.784836+00:00
-- url     : https://prove2.me/submissions/e448ea0a-7d83-401b-9876-5cb38af5a27d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
import Theorems.Thm_DiscreteGroups_sglob_LConvU_map_fixedProj_of_invariant
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvU
open GroundTheory.Automorphic Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
namespace DiscreteGroups.sglob.LConvU
theorem _root_.solution {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]
end DiscreteGroups.sglob.LConvU
