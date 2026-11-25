-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvU.hop_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:06:50.116072+00:00
-- url     : https://prove2.me/submissions/b68189d7-1c8a-4612-998c-0df2b97c90a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
import Theorems.Thm_DiscreteGroups_sglob_LConvU_hop_apply
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


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
theorem _root_.solution {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]
end DiscreteGroups.sglob.LConvU
