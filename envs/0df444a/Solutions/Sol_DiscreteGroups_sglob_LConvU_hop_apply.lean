-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvU.hop_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:56:27.112793+00:00
-- url     : https://prove2.me/submissions/35a7e2cc-a7d3-439e-92ca-c1649a710d43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA

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
theorem _root_.solution (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl
end DiscreteGroups.sglob.LConvU
