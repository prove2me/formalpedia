-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvU.span_hop_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:54.478864+00:00
-- url     : https://prove2.me/submissions/e298c9c9-bc43-4def-bd09-bb78ddad15f0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
import Theorems.Thm_DiscreteGroups_sglob_LConvU_hop_one
import Theorems.Thm_DiscreteGroups_sglob_LConvU_span_hop_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mem_span_orbit
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_ReciprocityTheory_GC_burnside_surj_of_irred


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
theorem _root_.solution [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2
end DiscreteGroups.sglob.LConvU
