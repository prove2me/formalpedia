-- Prove2me | solution 1 for Formalism.G0.AllButLESmithP.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:39.017584+00:00
-- url     : https://prove2.me/submissions/01640780-4bef-44e7-8c83-cb98f1f34835

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
import Theorems.Thm_Formalism_G0_AllButLESmithP_down
import Theorems.Thm_Formalism_G0_AllButLESmithP_up

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
variable {P : Submodule O M} {n : ℕ}
namespace Formalism.G0.AllButLESmithP
theorem _root_.solution (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (B : Finset (Fin n)) (hB : ∀ i, i ∈ B ↔ ¬ snf.a i ∣ π ^ E) :
    AllButLE π ⊤ P g E ↔ B.card + (Fintype.card ι - n) ≤ g := by
  classical
  let S : Finset ι := B.map snf.f ∪ (Finset.univ.map snf.f)ᶜ
  have hcard : S.card = B.card + (Fintype.card ι - n) := by
    rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_compl, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_compl] at hj'
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    exact hj' (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  have hin : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨i', hi', he⟩ := Finset.mem_map.mp h
      rw [snf.f.injective he] at hi'
      exact (hB i).mp hi'
    · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ i)) (Finset.mem_compl.mp h)
  have hout : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E := by
    intro j hj
    have h1 : j ∈ Finset.univ.map snf.f := by
      by_contra h
      exact hj (Finset.mem_union_right _ (Finset.mem_compl.mpr h))
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp h1
    refine ⟨i, rfl, ?_⟩
    by_contra h
    exact hj (Finset.mem_union_left _ (Finset.mem_map_of_mem _ ((hB i).mpr h)))
  rw [← hcard]
  exact ⟨up snf π hπ g E S hin, down snf π g E S hout⟩
end Formalism.G0.AllButLESmithP
