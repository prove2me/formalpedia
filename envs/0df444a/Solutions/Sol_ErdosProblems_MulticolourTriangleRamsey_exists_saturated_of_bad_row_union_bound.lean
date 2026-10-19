-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_saturated_of_bad_row_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/ca5c75f3-a62f-47ae-a411-c3145bab5593

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationMatrices

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m s : ℕ)
    (hbound :
      (∑ T ∈
          (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
        (badSaturationRows H m T).card ^ s) <
          Fintype.card (Fin s → (Fin m → Fin H) → Fin H)) :
    ∃ A : Fin s → (Fin m → Fin H) → Fin H, IsSaturated A := by
  classical
  by_contra hno
  push Not at hno
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  have hcover :
      (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)) ⊆
        columnSets.biUnion (fun T => badSaturationMatrices H m s T) := by
    intro A _
    have hA := hno A
    unfold IsSaturated at hA
    push Not at hA
    obtain ⟨T, hTcard, hrows⟩ := hA
    apply Finset.mem_biUnion.mpr
    refine ⟨T, ?_, ?_⟩
    · simp [columnSets, hTcard]
    · simp only [badSaturationMatrices, Fintype.mem_piFinset,
        badSaturationRows, Finset.mem_filter, Finset.mem_univ, true_and]
      intro row
      unfold RowCovers
      intro hcover_row
      obtain ⟨symbol, hmissing⟩ := hrows row
      obtain ⟨column, hcolumn, heq⟩ := hcover_row symbol
      exact hmissing column hcolumn heq
  have hcard :
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
        ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card := by
    calc
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) =
          (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)).card := by
            simp
      _ ≤ (columnSets.biUnion
        (fun T => badSaturationMatrices H m s T)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card :=
        Finset.card_biUnion_le
  simp_rw [card_badSaturationMatrices] at hcard
  change
    Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
      ∑ T ∈
        (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
          (badSaturationRows H m T).card ^ s at hcard
  exact (Nat.not_lt_of_ge hcard) hbound
end ErdosProblems.MulticolourTriangleRamsey
