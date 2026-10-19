-- Prove2me | solution 1 for CompactnessConjecture.subdivisionPoint_base_of_point_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/dee3ff09-df6a-4711-b9d2-3233aaaf8c17

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_point
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_base_pair_adj
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_center_pair_adj
import Theorems.Thm_CompactnessConjecture_subdivisionPoint_center_of_point_base

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ q : SymplecticPoint K,
      copy (.inl (.inl otherBase)) = .inl q := by
  obtain ⟨c, hc⟩ := subdivisionPoint_center_of_point_base K
    copy (center := center) hbase
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (otherBase, center))) at hcenteradj
  rw [hc] at hcenteradj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj
  have hotheradj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl otherBase)))
    (copy (.inr (otherBase, center))) at hotheradj
  rw [hpair] at hotheradj
  obtain ⟨q, hq, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hotheradj.symm
  exact ⟨q, hq⟩
end CompactnessConjecture
