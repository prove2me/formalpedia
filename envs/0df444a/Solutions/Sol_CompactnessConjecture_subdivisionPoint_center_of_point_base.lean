-- Prove2me | solution 1 for CompactnessConjecture.subdivisionPoint_center_of_point_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/a5e3152e-61c7-4246-b345-e4f8ebc77b09

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_point
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_adjacent_to_line
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_base_pair_adj
import Theorems.Thm_CompactnessConjecture_subdivisionGraph_center_pair_adj

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
    {base : Fin 3} {center : Fin k}
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨c, hc, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj.symm
  exact ⟨c, hc⟩
end CompactnessConjecture
