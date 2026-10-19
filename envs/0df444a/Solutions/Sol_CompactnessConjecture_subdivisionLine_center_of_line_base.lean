-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_center_of_line_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/2a8b9cc2-76bf-4146-8e7f-d9eeacc56c7d

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
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨C, hC, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj.symm
  exact ⟨C, hC⟩
end CompactnessConjecture
